

# Norm-Guided Planning

This ReadMe is here to explain the current state of the integration of temporal planning and thus norm-guided planning into Fast Downward via the fastdownward library from Hackage. Fast Downward is a classical domain indepenedent planner written in C++. fastdownward is a Domain Specific Language for defining planning problems, converting them into a format Fast Downward recognises and solving them in Fast Downward. But fastdownward is written in Haskell. It is essentially a wrapper to Fast Downward.


# Temporal Planning planning problem

## Explanation

The temporal planning problem we want to solve is a variant of BlocksWorld, the original 'toy problem' in AI. In this variant, there are three blocks: A, B and C. But there is also a man on fire, and a bucket of water. It is clear from the description what any sane person might want the robot arm to do first: pick up the bucket of water and douse the burning man before restacking the blocks. The temporal nature of the problem is 'interocular'. 

But how might we use fastdownward to solve it? 

Well we have to follow the standard approach in temporal planning: Use Linear Temporal Logic over Finite Traces and the well known correspondance between Deterministic Finite Automata. I'll explain the approach briefly here. In essence the behaviour we want to enforce in the above BlocksWorld variant is described by the LTLf formula (~task Until safety) and (Eventually task). This formula describes the states in a successful temporal plan from initial to goal state. That is, each state should adhere to that logical relationship that prescribes that no action is taken to finish the task until safety has been achieved. The formula thus desrcibes the relationship between each state in order from start to finish, or over what is called a trace, a sequence of states. Each state in the trace has associated with it a proposition, either safety or task or neither/empty. 

Now, each Linear Temporal Logic Formula over Finite Traces has associated with it a Deterministic Finite Automaton. The language of the automaton is a set of propositions such as {safety, task}. Perhaps you see where we are going now. 

The way we enforce the desired temporal ordering in the end plan is this: translate an LTLf formula to a DFA; update the state of the DFA with each action; set the goal so that it is satisfied if the DFA state is a final state in the DFA (ie the acceptance condition of a DFA). If the DFA state is found to be in a final state, the planner is able to store this as a possible solution.

The more technical way to describe what we are doing here is creating the product of the planners' transition system and the DFA describing the temporal formula. We are then asking the planner to search this product transition system in order to find a plan.

## BlocksWorld Variant

Now we move on to the solution to the problem. 

It is best in this case to move to the end of the source file rather than start at the beginning.

We solve a problem using the fastdownward library by calling the function solve, which takes as arguments a search configuration, a list of possible actions and a list of goal conditions:

It looks like this: 

``` haskell
solve
    Exec.bjolp
    actions
    [FastDownward.any [dfaStateName ?= stateName | stateName <- Set.toList $ dfaFinalStateNames $ constraintInfo temporalConstraint ]]
```
Exec.bjolp is the default search configuration defined in the Exec module. actions are a list of actions we have defined in the 'blocksWorldEthical.hs' file. The last list is a bit of a mouthful. It is just the list of goal conditions and states that if the DFA state variable carries the name of any of the final states in the DFA, then the goal has been reached. 

The list of actions is as so: 

``` haskell
let pickupActions =  [  updateAutomaton temporalConstraint probDef state dfaStateName (pickUp p) | p <- [aProp,bProp,cProp,bucketProp] ]
      putdownActions = [  updateAutomaton temporalConstraint probDef state dfaStateName (putDown p) | p <- [aProp,bProp,cProp,bucketProp] ]
      stackActions   = [  updateAutomaton temporalConstraint probDef state dfaStateName (stack p1 p2) | p1 <- [aProp,bProp,cProp], p2 <- [aProp,bProp,cProp] ]
      douseActions   = [  updateAutomaton temporalConstraint probDef state dfaStateName (douse p) | p <- [p1Prop,p2Prop] ]

  let actions = pickupActions ++ putdownActions ++ stackActions ++ douseActions
```

And updateAutomaton is defined like this:

``` haskell
updateAutomaton :: 
     TemporalConstraint                    
  -> ProblemDef
  -> State
  -> Var String                 
  -> Effect Action 
  -> Effect Action
updateAutomaton tmpConstraint pDef st dfaStateVar act = do 
    act' <- act 
    let dfaInfo = constraintInfo tmpConstraint
    
    snap <- computeSnapshotFromState st pDef 
    currentState <- readVar dfaStateVar
    
    case findDFATransition dfaInfo currentState snap of
        Just nextState -> writeVar dfaStateVar nextState
        Nothing -> empty
    
    return act'
```

And this is it. You just need to translate an LTLf formula to a DFA and track its state as the search progresses. Next we move on to explaining precisely how we have done this.

# LTLf to Deterministic Finite Automaton

## Datatypes and Definitions for LTLf formulas:

The following datatypes and functions describe the syntactic stucture of LTLf formulas. The LTLf dataype in particular closely resembles the Backus Naur form of the context free grammar for LTLf. The functions which follow that are for defining other common operators which can be found in LTLf in terms of the simpler operators we define in the sum datatype.

``` haskell
data Atom = Atom String 
  deriving (Eq, Ord, Show, Generic)

data LTLf
  = TrueF
  | FalseF
  | Prop Atom
  | Not LTLf
  | And LTLf LTLf
  | Or LTLf LTLf
  | Next LTLf
  | Until LTLf LTLf
  | Release LTLf LTLf
  deriving (Eq, Ord, Show, Generic)

-- Derived operators
eventually :: LTLf -> LTLf
eventually phi = Until TrueF phi

always :: LTLf -> LTLf
always phi = Not (eventually (Not phi))

weakUntil :: LTLf -> LTLf -> LTLf
weakUntil phi psi = Or (Until phi psi) (always phi)

strongRelease :: LTLf -> LTLf -> LTLf
strongRelease phi psi = And (Release phi psi) (eventually phi)
```
The following function takes and LTLf formula and outputs a Deterministic Finite Automaton (DFA) which has sets of sets of LTLf formulas as states and Atoms as symbols/labels. Each step in this function describes a step in the algorithm for translating LTLf to DFA and we will follow this sequence in this section in detail, describing each helper function in the let expression along the way.

``` haskell
compileLTLfToDFA :: LTLf -> DFA (Set.Set (Set.Set LTLf)) (Set.Set Atom)
compileLTLfToDFA formula =
  let
    phi_nnf = toNNF formula
    cl = closure phi_nnf
    elementarySets = generateElementarySets cl
    transitions = buildNFATransitions cl elementarySets
    initials = findInitialStates formula elementarySets
    finals = findFinalStates elementarySets
  in
    if null elementarySets
    then error "No elementary sets found - formula may be unsatisfiable"
    else nfaToDFA transitions initials finals
```
### toNNF

The first step in the algorithm is to convert an LTLf formula to Negation Normal Form (NNF). This simply means we are moving the Negation 'inward' inside formulas using De Morgans laws and analagous rules for temporal operators, so that negation only acts on propositional atoms, and not on temporal operators. Here is the toNNF function: 

``` haskell
toNNF :: LTLf -> LTLf
toNNF TrueF = TrueF
toNNF FalseF = FalseF
toNNF (Prop a) = Prop a
toNNF (Not TrueF) = FalseF
toNNF (Not FalseF) = TrueF
toNNF (Not (Not phi)) = toNNF phi
toNNF (Not (Prop a)) = Not (Prop a)
toNNF (Not (And phi psi)) = Or (toNNF (Not phi)) (toNNF (Not psi))
toNNF (Not (Or phi psi)) = And (toNNF (Not phi)) (toNNF (Not psi))
toNNF (Not (Next phi)) = Next (toNNF (Not phi))
toNNF (Not (Until phi psi)) = Release (toNNF (Not phi)) (toNNF (Not psi))
toNNF (Not (Release phi psi)) = Until (toNNF (Not phi)) (toNNF (Not psi))
toNNF (And phi psi) = And (toNNF phi) (toNNF psi)
toNNF (Or phi psi) = Or (toNNF phi) (toNNF psi)
toNNF (Next phi) = Next (toNNF phi)
toNNF (Until TrueF phi) = Until TrueF (toNNF phi)  
toNNF (Until FalseF phi) = toNNF phi  
toNNF (Until phi TrueF) = TrueF  
toNNF (Until phi FalseF) = toNNF (always phi)
toNNF (Until phi psi) = Until (toNNF phi) (toNNF psi)
toNNF (Release phi psi) = Release (toNNF phi) (toNNF psi)
```
As we can see via this recursive definition, the final result of 'toNNF phi' is a temporal formula whose negations are pushed inwards.

### Closure Set of a Temporal Formula:

The closure of an LTLf formula is the set of its subformulas taken with the union of the set of its negated subformulas such that the resultant set is simplified and added to {True, False}. 

``` haskell
closure :: LTLf -> Set.Set LTLf
closure phi = 
    let cl = subformulas (toNNF phi)
        allFormulas = Set.union cl (Set.map Not cl)
        -- Remove redundant Not (Not ...) formulas
        simplified = Set.filter (\f -> case f of
                                        Not (Not _) -> False
                                        _ -> True) allFormulas
    in Set.union (Set.fromList [TrueF, FalseF]) simplified
```

``` haskell
subformulas :: LTLf -> Set.Set LTLf
subformulas TrueF = Set.singleton TrueF
subformulas FalseF = Set.singleton FalseF
subformulas (Prop a) = Set.singleton (Prop a)
subformulas (Not phi) = Set.insert (Not phi) (subformulas phi)
subformulas (And phi psi) = Set.insert (And phi psi) $ Set.union (subformulas phi) (subformulas psi)
subformulas (Or phi psi) = Set.insert (Or phi psi) $ Set.union (subformulas phi) (subformulas psi)
subformulas (Next phi) = Set.insert (Next phi) (subformulas phi)
subformulas (Until phi psi) = Set.insert (Until phi psi) $ Set.union (subformulas phi) (subformulas psi)
subformulas (Release phi psi) = Set.insert (Release phi psi) $ Set.union (subformulas phi) (subformulas psi)
```

### Elementary Sets:
The set of elementary sets is a filtered set of subsets of the closure. The filter conditions are:
 - no contradictions in the subset
 - TrueF must be in every subset
 - FalseF must not be in any subset
 - If 'And phi chi' is a member of the subset, then phi and chi must both be members
 - If 'Or phi chi' is a member, then phi or chi must be members
   
``` haskell
generateElementarySets :: Set.Set LTLf -> [Set.Set LTLf]
generateElementarySets cl = 
  filter (isElementary cl) (allSubsets cl)
```

``` haskell
isElementary :: Set.Set LTLf -> Set.Set LTLf -> Bool
isElementary cl b =
  -- No contradictions
  Set.null (Set.intersection b (Set.map Not b))
  &&
  -- TrueF must be in every elementary set
  (Set.member TrueF b)
  &&
  -- FalseF must not be in any elementary set
  (not (Set.member FalseF b))
  &&
  -- Boolean closure for And
  (forallInSet (\psi -> 
    case psi of
      And phi chi -> (Set.member (And phi chi) b) == (Set.member phi b && Set.member chi b)
      _ -> True) b)
  &&
  -- Boolean closure for Or
  (forallInSet (\psi ->
    case psi of
      Or phi chi -> (Set.member (Or phi chi) b) == (Set.member phi b || Set.member chi b)
      _ -> True) b)
  where
    forallInSet p s = all p (Set.toList s)

```
### NFA Transitions 

The next step in the procedure for translating an LTLf formula into a DFA is to translate it first into an NFA. We don't build an NFA per say, but rather the list of its transitions: 

``` haskell
buildNFATransitions :: Set.Set LTLf -> [Set.Set LTLf] -> [NFATransition LTLf]
buildNFATransitions cl elementarySets =
    [ NFATransition b b' label
    | b <- elementarySets
    , b' <- elementarySets
    , label <- allPossibleLabels  
    , isConsistentTransition cl b b' label
    ]
  where
    allAtoms = Set.unions [atomsFromLiteral f | f <- Set.toList cl, isLiteral f]
    allPossibleLabels = Set.toList (Set.powerSet allAtoms)
```

Where NFATransition is defined as:

``` haskell
data NFATransition a = NFATransition
  { nfaFrom :: Set.Set a
  , nfaTo :: Set.Set a
  , nfaLabel :: Set.Set Atom
  } deriving (Show, Eq, Ord)
```
So we can see that a state in the NFA corresponds to a set of LTLf formulas, selected from the elementary sets, and a label for a transition is simply an atomic proposition. But we need to impose a condition, the transition must be consistent, hence the function in the list comprehension: isConsistentTransition.

This function takes three sets of LTLf formulas: the closure of the original formula and the two proposed sets from which we will select the source and target states for each transition - the final argument is the label.

``` haskell
-- Check if a transition is consistent with the observed label
isConsistentTransition :: Set.Set LTLf -> Set.Set LTLf -> Set.Set LTLf -> Set.Set Atom -> Bool
isConsistentTransition cl b b' label =
  -- Condition 1: The label must be consistent with the literals in b
  (all (\lit -> 
      case lit of
        Prop a -> Set.member a label == Set.member lit b
        Not (Prop a) -> (not (Set.member a label)) == Set.member lit b
        _ -> True)
      (Set.filter isLiteral b))
  &&
  -- Condition 2: All next obligations must be satisfied in b'
  (Set.isSubsetOf (nextSet b) b')
  &&
  -- Condition 3: Until conditions
  (all (\psi ->
      case psi of
        Until phi chi -> 
          if Set.member (Until phi chi) b
          then 
            -- Until is satisfied if chi holds now, 
            -- OR (phi holds now AND Until holds in next state)
            holdsInLabel chi label ||
            (holdsInLabel phi label && Set.member (Until phi chi) b')
          else True
        _ -> True)
      (Set.toList b))
  &&
  -- Condition 4: Release conditions (dual of Until)
  (all (\psi ->
      case psi of
        Release phi chi ->
          if Set.member (Release phi chi) b
          then
            -- Release holds if chi holds now AND (phi holds now OR Release holds in next state)
            holdsInLabel chi label &&
            (holdsInLabel phi label || Set.member (Release phi chi) b')
          else True
        _ -> True)
      (Set.toList b))
  where
    forallInSet p s = all p (Set.toList s)
```
### Initial and Final States of the NFA

The next step in the algorithm invloves determining which are the initial and final states in the NFA. This procedure involves filtering the elementary sets of the formula down to a list of sets of LTLf formulas. We first convert the original formula to NNF, then we apply the filter: the set remains if the original formula (in NNF) is contained in the set, either as a negation or otherwise.

``` haskell
containsFormula :: Set.Set LTLf -> LTLf -> Bool
containsFormula b phi = 
  case phi of
    Not psi -> Set.member (Not psi) b  
    _ -> Set.member phi b

-- Find initial states (must contain the original formula)
findInitialStates :: LTLf -> [Set.Set LTLf] -> [Set.Set LTLf]
findInitialStates phi elementarySets =
  let phi_nnf = toNNF phi
  in filter (\b -> containsFormula b phi_nnf) elementarySets
```
Next we find the final states (the states where acceptance is determined). 

``` haskell
isFinalState :: Set.Set LTLf -> Bool
isFinalState b = 
    -- No Next formulas
    not (any isNextFormula (Set.toList b))
    &&
    -- No unsatisfied Until formulas (including Eventually)
    not (any (\psi -> 
        case psi of
            -- Eventually phi (Until TrueF phi)
            Until TrueF phi -> 
                not (Set.member phi b)
            
            -- Regular Until phi chi
            Until phi chi -> 
                not (Set.member chi b) && 
                (not (Set.member phi b) || not (Set.member (Until phi chi) b))
            
            -- Anything else is not an unsatisfied obligation
            _ -> False)
        (Set.toList b))

findFinalStates :: [Set.Set LTLf] -> Set.Set (Set.Set LTLf)
findFinalStates = Set.fromList . filter isFinalState
```
### Converting an NFA to a DFA 

Now that we have identified and collected the final and intitial states of the NFA, we have enough information to 'determinize' it.

First we have the datatype for DFA's:

``` haskell
data DFA s a = DFA
  { dfaInitial :: s
  , dfaTransitions :: Map.Map (s, a) s
  , dfaFinals :: Set.Set s
  } deriving (Show, Eq, Ord)
```

Instead of storing the transitions in a list, we build the DFA explicity as a record with three fields. There is the initial state of type s. The the dfaTransitions of type 'Map.Map (s, a) s'. We store the transitions in this way for quicker access - once we have our DFA available to influence the planner, we want the acceptance checks to run quickly. And lastly we have the final states, the dfaFinals, stored as sets of type s, 'Set.Set s'.

Now we turn to the nfaDFA function:

``` haskell
nfaToDFA :: [NFATransition LTLf] 
         -> [Set.Set LTLf]  -- Initial states
         -> Set.Set (Set.Set LTLf)  -- Final states
         -> DFA (Set.Set (Set.Set LTLf)) (Set.Set Atom)
nfaToDFA transitions nfaInitials nfaFinals =
  let
    -- Get all alphabet symbols (all subsets of atoms from transitions)
    allAtoms = Set.unions [label | NFATransition _ _ label <- transitions]
    alphabet = Set.toList (Set.powerSet allAtoms)
    
    -- Build transition map for quick lookup
    transMap :: Map.Map (Set.Set LTLf, Set.Set Atom) (Set.Set (Set.Set LTLf))
    transMap = Map.fromListWith Set.union
      [ ((from, label), Set.singleton to)
      | NFATransition from to label <- transitions
      ] 
    
   
    nfaInitialSet = Set.fromList nfaInitials
    initialDFAState = epsilonClosure nfaInitialSet transMap
    sinkState = Set.empty
    -- Compute all reachable DFA states
    allDFAStates = Set.insert sinkState (closureDeterminize (Set.singleton initialDFAState) alphabet transMap)
    
    -- Build DFA transitions
    dfaTransitionsMap = Map.fromList
	  [ ((dfaState, symbol), nextDFAState)
	  | dfaState <- Set.toList allDFAStates
	  , symbol <- alphabet
	  , let nextDFAState = 
	          let next = epsilonClosure 
	                      (Set.unions 
	                        [ Map.findWithDefault Set.empty (nfaState, symbol) transMap
	                        | nfaState <- Set.toList dfaState
	                        ]) transMap
	          in if Set.null next then sinkState else next
	  ]    
    
    -- Final DFA states: any DFA state containing an NFA final state
    dfaFinalStates = Set.filter 
      (\dfaState -> not (Set.null (Set.intersection dfaState nfaFinals)))
      allDFAStates
    
  in DFA initialDFAState dfaTransitionsMap dfaFinalStates 
```

## Passing traces through the DFA

In order to use the DFA in the planning system, we need to make it operational. We achieve this with the following two functions:

``` haskell
runDFA :: (Ord s, Ord a) => DFA s a -> [a] -> s
runDFA dfa trace =
  foldl' (\state symbol -> 
    case Map.lookup (state, symbol) (dfaTransitions dfa) of
      Just next -> next
      Nothing -> error "No transition defined"
  ) (dfaInitial dfa) trace

accepts :: (Ord s, Ord a) => DFA s a -> [a] -> Bool
accepts dfa trace =
  let finalState = runDFA dfa trace
  in Set.member finalState (dfaFinals dfa)
```
runDFA takes a list of atoms (the language of the DFA is a set of atoms) and searches the transition map of the DFA for a matching transition. If their is a (state, symbol) pair - state, atom pair - then the associated state is returned. This process is repeated for each atom in the list in order until the trace has been exhausted. 

accepts checks whether the result of runDFA on a trace is contained in the set of final states. If it is, the DFA accepts the trace.

Here is an example of a DFA in action: 

``` haskell
testDFA :: IO ()
testDFA = do
  let task = Atom "task_completion"
      safety = Atom "safety"
      formula = And
        (Until (Not (Prop task)) (Prop safety))
        (eventually (Prop task))
  
  let dfa = compileLTLfToDFA formula
  
  -- Test trace 1: safety always true, task becomes true
  let trace1 = [
        		Set.fromList [safety],           -- step 1: safety true, task false
        		Set.fromList [safety],           -- step 2: safety true, task false  
        		Set.fromList [safety, task]      -- step 3: both true
      			]
  
  putStrLn $ "Trace 1 accepted? " ++ show (accepts dfa trace1)
  
  let trace2 = [
        		Set.fromList [task],
        		Set.fromList [task],                 
        		Set.fromList [task]
      		   ]
  
  putStrLn $ "Trace 2 accepted? " ++ show (accepts dfa trace2)
  
  
  let trace3 = [
        		Set.fromList [safety],
        		Set.fromList [safety],
        		Set.fromList [safety]
      			]
  
  putStrLn $ "Trace 3 accepted? " ++ show (accepts dfa trace3)
```
If you run the above code in the ghci REPL, you should see that the DFA accepts the first trace, and then rejects the last two traces. 

# Testing and Debugging the LTLf to DFA translation

## Generating Custom Datatypes for Tests
In order to be able to test properties of the translation with QuickCheck, we will need to supply QuickCheck with methods for generating instances of the custom datatypes we use to build our definition of LTLf formulas. This is done by creating instances of the typeclass Arbitrary for the datatypes Atom and LTLf.

``` haskell
instance Arbitrary Atom where 
	arbitrary = oneof [
			Atom <$> (pure "safety"),
			Atom <$> (pure "taskCompletion")
		]

data FormulaClass = Simple | Linear | Balanced | Complex

ltlfGenWithClass :: Int -> FormulaClass -> Gen LTLf
ltlfGenWithClass 0 _ = oneof [pure TrueF, pure FalseF, Prop <$> arbitrary]
ltlfGenWithClass n Simple = frequency [
    (5, Prop <$> arbitrary),
    (2, Not <$> (ltlfGenWithClass (n-1) Simple)),
    (1, Next <$> (ltlfGenWithClass (n-1) Simple))
  ]
ltlfGenWithClass n Linear = frequency [
    (3, Prop <$> arbitrary),
    (2, Not <$> (ltlfGenWithClass (n-1) Linear)),
    (1, Until <$> (ltlfGenWithClass (n-1) Linear) <*> (ltlfGenWithClass 0 Linear))
    
  ]
ltlfGenWithClass n Complex = 
    ltlfGenWithClass n Simple
```
Instead of setting 'arbitrary = ltlfGenWithClass' for LTLf formulas, we first define a generator that uses ltlgGenWithClass called smallLTLf2:
``` haskell
smallLTLf2 :: Gen LTLf
smallLTLf2 = sized $ \n -> 
    frequency [
        (5, ltlfGenWithClass (min n 2) Simple),
        (4, ltlfGenWithClass (min n 2) Linear),
        (1, ltlfGenWithClass (min n 2) Complex)
    ]
```
Now we define Arbitrary for LTLf with smallLTLf2: 
``` haskell
instance Arbitrary LTLf where
	arbitrary = smallLTLf2
```
smallLTLf2 uses a statistically inspired strategy to generate LTLf formulas. The frequency function essentially accepts a frequency distribution with weights 5, 4, and 1 for Simple, Linear and Complex formulas respectively. This fixes the probabilities of occurrence of each type of formula in the generation process. This is part of the strategy we use to make sure we are testing the functions in the translation code with 'representative' examples of LTLf formulas. We are mainly interested in the kind of formula likely to appear in a planning scenario of interest. That being said, non-representative examples are still valuable as they stress-test the translation for correctness.

Thus, while we have a higher chance of generating formulas of particular interest in planning scenarios in our tests, we still generate some which are not that interesting, to make sure we are covering cases which are still valid LTLf formulas that wont see use in the final planning code. 

Now that we have a generator for LTLf formulas, we can test the code that uses this data for correctness. The following property checks whether, given a 'Next phi' formula in the source state for an NFA, the target contains phi. Ie, if 'Next phi' is true at step s_{i}, then s_{i+1} step should have phi as true: 

``` haskell
propTransitionNextConsistent :: Property
propTransitionNextConsistent = forAll smallLTLf2 $ \formula ->
    let cl = closure (toNNF formula)
        elemSets = generateElementarySets cl
        transitions = buildNFATransitions cl elemSets
    in all (\(NFATransition from to _) -> 
            all (\nextF -> Set.member (unwrapNext nextF) to)
                (Set.filter isNextFormula from))
        transitions
```


















