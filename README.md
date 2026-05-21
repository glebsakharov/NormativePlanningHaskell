

# LTLf and Finite Automata in Norm-Guided Planning

This ReadMe is here to explain the current state of the integration of temporal planning into Fast Downward via the fastdownward library from Hackage. Fast Downward is a classical domain indepenedent planner written in C++. fastdownward is a Domain Specific Language for defining planning problems, converting them into a format Fast Downward recognises and solving them in Fast Downward. But fastdownward is written in Haskell. It is essentially a wrapper to Fast Downward.

# A classical planning problem in fastdownward: Gripper

# Temporal Planning planning problem

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








