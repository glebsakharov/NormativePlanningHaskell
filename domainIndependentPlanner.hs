module DomainIndPlanner where 

import Control.Monad
import qualified FastDownward.Exec as Exec
import FastDownward
import Data.List ((\\), nub, union, intersect, any)
import qualified Data.Set as Set  
import qualified Data.Map as M


{- 

================================================================================
LTLf and Finite Automata in Norm-Guided Planning
================================================================================

This module integrates temporal norms into a classical planning setting by
compiling temporal logic specifications into finite-state automata and
synchronously composing them with the planner’s transition system.

The key idea is that temporal constraints over plans can be enforced 
incrementally during search, rather than verified post hoc over completed plans.

------------------------------------------------------------------------------
1. The Planning Setting
------------------------------------------------------------------------------

A classical planner searches for a finite sequence of actions:

    a0, a1, a2, ..., an

that transforms an initial state s0 into a state satisfying a goal condition.

Each action induces a transition:

    si --ai--> si+1

A plan is therefore a finite trace:

    s0, s1, s2, ..., sn

Standard planners enforce:
    - Action preconditions
    - Goal conditions

However, they do not natively enforce *temporal constraints*, such as:

    - "Safety must always hold."
    - "A task must eventually be completed."
    - "Condition A must hold until condition B occurs."
    - "Event X must occur before event Y."

These are naturally expressed in temporal logic. And are inescapable for planning in a normatively constrained domain

------------------------------------------------------------------------------
2. Linear Temporal Logic over Finite Traces (LTLf)
------------------------------------------------------------------------------

LTLf (Linear Temporal Logic over finite traces) is a formal language for
specifying temporal properties of *finite* sequences of states.

Unlike classical LTL (which is interpreted over infinite traces), LTLf is
interpreted over finite sequences:

    s0, s1, ..., sn

This makes LTLf particularly appropriate for planning, since plans are finite.

LTLf includes temporal operators such as:

    X φ        (Next)
    F φ        (Eventually)
    G φ        (Always)
    φ U ψ      (Until)
    ¬φ         (Negation)
    φ ∧ ψ      (Conjunction)
    φ ∨ ψ      (Disjunction)

Semantics are defined relative to positions within a finite trace.

For example:

    F φ

means that φ holds at some state si in the trace.

    G φ

means that φ holds at every state of the trace.

    φ U ψ

means that ψ must eventually hold, and φ must hold at all states prior
to the first occurrence of ψ.

------------------------------------------------------------------------------
3. Why We Compile LTLf to Finite Automata
------------------------------------------------------------------------------

Directly evaluating temporal formulas over traces during search is expensive
and conceptually awkward, because it requires reasoning over prefixes of
potentially long execution histories.

Instead, we exploit the following fundamental result:

    For every LTLf formula φ, there exists a finite automaton Aφ such that
    a finite trace satisfies φ if and only if that trace is accepted by Aφ.

This means:

    Temporal logic over traces
        ⇔
    Language recognition by a finite automaton

Thus, instead of reasoning about formulas over histories, we can reason about
automaton states.

------------------------------------------------------------------------------
4. What the Automaton Represents
------------------------------------------------------------------------------

The automaton encodes the "progress" of a temporal formula.

Each automaton state summarises:

    - Which sub-obligations of the temporal formula remain to be satisfied
    - Whether a violation has occurred

The automaton consumes, at each step, a *snapshot* of the world state.

A snapshot is a set of atomic propositions that are true in the current state,
for example:

    { APSafety, APTaskCompletion }

The transition function:

    δ : Q × Snapshot → Q

advances the automaton state based on which propositions hold after each action.

The automaton may contain:

    - Normal states (norm still satisfiable)
    - Accepting states (norm satisfied at end of trace)
    - Violation states (norm irreparably broken)

In our norm-enforcement setting, violation states are treated as dead states
and are pruned immediately during search.

------------------------------------------------------------------------------
5. Synchronous Product with the Planner
------------------------------------------------------------------------------

Conceptually, we construct the synchronous product of:

    (1) The planning transition system
    (2) The norm automaton

The combined state space becomes:

    (world_state, automaton_state)

For each candidate action:

    1. The world transitions to a successor state.
    2. A snapshot is extracted.
    3. The automaton transitions accordingly.
    4. If the automaton reaches a violation state, the transition is rejected.

Thus, norm enforcement reduces to:

    State-based admissibility filtering

rather than trace-based verification.

------------------------------------------------------------------------------
6. Why LTLf (Not Full LTL)
------------------------------------------------------------------------------

Classical LTL assumes infinite traces and is typically compiled into Büchi
automata with acceptance conditions based on infinite recurrence.

Planning problems, however, produce finite traces.

LTLf is therefore strictly more appropriate, because:

    - Acceptance is defined at the end of a finite trace.
    - The resulting automata are finite automata (DFA/NFA),
      not Büchi automata.
    - No reasoning about infinite repetition is required.

In this module, temporal norms are interpreted over finite plans.

------------------------------------------------------------------------------
7. Practical Implications for This Module
------------------------------------------------------------------------------

In this implementation:

    - Temporal formulas are represented explicitly (TemporalFormula).
    - Relevant atomic propositions are extracted from world states.
    - A deterministic norm automaton tracks compliance.
    - The planner state is augmented with an automaton state variable.
    - Actions are wrapped so that transitions leading to violations are pruned.

This ensures:

    ✔ All generated plans satisfy the temporal norms by construction.
    ✔ No post-hoc trace checking is required.
    ✔ Norms can be composed modularly by combining automata.

------------------------------------------------------------------------------
8. Conceptual Summary
------------------------------------------------------------------------------

LTLf provides a declarative way to specify temporal norms over plans.

Finite automata provide an operational mechanism to enforce those norms
incrementally during search.

The core theoretical bridge is:

    LTLf formula φ
        ⇓ (compilation)
    Deterministic finite automaton Aφ
        ⇓ (synchronous composition)
    Norm-guided planning

This architecture cleanly separates:

    - Domain dynamics (world transitions)
    - Normative constraints (automaton progression)

while preserving correctness and modularity.

================================================================================
-}
----------------------------------------------------
-- Utility
----------------------------------------------------

allM :: Monad m => (a -> m Bool) -> [a] -> m Bool
allM _ []     = return True
allM f (x:xs) = do
  cond <- f x
  if not cond then return False else allM f xs

----------------------------------------------------
-- Norm Logic Layer
----------------------------------------------------

data AtomicProp
  = APSafety
  | APTaskCompletion
  deriving (Eq, Ord, Show)

type Snapshot = Set.Set AtomicProp

data StateFormula
  = Atom AtomicProp
  | NotF StateFormula
  | AndF StateFormula StateFormula
  | OrF  StateFormula StateFormula
  deriving (Ord, Eq, Show)

data TemporalFormula
  = TrueF
  | FalseF
  | AndT TemporalFormula TemporalFormula
  | OrT TemporalFormula TemporalFormula
  | StateT StateFormula
  | NotT TemporalFormula
  | Next TemporalFormula
  | Always TemporalFormula
  | Eventually TemporalFormula
  | Until TemporalFormula TemporalFormula
  deriving (Ord, Eq, Show)

----------------------------------------------------
-- State Formula Evaluation
----------------------------------------------------

evalStateFormula :: Snapshot -> StateFormula -> Bool
evalStateFormula snap (Atom p)      = Set.member p snap
evalStateFormula snap (NotF f)      = not (evalStateFormula snap f)
evalStateFormula snap (AndF f g)    = evalStateFormula snap f && evalStateFormula snap g
evalStateFormula snap (OrF f g)     = evalStateFormula snap f || evalStateFormula snap g

----------------------------------------------------
-- Temporal Formula Progression
----------------------------------------------------

simplify :: TemporalFormula -> TemporalFormula
simplify (AndT TrueF x)  = simplify x
simplify (AndT x TrueF)  = simplify x
simplify (AndT FalseF _) = FalseF
simplify (AndT _ FalseF) = FalseF
simplify (OrT FalseF x)  = simplify x
simplify (OrT x FalseF)  = simplify x
simplify (OrT TrueF _)   = TrueF
simplify (OrT _ TrueF)   = TrueF
simplify (NotT TrueF)    = FalseF
simplify (NotT FalseF)   = TrueF
simplify (AndT x y)      = AndT (simplify x) (simplify y)
simplify (OrT x y)       = OrT (simplify x) (simplify y)
simplify (NotT x)        = NotT (simplify x)
simplify x               = x

progress :: Snapshot -> TemporalFormula -> TemporalFormula
progress _ TrueF  = TrueF
progress _ FalseF = FalseF

progress snap (StateT sf) =
  if evalStateFormula snap sf then TrueF else FalseF

progress snap (NotT φ) =
  simplify $ NotT (progress snap φ)

progress snap (AndT φ ψ) =
  simplify $ AndT (progress snap φ) (progress snap ψ)

progress snap (OrT φ ψ) =
  simplify $ OrT (progress snap φ) (progress snap ψ)

progress _ (Next φ) = φ

progress snap (Always φ) =
  simplify $ AndT (progress snap φ) (Always φ)

progress snap (Eventually φ) =
  simplify $ OrT (progress snap φ) (Eventually φ)

progress snap (Until φ ψ) =
  simplify $
    OrT (progress snap ψ)
        (AndT (progress snap φ) (Until φ ψ))

----------------------------------------------------
-- Norm Automaton (Formula-Based)
----------------------------------------------------

data NormAutomaton q = NormAutomaton
  { initialState :: q
  , transition   :: Snapshot -> q -> q
  , isViolation  :: q -> Bool
  }

compileTemporal :: TemporalFormula -> NormAutomaton TemporalFormula
compileTemporal φ =
  NormAutomaton
    { initialState = φ
    , transition   = progress
    , isViolation  = (== FalseF)
    }

----------------------------------------------------
-- Domain Datatypes
----------------------------------------------------

data State = State
  { objects :: [PropInfoObject]
  }

data ProblemDef = Prob 
  { goalCondition   :: State -> Effect Bool
  , safetyCondition :: State -> Effect Bool
  }

data Value = SafetyFirst | TaskCompletion
  deriving (Ord, Eq, Show)

data PropInfoObject = Prop
  { object     :: Object 
  , location   :: Var Location
  , clear      :: Var Bool
  , fireStatus :: Var FireStatus
  }

data Person = P1 | P2 deriving (Show, Eq, Ord)
data Block  = A | B | C deriving (Show, Eq, Ord)

data Object
  = ObjectP Person
  | Bucket
  | ObjectB Block
  | Table
  | Floor
  deriving (Show, Eq, Ord)

data Location = OnTable | OnObj Object | InHand | OnFloor
  deriving (Show, Eq, Ord)

type Pos = Var Location

data FireStatus = Burning | Safe
  deriving (Show, Eq, Ord)

type FireVar = Var FireStatus

data HandStatus = Holding Object | Empty
  deriving (Show, Eq, Ord)

type HandState = Var HandStatus

data Action
  = Pickup Object
  | Douse Object
  | PutDown Object
  | StackObject Object Object
  deriving (Show)

----------------------------------------------------
-- Snapshot Construction
----------------------------------------------------

snapshotFromState :: ProblemDef -> State -> Effect Snapshot
snapshotFromState prob st = do
  safe <- safetyCondition prob st
  goal <- goalCondition prob st
  return $ Set.fromList $
       [ APSafety         | safe ]
    ++ [ APTaskCompletion | goal ]

----------------------------------------------------
-- Norm-Constrained Action Wrapper
----------------------------------------------------

advanceNorm
  :: (Ord q) 
  => NormAutomaton q
  -> Var q
  -> Snapshot
  -> Effect ()
advanceNorm aut normVar snap = do
  qOld <- readVar normVar
  let qNew = transition aut snap qOld

  guard (not (isViolation aut qNew))

  writeVar normVar qNew

constrainAction
  :: NormAutomaton TemporalFormula
  -> Var TemporalFormula
  -> ProblemDef
  -> State
  -> Effect Action
  -> Effect Action
constrainAction aut normVar probDef st action = do

  -- Execute world effects first
  act <- action

  -- Snapshot AFTER mutation
  snap <- snapshotFromState probDef st

  -- Advance automaton
  advanceNorm aut normVar snap

  return act

  -- | Create deep copies of all PropInfoObjects, preserving the Var structure
{-cloneProps :: [PropInfoObject] -> Effect [PropInfoObject]
cloneProps props = forM props $ \Prop{object, location, clear, fireStatus} -> do
  loc'   <- newVar =<< readVar location
  clr'   <- newVar =<< readVar clear
  fire'  <- newVar =<< readVar fireStatus
  return $ Prop object loc' clr' fire'

-- | Commit cloned Props back to original ones
commitProps :: [PropInfoObject] -> [PropInfoObject] -> Effect ()
commitProps clones originals =
  forM_ (zip clones originals) $ \(c, o) -> do
    writeVar (location o) =<< readVar (location c)
    writeVar (clear o)    =<< readVar (clear c)
    writeVar (fireStatus o)=<< readVar (fireStatus c)

-- | Safe constrainAction: executes action on clones first
constrainAction
  :: NormAutomaton TemporalFormula
  -> Var TemporalFormula
  -> ProblemDef
  -> State
  -> Effect Action
  -> Effect Action
constrainAction aut normVar probDef st action = do

  -- 1. Clone state
  clones <- cloneProps (objects st)
  let stClone = st { objects = clones }

  -- 2. Run action on clone
  act <- actionOnClone action stClone

  -- 3. Take snapshot and advance norm on clone
  snap <- snapshotFromState probDef stClone
  advanceNorm aut normVar snap

  -- 4. If norm passes, commit back
  commitProps clones (objects st)

  return act

-- | Run an Effect action assuming the State object is replaced by clone
--   This depends on your DSL: for many planners you can temporarily swap in cloned Props
actionOnClone :: Effect Action -> State -> Effect Action
actionOnClone action stClone = do
  -- Implementation depends on your Effect DSL
  -- simplest: assume 'action' reads from the State passed explicitly
  action-}

----------------------------------------------------
-- Problem Definition
----------------------------------------------------

problem :: Problem (SolveResult Action)
problem = do

  --------------------------------------------------
  -- Initial State Variables
  --------------------------------------------------

  handState <- newVar Empty
  aLocation <- newVar (OnObj Table)
  aClear <- newVar False
  aFire <- newVar Safe
  let aProp = Prop (ObjectB A) aLocation aClear aFire

  bLocation <- newVar (OnObj Table)
  bClear <- newVar True
  bFire <- newVar Safe
  let bProp = Prop (ObjectB B) bLocation bClear bFire

  cLocation <- newVar (OnObj Table)
  cClear <- newVar True
  cFire <- newVar Safe
  let cProp = Prop (ObjectB C) cLocation cClear cFire

  tLocation <- newVar (OnObj Floor)
  tClear <- newVar True
  tFire <- newVar Safe
  let tProp = Prop Table tLocation tClear tFire

  bucketLocation <- newVar (OnObj Table)
  bucketClear <- newVar True
  bucketFire <- newVar Safe
  let bucketProp = Prop Bucket bucketLocation bucketClear bucketFire

  p1Location <- newVar (OnObj (ObjectB A))
  p1Clear <- newVar False
  p1Fire <- newVar Safe
  let p1Prop = Prop (ObjectP P1) p1Location p1Clear p1Fire

  p2Location <- newVar (OnObj Table)
  p2Clear <- newVar True
  p2Fire <- newVar Burning
  let p2Prop = Prop (ObjectP P2) p2Location p2Clear p2Fire

  let state = State [aProp,bProp,cProp,tProp,bucketProp,p1Prop,p2Prop]

  --------------------------------------------------
  -- Goal + Safety
  --------------------------------------------------

  let safetY st = allM safe (objects st)
        where safe Prop{fireStatus} = do
                f <- readVar fireStatus
                return (f == Safe)

  let 
    goalCheck :: State -> Effect Bool 
    goalCheck State{objects} = allM goalSatisfied objects
      where
      goalSatisfied Prop{object, location, clear, fireStatus} = do
        loc     <- readVar location 
        clr     <- readVar clear 
        fireSt  <- readVar fireStatus
        case object of
          ObjectB A ->
            return (loc == OnObj Table && clr == False && fireSt == Safe)
          ObjectB B ->
            return (loc == OnObj (ObjectB A) && clr == False && fireSt == Safe)
          ObjectB C ->
            return (loc == OnObj (ObjectB B) && clr == True && fireSt == Safe)
          ObjectP P1 ->
            return (loc == OnObj Table && clr == True && fireSt == Safe)
          ObjectP P2 ->
            return (loc == OnObj Table && clr == True && fireSt == Safe)
          Bucket ->
            return (loc == OnObj Table && clr == True && fireSt == Safe)
          Table ->
            return (loc == OnObj Floor && clr == True && fireSt == Safe) 

  let probDef = Prob goalCheck safetY



  --------------------------------------------------
  -- Norm Definition
  --------------------------------------------------

  let normFormula =
        Always (StateT (Atom APSafety))

  let normAut = compileTemporal normFormula

  normVar <- newVar TrueF 
  resetInitial normVar (initialState normAut)

  --------------------------------------------------
  -- Define Actions (unchanged)
  --------------------------------------------------

  ------------------------------------------------
    -- Pickup
    ------------------------------------------------
  let 
    clearOf :: Object -> Var Bool -- helper function 
    clearOf (ObjectB A) = clear aProp
    clearOf (ObjectB B) = clear bProp
    clearOf (ObjectB C) = clear cProp
    clearOf (ObjectP P1) = clear p1Prop
    clearOf (ObjectP P2) = clear p2Prop
    clearOf Bucket = clear bucketProp
    clearOf Table = clear tProp


    pickUp :: PropInfoObject -> Effect Action
    pickUp prp = do
      let obj   = object prp
          locV  = location prp
          clrV  = clear prp
          fireV = fireStatus prp

      -- Preconditions
      guard =<< readVar clrV                   -- the object should have nothing on top of it before being picked up
      guard . (== Empty) =<< readVar handState -- the robot hand should be empty before it tries to pick the object up
      guard (obj /= Table)                     -- never try to pick up the table
      guard . (== Safe) =<< readVar fireV      -- the object should not be on fire
      guard . (/= InHand) =<< readVar locV     -- the object should not already be being held by the robot hand

      -- Read location once
      loc <- readVar locV

      
      case loc of
        OnObj support -> do
          let supportClear = clearOf support   -- Technically a postcondition:
          writeVar supportClear True           -- make the o2 clear after picking up o1 from its top
        _ -> pure ()

      -- Postconditions
      writeVar locV InHand                     -- change the location of the object to in the robots hand
      writeVar handState (Holding obj)         -- the hand should be holding the object after picking it up
      writeVar clrV False                      -- the object is not clear on top after being picked up

      return (Pickup obj)

    ------------------------------------------------
    -- PutDown
    ------------------------------------------------
    
    putDown :: PropInfoObject -> Effect Action
    putDown Prop{object, location, clear} = do

      -- Precondtions
      guard . (== Holding object) =<< readVar handState
      guard . (== InHand)         =<< readVar location

      -- Postconditions
      writeVar location OnTable
      writeVar handState Empty
      writeVar clear True

      

      return (PutDown object) 

  

    ------------------------------------------------
    -- Stack
    ------------------------------------------------

    stack :: PropInfoObject -> PropInfoObject -> Effect Action 
    stack prp1
          prp2 = do 

      -- Preconditons - logical
      guard (object prp1 /= object prp2)
      guard . (== (Holding $ object prp1)) =<< readVar handState
      guard =<< (readVar $ clear prp2) 
      guard . (/= InHand) =<< (readVar $ location prp2)
      guard . (== InHand) =<< (readVar $ location prp1)
      

      -- Postconditions
      writeVar (location prp1) (OnObj $ object prp2)
      writeVar handState Empty 
      writeVar (clear prp1) True 
      writeVar (clear prp2) False 

      
      return $ StackObject (object prp1) (object prp2)




    ------------------------------------------------
    -- Douse
    ------------------------------------------------
    douse :: PropInfoObject -> Effect Action
    douse prop = do

      -- Preconditions
      guard (object prop == ObjectP P1 || object prop == ObjectP P2)
      guard . (== Holding Bucket) =<< readVar handState
      guard . (== Burning) =<< (readVar $ fireStatus prop)
      guard . (/= InHand) =<< (readVar $ location prop)
      guard . (== InHand) =<< (readVar $ location bucketProp)
      guard =<< (readVar $ clear prop)

      -- Postconditions
      writeVar (fireStatus prop) Safe
      writeVar handState Empty
      writeVar (location bucketProp) OnTable

      

      return (Douse $ object prop)

  let allProps = [aProp,bProp,cProp,p1Prop,p2Prop,tProp,bucketProp]

  let pickupActions =  [  constrainAction normAut normVar probDef state (pickUp p) | p <- allProps ]
      putdownActions = [  constrainAction normAut normVar probDef state (putDown p) | p <- allProps ]
      stackActions   = [  constrainAction normAut normVar probDef state (stack p1 p2) | p1 <- allProps, p2 <- allProps ]
      douseActions   = [  constrainAction normAut normVar probDef state (douse p) | p <- allProps ]

  let actions = pickupActions ++ putdownActions ++ stackActions ++ douseActions

  --------------------------------------------------
  -- Solve
  --------------------------------------------------

  solve
    Exec.bjolp
    actions
    [ location aProp ?= OnTable
    , location bProp ?= OnObj (ObjectB A)
    , location cProp ?= OnObj (Table)
    , location p1Prop ?= OnTable
    , location p2Prop ?= OnTable
    , fireStatus p1Prop ?= Safe
    , fireStatus p2Prop ?= Safe
    , location bucketProp ?= OnTable
    , handState ?= Empty
    , clear aProp ?= False
    , clear bProp ?= True 
    , clear cProp    ?= True
    , clear p1Prop   ?= True 
    , clear p2Prop   ?= True 
    , clear bucketProp ?= True 
    , clear tProp ?= True 

    ]


main :: IO ()
main = do
  res <- runProblem problem
  case res of
    Solved plan -> do
      putStrLn "Found a plan!"
      zipWithM_ (\i step -> putStrLn (show i ++ ": " ++ show step))
                [1..] (totallyOrderedPlan plan)

    Unsolvable ->
      putStrLn "Problem proven to be unsolvable."

    UnsolvableIncomplete ->
      putStrLn "Problem appears unsolvable, but search was incomplete."

    OutOfMemory ->
      putStrLn "Fast Downward ran out of memory."

    OutOfTime ->
      putStrLn "Fast Downward ran out of time."

    CriticalError ->
      putStrLn "Fast Downward encountered a critical error."

    InputError ->
      putStrLn "Fast Downward could not parse the input."

    Unsupported ->
      putStrLn "The chosen search engine is incompatible with this problem."

    Crashed stdout stderr exitCode -> do
      putStrLn "Fast Downward crashed!"
      putStrLn $ "Exit code: " ++ show exitCode
      putStrLn "Standard output:"
      putStrLn stdout
      putStrLn "Standard error:"
      putStrLn stderr

























      



