module DomainIndPlanner where 

import Control.Monad
import qualified FastDownward.Exec as Exec
import FastDownward
import Data.List ((\\), nub, union, intersect, any)
import qualified Data.Set as Set  
import qualified Data.Map as M
import Control.Applicative



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
  = FalseF
  | TrueF
  | StateT StateFormula
  | AndT TemporalFormula TemporalFormula
  | OrT TemporalFormula TemporalFormula
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
simplify (Next x)        = Next $ simplify x  
simplify (Always x)      = Always $ simplify x 
simplify (Eventually x)  = Eventually $ simplify x 
simplify (Until x y)     = Until  (simplify x) (simplify y) 



withSnapshot :: Var NormAutState -> Effect a -> Effect a
withSnapshot var action = do
    original <- readVar var
    result <- action
    writeVar var original
    return result

progress :: Snapshot -> TemporalFormula -> Var NormAutState -> Effect (Var NormAutState)
progress sn (StateT sf) normState = do
    state <- readVar normState
    case state of
        Waiting ->
            if evalStateFormula sn sf
                then do
                    writeVar normState Satisfied
                    return normState
                else do
                    writeVar normState Violated
                    empty
        _ -> return normState

progress sn (NotT f) normState = do 
    state <- readVar normState 
    case state of 
        Waiting -> do 
            s <- (withSnapshot normState $ do 
                    progress sn f normState
                    readVar normState )
            case s of 
                Violated -> do 
                    writeVar normState Violated
                    return normState
                Satisfied -> do 
                    writeVar normState Satisfied
                    empty 
                Waiting -> return normState
        Satisfied -> do 
            writeVar normState Satisfied
            empty
        Violated -> return normState

progress sn (OrT f1 f2) normState = do
    state <- readVar normState
    case state of
        Waiting ->
            withSnapshot normState (progress sn f1 normState)
            <|>
            withSnapshot normState (progress sn f2 normState)
        _ -> return normState


progress sn (AndT f1 f2) normState = do
    state <- readVar normState
    case state of
        Waiting -> do
            s1 <- withSnapshot normState $ do
                    progress sn f1 normState
                    readVar normState

            s2 <- withSnapshot normState $ do
                    progress sn f2 normState
                    readVar normState

            case (s1, s2) of
                (Satisfied, Satisfied) -> do
                    writeVar normState Satisfied
                    return normState

                (Violated, _) -> do
                    writeVar normState Violated
                    empty

                (_, Violated) -> do
                    writeVar normState Violated
                    empty

                _ -> return normState

        _ -> return normState

progress _ (Next _) normState = return normState
  

progress sn (Eventually f) normState = do
    state <- readVar normState
    case state of
        Waiting -> do
            result <- withSnapshot normState $ do
                progress sn f normState
                readVar normState

            case result of
                Satisfied -> do
                    writeVar normState Satisfied
                    return normState

                Violated -> return normState

                Waiting -> return normState

        _ -> return normState
-- f2 must eventually hold and f1 must hold at all states prior to the first occurrence f2   
progress sn (Until f1 f2) normState = do
    state <- readVar normState
    case state of
        Waiting ->
            (withSnapshot normState (progress sn f2 normState))
            <|>
            (withSnapshot normState $ do
                progress sn f1 normState
                progress sn (Until f1 f2) normState)

        _ -> return normState    


----------------------------------------------------
-- Norm Automaton (Formula-Based)
----------------------------------------------------

data NormAutomaton q = NormAutomaton
  { initialState :: Var q
  , transition   :: Snapshot -> TemporalFormula -> Var q -> Effect (Var q)
  , isViolation  :: q -> Effect Bool
  , isAccepting :: q -> Effect Bool
  , isWaiting :: q -> Effect Bool
  }

data NormAutState = Waiting | Satisfied | Violated deriving (Eq, Show, Ord)

violation :: NormAutState -> Effect Bool 
violation autState  = do 
    case autState of Violated -> return True 
                     _ -> return False 

accepting :: NormAutState -> Effect Bool 
accepting autState = do 
    case autState of Satisfied -> return True 
                     _ -> return False 

waiting :: NormAutState -> Effect Bool
waiting autState = do 
    case autState of Waiting -> return True 
                     _ -> return False





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

-- Variable backtracking mechanism



advanceNorm
  :: NormAutomaton NormAutState
  -> TemporalFormula
  -> Var NormAutState
  -> Snapshot
  -> Effect ()
advanceNorm aut tmpf normVar snap = do
  
  qNew <- (transition aut snap tmpf normVar)
  qNew' <- readVar qNew
  violated <- violation qNew'
  guard (not (violated))

  writeVar normVar qNew'

constrainAction
  :: 
     NormAutomaton NormAutState
  -> TemporalFormula
  -> Var NormAutState
  -> Var NormAutState
  -> ProblemDef
  -> State 
  -> State
  -> Effect Action
  -> Effect Action
constrainAction aut tmpf autState autState' probDef st st' action = do

  -- Execute world effects first
  act <- action

  -- Snapshot AFTER mutation
  snap <- snapshotFromState probDef st

  -- Advance automaton
  advanceNorm aut tmpf autState snap

  q <- readVar autState
  snap' <- snapshotFromState probDef st

  violated <- violation q 

  if violated
    then do rollBack aut autState autState' probDef st st' 
            guard(not (violated))
            return act 
    else return act

-- Variable rollback mechanism 

rollBack :: NormAutomaton NormAutState ->
            Var NormAutState ->
            Var NormAutState->
            ProblemDef ->
            State -> 
            State ->
            Effect ()
rollBack aut normVar normVar' probDef st st' = do 
     let obs = objects st 
     let obs' = objects st'
     forM_ (zip obs obs') $ \(o1,o2) -> do 
        writeVar (location o1) =<< readVar (location o2)
        writeVar (clear o1)    =<< readVar (clear o2)
        writeVar (fireStatus o1) =<< readVar (fireStatus o2)
        writeVar (normVar) =<< readVar (normVar')



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

  ----------------------------------------------------------
  -- copies 
  ----------------------------------------------------------

  handState' <- newVar Empty
  aLocation' <- newVar (OnObj Table)
  aClear' <- newVar False
  aFire' <- newVar Safe
  let aProp' = Prop (ObjectB A) aLocation aClear aFire

  bLocation' <- newVar (OnObj Table)
  bClear' <- newVar True
  bFire' <- newVar Safe
  let bProp' = Prop (ObjectB B) bLocation bClear bFire

  cLocation' <- newVar (OnObj Table)
  cClear' <- newVar True
  cFire' <- newVar Safe
  let cProp' = Prop (ObjectB C) cLocation cClear cFire

  tLocation' <- newVar (OnObj Floor)
  tClear' <- newVar True
  tFire' <- newVar Safe
  let tProp' = Prop Table tLocation tClear tFire

  bucketLocation' <- newVar (OnObj Table)
  bucketClear' <- newVar True
  bucketFire' <- newVar Safe
  let bucketProp' = Prop Bucket bucketLocation bucketClear bucketFire

  p1Location' <- newVar (OnObj (ObjectB A))
  p1Clear' <- newVar False
  p1Fire' <- newVar Safe
  let p1Prop' = Prop (ObjectP P1) p1Location p1Clear p1Fire

  p2Location' <- newVar (OnObj Table)
  p2Clear' <- newVar True
  p2Fire' <- newVar Burning
  let p2Prop' = Prop (ObjectP P2) p2Location p2Clear p2Fire

  let state = State [aProp,bProp,cProp,tProp,bucketProp,p1Prop,p2Prop]
  let state' = State [aProp',bProp',cProp',tProp',bucketProp',p1Prop',p2Prop']

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
  autState <- newVar Waiting 
  autState' <- newVar Waiting 

  let 
      normAut :: NormAutomaton (NormAutState) 
      normAut = 
            NormAutomaton 
              { initialState = autState
                ,transition = progress 
                ,isViolation = violation
                ,isAccepting = accepting
                ,isWaiting = waiting
              }


  let normFormula =
       AndT (Until (NotT (StateT (Atom APTaskCompletion))) (StateT (Atom APSafety))) (Eventually (StateT (Atom APTaskCompletion)))

  

  {-normVar <- newVar Waiting
  normVar' <- newVar Waiting-}
  {-
  normVar <- newVar TrueF 
  normVar' <- newVar TrueF -}
  -- resetInitial normVar (initialState normAut)

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

      let propObj' = head (filter (\x -> obj == object x) $ objects state')


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
          let supportClear = clearOf support   
          writeVar supportClear True 
          {-- rewrite to support backtracking-}
          let loc' = location propObj' 
          l' <- readVar loc'
          let supp (OnObj sup) = clearOf sup 
          let supportClear' = (supp l')
          writeVar supportClear' True          
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

  let pickupActions =  [  constrainAction normAut normFormula autState autState' probDef state state' (pickUp p) | p <- allProps ]
      putdownActions = [  constrainAction normAut normFormula autState autState' probDef state state' (putDown p) | p <- allProps ]
      stackActions   = [  constrainAction normAut normFormula autState autState' probDef state state' (stack p1 p2) | p1 <- allProps, p2 <- allProps ]
      douseActions   = [  constrainAction normAut normFormula autState autState' probDef state state' (douse p) | p <- allProps ]

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
























      



