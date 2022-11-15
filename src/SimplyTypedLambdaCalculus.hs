module SimplyTypedLambdaCalculus where

import Relude

data Expr
    = Var Name
    | Lambda Name Expr
    | App Expr Expr
    | Zero
    | Add1 Expr
    | Rec Ty Expr Expr Expr
    | Ann Expr Ty
    deriving (Show)

data Ty = TNat | TArr Ty Ty deriving (Eq, Show)

newtype Name = Name Text deriving (Show, Eq)

newtype Env val = Env [(Name, val)] deriving (Show)

initEnv :: Env val
initEnv = Env []

instance Functor Env where
    fmap f (Env xs) = Env $ map (second f) xs

newtype Message = Message Text deriving (Show)

failure :: Text -> Either Message a
failure = Left . Message

lookupVar :: Env val -> Name -> Either Message val
lookupVar (Env []) (Name x) = failure ("Not found: " <> x)
lookupVar (Env ((y, v) : env')) x
    | y == x = pure v
    | otherwise = lookupVar (Env env') x

type Context = Env Ty

initCtx :: Context
initCtx = initEnv

extend :: Env val -> Name -> val -> Env val
extend (Env env) x v = Env ((x, v) : env)

synth :: Context -> Expr -> Either Message Ty
synth ctx (Var x) = lookupVar ctx x
synth ctx (App rator rand) = do
    ty <- synth ctx rator
    case ty of
        TArr argT retT -> do
            check ctx rand argT
            pure retT
        other -> failure $ "Not a function type: " <> show other
synth ctx (Rec ty tgt base step) = do
    tgtT <- synth ctx tgt
    case tgtT of
        TNat -> do
            check ctx base tgtT
            check ctx step . TArr TNat $ TArr ty ty
            pure ty
        other -> failure $ "Not the type Nat: " <> show other
synth ctx (Ann e t) = check ctx e t $> t
synth _ other =
    failure $ "Can't find a type of " <> show other <> ". Try adding a type annotation."

check :: Context -> Expr -> Ty -> Either Message ()
check ctx (Lambda x body) t =
    case t of
        TArr arg ret ->
            check (extend ctx x arg) body ret
        other -> failure $ "Lambda requires a function type, but got " <> show other
check ctx Zero t =
    case t of
        TNat -> Right ()
        other ->
            failure $
                "Zero should be a Nat, but was used where a " <> show other <> " was expected"
check ctx (Add1 n) t =
    case t of
        TNat -> check ctx n TNat
        other ->
            failure $
                "Add1 should be a Nat, but was used where a " <> show other <> " was expected"
check ctx other t = do
    t' <- synth ctx other
    if t' == t
        then pure ()
        else failure $ "Expected " <> show t <> " but got " <> show t'

data Value
    = VZero
    | VAdd1 Value
    | VClosure (Env Value) Name Expr
    | VNeutral Ty Neutral
    deriving (Show)

data Neutral
    = NVar Name
    | NApp Neutral Normal
    | NRec Ty Neutral Normal Normal
    deriving (Show)

data Normal = Normal
    { normalType :: Ty
    , normalValue :: Value
    }
    deriving (Show)

eval :: Env Value -> Expr -> Value
eval env (Var x) =
    case lookupVar env x of
        Left msg -> error $ "Internal error: " <> show msg
        Right v -> v
eval env (Lambda x body) = VClosure env x body
eval env (App rator rand) = doApply (eval env rator) (eval env rand)
eval env Zero = VZero
eval env (Add1 n) = VAdd1 (eval env n)
eval env (Rec t tgt base step) = doRec t (eval env tgt) (eval env base) (eval env step)
eval env (Ann e t) = eval env e

doApply :: Value -> Value -> Value
doApply (VClosure env x body) arg = eval (extend env x arg) body
doApply (VNeutral (TArr t1 t2) neu) arg = VNeutral t2 (NApp neu (Normal t1 arg))
doApply _ _ = error "Internal error"

doRec :: Ty -> Value -> Value -> Value -> Value
doRec t VZero base step = base
doRec t (VAdd1 n) base step = doApply (doApply step n) (doRec t n base step)
doRec t (VNeutral TNat neu) base step =
    VNeutral t (NRec t neu (Normal t base) (Normal (TArr TNat (TArr t t)) step))
doRec _ _ _ _ = error "Internal error"

readBackNormal :: [Name] -> Normal -> Expr
readBackNormal used (Normal t v) = readBack used t v

freshen :: [Name] -> Name -> Name
freshen used x
    | x `elem` used = freshen used (nextName x)
    | otherwise = x
  where
    nextName :: Name -> Name
    nextName (Name x) = Name (x <> "'")

readBack :: [Name] -> Ty -> Value -> Expr
readBack used TNat VZero = Zero
readBack used TNat (VAdd1 pred) = Add1 (readBack used TNat pred)
readBack used (TArr t1 t2) fun =
    let x = freshen used (argName fun)
        xVal = VNeutral t1 (NVar x)
     in Lambda x (readBack used t2 (doApply fun xVal))
  where
    argName (VClosure _ x _) = x
    argName _ = Name "x"
readBack used t1 (VNeutral t2 neu) =
    -- Note: checking t1 and t2 for equality here is a good way to find bugs,
    -- but is not strictly necessary.
    if t1 == t2
        then readBackNeutral used neu
        else error "Internal error: mismatched types at readBackNeutral"
readBack _ _ _ = error "Internal error"

readBackNeutral :: [Name] -> Neutral -> Expr
readBackNeutral used (NVar x) = Var x
readBackNeutral used (NApp rator arg) = App (readBackNeutral used rator) (readBackNormal used arg)
readBackNeutral used (NRec t neu base step) =
    Rec t (readBackNeutral used neu) (readBackNormal used base) (readBackNormal used step)

type Defs = Env Normal

noDefs :: Defs
noDefs = initEnv

defsToContext :: Defs -> Context
defsToContext = fmap normalType

defsToEnv :: Defs -> Env Value
defsToEnv = fmap normalValue

normWithDefs :: Defs -> Expr -> Either Message Normal
normWithDefs defs e = do
    t <- synth (defsToContext defs) e
    let v = eval (defsToEnv defs) e
    pure $ Normal t v

addDefs :: Defs -> [(Name, Expr)] -> Either Message Defs
addDefs defs [] = pure defs
addDefs defs ((x, e) : more) = do
    norm <- normWithDefs defs e
    addDefs (extend defs x norm) more

definedNames :: Defs -> [Name]
definedNames (Env defs) = map fst defs

normWithTestDefs :: Expr -> Either Message Expr
normWithTestDefs e = do
    defs <-
        addDefs
            noDefs
            [
                ( Name "two"
                , Ann
                    (Add1 (Add1 Zero))
                    TNat
                )
            ,
                ( Name "three"
                , Ann
                    (Add1 (Add1 (Add1 Zero)))
                    TNat
                )
            ,
                ( Name "+"
                , Ann
                    ( Lambda
                        (Name "n")
                        ( Lambda
                            (Name "k")
                            ( Rec
                                TNat
                                (Var (Name "n"))
                                (Var (Name "k"))
                                ( Lambda
                                    (Name "pred")
                                    ( Lambda
                                        (Name "almostSum")
                                        (Add1 (Var (Name "almostSum")))
                                    )
                                )
                            )
                        )
                    )
                    (TArr TNat (TArr TNat TNat))
                )
            ]
    norm <- normWithDefs defs e
    pure $ readBackNormal (definedNames defs) norm

test1, test2, test3 :: Either Message Expr
test1 = normWithTestDefs (Var (Name "+"))
test2 =
    normWithTestDefs
        ( App
            (Var (Name "+"))
            (Var (Name "three"))
        )
test3 =
    normWithTestDefs
        ( App
            ( App
                (Var (Name "+"))
                (Var (Name "three"))
            )
            (Var (Name "two"))
        )
