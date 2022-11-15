module UntypedLambdaCalculus where

import Relude

data Expr = Var Name | Lambda Name Expr | App Expr Expr deriving (Show)

data Value = VClosure (Env Value) Name Expr | VNeutral Neutral deriving (Show)

data Neutral = NVar Name | NApp Neutral Value deriving (Show)

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

extend :: Env val -> Name -> val -> Env val
extend (Env env) x v = Env ((x, v) : env)

eval :: Env Value -> Expr -> Either Message Value
eval env (Var x) = lookupVar env x
eval env (Lambda x body) = pure $ VClosure env x body
eval env (App rator rand) = do
    fun <- eval env rator
    arg <- eval env rand
    doApply fun arg

doApply :: Value -> Value -> Either Message Value
doApply (VClosure env x body) arg = eval (extend env x arg) body
doApply (VNeutral neu) arg = pure . VNeutral $ NApp neu arg

runProgram :: [(Name, Expr)] -> Expr -> Either Message Expr
runProgram defs expr = do
    env <- addDefs initEnv defs
    val <- eval env expr
    readBack (map fst defs) val
  where
    addDefs :: Env Value -> [(Name, Expr)] -> Either Message (Env Value)
    addDefs env [] = pure env
    addDefs env ((x, e) : defs) = do
        v <- eval env e
        addDefs (extend env x v) defs

test :: Either Message Expr
test = runProgram churchDefs (App (App (Var (Name "+")) (toChurch 2)) (toChurch 3))
  where
    churchDefs :: [(Name, Expr)]
    churchDefs =
        [
            ( Name "zero"
            , Lambda
                (Name "f")
                ( Lambda
                    (Name "x")
                    (Var (Name "x"))
                )
            )
        ,
            ( Name "add1"
            , Lambda
                (Name "n")
                ( Lambda
                    (Name "f")
                    ( Lambda
                        (Name "x")
                        ( App
                            (Var (Name "f"))
                            ( App
                                ( App
                                    (Var (Name "n"))
                                    (Var (Name "f"))
                                )
                                (Var (Name "x"))
                            )
                        )
                    )
                )
            )
        ,
            ( Name "+"
            , Lambda
                (Name "j")
                ( Lambda
                    (Name "k")
                    ( Lambda
                        (Name "f")
                        ( Lambda
                            (Name "x")
                            ( App
                                (App (Var (Name "j")) (Var (Name "f")))
                                ( App
                                    (App (Var (Name "k")) (Var (Name "f")))
                                    (Var (Name "x"))
                                )
                            )
                        )
                    )
                )
            )
        ]

    toChurch :: Integer -> Expr
    toChurch n
        | n <= 0 = Var $ Name "zero"
        | otherwise = App (Var $ Name "add1") . toChurch $ n - 1

freshen :: [Name] -> Name -> Name
freshen used x
    | x `elem` used = freshen used (nextName x)
    | otherwise = x
  where
    nextName :: Name -> Name
    nextName (Name x) = Name (x <> "'")

readBack :: [Name] -> Value -> Either Message Expr
readBack used (VNeutral (NVar x)) = pure $ Var x
readBack used (VNeutral (NApp fun arg)) = do
    rator <- readBack used $ VNeutral fun
    rand <- readBack used arg
    pure $ App rator rand
readBack used fun@(VClosure _ x _) = do
    let x' = freshen used x
    bodyVal <- doApply fun . VNeutral $ NVar x'
    bodyExpr <- readBack (x' : used) bodyVal
    pure $ Lambda x' bodyExpr

normalize :: Expr -> Either Message Expr
normalize expr = do
    val <- eval initEnv expr
    readBack [] val

main :: IO ()
main = print test
