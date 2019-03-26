{-# LANGUAGE GADTs, FlexibleContexts #-}



-- NAME -- Lane Gramling
-- KUID -- 2766765
-- Comments:
--    Known issue:
--      - AND operators seem only to return the boolean value of the first operand.
--        Not sure why this is, I have scoured around and I guess I can't find why.
--    Other than this, nothing else seems to break.
--
-- Instructions for use:
--    1) Load in p1-parser.hs
--    2) Evaluate an ABE from a string using
--          evalM (parseABE "<string parseable as AE>") (for base evaluator)
--          evalErr (parseABE "<string parseable as AE>") (for type-checking eval)
--          interpOptM (parseABE "<string parseable as AE>") (for base eval using optimizer)
--


-- Imports for Parsec

import Control.Monad
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Language
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Token


-- AST Definition

data TABE where
  TNum :: TABE
  TBool :: TABE
  deriving (Show,Eq)

data ABE where
  Num :: Int -> ABE
  Plus :: ABE -> ABE -> ABE
  Minus :: ABE -> ABE -> ABE
  Mult :: ABE -> ABE -> ABE
  Div :: ABE -> ABE -> ABE
  Boolean :: Bool -> ABE
  And :: ABE -> ABE -> ABE
  Leq :: ABE -> ABE -> ABE
  IsZero :: ABE -> ABE
  If :: ABE -> ABE -> ABE -> ABE
  deriving (Show,Eq)

-- AST Pretty Printer

pprint :: ABE -> String
pprint (Num n) = show n
pprint (Boolean b) = show b
pprint (Plus n m) = "(" ++ pprint n ++ " + " ++ pprint m ++ ")"
pprint (Minus n m) = "(" ++ pprint n ++ " - " ++ pprint m ++ ")"
pprint (Mult n m) = "(" ++ pprint n ++ " * " ++ pprint m ++ ")"
pprint (Div n m) = "(" ++ pprint n ++ " / " ++ pprint m ++ ")"
pprint (And n m) = "(" ++ pprint n ++ " && " ++ pprint m ++ ")"
pprint (Leq n m) = "(" ++ pprint n ++ " <= " ++ pprint m ++ ")"
pprint (IsZero m) = "(isZero " ++ pprint m ++ ")"
pprint (If c n m) = "(if " ++ pprint c ++ " then " ++ pprint n ++ " else " ++ pprint m ++ ")"


-- Parser (Requires ParserUtils and Parsec)

languageDef =
  javaStyle { identStart = letter
            , identLetter = alphaNum
            , reservedNames = [ "if0"
                              , "then"
                              , "else"
                              ]
            , reservedOpNames = [ "+","-","*","/"]
            }

lexer = makeTokenParser languageDef

inFix o c a = (Infix (reservedOp lexer o >> return c) a)
preFix o c = (Prefix (reservedOp lexer o >> return c))
postFix o c = (Postfix (reservedOp lexer o >> return c))

parseString p str =
  case parse p "" str of
    Left e -> error $ show e
    Right r -> r

expr :: Parser ABE
expr = buildExpressionParser opTable term

opTable = [ [ inFix "*" Mult AssocLeft
            , inFix "/" Div AssocLeft ]
          , [ inFix "+" Plus AssocLeft
            , inFix "-" Minus AssocLeft ]
          , [ inFix "<=" Leq AssocLeft
            , preFix "isZero" IsZero ]
          , [ inFix "&&" And AssocLeft ]
          ]

numExpr :: Parser ABE
numExpr = do i <- integer lexer
             return (Num (fromInteger i))

trueExpr :: Parser ABE
trueExpr = do i <- reserved lexer "true"
              return (Boolean True)

falseExpr :: Parser ABE
falseExpr = do i <- reserved lexer "false"
               return (Boolean False)

ifExpr :: Parser ABE
ifExpr = do reserved lexer "if"
            c <- expr
            reserved lexer "then"
            t <- expr
            reserved lexer "else"
            e <- expr
            return (If c t e)

term = parens lexer expr
       <|> numExpr
       <|> trueExpr
       <|> falseExpr
       <|> ifExpr

-- Parser invocation

parseABE = parseString expr



-- Lift Functions

-- Lift an Int operator to ABEs
liftNum :: (Int -> Int -> Int) -> ABE -> ABE -> ABE
liftNum op (Num l) (Num r) = (Num (op l r)) -- op identifies the operator

-- Lift an Int operator with Bool results to ABEs
liftNumToBool :: (Int -> Int -> Bool) -> ABE -> ABE -> ABE
liftNumToBool op (Num l) (Num r) = (Boolean (op l r)) -- op identifies the operator

-- Lift a Boolean Operator with Bool results to ABEs
liftBool :: (Bool -> Bool -> Bool) -> ABE -> ABE -> ABE
liftBool op (Boolean l) (Boolean r) = (Boolean (op l r)) -- op identifies the operator


-- Evaluation Functions

evalM :: ABE -> (Maybe ABE)
evalM (Num n) = if n >= 0 then Just (Num n) else Nothing
evalM (Boolean b) = Just (Boolean b)
evalM (Plus l r) = do a1 <- (evalM l)
                      a2 <- (evalM r)
                      return (liftNum (+) a1 a2)
evalM (Minus l r) = do a1 <- (evalM l)
                       a2 <- (evalM r)
                       case a1 of
                         (Num a11) -> case a2 of -- l-r<=0 case
                                        (Num a22) ->
                                            if ((a11-a22)<0) then Nothing else return (liftNum (-) a1 a2)
evalM (Mult l r) = do a1 <- (evalM l)
                      a2 <- (evalM r)
                      return (liftNum (*) a1 a2)
evalM (Div l r) = do a1 <- (evalM l)
                     a2 <- (evalM r)
                     if a2==(Num 0) then Nothing else return (liftNum (div) a1 a2) -- div/0 case
evalM (And l r) = do a1 <- (evalM l) -- Boolean Operands
                     a2 <- (evalM r)
                     return (liftBool (&&) a1 a2)
evalM (Leq l r) = do a1 <- (evalM l) -- Numeric Operands, Boolean Result
                     a2 <- (evalM r)
                     return (liftNumToBool (<=) a1 a2)
evalM (IsZero n) = do n1 <- (evalM n) -- Numeric Operand, Boolean Result
                      return (liftNumToBool (==) n1 (Num 0))
evalM (If c t e) = do (Boolean c1) <- (evalM c)
                      if c1 then evalM t else evalM e
evalM _ = Nothing -- Replace this with your interpreter

-- evalErr -- Evaluator which includes pattern matching of types as conditions
--              for continuing the evaluation; Cases act as guards which upon a
--              type mismatch will terminate the evaluation, returning Nothing.
--              (Dynamic error checking)
evalErr :: ABE -> (Maybe ABE)
evalErr (Num n) = if n >= 0 then Just (Num n) else Nothing
evalErr (Plus l r) = do ll <- (evalErr l)
                        rr <- (evalErr r)
                        case ll of
                          (Num ln) -> case rr of
                                        (Num rn) -> (return (Num (ln + rn)))
                                        _ -> Nothing
                          _ -> Nothing
evalErr (Minus l r) = do ll <- (evalErr l)
                         rr <- (evalErr r)
                         case ll of
                           (Num ln) -> case rr of -- l-r<=0 case
                                        (Num rn) -> if ((ln-rn)<0) then Nothing else return (Num (ln - rn))
                                        _ -> Nothing
                           _ -> Nothing
evalErr (Mult l r) = do ll <- (evalErr l)
                        rr <- (evalErr r)
                        case ll of
                          (Num ln) -> case rr of
                                        (Num rn) -> (return (Num (ln * rn)))
                                        _ -> Nothing
                          _ -> Nothing
evalErr (Div l r) = do ll <- (evalErr l)
                       rr <- (evalErr r)
                       case ll of
                         (Num ln) -> case rr of
                                      (Num rn) -> (if rn==0 then Nothing else return (Num (ln + rn)))
                                      _ -> Nothing
                         _ -> Nothing
evalErr (And l r) = do ll <- (evalErr l) -- Boolean operands
                       rr <- (evalErr r)
                       case ll of
                         (Boolean lb) -> case rr of
                                      (Boolean rb) -> (return (Boolean (lb && rb)))
                                      _ -> Nothing
                         _ -> Nothing
evalErr (Leq l r) = do ll <- (evalErr l) -- Numeric operands
                       rr <- (evalErr r)
                       case ll of
                         (Num ln) -> case rr of
                                      (Num rn) -> (return (Boolean (ln <= rn)))
                                      _ -> Nothing
                         _ -> Nothing
evalErr (IsZero n) = do nn <- (evalErr n) -- Numeric operand
                        case nn of
                          (Num n1) -> (return (Boolean (n1 == 0)))
                          _ -> Nothing
evalErr (If c t e) = do cc <- (evalErr c)
                        case cc of
                          (Boolean b) -> if b then (evalErr t) else (evalErr e)
                          _ -> Nothing
evalErr _ = Nothing -- Replace this with your interpreter

-- Type Derivation Function
typeofM :: ABE -> (Maybe TABE)
typeofM (Num n) = Just TNum
typeofM (Boolean b) = Just TBool
typeofM (Plus l r) = do TNum <- (typeofM l)
                        TNum <- (typeofM r)
                        return TNum
typeofM (Minus l r) = do TNum <- (typeofM l)
                         TNum <- (typeofM r)
                         return TNum
typeofM (Mult l r) = do TNum <- (typeofM l)
                        TNum <- (typeofM r)
                        return TNum
typeofM (Div l r) = do TNum <- (typeofM l)
                       TNum <- (typeofM r)
                       return TNum
typeofM (And l r) = do TBool <- (typeofM l) -- Boolean Operands
                       TBool <- (typeofM r)
                       return TBool
typeofM (Leq l r) = do TNum <- (typeofM l) -- Numeric Operands
                       TNum <- (typeofM r)
                       return TBool
typeofM (IsZero n) = do TNum <- (typeofM n) -- Numeric Operand
                        return TBool
typeofM (If c t e) = do c1 <- (typeofM c)
                        t1 <- (typeofM t)
                        e1 <- (typeofM e) -- Confirm then/else types match
                        if c1==TBool && t1==e1 then return t1 else Nothing
-- typeofM _ = Nothing


-- Combined interpreter
-- evalTypeM -- Takes in an ABE and guards the evaluator with the type checker.
evalTypeM :: ABE -> Maybe ABE
evalTypeM e = case (typeofM e) of
                Just _ -> (evalM e)
                Nothing -> Nothing
-- evalTypeM _ = Nothing


-- Optimizer
-- optimize -- Simplifies some reflexive expressions before evaluation.
optimize :: ABE -> ABE
optimize (Plus l (Num 0)) = l -- x + 0 -> x
optimize (If (Boolean true) t e) = t
optimize (If (Boolean false) t e) = e
optimize e = e


-- interpOptM -- Interprets an expression, making use of the optimizer.
interpOptM :: ABE -> Maybe ABE
interpOptM e = evalM (optimize e)
interpOptM _ = Nothing
