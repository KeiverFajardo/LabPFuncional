module Lintings where

import AST
import LintTypes


--------------------------------------------------------------------------------
-- AUXILIARES
--------------------------------------------------------------------------------

-- Computa la lista de variables libres de una expresión
freeVariables :: Expr -> [Name]
--freeVariables = undefined
--------------------------CODIGO AGREGADO
freeVariables (Var x) = [x]
freeVariables (Lam x e) = filter (/= x) (freeVariables e)
freeVariables (App e1 e2) = freeVariables e1 ++ freeVariables e2
--freeVariables (Let x e1 e2) = freeVariables e1 ++ filter (/= x) (freeVariables e2)
freeVariables (Lit _) = []
freeVariables (Infix Add e1 e2) = freeVariables e1 ++ freeVariables e2
freeVariables (Infix Mult e1 e2) = freeVariables e1 ++ freeVariables e2
freeVariables (Infix Eq e1 e2) = freeVariables e1 ++ freeVariables e2
freeVariables (If cond th el) = freeVariables cond ++ freeVariables th ++ freeVariables el
--------------------------END CODIGO AGREGADO

--------------------------------------------------------------------------------
-- LINTINGS
--------------------------------------------------------------------------------
getExpr :: Expr -> Expr
getExpr = id


--------------------------------------------------------------------------------
-- Computación de constantes
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Reduce expresiones aritméticas/booleanas
-- Construye sugerencias de la forma (LintCompCst e r)
lintComputeConstant :: Linting Expr
--lintComputeConstant = undefined
--------------------------CODIGO AGREGADO
lintComputeConstant expr = case expr of
    Infix Add (Lit (LitInt n1)) (Lit (LitInt n2)) 
        | n1 + n2 >= 0 -> return (Lit (LitInt (n1 + n2)), [LintCompCst expr (Lit (LitInt (n1 + n2)))])
        | otherwise -> return (expr, [])
    
    Infix Sub (Lit (LitInt n1)) (Lit (LitInt n2)) 
        | n1 - n2 >= 0 -> return (Lit (LitInt (n1 - n2)), [LintCompCst expr (Lit (LitInt (n1 - n2)))])
        | otherwise -> return (expr, [])
    
    Infix Mult (Lit (LitInt n1)) (Lit (LitInt n2)) 
        | n1 * n2 >= 0 -> return (Lit (LitInt (n1 * n2)), [LintCompCst expr (Lit (LitInt (n1 * n2)))])
        | otherwise -> return (expr, [])

    Infix Div (Lit (LitInt n1)) (Lit (LitInt n2)) 
        | n2 == 0 -> return (expr, [])  -- No se sugiere en caso de división por cero
        | otherwise -> return (Lit (LitInt (n1 `div` n2)), [LintCompCst expr (Lit (LitInt (n1 `div` n2)))])
    
    Infix And (Lit (LitBool b1)) (Lit (LitBool b2)) -> 
        return (Lit (LitBool (b1 && b2)), [LintCompCst expr (Lit (LitBool (b1 && b2)))])
    
    Infix Or (Lit (LitBool b1)) (Lit (LitBool b2)) -> 
        return (Lit (LitBool (b1 || b2)), [LintCompCst expr (Lit (LitBool (b1 || b2)))])
    
    -- Otras combinaciones no deben ser evaluadas
    _ -> return (expr, [])
--------------------------END CODIGO AGREGADO

--------------------------------------------------------------------------------
-- Eliminación de chequeos redundantes de booleanos
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Elimina chequeos de la forma e == True, True == e, e == False y False == e
-- Construye sugerencias de la forma (LintBool e r)
lintRedBool :: Linting Expr
--lintRedBool = undefined
--------------------------CODIGO AGREGADO
lintRedBool = do
  expr <- getExpr
  case expr of
    Infix Eq e (Lit True) -> return e
    Infix Eq (Lit True) e -> return e
    Infix Eq e (Lit False) -> return (If e (Lit 0) (Lit 1))
    Infix Eq (Lit False) e -> return (If e (Lit 1) (Lit 0))
    _ -> return expr
--------------------------END CODIGO AGREGADO

--------------------------------------------------------------------------------
-- Eliminación de if redundantes
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Sustitución de if con literal en la condición por la rama correspondiente
-- Construye sugerencias de la forma (LintRedIf e r)
lintRedIfCond :: Linting Expr
--lintRedIfCond = undefined
--------------------------CODIGO AGREGADO
lintRedIfCond = do
  expr <- getExpr
  case expr of
    If (Lit True) th _ -> return th
    If (Lit False) _ el -> return el
    _ -> return expr
--------------------------END CODIGO AGREGADO

--------------------------------------------------------------------------------
-- Sustitución de if por conjunción entre la condición y su rama _then_
-- Construye sugerencias de la forma (LintRedIf e r)
lintRedIfAnd :: Linting Expr
--lintRedIfAnd = undefined
--------------------------CODIGO AGREGADO
lintRedIfAnd = do
  expr <- getExpr
  case expr of
    If cond th el -> return $ If (Add cond (Lit 1)) th el
    _ -> return expr
--------------------------END CODIGO AGREGADO

--------------------------------------------------------------------------------
-- Sustitución de if por disyunción entre la condición y su rama _else_
-- Construye sugerencias de la forma (LintRedIf e r)
lintRedIfOr :: Linting Expr
--lintRedIfOr = undefined
--------------------------CODIGO AGREGADO
lintRedIfOr = do
  expr <- getExpr
  case expr of
    If cond th el -> return $ If (Add cond (Lit 0)) th el
    _ -> return expr
--------------------------END CODIGO AGREGADO

--------------------------------------------------------------------------------
-- Chequeo de lista vacía
--------------------------------------------------------------------------------
-- Sugiere el uso de null para verificar si una lista es vacía
-- Construye sugerencias de la forma (LintNull e r)

lintNull :: Linting Expr
--lintNull = undefined
--------------------------CODIGO AGREGADO
lintNull expr = case expr of
    Infix Eq (Lit (Lit [])) e -> 
        return (App (Var "null") e, [LintNull expr (App (Var "null") e)])  -- Reemplaza e == []
    
    Infix Eq e (Lit (Lit [])) -> 
        return (App (Var "null") e, [LintNull expr (App (Var "null") e)])  -- Reemplaza [] == e
    
    Infix Eq (App (Var "length") e) (Lit (LitInt 0)) -> 
        return (App (Var "null") e, [LintNull expr (App (Var "null") e)])  -- Reemplaza length e == 0
    
    Infix Eq (Lit (LitInt 0)) (App (Var "length") e) -> 
        return (App (Var "null") e, [LintNull expr (App (Var "null") e)])  -- Reemplaza 0 == length e
    
    App (Var "length") e -> 
        return (e, [LintNull expr (App (Var "null") e)])  -- Sugerencia de reemplazo para length

    -- Procesamos recursivamente subexpresiones
    _ -> return (expr, [])
--------------------------END CODIGO AGREGADO

--------------------------------------------------------------------------------
-- Eliminación de la concatenación
--------------------------------------------------------------------------------
-- se aplica en casos de la forma (e:[] ++ es), reemplazando por (e:es)
-- Construye sugerencias de la forma (LintAppend e r)

lintAppend :: Linting Expr
--lintAppend = undefined
--------------------------CODIGO AGREGADO
lintAppend = do
  expr <- getExpr
  case expr of
    App (App (Var "++") (App (Var ":") [e, []])) es -> return (App (Var ":") [e, es])
    _ -> return expr
--------------------------END CODIGO AGREGADO

--------------------------------------------------------------------------------
-- Composición
--------------------------------------------------------------------------------
-- se aplica en casos de la forma (f (g t)), reemplazando por (f . g) t
-- Construye sugerencias de la forma (LintComp e r)

lintComp :: Linting Expr
--lintComp = undefined
--------------------------CODIGO AGREGADO
lintComp = do
  expr <- getExpr
  case expr of
    App f (App g t) -> return $ App (App (Var ".") [f, g]) t
    _ -> return expr
--------------------------END CODIGO AGREGADO

--------------------------------------------------------------------------------
-- Eta Redución
--------------------------------------------------------------------------------
-- se aplica en casos de la forma \x -> e x, reemplazando por e
-- Construye sugerencias de la forma (LintEta e r)

lintEta :: Linting Expr
--lintEta = undefined
--------------------------CODIGO AGREGADO
lintEta = do
  expr <- getExpr
  case expr of
    Lam x (App e (Var x')) | x == x' -> return e
    _ -> return expr
--------------------------END CODIGO AGREGADO

--------------------------------------------------------------------------------
-- Eliminación de recursión con map
--------------------------------------------------------------------------------

-- Sustituye recursión sobre listas por `map`
-- Construye sugerencias de la forma (LintMap f r)
lintMap :: Linting FunDef
lintMap = undefined
-------------------------- CODIGO AGREGADO
--------------------------END CODIGO AGREGADO

--------------------------------------------------------------------------------
-- Combinación de Lintings
--------------------------------------------------------------------------------


-- Dada una transformación a nivel de expresión, se construye
-- una transformación a nivel de función
liftToFunc :: Linting Expr -> Linting FunDef
--liftToFunc = undefined
--------------------------CODIGO AGREGADO
liftToFunc lintExpr = do
  (FunDef name body) <- getFuncDef
  expr <- lintExpr body
  return $ FunDef name expr
--------------------------END CODIGO AGREGADO

-- encadenar transformaciones:
(>==>) :: Linting a -> Linting a -> Linting a
--lint1 >==> lint2 = undefined
--------------------------CODIGO AGREGADO
lint1 >==> lint2 = do
  result1 <- lint1
  result2 <- lint2
  return result2
--------------------------END CODIGO AGREGADO

-- aplica las transformaciones 'lints' repetidas veces y de forma incremental,
-- hasta que ya no generen más cambios en 'func'
lintRec :: Linting a -> Linting a
--lintRec lints func = undefined
--------------------------CODIGO AGREGADO
lintRec lints func = do
  result <- lints func
  if result == func
    then return result
    else lintRec lints result
--------------------------END CODIGO AGREGADO
