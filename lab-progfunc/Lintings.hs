--------------------------------------------------------------------------------
-- GRUPO 143
-- ESTUDIANTES
-- KEIVER FAJARDO 6.428.559-9
-- JUAN IGNACIO CABRERA 5.478.549-4
--------------------------------------------------------------------------------

module Lintings where

import AST
import LintTypes


--------------------------------------------------------------------------------
-- AUXILIARES
--------------------------------------------------------------------------------

-- Computa la lista de variables libres de una expresión
freeVariables :: Expr -> [Name]
freeVariables (Var x) = [x]
freeVariables (Lit _) = []
freeVariables (Lam x e) = filter (/= x) (freeVariables e)
freeVariables (App e1 e2) = freeVariables e1 ++ freeVariables e2
freeVariables (Infix _ e1 e2) =  freeVariables e1 ++ freeVariables e2
freeVariables (If cond th el) = freeVariables cond ++ freeVariables th ++ freeVariables el
freeVariables (Case e1 e2 (n1, n2, e3)) =
    freeVariables e1 ++ freeVariables e2 ++ filter (/= n1) (filter (/= n2)  (freeVariables e3))

--------------------------------------------------------------------------------
-- LINTINGS
--------------------------------------------------------------------------------


--------------------------------------------------------------------------------
-- Computación de constantes
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Reduce expresiones aritméticas/booleanas
-- Construye sugerencias de la forma (LintCompCst e r) 

lintComputeConstant :: Linting Expr
lintComputeConstant expr = case expr of
    Infix Add (Lit (LitInt x)) (Lit (LitInt y)) -> 
        let result = Lit (LitInt (x + y))
        in (result, [LintCompCst expr result])

    Infix Sub (Lit (LitInt x)) (Lit (LitInt y)) -> 
        let result = if x >= y then Lit (LitInt (x - y)) else expr
        in if x >= y then (result, [LintCompCst expr result]) else (expr, [])

    Infix Mult (Lit (LitInt x)) (Lit (LitInt y)) -> 
        let result = Lit (LitInt (x * y))
        in (result, [LintCompCst expr result])

    Infix Div (Lit (LitInt x)) (Lit (LitInt y)) -> 
        if y /= 0 
        then let result = Lit (LitInt (x `div` y))
            in (result, [LintCompCst expr result])
        else (expr, [])

    Infix And (Lit (LitBool x)) (Lit (LitBool y)) -> 
        let result = Lit (LitBool (x && y))
        in (result, [LintCompCst expr result])

    Infix Or (Lit (LitBool x)) (Lit (LitBool y)) -> 
        let result = Lit (LitBool (x || y))
        in (result, [LintCompCst expr result])

    -- Caso para lambdas: recorrer el cuerpo de la lambda
    App e1 e2 -> 
        let (e1', suggestions1) = lintComputeConstant e1
            (e2', suggestions2) = lintComputeConstant e2
        in (App e1' e2', suggestions1 ++ suggestions2)

    Lam name body ->
        let (body', suggestions) = lintComputeConstant body
        in (Lam name body', suggestions)

    If e1 e2 e3 -> 
        let (e1', suggestions1) = lintComputeConstant e1
            (e2', suggestions2) = lintComputeConstant e2
            (e3', suggestions3) = lintComputeConstant e3
        in (If e1' e2' e3', suggestions1 ++ suggestions2 ++ suggestions3)

    Infix op left right ->
        let (left', suggestionsLeft) = lintComputeConstant left
            (right', suggestionsRight) = lintComputeConstant right
            simplifiedExpr = Infix op left' right'
        in if simplifiedExpr /= expr
            then let (finalExpr, finalSuggestions) = lintComputeConstant simplifiedExpr
             in (finalExpr, suggestionsLeft ++ suggestionsRight ++ finalSuggestions)
            else (expr, suggestionsLeft ++ suggestionsRight)

    Case expr1 expr2 (name1, name2, expr3) -> 
        let (expr1', suggestions1) = lintComputeConstant expr1
            (expr2', suggestions2) = lintComputeConstant expr2
            (expr3', suggestions3) = lintComputeConstant expr3
        in (Case expr1' expr2' (name1, name2, expr3'), suggestions1 ++ suggestions2 ++ suggestions3)

    -- Caso Base: Expresión que no se simplifica
    _ -> (expr, [])

--------------------------------------------------------------------------------
-- Eliminación de chequeos redundantes de booleanos
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Elimina chequeos de la forma e == True, True == e, e == False y False == e
-- Construye sugerencias de la forma (LintBool e r)
lintRedBool :: Linting Expr
lintRedBool expr = case expr of
    -- Expresiones de la forma e == True
    Infix Eq e (Lit (LitBool True)) -> 
        let (e', suggestions) = lintRedBool e
        in (e', suggestions ++ [LintBool expr e'])

    -- Expresiones de la forma True == e
    Infix Eq (Lit (LitBool True)) e -> 
        let (e', suggestions) = lintRedBool e
        in (e', suggestions ++ [LintBool expr e'])

    -- Expresiones de la forma e == False
    Infix Eq e (Lit (LitBool False)) -> 
        let (e', suggestions) = lintRedBool e
            result = App (Var "not") e'
        in (result, suggestions ++ [LintBool expr result])

    -- Expresiones de la forma False == e
    Infix Eq (Lit (LitBool False)) e -> 
        let (e', suggestions) = lintRedBool e
            result = App (Var "not") e'
        in (result, suggestions ++ [LintBool expr result])

    App e1 e2 -> 
        let (e1', suggestions1) = lintRedBool e1
            (e2', suggestions2) = lintRedBool e2
        in (App e1' e2', suggestions1 ++ suggestions2)

    Lam name body ->
        let (body', suggestions) = lintRedBool body
        in (Lam name body', suggestions)

    If e1 e2 e3 -> 
        let (e1', suggestions1) = lintRedBool e1
            (e2', suggestions2) = lintRedBool e2
            (e3', suggestions3) = lintRedBool e3
        in (If e1' e2' e3', suggestions1 ++ suggestions2 ++ suggestions3)

    Infix op left right -> 
        let (left', suggestionsLeft) = lintRedBool left
            (right', suggestionsRight) = lintRedBool right
        in (Infix op left' right', suggestionsLeft ++ suggestionsRight)

    Case expr1 expr2 (name1, name2, expr3) -> 
        let (expr1', suggestions1) = lintRedBool expr1
            (expr2', suggestions2) = lintRedBool expr2
            (expr3', suggestions3) = lintRedBool expr3
        in (Case expr1' expr2' (name1, name2, expr3'), suggestions1 ++ suggestions2 ++ suggestions3)

    _ -> (expr, [])


--------------------------------------------------------------------------------
-- Eliminación de if redundantes
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Sustitución de if con literal en la condición por la rama correspondiente
-- Construye sugerencias de la forma (LintRedIf e r) 
lintRedIfCond :: Linting Expr
lintRedIfCond expr = case expr of
    If (Lit (LitBool False)) (Lit (LitInt x)) (Lit (LitInt y)) ->
        let result = (Lit (LitInt y))
        in (result, [LintRedIf expr result])

    If (Lit (LitBool True)) (Lit (LitInt x)) (Lit (LitInt y)) ->
        let result = (Lit (LitInt x))
        in (result, [LintRedIf expr result])
    
    If (Lit (LitBool True)) (Lit (LitBool x)) (Lit (LitBool y)) ->
        let result = (Lit (LitBool x))
        in (result, [LintRedIf expr result])

    If (Lit (LitBool True)) (Lit (LitInt y)) (Var x) ->
        let result = (Lit (LitInt y))
        in (result, [LintRedIf expr result])

    If (Lit (LitBool True)) (Infix Add (Var w) (Lit (LitInt x))) (Lit (LitInt y)) ->
        let result = (Infix Add (Var w) (Lit (LitInt x)))
        in (result, [LintRedIf expr result])
    
    If (Lit (LitBool False)) (Var z) (Lit LitNil) ->
        let result = (Lit LitNil)
        in (result, [LintRedIf expr result])
    
    If (Lit (LitBool False)) (Lit LitNil) e1 ->
        let (e1', suggestions2) = lintRedIfCond e1
        in (e1', suggestions2 ++ [LintRedIf (If (Lit (LitBool False)) (Lit LitNil) e1') e1'])

    If (Lit (LitBool False)) e1 e2 ->
        let (e2', suggestions2) = lintRedIfCond e2
        in (e2', suggestions2 ++ [LintRedIf (If (Lit (LitBool False)) e1 e2') e2'])

    If (Lit (LitBool True)) e1 (Var z) ->
        let (e1', suggestions2) = lintRedIfCond e1
        in (e1', suggestions2 ++ [LintRedIf (If (Lit (LitBool True)) e1' (Var z)) e1'])

    If (Lit (LitBool True)) e1 e2 ->
        let (e1', suggestions2) = lintRedIfCond e1
        in (e1', suggestions2 ++ [LintRedIf (If (Lit (LitBool True)) e1' e2) e1'])

    Infix Add (Var x) other -> 
        let (simplifiedThen, suggestionsThen) = lintRedIfCond other
        in (Infix Add (Var x) simplifiedThen, suggestionsThen)

    Infix Add (Lit (LitInt y)) other -> 
        let (simplifiedThen, suggestionsThen) = lintRedIfCond other
        in (Infix Add (Lit (LitInt y)) simplifiedThen, suggestionsThen)

    Infix Add other (Lit (LitInt y)) -> 
        let (simplifiedThen, suggestionsThen) = lintRedIfCond other
        in (Infix Add simplifiedThen (Lit (LitInt y)), suggestionsThen)

    Infix op e2 e3 ->
        let (e2', suggestions2) = lintRedIfCond e2
            (e3', suggestions3) = lintRedIfCond e3
        in (Infix op e2' e3', suggestions2 ++ suggestions3)
   
    Lam name body ->
        let (body', suggestions) = lintRedIfCond body
        in (Lam name body', suggestions)

    App e1 e2 -> 
        let (e1', suggestions1) = lintRedIfCond e1
            (e2', suggestions2) = lintRedIfCond e2
        in (App e1' e2', suggestions1 ++ suggestions2)

    If e1 e2 e3 -> 
        let (e1', suggestions1) = lintRedIfCond e1
            (e2', suggestions2) = lintRedIfCond e2
            (e3', suggestions3) = lintRedIfCond e3
        in (If e1' e2' e3', suggestions1 ++ suggestions2 ++ suggestions3)

    Case expr1 expr2 (name1, name2, expr3) -> 
        let (expr1', suggestions1) = lintRedIfCond expr1
            (expr2', suggestions2) = lintRedIfCond expr2
            (expr3', suggestions3) = lintRedIfCond expr3
        in (Case expr1' expr2' (name1, name2, expr3'), suggestions1 ++ suggestions2 ++ suggestions3)

    _ -> (expr, [])
    
--------------------------------------------------------------------------------
-- Sustitución de if por conjunción entre la condición y su rama _then_
-- Construye sugerencias de la forma (LintRedIf e r)
lintRedIfAnd :: Linting Expr
lintRedIfAnd expr = case expr of
    -- Caso: if c then e else False => c && e
    If cond e (Lit (LitBool False)) -> 
        let (cond', suggestionsCond) = lintRedIfAnd cond  -- Simplificamos la condición
            (e', suggestionsE) = lintRedIfAnd e  -- Simplificamos la rama `then` si es necesario
            result = Infix And cond' e'  -- Reemplazamos por conjunción
        in (result, suggestionsCond ++ suggestionsE ++ [LintRedIf expr result])

    App e1 e2 -> 
        let (e1', suggestions1) = lintRedIfAnd e1
            (e2', suggestions2) = lintRedIfAnd e2
        in (App e1' e2', suggestions1 ++ suggestions2)

    Lam name body ->
        let (body', suggestions) = lintRedIfAnd body
        in (Lam name body', suggestions)

    If e1 e2 e3 -> 
        let (e1', suggestions1) = lintRedIfAnd e1
            (e2', suggestions2) = lintRedIfAnd e2
            (e3', suggestions3) = lintRedIfAnd e3
        in (If e1' e2' e3', suggestions1 ++ suggestions2 ++ suggestions3)

    Infix op e2 e3 ->
        let (e2', suggestions2) = lintRedIfAnd e2
            (e3', suggestions3) = lintRedIfAnd e3
        in (Infix op e2' e3', suggestions2 ++ suggestions3)

    Case expr1 expr2 (name1, name2, expr3) -> 
        let (expr1', suggestions1) = lintRedIfAnd expr1
            (expr2', suggestions2) = lintRedIfAnd expr2
            (expr3', suggestions3) = lintRedIfAnd expr3
        in (Case expr1' expr2' (name1, name2, expr3'), suggestions1 ++ suggestions2 ++ suggestions3)

    _ -> (expr, [])


--------------------------------------------------------------------------------
-- Sustitución de if por disyunción entre la condición y su rama _else_
-- Construye sugerencias de la forma (LintRedIf e r)
lintRedIfOr :: Linting Expr
lintRedIfOr expr = case expr of
    -- Caso: if c then True else e => c || e
    If cond (Lit (LitBool True)) e -> 
        let (cond', suggestionsCond) = lintRedIfOr cond  -- Simplificamos la condición
            (e', suggestionsE) = lintRedIfOr e  -- Simplificamos la rama `else` si es necesario
            result = Infix Or cond' e'  -- Reemplazamos por disyunción
        in (result, suggestionsCond ++ suggestionsE ++ [LintRedIf expr result])

    App e1 e2 -> 
        let (e1', suggestions1) = lintRedIfOr e1
            (e2', suggestions2) = lintRedIfOr e2
        in (App e1' e2', suggestions1 ++ suggestions2)

    Lam name body ->
        let (body', suggestions) = lintRedIfOr body
        in (Lam name body', suggestions)

    If e1 e2 e3 -> 
        let (e1', suggestions1) = lintRedIfOr e1
            (e2', suggestions2) = lintRedIfOr e2
            (e3', suggestions3) = lintRedIfOr e3
        in (If e1' e2' e3', suggestions1 ++ suggestions2 ++ suggestions3)

    Infix op e2 e3 ->
        let (e2', suggestions2) = lintRedIfOr e2
            (e3', suggestions3) = lintRedIfOr e3
        in (Infix op e2' e3', suggestions2 ++ suggestions3)

    Case expr1 expr2 (name1, name2, expr3) -> 
        let (expr1', suggestions1) = lintRedIfOr expr1
            (expr2', suggestions2) = lintRedIfOr expr2
            (expr3', suggestions3) = lintRedIfOr expr3
        in (Case expr1' expr2' (name1, name2, expr3'), suggestions1 ++ suggestions2 ++ suggestions3)

    _ -> (expr, [])



--------------------------------------------------------------------------------
-- Chequeo de lista vacía
--------------------------------------------------------------------------------
-- Sugiere el uso de null para verificar si una lista es vacía
-- Construye sugerencias de la forma (LintNull e r) 

lintNull :: Linting Expr
lintNull expr = case expr of
    -- Caso: length e == 0 => null e
    Infix Eq (App (Var "length") e) (Lit (LitInt 0)) -> 
        let (e', suggestionsE) = lintNull e  -- Simplificamos la lista
            result = App (Var "null") e'  -- Reemplazamos por null
        in (result, suggestionsE ++ [LintNull expr result])

    -- Caso: 0 == length e => null e
    Infix Eq (Lit (LitInt 0)) (App (Var "length") e) -> 
        let (e', suggestionsE) = lintNull e  -- Simplificamos la lista
            result = App (Var "null") e'  -- Reemplazamos por null
        in (result, suggestionsE ++ [LintNull expr result])

    -- Caso: e == [] => null e
    Infix Eq e (Lit LitNil) -> 
        let (e', suggestionsE) = lintNull e  -- Simplificamos la lista
            result = App (Var "null") e'  -- Reemplazamos por null
        in (result, suggestionsE ++ [LintNull expr result])

    -- Caso: [] == e => null e
    Infix Eq (Lit LitNil) e -> 
        let (e', suggestionsE) = lintNull e  -- Simplificamos la lista
            result = App (Var "null") e'  -- Reemplazamos por null
        in (result, suggestionsE ++ [LintNull expr result])

    App e1 e2 -> 
        let (e1', suggestions1) = lintNull e1
            (e2', suggestions2) = lintNull e2
        in (App e1' e2', suggestions1 ++ suggestions2)

    Lam name body ->
        let (body', suggestions) = lintNull body
        in (Lam name body', suggestions)

    If e1 e2 e3 -> 
        let (e1', suggestions1) = lintNull e1
            (e2', suggestions2) = lintNull e2
            (e3', suggestions3) = lintNull e3
        in (If e1' e2' e3', suggestions1 ++ suggestions2 ++ suggestions3)

    Infix op e2 e3 ->
        let (e2', suggestions2) = lintNull e2
            (e3', suggestions3) = lintNull e3
        in (Infix op e2' e3', suggestions2 ++ suggestions3)

    Case expr1 expr2 (name1, name2, expr3) -> 
        let (expr1', suggestions1) = lintNull expr1
            (expr2', suggestions2) = lintNull expr2
            (expr3', suggestions3) = lintNull expr3
        in (Case expr1' expr2' (name1, name2, expr3'), suggestions1 ++ suggestions2 ++ suggestions3)

    _ -> (expr, [])


--------------------------------------------------------------------------------
-- Eliminación de la concatenación
--------------------------------------------------------------------------------
-- se aplica en casos de la forma (e:[] ++ es), reemplazando por (e:es)
-- Construye sugerencias de la forma (LintAppend e r) 

lintAppend :: Linting Expr
lintAppend expr = case expr of
    -- Caso: e : [] ++ es => e : es
    Infix Append (Infix Cons e (Lit LitNil)) es -> 
        let (e', suggestionsE) = lintAppend e  -- Recursivamente simplificamos la lista `es`
            (es', suggestionsES) = lintAppend es
            result = Infix Cons e' es'  -- Usamos Infix Cons directamente para e : es
            expr' = (Infix Append (Infix Cons e' (Lit LitNil)) es')
        in (result, suggestionsE ++ suggestionsES ++ [LintAppend expr' result])
    
    -- Caso general de `Append` para evaluar recursivamente `e1` y `e2`
    Infix Append e1 e2 -> 
        let (e1', suggestions1) = lintAppend e1
            (e2', suggestions2) = lintAppend e2
            simplifiedExpr = Infix Append e1' e2'
        in if simplifiedExpr /= expr
           then (simplifiedExpr, suggestions1 ++ suggestions2 ++ [LintAppend expr simplifiedExpr])
           else (expr, suggestions1 ++ suggestions2)

    App e1 e2 -> 
        let (e1', suggestions1) = lintAppend e1
            (e2', suggestions2) = lintAppend e2
        in (App e1' e2', suggestions1 ++ suggestions2)

    Lam name body ->
        let (body', suggestions) = lintAppend body
        in (Lam name body', suggestions)

    If e1 e2 e3 -> 
        let (e1', suggestions1) = lintAppend e1
            (e2', suggestions2) = lintAppend e2
            (e3', suggestions3) = lintAppend e3
        in (If e1' e2' e3', suggestions1 ++ suggestions2 ++ suggestions3)

    Infix op e2 e3 ->
        let (e2', suggestions2) = lintAppend e2
            (e3', suggestions3) = lintAppend e3
        in (Infix op e2' e3', suggestions2 ++ suggestions3)

    Case expr1 expr2 (name1, name2, expr3) -> 
        let (expr1', suggestions1) = lintAppend expr1
            (expr2', suggestions2) = lintAppend expr2
            (expr3', suggestions3) = lintAppend expr3
        in (Case expr1' expr2' (name1, name2, expr3'), suggestions1 ++ suggestions2 ++ suggestions3)

    _ -> (expr, [])

--------------------------------------------------------------------------------
-- Composición
--------------------------------------------------------------------------------
-- se aplica en casos de la forma (f (g t)), reemplazando por (f . g) t
-- Construye sugerencias de la forma (LintComp e r) 
lintComp :: Linting Expr
lintComp expr = case expr of
    App e1 e2 -> 
        let (e1', suggestionsE1) = lintComp e1
            (e2', suggestionsE2) = lintComp e2
            simplifiedExpr = App e1' e2'
        in case e2' of
            App left right -> 
                let newResult = App (Infix Comp e1' left) right
                in (newResult, suggestionsE1 ++ suggestionsE2 ++ [LintComp simplifiedExpr newResult])
            _ -> (simplifiedExpr, suggestionsE1 ++ suggestionsE2)
    
    Infix op e2 e3 ->
        let (e2', suggestions2) = lintComp e2
            (e3', suggestions3) = lintComp e3
        in (Infix op e2' e3', suggestions2 ++ suggestions3)

    Lam name body ->
        let (body', suggestions) = lintComp body
        in (Lam name body', suggestions)

    If e1 e2 e3 -> 
        let (e1', suggestions1) = lintComp e1
            (e2', suggestions2) = lintComp e2
            (e3', suggestions3) = lintComp e3
        in (If e1' e2' e3', suggestions1 ++ suggestions2 ++ suggestions3)

    Case expr1 expr2 (name1, name2, expr3) -> 
        let (expr1', suggestions1) = lintComp expr1
            (expr2', suggestions2) = lintComp expr2
            (expr3', suggestions3) = lintComp expr3
        in (Case expr1' expr2' (name1, name2, expr3'), suggestions1 ++ suggestions2 ++ suggestions3)

    _ -> (expr, [])

    
--------------------------------------------------------------------------------
-- Eta Redución
--------------------------------------------------------------------------------
-- se aplica en casos de la forma \x -> e x, reemplazando por e
-- Construye sugerencias de la forma (LintEta e r)
-- Propaga las variables libres desde expresiones internas
lintEta :: Linting Expr
lintEta expr = case expr of
    Lam name body ->
        let (body', suggestions) = lintEta body
        in case body' of
            App e1 (Var name') ->
                if name' == name && not (name `elem` freeVariables e1)
                    then (e1, suggestions ++ [LintEta (Lam name body') e1])
                else (Lam name body', suggestions)
            _ -> (Lam name body', suggestions)
    
    App e1 e2 -> 
        let (e1', suggestions1) = lintEta e1
            (e2', suggestions2) = lintEta e2
        in (App e1' e2', suggestions1 ++ suggestions2)

    If e1 e2 e3 -> 
        let (e1', suggestions1) = lintEta e1
            (e2', suggestions2) = lintEta e2
            (e3', suggestions3) = lintEta e3
        in (If e1' e2' e3', suggestions1 ++ suggestions2 ++ suggestions3)

    Infix op e2 e3 ->
        let (e2', suggestions2) = lintEta e2
            (e3', suggestions3) = lintEta e3
        in (Infix op e2' e3', suggestions2 ++ suggestions3)

    Case expr1 expr2 (name1, name2, expr3) -> 
        let (expr1', suggestions1) = lintEta expr1
            (expr2', suggestions2) = lintEta expr2
            (expr3', suggestions3) = lintEta expr3
        in (Case expr1' expr2' (name1, name2, expr3'), suggestions1 ++ suggestions2 ++ suggestions3)

    _ -> (expr, [])

--------------------------------------------------------------------------------
-- Eliminación de recursión con map
--------------------------------------------------------------------------------

-- Sustituye recursión sobre listas por `map`
-- Construye sugerencias de la forma (LintMap f r)
lintMap :: Linting FunDef
lintMap (FunDef name expr) = 
    let (expr', suggestions) = lintMapExpr name expr
    in (FunDef name expr', suggestions)

-- Definición de lintMapExpr para operar en Expr, con el nombre de la función original
lintMapExpr :: Name -> Linting Expr
lintMapExpr name expr = case expr of
    -- Detecta el patrón \ls -> case ls of [] -> []; (x : xs) -> expr : <func> xs
    Lam l (Case (Var l') (Lit LitNil) (x, xs, Infix Cons (e1) (App (Var func) (Var xs'))))
        | l == l' && xs == xs'&& name == func && not (l `elem` freeVariables (e1)) && not (xs `elem` freeVariables (e1)) && not (func `elem` freeVariables (e1)) -> 
            let -- Identificamos la función recursiva
                result = App (Var "map") (Lam x e1)  -- Reemplazamos con la llamada a map
                suggestion = LintMap (FunDef name expr) (FunDef name result)
            in (result, [suggestion])

    Lam n body -> 
        let (body', suggestions) = lintMapExpr name body
        in (Lam n body', suggestions)

    App e1 e2 -> 
        let (e1', suggestions1) = lintMapExpr name e1
            (e2', suggestions2) = lintMapExpr name e2
        in (App e1' e2', suggestions1 ++ suggestions2)

    Infix op e1 e2 -> 
        let (e1', suggestions1) = lintMapExpr name e1
            (e2', suggestions2) = lintMapExpr name e2
        in (Infix op e1' e2', suggestions1 ++ suggestions2)

    Case e1 e2 (n1, n2, e3) -> 
        let (e1', suggestions1) = lintMapExpr name e1
            (e2', suggestions2) = lintMapExpr name e2
            (e3', suggestions3) = lintMapExpr name e3
        in (Case e1' e2' (n1, n2, e3'), suggestions1 ++ suggestions2 ++ suggestions3)

    If e1 e2 e3 -> 
        let (e1', suggestions1) = lintMapExpr name e1
            (e2', suggestions2) = lintMapExpr name e2
            (e3', suggestions3) = lintMapExpr name e3
        in (If e1' e2' e3', suggestions1 ++ suggestions2 ++ suggestions3)

    _ -> (expr, [])


--------------------------------------------------------------------------------
-- Combinación de Lintings
--------------------------------------------------------------------------------

-- Dada una transformación a nivel de expresión, se construye
-- una transformación a nivel de función

liftToFunc :: Linting Expr -> Linting FunDef
liftToFunc lintExpr (FunDef name expr) = 
    let (newExpr, suggestions) = lintExpr expr
    in (FunDef name newExpr, suggestions)


-- encadenar transformaciones:
(>==>) :: Linting a -> Linting a -> Linting a
lint1 >==> lint2 = \expr -> 
    let (e', ls) = lint1 expr 
        (e'', ls') = lint2 e'   
    in (e'', ls ++ ls') 

-- aplica las transformaciones 'lints' repetidas veces y de forma incremental,
-- hasta que ya no generen más cambios en 'func'
lintRec :: Linting a -> Linting a
lintRec lints func = 
    let (func', suggestions) = lints func
    in case suggestions of
        [] -> (func, suggestions) -- La lista está vacía
        _  -> let (finalFunc, moreSuggestions) = lintRec lints func'
                in (finalFunc, suggestions ++ moreSuggestions)-- La lista no está vacía
        
{- lintRec :: Linting a -> Linting a
lintRec lints func = 
    let (func', suggestions) = lints func
    in if null suggestions
      then (func, suggestions)  -- No hay más cambios, se retorna el original
      else 
          let (finalFunc, moreSuggestions) = lintRec lints func'
          in (finalFunc, suggestions ++ moreSuggestions) -}
