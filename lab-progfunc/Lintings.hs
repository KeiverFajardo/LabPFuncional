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
freeVariables (Lit _) = []
freeVariables (Lam x e) = filter (/= x) (freeVariables e)
freeVariables (App e1 e2) = freeVariables e1 ++ freeVariables e2
freeVariables (Infix _ e1 e2) =  freeVariables e1 ++ freeVariables e2
freeVariables (If cond th el) = freeVariables cond ++ freeVariables th ++ freeVariables el
freeVariables (Case e1 e2 (n1, n2, e3)) =
    freeVariables e1 ++ freeVariables e2 ++ filter (/= n1) (filter (/= n2)  (freeVariables e3))

-- Computa la lista de variables ligadas de una expresión
boundVariables :: Expr -> [Name]
boundVariables (Var x) = []
boundVariables (Lit _) = []
boundVariables (Lam x e) = [x] ++ (boundVariables e)
boundVariables (App e1 e2) = boundVariables e1 ++ boundVariables e2
boundVariables (Infix _ e1 e2) =  boundVariables e1 ++ boundVariables e2
boundVariables (If cond th el) = boundVariables cond ++ boundVariables th ++ boundVariables el
boundVariables (Case e1 e2 (n1, n2, e3)) =
    boundVariables e1 ++ boundVariables e2 ++ boundVariables e3

-- Computa la lista de variables validas de una expresión
validVariables :: [Name] -> [Name] -> [Name]
validVariables freeVars boundVars = filter (`notElem` boundVars) freeVars

appVariables :: [Name] -> Expr
appVariables []       = Lit LitNil
appVariables [x]      = Var x
appVariables (x:xs)   = foldl App (Var x) (map Var xs)

--------------------------END CODIGO AGREGADO


--------------------------------------------------------------------------------
-- LINTINGS
--------------------------------------------------------------------------------


--------------------------------------------------------------------------------
-- Computación de constantes
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Reduce expresiones aritméticas/booleanas
-- Construye sugerencias de la forma (LintCompCst e r) EJ 4

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
          then (simplifiedExpr, suggestionsLeft ++ suggestionsRight)
          else (expr, suggestionsLeft ++ suggestionsRight)

    Case expr1 expr2 (name1, name2, expr3) -> 
        let (expr1', suggestions1) = lintComputeConstant expr1
            (expr2', suggestions2) = lintComputeConstant expr2
            (expr3', suggestions3) = lintComputeConstant expr3
        in (Case expr1' expr2' (name1, name2, expr3'), suggestions1 ++ suggestions2 ++ suggestions3)

    {- Infix op (Var x) left ->
        let (left', suggestionsLeft) = lintComputeConstant left
            simplifiedExpr = Infix op (Var x) left'
        in if simplifiedExpr /= expr
          then (simplifiedExpr, suggestionsLeft)
          else (expr, suggestionsLeft) -}

    -- Caso Base: Expresión que no se simplifica
    _ -> (expr, [])

{- "(2 + 2) + (1 + 1)"
Infix Add (Infix Add (Lit (LitInt 2)) (Lit (LitInt 2)))
          (Infix Add (Lit (LitInt 1)) (Lit (LitInt 1)))

(Lit (LitInt 6), [LintCompCst (Infix Add (Lit (LitInt 2)) (Lit (LitInt 2))) 
                              (Lit (LitInt 4))
                  ,LintCompCst (Infix Add (Lit (LitInt 1)) (Lit (LitInt 1))) 
                              (Lit (LitInt 2))
                  ,,LintCompCst (Infix Add (Lit (LitInt 4)) (Lit (LitInt 2))) 
                              (Lit (LitInt 6))]) -}

--------------------------------------------------------------------------------
-- Eliminación de chequeos redundantes de booleanos
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Elimina chequeos de la forma e == True, True == e, e == False y False == e
-- Construye sugerencias de la forma (LintBool e r) EJ 5
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

    -- Caso para lambdas: recorrer el cuerpo de la lambda
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

    -- Caso recursivo para sub-expresiones
    Infix op left right -> 
        let (left', suggestionsLeft) = lintRedBool left
            (right', suggestionsRight) = lintRedBool right
        in (Infix op left' right', suggestionsLeft ++ suggestionsRight)

    -- Caso de `Case`, debemos recorrer las ramas y las expresiones dentro
    Case expr1 expr2 (name1, name2, expr3) -> 
        let (expr1', suggestions1) = lintRedBool expr1
            (expr2', suggestions2) = lintRedBool expr2
            (expr3', suggestions3) = lintRedBool expr3
        in (Case expr1' expr2' (name1, name2, expr3'), suggestions1 ++ suggestions2 ++ suggestions3)

    -- Si no hay chequeos redundantes, devolvemos la expresión original
    _ -> (expr, [])


--------------------------------------------------------------------------------
-- Eliminación de if redundantes
--------------------------------------------------------------------------------
{- If (Lit (LitBool True)) (Infix Add (Var "x") (If (Lit (LitBool False)) (Lit (LitInt w)) (Lit (LitInt y)))) (Lit (LitInt x)) -}
--------------------------------------------------------------------------------
-- Sustitución de if con literal en la condición por la rama correspondiente
-- Construye sugerencias de la forma (LintRedIf e r) REVISAR los IF EJ 6
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
    
    If (Lit (LitBool True)) exp (Var z) ->
        let result = exp
        in (result, [LintRedIf expr result])

    If (Lit (LitBool False)) (Var z) (Lit LitNil) ->
        let result = (Lit LitNil)
        in (result, [LintRedIf expr result])
    
    If (Lit (LitBool False)) (Lit LitNil) e1 ->
        let result = e1
        in (result, [LintRedIf expr result])

    If (Lit (LitBool False)) e1 e2 ->
        let result = e2
        in (result, [LintRedIf expr result])

    If (Lit (LitBool True)) e1 e2 ->
        let result = e1
        in (result, [LintRedIf expr result])

    {- If (Lit (LitBool False)) left right ->
        let result = right
        in (result, [LintRedIf expr result])

    If (Lit (LitBool True)) left right ->
        let result = left
        in (result, [LintRedIf expr result]) -}

    Infix Add (Var x) other -> 
        let (simplifiedThen, suggestionsThen) = lintRedIfCond other
        in (Infix Add (Var x) simplifiedThen, suggestionsThen)

    Infix Add (Lit (LitInt y)) other -> 
        let (simplifiedThen, suggestionsThen) = lintRedIfCond other
        in (Infix Add (Lit (LitInt y)) simplifiedThen, suggestionsThen)

    Infix Add other (Lit (LitInt y)) -> 
        let (simplifiedThen, suggestionsThen) = lintRedIfCond other
        in (Infix Add simplifiedThen (Lit (LitInt y)), suggestionsThen)

    {- Infix And (Lit (LitBool False)) other  -> 
        let (simplifiedThen, suggestionsThen) = lintRedIfCond other
            result =  simplifiedThen
            
         {- (Infix Add simplifiedThen (Lit (LitInt y)), suggestionsThen) -}
        in (result, suggestionsThen ++ [LintRedIf expr result]) -}

    {- Infix Add left right -> 
        let (left', suggestionsLeft) = lintRedIfCond left
            (right', suggestionsRight) = lintRedIfCond right
            simplifiedExpr = Infix Add left' right'
        in if simplifiedExpr /= expr
          then (simplifiedExpr, suggestionsLeft ++ suggestionsRight)
          else (expr, suggestionsLeft ++ suggestionsRight) -}

    {- If (Lit (LitBool True)) thenExpr elseExpr ->
      let (simplifiedThen, suggestionsThen) = lintRedIfCond thenExpr
          -- Reconstruimos el `If` con las ramas simplificadas
          simplifiedExpr = simplifiedThen
      in (simplifiedExpr, suggestionsThen) -}

    {- -- Caso: if True then t else e => t
    If (Lit (LitBool True)) t _ -> 
        let (t', suggestions) = lintRedIfCond t  -- Simplificamos la rama `then` si es necesario
        in (t', suggestions ++ [LintRedIf expr t'])

    -- Caso: if False then t else e => e
    If (Lit (LitBool False)) _ e -> 
        let (e', suggestions) = lintRedIfCond e  -- Simplificamos la rama `else` si es necesario
        in (e', suggestions ++ [LintRedIf expr e'])
 -}
    {- If (Lit (LitBool False)) (Lit (LitInt x)) right ->
        let (right', suggestionsRight) = lintRedIfCond right
        in (If (Lit (LitBool False)) (Lit (LitInt x)) right', suggestionsRight)

    If (Lit (LitBool True)) left (Lit (LitInt x)) ->
        let (left', suggestionsLeft) = lintRedIfCond left
        in (If (Lit (LitBool True)) left (Lit (LitInt x)), suggestionsLeft) -}

    -- Caso para lambdas: recorrer el cuerpo de la lambda
    App e1 e2 -> 
        let (e1', suggestions1) = lintRedIfCond e1
            (e2', suggestions2) = lintRedIfCond e2
        in (App e1' e2', suggestions1 ++ suggestions2)

    Lam name body ->
        let (body', suggestions) = lintRedIfCond body
        in (Lam name body', suggestions)
    
    {- Lam name body ->
        let (body', suggestions) = case body of
                App (Lam e1 e2) e3 -> 
                    let (r, eR) = lintRedIfCond (Lam e1 e2)
                    in (r, eR)
                _         -> lintRedIfCond body

            (res, sRes) = if null suggestions
                            then (expr, [])
                            else (body', suggestions) 
        in (res, sRes) -}

    If e1 e2 e3 -> 
        let (e1', suggestions1) = lintRedIfCond e1
            (e2', suggestions2) = lintRedIfCond e2
            (e3', suggestions3) = lintRedIfCond e3
        in (If e1' e2' e3', suggestions1 ++ suggestions2 ++ suggestions3)

    Infix op e2 e3 ->
        let (e2', suggestions2) = lintRedIfCond e2
            (e3', suggestions3) = lintRedIfCond e3
        in (Infix op e2' e3', suggestions2 ++ suggestions3)

    -- Caso de `Case`, debemos recorrer las ramas y las expresiones dentro
    Case expr1 expr2 (name1, name2, expr3) -> 
        let (expr1', suggestions1) = lintRedIfCond expr1
            (expr2', suggestions2) = lintRedIfCond expr2
            (expr3', suggestions3) = lintRedIfCond expr3
        in (Case expr1' expr2' (name1, name2, expr3'), suggestions1 ++ suggestions2 ++ suggestions3)


    -- Si no es un `if` con un literal en la condición, devolvemos la expresión original
    _ -> (expr, [])
    


--------------------------------------------------------------------------------
-- Sustitución de if por conjunción entre la condición y su rama _then_
-- Construye sugerencias de la forma (LintRedIf e r) EJ 6
lintRedIfAnd :: Linting Expr
lintRedIfAnd expr = case expr of
    -- Caso: if c then e else False => c && e
    If cond e (Lit (LitBool False)) -> 
        let (cond', suggestionsCond) = lintRedIfAnd cond  -- Simplificamos la condición
            (e', suggestionsE) = lintRedIfAnd e  -- Simplificamos la rama `then` si es necesario
            result = Infix And cond' e'  -- Reemplazamos por conjunción
        in (result, suggestionsCond ++ suggestionsE ++ [LintRedIf expr result])

    -- Caso para lambdas: recorrer el cuerpo de la lambda
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

    -- Caso de `Case`, debemos recorrer las ramas y las expresiones dentro
    Case expr1 expr2 (name1, name2, expr3) -> 
        let (expr1', suggestions1) = lintRedIfAnd expr1
            (expr2', suggestions2) = lintRedIfAnd expr2
            (expr3', suggestions3) = lintRedIfAnd expr3
        in (Case expr1' expr2' (name1, name2, expr3'), suggestions1 ++ suggestions2 ++ suggestions3)

    -- Si no corresponde a este patrón, devolvemos la expresión original
    _ -> (expr, [])


--------------------------------------------------------------------------------
-- Sustitución de if por disyunción entre la condición y su rama _else_
-- Construye sugerencias de la forma (LintRedIf e r) EJ 6
lintRedIfOr :: Linting Expr
lintRedIfOr expr = case expr of
    -- Caso: if c then True else e => c || e
    If cond (Lit (LitBool True)) e -> 
        let (cond', suggestionsCond) = lintRedIfOr cond  -- Simplificamos la condición
            (e', suggestionsE) = lintRedIfOr e  -- Simplificamos la rama `else` si es necesario
            result = Infix Or cond' e'  -- Reemplazamos por disyunción
        in (result, suggestionsCond ++ suggestionsE ++ [LintRedIf expr result])

    -- Caso para lambdas: recorrer el cuerpo de la lambda
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

    -- Caso de `Case`, debemos recorrer las ramas y las expresiones dentro
    Case expr1 expr2 (name1, name2, expr3) -> 
        let (expr1', suggestions1) = lintRedIfOr expr1
            (expr2', suggestions2) = lintRedIfOr expr2
            (expr3', suggestions3) = lintRedIfOr expr3
        in (Case expr1' expr2' (name1, name2, expr3'), suggestions1 ++ suggestions2 ++ suggestions3)

    -- Si no corresponde a este patrón, devolvemos la expresión original
    _ -> (expr, [])



--------------------------------------------------------------------------------
-- Chequeo de lista vacía
--------------------------------------------------------------------------------
-- Sugiere el uso de null para verificar si una lista es vacía
-- Construye sugerencias de la forma (LintNull e r) FALTA REVISAR PARA LAS ANIDADAS EJ 7

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

    -- Caso: funciones anidadas, como en (\ys -> (\ls -> length ls == 0) ys)  REVISAR ESTA
    App (Lam name body) _ -> 
        let (body', suggestions) = lintNull body
        in (Lam name body', suggestions)

    -- Caso para lambdas: recorrer el cuerpo de la lambda
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

    -- Caso de `Case`, debemos recorrer las ramas y las expresiones dentro
    Case expr1 expr2 (name1, name2, expr3) -> 
        let (expr1', suggestions1) = lintNull expr1
            (expr2', suggestions2) = lintNull expr2
            (expr3', suggestions3) = lintNull expr3
        in (Case expr1' expr2' (name1, name2, expr3'), suggestions1 ++ suggestions2 ++ suggestions3)

    -- Si no corresponde a este patrón, devolvemos la expresión original
    _ -> (expr, [])


--------------------------------------------------------------------------------
-- Eliminación de la concatenación
--------------------------------------------------------------------------------
-- se aplica en casos de la forma (e:[] ++ es), reemplazando por (e:es)
-- Construye sugerencias de la forma (LintAppend e r) Esta!!!! puede tener la sol recursiva de todas EJ 8

lintAppend :: Linting Expr
lintAppend expr = case expr of
    -- Caso: e : [] ++ es => e : es
    Infix Append (Infix Cons (Var x) (Lit LitNil)) es -> 
        let (es', suggestionsE) = lintAppend es  -- Recursivamente simplificamos la lista `es`
            result = Infix Cons (Var x) es'  -- Usamos Infix Cons directamente para e : es
            expr' = (Infix Append (Infix Cons (Var x) (Lit LitNil)) es')
        in (result, suggestionsE ++ [LintAppend expr' result])
    
    -- Caso general de `Append` para evaluar recursivamente `e1` y `e2`
    Infix Append e1 e2 -> 
        -- Simplificamos `e1` y `e2` primero
        let (e1', suggestions1) = lintAppend e1
            (e2', suggestions2) = lintAppend e2
            simplifiedExpr = Infix Append e1' e2'
        in if simplifiedExpr /= expr
           then (simplifiedExpr, suggestions1 ++ suggestions2 ++ [LintAppend expr simplifiedExpr])
           else (expr, suggestions1 ++ suggestions2)

    -- Caso para lambdas: recorrer el cuerpo de la lambda
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

    -- Caso de `Case`, debemos recorrer las ramas y las expresiones dentro
    Case expr1 expr2 (name1, name2, expr3) -> 
        let (expr1', suggestions1) = lintAppend expr1
            (expr2', suggestions2) = lintAppend expr2
            (expr3', suggestions3) = lintAppend expr3
        in (Case expr1' expr2' (name1, name2, expr3'), suggestions1 ++ suggestions2 ++ suggestions3)

    -- Si no corresponde a este patrón, devolvemos la expresión original
    _ -> (expr, [])

    {-  -- Caso recursivo para `Cons` con lista vacía y `Append` anidados
    Infix Cons e1 (Infix Append (Lit LitNil) e2) ->
        let (e2', suggestions) = lintAppend e2
            result = Infix Cons e1 e2'
        in (result, suggestions ++ [LintAppend expr result])

    -- Caso general: recorre la expresión sin hacer ninguna transformación
    Infix Cons e1 e2 -> 
        let (e1', suggestions1) = lintAppend e1
            (e2', suggestions2) = lintAppend e2
            result = Infix Cons e1' e2'
        in (result, suggestions1 ++ suggestions2) -}

    {- Infix Append (Infix Cons e (Lit LitNil)) es  -> 
        let (e', suggestions) = lintAppend e
            (es', suggestionsE) = lintAppend es 
            result = Infix Cons e' es'
        in (result, suggestions ++ suggestionsE ++ [LintAppend expr result])  -}

 

    -- Caso para aplicaciones, aplicar recursivamente la linting
    {- App func arg -> 
        let (func', suggestionsFunc) = lintAppend func
            (arg', suggestionsArg) = lintAppend arg
        in (App func' arg', suggestionsFunc ++ suggestionsArg) -}


--------------------------------------------------------------------------------
-- Composición
--------------------------------------------------------------------------------
-- se aplica en casos de la forma (f (g t)), reemplazando por (f . g) t
-- Construye sugerencias de la forma (LintComp e r) FALTA UN CASO BORDE EJ 9 FALTA COMPOSICION Y ETA REDUCCIONNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNN
{- App (Var "f") (App (Var "g") (App (Var "h") (Var "x"))) -}
lintComp :: Linting Expr
lintComp expr = case expr of
    -- Patrón adicional para aplicar una lambda con una operación infija
    App (Lam x (Infix op (Var x') (Lit lit))) e1 | x == x' ->
        let (e1', suggestions) = lintComp e1
            result = App (Lam x (Infix op (Var x) (Lit lit))) e1'
        in (result, suggestions)

    App (Var g) (App (Var h) (Var x)) -> 
        let result = App (Infix Comp  (Var g) (Var h)) (Var x)  
        in (result, [LintComp expr result])
    
    App (Var f) (App (Var g) (Lit (LitInt h))) -> 
        let result = App (Infix Comp  (Var f) (Var g)) (Lit (LitInt h)) 
        in (result, [LintComp expr result])

    App (Lam name body) e1 -> 
        let (e1', suggestionsLeft) = lintComp e1
            result = App (Lam name body) e1'
        in (result, suggestionsLeft ++ [LintComp expr result])

    App (Var f) (App e1 (Var x)) -> 
        let (e1', suggestionsLeft) = lintComp e1
            result = App (Infix Comp (Var f) e1') (Var x) 
        in (result, suggestionsLeft ++ [LintComp expr result])

    App e1 e2 -> 
        let (e1', suggestionsLeft) = lintComp e1
            (e2', suggestionsRight) = lintComp e2
            simplifiedExpr = App e1' e2'
        in if simplifiedExpr /= expr
          then (simplifiedExpr, suggestionsLeft ++ suggestionsRight)
          else if null suggestionsLeft && null suggestionsRight
                then (expr, [])
                else (simplifiedExpr, suggestionsLeft ++ suggestionsRight)
          
    
    Lam name body ->
        let (body', suggestions) = lintComp body
        in (Lam name body', suggestions)

    If e1 e2 e3 -> 
        let (e1', suggestions1) = lintComp e1
            (e2', suggestions2) = lintComp e2
            (e3', suggestions3) = lintComp e3
        in (If e1' e2' e3', suggestions1 ++ suggestions2 ++ suggestions3)

    Infix op e2 e3 ->
        let (e2', suggestions2) = lintComp e2
            (e3', suggestions3) = lintComp e3
        in (Infix op e2' e3', suggestions2 ++ suggestions3)

    Case expr1 expr2 (name1, name2, expr3) -> 
        let (expr1', suggestions1) = lintComp expr1
            (expr2', suggestions2) = lintComp expr2
            (expr3', suggestions3) = lintComp expr3
        in (Case expr1' expr2' (name1, name2, expr3'), suggestions1 ++ suggestions2 ++ suggestions3)

    -- Si no corresponde a este patrón, devolvemos la expresión original
    _ -> (expr, [])

    {- App (Var f) (App (Var g) exp) -> 
        let (expr1', suggestions1) = lintComp exp
            result = App (Infix Comp  (Var f) (Var g)) expr1' 
        in (result, suggestions1 ++ [LintComp expr result])
 -}
    {- App (Var f) (App (Lam y body) (Var z)) -> 
        let result = App (Infix Comp (Var f) (Lam y body)) (Var z) 
        in (result, [LintComp expr result]) -}

    {- App (Lam d body') (App (Var g) (App (Lam y body) (Var x))) -> 
        let result = App (Infix Comp (Lam d body') (Infix Comp (Var g) (Lam y body))) (Var x) 
        in (result, [LintComp expr result]) -}
    

    -- Caso de aplicación anidada con expresión general en el segundo argumento
    {- App (App (Var f) expr1) expr2 ->
        let (expr1', suggestions1) = lintComp expr1
            (expr2', suggestions2) = lintComp expr2
            result = App (Infix Comp (Var f) expr1') expr2'
        in (result, suggestions1 ++ suggestions2) -}


   {-  -- Caso: f (g t) => (f . g) t
    App f (App g t) -> 
        let (t', suggestionsT) = lintComp t  -- Recursivamente simplificamos `t`
            -- Reemplazamos f (g t) por (f . g) t
            result = App (Infix Comp f g) t'  
        in (result, suggestionsT ++ [LintComp expr result])

    -- Caso: (f (g t)) => (f . g) t (sin paréntesis exteriores)
    -- Este caso ya está cubierto por el anterior, ya que la forma recursiva lo maneja.
    App (App f g) t -> 
        let (t', suggestionsT) = lintComp t  -- Recursivamente simplificamos `t`
            result = App (Infix Comp f g) t'  -- Reemplazamos (f (g t)) por (f . g) t
        in (result, suggestionsT ++ [LintComp expr result])
 -}
 
 {- Lam a e1 ->
        let (e1N, rE1N) = case e1 of 
                                App (Lam b e3) e4 -> lintErna (Lam b e3) e4 
                                _                 -> lintEta e1
            libreVars = varsAux e1N : freeVariables (Lam a e1N)
            (r, rE) = if not (elem (a) libreVars)
                        then let eNew = LintEtaAux e1N a
                            in (eNew, rE1N ++ [LinEta (Lam a e1N) eNew])
                        else if null rE1N
                            then (e, [])
                            else (Lam a e1N, rE1N)
        in (r, rE)


Lam name body ->
        let (body', suggestions) = case body of
                        App (Lam e1 e2) e3 -> 
                            let (res1, eres1) = lintEta (Lam e1 e2)
                                ress = App res1 e3
                            in (ress, eres1)
                        _   -> lintEta body
            variablesLibres = freeVariables(Lam name body')
            (resultado, sresultado) = if not (elem (name) variablesLibres)
                                        then let exprNueva = (App body' (Var name))
                                            in (exprNueva, suggestions ++ [LintEta (Lam name body') exprNueva])
                                        else if null suggestions
                                            then (expr, [])
                                            else (Lam name body', suggestions)
        in (resultado, sresultado) -}


{-  App e1 (App e2 e3) -> 
        let (e1', suggestionsE1) = lintComp e1
            (e2', suggestionsE2) = lintComp e2
            (e3', suggestionsE3) = lintComp e3
            result = App (Infix Comp e1' e2') e3'
        in (result, suggestionsE1 ++ suggestionsE2 ++ suggestionsE3 ++ [LintComp (App e1' (App e2' e3'))  result]) -}
--------------------------------------------------------------------------------
-- Eta Redución
--------------------------------------------------------------------------------
-- se aplica en casos de la forma \x -> e x, reemplazando por e
-- Construye sugerencias de la forma (LintEta e r) OJO FALTA EL CASO BORDE EJ 10
-- Propaga las variables libres desde expresiones internas
lintEta :: Linting Expr
lintEta expr = case expr of
    {- Version1 -}
    {- Lam x (App e (Var x')) | x == x' ->
                                let (e', suggestions) = lintEta e
                                in if (x == x' && not (x `elem` freeVariables e') && not (x' `elem` freeVariables e'))
                                    then (e', suggestions ++ [LintEta (Lam x (App e' (Var x'))) e'])
                                    else (Lam x (App e' (Var x')), suggestions) 
                            | otherwise -> (Lam x (App e (Var x')), [])

    Lam name body ->
        let (body', suggestions) = case body of
                App e1 e2 | e2 == appVariables([name]) -> 
                                let (r, eR) = lintEta e1
                                in (r, eR)
                            | otherwise -> (App e1 e2, [])
                _         -> 
                                let (r, eR) = lintEta body
                                    reducedExpr = Lam name r
                                in case reducedExpr of
                                    Lam y (App e (Var y')) | y == y' && not (y `elem` freeVariables e) ->
                                        let newExpr = e
                                            suggestion = LintEta reducedExpr newExpr
                                        in (newExpr, suggestions ++ [suggestion])    
                                    _ -> (reducedExpr, suggestions)

            (res, sRes) = if not (name `elem` freeVariables body')
                        then (body', suggestions ++ [LintEta (Lam name (App body (appVariables([name])))) body']) 
                        else if null suggestions
                            then (expr, [])
                            else (body', suggestions)
        in (res, sRes) -}
    {- Fin Version1 -}
    {- Version2 -}
    Lam x (App e (Var x')) | x == x' && not (x `elem` freeVariables e) ->
        let (e', suggestions) = lintEta e
            suggestion = LintEta (Lam x (App e (Var x'))) e'
        in (e', suggestions ++ [suggestion])

    -- Caso general para lambda
    Lam x body ->
        let (body', suggestions) = lintEta body
        in if x `elem` freeVariables body'
           then (Lam x body', suggestions) -- No aplica eta-reducción
           else
               let suggestion = LintEta (Lam x body') body'
               in (body', suggestions ++ [suggestion])
     {- Fin Version2 -}
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

    -- Si no corresponde a ningún caso, devolvemos la expresión tal cual
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

    -- Casos recursivos para explorar dentro de la expresión
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

    -- Si no coincide ningún patrón
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
{- e -> l1 -> e' ls
e' -> l2 -> e'' ls'
e -> l1 >==> l2 -> e'' (ls ++ ls') -}

(>==>) :: Linting a -> Linting a -> Linting a
lint1 >==> lint2 = \expr -> 
    let (e', ls) = lint1 expr 
        (e'', ls') = lint2 e'   
    in (e'', ls ++ ls') 



-- aplica las transformaciones 'lints' repetidas veces y de forma incremental,
-- hasta que ya no generen más cambios en 'func'
lintRec :: Eq a => Linting a -> Linting a
lintRec lints func = 
    let (func', suggestions) = lints func
    in if func' == func
      then (func, suggestions)  -- No hay más cambios, se retorna el original
      else 
          let (finalFunc, moreSuggestions) = lintRec lints func'
          in (finalFunc, suggestions ++ moreSuggestions)
