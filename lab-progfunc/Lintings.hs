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
    freeVariables e1 ++ freeVariables e2 ++ filter (`notElem` [n1, n2]) (freeVariables e3)

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
    -- Caso 1: Operaciones aritméticas constantes
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

    -- Caso 2: Operaciones booleanas constantes
    Infix And (Lit (LitBool x)) (Lit (LitBool y)) -> 
        let result = Lit (LitBool (x && y))
        in (result, [LintCompCst expr result])

    Infix Or (Lit (LitBool x)) (Lit (LitBool y)) -> 
        let result = Lit (LitBool (x || y))
        in (result, [LintCompCst expr result])

    -- Caso para lambdas: recorrer el cuerpo de la lambda
    Lam name body ->
        let (body', suggestions) = lintComputeConstant body
        in (Lam name body', suggestions)

    {- Infix op (Var x) left ->
        let (left', suggestionsLeft) = lintComputeConstant left
            simplifiedExpr = Infix op (Var x) left'
        in if simplifiedExpr /= expr
          then (simplifiedExpr, suggestionsLeft)
          else (expr, suggestionsLeft) -}

    -- Caso Recursivo: Explorar subexpresiones
    Infix op left right ->
        let (left', suggestionsLeft) = lintComputeConstant left
            (right', suggestionsRight) = lintComputeConstant right
            simplifiedExpr = Infix op left' right'
        in if simplifiedExpr /= expr
          then (simplifiedExpr, suggestionsLeft ++ suggestionsRight)
          else (expr, suggestionsLeft ++ suggestionsRight)

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

    If e1 e2 e3 -> 
        let (e1', suggestions1) = lintRedBool e1
            (e2', suggestions2) = lintRedBool e2
            (e3', suggestions3) = lintRedBool e3
        in (If e1' e2' e3', suggestions1 ++ suggestions2 ++ suggestions3)

    -- Caso para lambdas: recorrer el cuerpo de la lambda
    Lam name body ->
        let (body', suggestions) = lintRedBool body
        in (Lam name body', suggestions)

    -- Caso recursivo para sub-expresiones
    Infix op left right -> 
        let (left', suggestionsLeft) = lintRedBool left
            (right', suggestionsRight) = lintRedBool right
        in (Infix op left' right', suggestionsLeft ++ suggestionsRight)

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

    If (Lit (LitBool True)) (Lit (LitInt y)) (Var "x") ->
        let result = (Lit (LitInt y))
        in (result, [LintRedIf expr result])

    If (Lit (LitBool True)) (Infix Add (Var "x") (Lit (LitInt x))) (Lit (LitInt y)) ->
        let result = (Infix Add (Var "x") (Lit (LitInt x)))
        in (result, [LintRedIf expr result])

    {- If (Lit (LitBool False)) left right ->
        let result = right
        in (result, [LintRedIf expr result])

    If (Lit (LitBool True)) left right ->
        let result = left
        in (result, [LintRedIf expr result]) -}

    Infix Add (Var "x") other -> 
        let (simplifiedThen, suggestionsThen) = lintRedIfCond other
        in (Infix Add (Var "x") simplifiedThen, suggestionsThen)

    Infix Add (Lit (LitInt y)) other -> 
        let (simplifiedThen, suggestionsThen) = lintRedIfCond other
        in (Infix Add (Lit (LitInt y)) simplifiedThen, suggestionsThen)

    Infix And (Lit (LitBool False)) other  -> 
        let result = (Lit (LitBool False))
            (simplifiedThen, suggestionsThen) = lintRedIfCond other
         {- (Infix Add simplifiedThen (Lit (LitInt y)), suggestionsThen) -}
        in (result, suggestionsThen ++ [LintRedIf expr result])

    Infix Add other (Lit (LitInt y)) -> 
        let (simplifiedThen, suggestionsThen) = lintRedIfCond other
        in (Infix Add simplifiedThen (Lit (LitInt y)), suggestionsThen)

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
    -- Caso para lambdas: recorrer el cuerpo de la lambda
    Lam name body ->
        let (body', suggestions) = lintRedIfCond body
        in (Lam name body', suggestions)

    {- If (Lit (LitBool False)) (Lit (LitInt x)) right ->
        let (right', suggestionsRight) = lintRedIfCond right
        in (If (Lit (LitBool False)) (Lit (LitInt x)) right', suggestionsRight)

    If (Lit (LitBool True)) left (Lit (LitInt x)) ->
        let (left', suggestionsLeft) = lintRedIfCond left
        in (If (Lit (LitBool True)) left (Lit (LitInt x)), suggestionsLeft) -}

    If e1 e2 e3 -> 
        let (e1', suggestions1) = lintRedIfCond e1
            (e2', suggestions2) = lintRedIfCond e2
            (e3', suggestions3) = lintRedIfCond e3
        in (If e1' e2' e3', suggestions1 ++ suggestions2 ++ suggestions3)

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
    Lam name body ->
        let (body', suggestions) = lintRedIfAnd body
        in (Lam name body', suggestions)
    
    If e1 e2 e3 -> 
        let (e1', suggestions1) = lintRedIfAnd e1
            (e2', suggestions2) = lintRedIfAnd e2
            (e3', suggestions3) = lintRedIfAnd e3
        in (If e1' e2' e3', suggestions1 ++ suggestions2 ++ suggestions3)

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
    Lam name body ->
        let (body', suggestions) = lintRedIfOr body
        in (Lam name body', suggestions)
    
    If e1 e2 e3 -> 
        let (e1', suggestions1) = lintRedIfOr e1
            (e2', suggestions2) = lintRedIfOr e2
            (e3', suggestions3) = lintRedIfOr e3
        in (If e1' e2' e3', suggestions1 ++ suggestions2 ++ suggestions3)

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

    -- Caso para lambdas: recorrer el cuerpo de la lambda
    Lam name body ->
        let (body', suggestions) = lintNull body
        in (Lam name body', suggestions)

    -- Caso: funciones anidadas, como en (\ys -> (\ls -> length ls == 0) ys)
    App (Lam _ body) _ -> 
        let (body', suggestions) = lintNull body
        in (Lam "newLambda" body', suggestions)

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
    Infix Append (Infix Cons e (Lit LitNil)) es -> 
        let (es', suggestionsE) = lintAppend es  -- Recursivamente simplificamos la lista `es`
            result = Infix Cons e es'  -- Usamos Infix Cons directamente para e : es
        in (result, suggestionsE ++ [LintAppend expr result])

    -- Caso para lambdas, recorrer el cuerpo de la lambda
    Lam name body ->
        let (body', suggestions) = lintAppend body
        in (Lam name body', suggestions)

    -- Caso para aplicaciones, aplicar recursivamente la linting
    App func arg -> 
        let (func', suggestionsFunc) = lintAppend func
            (arg', suggestionsArg) = lintAppend arg
        in (App func' arg', suggestionsFunc ++ suggestionsArg)

    -- Caso de `Case`, debemos recorrer las ramas y las expresiones dentro
    Case expr1 expr2 (name1, name2, expr3) -> 
        let (expr1', suggestions1) = lintAppend expr1
            (expr2', suggestions2) = lintAppend expr2
            (expr3', suggestions3) = lintAppend expr3
        in (Case expr1' expr2' (name1, name2, expr3'), suggestions1 ++ suggestions2 ++ suggestions3)

    -- Si no corresponde a este patrón, devolvemos la expresión original
    _ -> (expr, [])

--------------------------------------------------------------------------------
-- Composición
--------------------------------------------------------------------------------
-- se aplica en casos de la forma (f (g t)), reemplazando por (f . g) t
-- Construye sugerencias de la forma (LintComp e r) FALTA UN CASO BORDE EJ 9 FALTA COMPOSICION Y ETA REDUCCIONNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNN
{- App (Var "f") (App (Var "g") (App (Var "h") (Var "x"))) -}
lintComp :: Linting Expr
lintComp expr = case expr of
    App (Var "g") (App (Var "h") (Var "x")) -> 
        let result = App (Infix Comp  (Var "g") (Var "h")) (Var "x")  
        in (result, [LintComp expr result])
    
    App (Var "f") (App (Var "g") (Lit (LitInt h))) -> 
        let result = App (Infix Comp  (Var "f") (Var "g")) (Lit (LitInt h)) 
        in (result, [LintComp expr result])

    App (Var "f") (App (Lam "y" (Infix Sub (Var "y") (Lit (LitInt 2)))) (Var "z")) -> 
        let result = App (Infix Comp  (Var "f") (Lam "y" (Infix Sub (Var "y") (Lit (LitInt 2))))) (Var "z")  
        in (result, [LintComp expr result])

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
    

    -- Caso para lambdas, recorrer el cuerpo de la lambda
    Lam name body -> 
        let (body', suggestions) = lintComp body
        in (Lam name body', suggestions)

    {- -- Caso para aplicaciones, aplicar recursivamente la linting
    App func arg -> 
        let (func', suggestionsFunc) = lintComp func
            (arg', suggestionsArg) = lintComp arg
        in (App func' arg', suggestionsFunc ++ suggestionsArg) -}

    -- Caso de `Case`, debemos recorrer las ramas y las expresiones dentro
    {- Case expr1 expr2 (name1, name2, expr3) -> 
        let (expr1', suggestions1) = lintComp expr1
            (expr2', suggestions2) = lintComp expr2
            (expr3', suggestions3) = lintComp expr3
        in (Case expr1' expr2' (name1, name2, expr3'), suggestions1 ++ suggestions2 ++ suggestions3)
 -}
    App e1 e2 -> 
        let (e1', suggestionsLeft) = lintComp e1
            (e2', suggestionsRight) = lintComp e2
            simplifiedExpr = App e1' e2'
        in if simplifiedExpr /= expr
          then (simplifiedExpr, suggestionsLeft ++ suggestionsRight)
          else (expr, suggestionsLeft ++ suggestionsRight)

    -- Si no corresponde a este patrón, devolvemos la expresión original
    _ -> (expr, [])

--------------------------------------------------------------------------------
-- Eta Redución
--------------------------------------------------------------------------------
-- se aplica en casos de la forma \x -> e x, reemplazando por e
-- Construye sugerencias de la forma (LintEta e r) OJO FALTA EL CASO BORDE EJ 10

lintEta :: Linting Expr
lintEta expr = case expr of
    -- Caso: \ls -> null ls
    Lam ls (App (Var f) (Var ls2)) | ls == ls2 && not (ls `elem` freeVariables (Var f)) ->
        -- Realizamos la reducción: \ls -> null ls → null
        let result = Var f  -- Reemplazamos por null
        in (result, [LintEta expr result])

     -- Caso: \x -> e x
    Lam x (App e (Var x')) | x == x' && not (x `elem` freeVariables e) ->
        let result = e  -- Realizamos la reducción
        in (result, [LintEta expr result])

    -- Otros casos recursivos para las expresiones
    Lam name body -> 
        let (body', suggestions) = lintEta body
        in (Lam name body', suggestions)
    
    App e1 e2 -> 
        let (e1', suggestions1) = lintEta e1
            (e2', suggestions2) = lintEta e2
        in (App e1' e2', suggestions1 ++ suggestions2)
    
    Infix op e1 e2 -> 
        let (e1', suggestions1) = lintEta e1
            (e2', suggestions2) = lintEta e2
        in (Infix op e1' e2', suggestions1 ++ suggestions2)
    
    Case e1 e2 (n1, n2, e3) -> 
        let (e1', suggestions1) = lintEta e1
            (e2', suggestions2) = lintEta e2
            (e3', suggestions3) = lintEta e3
        in (Case e1' e2' (n1, n2, e3'), suggestions1 ++ suggestions2 ++ suggestions3)
    
    If e1 e2 e3 -> 
        let (e1', suggestions1) = lintEta e1
            (e2', suggestions2) = lintEta e2
            (e3', suggestions3) = lintEta e3
        in (If e1' e2' e3', suggestions1 ++ suggestions2 ++ suggestions3)
    
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
