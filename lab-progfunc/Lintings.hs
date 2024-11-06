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
freeVariables (Lit _) = []
freeVariables (Infix Add e1 e2) = freeVariables e1 ++ freeVariables e2
freeVariables (Infix Mult e1 e2) = freeVariables e1 ++ freeVariables e2
freeVariables (Infix Eq e1 e2) = freeVariables e1 ++ freeVariables e2
freeVariables (If cond th el) = freeVariables cond ++ freeVariables th ++ freeVariables el
--------------------------END CODIGO AGREGADO

--------------------------------------------------------------------------------
-- LINTINGS
--------------------------------------------------------------------------------


--------------------------------------------------------------------------------
-- Computación de constantes
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Reduce expresiones aritméticas/booleanas
-- Construye sugerencias de la forma (LintCompCst e r)

{- "(2 + 2) + (1 + 1)"
Infix Add (Infix Add (Lit (LitInt 2)) (Lit (LitInt 2)))
          (Infix Add (Lit (LitInt 1)) (Lit (LitInt 1)))

(Lit (LitInt 6), [LintCompCst (Infix Add (Lit (LitInt 2)) (Lit (LitInt 2))) 
                              (Lit (LitInt 4))
                  ,LintCompCst (Infix Add (Lit (LitInt 1)) (Lit (LitInt 1))) 
                              (Lit (LitInt 2))
                  ,,LintCompCst (Infix Add (Lit (LitInt 4)) (Lit (LitInt 2))) 
                              (Lit (LitInt 6))]) -}

lintComputeConstant :: Linting Expr
lintComputeConstant = undefined
--------------------------CODIGO AGREGADO

--------------------------END CODIGO AGREGADO

--------------------------------------------------------------------------------
-- Eliminación de chequeos redundantes de booleanos
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Elimina chequeos de la forma e == True, True == e, e == False y False == e
-- Construye sugerencias de la forma (LintBool e r)
lintRedBool :: Linting Expr
lintRedBool = undefined
--------------------------CODIGO AGREGADO

--------------------------END CODIGO AGREGADO

--------------------------------------------------------------------------------
-- Eliminación de if redundantes
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Sustitución de if con literal en la condición por la rama correspondiente
-- Construye sugerencias de la forma (LintRedIf e r)
lintRedIfCond :: Linting Expr
lintRedIfCond = undefined
--------------------------CODIGO AGREGADO

--------------------------END CODIGO AGREGADO

--------------------------------------------------------------------------------
-- Sustitución de if por conjunción entre la condición y su rama _then_
-- Construye sugerencias de la forma (LintRedIf e r)
lintRedIfAnd :: Linting Expr
lintRedIfAnd = undefined
--------------------------CODIGO AGREGADO

--------------------------END CODIGO AGREGADO

--------------------------------------------------------------------------------
-- Sustitución de if por disyunción entre la condición y su rama _else_
-- Construye sugerencias de la forma (LintRedIf e r)
lintRedIfOr :: Linting Expr
lintRedIfOr = undefined
--------------------------CODIGO AGREGADO

--------------------------END CODIGO AGREGADO

--------------------------------------------------------------------------------
-- Chequeo de lista vacía
--------------------------------------------------------------------------------
-- Sugiere el uso de null para verificar si una lista es vacía
-- Construye sugerencias de la forma (LintNull e r)

lintNull :: Linting Expr
lintNull = undefined
--------------------------CODIGO AGREGADO

--------------------------END CODIGO AGREGADO

--------------------------------------------------------------------------------
-- Eliminación de la concatenación
--------------------------------------------------------------------------------
-- se aplica en casos de la forma (e:[] ++ es), reemplazando por (e:es)
-- Construye sugerencias de la forma (LintAppend e r)

lintAppend :: Linting Expr
lintAppend = undefined
--------------------------CODIGO AGREGADO

--------------------------END CODIGO AGREGADO

--------------------------------------------------------------------------------
-- Composición
--------------------------------------------------------------------------------
-- se aplica en casos de la forma (f (g t)), reemplazando por (f . g) t
-- Construye sugerencias de la forma (LintComp e r)

lintComp :: Linting Expr
lintComp = undefined
--------------------------CODIGO AGREGADO

--------------------------END CODIGO AGREGADO

--------------------------------------------------------------------------------
-- Eta Redución
--------------------------------------------------------------------------------
-- se aplica en casos de la forma \x -> e x, reemplazando por e
-- Construye sugerencias de la forma (LintEta e r)

lintEta :: Linting Expr
lintEta = undefined
--------------------------CODIGO AGREGADO

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
liftToFunc lintExpr (FunDef name body) =
  let (newBody, suggestions) = lintExpr body
  in (FunDef name newBody, suggestions)
--------------------------END CODIGO AGREGADO

-- encadenar transformaciones:
{- e -> l1 -> e' ls
e' -> l2 -> e'' ls'
e -> l1 >==> l2 -> e'' (ls ++ ls') -}

(>==>) :: Linting a -> Linting a -> Linting a
--lint1 >==> lint2 = undefined
--------------------------CODIGO AGREGADO
l1 >==> l2 = \expr ->
  let (expr', suggestions1) = l1 expr
      (expr'', suggestions2) = l2 expr'
  in (expr'', suggestions1 ++ suggestions2)
--------------------------END CODIGO AGREGADO


-- aplica las transformaciones 'lints' repetidas veces y de forma incremental,
-- hasta que ya no generen más cambios en 'func'
lintRec :: Linting a -> Linting a
--lintRec lints func = undefined
--------------------------CODIGO AGREGADO
lintRec lints func = applyLints func []
   where
    -- Subfunción para aplicar los lints hasta que no haya cambios
    applyLints func suggestions =
      let (newFunc, newSuggestions) = lints func
      in if compareByStringAux newFunc func
         then (newFunc, suggestions)  -- Termina cuando no hay más cambios
         else applyLints newFunc (suggestions ++ newSuggestions)

    -- Subfunción auxiliar de comparación basada en la conversión a String (sin modificar la firma de lintRec)
    compareByStringAux :: (ShowExpr a) => a -> a -> Bool
    compareByStringAux x y = showExpr x == showExpr y

    
--------------------------END CODIGO AGREGADO

class ShowExpr a where
  showExpr :: a -> String

instance ShowExpr FunDef where
  showExpr (FunDef name body) = 
    "fun " ++ name ++ " = " ++ showExpr body

instance ShowExpr Expr where
  showExpr (Var name)          = name
  showExpr (Lit lit)           = showLit lit
  showExpr (Infix op e1 e2)    = "(" ++ showExpr e1 ++ " " ++ showOp op ++ " " ++ showExpr e2 ++ ")"
  showExpr (App e1 e2)         = showExpr e1 ++ " " ++ showExpr e2
  showExpr (Lam name body)     = "\\" ++ name ++ " -> " ++ showExpr body
  showExpr (Case expr alt (n1, n2, expr2)) = 
    "case " ++ showExpr expr ++ " of " ++ n1 ++ " " ++ n2 ++ " -> " ++ showExpr expr2
  showExpr (If cond thenExpr elseExpr) = 
    "if " ++ showExpr cond ++ " then " ++ showExpr thenExpr ++ " else " ++ showExpr elseExpr

showLit :: Lit -> String
showLit (LitInt i)  = show i
showLit (LitBool b) = show b
showLit LitNil      = "[]"

showOp :: Op -> String
showOp Add    = "+"
showOp Sub    = "-"
showOp Mult   = "*"
showOp Div    = "/"
showOp Eq     = "=="
showOp GTh    = ">"
showOp LTh    = "<"
showOp And    = "&&"
showOp Or     = "||"
showOp Cons   = ":"
showOp Comp   = "."
showOp Append = "++" 