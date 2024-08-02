-- Generate appendTree<0..4> and addDigits<0..4> for Data.FingerTree
module Main where

main :: IO ()
main = putStr (compose [showAppend n | n <- [0..4]] "")

showAppend :: Int -> ShowS
showAppend n =
    showChar '\n' .
    showString "appendTree" . shows n . showString " :: (Measured v a) => " .
    showFunType ([ft] ++ replicate n "a" ++ [ft]) ft . showString "\n" .
    appendTreeClause "Empty" "xs" (showCons (args n) (showString "xs")) .
    appendTreeClause "xs" "Empty" (showSnoc (showString "xs") (args n)) .
    appendTreeClause "(Single x)" "xs"
        (showCons ('x':args n) (showString "xs")) .
    appendTreeClause "xs" "(Single x)"
        (showSnoc (showString "xs") (args n++"x")) .
    appendTreeClause "(Deep _ pr1 m1 sf1)" "(Deep _ pr2 m2 sf2)"
        (showString "deep pr1 (addDigits" . shows n . showString " m1 sf1" .
         showArgList (args n) . showString " pr2 m2) sf2") .
    showChar '\n' .
    showString "addDigits" . shows n . showString " :: (Measured v a) => " .
    showFunType ([ft_node, digit] ++ replicate n "a" ++ [digit, ft_node])
        ft_node .
    showString "\n" .
    compose [addDigitsClause n1 n2 | n1 <- [1..4], n2 <- [1..4]]
  where
    ft = "FingerTree v a"
    digit = "Digit a"
    ft_node = "FingerTree v (Node v a)"
    showFunType ts tr =
        compose [showString t . showString " -> " | t <- ts] . showString tr
    appendTreeClause t1 t2 rhs =
        showString "appendTree" . shows n .
            showChar ' ' . showString t1 . showArgList (args n) .
            showChar ' ' . showString t2 .
            showString " =\n    " . rhs . showChar '\n'
    addDigitsClause n1 n2 =
        showString "addDigits" . shows n .
            showString " m1 (" . showDigit vs1 . showChar ')' .
            showArgList vsm .
            showString " (" . showDigit vs2 . showString ") m2" .
            showString " =\n    " .
            showString "appendTree" . shows (length ns) .
            showString " m1" .
            compose [showString " (" . showNode node . showChar ')' |
                node <- ns] .
            showString " m2" . showChar '\n'
      where
        vs = args (n1+n+n2)
        vs1 = take n1 vs
        vsm = take n (drop n1 vs)
        vs2 = drop (n1+n) vs
        ns = nodes vs

data Node a = Node2 a a | Node3 a a a

nodes :: [a] -> [Node a]
nodes [a, b] = [Node2 a b]
nodes [a, b, c] = [Node3 a b c]
nodes [a, b, c, d] = [Node2 a b, Node2 c d]
nodes (a:b:c:xs) = Node3 a b c : nodes xs

type Var = Char

showNode :: Node Var -> ShowS
showNode (Node2 a b) =
    showString "node2 " . showChar a . showChar ' ' . showChar b
showNode (Node3 a b c) =
    showString "node3 " . showChar a . showChar ' ' . showChar b .
        showChar ' ' . showChar c

showDigit :: [Var] -> ShowS
showDigit vs =
    showString (["One", "Two", "Three", "Four"]!!(length vs-1)) .
    showArgList vs

showArgList :: [Var] -> ShowS
showArgList vs = compose [showChar ' ' . showChar c | c <- vs]

args :: Int -> [Var]
args n = take n ['a'..]

showCons :: [Var] -> ShowS -> ShowS
showCons xs sf = compose [showChar x . showString " <| " | x <- xs] . sf

showSnoc :: ShowS -> [Var] -> ShowS
showSnoc sf xs = sf . compose [showString " |> " . showChar x | x <- xs]

compose :: [a -> a] -> a -> a
compose = flip (foldr id)
