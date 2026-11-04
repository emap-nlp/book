import CSwL.Parsing.ParseTrees
import Mathlib.Data.List.Monad

-- # Parsers e combinadores de parsers

namespace Parsing

abbrev Parser (α β : Type) := StateT (List α) List β

example {α β : Type} :
    Parser α β = (List α → List (β × List α)) := rfl

#eval (pure 1 : Parser Char Nat).run "ab".toList
#eval (failure : Parser Char Nat).run "ab".toList

def symbol {α : Type} [BEq α] (c : α) : Parser α α
  | x :: xs => if x == c then [(x, xs)] else []
  | [] => []

def token {α : Type} [BEq α] (cs : List α)
  : Parser α (List α)
  | xs =>
    if cs == xs.take cs.length then
     [(cs, xs.drop cs.length)]
    else []

def satisfy {α : Type} (p : α → Bool) : Parser α α
  | x :: xs => if p x then [(x, xs)] else []
  | [] => []

def digit : Parser Char Char := satisfy Char.isDigit

#eval (symbol 'a').run "ab".toList
#eval (token "ab".toList).run "abc".toList
#eval digit.run "42".toList

-- ### Exercise (1 star): symbol-satisfy ⭐

-- Defina `symbol'`, que faz o mesmo que `symbol`, usando `satisfy`.

def symbol' {α : Type} [BEq α] (c : α) : Parser α α :=
  sorry

theorem symbol'_eq_symbol {α : Type} [BEq α] (c : α)
    (xs : List α) : symbol' c xs = symbol c xs := by
  sorry

def just {α β : Type} (p : Parser α β) : Parser α β
 | xs => (p xs).filter fun (_, ys) => ys.isEmpty

example {α β : Type} (p q : Parser α β) (xs : List α) :
    (p <|> q) xs = p xs ++ q xs := rfl

example {α β γ : Type} (p : Parser α β) (q : β → Parser α γ)
    (xs : List α) :
    (p >>= q) xs =
      (p xs).flatMap fun (r, ys) => q r ys := rfl

def pD : Parser String String :=
  symbol "every" <|> symbol "some" <|> symbol "no"

def pN : Parser String String :=
  symbol "dwarf" <|> symbol "wizard"

def pVP : Parser String String :=
  symbol "smiled" <|> symbol "laughed"

def pNP : Parser String (List String) :=
  (do
    let w ← symbol "Alice" <|> symbol "Dorothy"
    return [w]) <|>
  (do
    let d ← pD
    let n ← pN
    return [d, n])

def pS : Parser String (List String) := do
  let np ← pNP
  let vp ← pVP
  return np ++ [vp]

#eval pS.run ["every", "wizard", "smiled"]
#eval pS.run ["Alice", "laughed", "loudly"]

example {α β γ : Type} (f : β → γ) (p : Parser α β)
    (xs : List α) :
    (f <$> p) xs =
      (p xs).flatMap fun (r, ys) => [(f r, ys)] := rfl

def digitize : Parser Char Nat :=
  (fun c => c.toNat - '0'.toNat) <$> digit

#eval digitize.run "42".toList

def epsilonT {α β : Type} : Parser α (ParseTree α β) :=
  pure .ep

def symbolT {α β : Type} [BEq α] (s : α) :
    Parser α (ParseTree α β) :=
  .leaf <$> symbol s

def collect {α β : Type} :
    List (Parser α β) → Parser α (List β)
  | [] => pure []
  | p :: ps => do
    let r ← p
    let rs ← collect ps
    return r :: rs

def parseAs {α β : Type} (label : β)
    (ps : List (Parser α (ParseTree α β))) :
    Parser α (ParseTree α β) :=
  .branch label <$> collect ps

def det : Parser String (ParseTree String Char) :=
  symbolT "every" <|> symbolT "some" <|> symbolT "no"

def cn : Parser String (ParseTree String Char) :=
  symbolT "man" <|> symbolT "woman"

def vp : Parser String (ParseTree String Char) :=
  symbolT "smiled" <|> symbolT "laughed"

def np : Parser String (ParseTree String Char) :=
  symbolT "Alice" <|> symbolT "Dorothy"
  <|> parseAs 'N' [det, cn]

def sent : Parser String (ParseTree String Char) :=
  parseAs 'S' [np, vp]

#eval (just sent).run ["every", "man", "laughed"] |>.map
  (toString ·.1)

partial def palindrome :
    Parser Char (ParseTree Char Char) :=
  epsilonT <|> symbolT 'a' <|> symbolT 'b' <|> symbolT 'c'
  <|> parseAs 'A' [symbolT 'a', palindrome, symbolT 'a']
  <|> parseAs 'A' [symbolT 'b', palindrome, symbolT 'b']
  <|> parseAs 'A' [symbolT 'c', palindrome, symbolT 'c']

#eval (just palindrome).run "abcba".toList |>.map
  (toString ·.1)
#eval palindrome.run "aba".toList |>.map fun (t, ys) =>
  (toString t, String.ofList ys)

partial def many {α β : Type} (p : Parser α β) :
    Parser α (List β) :=
  (do
    let r ← p
    let rs ← many p
    return r :: rs) <|> pure []

#eval (many (symbol 'a')).run "aab".toList

-- ### Exercise (1 star): parse-many-as ⭐

-- Para ter uma árvore, a repetição precisa ficar sob um rótulo. Defina
-- `parseManyAs l p`, que aplica `p` quantas vezes for possível e põe as
-- árvores obtidas sob um nó com rótulo `l`. Confira o resultado com
-- `adjectives`, uma sequência de adjetivos sob o rótulo `J`.

def parseManyAs {α β : Type} (l : β)
    (p : Parser α (ParseTree α β)) :
    Parser α (ParseTree α β) :=
  sorry

def adjectives : Parser String (ParseTree String Char) :=
  parseManyAs 'J' (symbolT "happy" <|> symbolT "evil")

theorem adjectives_happy_evil :
    ((adjectives.run ["happy", "evil", "dwarf"]).map
      fun (t, ys) => (toString t, ys)) =
    [("[.J happy evil]", ["dwarf"]),
     ("[.J happy]", ["evil", "dwarf"]),
     ("[.J ]", ["happy", "evil", "dwarf"])] := by
  sorry

partial def leftRec : Parser Char (ParseTree Char Char) :=
  parseAs 'A' [leftRec, symbolT 'a'] <|> symbolT 'b'

end Parsing

