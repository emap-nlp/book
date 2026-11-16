import CSwL.Parsing.ParseTrees
import Mathlib.Data.List.Monad

-- # Parsers e combinadores de parsers

namespace Parsing

-- Nesta seção, vamos construir parsers para gramáticas livres de contexto. As
-- regras têm a forma `A → B₁ ⋯ Bₙ`, em que cada `Bᵢ` pode ser um terminal ou
-- um não terminal. Regras com o mesmo símbolo à esquerda podem ser reunidas
-- com `|`, que indica escolha. Para transformar a gramática em um parser,
-- vamos partir de parsers básicos e combinadores de parsers.

-- Considere a entrada `[every, wizard, smiled]` e a gramática abaixo. Para
-- analisar a entrada como `S`, o parser usa a única regra `S → NP VP`. Ele
-- precisa primeiro analisar um prefixo da entrada como `NP`. A produção de
-- `NP` tem quatro alternativas, e o parser tenta todas. As duas primeiras
-- falham, porque a entrada não começa com `Alice` nem com `Dorothy`. A
-- terceira, `D N`, pede um `D` e depois um `N`. Entre as alternativas de `D`,
-- só `every` dá certo, e sobra `[wizard, smiled]`. Sobre esse resto, a
-- alternativa `dwarf` de `N` falha e `wizard` dá certo, e sobra `[smiled]`. A
-- quarta, `D ADJS N`, também lê `every`, mas falha em seguida: `ADJS` pede
-- pelo menos um `ADJ`, e `wizard` é alternativa de `N`. Assim `NP` reconhece
-- o prefixo `every wizard` e deixa `[smiled]` para o `VP`, que reconhece
-- `smiled` e não deixa resto algum. Essa estratégia, que parte do símbolo
-- inicial e desce pelas regras até os terminais, é chamada de **descida
-- recursiva**.

-- S    ::= NP VP ;
-- NP   ::= "Alice" | "Dorothy" | D N | D ADJS N ;
-- ADJS ::= ADJ "..." ADJ ;
-- VP   ::= "smiled" | "laughed" ;
-- D    ::= "every" | "some" | "no" ;
-- ADJ  ::= "happy" | "evil" ;
-- N    ::= "dwarf" | "wizard" ;

-- Em Lean, `StateT` é um construtor de tipos. Como mostra o `#print` a
-- seguir, ele recebe três parâmetros: o tipo `σ` do estado, um construtor de
-- tipos `m` e o tipo `α` do resultado. Então `StateT σ m α` é o tipo das
-- funções `σ → m (α × σ)`. Cada função recebe um estado e devolve, dentro de
-- `m`, um resultado e um novo estado.

-- Para implementar um parser, usamos `List α` como estado, pois a lista
-- representa a parte da entrada que ainda falta analisar. Escolhemos `List`
-- para `m`, de modo que o parser possa devolver zero, uma ou várias
-- respostas.

-- Substituindo, `StateT (List α) List β` é `List α → List (β × List α)`, como
-- o `example` abaixo confirma. A vantagem de reusar `StateT` é que as
-- operações para combinar parsers, que veremos a seguir, já vêm prontas com
-- ele, e não precisamos defini-las.

#print StateT

abbrev Parser (α β : Type) := StateT (List α) List β

example {α β : Type} :
    Parser α β = (List α → List (β × List α)) := rfl

-- Em `Parser α β`, `α` é o tipo dos símbolos da entrada e `β` é o tipo do
-- resultado, que pode ser uma árvore. Cada par devolvido pelo parser contém
-- um resultado e o resto da entrada correspondente. Quando o parser produz
-- duas árvores distintas com o mesmo resto, elas são duas análises do mesmo
-- prefixo.

-- A expressão `p.run xs` aplica o parser `p` à entrada `xs`. Para transformar
-- um valor `r : β` em um parser, usamos `pure r`. Ao receber `xs`, esse
-- parser produz exatamente uma análise, `[(r, xs)]`. O resultado é `r` e o
-- resto é a própria entrada. No primeiro exemplo, `pure 2` produz o número
-- `2` e deixa os dois caracteres de `"ab"` intactos.

-- Já `failure` produz `[]` para qualquer entrada. A lista vazia indica que
-- não houve análise. Tanto `pure` quanto `failure` podem ser usados para
-- qualquer tipo de resultado `β`.

#eval (pure 2 : Parser Char Nat).run "ab".toList
#eval (failure : Parser Char Nat).run "ab".toList

-- O parser `symbol c` reconhece um símbolo `c` no início da entrada. Se a
-- lista começa com `c`, ele devolve esse símbolo e deixa a cauda da lista
-- como resto. Se a lista é vazia ou começa com outro símbolo, a análise
-- falha.

-- Podemos generalizar esse parser para reconhecer uma lista inteira de
-- símbolos, chamada aqui de **token**. O parser `token cs` usa `List.take`
-- para comparar `cs` com o prefixo da entrada de mesmo comprimento. Se forem
-- iguais, devolve `cs` e usa `List.drop` para obter o resto. Assim,
-- `symbol c` devolve um símbolo e `token cs` devolve uma lista de símbolos.

-- O parser `satisfy p` reconhece o primeiro símbolo da entrada quando ele
-- satisfaz a propriedade `p`. Por exemplo, `digit` usa `Char.isDigit` para
-- reconhecer um dígito no início de uma lista de caracteres.

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

#eval (symbol 'a').run "abc".toList
#eval (token "ab".toList).run "abcde".toList
#eval digit.run "42".toList

-- ### Exercise (1 star): symbol-satisfy ⭐

-- Defina `symbol'`, que faz o mesmo que `symbol`, usando `satisfy`.

def symbol' {α : Type} [BEq α] (c : α) : Parser α α :=
  sorry

theorem symbol'_eq_symbol {α : Type} [BEq α] (c : α)
    (xs : List α) : symbol' c xs = symbol c xs := by
  sorry

-- A escolha do tipo da entrada determina o que conta como um símbolo. Se a
-- entrada é uma lista de palavras, `Alice` é um único símbolo de tipo
-- `String`. Se a entrada é uma lista de caracteres, `Alice` é um token de
-- cinco símbolos de tipo `Char`.

#eval
  let s : String := "Alice"
  let xs : List String := ["Alice", "laughed"]
  (symbol s).run xs
#eval
  let tk : List Char := "Alice".toList
  let xs : List Char := "Alice laughed".toList
  (token tk).run xs

-- Com esses parsers elementares, podemos reconhecer os terminais da
-- gramática. Para analisar os não terminais, precisamos combinar parsers,
-- seja para reunir alternativas, seja para aplicá-los em sequência.

-- Uma função que constrói um parser a partir de outros parsers é chamada de
-- **combinador de parsers**. Um primeiro exemplo é `just`. O parser `just p`
-- aplica `p` à entrada e mantém apenas os pares cujo resto é vazio, isto é,
-- as análises que consomem a entrada inteira.

def just {α β : Type} (p : Parser α β) : Parser α β
 | xs => (p xs).filter fun (_, ys) => ys.isEmpty

-- Para representar a escolha entre duas alternativas, usamos `p <|> q`. Os
-- dois parsers recebem a mesma entrada, e o resultado é a concatenação das
-- listas de análises, com as de `p` primeiro. Se ambos tiverem sucesso, as
-- análises de ambos aparecem no resultado.

-- Por exemplo, para reconhecer `VP → smiled | laughed` em uma lista de
-- palavras, podemos usar `symbol "smiled" <|> symbol "laughed"`. O `example`
-- mostra a igualdade que caracteriza a escolha para parsers.

example {α β : Type} (p q : Parser α β) (xs : List α) :
    (p <|> q) xs = p xs ++ q xs := rfl

-- Até aqui, os parsers de terminais devolvem os símbolos reconhecidos. Para
-- obter uma árvore, precisamos transformar o resultado da análise. A
-- expressão `f <$> p` aplica a função `f` ao resultado de cada análise de
-- `p`, preservando o resto da entrada de cada uma. Se `p : Parser α β` e
-- `f : β → γ`, então `f <$> p : Parser α γ`.

-- Por exemplo, `digit` devolve um caractere. O parser `digitize` usa `<$>`
-- para convertê-lo no número natural que ele representa. Na entrada
-- `"42".toList`, o resultado é `4` e o resto é `['2']`. Na entrada
-- `"x2".toList`, a análise falha já no primeiro caractere.

-- Um construtor de tipos `m` equipado com uma operação `<$>` que transforma
-- uma função de `β` em `γ` em uma função de `m β` em `m γ`, e que obedece a
-- certas leis, é chamado de **funtor**. Para listas, `f <$> xs` é `xs.map f`.
-- Para parsers, a transformação ocorre nos resultados das análises.

example {α β γ : Type} (f : β → γ) (p : Parser α β)
    (xs : List α) :
    (f <$> p) xs =
      (p xs).flatMap fun (r, ys) => [(f r, ys)] := rfl

def digitize : Parser Char Nat :=
  (fun c => c.toNat - '0'.toNat) <$> digit

#eval digitize.run "42".toList
#eval digitize.run "x2".toList

example : (· + 1) <$> [1, 2, 3] = [1, 2, 3].map (· + 1) :=
  by decide

-- Usaremos `<$>` para construir árvores sintáticas. Os parsers terão o tipo
-- `Parser α (ParseTree α β)`. Os terminais, de tipo `α`, aparecem nas folhas.
-- Os rótulos dos nós internos, de tipo `β`, identificam os não terminais da
-- gramática.

-- Para um terminal `s`, `symbolT s` aplica o construtor `.leaf` ao resultado
-- de `symbol s`. Uma regra como `D → every | some | no` também deve aparecer
-- na árvore. Por isso, `det` escolhe um dos três parsers de terminais e põe a
-- folha resultante sob um nó rotulado `"D"`. O mesmo procedimento dá os
-- parsers de `ADJ`, `N` e `VP`.

def symbolT {α β : Type} [BEq α] (s : α)
  : Parser α (ParseTree α β) := .leaf <$> symbol s

def det : Parser String (ParseTree String String) :=
  (fun t => .branch "D" [t]) <$>
    (symbolT "every" <|> symbolT "some" <|> symbolT "no")

def adj : Parser String (ParseTree String String) :=
  (fun t => .branch "ADJ" [t]) <$>
    (symbolT "happy" <|> symbolT "evil")

def n : Parser String (ParseTree String String) :=
  (fun t => .branch "N" [t]) <$>
    (symbolT "dwarf" <|> symbolT "wizard")

def vp : Parser String (ParseTree String String) :=
  (fun t => .branch "VP" [t]) <$>
    (symbolT "smiled" <|> symbolT "laughed")

#eval det.run ["every", "wizard", "smiled"] |>.map
  fun (t, ys) => (toString t, ys)

-- Para analisar a regra `NP → D N`, primeiro aplicamos `det` à entrada. Para
-- cada análise obtida, aplicamos `n` ao resto.

-- Para encadear esses passos, usamos `>>=`. Em `p >>= f`, analisamos a
-- entrada com `p`. Para cada par `(r, ys)` devolvido, `f r` constrói o parser
-- que será aplicado ao resto `ys`. O `List.flatMap` do primeiro exemplo reúne
-- em uma única lista todas as análises obtidas dessa maneira. No segundo
-- exemplo, o primeiro passo obtém a árvore de `D`, o segundo obtém a de `N`,
-- e `pure` devolve o nó `NP` sem consumir mais símbolos.

example {α β γ : Type} (p : Parser α β) (f : β → Parser α γ)
    (xs : List α) :
    (p >>= f) xs =
      (p xs).flatMap fun (r, ys) => f r ys := rfl

#eval
  (det >>= fun td =>
    n >>= fun tn =>
      pure (ParseTree.branch "NP" [td, tn])).run
    ["every", "wizard", "smiled"] |>.map
  fun (t, ys) => (toString t, ys)

-- A notação `do` permite escrever a sequência anterior com um passo por
-- linha. Em `let td ← det`, aplicamos `det` e damos o nome `td` à árvore
-- obtida. O próximo passo aplica `n` ao resto deixado por `det`. Na última
-- linha desse bloco `do`, `return e` tem o mesmo efeito que `pure e`. A
-- expressão `e` constrói o nó `NP` com as árvores `td` e `tn`. Para cada par
-- de árvores obtido nos passos anteriores, esse último passo devolve o nó e
-- mantém o resto deixado por `n`. O primeiro `example` verifica a igualdade
-- com a versão que usa `>>=` e `pure`.

-- Um construtor de tipos com operações `pure` e `>>=` que obedecem a certas
-- leis é chamado de **mônada**. A notação `do` funciona para qualquer mônada.
-- Essas operações também permitem definir `<$>`: aplicamos o parser e
-- devolvemos o resultado transformado com `pure`. O segundo `example` mostra
-- essa igualdade para parsers.

example :
    (det >>= fun td =>
       n >>= fun tn =>
         pure (ParseTree.branch "NP" [td, tn])) =
    (do
      let td ← det
      let tn ← n
      return ParseTree.branch "NP" [td, tn]) := rfl

example {α β γ : Type} (f : β → γ) (p : Parser α β) :
    (f <$> p) = (do
      let r ← p
      return f r) := rfl

-- O lado direito de uma regra pode ter qualquer número de terminais e não
-- terminais. Para aplicar seus parsers em sequência, usamos `collect ps`. A
-- função recebe uma lista de parsers com o mesmo tipo de resultado e constrói
-- um parser que devolve a lista dos resultados, na mesma ordem.

-- Se a lista de parsers é vazia, `pure []` produz uma análise cujo resultado
-- é `[]` e cujo resto é a entrada inteira. Para `p :: ps`, aplicamos `p`,
-- aplicamos `collect ps` ao resto e acrescentamos o primeiro resultado à
-- lista dos demais. Por exemplo, `collect [det, n]` produz as duas árvores
-- que usamos para construir o nó `NP`.

-- Para obter a árvore da regra inteira, usamos `parseAs`. Para uma regra
-- `A → B₁ ⋯ Bₙ`, passamos o rótulo de `A` e a lista dos parsers de
-- `B₁, …, Bₙ`. A função aplica `collect` e, com `<$>`, reúne as árvores
-- obtidas sob um nó com o rótulo de `A`. Com um único parser, o `example`
-- mostra que isso dá a mesma construção que usamos em `det`.

def collect {α β : Type} :
    List (Parser α β) → Parser α (List β)
  | [] => pure []
  | p :: ps => do
    let r ← p
    let rs ← collect ps
    return r :: rs

#eval (collect [det, n]).run
    ["every", "wizard", "smiled"] |>.map
  fun (ts, ys) => (ts.map toString, ys)

def parseAs {α β : Type} (label : β)
  (ps : List (Parser α (ParseTree α β)))
  : Parser α (ParseTree α β) :=
  .branch label <$> collect ps

example {α β : Type} (l : β)
    (p : Parser α (ParseTree α β)) :
    parseAs l [p] = (fun t => .branch l [t]) <$> p := by
  funext xs
  simp [parseAs, collect]

-- A regra de `ADJS` pede uma sequência de um ou mais adjetivos. Se ela
-- aceitasse também a sequência vazia, `every wizard` teria duas análises como
-- `NP`, uma pela regra `D N` e outra pela regra `D ADJS N`.

-- O combinador `many1 p` aplica `p` uma ou mais vezes e devolve a lista dos
-- resultados. A primeira alternativa aplica `p` uma vez e continua
-- recursivamente. A segunda aplica `p` uma única vez. Com essa ordem, no
-- exemplo com `symbol 'a'`, a análise mais longa aparece primeiro. O
-- combinador `many p` acrescenta a possibilidade de zero ocorrências, com
-- `pure []`.

-- A chamada recursiva de `many1 p` usa o resto deixado por `p`. Como esse
-- resto fica dentro de `StateT`, o Lean não consegue verificar a diminuição
-- da entrada nessa definição. Com `partial def`, podemos definir o parser sem
-- apresentar uma prova de terminação. Nas provas, o corpo da definição fica
-- opaco. Podemos examinar seu comportamento executando-o sobre entradas
-- concretas.

-- Se `p` sempre consome pelo menos um símbolo quando tem sucesso, cada
-- chamada recursiva recebe uma lista menor. Na regra `ADJS ::= ADJ ADJS`, por
-- exemplo, `ADJ` consome uma palavra antes da chamada recursiva. Se `p` puder
-- ter sucesso deixando a entrada intacta, `many1 p` pode voltar a chamar a si
-- mesmo sobre a mesma lista.

partial def many1 {α β : Type} (p : Parser α β) :
    Parser α (List β) :=
  (do
    let r ← p
    let rs ← many1 p
    return r :: rs)
  <|> (do
    let r ← p
    return [r])

def many {α β : Type} (p : Parser α β) :
    Parser α (List β) :=
  many1 p <|> pure []

#eval (many1 (symbol 'a')).run "aab".toList
#eval (many (symbol 'a')).run "aab".toList
#eval (many1 (symbol 'a')).run "bab".toList
#eval (many (symbol 'a')).run "bab".toList

-- Já temos parsers para os terminais e para as categorias `D`, `ADJ`, `N` e
-- `VP`. Para completar a gramática, `adjs` aplica `many1 adj` e põe a lista
-- de árvores resultante sob um nó `ADJS`. O parser `np` reúne as alternativas
-- de `NP` com `<|>`, e `sent` usa `parseAs` com a sequência `[np, vp]`. Nos
-- exemplos, `just sent` mantém apenas as análises da sentença inteira.

def adjs : Parser String (ParseTree String String) :=
  .branch "ADJS" <$> many1 adj

def np : Parser String (ParseTree String String) :=
  parseAs "NP" [symbolT "Alice" <|> symbolT "Dorothy"]
  <|> parseAs "NP" [det, n]
  <|> parseAs "NP" [det, adjs, n]

def sent : Parser String (ParseTree String String) :=
  parseAs "S" [np, vp]

#eval (just sent).run ["every", "wizard", "smiled"] |>.map
  (toString ·.1)
#eval (just sent).run ["Alice", "laughed"] |>.map
  (toString ·.1)
#eval (just sent).run
    ["every", "happy", "evil", "wizard", "smiled"] |>.map
  (toString ·.1)

-- ### Exercise (2 stars): adjs-recursive ⭐⭐

-- A regra de `ADJS` também pode ser escrita sem `"..."`, de forma recursiva:

-- ADJS ::= ADJ ADJS | ADJ ;

-- Defina `adjsRec`, o parser dessa regra, com `parseAs` e uma linha por
-- alternativa. As duas regras geram as mesmas sequências de adjetivos, mas as
-- árvores são diferentes.

partial def adjsRec :
    Parser String (ParseTree String String) :=
  sorry

theorem adjsRec_happy_evil :
    ((just adjsRec).run ["happy", "evil"]).map
      (toString ·.1) =
    ["[.ADJS [.ADJ happy] [.ADJS [.ADJ evil]]]"] := by
  sorry

-- Agora troque a última alternativa por `ε`: defina `adjsEps`, o parser de
-- `ADJS ::= ADJ ADJS | ε`, e `npEps`, o parser das duas alternativas
-- `D N | D ADJS N` de `NP` com `adjsEps` no lugar de `adjs`. O último teorema
-- mostra o que acontece com `every wizard`.

partial def adjsEps :
    Parser String (ParseTree String String) :=
  sorry

def npEps : Parser String (ParseTree String String) :=
  sorry

theorem npEps_every_wizard :
    ((just npEps).run ["every", "wizard"]).map
      (toString ·.1) =
    ["[.NP [.D every] [.N wizard]]",
     "[.NP [.D every] [.ADJS ] [.N wizard]]"] := by
  sorry

-- A descida recursiva exige cuidado com a posição da chamada recursiva. Em
-- uma regra como `A → A a`, o parser de `A` chama a si mesmo sobre a mesma
-- entrada, antes de tentar reconhecer `a`, como ilustra `leftRec`. Isso
-- também pode ocorrer se os símbolos antes da chamada recursiva aceitarem a
-- entrada vazia.

-- No reconhecedor por divisão da seção Reconhecendo e Analisando Linguagens
-- Livres de Contexto, os pedaços externos das regras recursivas têm um
-- símbolo cada, o que permitia provar que as chamadas recursivas recebiam
-- entradas menores. Existem combinadores de parsers que garantem a terminação
-- e aceitam recursão à esquerda (Danielsson, 2010).

partial def leftRec : Parser Char (ParseTree Char Char) :=
  parseAs 'A' [leftRec, symbolT 'a']
  <|> parseAs 'A' [symbolT 'b']

-- THE FOLLOWING DETAILS CAN BE SKIPPED (Contornando a recursão à esquerda)
-- Toda gramática livre de contexto pode ser reescrita sem recursão à
-- esquerda, sem mudar a linguagem que ela gera. A gramática de `leftRec`,
-- `A → A a | b`, gera as palavras formadas por um `b` seguido de zero ou mais
-- `a`. A mesma linguagem é gerada por `A → b A'` e `A' → a A' | ε`, com um
-- novo não terminal `A'`. Agora toda chamada recursiva vem depois de consumir
-- um `b` ou um `a`, e o parser termina. O preço é que as árvores mudam. Para
-- `baa`, a gramática original dá `[.A [.A [.A b] a] a]`, uma árvore que
-- cresce para a esquerda; a nova dá uma árvore que cresce para a direita, com
-- os nós `A'`. Se a forma da árvore importa, por exemplo para a interpretação
-- semântica, é preciso converter uma árvore na outra.

-- Há também algoritmos que analisam qualquer gramática livre de contexto,
-- inclusive com recursão à esquerda, como CKY e Earley. Em vez de descer
-- pelas regras, eles guardam numa tabela as análises já encontradas para cada
-- trecho da entrada. A seção Leituras adicionais traz referências.
-- END DETAILS

-- ### Exercise (2 stars): palindrome-parser ⭐⭐

-- Defina `palindrome`, um parser para a gramática dos palíndromos sobre
-- `{a, b, c}`, com uma linha por regra. Cada regra usada vira um nó com
-- rótulo `A`, inclusive `A → ε` e as regras que só têm um terminal à direita:

-- A ::= ε | "a" | "b" | "c" | "a" A "a" | "b" A "b" | "c" A "c" ;

-- Como o parser é recursivo, a definição é `partial def`, e os testes abaixo
-- são verificados executando o parser, com `native_decide`. O segundo mostra
-- que, sem `just`, o parser também devolve as análises de prefixos da
-- entrada, com o seu resto.

partial def palindrome :
    Parser Char (ParseTree Char Char) :=
  sorry

theorem palindrome_abcba :
    ((just palindrome).run "abcba".toList).map
      (toString ·.1) = ["[.A a [.A b [.A c] b] a]"] := by
  sorry

theorem palindrome_aba :
    (palindrome.run "aba".toList).map
      (fun (t, ys) => (toString t, String.ofList ys)) =
    [("[.A ]", "aba"),
     ("[.A a]", "ba"),
     ("[.A a [.A b] a]", "")] := by
  sorry

-- Em resumo, usamos `symbolT` para obter a folha de um terminal `t`. Para uma
-- regra com não terminal `A` à esquerda, usamos `parseAs` com o rótulo de `A`
-- e a lista de parsers dos símbolos à direita, na ordem em que aparecem.
-- Quando há mais de uma alternativa, reunimos os parsers correspondentes com
-- `<|>`. Se a regra tem um só símbolo à direita, podemos usar `<$>` para pôr
-- o resultado do parser desse símbolo sob um nó rotulado com `A`, como
-- fizemos com as categorias cujas alternativas têm um só terminal. Para uma
-- repetição como `ADJ "..." ADJ`, usamos `many1` para aplicar o parser de
-- `ADJ` uma ou mais vezes.

end Parsing

