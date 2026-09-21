import Mathlib.Tactic
import CSwLCompat

-- # Programação Funcional no Lean

-- Neste capítulo, apresentamos o essencial sobre a linguagem de programação
-- Lean. Nosso objetivo é apresentar o suficiente para que o leitor possa
-- acompanhar os exemplos do restante do livro. Para uma apresentação
-- completa, sugerimos a leitura de (Christiansen, 2023) e (FRO, 2026).

namespace IntroL

-- ## Termos e Tipos

-- Em Lean, um termo é uma expressão sintaticamente válida que representa um
-- objeto e possui um tipo.

-- Semanticamente, tipos como conjuntos, mas eles não são conjuntos. Podemos
-- pensar em tipos como classes para classificarmos termos. Com tipos podemos
-- impor uma disciplina que a matemática segue apenas implicitamente. No papel
-- podemos escrever `1 ∈ 2`, mas em Lean a tipagem marca a expressão como um
-- erro.

-- Alguns tipos básicos já estão definidos no sistema como `ℕ`, `ℤ`, `ℚ` ou
-- `Bool`. Se `σ` e `τ` são tipos, `σ → τ` representa o tipo das funções de
-- `σ` em `τ`. Um tipo é de ordem superior quando tem `→` aninhada à esquerda
-- de outra `→`, como em `(ℤ → ℤ) → ℚ`: o tipo das funções que recebem uma
-- função de `ℤ` em `ℤ` e devolvem um `ℚ`.

-- Ao abrir um arquivo Lean, podemos além de escrever declarações, podemos
-- interagir diretamente com o sistema através de comandos. Comandos são
-- prefixados com `#`. O comando `#eval` calcula o valor de um termo.

#eval 1 + 2
#eval "Olá, " ++ "mundo"

-- Uma `def`inição introduz um nome no ambiente. Os dois-pontos anunciam o
-- tipo, e o `:=` dá o valor. `100` é um termo do tipo `Nat`, e `"Chomsky"` é
-- um termo do tipo `String`. Em alguns contextos, o tipo não precisa ser
-- declarado quando Lean consegue descobri-lo sozinho. Escrever `def n := 100`
-- funciona, porque Lean irá interpretar `100 : ℕ` e logo estabelecer que a
-- constante `n : ℕ`, mas escrever o tipo é conveniente e ajuda a tornar o
-- código mais legível. O comando `#check` pergunta ou confirma o tipo, sem
-- calcular nada.

def author : String := "Chomsky"

#eval  author
#check author
#check (author : String)

-- Tipos também são termos, e portanto têm tipo. O tipo de `true` é `Bool`, o
-- tipo de `Bool` é `Type`, e o de `Type` é `Type 1`. Esta hierarquia de
-- universos existe para que não exista um tipo de todos os tipos, o que
-- produziria um paradoxo. Para nós, em geral, basta saber que a pergunta
-- "qual o tipo disto?" tem sempre resposta.

#check true
#check Bool
#check Nat
#check Type

-- ## Funções

-- O tipo `Nat → Nat` representa todas as funções que recebem um número natual
-- e devolvem um número natural. O termo `fun x : Nat => x * x` é uma
-- particular função deste tipo. Ao aplicar o termo `12 : Nat`, temos o
-- `144 : Nat` como resposta. Ao invés de `fun` podemos usar `λ` e ao invés de
-- `=>` podemos usar `↦`, em Lean podemos usar os caracteres unicode.

#check (λ x ↦ x * x) 12
#eval (λ x ↦ x * x) 12

-- Mas podemos nomear abstrações, principalmente quando queremos que elas
-- possam ser reusadas. E em Lean podemos usar caracteres unicode como
-- mostramos a seguir.

def square₁ : Nat → Nat :=
  fun x => x * x

-- Normalmente pode ser conveniente nomear os parâmetros de uma função. A
-- seguir, parâmetros de mesmo tipo podem ser agrupados.

def square₂ (x : ℕ) : ℕ := x * x

def agePlusNameSize (age : ℕ) (name : String) : ℕ :=
  age * name.length

def maximum (n k : Nat) : Nat :=
  if n < k then
    k
  else n

-- O nome do argumento não importa, as duas funções abaixo são iguais, como
-- podemos comprovar pela prova abaixo usando `rfl`.

example :
    (λ (x : Nat) => x * x) = (λ (z : Nat) => z * z) := rfl

-- Nomes são definidos em `namespaces`. As definições deste capítulo estarão
-- no namespace `IntroL`. A notação `name.length` acima infere pelo tipo de
-- `name` que estamos falando da função `length` definida no namespace
-- `String` mesmo nome do tipo `String`. Ver (Christiansen, 2023).

-- Perguntado sobre um nome que foi definido, o `#check` responde com a
-- assinatura, e não com o tipo seta. Envolver o nome em parênteses força a
-- segunda forma. Mas as duas dizem o mesmo. As três versões de `square` tem o
-- mesmo tipo e como veremos, podemos provar que são iguais.

#check square₂
#check (square₂)

-- As vezes podemos querer introduzir uma constante ou tipo sem especificar
-- seu comportamento o valor. Para isso usamos `opaque`, um símbolo com o tipo
-- mas sem implementação. Exemplos de (Baanen et al., 2026).

opaque a : ℕ
opaque b : ℕ
opaque f : ℕ → ℕ
opaque g : ℕ → ℕ → ℕ

-- Conferir tipo não demanda computação, logo o comando `#check` funciona
-- retornando o tipo da expressão sem avaliá-la.

#check g a

-- Os exercícios deste capítulo vêm com **testes** escritos como teoremas
-- simples. Um `example` enuncia uma afirmação sem lhe dar nome; o que vem
-- depois do `:=` é a justificativa. A tática `rfl` fecha uma igualdade quando
-- os dois lados **calculam** o mesmo valor — é o que confere se a definição
-- pedida faz o que se pediu. Um `theorem` é um `example` com nome, e o nome
-- serve para que o enunciado possa ser referenciado depois, possivelmente na
-- prova de outro teorema. Aqui esses três recursos aparecem só como
-- ferramenta de teste. O que significa provar em Lean, e como se constrói uma
-- prova que `rfl` não fecha sozinha, é o assunto de Prova em Lean.

-- ### Exercise (1 star): sum-of-squares ⭐

-- Defina `sumOfSquares` que recebe dois naturais e devolve `m² + n²`. Para
-- fechar o exemplo, use `rfl`.

def sumOfSquares (m n : Nat) : Nat :=
 sorry

example : sumOfSquares 3 4 = 25 := sorry

-- Lean é uma linguagem muito extensiva, boa parte de Lean é escrita em Lean,
-- usando os recursos de *meta programação*. Os operadores `+` ou `*` entre
-- outros são símbolos sintáticos associados a definições. Lean tem um
-- mecanismo de `classes` para definir operadores polimorficos como o `+` para
-- os naturais (interpretado como a função `Nat.add`) ou para números de ponto
-- flutuante.

#eval Nat.add 2 2
#eval Float.add 2.1 2
#eval 2.1 + 2

-- Podemos forçar o tipo do primeiro argumento, definimos qual multiplicação
-- estamos interessados. O segundo argumento, `10`, recebe o tipo
-- correspondente.

#eval (1 : Int) * 10
#eval (1 : Float) * 10

-- No comando abaixo, o tipo de `x` é algo como `?m.7`. Isto significa que
-- Lean sem dizer o tipo de `x`, Lean não tem como saber qual o `*` desejado,
-- `Nat`, `Int`, ou qualquer outro tipo com multiplicação. O `?m.7` é uma
-- *metavariável*: um buraco que Lean deixa em aberto à espera de informação
-- que decida a questão.

#check fun x => x * x

-- Anotar o argumento resolve, e a resposta passa a ser o tipo esperado. O
-- contexto também resolve. Aplicada a `4`, a função agora é sobre `Nat`
-- assumida a interpretação padrão de números como `Nat`.

#check fun (x : Nat) => x * x
#check (fun x => x * x) 4

-- Funções podem ser passadas como *argumento* para outras funções.
-- `tranformWord` recebe uma função, e é isso que o torna uma função de ordem
-- superior.

def pluralize (w : String) : String := w ++ "s"

def transformWord (f : String → String) (w : String) : String :=
  f w

#eval transformWord pluralize "dragon"

-- Uma função também pode ser produzida como resultado. O que é equivalente a
-- uma avaliação parcial. Abaixo, a função `h₁` recebe dois naturais para
-- produzir a saída. A função `h₂` recebe um natural, para então devolver a
-- função que ao receber um natural irá produzir como saída a soma dos dois
-- valores recebidos. O interessante que não preciso escrever `h₁` como `h₂`,
-- é perfeitamente aceitável passar apenas um dos argumentos para `h₁` e ver
-- que o tipo da expressão resultante.

def h₁ (x y : Nat) : Nat :=
  x + y

def h₂ (x : Nat) : (Nat → Nat) :=
  fun y => x + y

#check h₁ 1

-- ## Expressões

-- Uma *expressão* é uma construção sintática da linguagem. Toda expressão é
-- um termo. Um *termo canônico* é um termo que já está na forma final de sua
-- computação, não podendo ser reduzido. Construções sintáticas que
-- normalmente não tem valor em linguagens imperativas, também são termos em
-- Lean.

-- O `let` nomeia um valor dentro de uma expressão, e a expressão inteira tem
-- valor. O ponto-e-vírgula é uma alternativa a quebra de linha e alinhamento
-- de identação.

#eval
  let a := (let a := 10; a) + (let b := 10; b)
  a

-- O `if-then-else` também é expressão. Os dois ramos têm de ter o mesmo tipo.
-- É por isso que o resultado pode ser atribuído:

#eval
  let a := if 5 < 10 then 1 else 0
  a

-- ## Estruturas

-- Uma `structure` agrupa vários valores num só, dando nome a cada campo.
-- `Point` tem dois campos, `x` e `y`, ambos `Float`. E a estrutura introduz
-- um novo tipo chamado `Point` e um `namespace` de mesmo nome.

structure Point where
  x : Float
  y : Float
deriving Repr

-- Além do tipo, algumas definições como `Point.mk`, função (construtor) que
-- cria termos do tipo `Point` também são criadas pela declaração acima.
-- Também podemos usar a sintaxe com chaves. Para mais detalhes, ver
-- (Christiansen, 2023).

def origin₁ : Point := { x := 0.0, y := 0.0 }
def origin₂ : Point := Point.mk 0.0 0.0

#eval origin₁
#check Point.mk

-- Cada campo tem uma função de projeção. No exemplo, `Point.x` e `Point.y`.
-- Todas as funções introduzidas na declaração da estrutura ficam no namespace
-- criado pelo comando `structure`.

#eval origin₁.x

-- A notação `⟨_, _⟩` é a **notação de anônima** para o construtor: serve
-- quando o tipo esperado já deixa claro qual construtor usar.

def origin₃ : Point := ⟨0.0, 0.0⟩

-- Uma função sobre `Point` também pode desmontar o argumento com `⟨_, _⟩`, em
-- vez de projetar campo a campo:

def addPoints (p1 p2 : Point) : Point :=
  ⟨p1.x + p2.x, p1.y + p2.y⟩

#eval addPoints origin₁ ⟨1.0, 2.0⟩

-- Também podemos usar `with` para criar uma cópia da estrutura alterando só
-- alguns campos. Isti é útil quando a `structure` tem muitos campos.

def scaleX (p : Point) (factor : Float) : Point :=
  { p with x := p.x * factor }

#eval scaleX ⟨2.0, 3.0⟩ 10.0

-- ## Tipos Indutivos

-- Tipos indutivos vêm antes da recursão porque, em Lean, uma função recursiva
-- se escreve casando padrão sobre as formas de um tipo indutivo: sem o tipo
-- declarado, não há sobre o que recursar.

-- A palavra-chave `inductive` declara um tipo listando as formas que seus
-- valores podem ter. Quando nenhuma forma carrega argumento, o tipo é uma
-- enumeração; quando carrega, é um registro variante; quando a forma se
-- refere ao próprio tipo sendo definido, é uma árvore. As três coisas são o
-- mesmo mecanismo.

-- Essa é a construção mais importante do curso. Em Batalha Naval veremos que
-- uma gramática escrita na notação usual — a Forma de Backus-Naur — é
-- literalmente um tipo `inductive`, e daí em diante todo fragmento da língua
-- é declarado assim. A enumeração é o caso mais simples.
-- `deriving Repr, DecidableEq` pede que a exibição e o teste de igualdade
-- sejam gerados em vez de escritos à mão. Os dias da semana, nada mais são
-- dias da semana.

inductive Day where
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday
deriving Repr

-- ### Exercise (1 star): is-weekend ⭐

-- Complete `isWeekend`, que responde se o dia é sábado ou domingo.

def isWeekend (d : Day) : Bool :=
 sorry

-- O tipo `Bool` é a enumeração de duas formas, dois construtores. O tipo
-- `Nat` é o caso em que uma das formas se refere ao próprio tipo que está
-- sendo definido. Podemos usar `#print Nat` para mostrar a declaração do tipo
-- `Nat`.

example : 2 = Nat.succ (Nat.succ Nat.zero) := rfl

-- ## Recursão

-- Uma definição recursiva precisa de duas coisas: ter caso base, e chegar
-- nele. O segundo não é uma recomendação — é uma exigência que o compilador
-- verifica, e a definição é rejeitada se ele não conseguir ver que a recursão
-- termina.

-- Em `Nat`, os dois casos do tipo dão as duas coisas de uma vez. Casar por
-- `0` (`Nat.zero`) e `n + 1` (`Nat.succ n`). O caso base é `0`, e a chamada
-- recursiva recebe o `n` que estava dentro do `succ`, necessariamente menor.
-- Não há um terceiro caso a esquecer, e não há argumento para o qual a função
-- não responda.

-- O fatorial é o exemplo mínimo dessa forma: um caso base e um caso que chama
-- a si mesmo com um argumento menor.

def factorial : Nat → Nat
  | 0     => 1
  | n + 1 => (n + 1) * factorial n

-- A mesma função sem casar padrão, decidindo o caso base com um `if`.
-- Funciona, e serve de contraste: aqui o argumento da chamada recursiva é
-- `x - 1`, e que ele seja menor que `x` é um fato a ser verificado, não algo
-- que a forma da definição já garanta. Neste caso Lean verifica sozinho; em
-- definições menos óbvias, não — e aí a prova de terminação passa a ser
-- trabalho do programador.

def factorial' (x : Nat) : Nat :=
  if x = 0 then 1
  else x * factorial' (x - 1)

-- O casamento de padrão de `factorial` é um *açucar sintático*, na verdade a
-- expressão `match` está oculta na definição. A seguir, usamos de forma
-- explicita. Como exemplo, vamos implementar em Lean um gerador recursivo de
-- sentença.

def gen (x : Nat) : String :=
  match x with
  | 0     => "Sentences can go on"
  | n + 1 => gen n ++ " and on"

def genS (n : Nat) : String := gen n ++ "."

-- A função `story` a seguir fornece outro exemplo de recursão.

def story : Nat → String
  | 0     =>
    "Let's cook and eat that final missionary, " ++
    "and off to bed."
  | k + 1 =>
    "The night was pitch dark, mysterious and deep.\n" ++
    "Ten cannibals were seated around a boiling " ++
    "cauldron.\n" ++
    "Their leader got up and addressed them like " ++
    "this:\n'" ++
    story k ++ "'"

-- podemos usar `#eval story 2` direto, mas as quebras de linha não seriam
-- interpretadas. o símbolo `<|` faz com que a expressão `story 2` seja
-- executada antes de passada para a função `IO.println` que efetivamente
-- interpreta as quebras de linha e outros caracteres especiais que possam
-- estar contidos em uma string.

#eval IO.println <| story 2

-- ### Exercise (1 star): sum-to ⭐

-- Implemente `sumTo n` para devolver `0 + 1 + ... + n` e termine a prova de
-- que a função está correta para a entrada `4`.

def sumTo : Nat → Nat :=
  sorry

theorem sumTo_test : sumTo 4 = 10 := sorry

-- ## Listas e Polimorfismo

-- `List α` é o tipo das listas de elementos do tipo `α`, e é um tipo indutivo
-- como os da seção anterior: uma lista é vazia, `[]` (`List.nil`), ou é um
-- elemento seguido de uma lista, `x :: xs` (`List.cons`). Nada mais é uma
-- lista.

#print List

-- É por isso que a recursão sobre lista tem exatamente a forma da recursão
-- sobre `Nat`. Dois casos, e o segundo dá acesso a algo estritamente menor,
-- aqui a cauda. O `α` em `List α` é um parâmetro: `List Nat` e `List String`
-- são tipos diferentes, produzidos pelo mesmo `List`. Uma função que não olha
-- para dentro dos elementos não tem por que se comprometer com um deles. Como
-- já falamos, `{α : Type}` declara o parâmetro entre chaves, o que o torna
-- *implícito*. Lean o descobre a partir do argumento, e quem chama não
-- escreve.

def size {α : Type} : List α → Nat
  | []      => 0
  | _ :: xs => 1 + size xs

-- ### Exercise (1 star): sum-list ⭐

-- Complete `sumList` que soma os elementos de uma lista.

def sumList (ns : List Nat) : Nat :=
  sorry

theorem sumList_test : sumList [1, 2, 3, 4] = 10 := sorry

-- ### Exercise (1 star): count-zeros ⭐

-- Termina a implementação de `countZeros`, que conta quantos zeros temos na
-- lista passada.

def countZeros (ns : List Nat) : Nat :=
  sorry

theorem countZeros_test : countZeros [0, 1, 0, 2, 0] = 3 :=
  sorry

-- ## O tipo `Option`

-- Uma função de tipo `List α → α` promete devolver um elemento para qualquer
-- lista que receba. Para a lista vazia não existe elemento nenhum, e a
-- promessa é impossível. A correção é no tipo, não no corpo:
-- `List α → Option α` promete devolver *ou* um elemento (`some x`) *ou* nada
-- (`none`). Quem chama fica obrigado a tratar os dois casos. O ganho é que o
-- caso sem resposta deixa de ser invisível: ele está na assinatura, não pode
-- ser ignorado.

def myLast {α : Type} : List α → Option α
  | []      => none
  | [x]     => some x
  | _ :: xs => myLast xs

def average (xs : List Int) : Option Rat :=
  if xs.isEmpty then none
  else some ((xs.sum : Rat) / (xs.length : Rat))

-- Como alternativa ao retorno de um `Option`, algumas funções como
-- `String.back` retornam o valor *default* do tipo que retornam. O tipo
-- `Char` tem como valor default `'A'`.

#eval (default : Char)
#eval "".back

-- ## Processamento de Listas

-- Algumas operações cobrem quase todo uso de lista no curso. Todas se
-- escreveriam por recursão, como `size` acima, mas estas função de ordem
-- superior simplificam nosso trabalho.

-- A função `List.map` aplica uma função a cada elemento; `List.filter` filtra
-- a lista com os que satisfazem uma condição. A `List.foldl` (e também temos
-- a `List.foldr`) reduzem a lista a um valor final a partir do processamento
-- sucesso de uma função.

def entities : List String :=
  ["Dorothy", "Toto", "Aunt Em", "Scarecrow"]

#eval entities.map String.length
#eval entities.filter (fun x => x.length > 4)
#eval entities.foldl (fun s a => a.length + s) 0

-- As funções `List.all` e `List.any` perguntam se *todos* os elementos
-- satisfazem uma condição, ou se *algum* satisfaz, ambas devolvem `Bool`.

#eval entities.all (fun e => e.length > 2)
#eval entities.any (fun e => e.startsWith "T")

-- ## Composição de Funções

-- E a composição: `f ∘ g` é a função que aplica `g` e depois `f`, de modo que
-- `(f ∘ g) x` é `f (g x)`. Podemos compor duas conversões, de Kelvin para
-- Celsius, depois de Celsius para Fahrenheit.

#eval (square₁ ∘ square₂) 5
#eval entities.map (size ∘ String.toList)

def celsiusToFahrenheit (c : Int) : Int := c * 9 / 5 + 32
def kelvinToCelsius (k : Int) : Int := k - 273

def kelvinToFahrenheit : Int → Int := celsiusToFahrenheit ∘ kelvinToCelsius

-- ## Classes de Tipos

-- Vamos definir uma função para contar as ocorrências de um valor de um tipo
-- `α`, em qualquer lista de valores do tipo `α`. Para esta função, nossa
-- única exigência é garantir que poderemos comparar valores do tipo `α`. Essa
-- exigência entra na assinatura entre colchetes, `[BEq α]`. Isto significa
-- que uma instância de igualdade para `α` deve estar disponível para o Lean
-- encontrar no ponto de uso. Tente remover `[BEq α]` na definição abaixo, o
-- erro irá aparecer no uso do operador `==`.

def count {α : Type} [BEq α] (x : α) : List α → Nat
  | []      => 0
  | y :: ys => if x == y then count x ys + 1 else count x ys

-- Até aqui só usamos a classe `BEq`, tanto `Nat` quanto `String` tem
-- instâncias para esta classe e por isso `count` funcionará para estes tipos.

-- Na declaração do tipo `Day`, a instrução `deriving Repr` pediu para que uma
-- instância padrão para a classe `Repr` fosse gerada. E podemos também pedir
-- para que seja gerada uma instância para `BEq`.

deriving instance BEq for Day

#eval count Day.friday [.friday, .sunday, .friday, .monday]

-- Note que para outros tipos, a noção de igualdade pode não ser tão trivial,
-- e exigir uma implementação específica. Por exemplo:

structure Angle where
  deg : Int
deriving Repr

def Angle.norm (a : Angle) : Int :=
  a.deg % 360

instance : BEq Angle where
  beq a b := a.norm == b.norm

#eval (⟨-90⟩ : Angle) == ⟨270⟩

-- Em tempo, em Lean, duas noções de igualdade convivem:

-- - `BEq α` devolve `Bool` e se escreve `==`.

-- - `DecidableEq α` devolve uma *prova* de igualdade ou de desigualdade.
--   Permite usar `=` num `if` e usar o resultado numa demonstração.

-- Outra classe relevante em Lean é a classe `Repr` para especificar como
-- valores de um tipo devem ser representados textualmente. Uma instância de
-- `Repr` não produz diretamente uma `String`; ela produz um valor de tipo
-- `Std.Format`, uma representação intermediária que descreve o texto a ser
-- exibido e permite incluir informações sobre indentação e possíveis quebras
-- de linha. Assim, ao definir uma instância de `Repr` para um tipo, estamos
-- essencialmente dizendo ao Lean como representar valores desse tipo,
-- deixando para uma etapa posterior a decisão de como essa representação será
-- efetivamente apresentada.

-- Essa separação entre a estrutura a ser impressa e sua apresentação concreta
-- é a ideia central de *pretty printing*. Em vez de decidir antecipadamente
-- onde cada linha deve terminar, construímos um documento que pode ser
-- renderizado de diferentes maneiras conforme o espaço disponível: uma
-- expressão pode aparecer em uma única linha quando couber ou ser distribuída
-- em várias linhas, com indentação apropriada, quando necessário. A abordagem
-- foi sistematizada por Wadler (Wadler, 2003) e é usada pelo `Std.Format` do
-- Lean. Para nós, isso é particularmente interessante porque mostra mais um
-- exemplo de como classes e instâncias permitem associar uma operação a um
-- tipo sem modificar sua definição: a estrutura sintática ou semântica
-- permanece a mesma, enquanto sua forma de apresentação é fornecida por uma
-- instância de Repr.

-- A seguir, vamos customizar a instância de `Day` para a classe `Repr`.
-- Usamos a palavra-chave `instance`. Não precisamos dar nome a instâncias,
-- mas neste caso usamos `insReprDay`.

instance insReprDay : Repr Day where
  reprPrec := fun d _n =>
   match d with
   | .monday    => f!"segunda"
   | .tuesday   => f!"terça"
   | .wednesday => f!"quarta"
   | .thursday  => f!"quinta"
   | .friday    => f!"sexta"
   | .saturday  => f!"sábado"
   | .sunday    => f!"domingo"

#eval Day.friday

-- ## Cadeias de Textos

-- `String` é uma sequência UTF-8 empacotada, não uma lista de caracteres.
-- Isso a torna eficiente para guardar texto e inadequada para percorrer a
-- cadeia. Não há padrão `c :: cs` para casar diretamente numa `String`. Mas
-- podemos converter uma `String` em uma lista de caracteres e uma lista de
-- caracteres em uma `String`.

def hword : List Char → Bool
  | []      => false
  | c :: cs => c == 'h' || hword cs

#eval hword "shrimptoast".toList
#eval hword "antiquing".toList

def reversal : List Char → List Char
  | []     => []
  | c :: t => reversal t ++ [c]

#eval String.ofList (reversal "Chomsky".toList)

def initS (s : String) : String :=
  String.ofList s.toList.dropLast

#eval initS "Brasil"

-- ## Lean e o Cálculo Lambda

-- No [cálculo lambda](https://en.wikipedia.org/wiki/Lambda_calculus) (LC)
-- temos três formas de construir expressões. Usando a Forma de Backus-Naur
-- (BNF) para representar a linguagem de LC.

-- E ::= _v | "(" E E ")" | "(" "λ" _v "↦" E ")" ;

-- Uma expressão é uma variável, ou a justaposição de duas expressões
-- (aplicação), ou um lambda seguido de variável e expressão (abstração). E
-- nada além disso é expressão. A gramática acima pode ser implementada como
-- um tipo indutivo. Cada cláusula da BNF corresponde a um construtor.

inductive Lam where
  | var (name : String)
  | app (fn arg : Lam)
  | abs (binder : String) (body : Lam)

-- Essa correspondência é o motor do curso. Cada fragmento de linguagem,
-- expresso como uma gramática, pode ser formalizado como um tipo `inductive`.
-- O que torna "esta expressão é bem formada" a mesma coisa que "este termo
-- tem esse tipo". O tipo `Lam` não será usado. Lean é baseado no Cálculo de
-- Construtores Indutivos (CiC), uma extensão de LC com tipos. Mas `Lam` serve
-- apenas para ilustrar a idéia de como uma gramática para uma linguagem pode
-- ser implementada como tipo indutivo. Veremos outros exemplos no decorrer do
-- texto.

-- A redução de um termo lambda significa simplificar o termo até um formato
-- que não adimite maiores simplficações. Quando aplicamos um termo a outro
-- termo, temos uma β-redução. O parâmetro da função é substituido pelo termo
-- passado como valor para a abstração no corpo da abstração. Em Lean essa
-- redução é o que o `#eval` executa e o que o `rfl` verifica:

#eval (λ x => x + 42) 5 = 5 + 42
example : (fun x => x + 42) 5 = 47 := rfl

-- A substituição de termos por termos não é trivial, considere a aplicação de
-- `x` em `(λ y λ x ↦ x + y) x`. Trocando `y` por `x`, obtém-se `λ x ↦ x + x`.
-- Mas o resultado correto é uma função que soma dois valores distintos. Em
-- Lean este tipo de erro não ocorre.

-- Um aspecto do cálculo lambda é que reduções podem não terminar. Observe o
-- comportamento de redução de `(λ x ↦ x x) (λ x ↦ x x)`. Esta expressão não é
-- bem formada em Lean. Substituindo `x` por `(λx ↦ x x)` no corpo `x x`,
-- obtém-se `(λx ↦ x x) (λx ↦ x x)`, o mesmo termo de partida. A redução é
-- portanto um laço, qualquer número de passos devolve o termo original, e a
-- normalização nunca termina. Lean acusa dois erros na declaração a seguir. A
-- auto-aplicação `x x` exige que `x` seja função de algum tipo `?m → ?n`, mas
-- o argumento é o próprio `x`, que teria então de ter simultaneamente o tipo
-- `?m`. Como não há atribuição de tipos possível, o termo não pode nem ser
-- *escrito* em Lean.

sf_expect_failure
  def omega := (fun x => x x) (fun x => x x)

-- No *cálculo lambda tipado* (LCT) no qual Lean é baseado todo termo bem
-- tipado tem forma normal, e a redução sempre termina. A contrapositiva é o
-- que se observa aqui: um termo cuja redução não termina não pode ser bem
-- tipado. É por isso que Lean pode ser ao mesmo tempo uma linguagem de
-- programação e uma lógica consistente: a terminação é garantida pelos tipos.
-- O preço é que Lean pode não conseguir determinar sozinho que uma função
-- sempre termina, e nestes casos teremos que ajudar Lean fornecendo a prova
-- de terminação.

-- Para além dos tipos simples, em Lean, temos também os **tipos indutivos**
-- (como apresentado), **tipos dependentes** (um tipo pode depender de um
-- valor, como `Vector`), **proposições como tipos**, o tipo `Prop` como
-- veremos em Proof, e os **universos** de tipos `Type`, `Type 1`, e assim por
-- diante, o que evita os paradoxos que apareceriam se tivéssemos um tipo de
-- todos os tipos.

end IntroL

