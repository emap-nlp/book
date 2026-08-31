import Mathlib.Tactic

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
-- constante `n : ℕ` — mas escrever o tipo é conveniente e ajuda a tornar o
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
-- e devolvem um número natural. O termo `fun x => x * x : Nat → Nat` é uma
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

def square₂ : ℕ → ℕ :=
  λ x ↦ x * x

-- Normalmente pode ser conveniente nomear os parâmetros de uma função. A
-- seguir, parâmetros de mesmo tipo podem ser agrupados.

def square₃ (x : ℕ) : ℕ := x * x

def agePlusNameSize (age : ℕ) (name : String) : ℕ :=
  age * name.length

def maximum (n k : Nat) : Nat :=
  if n < k then
    k
  else n

-- Nomes são definidos em `namespaces`. As definições deste capítulo estarão
-- no namespace `IntroL`. A notação `name.length` acima infere pelo tipo de
-- `name` que estamos falando da função `length` definida no namespace
-- `String` mesmo nome do tipo `String`. Ver (Christiansen, 2023).

-- Perguntado sobre um nome que foi definido, o `#check` responde com a
-- assinatura, e não com o tipo seta. Envolver o nome em parênteses força a
-- segunda forma. Mas as duas dizem o mesmo. As três versões de `square` tem o
-- mesmo tipo e como veremos, podemos provar que são iguais.

#check square₃
#check (square₃)

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

-- ### Exercise (1 star): sum-of-squares ⭐

-- Defina `sumOfSquares` que recebe dois naturais e devolve `m² + n²`.

def sumOfSquares (m n : Nat) : Nat :=
 sorry

example : sumOfSquares 3 4 = 25 := by
 sorry

-- Lean é uma linguagem muito extensiva, na verdade, boa parte de Lean é
-- escrita em Lean, usando os recursos de *meta programação*. Os operadores
-- `+` ou `*` entre outros são símbolos sintáticos associados a definições.
-- Lean tem um mecanismo de `classes` para definir operadores polimorficos
-- como o `+` para os naturais (interpretado como a função `Nat.add`) ou para
-- números de ponto flutuante.

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

-- Se função é valor, então nada impede que ela seja *argumento* de outra
-- função. `h` recebe uma função de `Nat → Nat` e um valor, e é isso que o
-- torna uma função de ordem superior.

def h (f : Nat → Nat) (x : Nat) : Nat := f x
#eval h (λ x => x + 1) 10

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

-- ### Exercise (1 star): building-terms ⭐

-- Adaptado de (Baanen et al., 2026). Cada `def` declara `{α β γ : Type}`, são
-- funções parametrizadas por tipo. Para as quatro funções abaixo, cujo tipo
-- foi definido, pede-se fornecer o termo para o tipo correspondente. Dica,
-- use `_` para identificar no *InfoView* qual tipo o termo na posição deverá
-- ter.

-- O `section` permite criar uma seção, onde definições podem compartilhar,
-- por exemplo, a declaração de variáveis. Veja o tipo de `projFst`.

section
variable {α β γ : Type}

def I : α → α :=
  fun x => x

def K : α → β → α :=
  fun a _b ↦ a

def C : (α → β → γ) → β → α → γ :=
  sorry

def projFst : α → α → α :=
  sorry

def projSnd : α → α → α :=
  sorry

def someNonsense : (α → β → γ) → α → (α → γ) → β → γ :=
  sorry

end

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

-- ## O tipo Prop e Provas

-- O que diferencia Lean de outras linguagens como Python e Java é a
-- capacidade de na mesma linguagem que usamos para 'programar' funções,
-- escrevermos 'provas' sobre estas funções.

-- Nesta 'Exemplos extraídos de (Yingchareonthawornchai, 2025). Uma proposição
-- é um enunciado que pode ser verdadeiro ou falso. O enunciado `1 = 1` é
-- verdadeiro, enquanto `square₁ 12 = 2` é falso. Toda proposição é todo tipo
-- `Prop`.

#check square₁ 12 = 2

-- Podemos declarar proposições como a seguir e verificar que `1 = 1 : Prop`,
-- mas não podemos *avaliar* uma proposição.

def p1 : Prop := 1 = 1

#check p1

-- Toda proposição verdadeira tem uma prova, e uma prova é um *termo* do tipo
-- da proposição que testemunha a verdade da proposição. Provar `1 = 1` é
-- exibir um termo de tipo `1 = 1`, exatamente o que o termo `Eq.refl 1` faz
-- abaixo. Declarar um teorema é muito parecido com declarar uma função.

theorem OneEqSelf : 1 = 1 := Eq.refl 1

-- A mesma ideia vale para dizer que duas funções são a mesma coisa — não é
-- analogia, é a proposição `f = g`, provável do mesmo jeito. Agora usando o
-- modo `tactic` iniciado com `by`. Usamos as taticas `rfl` e `intro` que
-- iremos explicar a seguir. Com `example` não precisamos dar nomes a teoremas
-- que não serão reusados.

example :
  ∀ (z : Nat), (λ x ↦ x * x) z = (fun y => y * y) z := by
  intro n
  rfl

-- Note que perguntar pelo tipo não é o mesmo que decidir se ela é verdadeira:

#check (square₁ = square₂)

-- Provar é dar um termo cujo tipo é a proposição. Para uma igualdade em que
-- os dois lados reduzem ao mesmo valor, o termo é `rfl` — de *reflexividade*,
-- que é o princípio de que tudo é igual a si mesmo. Ver (Baanen et al., 2026)
-- para uma explicação sobre `rfl`.

theorem square₁_eq_square₂ : square₁ = square₂ := by
 rfl

-- Escrito com `by`, `rfl` é uma *tática*: uma instrução para construir a
-- prova. Você pode inspecionar a definição de Lean para `Eq.refl`.

#print square₁_eq_square₂

-- theorem IntroL.square₁_eq_square₂ : square₁ = square₂ :=
-- Eq.refl square₁

-- Além de `rfl`, um pequeno repertório de táticas resolve o que os capítulos
-- seguintes precisam — conferido nos próprios arquivos, não escolhido a
-- priori. A ordem abaixo é a de (Yingchareonthawornchai, 2025), que apresenta
-- as táticas nesta sequência; `decide`, `omega`, `obtain`, `cases`, `simp` e
-- `induction` não vêm de lá (o curso os introduz onde a necessidade aparece)
-- e ficam ao final, fora da ordem do FAA2025:

-- rfl          fecha a = b quando os dois lados calculam o mesmo valor
-- exact e      fornece o termo que é a prova
-- intro h      introduz uma hipótese, para provar uma implicação ou ∀
-- constructor  parte um ∧ ou um ↔ em dois objetivos
-- apply h      aplica uma implicação ou lema, deixando a(s) premissa(s)
--              como novo(s) objetivo(s)
-- unfold nome  desdobra uma definição, antes de continuar
-- rw [h]       reescreve o objetivo usando a igualdade h, da esquerda para
--              a direita
-- assumption   fecha o objetivo com uma hipótese já disponível
-- decide       fecha um objetivo decidível calculando a resposta
-- omega        resolve aritmética linear em Nat e Int
-- obtain ⟨_,_⟩ := h  desmonta uma hipótese composta (conjunção, existencial)
-- cases h      dado h : P ∨ Q, parte a prova em dois casos
-- simp [...]   reescreve com um conjunto de lemas até não haver mais o que
--              simplificar
-- induction x  prova por casos sobre a forma como x foi construído
-- funext x     duas funções são iguais quando concordam em todo ponto

-- Duas notações de prova não são táticas: `⟨t, h⟩` monta um par (para provar
-- uma conjunção ou exibir a testemunha de um existencial), e `h.1`/`h.2`
-- desmontam um par que está numa hipótese.

-- ### Exercise (1 star): rfl-arithmetic ⭐

-- Termine a prova usando `rfl`.

example : 7 * 6 = 42 :=
  sorry

-- ### Exercise (1 star): square-unfold ⭐

-- Prove que `square₁ n = n * n`; uma variável aparece, então `rfl` não basta
-- sozinho — é preciso desdobrar a definição antes.

example (n : Nat) : square₁ n = n * n := by
  sorry

-- ### Exercise (1 star): identity-implication ⭐

-- Provar `P → Q` é: suponha `P`, derive `Q`. Prove `P → P`. Fonte:
-- (Yingchareonthawornchai, 2025)

example (P : Prop) : P → P := by
  sorry

-- ### Exercise (1 star): p-implies-q-implies-p ⭐

-- Complete a prova abaixo. Fonte: (Yingchareonthawornchai, 2025)

example (P Q : Prop) : P → (Q → P) := by
  sorry

-- ### Exercise (1 star): and-intro ⭐

-- Prove `P ∧ Q` a partir de `P` e de `Q`. Fonte: (Yingchareonthawornchai,
-- 2025). Dica: `constructor` parte o objetivo `P ∧ Q` em dois; cada um se
-- fecha com `exact`.

#check And.intro

-- And.intro {a b : Prop} (left : a) (right : b) : a ∧ b

example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  sorry

-- ### Exercise (2 stars): and-comm ⭐⭐

-- Prove que a conjunção comuta. Fonte: (Yingchareonthawornchai, 2025). Dica:
-- um `↔` se parte em dois objetivos com `constructor`; em cada um, `intro h`
-- seguido de `obtain ⟨_,_⟩ := h` desmonta a conjunção da hipótese, e
-- `constructor` reconstrói a conjunção invertida.

-- Veja também o que acontece ao avaliar `(10,20).1`. `And` em Lean é uma
-- `structure` com dois campos.

example (P Q : Prop) : P ∧ Q ↔ Q ∧ P := by
 sorry

-- ### Exercise (1 star): implication-transitivity ⭐

-- Fonte: (Yingchareonthawornchai, 2025). Dica: `intro`, depois `apply` duas
-- vezes, encadeando as duas hipóteses.

example (P Q R : Prop) (h : P → Q) (h2 : Q → R) :
    P → R := by
  sorry

-- ### Exercise (1 star): apply-several-premises ⭐

-- Adaptado de (Yingchareonthawornchai, 2025).

example (P Q R S : Prop) (h0 : P ∧ Q ∧ R)
    (h : P → Q → R → S) : S := by
  sorry

-- Nem toda prova precisa de lógica proposicional abstrata — às vezes o que
-- falta é desdobrar uma definição local antes de concluir.

-- ### Exercise (1 star): unfold-direct-proof ⭐

-- Fonte: (Yingchareonthawornchai, 2025), com `f` definida localmente igual ao
-- arquivo. Dica: `intro h`, `unfold f at h` (ou `rw [f] at h`), depois
-- concluir por `omega` ou `assumption`.

def f₁ (x y : Nat) : Prop := x = y

example (x : Nat) : f₁ x 1 → x ≠ 2 := by
  sorry

-- ### Exercise (1 star): unfold-conjunction ⭐

-- Fonte: (Yingchareonthawornchai, 2025).

example (x y : Nat) : f₁ 0 x ∧ f₁ 0 y → x = y := by
  sorry

-- ### Exercise (1 star): exists-witness ⭐

-- Prove que `∃ n : Nat, n + n = 10`, exibindo a testemunha com `⟨_, _⟩` ou
-- usando `Exists.intro`.

#check Exists.intro

-- Exists.intro.{u} {α : Sort u} {p : α → Prop} (w : α) (h : p w) : Exists p

example : ∃ n : Nat, n + n = 10 := by
  sorry

-- ### Exercise (1 star): cases-on-or ⭐

-- Prove que `P ∨ Q → Q ∨ P`, usando `cases` sobre a hipótese, complete a
-- prova.

#check Or.intro_left

-- Or.intro_left {a : Prop} (b : Prop) (h : a) : a ∨ b

#check Or.intro_right

-- Or.intro_right {b : Prop} (a : Prop) (h : b) : a ∨ b

example (P Q : Prop) : P ∨ Q → Q ∨ P := by
  intro h
  cases h with
  | inl hp =>
    sorry
  | inr hq =>
    sorry

-- ## Tipos indutivos

-- Tipos indutivos vêm antes da recursão porque, em Lean, uma função recursiva
-- se escreve casando padrão sobre as formas de um tipo indutivo: sem o tipo
-- declarado, não há sobre o que recursar.

-- `inductive` declara um tipo listando as formas que seus valores podem ter.
-- Quando nenhuma forma carrega argumento, o tipo é uma enumeração; quando
-- carrega, é um registro variante; quando a forma se refere ao próprio tipo
-- sendo definido, é uma árvore. As três coisas são o mesmo mecanismo.

-- Essa é a construção mais importante do curso. Em Gramáticas para jogos
-- veremos que uma gramática escrita na notação usual — a Forma de Backus-Naur
-- — é literalmente um tipo `inductive`, e daí em diante todo fragmento da
-- língua é declarado assim.

-- A enumeração é o caso mais simples. `deriving Repr, DecidableEq` pede que a
-- exibição e o teste de igualdade sejam gerados em vez de escritos à mão.

-- Os dias da semana, nada mais são dias da semana.

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

-- `Bool` é a enumeração de duas formas; `Nat` é o caso em que uma das formas
-- se refere ao próprio tipo que está sendo definido. E `#print` mostra a
-- declaração.

#print Bool

-- inductive Bool : Type
-- number of parameters: 0
-- constructors:
-- Bool.false : Bool
-- Bool.true : Bool

#print Day

-- inductive IntroL.Day : Type
-- number of parameters: 0
-- constructors:
-- IntroL.Day.monday : Day
-- IntroL.Day.tuesday : Day
-- IntroL.Day.wednesday : Day
-- IntroL.Day.thursday : Day
-- IntroL.Day.friday : Day
-- IntroL.Day.saturday : Day
-- IntroL.Day.sunday : Day

#print Nat

-- inductive Nat : Type
-- number of parameters: 0
-- constructors:
-- Nat.zero : ℕ
-- Nat.succ : ℕ → ℕ

-- Ou seja: um natural é `Nat.zero`, ou é `Nat.succ n` para algum natural `n`,
-- e nada mais. O `2` que se escreve é notação para
-- `Nat.succ (Nat.succ
-- Nat.zero)`.

example : 2 = Nat.succ (Nat.succ Nat.zero) := rfl

-- ## Prova por indução

-- A última tática da tabela, `induction`, prova algo para todo valor de um
-- tipo indutivo, e não para um valor de cada vez.

-- ### Exercise (1 star): add-zero-induction ⭐

-- Prove que `n + 0 = n` para todo `n`, usando `induction n`. No caso `0`,
-- `rfl` fecha; no caso `n + 1`, a hipótese de indução (`ih`) resolve `omega`.

example (n : Nat) : n + 0 = n := by
 sorry

-- Quem quiser praticar Lean provas em Lean, pode jogar o [Natural Number
-- Game](https://adam.math.hhu.de/#/g/leanprover-community/nng4/).

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

#eval factorial 5

-- 120

#eval factorial 0

-- 1

-- A mesma função sem casar padrão, decidindo o caso base com um `if`.
-- Funciona, e serve de contraste: aqui o argumento da chamada recursiva é
-- `x
-- - 1`, e que ele seja menor que `x` é um fato a ser verificado, não algo
-- que a forma da definição já garanta. Neste caso Lean verifica sozinho; em
-- definições menos óbvias, não — e aí a prova de terminação passa a ser
-- trabalho do programador.

def factorial' (x : Nat) : Nat :=
  if x = 0 then 1
  else x * factorial' (x - 1)

-- O casamento de padrão de `factorial` é um *açucar sintático*, na verdade a
-- expressão `match` está oculta na definição. A seguir, usamos de forma
-- explicita.

-- Como exemplo, vamos implementar em Lean um gerador recursivo de sentença.

def gen (x : Nat) : String :=
  match x with
  | 0     => "Sentences can go on"
  | n + 1 => gen n ++ " and on"

def genS (n : Nat) : String := gen n ++ "."

#eval genS 3

-- "Sentences can go on and on and on and on."

-- A função de story a seguir fornece outro exemplo de recursão.

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
-- interpretada antes de passada para a função `IO.println` que efetivamente
-- imprime uma linha na saída.

#eval IO.println <| story 2

-- The night was pitch dark, mysterious and deep.
-- Ten cannibals were seated around a boiling cauldron.
-- Their leader got up and addressed them like this:
-- 'The night was pitch dark, mysterious and deep.
-- Ten cannibals were seated around a boiling cauldron.
-- Their leader got up and addressed them like this:
-- 'Let's cook and eat that final missionary, and off to bed.''

-- ### Exercise (1 star): sum-to ⭐

-- Implemente `sumTo n` para devolver `0 + 1 + ... + n` e termine a prova de
-- que a função está correta para a entrada `4`.

def sumTo : Nat → Nat :=
  sorry

theorem sumTo_test : sumTo 4 = 10 := sorry

-- ## Listas e polimorfismo

-- `List α` é o tipo das listas de elementos do tipo `α`, e é um tipo indutivo
-- como os da seção anterior: uma lista é vazia, `[]` (`List.nil`), ou é um
-- elemento seguido de uma lista, `x :: xs` (`List.cons`). Nada mais é uma
-- lista.

#print List

-- inductive List.{u} : Type u → Type u
-- number of parameters: 1
-- constructors:
-- List.nil : {α : Type u} → List α
-- List.cons : {α : Type u} → α → List α → List α

-- É por isso que a recursão sobre lista tem exatamente a forma da recursão
-- sobre `Nat` — dois casos, e o segundo dá acesso a algo estritamente menor,
-- aqui a cauda.

-- O `α` em `List α` é um parâmetro: `List Nat` e `List String` são tipos
-- diferentes, produzidos pelo mesmo `List`. Uma função que não olha para
-- dentro dos elementos não tem por que se comprometer com um deles.

-- Como já falamos, `{α : Type}` declara o parâmetro entre chaves, o que o
-- torna *implícito*. Lean o descobre a partir do argumento, e quem chama não
-- escreve.

def size {α : Type} : List α → Nat
  | []      => 0
  | _ :: xs => 1 + size xs

#eval size [10, 20, 30]

-- 3

#eval size ["Chomsky", "Montague"]

-- 2

-- ### Exercise (1 star): sum-list ⭐

-- `sumList` soma os elementos de uma lista. Complete e termine a prova.

def sumList : List Nat → Nat :=
  sorry

theorem sumList_test : sumList [1, 2, 3, 4] = 10 :=
  sorry

-- ### Exercise (1 star): count-zeros ⭐

-- `countZeros` conta quantos zeros a lista tem. Idem.

def countZeros : List Nat → Nat :=
  sorry

theorem countZeros_test : countZeros [0, 1, 0, 2, 0] = 3 :=
  sorry

-- ## O tipo Option

-- Uma função de tipo `List α → α` promete devolver um elemento para qualquer
-- lista que receba. Para a lista vazia não existe elemento nenhum, e a
-- promessa é impossível. Não por falta de cuidado do programador, mas porque
-- o tipo afirma algo falso.

-- A correção é no tipo, não no corpo: `List α → Option α` promete devolver
-- *ou* um elemento (`some x`) *ou* nada (`none`). Quem chama fica obrigado a
-- tratar os dois casos. O ganho é que o caso sem resposta deixa de ser
-- invisível: ele está na assinatura, e não há como esquecê-lo.

#print Option

-- inductive Option.{u} : Type u → Type u
-- number of parameters: 1
-- constructors:
-- Option.none : {α : Type u} → Option α
-- Option.some : {α : Type u} → α → Option α

def myLast {α : Type} : List α → Option α
  | []      => none
  | [x]     => some x
  | _ :: xs => myLast xs

#eval myLast [1,2,3]

-- some 3

#eval myLast ([] : List Nat)

-- none

def average (xs : List Int) : Option Rat :=
  if xs.isEmpty then none
  else some ((xs.sum : Rat) / (xs.length : Rat))

#eval average [1,2,3,4]

-- some (5 / 2)

#eval average []

-- none

-- Algumas funções devolvem um valor default no caso ruim, em vez de `Option`.
-- `String.back` é uma delas, e vale conhecer as que são assim.

#eval "rad".back

-- 'd'

#eval "".back

-- 'A'

-- ## Processamento de listas e composição de funções

-- Algumas perações cobrem quase todo uso de lista no curso. Todas se
-- escreveriam por recursão, como `size` acima, mas estas função de ordem
-- superior simplificam nosso trabalho.

-- `map` aplica uma função a cada elemento; `filter` filtra a lista com os que
-- satisfazem uma condição. A `foldl` (e também temos a `foldr`) reduzem a
-- lista a um valor final a partir do processamento sucesso de uma função.

def entities : List String :=
  ["Dorothy", "Toto", "Aunt Em", "Scarecrow"]

#eval entities.map String.length

-- [7, 4, 7, 9]

#eval entities.filter (fun x => x.length > 4)

-- ["Dorothy", "Aunt Em", "Scarecrow"]

#eval entities.foldl (fun s a => a.length + s) 0

-- 27

-- `all` e `any` perguntam se *todos* os elementos satisfazem uma condição, ou
-- se *algum* satisfaz, ambas devolvem `Bool`.

#eval entities.all (fun e => e.length > 2)

-- true

#eval entities.any (fun e => e.startsWith "T")

-- true

-- E a composição: `f ∘ g` é a função que aplica `g` e depois `f`, de modo que
-- `(f ∘ g) x` é `f (g x)`. Ela produz função nova sem nomear argumento nenhum
-- — `double ∘ double` é quadruplicar.

#eval (square₁ ∘ square₂) 5

-- 625

#eval entities.map (size ∘ String.toList)

-- [7, 4, 7, 9]

-- ## As duas leituras de uma função

-- Uma função admite duas leituras, e as duas importam:

-- - **extensional** — a função como tabela: o conjunto de pares entrada/saída.
--   Uma conversão de Celsius para Fahrenheit é a tabela
--   `{(0, 32), (100, 212), …}`, ponto.

-- - **intensional** — a função como instrução de cálculo. A mesma conversão é
--   `x ↦ x * 9 / 5 + 32`, uma receita que produz a tabela sem precisar
--   listá-la.

-- Em Lean, `def` escreve sempre a versão intensional — a instrução —, mas
-- duas instruções diferentes podem ser a mesma função, no sentido
-- extensional, se produzem a mesma tabela. É isso que `funext` verifica: duas
-- funções são iguais quando concordam em todo ponto do domínio.

def celsiusToFahrenheit (c : Int) : Int := c * 9 / 5 + 32

#eval celsiusToFahrenheit 0

-- 32

#eval celsiusToFahrenheit 100

-- 212

-- ### Composição

-- Componhamos duas conversões: de Kelvin para Celsius, depois de Celsius para
-- Fahrenheit. `∘` é `Function.comp`, e `(f ∘ g) x = f (g x)` — primeiro `g`,
-- depois `f`, na ordem em que a leitura da notação sugere o contrário.

def kelvinToCelsius (k : Int) : Int := k - 273

def kelvinToFahrenheit : Int → Int :=
  celsiusToFahrenheit ∘ kelvinToCelsius

#eval kelvinToFahrenheit 373

-- 212

-- ## Classes de tipos

-- Nós já vimos isso lá no começo, mas `count` conta ocorrências em qualquer
-- lista cujos elementos se possam comparar. Essa exigência entra na
-- assinatura entre colchetes, `[BEq α]`: uma instância de igualdade para `α`,
-- que Lean encontra sozinho no ponto de uso.

-- Duas noções de igualdade convivem, e vale separá-las desde já:

-- - `BEq α` devolve `Bool` e se escreve `==`.

-- - `DecidableEq α` devolve uma *prova* de igualdade ou de desigualdade.
--   Permite usar `=` num `if` e usar o resultado numa demonstração.

-- Tente remover `[BEq α]` na definição abaixo.

def count {α : Type} [BEq α] (x : α) : List α → Nat
  | []      => 0
  | y :: ys => if x == y then count x ys + 1 else count x ys

#eval count 2 [1, 2, 2, 3]

-- 2

#eval count "thou" ["thou","art","thou"]

-- 2

-- Até aqui só **usamos** classes: `[BEq α]` pede uma instância que o Lean
-- encontra sozinho. Falta o outro lado — declarar uma.

-- Na verdade já declaramos várias, sem escrever nenhuma. Toda vez que um tipo
-- termina com `deriving Repr`, o Lean escreve por nós a instância de `Repr`
-- que o `#eval` usa para exibir valores daquele tipo. É o que `Day` faz:

#eval Day.saturday

-- IntroL.Day.saturday

-- O que sai é o nome do construtor, porque é isso que uma instância derivada
-- sabe fazer. Para escolher a forma de exibição, a instância tem de ser
-- escrita à mão, com a palavra-chave `instance`. A classe para isso é
-- `ToString`, que dá sentido a `toString`:

instance : ToString Day where
  toString
    | .monday    => "segunda"
    | .tuesday   => "terça"
    | .wednesday => "quarta"
    | .thursday  => "quinta"
    | .friday    => "sexta"
    | .saturday  => "sábado"
    | .sunday    => "domingo"

#eval toString Day.saturday

-- "sábado"

-- A instância não tem nome: quem a procura é o Lean, pelo tipo, e não nós
-- pelo nome. Declarar uma instância é dizer "este tipo pertence a esta
-- classe, e eis como" — implementar os campos que a classe exige, aqui só o
-- `toString`.

-- `Repr` e `ToString` convivem porque servem a coisas diferentes: `Repr`
-- exibe para quem está programando e tende a mostrar a estrutura; `ToString`
-- produz o texto que se quer mostrar a quem lê. Nos capítulos seguintes,
-- quase toda instância escrita à mão será de `ToString` — para que uma árvore
-- sintática se imprima como a sentença que ela representa.

-- ## Cadeias e textos

-- `String` é uma sequência UTF-8 empacotada, não uma lista de caracteres.
-- Isso a torna eficiente para guardar texto e inadequada para percorrer a
-- cadeia. Não há padrão `c :: cs` para casar diretamente numa `String`.

-- Mas podemos converter uma `String` em uma lista de caracteres e uma lista
-- de caracteres em uma `String`.

def hword : List Char → Bool
  | []      => false
  | c :: cs => c == 'h' || hword cs

#eval hword "shrimptoast".toList

-- true

#eval hword "antiquing".toList

-- false

def reversal : List Char → List Char
  | []     => []
  | c :: t => reversal t ++ [c]

#eval String.ofList (reversal "Chomsky".toList)

-- "yksmohC"

-- Remove o último caractere.

def initS (s : String) : String :=
  String.ofList s.toList.dropLast

#eval initS "flicka"

-- "flick"

-- ## Cálculo lambda

-- A notação `fun x => e` não é invenção de linguagem de programação. Ela
-- resolve uma ambiguidade real, e vale ver qual.

-- A expressão `x² + y` não determina uma função. Ela pode ser lida como
-- função de `x`, com `y` fixo; como função de `y`, com `x` fixo; ou como
-- função dos dois. O que falta é dizer qual variável é o parâmetro — e o
-- operador lambda é exatamente o marcador que diz isso. Em `λx ↦ x² + y`, o
-- `x` está **ligado** e o `y` está **livre**.

-- O nome da variável ligada não importa: `λz ↦ z² + y` é a mesma função. E
-- isso não é convenção — em Lean as duas são o mesmo termo, e o `rfl` prova:

example :
    (fun (x : Nat) => x * x) =
      (fun (z : Nat) => z * z) := rfl

-- ### A gramática dos termos

-- O cálculo lambda tem três formas de construir expressão, e nada mais.
-- Escritas na notação usual para gramáticas — a Forma de Backus-Naur, ou BNF:

-- E ::= _v | "(" E E ")" | "(" "λ" _v "↦" E ")" ;

-- Leia: uma expressão é uma variável, ou a justaposição de duas expressões
-- (aplicação), ou um lambda seguido de variável e expressão (abstração). A
-- última cláusula é implícita e importante: **nada além disso é expressão**.

-- Aqui está o ponto. Uma gramática BNF é uma definição indutiva, e uma
-- definição indutiva é um tipo `inductive` — o mesmo mecanismo com que
-- Morfologia declara as classes de declinação do sueco e os traços
-- fonológicos. As duas coisas são a mesma, escritas em notações diferentes:

-- A gramática acima, como tipo. Cada cláusula da BNF virou um construtor.

inductive Lam where
  | var (name : String)
  | app (fn arg : Lam)
  | lam (binder : String) (body : Lam)

-- Essa correspondência é o motor do curso. Daqui em diante, cada fragmento da
-- língua vai ser dado por uma gramática, e a gramática vai ser um tipo
-- `inductive` — o que torna "esta expressão é bem formada" a mesma coisa que
-- "este termo tem esse tipo".

-- Aqui, `Lam` fica como ilustração e não será usado: o cálculo lambda que
-- interessa é o próprio Lean, não uma cópia dele dentro de Lean.

-- ### Redução

-- O que se faz com uma aplicação é substituir. A regra é uma só:

-- (λx ↦ E) A  →  E\[x := A\]

-- onde `E\[x := A\]` é `E` com toda ocorrência livre de `x` trocada por `A`.
-- Isso é a β-redução, e é o único mecanismo de cálculo do cálculo lambda
-- inteiro.

-- Em Lean essa redução é o que o `#eval` executa e o que o `rfl` verifica:

example : (fun (x : Nat) => x + 42) 5 = 5 + 42 := rfl

-- ### Captura de variável

-- Substituir ingenuamente dá errado, e o exemplo clássico merece atenção
-- porque o erro é silencioso. Considere aplicar `λyλx ↦ x + y` ao argumento
-- `x`.

-- Trocando `y` por `x` sem cuidado, obtém-se `λx ↦ x + x` — a função que soma
-- um número a si mesmo. Mas o resultado correto é a função que soma `x` a um
-- número dado: o `x` que veio de fora foi **capturado** pelo `λx` que já
-- estava lá. Que o resultado é outro se vê renomeando antes: `λyλz
-- ↦ z + y`
-- aplicado a `x` dá `λz ↦ z + x`, que é o certo.

-- A saída é renomear a variável ligada quando houver risco de captura. Lean
-- faz isso sozinho — internamente as variáveis ligadas não têm nome, e o
-- problema não existe:

example (x : Nat) :
    (fun y => fun z => z + y) x = (fun z => z + x) := rfl

-- ### Funções são dados

-- Abstração e aplicação, como definidas, não distinguem dados de funções. Se
-- tudo é expressão, então uma função pode receber função, devolver função, e
-- ser aplicada a si mesma. Não há duas categorias de coisas.

-- É isso que permite escrever uma função que aplica outra a um argumento
-- fixo:

def applyToDragon (f : String → String) : String :=
  f "dragon"

def pluralize (w : String) : String := w ++ "s"

#eval applyToDragon pluralize

-- "dragons"

-- ### Exercise (1 star): twice ⭐

-- Outro exemplo de função de ordem superior é `λf λx ↦ f (f x)`, que aplica
-- uma função duas vezes a uma entrada dada. Ponha-a para trabalhar reduzindo:
-- `(λf λx ↦ f (f x)) (λy ↦ 1 + y)`.

def twice {α : Type} (f : α → α) : α → α :=
  sorry

theorem twice_test1 :
    twice (fun y => 1 + y) = fun x => 2 + x := sorry

theorem twice_test2 : twice (fun y => 1 + y) 0 = 2 :=
  sorry

-- Um aspecto do cálculo lambda é que reduções podem não terminar. Observe o
-- comportamento de redução de `(λx ↦ x x) (λx ↦ x x)`, e depois de
-- `(λx
-- ↦ x x x) (λx ↦ x x x)`.

-- Este exercício não se enuncia em Lean, e a razão é o assunto da questão:

-- **1. Um passo de redução.** Substituindo `x` por `(λx ↦ x x)` no corpo
-- `x x`, obtém-se `(λx ↦ x x) (λx ↦ x x)` — o mesmo termo de partida. A
-- redução é portanto um laço: qualquer número de passos devolve o termo
-- original, e a normalização nunca termina. Este termo é o combinador
-- tradicionalmente chamado `Ω`. Já `(λx ↦ x x x) (λx ↦ x x x)` reduz a
-- `(λx ↦ x x x) (λx ↦ x x x) (λx ↦ x x x)`: além de não terminar, cada passo
-- produz um termo *maior* que o anterior, então nem mesmo o tamanho fica
-- estável.

-- **2. A mensagem do Lean.** Descomentando
-- `def omega := (fun x => x x)
-- (fun x => x x)` abaixo, o Lean acusa dois
-- erros: a auto-aplicação `x x` exige que `x` seja função de algum tipo
-- `?m → ?n`, mas o argumento é o próprio `x`, que teria então de ter
-- simultaneamente o tipo `?m`. O elaborador precisa resolver `?m = ?m → ?n`,
-- e não existe tipo que satisfaça isso (falha o *occurs check*: `?m`
-- ocorreria dentro de si mesmo). Como não há atribuição de tipos possível, o
-- termo não pode nem ser *escrito* em Lean.

-- **3. Relação entre não terminar e não ter tipo.** O cálculo lambda *tipado*
-- (simplesmente tipado, e também o de Lean) é fortemente normalizante: todo
-- termo bem tipado tem forma normal, e a redução sempre termina. A
-- contrapositiva é o que se observa aqui: um termo cuja redução não termina
-- não pode ser bem tipado. Os dois fenômenos têm a mesma raiz — a
-- auto-aplicação `x x` — e o sistema de tipos funciona como um filtro que
-- rejeita exatamente esses termos. É por isso que Lean pode ser ao mesmo
-- tempo uma linguagem de programação e uma lógica consistente: a terminação é
-- garantida pelos tipos, não pela boa vontade do programador. (O preço é que
-- Lean também rejeita programas que terminam, mas cuja terminação ele não
-- sabe verificar; daí a necessidade de provar terminação em definições
-- recursivas.)

-- -- def omega := (fun x => x x) (fun x => x x)

-- ## Tipos na gramática e na computação

-- No cálculo lambda como está, toda expressão se aplica a toda expressão.
-- Nada impede escrever o número `4` aplicado a uma função, e o resultado não
-- é falso — é sem sentido. Tipos existem para excluir isso.

-- A gramática dos tipos também é uma BNF, com duas cláusulas:

-- τ ::= _b | "(" τ "→" τ ")" ;

-- Há tipos básicos, e há tipos de função construídos a partir deles. Na
-- semântica, os dois básicos costumam ser `e`, das entidades, e `t`, dos
-- valores de verdade — a notação de Montague, que o capítulo sobre o
-- fragmento de inglês retoma. Em Lean, `t` é `Prop`.

-- E a atribuição de tipos a expressões se dá por três regras:

-- - **variáveis** — para cada tipo há variáveis daquele tipo;
-- - **abstração** — se `x : δ` e `E : τ`, então `(λx ↦ E) : δ → τ`;
-- - **aplicação** — se `E₁ : δ → τ` e `E₂ : δ`, então `(E₁ E₂) : τ`.

-- Não há mais nada. O `#check` do Lean é essas três regras rodando:

-- `restful` é uma propriedade de dias: aplicada a um, dá uma afirmação.
-- `opaque` declara o nome com o tipo e sem corpo — aqui o assunto são os
-- tipos, e qualquer definição serviria.

opaque restful : Day → Prop

section
variable (d : Day)

-- regra da aplicação: `restful : Day → Prop` e `d : Day`, logo
-- `restful
-- d : Prop`

#check restful d

-- restful d : Prop

-- regra da abstração: `y : Day` e `restful y : Prop`, logo o lambda é
-- `Day → Prop`

#check fun (y : Day) => restful y

-- fun y => restful y : Day → Prop

end

-- ### Lean como cálculo lambda

-- O que se descreveu acima é o cálculo lambda com tipos simples, e Lean o
-- contém. Abstração, aplicação, β-redução, tipos de função: tudo o que foi
-- dito vale literalmente, e os `#check` acima são as regras de tipagem sendo
-- aplicadas.

-- Lean vai além disso em pontos que o curso vai usar:

-- - **tipos indutivos** — os deste capítulo, que aqui se revelam ser
--   gramáticas: uma BNF é um tipo, com casamento de padrão e recursão
--   garantidamente terminante;

-- - **tipos dependentes** — um tipo pode depender de um valor, o que permite
--   exigir na assinatura condições que aqui teriam de ser verificadas à parte;

-- - **proposições como tipos** — `Prop` não é um tipo básico opaco: uma prova
--   de `P` é um termo de tipo `P`, e é por isso que o mesmo verificador serve
--   para checar programas e demonstrações;

-- - **universos** — `Type`, `Type 1`, e assim por diante, o que evita os
--   paradoxos que apareceriam se houvesse um tipo de todos os tipos.

-- Para o que vem pela frente, a leitura útil é essa: o aparato da semântica
-- de Montague é um fragmento do que Lean oferece, e o excedente é o que vai
-- permitir demonstrar coisas sobre os significados, e não apenas calculá-los.

-- E o termo `(λx ↦ x x) (λx ↦ x x)` do exercício anterior? Você consegue
-- achar um tipo para ele?

-- **Não.** Nenhuma atribuição de tipos funciona, e a maneira de mostrar isso
-- é tentar construí-la e ver onde ela quebra.

-- Suponha que `λx ↦ x x` tenha tipo. Chame de `σ` o tipo de `x`. No corpo
-- `x x`, o `x` da esquerda está em posição de função aplicada a um argumento,
-- logo `σ` tem de ser um tipo de função: `σ = σ₁ → τ` para algum `σ₁` e `τ`.
-- O `x` da direita é o argumento dessa aplicação, então seu tipo tem de ser o
-- domínio: `σ = σ₁`. Combinando as duas exigências, `σ = σ → τ`. Não há tipo
-- simples que satisfaça essa equação: qualquer solução teria de ser um tipo
-- estritamente maior que si mesmo (a árvore de `σ → τ` contém a de `σ` como
-- subárvore própria), e não existe tipo finito assim. É precisamente o
-- *occurs check* que o unificador do Lean reporta ao dizer que `x` tem tipo
-- `?m → ?n` mas se espera `?m`.

-- Portanto `λx ↦ x x` já é intipável, e a fortiori a aplicação dele a si
-- mesmo também. Vale notar que a impossibilidade não é um defeito do Lean:
-- ela é consequência de o sistema ser fortemente normalizante. Sistemas que
-- admitem tipos recursivos (`σ ≅ σ → τ`, via `μ`-tipos) conseguem tipar esse
-- termo, mas ao preço de perder a garantia de terminação — e, se usados como
-- lógica, a consistência.

-- ## Tipos como disciplina

-- O tipo de uma função diz o que ela aceita e o que devolve, e Lean recusa a
-- aplicação que não respeite isso — ao escrever, antes de rodar.

-- Essa recusa é o instrumento central do texto. As árvores sintáticas das
-- gramáticas que vêm a seguir serão tipos, e os significados também; daí em
-- diante, "esta combinação de palavras não é bem formada" e "este programa
-- não tipa" passam a ser a mesma frase.

end IntroL

