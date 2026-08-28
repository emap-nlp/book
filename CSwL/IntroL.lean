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

-- ### Exercise (1 star): sumOfSquares ⭐

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

-- ### Exercise (1 star): construindo-termos ⭐

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
-- 3 e 4 precisam — conferido nos próprios arquivos, não escolhido a priori. A
-- ordem abaixo é a de (Yingchareonthawornchai, 2025), que apresenta as
-- táticas nesta sequência; `decide`, `omega`, `obtain`, `cases`, `simp` e
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

-- Duas notações de prova não são táticas: `⟨t, h⟩` monta um par (para provar
-- uma conjunção ou exibir a testemunha de um existencial), e `h.1`/`h.2`
-- desmontam um par que está numa hipótese.

-- ### Exercício'

-- Termine a prova usando `rfl`.

example : 7 * 6 = 42 :=
  rfl

-- ### Exercício' — `double n = n + n`

-- Prove que `double n = n + n`; uma variável aparece, então `rfl` não basta.

example (n : Nat) : square₁ n = n * n := by
  unfold square₁
  rfl

-- ### Exercício' — `P → P`

-- Provar `P → Q` é: suponha `P`, derive `Q`. Provar `P ∧ Q` é provar as duas
-- coisas. Fonte: (Yingchareonthawornchai, 2025)

example (P : Prop) : P → P := by
  intro h
  exact h

-- ### Exercise (1 star): p-implica-q-implica-p ⭐

-- Complete a prova abaixo. Fonte: (Yingchareonthawornchai, 2025)

example (P Q : Prop) : P → (Q → P) := by
  sorry

-- ### Exercício' — Conjunção a partir das partes

-- Fonte: (Yingchareonthawornchai, 2025). Dica: `constructor` parte o objetivo
-- `P ∧ Q` em dois; cada um se fecha com `exact`.

#check And.intro

-- And.intro {a b : Prop} (left : a) (right : b) : a ∧ b

example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  apply And.intro
  · exact hP
  · exact hQ

-- ### Exercício' — Comutatividade da conjunção

-- Fonte: (Yingchareonthawornchai, 2025). Dica: um `↔` se parte em dois
-- objetivos com `constructor`; em cada um, `intro h` seguido de
-- `obtain ⟨_,_⟩ := h` desmonta a conjunção da hipótese, e `constructor`
-- reconstrói a conjunção invertida.

-- Veja também o que acontece ao avaliar `(10,20).1`. `And` em Lean é uma
-- `structure` com dois campos.

example (P Q : Prop) : P ∧ Q ↔ Q ∧ P := by
 constructor
 · intro h
   obtain ⟨h1, h2⟩ := h
   apply And.intro
   · exact h2
   · exact h1
 · intro h
   constructor
   · exact h.2
   · exact h.1

-- ### Exercise (1 star): transitividade-implicacao ⭐

-- Fonte: (Yingchareonthawornchai, 2025). Dica: `intro`, depois `apply` duas
-- vezes, encadeando as duas hipóteses.

example (P Q R : Prop) (h : P → Q) (h2 : Q → R) :
    P → R := by
  sorry

-- ### Exercise (1 star): apply-varias-premissas ⭐

-- Adaptado de (Yingchareonthawornchai, 2025).

example (P Q R S : Prop) (h0 : P ∧ Q ∧ R)
    (h : P → Q → R → S) : S := by
  sorry

-- Nem toda prova precisa de lógica proposicional abstrata — às vezes o que
-- falta é desdobrar uma definição local antes de concluir.

-- ### Exercise (1 star): prova-direta-unfold ⭐

-- Fonte: (Yingchareonthawornchai, 2025), com `f` definida localmente igual ao
-- arquivo. Dica: `intro h`, `unfold f at h` (ou `rw [f] at h`), depois
-- concluir por `omega` ou `assumption`.

def f₁ (x y : Nat) : Prop := x = y

example (x : Nat) : f₁ x 1 → x ≠ 2 := by
  sorry

-- ### Exercise (1 star): desmontando-conjuncao-unfold ⭐

-- Fonte: (Yingchareonthawornchai, 2025).

example (x y : Nat) : f₁ 0 x ∧ f₁ 0 y → x = y := by
  sorry

-- ### Exercício' — Existe um par par

-- Prove que `∃ n : Nat, n + n = 10`, exibindo a testemunha com `⟨_, _⟩` ou
-- usando `Exists.intro`.

#check Exists.intro

-- Exists.intro.{u} {α : Sort u} {p : α → Prop} (w : α) (h : p w) : Exists p

example : ∃ n : Nat, n + n = 10 := by
  apply Exists.intro 5
  rfl

-- ### Exercise (1 star): casos-sobre-ou ⭐

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

-- Ref. CSwFP/3 §3.13 (p. 55) — adiantado para antes da recursão, por
-- necessidade Lean-vs-Haskell: em Lean a recursão se apresenta por casamento
-- de padrão sobre um `inductive`, então o tipo indutivo tem de vir primeiro.

-- `inductive` declara um tipo listando as formas que seus valores podem ter.
-- Quando nenhuma forma carrega argumento, o tipo é uma enumeração; quando
-- carrega, é um registro variante; quando a forma se refere ao próprio tipo
-- sendo definido, é uma árvore. As três coisas são o mesmo mecanismo.

-- Essa é a construção mais importante do curso. O capítulo 3 mostra que uma
-- gramática escrita na notação usual — a Forma de Backus-Naur — é
-- literalmente um tipo `inductive`, e do capítulo 4 em diante todo fragmento
-- da língua é declarado assim.

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

-- ### Exercício' — Day

-- Complete `isWeekend`, que responde se o dia é sábado ou domingo.

def isWeekend (d : Day) : Bool :=
 match d with
 | .saturday => true
 | .sunday => true
 | _ => false

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

-- ### Exercício' — Indução sobre `Nat`

-- Prove que `n + 0 = n` para todo `n`, usando `induction n`. No caso `0`,
-- `rfl` fecha; no caso `n + 1`, a hipótese de indução (`ih`) resolve `omega`.

example (n : Nat) : n + 0 = n := by
 induction n with
 | zero => rfl
 | succ a ih =>
   -- try `apply?`
   omega

-- Quem quiser praticar Lean provas em Lean, pode jogar o [Natural Number
-- Game](https://adam.math.hhu.de/#/g/leanprover-community/nng4/).

-- ## Recursão

-- Ref. CSwFP/3 §3.5 (p. 40).

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

-- ### Exercise (1 star): sumTo ⭐

-- Implemente `sumTo n` para devolver `0 + 1 + ... + n` e termine a prova de
-- que a função está correta para a entrada `4`.

def sumTo : Nat → Nat :=
  sorry

theorem sumTo_test : sumTo 4 = 10 := sorry

-- ## Listas e polimorfismo

-- Ref. CSwFP/3 §3.6 (p. 41) + §3.4 (p. 39, polimorfismo genérico).

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

-- ### Exercise (1 star): sumList ⭐

-- `sumList` soma os elementos de uma lista. Complete e termine a prova.

def sumList : List Nat → Nat :=
  sorry

theorem sumList_test : sumList [1, 2, 3, 4] = 10 :=
  sorry

-- ### Exercise (1 star): countZeros ⭐

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

-- Ref. CSwFP/3 §3.7 e CSwFP/3 §3.8 (p. 42–43).

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

-- ## Classes de tipos

-- Ref. CSwFP/3 §3.9 (p. 45).

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

-- ## Cadeias e textos

-- Ref. CSwFP/3 §3.10 (p. 47–48).

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

end IntroL

