import Mathlib.Tactic
import CSwL.IntroL

-- # Provas em Lean

-- Neste capítulo vamos falar sobre o tipo `Prop` em Lean para representação
-- de proposições lógicas em tipos dependentes. A representação de proposições
-- e contrução de provas é o que torna Lean um assistente de prova, além de
-- linguagem de programação. Vamos apresentar provas como termos e a
-- construção de provas com táticas.

-- Supomos conhecida a lógica proposicional e a de predicados — sintaxe,
-- semântica, e a noção de consequência. Para uma apresentação a partir do
-- início, ver (Enderton, 2001).

namespace Proof

-- ## O tipo `Prop` e Provas

-- O que diferencia Lean de outras linguagens como Python e Java é a
-- capacidade de na mesma linguagem que usamos para 'programar' funções,
-- escrevermos 'provas' sobre estas funções.

-- Uma proposição é um enunciado que pode ser verdadeiro ou falso. O enunciado
-- `1 = 1` é verdadeiro, enquanto `square₁ 12 = 2` é falso. Toda proposição é
-- todo tipo `Prop` (Yingchareonthawornchai, 2025). Podemos declarar
-- proposições, mas não podemos *avaliar* uma proposição. Note que perguntar
-- pelo tipo não é o mesmo que decidir se ela é verdadeira.

def p₁ : Prop := 1 = 1
def p₂ : Prop := 1 = 2
#check p₁
#check p₂

open IntroL in
#check square₁ 12 = 2

-- Em Lean, proposições são tipos e provas são termos desses tipos. Ou seja,
-- provar algo é exatamente o mesmo ato de construir um valor em `Prop`. Por
-- isso a forma mais direta de provar é escrever o termo à mão, do mesmo jeito
-- que definimos qualquer função. Provar `1 = 1` é exibir um termo de tipo
-- `1 = 1`, exatamente o que o construtor `refl` do tipo `Eq` faz abaixo. Este
-- tipo representa a relação de igualdade. Podemos notar que declarar um
-- teorema é muito parecido com declarar uma função, como vimos em IntroL.

theorem OneEqSelf : 1 = 1 := Eq.refl 1

-- Acontece que, para propriedades um pouco menos triviais, o termo para
-- provar uma proposição pode ficar grande e pouco natural de escrever
-- manualmente. É aí que entra a palavra `by`. Ela introduz um *modo* chamado
-- 'tactic mode' onde usamos uma pequena linguagem de comandos (táticas) em
-- que descrevemos como a prova deve ser montada e deixamos o Lean construir o
-- termo por nós.

-- A tática `rfl` prova igualdades quando os dois lados são iguais por
-- definição, isto é, quando Lean consegue reduzi-los até a mesma expressão
-- por computação. Essa redução inclui, por exemplo, a expansão de definições,
-- a aplicação de funções e a avaliação de `let`. Isso é uma consequência
-- importante da fundação de Lean em Calculus of Inductive Constructions (CiC)
-- (Nederpelt and Geuvers, 2014): expressões de tipos e programas podem ser
-- computadas e comparadas por redução. Assim, `rfl` é frequentemente usado
-- para dizer que os dois lados são iguais porque são o mesmo valor depois de
-- reduzir o código. O comando `#print double_theorem` irá mostrar que a
-- tática `rfl` construiu o termo `Eq.refl`.

def double (n : Nat) := n + n

theorem double_theorem : double 5 = 5 + 5 := by rfl

-- A tática `rfl` tem limitações, embora possamos provar que duas funções são
-- identificas a menos da sua mudança nos nomes dos parâmetros, precisamos do
-- teorema sobre a comutatividade dos naturais para provar o segundo exemplo.

example (z : Nat) : (λ x ↦ 2 * x) z = (fun y => 2 * y) z := by
  rfl

example (z : Nat) : (λ x ↦ 2 * x) z = (fun y => y * 2) z := by
  exact Nat.mul_comm 2 z

-- Além de `rfl`, um pequeno repertório de táticas resolve o que os capítulos
-- seguintes precisam.

-- ### Exercise (1 star): rfl-arithmetic ⭐

-- Complete a prova abaixo usando a tática `rfl`. Esta é a primeira prova que
-- do [Natural Number
-- Game](https://adam.math.hhu.de/#/g/leanprover-community/nng4/). O leitor
-- está convidado a jogar NNG para uma boa introdução a provas no Lean.

example (x q : Nat) : 37 * x + q = 37 * x + q :=
 sorry

-- ## Lógica Proposicional em Lean

-- Os conectivos lógicos `∧`, `∨`, `→`, `↔` e `¬` estão disponíveis
-- diretamente no Lean, de modo que uma fórmula proposicional pode ser
-- representada como uma proposição em Lean. Isso nos fornece uma ponte
-- conveniente entre a semântica da linguagem natural e o raciocínio formal.
-- Podemos traduzir o conteúdo semântico de uma sentença para uma proposição
-- em Lean e, em seguida, usar Lean para verificar se uma conclusão decorre de
-- um conjunto de hipóteses.

-- Vamos considerar um primeiro exemplo. Três irmãs — Ana, Maria e Cláudia —
-- foram a uma festa com vestidos de cores diferentes. Uma vestiu azul, a
-- outra branco, e a terceira, preto. Chegando à festa, o anfitrião perguntou
-- quem era cada uma delas.

-- - A de azul respondeu: "Ana é a que está de branco";
-- - A de branco disse: "Eu sou Maria";
-- - A de preto respondeu: "Cláudia é quem está de branco".

-- O anfitrião foi capaz de identificar cada irmã considerando que:

-- - Ana sempre diz a verdade;
-- - Maria às vezes diz a verdade;
-- - Cláudia nunca diz a verdade.

-- Para começar, vamos introduzir variáveis do tipo `Prop`, cada uma delas
-- representado uma proposição. São 3 pessoas e 3 cores. Vamos representar
-- "Ana veste azul" por `Aa` e assim por diante.

section PL

variable (
   Aa Ab Ap
   Ma Mb Mp
   Ca Cb Cp  : Prop)

-- A ideia é que as condições do problema sejam traduzidas em fórmulas
-- proposicionais. Por exemplo, podemos formalizar a sentença "Ana veste azul,
-- branco ou preto" com a fórmula em LP.

#check Aa ∨ Ab ∨ Ap

-- Aqui cabe a observação de que a formalização em LP não foi obtida
-- diretamente a partir da construção linguística original, uma oração
-- coordenando seus constituintes no predicado. Intuitivamente, a sentença foi
-- antes interpretada como três orações coordenadas (proposições completas),
-- "Ana veste azul ou Ana veste branco ou Ana veste preto".

-- A formalização completa do problema deve levar em consideração não apenas o
-- que foi dito explicitamente mas algumas condições implicitamente assumidas.
-- Definimos a estrutura `Premissas` por conveniência, ao invés de uma
-- variável por premissa.

structure Premissas : Prop where
   -- cada pessoa veste algum vestido
   hA : Aa ∨ Ab ∨ Ap
   hM : Ma ∨ Mb ∨ Mp
   hC : Ca ∨ Cb ∨ Cp

   -- cada vestido é de alguma pessoa
   ha : Ma ∨ Aa ∨ Ca
   hb : Ab ∨ Mb ∨ Cb
   hp : Ap ∨ Mp ∨ Cp

   -- uma pessoa veste apenas um vestido
   hA1 : (Aa → ¬ Ab ∧ ¬ Ap) ∧ (Ab → ¬ Aa ∧ ¬ Ap) ∧ (Ap → ¬ Aa ∧ ¬ Ab)
   hM1 : (Ma → ¬ Mb ∧ ¬ Mp) ∧ (Mb → ¬ Ma ∧ ¬ Mp) ∧ (Mp → ¬ Ma ∧ ¬ Mb)
   hC1 : (Ca → ¬ Cb ∧ ¬ Cp) ∧ (Cb → ¬ Ca ∧ ¬ Cp) ∧ (Cp → ¬ Ca ∧ ¬ Cb)

   -- cada vestido é de apenas uma pessoa
   ha1 : (Ma → ¬ Aa ∧ ¬ Ca) ∧ (Ca → ¬ Aa ∧ ¬ Ma) ∧ (Aa → ¬ Ma ∧ ¬ Ca)
   hb1 : (Mb → ¬ Ab ∧ ¬ Cb) ∧ (Cb → ¬ Ab ∧ ¬ Mb) ∧ (Ab → ¬ Mb ∧ ¬ Cb)
   hp1 : (Mp → ¬ Ap ∧ ¬ Cp) ∧ (Cp → ¬ Ap ∧ ¬ Mp) ∧ (Ap → ¬ Mp ∧ ¬ Cp)

   -- da resposta 1
   h1 : Aa → Ab
   h2 : Ca → ¬ Ab

   -- da resposta 2
   h3 : ¬ Ab

   -- da resposta 3
   h4 : Ap → Cb
   h5 : Cp → ¬ Cb

-- Podemos então enunciar o problema na forma do teorema abaixo.

theorem vestidos (h : Premissas Aa Ab Ap Ma Mb Mp Ca Cb Cp)
  : Ap ∧ Cb ∧ Ma := sorry

-- Consultar o tipo deste teorema com `#check vestidos` nos revela que ele tem
-- o formato de uma implicação, que pode ser lido como `Γ ⊢ α` Do conjunto `Γ`
-- de premissas em `Premissas` posso **derivar** `Ap ∧ Cb ∧ Ma`. Em Lean
-- podemos construir a prova de `α` a partir da aplicação de regras de dedução
-- a partir das fórmulas de `Γ`.

-- Chamamos "sistema dedutivo" um conjunto das regras de dedução. Existem
-- vários sistemas dedutivos. A formalização de Prop em Lean corresponde a
-- implementação do sistema chamado **dedução natural** definido por Gerhard
-- Gentzen em 1930s.

-- Neste sistema dedutivo, cada conectivo vem com dois tipos de regra: as de
-- **introdução**, que dizem como construir uma prova cuja conclusão usa o
-- conectivo, e as de **eliminação**, que dizem como usar uma prova cuja
-- hipótese o usa.

variable {P Q R : Prop}

-- A regra de introdução de `→` diz que para provar `P → Q`, supomos `P` e
-- derivamos `Q`. A tatica `intro` move o antecedente para as hipóteses. A
-- regra de eliminação é a chamada regra **modus ponens**. De `P → Q` e de
-- `P`, conclua `Q`. Em Lean isso é aplicação `h hP` já é a prova de `Q`. A
-- tática `apply` faz o mesmo de trás para frente, ela transforma o objetivo
-- `Q` no objetivo `P`. A `exact` fecha a prova indicando a hipótese cujo tipo
-- corresponde ao *goal* aberto. A `assumption` fecha o *goal* quando o tipo
-- de alguma das hipóteses corresponde ao tipo do *goal*, sem precisarmos
-- passar a hipótese nominalmente, como quando usamos `exact`.

example : P → (Q → P) := by
  intro hP hQ
  exact hP

example (h₁ : P → Q) (h₂ : Q → R) : P → R := by
  intro hP
  apply h₂
  apply h₁
  assumption

example (h : P → Q) (hP : P) : Q := h hP

-- Para a conjunção. Provar `P ∧ Q` depende de uma prova de `P` e `Q`. A
-- tática `constructor` parte o objetivo em dois; o construtor anônimo
-- `⟨_, _⟩` faz o mesmo em forma de termo. A eliminação de `∧` em `P ∧ Q`
-- significa que podemos concluir `P` ou `Q`. São duas regras, e em Lean são
-- as projeções `.1` (ou `.left`) e `.2` (ou `.right`). A tática `obtain`
-- desmonta a hipótese de uma vez, dando nome às duas partes.

example (hP : P) (hQ : Q) : P ∧ Q := by
  constructor
  · exact hP
  · exact hQ

example (hP : P) (hQ : Q) : P ∧ Q := ⟨hP, hQ⟩
example (hP : P) (hQ : Q) : P ∧ Q := And.intro hP hQ

example (h : P ∧ Q) : Q ∧ P := by
  obtain ⟨hP, hQ⟩ := h
  exact ⟨hQ, hP⟩

example (h : P ∧ Q) : Q ∧ P := ⟨h.2, h.1⟩

-- Para provar `P ∨ Q` basta provar um dos dois lados. São duas regras, e as
-- táticas `left` e `right` escolhem qual. A eliminação de `∨` é a prova por
-- casos. De `P ∨ Q` não se sabe qual dos dois vale. Para concluir `R` a
-- partir dela é preciso concluir `R` nos dois casos. A tática `cases` abre
-- exatamente esses dois objetivos.

example (hP : P) : P ∨ Q := by
  left
  exact hP

example (h : P ∨ Q) : Q ∨ P := by
  cases h with
  | inl hP => right; exact hP
  | inr hQ => left; exact hQ

-- Não há um conectivo primitivo para a negação: `¬ P` é notação para
-- `P → False` onde `False` é a proposição sem nenhuma prova. A introdução de
-- `¬` é a introdução de `→`, para provar `¬P`, suponha `P` e derive `False`.
-- A eliminação é a eliminação de `→`. A regra que a tradição chama de **ex
-- falso quodlibet** (princípio da explosão), é uma regra que dita que, a
-- partir de uma contradição ou de uma premissa falsa, qualquer conclusão pode
-- ser deduzida. `False.elim` em Lean. As duas juntas são `absurd`.

example (h : P → Q) : ¬Q → ¬P := by
  intro hnQ hP
  exact hnQ (h hP)

example (hP : P) (hn : ¬P) : False := hn hP
example (h : False) : P := False.elim h
example (hP : P) (hn : ¬P) : Q := absurd hP hn

-- A `P ↔ Q` é a conjunção das duas implicações, e as regras seguem disso. A
-- tática `constructor` parte o objetivo nas duas direções, e `.mp` e `.mpr`
-- são as eliminações de `P → Q` e de `Q → P`.

example : P ∧ Q ↔ Q ∧ P := by
  constructor
  · intro h; exact ⟨h.2, h.1⟩
  · intro h; exact ⟨h.2, h.1⟩

example (h : P ↔ Q) (hP : P) : Q := h.mp hP

-- Até aqui não usamos em nenhum momento "ou `P` vale ou não vale". Todas as
-- regras até aqui são **construtivas**, uma prova de `P ∨ Q` traz consigo
-- qual dos dois lados foi usado. Uma prova de `P` é uma construção de `P`. O
-- raciocínio **clássico** acrescenta o princípio chamado de terceiro
-- excluído. Dele saem as duas táticas. A primeira é `by_cases`, que parte a
-- prova em dois casos, supondo `P` num e `¬P` no outro. E a tatica
-- `by_contra` prova `P` supondo `¬P` e derivando `False`, a redução ao
-- absurdo.

example : P ∨ ¬P := Classical.em P

example : ¬¬P → P := by
  intro h
  by_cases hP : P
  · exact hP
  · exact absurd hP h

example (h : ¬¬P) : P := by
  by_contra hn
  exact h hn

-- ### Exercise (2 stars): de-morgan ⭐⭐

-- Uma das leis de De Morgan vale construtivamente; a outra precisa do
-- terceiro excluído.

example : ¬(P ∨ Q) ↔ (¬P ∧ ¬Q) := sorry

example : ¬(P ∧ Q) ↔ (¬P ∨ ¬Q) := sorry

-- ### Exercise (1 star): contrapositive ⭐

-- Prove a contrapositiva. Só uma das direções precisa de raciocínio clássico.

example : (P → Q) ↔ (¬Q → ¬P) := sorry

-- ### Exercise (1 star): exchange-prop ⭐

-- Complete a representação do argumento abaixo em linguagem lógica.

-- Se o câmbio cair, temos inflação. Se as exportações crescerem, diminuímos o
-- déficit. O câmbio cai ou diminuímos o déficit. Logo, temos inflação ou as
-- exportações crescem.

section

variable (
  p -- o câmbio cai
  q -- temos inflação
  r -- as exportações crescem
  s -- Diminuimos o déficit
  : Prop)

def exchange : Prop :=
  sorry
end

-- ### Exercise (2 stars): and-comm ⭐⭐

-- Prove que a conjunção é comutativa.

example (P Q : Prop) : P ∧ Q ↔ Q ∧ P := by
 sorry

-- ### Exercise (1 star): implication-transitivity ⭐

-- Complete a prova abaixo.

example (P Q R : Prop) (h : P → Q) (h2 : Q → R) : P → R := by
  sorry

-- ### Exercise (1 star): unfold-direct-proof ⭐

-- Em algumas provas, podemos precisar expandir uma definição antes de
-- qualquer outro passo de manipulação dos conectivos lógicos. Logo após
-- introduzir o antecedente da implicaçõa como hipótese, considere
-- `unfold E at h` para expandir a definição de `E` na hipótese recém
-- introduzida `h`. Feche a prova com a táctica `linarith`.

def E (x y : Nat) : Prop := x = y

example (x : Nat) : E x 1 → x ≠ 2 := by
  sorry

-- ### Exercise (1 star): unfold-rw-conjunction ⭐

-- Na prova abaixo, o antecedente da implicação precisa ser transformado em
-- hipótese, digamos `h`. Em seguida podemos expandir a definição de `E`.
-- Neste momento, `linarith` já fecharia a prova. Mas sugerimos uma solução
-- mais manual, obter duas novas hipóteses `h1` e `h2` a partir de `h`
-- (eliminação da conjunção). A partir dai, podemos reescrever o *goal* com as
-- hipóteses da forma `h : α = β` com `rewrite [h]` quer irá reescrever o
-- *goal* trocando as ocorrências de `α` por `β`. Finalmente, fechamos a prova
-- com `rfl`. Experimente também a variação de `rewrite` chamada `rw`, que
-- tenta aplicar `rfl` logo após as reescritas.

example (x y : Nat) : E x 0 ∧ E y 0 → x = y := by
  sorry

-- ### Exercise (2 stars): dresses ⭐⭐

-- Complete a prova do teorema, provando que o problema dos vestidos tem a
-- solução onde Ana veste preto, Cláudia veste branco e Maria veste azul.

theorem vestidos₁ (h : Premissas Aa Ab Ap Ma Mb Mp Ca Cb Cp)
  : Ap ∧ Cb ∧ Ma := by
  obtain
    ⟨hA, hM, hC, ha, hb, hp, hA1, hM1,
     hC1, ha1, hb1, hp1, h1, h2, h3, h4, h5⟩ := h

  -- Ana não está de azul: se estivesse, por `h1` ela estaria de branco, mas Ana
  -- não está de branco por `h3`.
  have hnAa : ¬ Aa := by
    sorry

  have hAp : Ap := by
   cases hA with
   | inl hAa => exact absurd hAa hnAa
   | inr hx =>
     cases hx with
     | inl hAb => exact absurd hAb h3
     | inr hAp => exact hAp

  have hCb : Cb := sorry

  have hnCa : ¬ Ca := sorry

  have hMa : Ma := by
    rcases ha with hMa | hAa | hCa
    · sorry
    · sorry
    · sorry

  exact ⟨hAp, hCb, hMa⟩

end PL

-- ## As regras dos quantificadores em Lean

-- O mesmo tipo `Prop` em Lean não está limitado ao raciocínio proposicional.
-- Também podemos representar lógica de primeira ordem em `Prop`. Como já
-- falamos, o Lean se baseia em na teoria dos tipos, na qual se assume que
-- cada variável pertence a algum tipo. Você pode pensar em um tipo como um
-- "universo" ou um "domínio de discurso", no sentido da lógica de primeira
-- ordem. Com a diferença importante de que em lógica de primeira ordem,
-- entedemos o domínio da interpretação com um conjunto não vazio, e um tipo
-- em Lean não necessariamente precisa ser *habitado*.

-- A expressividade de `Prop` vai além de lógica de primeira ordem. Poderíamos
-- ainda falar de lógicas
-- [polissortidas](https://en.wikipedia.org/wiki/First-order_logic) onde
-- poderíamos ter mais de um tipo usado em uma mesma expressão lógica. Por
-- exemplo, podemos querer usar a lógica de primeira ordem para geometria, com
-- quantificadores sobre pontos e linhas. Mas nesta seção, nos restringimos os
-- predicados a um único universo `U`.

section FOL

variable (U : Type)
variable (P Q : U → Prop)

-- Seguindo a apresentação de Lógica Proposicional, quatro novas regras
-- precisam ser explicadas, duas para cada quantificador.

-- A introdução de `∀` diz que para provar que algo vale de todo `x`, tome um
-- `x` arbitrário e prove que vale para ele. É a mesma `intro` agora sobre um
-- objeto em vez de uma hipótese. A eliminação de `∀` é aplicação: de
-- `∀ x P x` e de um objeto `d`, sai `P d`.

example (h : ∀ x, P x) : ∀ y, P y := by
  intro n
  exact h n

-- A introdução de `∃` exige exibir a testemunha. A tática `use` substitui a
-- variável quantificada pelo objeto passado, e deixa como objetivo o que
-- falta provar sobre ele.

example (y : U) (h : P y) : ∃ x, P x :=
  Exists.intro y h

example (y : U) (h : P y) : ∃ x, P x := by
  use y

-- A eliminação de `∃` é a mais delicada. De `∃ x P x` sabe-se que há uma
-- testemunha, mas não sabemos qual elemento do domínio ela é. A tática
-- `obtain` aplica o teorema `Exists.elim`, introduz com um nome, junto com a
-- propriedade que ele satisfaz.

example (h : ∃ x, P x ∧ Q x) : ∃ x, Q x := by
  apply Exists.elim h
  intro d hd
  use d
  exact hd.2

example (h : ∃ x, P x ∧ Q x) : ∃ x, Q x := by
  obtain ⟨d, hP, hQ⟩ := h
  exact ⟨d, hQ⟩

-- A demonstração abaixo não é válida se não declararmos uma variável `u : U`,
-- mesmo que `u` não apareça no enunciado do teorema. Isso destaca uma
-- diferença entre a lógica de primeira ordem e a lógica implementada em Lean.
-- Na dedução natural, podemos provar `∀ x P x → ∃ x P x`, o que mostra que
-- nosso sistema de prova assume implicitamente que o universo tem pelo menos
-- um objeto. Em contraste, em Lean, é possível que um tipo esteja vazio, e,
-- portanto, a prova requer uma suposição explícita de que existe um elemento
-- `u : U`.

variable (u : U)

example: (∀ x , P x) → ∃ x, P x := by
 intro h
 use u
 exact h u

-- ### Exercise (2 stars): forall-exists-swap ⭐⭐

-- Prove o exemplo abaixo e reflita sobre porque não podemos substituir `→`
-- por `↔`.

example {U : Type} (R : U → U → Prop) :
  (∃ y, ∀ x, R x y) → (∀ x, ∃ y, R x y) :=
 sorry

-- ### Exercise (1 star): exists-witness ⭐

-- Prove que `∃ n : Nat, n + n = 10`, exibindo a testemunha. Você pode usar
-- `Exists.intro`.

example : ∃ n : Nat, n + n = 10 := by
  sorry

-- ## Prova por indução

-- Outra tática de prova que podemos precisar é a `induction`. Ela prova algo
-- para todo valor de um tipo indutivo, e não para um valor de cada vez.

-- Considere o exemplo abaixo e a esperada *prova por indução* que faríamos no
-- papel. Mostramos para o caso base, que em `Nat` é o `zero` e depois o passo
-- indutivo, cuja hipótese de indução é nomeada como `ih`.

example (n : Nat) : n + 0 = n := by
  induction n with
  | zero => rfl
  | succ a ih =>
    linarith

-- Ao longo do texto, outras táticas poderão ser usadas como: `decide`,
-- `omega`, `simp` e `funext`, discutiremos quando forem necessárias.

end FOL
end Proof

