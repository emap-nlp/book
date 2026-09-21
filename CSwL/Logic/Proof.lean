import Mathlib.Tactic
import CSwL.IntroL

-- # Provas em Lean

-- Neste capítulo vamos falar sobre o tipo `Prop` em Lean para representação
-- de proposições lógicas em tipos dependentes. A representação de proposições
-- e construção de provas é o que torna Lean um assistente de prova, além de
-- linguagem de programação. Vamos apresentar provas como termos e a
-- construção de provas com táticas.

-- Supomos conhecida a lógica proposicional e a de predicados — sintaxe,
-- semântica, e a noção de consequência. Para uma apresentação a partir do
-- início, ver (Enderton, 2001).

namespace Proof

-- ## O tipo `Prop` e Provas

-- O que diferencia Lean de outras linguagens como Python ou Java, é a
-- capacidade de usarmos a mesma linguagem para programar funções e escrever
-- provas sobre estas funções.

-- Uma proposição é um enunciado que pode ser verdadeiro ou falso. O enunciado
-- `1 = 1` é verdadeiro, enquanto `square₁ 12 = 2` é falso. Toda proposição é
-- um tipo em `Prop` (Yingchareonthawornchai, 2025). Podemos declarar
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
-- importante da fundação de Lean em *Calculus of Inductive Constructions*
-- (CIC) (Nederpelt and Geuvers, 2014): expressões de tipos e programas podem
-- ser computadas e comparadas por redução. Assim, `rfl` é frequentemente
-- usado para dizer que os dois lados são iguais porque são o mesmo valor
-- depois de reduzir o código. O comando `#print double_theorem` irá mostrar
-- que a tática `rfl` construiu o termo `Eq.refl`.

def double (n : Nat) := n + n

theorem double_theorem : double 5 = 5 + 5 := by rfl

-- A tática `rfl` só funciona quando os dois lados são idênticos por
-- definição. Para propriedades que exigem leis algébricas (como a
-- comutatividade da multiplicação), precisamos aplicar teoremas específicos,
-- como `Nat.mul_comm`.

example (z : Nat) : (λ x ↦ 2 * x) z = (fun y => 2 * y) z := by
  rfl

example (z : Nat) : (λ x ↦ 2 * x) z = (fun y => y * 2) z := by
  exact Nat.mul_comm 2 z

-- ### Exercise (1 star): rfl-arithmetic ⭐

-- Complete a prova abaixo usando a tática `rfl`. Esta é a primeira prova do
-- [Natural Number
-- Game](https://adam.math.hhu.de/#/g/leanprover-community/nng4/). O leitor
-- está convidado a jogar NNG para uma boa introdução a provas no Lean.

example (x q : Nat) : 37 * x + q = 37 * x + q :=
 sorry

-- ## Lógica Proposicional em Lean

namespace PL

-- Os conectivos lógicos `∧`, `∨`, `→`, `↔` e `¬` estão disponíveis
-- diretamente no Lean, de modo que uma fórmula proposicional pode ser
-- representada como uma proposição em Lean. Isso nos fornece uma ponte
-- conveniente entre a semântica da linguagem natural e o raciocínio formal.
-- Podemos traduzir o conteúdo semântico de uma sentença para uma proposição
-- em Lean e, em seguida, usar Lean para verificar se uma conclusão decorre de
-- um conjunto de hipóteses.

-- Chamamos "sistema dedutivo" um conjunto das regras de dedução. Existem
-- vários sistemas dedutivos. A formalização de Prop em Lean corresponde a
-- implementação do sistema chamado **dedução natural** definido por Gerhard
-- Gentzen em 1930. Usando as regras de dedução natural, podemos provar que
-- uma fórmula `α` pode ser derivada a partir de um conjunto de fórmulas `Γ`,
-- dizemos que `Γ ⊢ α`. Dizemos que `⊢ α` quando a fórmula `α` é válida, uma
-- tautologia.

-- Neste sistema dedutivo, cada conectivo vem com dois tipos de regra. As de
-- **introdução**, que dizem como construir uma prova cuja conclusão usa o
-- conectivo, e as de **eliminação**, que dizem como usar uma prova cuja
-- hipótese o usa.

variable {P Q R : Prop}

-- A regra de introdução de `→` diz que para provar `P → Q`, supomos `P` e
-- derivamos `Q`. A tatica `intro` move o antecedente para as hipóteses.

-- A regra de eliminação é a chamada regra **modus ponens**. A partir de
-- `P → Q` e de `P`, podemos concluir `Q`. O termo Lean `h hP` já é a prova de
-- `Q`. A tática `apply` faz o mesmo de trás para frente, ela transforma o
-- objetivo `Q` no novo objetivo `P`. A `exact` fecha a prova fornecendo a
-- hipótese cujo tipo coincide com o tipo do objetivo. A `assumption` busca
-- automaticamente se alguma hipótese do contexto coincide com o objetivo, sem
-- que seja necessário nomeá-la explicitamente.

example : P → (Q → P) := by
  intro hP hQ
  exact hP

example (h₁ : P → Q) (h₂ : Q → R) : P → R := by
  intro hP
  apply h₂
  apply h₁
  assumption

example (h : P → Q) (hP : P) : Q := h hP

-- Para a conjunção, provar `P ∧ Q` depende de uma prova de `P` e de uma prova
-- de `Q`. A tática `constructor` divide o objetivo em dois novos objetivos; o
-- construtor anônimo `⟨_, _⟩` faz o mesmo em forma de termo. A eliminação de
-- `∧` em `P ∧ Q` significa que podemos concluir `P` ou `Q`. São duas regras,
-- e em Lean são as projeções `.1` (ou `.left`) e `.2` (ou `.right`). A tática
-- `obtain` desmonta a hipótese de uma vez, dando nome às duas partes.

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

-- Para provar `P ∨ Q` basta provar um dos dois lados. São duas regras, e os
-- construtores `Or.inl` (aplicado pela tática `left`) e `Or.inr` (aplicado
-- pela tática `right`) formalizam elas. A regra de eliminação da disjunção é
-- o teorema `Or.elim`, a chamada "prova por casos". Dada a hipótese `P ∨ Q`,
-- não sabemos qual das duas proposições é verdadeira. Portanto, para concluir
-- `R`, precisamos provar `R` em ambos os casos (assumindo `P` no primeiro e
-- `Q` no segundo). A tática `cases` gera exatamente esses dois cenários.

example (hP : P) : P ∨ Q := by
  left
  exact hP

example (h : P ∨ Q) : Q ∨ P := by
  cases h with
  | inl hP => right; exact hP
  | inr hQ => left; exact hQ

-- Não há um conectivo primitivo para a negação: `¬ P` é notação para
-- `P → False` onde `False` é a proposição que não possui prova. Desta forma,
-- a introdução da negação usa a mesma regra da introdução da implicação `→`.
-- Para provar `¬P`, supomos `P` para derivar `False`. A eliminação é a
-- eliminação de `→`. A regra que a tradição chama de **ex falso quodlibet**
-- (princípio da explosão), a partir de uma contradição ou de uma premissa
-- falsa, qualquer conclusão pode ser deduzida. `False.elim` em Lean. As duas
-- juntas são `absurd`.

example (h : P → Q) : ¬Q → ¬P := by
  intro hnQ hP
  exact hnQ (h hP)

example (hP : P) (hn : ¬P) : False := hn hP
example (h : False) : P := False.elim h
example (hP : P) (hn : ¬P) : Q := absurd hP hn

-- A bicondicional `P ↔ Q` é definida como a conjunção das duas implicações
-- ((P → Q) ∧ (Q → P)), a tática `constructor` evoca `Iff.intro` que
-- transforma o objetivo da prova em duas provas, uma para cada implicação. Os
-- parâmetros do construtor explicam as regras de eliminação, duas regras dado
-- tratar-se de uma conjunção de implicações, `Iff.mpr` e `Iff.mp`.

example : P ∧ Q ↔ Q ∧ P := by
  constructor
  · intro h; exact ⟨h.2, h.1⟩
  · intro h; exact ⟨h.2, h.1⟩

example (h : P ↔ Q) (hP : P) : Q := h.mp hP

-- Até este ponto, todas as regras que utilizamos pertencem à **lógica
-- construtiva** (ou intuicionista). Nela, provar uma disjunção `P ∨ Q` exige
-- construir explicitamente uma prova de `P` ou uma prova de `Q`. Não é
-- permitido afirmar que "um dos dois é verdade" sem saber qual. Em
-- particular, a lógica construtiva não assume que toda proposição é
-- necessariamente verdadeira ou falsa. A **lógica clássica** acrescenta o
-- princípio do terceiro excluído, `Classical.em`, que afirma que para
-- qualquer proposição `P`, vale `P ∨ ¬P`. A partir desse princípio, derivamos
-- duas táticas fundamentais para provas clássicas:

-- - `by_cases`. Quando usamos `by_cases (hP : P)`, o objetivo atual é dividido
--   em dois casos independentes, um assumindo `hP : P` (`P` é verdadeiro) e
--   outro assumindo `hP : ¬P` (`P` é falso).

-- - `by_contra`: Realiza a prova por redução ao absurdo. Para provar `P`,
--   supõe-se que `¬ P` e o objetivo torna-se derivar uma contradição (False).

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

-- Se o câmbio cair, temos inflação. Se as exportações crescerem, diminuímos o
-- déficit. O câmbio cai ou diminuímos o déficit. Logo, temos inflação ou as
-- exportações crescem.

-- complete a definição `exchange` para formalizar o parágrafo anterior. Você
-- deverá usar as variáveis proposicionais declaradas para `p` (câmbio cai),
-- `q` (temos inflação), `r` (exportações crescem) e `s` (diminuimos o
-- déficit) para construir a proposição esperada.

section
variable (p q r s : Prop)

def exchange : Prop :=
  sorry
end

-- ### Exercise (2 stars): implication-as-disj ⭐⭐

-- Complete a prova abaixo. Note que esta prova precisa do fragmento clássico.
-- Tente usar `by_cases`.

example (P Q : Prop) : (P → Q) → ¬ P ∨ Q := by
  sorry

-- ### Exercise (1 star): and-comm ⭐

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
-- introduzir o antecedente da implicação como hipótese, considere
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

-- Três irmãs — Ana, Maria e Cláudia — foram a uma festa com vestidos de cores
-- diferentes. Uma vestiu azul, a outra branco, e a terceira, preto. Chegando
-- à festa, o anfitrião perguntou quem era cada uma delas.

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

namespace Dresses

variable (Aa Ab Ap Ma Mb Mp Ca Cb Cp  : Prop)

-- A ideia é que as condições do problema sejam traduzidas em fórmulas
-- proposicionais. Por exemplo, podemos formalizar a sentença "Ana veste azul,
-- branco ou preto" como `Aa ∨ Ab ∨ Ap`. Note que a fórmula não foi obtida
-- diretamente a partir da construção linguística original, uma oração
-- coordenando seus constituintes no predicado. Intuitivamente, a sentença foi
-- antes interpretada como três orações coordenadas: "Ana veste azul ou Ana
-- veste branco ou Ana veste preto".

-- A formalização completa do problema deve levar em consideração não apenas o
-- que foi dito explicitamente mas algumas condições implicitamente assumidas.
-- Primeiro que cada irmã veste uma das cores.

variable (hA : Aa ∨ Ab ∨ Ap)
variable (hM : Ma ∨ Mb ∨ Mp)
variable (hC : Ca ∨ Cb ∨ Cp)

-- Em seguida, que cada vestido é de alguma das irmãs.

variable (ha : Ma ∨ Aa ∨ Ca)
variable (hb : Ab ∨ Mb ∨ Cb)
variable (hp : Ap ∨ Mp ∨ Cp)

-- Também precisaremos formalizar que uma irmã veste apenas um vestido e que
-- um vestido é vestido por apenas uma irmã.

variable (hA1 : (Aa → ¬ Ab ∧ ¬ Ap) ∧ (Ab → ¬ Aa ∧ ¬ Ap) ∧ (Ap → ¬ Aa ∧ ¬ Ab))
variable (hM1 : (Ma → ¬ Mb ∧ ¬ Mp) ∧ (Mb → ¬ Ma ∧ ¬ Mp) ∧ (Mp → ¬ Ma ∧ ¬ Mb))
variable (hC1 : (Ca → ¬ Cb ∧ ¬ Cp) ∧ (Cb → ¬ Ca ∧ ¬ Cp) ∧ (Cp → ¬ Ca ∧ ¬ Cb))

variable (ha1 : (Ma → ¬ Aa ∧ ¬ Ca) ∧ (Ca → ¬ Aa ∧ ¬ Ma) ∧ (Aa → ¬ Ma ∧ ¬ Ca))
variable (hb1 : (Mb → ¬ Ab ∧ ¬ Cb) ∧ (Cb → ¬ Ab ∧ ¬ Mb) ∧ (Ab → ¬ Mb ∧ ¬ Cb))
variable (hp1 : (Mp → ¬ Ap ∧ ¬ Cp) ∧ (Cp → ¬ Ap ∧ ¬ Mp) ∧ (Ap → ¬ Mp ∧ ¬ Cp))

-- Finalmente, a partir das perguntas feitas para as irmãs, podemos extrair as
-- seguintes proposições. Da primeira pergunta, extraímos `h1` e `h2`. Na
-- segunda pergunta extraímos `h3` e da terceira pergunta, `h4` e `h5`. O
-- leitor pode conferir como estas proposições foram extraídas considerando
-- cada possível irmã respondendo a cada pergunta.

variable (h1 : Aa → Ab)
variable (h2 : Ca → ¬ Ab)

variable (h3 : ¬ Ab)

variable (h4 : Ap → Cb)
variable (h5 : Cp → ¬ Cb)

-- Complete a prova do teorema, provando que o problema dos vestidos tem a
-- solução onde Ana veste preto, Cláudia veste branco e Maria veste azul. A
-- declaração `include ... in` irá incluir as variáveis declaradas (as
-- hipóteses) anteriormente que efetivamente são necessárias como parâmetros
-- para o teorema seguinte. A inclusão de hipóteses desnecessárias irá emitir
-- um alerta, mas não um erro.

include hA ha hC1 h1 h3 h4 in

theorem vestidos : Ap ∧ Cb ∧ Ma := by

  have hnAa : ¬ Aa := by
    sorry

  have hAp : Ap := by
   cases hA with
   | inl hAa => exact absurd hAa hnAa
   | inr hx =>
     sorry

  have hCb : Cb := by
    sorry

  have hnCa : ¬ Ca :=  by
    sorry

  have hMa : Ma := by
    sorry

  exact ⟨hAp, hCb, hMa⟩

end Dresses

end PL

-- ## As regras dos Quantificadores em Lean

-- O tipo `Prop` não está limitado ao raciocínio proposicional; ele também nos
-- permite representar proposições da lógica de primeira ordem. Como vimos, o
-- Lean é fundamentado na teoria dos tipos, na qual toda variável pertence a
-- algum tipo. Podemos entender um tipo como o "universo" ou "domínio de
-- discurso" da lógica formal. No entanto, como veremos, há uma diferença
-- importante: enquanto a lógica de primeira ordem clássica exige que o
-- domínio de interpretação seja sempre um conjunto não-vazio, em Lean um tipo
-- não precisa ser necessariamente habitado.

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

-- Seguindo a estrutura da seção anterior, explicaremos quatro novas regras:
-- duas para o quantificador universal (`∀`) e duas para o existencial (`∃`).

-- A introdução de `∀` estabelece que, para provar que uma propriedade vale
-- para todo `x`, basta tomar um `x` arbitrário e demonstrar que a propriedade
-- se aplica a ele. Em modo de tática, usamos a mesma tática `intro`, mas
-- agora ela adiciona um novo objeto no contexto, também como variável do tipo
-- apropriado, em vez de uma hipótese do tipo `Prop`. A eliminação de `∀` é
-- feita por aplicação direta: se temos uma prova `h : ∀ x, P x` e um objeto
-- `d`, a aplicação `h d` nos fornece uma prova de `P d`, desde que os tipos
-- obviamente sejam compatíveis.

example (h : ∀ x, P x) : ∀ y, P y := by
  intro n
  exact h n

-- A introdução de `∃` exige uma testemunha (o objeto que satisfaz a
-- propriedade). Em modo de tática, a tática `use` substitui a variável
-- quantificada pelo objeto fornecido e deixa como novo objetivo a prova de
-- que tal objeto satisfaz o predicado. Em modo de termo, isso é feito pelo
-- construtor `Exists.intro`.

example (y : U) (h : P y) : ∃ x, P x :=
  Exists.intro y h

example (y : U) (h : P y) : ∃ x, P x := by
  use y

-- A eliminação de `∃` é a regra mais delicada. De `∃ x, P x` sabe-se que há
-- uma testemunha, mas não sabemos qual elemento do domínio usar. A tática
-- `obtain` aplica o teorema `Exists.elim`, introduzindo a testemunha com um
-- nome no contexto, junto com a propriedade que ela satisfaz.

example (h : ∃ x, P x ∧ Q x) : ∃ x, Q x := by
  apply Exists.elim h
  intro d hd
  use d
  exact hd.2

example (h : ∃ x, P x ∧ Q x) : ∃ x, Q x := by
  obtain ⟨d, hP, hQ⟩ := h
  exact ⟨d, hQ⟩

-- Tendo apresentado as regras de introdução e eliminação dos quantificadores,
-- é importante observar como o Lean trata a existência de valores em um tipo
-- na prática.

-- A demonstração abaixo de `(∀ x, P x) → ∃ x, P x` só é válida se declararmos
-- previamente uma variável `u : U`. Isso evidencia uma diferença sutil entre
-- a lógica de primeira ordem tradicional e a implementação no Lean: enquanto
-- a dedução natural clássica assume implicitamente que o universo de discurso
-- é sempre não-vazio, no Lean um tipo pode ser vazio (não-habitado). Assim,
-- para instanciar a testemunha com `use u`, precisamos fornecer a suposição
-- explícita de que existe ao menos um elemento `u : U`. Uma outra forma de
-- ter o mesmo efeito seria demandar que o tipo `U` implemente a classe
-- `Nonempty`.

variable (u : U)

example: (∀ x , P x) → ∃ x, P x := by
 intro h
 use u
 exact h u

-- ### Exercise (2 stars): forall-exists-swap ⭐⭐

-- Prove o exemplo abaixo e reflita sobre porque não podemos substituir `→`
-- por `↔`.

example {U : Type} (R : U → U → Prop) :
  (∃ y, ∀ x, R x y) → (∀ x, ∃ y, R x y) := by
 sorry

-- ### Exercise (1 star): exists-witness ⭐

-- Prove que `∃ n : Nat, n + n = 10`, exibindo a testemunha. Você pode usar
-- `Exists.intro`.

example : ∃ n : Nat, n + n = 10 := by
  sorry

end FOL

-- ## Provas por Indução

-- Uma das ferramentas fundamentais no Lean é a tática `induction`. Em vez de
-- provar uma propriedade para elementos individuais, ela permite demonstrar
-- que uma afirmação é válida para todos os valores de um tipo indutivo (como
-- os `Nat`).

-- Considere o exemplo abaixo de uma prova por indução. Primeiro, demonstramos
-- a propriedade para o caso onde `n` é o termo `Nat.zero`. Em seguida,
-- provamos o passo indutivo, quando `n` é um termo gerado pelo construtor
-- `Nat.succ` e quando assumimos que a propriedade vale para um `a`
-- (armazenada na hipótese de indução `ih`) e demonstramos que ela se mantém
-- para o seu sucessor `a + 1`.

example (n : Nat) : n + 0 = n := by
  induction n with
  | zero => rfl
  | succ a ih =>
    linarith

-- ## Extensionalidade de Funções

-- Uma função pode ser compreendida sob duas perspectivas. Na perspectiva
-- extensional, a função é vista como uma relação ou tabela de mapeamento — o
-- conjunto de todos os pares de entrada e saída, como a tabela
-- `{(0, 32), (100, 212), ...}`. Na perspectiva intensional, a função é o
-- próprio algoritmo ou instrução que calcula a saída a partir da entrada,
-- como a expressão `λ x ↦ x * 9 / 5 + 32`, uma "receita" que gera a tabela
-- sem precisar enumerá-la.

-- No Lean, o comando `def` sempre define funções no sentido intensional. No
-- entanto, duas definições intencionalmente distintas podem representar a
-- mesma função no sentido extensional, desde que produzam a mesma saída para
-- cada entrada. É esse o princípio da extensionalidade de funções: a tática
-- `funext` transforma o objetivo de provar que duas funções são iguais
-- (`f = g`) no objetivo de demonstrar que elas coincidem para todo ponto do
-- domínio para o qual são definidas.

def double₁ (x : Nat) := 2 * x
def double₂ (x : Nat) := x + x

example : double₁ = double₂ := by
  funext n
  rw [double₁, double₂]
  exact (Nat.two_mul n)

-- ## Outras Táticas

-- No Lean, as táticas `decide` e `native_decide` têm a mesma ideia básica.
-- São usadas para provar uma proposição por computação, como existe uma
-- instância `Decidable`. Mas executam essa computação de formas diferentes. A
-- `decide` executa dentro do próprio kernel do Lean. É simples e totalmente
-- baseada na redução dos termos para formas normais do Lean, mas pode ser
-- lenta para computações grandes. A `native_decide` faz a mesma decisão,
-- porém compila a computação para código nativo antes de executá-la.

example : (List.range 100000).length = 100000 := by
  native_decide

-- Outras táticas como `omega` e `simp` aparecerão em momentos específicos dos
-- capítulos seguintes e serão explicadas à medida que se fizerem necessárias.

end Proof

