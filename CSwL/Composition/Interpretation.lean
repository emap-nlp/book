import CSwL.Composition.TypedMeanings

-- # A Implementação da Interpretação Semântica

namespace Composition

open ModelChecking

-- Em Significados Tipados para a Língua Natural, escolhemos as regras
-- semânticas ao montar cada expressão. Agora vamos definir funções que
-- percorrem a árvore sintática e escolhem a regra correspondente a cada
-- construtor. A interpretação de uma sentença, um valor de `Sent`, será um
-- valor de verdade.

-- Começamos pelas categorias lexicais. Cada substantivo comum recebe a
-- propriedade correspondente no modelo, e cada verbo transitivo ou
-- ditransitivo recebe uma relação. Os determinantes recebem as funções já
-- definidas; em particular, **some** e **a** têm a mesma interpretação.

-- O modelo não fornece interpretações para os adjetivos nem para **caught**.
-- Como em Verificação de Modelos com Lógica de Primeira Ordem, atribuímos a
-- eles propriedades ou relações que são falsas para todos os argumentos.

def intCN : CN → OnePlacePred
  | .girl => girl
  | .boy => boy
  | .princess => princess
  | .dwarf => dwarf
  | .giant => giant
  | .wizard => wizard
  | .sword => sword
  | .dagger => dagger

def intADJ : ADJ → OnePlacePred
  | _ => fun _ => false

def intTV : TV → TwoPlacePred
  | .loved => love
  | .admired => admire
  | .helped => help
  | .defeated => defeat
  | .caught => fun _ _ => false

def intDV : DV → ThreePlacePred
  | .gave => give

def intDET : DET → OnePlacePred → OnePlacePred → Bool
  | .a => a
  | .some => a
  | .every => every
  | .no => no
  | .the => the

-- As interpretações de `NP`, `VP` e `RCN` dependem umas das outras,
-- acompanhando a definição das categorias sintáticas. Por isso, são definidas
-- em um bloco `mutual`. A interpretação de `Sent` vem depois do bloco e
-- aplica a de `NP` à de `VP`. Em cada caso, interpretamos os constituintes e
-- aplicamos a regra semântica correspondente. A recursão segue as subárvores
-- da expressão recebida.

-- Os nomes próprios são tratados por `Rule.npName`. Os pronomes **everyone**
-- e **someone** recebem, respectivamente, os quantificadores `every` e `a`
-- com a restrição `person`. Os sintagmas formados por determinantes e
-- substantivos usam `Rule.npDet`.

-- As orações relativas usam as regras de interseção de propriedades. O mesmo
-- mecanismo interpreta um adjetivo junto de um substantivo: **happy wizard**
-- exige que a entidade satisfaça tanto a propriedade do adjetivo quanto a do
-- substantivo. Com a interpretação lexical adotada para os adjetivos, essa
-- propriedade será falsa para toda entidade.

mutual

def intNP : NP → OnePlacePred → Bool
  | .snowWhite => Rule.npName snowWhite
  | .alice => Rule.npName alice
  | .dorothy => Rule.npName dorothy
  | .goldilocks => Rule.npName goldilocks
  | .littleMook => Rule.npName littleMook
  | .atreyu => Rule.npName atreyu
  | .everyone => every person
  | .someone => a person
  | .npDet det cn =>
    Rule.npDet (intDET det) (intCN cn)
  | .npDetRel det rcn =>
    Rule.npDet (intDET det) (intRCN rcn)

def intVP : VP → OnePlacePred
  | .laughed => laugh
  | .cheered => cheer
  | .shuddered => shudder
  | .vpTrans tv np => Rule.vpTrans (intTV tv) (intNP np)
  | .vpDitrans dv np₁ np₂ =>
    Rule.vpDitrans (intDV dv) (intNP np₁) (intNP np₂)

def intRCN : RCN → OnePlacePred
  | .rcnSubj cn _ vp => Rule.rcnSubj (intCN cn) (intVP vp)
  | .rcnObj cn _ np tv =>
    Rule.rcnObj (intCN cn) (intNP np) (intTV tv)
  | .rcnAdj adj cn => Rule.rcnSubj (intADJ adj) (intCN cn)

end

def intSent : Sent → Bool
  | .sent np vp => Rule.sent (intNP np) (intVP vp)

-- O significado de **Alice admired Dorothy** pode agora ser calculado a
-- partir de sua árvore, construída com os valores `.alice`, `.admired` e
-- `.dorothy` das categorias sintáticas. A função `intSent` percorre essa
-- árvore e aplica as regras semânticas.

-- O exemplo provado por `rfl` mostra que o resultado é a mesma aplicação de
-- `Rule.sent`, `Rule.npName` e `Rule.vpTrans` que escrevemos à mão. A função
-- de interpretação automatiza essa escolha de regras.

#eval intSent (.sent .alice (.vpTrans .admired .dorothy))

example :
    intSent (.sent .alice (.vpTrans .admired .dorothy)) =
      Rule.sent (Rule.npName alice)
        (Rule.vpTrans admire (Rule.npName dorothy)) :=
  rfl

-- A árvore `sent1` representa **The dwarf that Snow White helped admired
-- every princess**. Podemos avaliá-la diretamente com `intSent` ou traduzi-la
-- com `lfSent` e avaliar a fórmula resultante no modelo.

-- O segundo comando `#eval` compara os dois caminhos para as trinta e duas
-- sentenças de `sentences`. Essa verificação avalia os exemplos da lista; uma
-- prova de equivalência para toda árvore exigiria demonstrar uma afirmação
-- geral sobre as funções de interpretação e tradução.

#eval (toString sent1, intSent sent1)

/-- Four noun phrases to build test sentences from. -/
def someNPs : List NP :=
  [.alice, .snowWhite,
   .npDet .every .wizard, .npDet .a .dwarf]

/-- The thirty-two sentences `NP TV NP` built from `someNPs`
and the verbs *helped* and *defeated*. -/
def sentences : List Sent :=
  someNPs.flatMap fun subj =>
    [TV.helped, TV.defeated].flatMap fun v =>
      someNPs.map fun obj =>
        Sent.sent subj (.vpTrans v obj)

open FOL in
#eval sentences.all fun s =>
  intSent s ==
    (lfSent s).eval entities intFairy ass0
      (liftAssign fintFairy)

-- A interpretação direta permite usar quantificadores como **most**. No
-- domínio finito do modelo, contamos os elementos da restrição que satisfazem
-- o escopo e os que não o satisfazem. **Most** é verdadeiro quando a primeira
-- quantidade é maior que a segunda.

-- Essa função tem o mesmo tipo dos outros significados de determinantes.
-- Podemos, portanto, passá-la a `Rule.npDet` e compor o resultado com
-- `Rule.sent`. É assim que avaliamos **Most girls laughed** e a sentença
-- sobre as pessoas que admiraram Goldilocks. Esses exemplos compõem os
-- significados diretamente, sem acrescentar um construtor à categoria
-- sintática `DET`.

def most (p q : OnePlacePred) : Bool :=
  (entities.filter fun x => p x && !q x).length <
    (entities.filter fun x => p x && q x).length

#eval Rule.sent (Rule.npDet most girl) laugh
#eval Rule.sent (Rule.npDet most person)
  (Rule.vpTrans admire (Rule.npName goldilocks))

-- ### Exercise (2 stars): at-least-at-most ⭐⭐

-- Defina `atLeastDet n` e `atMostDet n`, as interpretações de **at least n**
-- e **at most n**. Depois, prove as sentenças abaixo.

def atLeastDet (n : Nat) (p q : OnePlacePred) : Bool :=
  sorry

def atMostDet (n : Nat) (p q : OnePlacePred) : Bool :=
  sorry

theorem atLeastTwoGirlsLaughed :
    Rule.sent (Rule.npDet (atLeastDet 2) girl) laugh
      = true := by
  sorry

theorem atMostOneDwarfLaughed :
    Rule.sent (Rule.npDet (atMostDet 1) dwarf) laugh
      = true := by
  sorry

theorem notAtLeastThreeGirlsLaughed :
    Rule.sent (Rule.npDet (atLeastDet 3) girl) laugh
      = false := by
  sorry

end Composition

