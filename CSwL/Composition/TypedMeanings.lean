import CSwL.Composition.Quantification

-- # Significados Tipados para a Língua Natural

namespace Composition

open ModelChecking

-- Cada regra sintática da gramática de Verificação de Modelos com Lógica de
-- Primeira Ordem recebe uma regra semântica que combina os significados de
-- seus constituintes. Escrevemos `⟦X⟧` para o significado de uma expressão
-- `X`. Para saber quais combinações fazem sentido, atribuímos tipos a esses
-- significados.

-- A lógica tipada usa dois tipos básicos, `e` para entidades e `t` para
-- valores de verdade, e forma novos tipos de função a partir deles. Aqui,
-- eles são representados por `Entity` e `Bool`. As expressões dessa lógica
-- são funções do Lean, como em Lean e o Cálculo Lambda.

-- Uma sentença, de categoria `S`, tem significado de tipo `Bool`. Um
-- substantivo comum, um substantivo com modificadores ou um sintagma verbal,
-- de categorias `CN`, `RCN` e `VP`, denota uma propriedade, `Entity → Bool`,
-- abreviada por `OnePlacePred`. Um verbo transitivo, de categoria `TV`,
-- denota uma relação de tipo `TwoPlacePred`. Um `NP` recebe uma propriedade e
-- produz um valor de verdade, enquanto um `DET` recebe duas propriedades.
-- Esses tipos permitem combinar os significados seguindo as regras da
-- gramática.

-- Na regra `S → NP VP`, o significado do sujeito é aplicado ao do predicado.
-- O sujeito tem tipo `OnePlacePred → Bool`, e o predicado tem tipo
-- `OnePlacePred`, de modo que a aplicação produz o valor de verdade da
-- sentença.

-- Para dar aos nomes próprios o mesmo tipo dos demais sintagmas nominais, a
-- regra `npName` associa uma entidade `x` à função `fun P => P x`. Assim, o
-- significado de **Alice** recebe uma propriedade e verifica se Alice a tem.
-- Podemos vê-lo como a função característica do conjunto das propriedades de
-- Alice.

-- Na regra que combina determinante e substantivo, aplicamos o significado do
-- determinante à propriedade denotada pelo substantivo. O resultado continua
-- esperando uma propriedade, que será fornecida pelo sintagma verbal. A mesma
-- regra se aplica quando a restrição é um `RCN`.

namespace Rule

def sent (np : OnePlacePred → Bool)
    (vp : OnePlacePred) : Bool :=
  np vp

def npName (x : Entity) : OnePlacePred → Bool :=
  fun P => P x

def npDet (det : OnePlacePred → OnePlacePred → Bool)
    (cn : OnePlacePred) : OnePlacePred → Bool :=
  det cn

end Rule

-- Os determinantes relacionam a propriedade que restringe a quantificação à
-- propriedade que constitui seu escopo, conforme A Visão Relacional dos
-- Quantificadores. **Some** e **a** recebem a interpretação `a`, e **every**
-- recebe `every`.

-- Para **no**, exigimos que nenhuma entidade com a primeira propriedade tenha
-- a segunda. Para **the**, usamos a leitura de Russell: existe exatamente uma
-- entidade com a propriedade da restrição, e essa entidade tem a propriedade
-- do escopo. Na definição, a equivalência entre `p y` e `x = y` exige que `x`
-- seja o único elemento que satisfaz `p`.

def no (p q : OnePlacePred) : Bool :=
  entities.all (fun x => p x → ¬ q x)

def the (p q : OnePlacePred) : Bool :=
  entities.any (fun x =>
    entities.all (fun y => p y ↔ x = y) ∧ q x)

#eval (the princess laugh, no dwarf laugh)

-- Os substantivos comuns e os verbos intransitivos recebem as propriedades
-- fornecidas pelo modelo. Por exemplo, **girl** é interpretado por `girl`.
-- Uma oração relativa restringe essa propriedade por interseção com outra.

-- Em **girl that laughed**, uma entidade deve ser menina e ter rido. A regra
-- `rcnSubj` combina as duas propriedades por conjunção. Já em **girl that
-- some boy loved**, a entidade descrita ocupa a posição de objeto da relação
-- de amar. Para cada menina `x`, o sintagma **some boy** recebe a propriedade
-- `fun y => tv y x`. A regra `rcnObj` exige que esse quantificador aceite a
-- propriedade, isto é, que algum menino tenha amado `x`.

namespace Rule

def rcnSubj (cn vp : OnePlacePred) : OnePlacePred :=
  fun x => cn x && vp x

def rcnObj (cn : OnePlacePred) (np : OnePlacePred → Bool)
    (tv : TwoPlacePred) : OnePlacePred :=
  fun x => cn x && np (fun y => tv y x)

end Rule

-- Para a regra `VP → TV NP`, fixamos o sujeito `x` e formamos a propriedade
-- `fun y => tv x y`. Aplicamos o significado do objeto a essa propriedade e,
-- abstraindo sobre `x`, obtemos a propriedade denotada pelo sintagma verbal.
-- A regra `vpTrans` generaliza a construção usada em `defeated`; o teorema
-- abaixo verifica essa igualdade.

-- Um verbo ditransitivo exige duas aplicações desse procedimento. Na regra
-- `vpDitrans`, o primeiro objeto recebe uma propriedade que contém a
-- aplicação do segundo objeto. A relação do modelo recebe os argumentos na
-- ordem sujeito, primeiro objeto e segundo objeto. Essa ordem também fixa o
-- escopo dos dois quantificadores na composição.

namespace Rule

def vpTrans (tv : TwoPlacePred)
    (np : OnePlacePred → Bool) : OnePlacePred :=
  fun x => np (fun y => tv x y)

def vpDitrans (dv : ThreePlacePred)
    (np₁ np₂ : OnePlacePred → Bool) : OnePlacePred :=
  fun x => np₁ (fun y => np₂ (fun z => dv x y z))

theorem defeated_eq : defeated = vpTrans defeat :=
  rfl

end Rule

-- Podemos compor o significado de **Alice admired Dorothy** seguindo a árvore
-- `[S [NP Alice] [VP [TV admired] [NP Dorothy]]]`. Aplicamos `Rule.npName` às
-- entidades dos dois nomes próprios, combinamos a relação de admirar com o
-- objeto usando `Rule.vpTrans` e aplicamos `Rule.sent` ao sujeito e ao
-- predicado.

-- A avaliação consulta a relação do modelo. O teorema enuncia também uma
-- igualdade que vale para qualquer relação `r`: o resultado da composição é
-- `r alice dorothy`. A prova por `rfl` verifica as reduções das funções
-- aplicadas aos seus argumentos. Essa expressão é a forma normal do
-- significado composto.

namespace Rule

#eval sent (npName alice)
  (vpTrans admire (npName dorothy))

theorem alice_admired_dorothy (r : TwoPlacePred) :
    sent (npName alice) (vpTrans r (npName dorothy)) =
      r alice dorothy :=
  rfl

end Rule

-- ### Exercise (2 stars): snow-white-helped ⭐⭐

-- Componha, com as regras, o significado de **Snow White helped some dwarf**,
-- com uma relação `r` qualquer no lugar de **help**. Depois, escreva a sua
-- forma normal, sem as regras, e prove que as duas são iguais.

namespace Rule

def snowWhiteHelped (r : TwoPlacePred) : Bool :=
  sorry

def snowWhiteHelpedNF (r : TwoPlacePred) : Bool :=
  sorry

theorem snowWhiteHelped_nf (r : TwoPlacePred) :
    snowWhiteHelped r = snowWhiteHelpedNF r := by
  sorry

end Rule

end Composition

