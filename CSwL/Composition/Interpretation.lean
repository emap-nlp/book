import CSwL.Composition.TypedMeanings

-- # Implementando a interpretação semântica

namespace Composition

open ModelChecking

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

mutual
  def intSent : Sent → Bool
    | .sent np vp => Rule.sent (intNP np) (intVP vp)

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

#eval intSent (.sent .alice (.vpTrans .admired .dorothy))

example :
    intSent (.sent .alice (.vpTrans .admired .dorothy)) =
      Rule.sent (Rule.npName alice)
        (Rule.vpTrans admire (Rule.npName dorothy)) :=
  rfl

#eval (toString sent1, intSent sent1)

open FOL in
#eval sentences.all fun s =>
  intSent s ==
    (lfSent s).eval entities intFairy ass0
      (liftAssign fintFairy)

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

