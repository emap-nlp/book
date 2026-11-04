import CSwL.Composition.Quantification

-- # Significados tipados para a língua natural

namespace Composition

open ModelChecking

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

def no (p q : OnePlacePred) : Bool :=
  entities.all (fun x => p x → ¬ q x)

def the (p q : OnePlacePred) : Bool :=
  entities.any (fun x =>
    entities.all (fun y => p y ↔ x = y) ∧ q x)

#eval (the princess laugh, no dwarf laugh)

namespace Rule

def rcnSubj (cn vp : OnePlacePred) : OnePlacePred :=
  fun x => cn x && vp x

def rcnObj (cn : OnePlacePred) (np : OnePlacePred → Bool)
    (tv : TwoPlacePred) : OnePlacePred :=
  fun x => cn x && np (fun y => tv y x)

end Rule

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

