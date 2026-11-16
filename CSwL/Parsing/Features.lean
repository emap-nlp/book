-- # Traços e Categorias

namespace Parsing

inductive Feat where
  | masc | fem | neutr | mascOrFem
  | sg | pl
  | fst | snd | thrd
  | nom | accOrDat
  | pers | refl | wh
  | tense | infl
  | on | with | by | to | from
  deriving Repr, DecidableEq

def Feat.toString : Feat → String
  | .masc => "Masc" | .fem => "Fem" | .neutr => "Neutr"
  | .mascOrFem => "MascOrFem"
  | .sg => "Sg" | .pl => "Pl"
  | .fst => "Fst" | .snd => "Snd" | .thrd => "Thrd"
  | .nom => "Nom" | .accOrDat => "AccOrDat"
  | .pers => "Pers" | .refl => "Refl" | .wh => "Wh"
  | .tense => "Tense" | .infl => "Infl"
  | .on => "On" | .with => "With" | .by => "By" | .to => "To"
  | .from => "From"

instance : ToString Feat := ⟨Feat.toString⟩

abbrev Agreement := List Feat

def genderFeats   : Agreement := [.masc, .fem, .neutr, .mascOrFem]
def numberFeats   : Agreement := [.sg, .pl]
def personFeats   : Agreement := [.fst, .snd, .thrd]
def caseFeats     : Agreement := [.nom, .accOrDat]
def pronTypeFeats : Agreement := [.pers, .refl, .wh]
def tenseFeats    : Agreement := [.tense, .infl]
def prepTypeFeats : Agreement := [.on, .with, .by, .to, .from]

def allFeats : Agreement :=
  genderFeats ++ numberFeats ++ personFeats ++ caseFeats ++
    pronTypeFeats ++ tenseFeats ++ prepTypeFeats

def gender (fs : Agreement) : Agreement :=
  fs.filter (· ∈ genderFeats)
def number (fs : Agreement) : Agreement :=
  fs.filter (· ∈ numberFeats)
def person (fs : Agreement) : Agreement :=
  fs.filter (· ∈ personFeats)
def gcase (fs : Agreement) : Agreement :=
  fs.filter (· ∈ caseFeats)
def pronType (fs : Agreement) : Agreement :=
  fs.filter (· ∈ pronTypeFeats)
def tense (fs : Agreement) : Agreement :=
  fs.filter (· ∈ tenseFeats)
def prepType (fs : Agreement) : Agreement :=
  fs.filter (· ∈ prepTypeFeats)

#eval number [.pers, .sg, .thrd, .nom]

def prune (fs : Agreement) : Agreement :=
  if .masc ∈ fs || .fem ∈ fs then fs.erase .mascOrFem else fs

#eval prune [.mascOrFem, .fem, .sg]
#eval prune [.mascOrFem, .neutr, .sg]

abbrev CatLabel := String
abbrev Phon := String

structure Cat where
  phon : Phon
  label : CatLabel
  fs : Agreement
  subcatList : List Cat
  deriving Repr, BEq

instance : ToString Cat where
  toString c :=
    if c.phon == "_" then c.label ++ toString c.fs
    else c.phon ++ " " ++ c.label ++ toString c.fs

namespace Examples

def she : Cat := ⟨"she", "NP", [.pers, .thrd, .sg, .fem, .nom], []⟩
def her : Cat := ⟨"her", "NP", [.pers, .thrd, .sg, .fem, .accOrDat], []⟩
def they : Cat := ⟨"they", "NP", [.pers, .thrd, .pl, .nom], []⟩
def alice : Cat := ⟨"Alice", "NP", [.thrd, .sg, .fem], []⟩
def laughs : Cat := ⟨"laughs", "VP", [.tense, .sg, .thrd], []⟩
def child : Cat := ⟨"child", "CN", [.sg, .thrd, .mascOrFem], []⟩
def thing : Cat := ⟨"thing", "CN", [.sg, .thrd, .neutr], []⟩
def the : Cat := ⟨"the", "DET", [], []⟩

end Examples

open Examples in
#eval toString she

#eval toString ({ phon := "_", label := "NP", fs := [.sg], subcatList := [] } : Cat)

def combine (cat1 cat2 : Cat) : Option Agreement :=
  let feats := prune (allFeats.filter (· ∈ cat1.fs ++ cat2.fs))
  if (gender feats).length ≤ 1 && (number feats).length ≤ 1 &&
      (person feats).length ≤ 1 && (gcase feats).length ≤ 1 &&
      (pronType feats).length ≤ 1 && (tense feats).length ≤ 1 &&
      (prepType feats).length ≤ 1
  then some feats
  else none

def agree (cat1 cat2 : Cat) : Bool :=
  (combine cat1 cat2).isSome

def assign (f : Feat) (c : Cat) : Option Cat :=
  (combine c ⟨"", "", [f], []⟩).map fun fs' => { c with fs := fs' }

open Examples

#eval combine she laughs
#eval agree they laughs
#eval combine the child
#eval agree child thing
#eval (assign .nom alice).map toString
#eval (assign .nom her).map toString

-- ### Exercise (2 stars): combine-comm ⭐⭐

-- Prove que o resultado de `combine` não depende da ordem das duas
-- categorias.

theorem combine_comm (cat1 cat2 : Cat) :
    combine cat1 cat2 = combine cat2 cat1 := by
  sorry

-- ### Exercise (1 star): all-feats ⭐

-- A função `combine` filtra `allFeats`, então um traço que não esteja nessa
-- lista se perde. Prove que todo traço está em `allFeats`.

theorem mem_allFeats (f : Feat) : f ∈ allFeats := by
  sorry

end Parsing

