import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalisationLadders.CriterionTruncation
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.Cohomology

/- English proof (translation)
Take `⟨c₁, c₂, c₃⟩` from `CrystallineSemistableComparison.P.ses_cochains α β hi he hs`. Take `⟨δ, -, hinj, -, -, hex⟩` from `CrystallineSemistableComparison.P.les (CH.Mor.ofNatTrans α).hom (CH.Mor.ofNatTrans β).hom c₁ c₂ c₃`. Introduce `n`. Consider the cases of `n with`. Consider the case `zero => haveI : Subsingleton ((CH.cx F₂).H 0) := h₂ 0`.

Conclude with `⟨fun x y => hinj (Subsingleton.elim _ _)⟩`. Consider the case `succ n => haveI : Subsingleton ((CH.cx F₂).H (n + 1)) := h₂ (n + 1) haveI : Subsingleton ((CH.cx F₃).H n) := h₃ n`. Establish `key : ∀ x : (CH.cx F₁).H (n + 1), x = 0` using `fun x => by`. Take `⟨y, rfl⟩` from `(hex n x).1 (Subsingleton.elim _ _)`. Rewrite using `[Subsingleton.elim y 0, map_zero]`.

Conclude with `⟨fun x y => (key x).trans (key y).symm⟩`.
-/
theorem subsingleton_H_of_ses {R : Type} [CommRing R] {C : Type 1} [Category.{0} C]
    {F₁ F₂ F₃ : C ⥤ ModuleCat.{0} R} (α : F₁ ⟶ F₂) (β : F₂ ⟶ F₃)
    (hi : ∀ T, Function.Injective (α.app T).hom)
    (he : ∀ T, Function.Exact (α.app T).hom (β.app T).hom)
    (hs : ∀ T, Function.Surjective (β.app T).hom)
    (h₂ : ∀ n, Subsingleton (CH.H F₂ n)) (h₃ : ∀ n, Subsingleton (CH.H F₃ n)) :
    ∀ n, Subsingleton (CH.H F₁ n) := by
  obtain ⟨c₁, c₂, c₃⟩ := CrystallineSemistableComparison.P.ses_cochains α β hi he hs
  obtain ⟨δ, -, hinj, -, -, hex⟩ :=
    CrystallineSemistableComparison.P.les (CH.Mor.ofNatTrans α).hom (CH.Mor.ofNatTrans β).hom c₁ c₂ c₃
  intro n
  cases n with
  | zero =>
    haveI : Subsingleton ((CH.cx F₂).H 0) := h₂ 0
    exact ⟨fun x y => hinj (Subsingleton.elim _ _)⟩
  | succ n =>
    haveI : Subsingleton ((CH.cx F₂).H (n + 1)) := h₂ (n + 1)
    haveI : Subsingleton ((CH.cx F₃).H n) := h₃ n
    have key : ∀ x : (CH.cx F₁).H (n + 1), x = 0 := fun x => by
      obtain ⟨y, rfl⟩ := (hex n x).1 (Subsingleton.elim _ _)
      rw [Subsingleton.elim y 0, map_zero]
    exact ⟨fun x y => (key x).trans (key y).symm⟩

end GlobalTheory.CompanionTheory.Cohomology
