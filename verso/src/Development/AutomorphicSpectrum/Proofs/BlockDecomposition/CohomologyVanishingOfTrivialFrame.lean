import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalisationLadders.CriterionTruncation
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.FramedSite

/- English proof (translation)
Take `⟨-, -, hex0, hex⟩` from `CrystallineSemistableComparison.P.initial F E.D (Frame.initial E)`. Establish `key : ∀ x : CH.H F n, x = 0`. Introduce `x`. Take `⟨a, ha, rfl⟩` from `(CrystallineSemistableComparison.P.cls_surj (CH.cx F) n).1 x`. Use `((CrystallineSemistableComparison.P.cls_surj (CH.cx F) n).2.1 a ha).2 ?_` and prove the remaining obligations.

Consider the cases of `n with`. Consider the case `zero`. Take `⟨m, hm⟩` from `hex0 a ha`. Rewrite `hm` using `[one_smul]`. Establish `hm0 : m = 0` using `Subsingleton.elim _ _`.

Rewrite `hm` using `[hm0, map_zero]`. Conclude with `hm.symm`. Consider the case `succ n`. Take `⟨y, hy⟩` from `hex n a ha`. Rewrite `hy` using `[one_smul]`.

Conclude with `⟨y, hy⟩`. Conclude with `⟨fun x y => by rw [key x, key y]⟩`.
-/
theorem cohomology_subsingleton_of_frame_zero {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C}
    (E : Frame Φ 0) (F : C ⥤ ModuleCat.{0} R) (hD : Subsingleton (F.obj E.D)) (n : ℕ) :
    Subsingleton (CH.H F n) := by
  obtain ⟨-, -, hex0, hex⟩ := CrystallineSemistableComparison.P.initial F E.D (Frame.initial E)
  have key : ∀ x : CH.H F n, x = 0 := by
    intro x
    obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (CH.cx F) n).1 x
    refine ((CrystallineSemistableComparison.P.cls_surj (CH.cx F) n).2.1 a ha).2 ?_
    cases n with
    | zero =>
      obtain ⟨m, hm⟩ := hex0 a ha
      rw [one_smul] at hm
      have hm0 : m = 0 := Subsingleton.elim _ _
      rw [hm0, map_zero] at hm
      exact hm.symm
    | succ n =>
      obtain ⟨y, hy⟩ := hex n a ha
      rw [one_smul] at hy
      exact ⟨y, hy⟩
  exact ⟨fun x y => by rw [key x, key y]⟩

end GlobalTheory.CompanionTheory.FramedSite
