import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PermRepSingle
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ExistsFreeResolutionShortExact
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ProjectiveRepGroupHomologyPosVanishes
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.PermCoefPreservesShortExact
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ProjectivePermTensorFree
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ProjectiveResFreeRepOfInjective
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ShapiroIsIsoGroupHomologyZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.GroupHomologyDimensionShiftIsIso

open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab

namespace GlobalTheory.HomStab

/- English proof (translation)
Introduce `k G H X _ _ _ _ φ x hx hi hr ht`. Establish `key : ∀ (n : ℕ) (A : Rep k G), IsIso (groupHomology.map φ (ptMap φ x hx A) n)`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => exact fun A => GlobalTheory.T.shapiro_isIso_groupHomology_zero k G H X φ x hx hr ht A`.

Consider the case `succ n ih`. Introduce `A`. Take `⟨ι, K, i, e, h, hS⟩` from `GlobalTheory.T.exists_free_resolution_short_exact k G A`. Establish `hX` using `hS.map_of_exact (Rep.resFunctor (k := k) φ)`. Take `⟨hz, hY⟩` from `GlobalTheory.T.permCoef_preserves_shortExact k G X _ hS`.

Use `GlobalTheory.T.groupHomology_dimension_shift_isIso k G H φ _ _ hX hY (ptMap φ x hx K) (ptMap φ x hx (Rep.free k G ι)) (ptMap φ x hx A) ?_ ?_ n (GlobalTheory.T.projective_rep_groupHomology_pos_vanishes k H _ (GlobalTheory.T.projective_res_free_rep_of_injective k G H φ hi ι) n) (Gl …` and prove the remaining obligations. Introduce `a`. Conclude with `(Finsupp.mapRange_single (hf := map_zero (Rep.Hom.hom i))).symm`. Introduce `a`. Conclude with `(Finsupp.mapRange_single (hf := map_zero (Rep.Hom.hom e))).symm`.

Conclude with `⟨key, fun n => key n (Rep.trivial k G k)⟩`.
-/
theorem shapiro_pt : ∀ (k G H X : Type) [CommRing k] [Group G] [Group H] [MulAction G X] (φ : H →* G) (x : X) (hx : ∀ h, φ h • x = x), Function.Injective φ → φ.range = MulAction.stabilizer G x → (∀ y : X, ∃ g : G, g • x = y) → (∀ (n : ℕ) (A : Rep k G), IsIso (groupHomology.map φ (ptMap φ x hx A) n)) ∧ ∀ n : ℕ, IsIso (ptH k φ x hx n) := by
  intro k G H X _ _ _ _ φ x hx hi hr ht
  have key : ∀ (n : ℕ) (A : Rep k G), IsIso (groupHomology.map φ (ptMap φ x hx A) n) := by
    intro n
    induction n with
    | zero => exact fun A => GlobalTheory.T.shapiro_isIso_groupHomology_zero k G H X φ x hx hr ht A
    | succ n ih =>
      intro A
      obtain ⟨ι, K, i, e, h, hS⟩ := GlobalTheory.T.exists_free_resolution_short_exact k G A
      have hX := hS.map_of_exact (Rep.resFunctor (k := k) φ)
      obtain ⟨hz, hY⟩ := GlobalTheory.T.permCoef_preserves_shortExact k G X _ hS
      refine GlobalTheory.T.groupHomology_dimension_shift_isIso k G H φ _ _ hX hY (ptMap φ x hx K) (ptMap φ x hx (Rep.free k G ι))
        (ptMap φ x hx A) ?_ ?_ n (GlobalTheory.T.projective_rep_groupHomology_pos_vanishes k H _ (GlobalTheory.T.projective_res_free_rep_of_injective k G H φ hi ι) n)
        (GlobalTheory.T.projective_rep_groupHomology_pos_vanishes k G _ (GlobalTheory.T.projective_perm_tensor_free k G X ι) n) (ih K) (ih _)
      · intro a
        exact (Finsupp.mapRange_single (hf := map_zero (Rep.Hom.hom i))).symm
      · intro a
        exact (Finsupp.mapRange_single (hf := map_zero (Rep.Hom.hom e))).symm
  exact ⟨key, fun n => key n (Rep.trivial k G k)⟩

end GlobalTheory.HomStab

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab
/- English proof (translation)
Use `first`. Consider the case `exact @GlobalTheory.HomStab.shapiro_pt`.
-/
theorem _root_.GlobalTheory.T.shapiro_lemma_transitive_groupHomology : ∀ (k G H X : Type) [CommRing k] [Group G] [Group H] [MulAction G X] (φ : H →* G) (x : X) (hx : ∀ h, φ h • x = x), Function.Injective φ → φ.range = MulAction.stabilizer G x → (∀ y : X, ∃ g : G, g • x = y) → (∀ (n : ℕ) (A : Rep k G), IsIso (groupHomology.map φ (ptMap φ x hx A) n)) ∧ ∀ n : ℕ, IsIso (ptH k φ x hx n) := by
  first
  | exact @GlobalTheory.HomStab.shapiro_pt
end
