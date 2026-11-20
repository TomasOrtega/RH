import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompatibleReductionSystemGivesThickeningTower
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FormalAlg.isSystem_tower` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCompatibleReductionSystemGivesThickeningTower.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.compatibleReductionSystem_gives_thickening_tower : ∀ (R : Type) [CommRing R] (I : Ideal R) (W : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of R)) (t : ℕ → W.IdealSheafData), IsSystem f I t → ∃ (q : ∀ e, (t e).subscheme ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) (β : ∀ e, (t e).subscheme ⟶ (t (e + 1)).subscheme), (∀ e, (t e).subschemeι ≫ f = q e ≫ thick R I e) ∧ (∀ e, β e ≫ (t (e + 1)).subschemeι = (t e).subschemeι) ∧ ∀ e, IsPullback (β e) (q e) (q (e + 1)) (thickTrans R I e) := by
  first | exact @GlobalTheory.FormalAlg.isSystem_tower | exact GlobalTheory.FormalAlg.isSystem_tower | (intros; apply GlobalTheory.FormalAlg.isSystem_tower <;> assumption)
