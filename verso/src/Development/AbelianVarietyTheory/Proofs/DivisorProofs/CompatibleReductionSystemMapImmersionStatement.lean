import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompatibleReductionSystemMapImmersion
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FormalAlg.mapSystem` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCompatibleReductionSystemMapImmersion.lean&line=30#L30)
-/
theorem _root_.GlobalTheory.T.compatibleReductionSystem_map_immersion : ∀ (R : Type) [CommRing R] (I : Ideal R) (W W' : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of R)) (π : W' ⟶ W), IsSeparated f → IsImmersion π → ∀ t : ℕ → W'.IdealSheafData, IsSystem (π ≫ f) I t → (∀ e, IsProper ((t e).subschemeι ≫ π ≫ f)) → IsSystem f I (fun e => (t e).map π) ∧ (∀ e, IsProper (((t e).map π).subschemeι ≫ f)) ∧ ∀ e, ((t e).map π).comap π = t e := by
  first | exact @GlobalTheory.FormalAlg.mapSystem | exact GlobalTheory.FormalAlg.mapSystem | (intros; apply GlobalTheory.FormalAlg.mapSystem <;> assumption)
