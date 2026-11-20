import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsFiniteCosetsAdelicUnitaryBoundedDenominato
import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.DenomBound
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FHeightProofs%2FExistsFiniteCosetsAdelicUnitaryBoundedDenominato.lean&line=108#L108)
-/
theorem _root_.GlobalTheory.T.exists_finite_cosets_adelicUnitary_bounded_denominator : ∀ (D : D7) (V : HSp D) (U : Subgroup (GA D V)), IsOpen (U : Set (GA D V)) → ∀ d : ℕ, 0 < d → ∃ S : Finset (GA D V), ∀ k ∈ GfC V, BddDen V d k → ∃ x ∈ S, x⁻¹ * k ∈ U ∧ x⁻¹ * k ∈ GfC V := by
  first | exact @GlobalTheory.SmoothForms.Cover.exists_finset_cover | exact GlobalTheory.SmoothForms.Cover.exists_finset_cover | (intros; apply GlobalTheory.SmoothForms.Cover.exists_finset_cover <;> assumption)
