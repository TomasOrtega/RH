import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZeroTensorOfDegreeZeroComplexes
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsZeroTensorOfDegreeZeroComplexes.lean&line=47#L47)
-/
theorem _root_.GlobalTheory.T.isZero_tensor_of_degree_zero_complexes : ∀ (R : Type) [CommRing R] {I J K : Cx R} (τ : Pair I J K), τ.IsTensor → (∀ s : ℤ, s ≠ 0 → IsZero (I.X s)) → (∀ t : ℤ, t ≠ 0 → IsZero (J.X t)) → ∀ w : ℤ, w ≠ 0 → IsZero (K.X w) := by
  first | exact @GlobalTheory.EtC.isZero_tensor_of_deg_zero | exact GlobalTheory.EtC.isZero_tensor_of_deg_zero | (intros; apply GlobalTheory.EtC.isZero_tensor_of_deg_zero <;> assumption)
