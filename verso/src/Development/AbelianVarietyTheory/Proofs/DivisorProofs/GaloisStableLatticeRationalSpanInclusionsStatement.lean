import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisStableLatticeRationalSpanInclusions
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentIdealSmulMemSpanRational
open NumberField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.span_rational_le_span_and_different_smul_le` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FGaloisStableLatticeRationalSpanInclusions.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.galois_stable_lattice_rational_span_inclusions : ∀ (K K' L : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] [Field L] [NumberField L] [Algebra K K'] [IsGalois K K'] [Algebra K' L] (n : ℕ) (M : Submodule (𝓞 K') (Fin n → K')), (∀ (s : K' ≃ₐ[K] K'), ∀ x ∈ M, (fun i => s (x i)) ∈ M) → Submodule.span (𝓞 L) ((fun (x : Fin n → K) i => algebraMap K' L (algebraMap K K' (x i))) '' {x | (fun i => algebraMap K K' (x i)) ∈ M}) ≤ Submodule.span (𝓞 L) ((fun x i => algebraMap K' L (x i)) '' (M : Set (Fin n → K'))) ∧ (differentIdeal ℤ (𝓞 K')).map (algebraMap (𝓞 K') (𝓞 L)) • Submodule.span (𝓞 L) ((fun x i => algebraMap K' L (x i)) '' (M : Set (Fin n → K'))) ≤ Submodule.span (𝓞 L) ((fun (x : Fin n → K) i => algebraMap K' L (algebraMap K K' (x i))) '' {x | (fun i => algebraMap K K' (x i)) ∈ M}) := by
  first | exact @GlobalTheory.span_rational_le_span_and_different_smul_le | exact GlobalTheory.span_rational_le_span_and_different_smul_le | (intros; apply GlobalTheory.span_rational_le_span_and_different_smul_le <;> assumption)
