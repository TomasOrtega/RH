import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullLatticeContainsScaledBasis
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPart
open NumberField ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.LieHt GlobalTheory.LieRead
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFullLatticeContainsScaledBasis.lean&line=50#L50)
-/
theorem _root_.GlobalTheory.T.full_lattice_contains_scaled_basis : ∀ (K : Type) [Field K] [NumberField K] (g : ℕ) (L : Submodule (𝓞 K) (Fin g → K)), Full L → ∃ D : ℕ, 0 < D ∧ ∀ k : Fin g, (D : K) • (Pi.single k 1 : Fin g → K) ∈ L := by
  first | exact @GlobalTheory.LatNat.exists_natMul_single_mem | exact GlobalTheory.LatNat.exists_natMul_single_mem | (intros; apply GlobalTheory.LatNat.exists_natMul_single_mem <;> assumption)
