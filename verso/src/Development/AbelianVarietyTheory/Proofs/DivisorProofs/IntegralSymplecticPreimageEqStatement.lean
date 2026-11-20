import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralSymplecticPreimageEq
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtMapApply
open Matrix MeasureTheory Set GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm
open scoped ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIntegralSymplecticPreimageEq.lean&line=43#L43)
-/
theorem _root_.GlobalTheory.T.integral_symplectic_preimage_eq : ∀ {g : ℕ} {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (γ : Sp g) (D : Set (Fl g)) (φ : Fl g → F), ∫ x in (fun x : Fl g => x ᵥ* (γ⁻¹).mat) ⁻¹' D, φ (x ᵥ* (γ⁻¹).mat) = ∫ x in D, φ x := by
  first | exact @GlobalTheory.SympChange.setIntegral_vecMul_inv | exact GlobalTheory.SympChange.setIntegral_vecMul_inv | (intros; apply GlobalTheory.SympChange.setIntegral_vecMul_inv <;> assumption)
