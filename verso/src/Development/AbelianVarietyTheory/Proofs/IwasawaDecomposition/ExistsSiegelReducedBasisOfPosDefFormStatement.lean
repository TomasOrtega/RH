import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSiegelReducedBasisOfPosDefForm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegelZeroFront
open Matrix GlobalTheory.RedTh NumberField GlobalTheory.PolFan ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.RedTh.RedBasis.exists_siegel_basis` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsSiegelReducedBasisOfPosDefForm.lean&line=42#L42)
-/
theorem _root_.GlobalTheory.T.exists_siegelReduced_basis_of_posDef_form : ∀ (n : ℕ) (Y : Type) [AddCommGroup Y] (b₀ : Module.Basis (Fin n) ℤ Y) (B : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ), (∀ y z, B y z = B z y) → IsPosDef B → ∃ (b : Module.Basis (Fin n) ℤ Y) (d : Fin n → ℝ) (u : Matrix (Fin n) (Fin n) ℝ), IsSiegel d u ∧ (∀ i, 0 < d i) ∧ ∀ i j, B (b i) (b j) = gram d u i j := by
  first | exact @GlobalTheory.RedTh.RedBasis.exists_siegel_basis | exact GlobalTheory.RedTh.RedBasis.exists_siegel_basis | (intros; apply GlobalTheory.RedTh.RedBasis.exists_siegel_basis <;> assumption)
