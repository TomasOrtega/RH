import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixUnitOpUpperBlockLeviEqZero
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlkEquivInl
open NumberField MeasureTheory GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LeviGA.Eop_upper_blkGL_eq_zero` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FMatrixUnitOpUpperBlockLeviEqZero.lean&line=82#L82)
-/
theorem _root_.GlobalTheory.T.matrixUnitOp_upperBlock_levi_eq_zero : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a r : ℕ) (hr : r ≤ a) (f : Sm E a), (∀ (x : BlockIx a r → Ad E) (g : GA E a), f.1 (unip x * g) = f.1 g) → ∀ (τ : E →+* ℂ) (i j : Fin a), (i : ℕ) < r → r ≤ (j : ℕ) → ∀ (m₁ : GA E r) (m₂ : GA E (a - r)), (Eop τ i j f).1 (GlobalTheory.LeviGA.blkGL hr (m₁, m₂)) = 0 := by
  first | exact @GlobalTheory.LeviGA.Eop_upper_blkGL_eq_zero | exact GlobalTheory.LeviGA.Eop_upper_blkGL_eq_zero | (intros; apply GlobalTheory.LeviGA.Eop_upper_blkGL_eq_zero <;> assumption)
