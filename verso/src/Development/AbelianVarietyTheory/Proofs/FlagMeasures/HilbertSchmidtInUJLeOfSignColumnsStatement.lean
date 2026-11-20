import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HilbertSchmidtInUJLeOfSignColumns
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Formalism.RealPlaceAnalysis.FinalF
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FHilbertSchmidtInUJLeOfSignColumns.lean&line=41#L41)
-/
theorem _root_.GlobalTheory.T.hilbertSchmidt_inUJ_le_of_sign_columns : ∀ (n : ℕ) (ε : Fin n → Bool) (s : Bool) (h : Matrix (Fin n) (Fin n) ℂ), inUJ ε h → hs h ≤ n + 4 * ∑ i, ∑ j ∈ univ.filter (fun j => ε j = s), ‖h i j‖ ^ 2 := by
  first | exact @GlobalTheory.hs_le_of_cols | exact GlobalTheory.hs_le_of_cols | (intros; apply GlobalTheory.hs_le_of_cols <;> assumption)
