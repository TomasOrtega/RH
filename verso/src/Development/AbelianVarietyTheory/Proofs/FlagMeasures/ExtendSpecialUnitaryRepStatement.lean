import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExtendSpecialUnitaryRep
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsHaarMeasureSUJ
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SUExt.extends_to_U` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FExtendSpecialUnitaryRep.lean&line=79#L79)
-/
theorem _root_.GlobalTheory.T.extend_special_unitary_rep : ∀ (n : ℕ), 1 ≤ n → ∀ (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (m : ℤ) (π' : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (SUset ε) π' → (∀ z : ℂ, z ^ n = 1 → ∀ v, π' (z • (1 : Matrix (Fin n) (Fin n) ℂ)) v = z ^ m • v) → ∃ π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H), Ext ε m π' π ∧ IsURepOn (UJset ε) π := by
  first | exact @GlobalTheory.SUExt.extends_to_U | exact GlobalTheory.SUExt.extends_to_U | (intros; apply GlobalTheory.SUExt.extends_to_U <;> assumption)
