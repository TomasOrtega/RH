import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HarishChandraSeriesCentralIdempotentNeZero
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsMirClass
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.GLm.eSerC_ne_zero` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FHarishChandraSeriesCentralIdempotentNeZero.lean&line=108#L108)
-/
theorem _root_.GlobalTheory.T.harishChandraSeriesCentralIdempotent_ne_zero : ∀ (g : ℕ) [Fact g.Prime] (L : LabelDatum g), Green → ∀ (n : ℕ) (f : (ZMod g)[X]), f.Monic → f.natDegree = n → f.coeff 0 ≠ 0 → eSerC L n f ≠ 0 := by
  first | exact @GlobalTheory.GLm.eSerC_ne_zero | exact GlobalTheory.GLm.eSerC_ne_zero | (intros; apply GlobalTheory.GLm.eSerC_ne_zero <;> assumption)
