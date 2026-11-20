import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VerticalH2SurjectiveUniverses
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PullbackBijectiveDegreesOneTwo
open CategoryTheory GlobalTheory.CxCoh
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FVerticalH2SurjectiveUniverses.lean&line=120#L120)
-/
theorem _root_.GlobalTheory.T.vertical_h2_surjective_universes : VertHas.{1,1} (fun m ↦ Function.Surjective m.h2) ∧ VertHas.{1,0} (fun m ↦ Function.Surjective m.h2) ∧ VertHas.{0,0} (fun m ↦ Function.Surjective m.h2) := by
  first | exact @GlobalTheory.CxCoh.VertSurjTwo.inst | exact GlobalTheory.CxCoh.VertSurjTwo.inst | (intros; apply GlobalTheory.CxCoh.VertSurjTwo.inst <;> assumption)
