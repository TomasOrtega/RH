import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FontaineThetaEqZeroIffFontaineXiElementDvd
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FFontaineThetaEqZeroIffFontaineXiElementDvd.lean&line=25#L25)
-/
theorem _root_.GlobalTheory.T.fontaineTheta_eq_zero_iff_fontaineXiElement_dvd : ∀ (l : ℕ) [Fact l.Prime], ∀ e : Per.Fl l, IsEps e → ∀ a : Per.Ainf l, Per.θ l a = 0 ↔ xi e ∣ a := by
  first | exact @GlobalTheory.MemLoc.theta_eq_zero_iff_xi_dvd | exact GlobalTheory.MemLoc.theta_eq_zero_iff_xi_dvd | (intros; apply GlobalTheory.MemLoc.theta_eq_zero_iff_xi_dvd <;> assumption)
