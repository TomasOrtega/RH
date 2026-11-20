import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FontaineXiPowSaturatedQuotientComplete
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FFontaineXiPowSaturatedQuotientComplete.lean&line=108#L108)
-/
theorem _root_.GlobalTheory.T.fontaineXi_pow_saturated_quotient_complete : ∀ (l : ℕ) [Fact l.Prime], ∀ e : Per.Fl l, IsEps e → ∀ n : ℕ, (∀ a : Per.Ainf l, xi e ^ n ∣ (l : Per.Ainf l) * a → xi e ^ n ∣ a) ∧ IsAdicComplete (Ideal.span {(l : Per.Ainf l ⧸ Ideal.span {xi e ^ n})}) (Per.Ainf l ⧸ Ideal.span {xi e ^ n}) := by
  first | exact @GlobalTheory.MemLoc.XiSat.xi_sat | exact GlobalTheory.MemLoc.XiSat.xi_sat | (intros; apply GlobalTheory.MemLoc.XiSat.xi_sat <;> assumption)
