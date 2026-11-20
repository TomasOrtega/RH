import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisMembershipSpanIff
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.MemLoc.mem_Acris0_iff_span` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FAcrisMembershipSpanIff.lean&line=63#L63)
-/
theorem _root_.GlobalTheory.T.acris_membership_span_iff : ∀ (l : ℕ) [Fact l.Prime], ∀ e : Per.Fl l, IsEps e → ∀ s : Per.AinfP l, s ∈ Per.Acris0 l ↔ s ∈ Submodule.span (Per.Ainf l) {y : Per.AinfP l | ∃ n : ℕ, ((n.factorial : ℕ) : Per.AinfP l) * y = algebraMap (Per.Ainf l) (Per.AinfP l) (xi e) ^ n} := by
  first | exact @GlobalTheory.MemLoc.mem_Acris0_iff_span | exact GlobalTheory.MemLoc.mem_Acris0_iff_span | (intros; apply GlobalTheory.MemLoc.mem_Acris0_iff_span <;> assumption)
