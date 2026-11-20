import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrobeniusAcrisDecompositionMuPower
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.MemLoc.phiA_mem_ainf_add` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FFrobeniusAcrisDecompositionMuPower.lean&line=148#L148)
-/
theorem _root_.GlobalTheory.T.frobenius_acris_decomposition_mu_power : ∀ (l : ℕ) [Fact l.Prime], ∀ e : Per.Fl l, IsEps e → ∀ w : Per.Acris l, (l : Per.Acris l) * w = algebraMap (Per.Ainf l) (Per.Acris l) (mu e) ^ (l - 1) → ∀ y : Per.Acris l, ∃ (a : Per.Ainf l) (z : Per.Acris l), phiA l y = algebraMap (Per.Ainf l) (Per.Acris l) a + w * z := by
  first | exact @GlobalTheory.MemLoc.phiA_mem_ainf_add | exact GlobalTheory.MemLoc.phiA_mem_ainf_add | (intros; apply GlobalTheory.MemLoc.phiA_mem_ainf_add <;> assumption)
