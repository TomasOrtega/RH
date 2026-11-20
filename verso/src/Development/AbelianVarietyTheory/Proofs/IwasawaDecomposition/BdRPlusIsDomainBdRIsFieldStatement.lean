import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRPlusIsDomainBdRIsField
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FBdRPlusIsDomainBdRIsField.lean&line=124#L124)
-/
theorem _root_.GlobalTheory.T.bdRPlus_isDomain_bdR_isField : ∀ (l : ℕ) [Fact l.Prime], IsDomain (Per.BdRp l) ∧ Function.Injective (algebraMap (Per.BdRp l) (Per.BdR l)) ∧ IsField (Per.BdR l) ∧ ∀ e : Per.Fl l, IsEps e → ∀ x : Per.BdR l, ∃ (n : ℕ) (y : Per.BdRp l), x * algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (xi e)) ^ n = algebraMap (Per.BdRp l) (Per.BdR l) y := by
  first | exact @GlobalTheory.MemLoc.BdRField.bdR_isField | exact GlobalTheory.MemLoc.BdRField.bdR_isField | (intros; apply GlobalTheory.MemLoc.BdRField.bdR_isField <;> assumption)
