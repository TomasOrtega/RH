import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInjectiveBcrisToBdR
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsInjectiveBcrisToBdR.lean&line=58#L58)
-/
theorem _root_.GlobalTheory.T.exists_injective_bcris_to_bdR : ∀ (l : ℕ) [Fact l.Prime], ∀ j : Per.Acris l →+* Per.BdRp l, IsCrisP j → ∃ ι : Per.Bcris l →+* Per.BdR l, (∀ x : Per.Acris l, ι (algebraMap (Per.Acris l) (Per.Bcris l) x) = algebraMap (Per.BdRp l) (Per.BdR l) (j x)) ∧ Function.Injective ι := by
  first | exact @GlobalTheory.MemLoc.exists_iota_cris_dR | exact GlobalTheory.MemLoc.exists_iota_cris_dR | (intros; apply GlobalTheory.MemLoc.exists_iota_cris_dR <;> assumption)
