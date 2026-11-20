import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowInclRSmulMem
import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWeakTopologyWittTiltTensor
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZlTowerGen
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WeakClosed
open scoped Topology PowerSeries.WithPiTopology
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.WeakClosed.exists_pow_inclR_smul_mem` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FExistsPowInclRSmulMem.lean&line=76#L76)
-/
theorem _root_.GlobalTheory.T.exists_pow_inclR_smul_mem' : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P) (s : ℕ) {K LL : FinExt l} (T : Lt K LL) {d : ℕ} (b : LatB T d) (y : TW (RW LL) T), letI := twTop T b; ∀ U ∈ 𝓝 (0 : TW (RW LL) T), ∃ k : ℕ, ∀ z : RA LL, inclR LL ((((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (WittVector.teichmuller l (AI.εroot s) - 1)) : RA LL) ^ k * z) • y ∈ U := by
  first | exact @GlobalTheory.WeakClosed.exists_pow_inclR_smul_mem | exact GlobalTheory.WeakClosed.exists_pow_inclR_smul_mem | (intros; apply GlobalTheory.WeakClosed.exists_pow_inclR_smul_mem <;> assumption)
