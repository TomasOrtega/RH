import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCyclotomicKernelFixedBasisWittTensorLattic
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConvZero
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FExistsCyclotomicKernelFixedBasisWittTensorLattic.lean&line=508#L508)
-/
theorem _root_.GlobalTheory.T.exists_cyclotomicKernelFixedBasis_wittTensorLattice : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), FaithH AI → ∀ (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), ∃ e : Module.Basis (Fin (Module.finrank ↥(OL LL) ↥T.L.T)) (RW LL) (TW (RW LL) T), FixBasis AI T e := by
  first | exact @GlobalTheory.HWL.FixedBasis.main | exact GlobalTheory.HWL.FixedBasis.main | (intros; apply GlobalTheory.HWL.FixedBasis.main <;> assumption)
