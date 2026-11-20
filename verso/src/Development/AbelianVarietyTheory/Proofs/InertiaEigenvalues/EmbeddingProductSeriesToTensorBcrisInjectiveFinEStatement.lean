import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EmbeddingProductSeriesToTensorBcrisInjectiveFinE
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BKReal.IBInj.iB_injective_finExt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FEmbeddingProductSeriesToTensorBcrisInjectiveFinE.lean&line=157#L157)
-/
theorem _root_.GlobalTheory.T.embeddingProductSeriesToTensorBcris_injective_finExt : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (LL : FinExt l) (t : Wq l a →ₐ[ℤ_[l]] ↥(OL LL)) (ϖ : PiSys l e), Function.Injective (ϖ.iB t ↥LL.1) := by
  first | exact @GlobalTheory.BKReal.IBInj.iB_injective_finExt | exact GlobalTheory.BKReal.IBInj.iB_injective_finExt | (intros; apply GlobalTheory.BKReal.IBInj.iB_injective_finExt <;> assumption)
