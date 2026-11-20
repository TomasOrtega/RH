import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexConjUniformizerPowerDiagonalGLReindex
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BorelParam
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ReindexTorus.relIndex_conj_torusElt_reindex` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FRelIndexConjUniformizerPowerDiagonalGLReindex.lean&line=33#L33)
-/
theorem _root_.GlobalTheory.T.relIndex_conj_uniformizerPowerDiagonalGL_reindex : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ϖ : kˣ)
    (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (σ : n ≃ n') (e : n → ℤ),
    ((KO k n').map (MulAut.conj (torusElt k n' ϖ (e ∘ σ.symm))).toMonoidHom).relIndex (KO k n') =
      ((KO k n).map (MulAut.conj (torusElt k n ϖ e)).toMonoidHom).relIndex (KO k n) := by
  first | exact @GlobalTheory.ReindexTorus.relIndex_conj_torusElt_reindex | exact GlobalTheory.ReindexTorus.relIndex_conj_torusElt_reindex | (intros; apply GlobalTheory.ReindexTorus.relIndex_conj_torusElt_reindex <;> assumption)
