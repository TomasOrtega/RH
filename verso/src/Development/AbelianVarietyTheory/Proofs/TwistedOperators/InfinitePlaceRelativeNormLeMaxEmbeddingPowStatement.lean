import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfinitePlaceRelativeNormLeMaxEmbeddingPow
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VsizeNonneg
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix NumberField IsDedekindDomain
open scoped NNReal TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.NormInf.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FInfinitePlaceRelativeNormLeMaxEmbeddingPow.lean&line=21#L21)
-/
theorem _root_.GlobalTheory.T.infinitePlace_relativeNorm_le_maxEmbedding_pow : ∀ (D : D7) (w : InfinitePlace D.host.F) (y : D.host.E) (c : ℝ≥0), (∀ τ : GlobalTheory.AdelicU.EmbOver D.host.E w, ‖τ.1 y‖₊ ≤ c) → w (Algebra.norm D.host.F y) ≤ (c : ℝ) ^ Module.finrank D.host.F D.host.E := by
  first | exact @GlobalTheory.NormInf.main | exact GlobalTheory.NormInf.main | (intros; apply GlobalTheory.NormInf.main <;> assumption)
