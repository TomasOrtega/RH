import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealLineIsLineOfPlace
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixMulVecBasis
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FRealLineIsLineOfPlace.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.real_line_is_line_of_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (τ : ∀ w : InfinitePlace F, EmbOver E w) (γ : ℝ → GAd σ J), IsRealLine σ J γ →
      ∃ (w : InfinitePlace F) (Z : Matrix (Fin n) (Fin n) ℂ), IsLineOf σ J (τ w) Z γ := by
  first | exact @GlobalTheory.LeviHC.isLineOf_of_isRealLine | exact GlobalTheory.LeviHC.isLineOf_of_isRealLine | (intros; apply GlobalTheory.LeviHC.isLineOf_of_isRealLine <;> assumption)
