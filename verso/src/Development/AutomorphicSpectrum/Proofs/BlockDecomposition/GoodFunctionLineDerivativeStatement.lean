import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GoodFunctionLineDerivative
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GoodConstOfAniso
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal Topology

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FGoodFunctionLineDerivative.lean&line=90#L90)
-/
theorem _root_.GlobalTheory.T.good_function_line_derivative : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (U : Subgroup (GAd σ J)) (A : ℕ) (φ : GAd σ J → ℂ) (γ : ℝ → GAd σ J), Good σ J U A φ → IsRealLine σ J γ → Good σ J U A (lineDer γ φ) := by
  first | exact @GlobalTheory.CompanionTheory.RapidDecay.good_lineDer | exact GlobalTheory.CompanionTheory.RapidDecay.good_lineDer | (intros; apply GlobalTheory.CompanionTheory.RapidDecay.good_lineDer <;> assumption)
