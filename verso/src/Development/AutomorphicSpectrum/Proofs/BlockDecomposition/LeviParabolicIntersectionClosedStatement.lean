import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviParabolicIntersectionClosed
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipMinSubsetMinParOne
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov GlobalTheory.CompanionTheory.ParCocompact
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.ParCocompact.exists_leviOne_subgroup` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FLeviParabolicIntersectionClosed.lean&line=130#L130)
-/
theorem _root_.GlobalTheory.T.levi_parabolic_intersection_closed : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∃ L : Subgroup (GAd σ J), (L : Set (GAd σ J)) = leviMin σ J X Y ∩ minParOne σ J X ∧ IsClosed (L : Set (GAd σ J)) := by
  first | exact @GlobalTheory.CompanionTheory.ParCocompact.exists_leviOne_subgroup | exact GlobalTheory.CompanionTheory.ParCocompact.exists_leviOne_subgroup | (intros; apply GlobalTheory.CompanionTheory.ParCocompact.exists_leviOne_subgroup <;> assumption)
