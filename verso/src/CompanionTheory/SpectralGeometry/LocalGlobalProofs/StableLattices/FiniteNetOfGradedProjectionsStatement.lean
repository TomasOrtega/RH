import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FiniteNetOfGradedProjections
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HsConjTranspose
open Matrix
open CompanionTheory.RgExh.Dec CompanionTheory.RgExh.Dec.L ReciprocityTheory.ChartRestriction.DS GlobalTheory.CompanionTheory.PSubFlag GlobalTheory.CompanionTheory.UGeo
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.UGeo.GradNet.exists_net` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FStableLattices%2FFiniteNetOfGradedProjections.lean&line=46#L46)
-/
theorem _root_.GlobalTheory.T.finite_net_of_graded_projections : ∀ (n : ℕ) (ε : Fin n → Bool), ∃ (m : ℕ) (A : Fin m → Matrix (Fin n) (Fin n) ℂ), (∀ j, IsGrad ε (A j)) ∧ ∀ A' : Matrix (Fin n) (Fin n) ℂ, IsGrad ε A' → ∃ j, Formalism.REAL.hs (Pm (A j) - Pm A') ≤ 1 / 4 ∧ Formalism.REAL.hs (Pp (A j) - Pp A') ≤ 1 / 4 := by
  first | exact @GlobalTheory.CompanionTheory.UGeo.GradNet.exists_net | exact GlobalTheory.CompanionTheory.UGeo.GradNet.exists_net | (intros; apply GlobalTheory.CompanionTheory.UGeo.GradNet.exists_net <;> assumption)
