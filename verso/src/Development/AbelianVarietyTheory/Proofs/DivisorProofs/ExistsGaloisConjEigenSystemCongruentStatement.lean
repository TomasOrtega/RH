import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisConjEigenSystemCongruent
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
open NumberField IsDedekindDomain Formalism.L2.DIV GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsGaloisConjEigenSystemCongruent.lean&line=32#L32)
-/
theorem _root_.GlobalTheory.T.exists_galoisConj_eigenSystem_congruent : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (F : Frame l ι N) (lam : ι → ℕ → ℕ), F.Ok → ∀ (θ θ0 : F.I → PadicAlgCl l) (m : Ideal F.T), F.IsEig lam θ → F.Over θ m → F.Over θ0 m → ∃ θ', F.IsEig lam θ' ∧ (∀ i, ‖θ' i‖ ≤ 1) ∧ ∀ i, ‖θ' i - θ0 i‖ < 1 := by
  first | exact @GlobalTheory.ExpFrame.Conj.exists_eig_congr | exact GlobalTheory.ExpFrame.Conj.exists_eig_congr | (intros; apply GlobalTheory.ExpFrame.Conj.exists_eig_congr <;> assumption)
