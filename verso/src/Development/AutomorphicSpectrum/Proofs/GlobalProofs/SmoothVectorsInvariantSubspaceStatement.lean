import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SmoothVectorsInvariantSubspace
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsSmoothVec
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGlobalProofs%2FSmoothVectorsInvariantSubspace.lean&line=22#L22)
-/
theorem _root_.GlobalTheory.T.smooth_vectors_invariant_subspace : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π), (∀ u v : H, IsSmoothVec G π u → IsSmoothVec G π v → IsSmoothVec G π (u + v)) ∧ (∀ (c : ℂ) (v : H), IsSmoothVec G π v → IsSmoothVec G π (c • v)) ∧ (∀ g ∈ G, ∀ v : H, IsSmoothVec G π v → IsSmoothVec G π (π g v)) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.HCA.smooth_closed | exact GlobalTheory.CompanionTheory.Hypotheses₂.HCA.smooth_closed | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.HCA.smooth_closed <;> assumption)
