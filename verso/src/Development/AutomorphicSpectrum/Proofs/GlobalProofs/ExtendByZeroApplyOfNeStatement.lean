import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExtendByZeroApplyOfNe
import Mathlib
import Formalism.RealPlaceAnalysis.SmoothOnGVIff
import Formalism.FormalDegreeBessel.StatementG
open Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGlobalProofs%2FExtendByZeroApplyOfNe.lean&line=296#L296)
-/
theorem _root_.GlobalTheory.T.unitary_element_prescribed_blocks : ∀ {n m : ℕ} (ε : Fin n → Bool) (x y : Matrix (Fin n) (Fin m) ℂ) (A : Set (Fin m)),
    xᴴ * Formalism.REAL.Jm ε * x = 0 → xᴴ * Formalism.REAL.Jm ε * y = 1 →
    ∃ (u : Matrix (Fin m) (Fin n) ℂ) (w : Matrix (Fin n) (Fin m) ℂ), (∀ i v, i ∉ A → u i v = 0) ∧
      (∀ v i, i ∉ A → w v i = 0) ∧ (∀ i j, j ∈ A → (u * x) i j = 0) ∧
      1 + x * u + w * xᴴ * Formalism.REAL.Jm ε ∈ Formalism.QuantumDeterminants.UH (Formalism.REAL.Jm ε) ∧
      ∀ v ∈ Submodule.span ℂ (Set.range (fun i : A => (1 + x * u + w * xᴴ * Formalism.REAL.Jm ε) *ᵥ fun j => x j i) ∪
          Set.range (fun i : A => (1 + x * u + w * xᴴ * Formalism.REAL.Jm ε) *ᵥ fun j => y j i)),
        Formalism.REAL.Jm ε *ᵥ v ∈ Submodule.span ℂ (Set.range (fun i : A => (1 + x * u + w * xᴴ * Formalism.REAL.Jm ε) *ᵥ fun j => x j i) ∪
          Set.range (fun i : A => (1 + x * u + w * xᴴ * Formalism.REAL.Jm ε) *ᵥ fun j => y j i)) := by
  first | exact @GlobalTheory.CompanionTheory.EichlerTransf.eichler_transformation | exact GlobalTheory.CompanionTheory.EichlerTransf.eichler_transformation | (intros; apply GlobalTheory.CompanionTheory.EichlerTransf.eichler_transformation <;> assumption)
