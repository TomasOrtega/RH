import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SmoothVecHeadOfDerivativeFamily
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothVectorsModerateGrowthSmoothFrechetRep
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FamSmooth.famSmooth` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FSmoothVecHeadOfDerivativeFamily.lean&line=173#L173)
-/
theorem _root_.GlobalTheory.T.smoothVec_head_of_derivative_family : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ → ∀ v ∈ GlobalTheory.TypeSum.Fam ε σ, Formalism.L2.Theta.SmoothVec (GlobalTheory.SmoothGlob.lieSet ε) σ (v []) := by
  first | exact @GlobalTheory.FamSmooth.famSmooth | exact GlobalTheory.FamSmooth.famSmooth | (intros; apply GlobalTheory.FamSmooth.famSmooth <;> assumption)
