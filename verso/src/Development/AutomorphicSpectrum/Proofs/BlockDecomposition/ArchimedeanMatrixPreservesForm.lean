import Mathlib
import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StabUpTo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeisenbergCoords
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.CFin
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.CompanionTheory.CFin

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hcm n J g w τ`. Establish `h` using `GlobalTheory.HeisCoords.archMat_unitary hcm τ (projArch σ J w g)`. Establish `e : cT (starRingEnd ℂ) (archMat σ J τ (projArch σ J w g)) = (archMat σ J τ (projArch σ J w g))ᴴ`. Use extensionality with `i j`. Simplify using `[cT, Matrix.conjTranspose_apply]`.

Rewrite using `[e]`. Conclude with `h`.
-/
theorem archMat_projArch_unitary : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (g : GAd σ J) (w : InfinitePlace F) (τ : EmbOver E w), cT (starRingEnd ℂ) (archMat σ J τ (projArch σ J w g)) * J.map τ.1 * archMat σ J τ (projArch σ J w g) = J.map τ.1 := by
  intro F E _ _ _ _ _ σ hcm n J g w τ
  have h := GlobalTheory.HeisCoords.archMat_unitary hcm τ (projArch σ J w g)
  have e : cT (starRingEnd ℂ) (archMat σ J τ (projArch σ J w g)) = (archMat σ J τ (projArch σ J w g))ᴴ := by
    ext i j
    simp [cT, Matrix.conjTranspose_apply]
  rw [e]
  exact h

end GlobalTheory.CompanionTheory.CFin
