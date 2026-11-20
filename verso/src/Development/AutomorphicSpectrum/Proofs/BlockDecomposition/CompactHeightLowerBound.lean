import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RatVInjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZeroMemBoxF
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CvecSurjective

set_option maxSynthPendingDepth 1

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov GlobalTheory.CompanionTheory.RedCov.Simple
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.CompanionTheory.RedCov.Simple

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hCM n J D hD`. Take `⟨-, -, h2, -⟩` from `hCM`. Use `haveI : Algebra.IsQuadraticExtension F E := ⟨h2⟩`. Take `⟨P, hP, h⟩` from `GroundTheory.Automorphic.Reduction.exists_adelicNorm_vecMul_le_mul (hD.image (Bridge.continuous_trG σ J).inv)`. Use `⟨P, hP, fun g hg v hv => ?_⟩` and prove the remaining obligations.

Establish `hc` using `Bridge.cvec_ne_zero (F := F) hv`. Establish `e : GroundTheory.Automorphic.Reduction.ratVec (Bridge.cvec F v) ᵥ* (Bridge.trG σ J g).1 ᵥ* ((Bridge.trG σ J g)⁻¹).1 = GroundTheory.Automorphic.Reduction.ratVec (Bridge.cvec F v)`. Rewrite using `[Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one]`. Establish `h3 : GroundTheory.Automorphic.Reduction.adelicNorm (GroundTheory.Automorphic.Reduction.ratVec (Bridge.cvec F v) ᵥ* (Bridge.trG σ J g).1 ᵥ* ((Bridge.trG σ J g)⁻¹).1) ≤ P * GroundTheory.Automorphic.Reduction.height (Bridge.trG σ J g) (Bridge.cvec F v)` using `h _ ⟨g, hg, rfl⟩ _ (GroundTheory.Automorphic.Reduction.hasFiniteContent_height (Bridge.trG σ J g) hc)`. Rewrite `h3` using `[e]`.

Rewrite using `[Bridge.hgt_eq]`. Conclude with `(GroundTheory.Automorphic.Reduction.one_le_adelicNorm_ratVec hc).trans h3`.
-/
theorem exists_one_le_mul_hgt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (D : Set (GAd σ J)), IsCompact D → ∃ P : ℝ, 0 < P ∧ ∀ g ∈ D, ∀ v : Fin n → E, v ≠ 0 → 1 ≤ P * hgt σ J g v := by
  intro F E _ _ _ _ _ σ hCM n J D hD
  obtain ⟨-, -, h2, -⟩ := hCM
  haveI : Algebra.IsQuadraticExtension F E := ⟨h2⟩
  obtain ⟨P, hP, h⟩ := GroundTheory.Automorphic.Reduction.exists_adelicNorm_vecMul_le_mul
    (hD.image (Bridge.continuous_trG σ J).inv)
  refine ⟨P, hP, fun g hg v hv => ?_⟩
  have hc := Bridge.cvec_ne_zero (F := F) hv
  have e : GroundTheory.Automorphic.Reduction.ratVec (Bridge.cvec F v) ᵥ*
        (Bridge.trG σ J g).1 ᵥ* ((Bridge.trG σ J g)⁻¹).1 =
      GroundTheory.Automorphic.Reduction.ratVec (Bridge.cvec F v) := by
    rw [Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one]
  have h3 : GroundTheory.Automorphic.Reduction.adelicNorm (GroundTheory.Automorphic.Reduction.ratVec (Bridge.cvec F v) ᵥ*
        (Bridge.trG σ J g).1 ᵥ* ((Bridge.trG σ J g)⁻¹).1) ≤
      P * GroundTheory.Automorphic.Reduction.height (Bridge.trG σ J g) (Bridge.cvec F v) :=
    h _ ⟨g, hg, rfl⟩ _ (GroundTheory.Automorphic.Reduction.hasFiniteContent_height (Bridge.trG σ J g) hc)
  rw [e] at h3
  rw [Bridge.hgt_eq]
  exact (GroundTheory.Automorphic.Reduction.one_le_adelicNorm_ratVec hc).trans h3

end GlobalTheory.CompanionTheory.RedCov.Simple

end
