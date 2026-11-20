import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ParamsEx
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ActOfMemGfC
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RaisingLoweringOperators
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TranslateMemCoefLatFn
import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

namespace GlobalTheory.LieSpanConj

/- English proof (translation)
Establish `hu : IsUnit H.det` using `isUnit_iff_ne_zero.2 hd`. Use `set Zb : Matrix (Fin n) (Fin n) ℂ := -(H⁻¹ * Zᴴ * H) with hZb`. Establish `hA : Zbᴴ * H = -(H * Z)`. Rewrite using `[hZb, conjTranspose_neg, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_nonsing_inv, hH, neg_mul, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]`. Establish `hB : H * Zb = -(Zᴴ * H)`.

Rewrite using `[hZb, Matrix.mul_neg, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]`. Use `⟨(1 / 2 : ℂ) • (Z + Zb), (-(Complex.I / 2)) • (Z - Zb), ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[conjTranspose_smul, conjTranspose_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, hA, hB]`. Establish `: star (1 / 2 : ℂ) = 1 / 2` using `by simp`. Rewrite using `[this, ← smul_add]`.

Rewrite using `[show Zᴴ * H + -(H * Z) + (H * Z + -(Zᴴ * H)) = 0 by abel, smul_zero]`. Rewrite using `[conjTranspose_smul, conjTranspose_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, hA, hB]`. Establish `: star (-(Complex.I / 2)) = Complex.I / 2`. Simplify using `[Complex.conj_I]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this]`. Rewrite using `[show Zᴴ * H - -(H * Z) = H * Z + Zᴴ * H by abel, show H * Z - -(Zᴴ * H) = H * Z + Zᴴ * H by abel]`. Rewrite using `[← add_smul]`. Simplify using the standard rewrite rules. Rewrite using `[smul_smul, smul_add, smul_sub]`.

Establish `h1 : Complex.I * -(Complex.I / 2) = 1 / 2`. Use `Complex.I_sq` as an intermediate fact. Take the linear combination `(-(1 / 2 : ℂ)) * this`. Rewrite using `[h1]`. Use extensionality with `i j`.

Simplify using `only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_decomp {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ = H) (hd : H.det ≠ 0)
    (Z : Matrix (Fin n) (Fin n) ℂ) :
    ∃ X Y : Matrix (Fin n) (Fin n) ℂ, Xᴴ * H + H * X = 0 ∧ Yᴴ * H + H * Y = 0 ∧
      Z = X + Complex.I • Y := by
  have hu : IsUnit H.det := isUnit_iff_ne_zero.2 hd
  set Zb : Matrix (Fin n) (Fin n) ℂ := -(H⁻¹ * Zᴴ * H) with hZb
  have hA : Zbᴴ * H = -(H * Z) := by
    rw [hZb, conjTranspose_neg, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
      conjTranspose_nonsing_inv, hH, neg_mul, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu,
      Matrix.mul_one]
  have hB : H * Zb = -(Zᴴ * H) := by
    rw [hZb, Matrix.mul_neg, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]
  refine ⟨(1 / 2 : ℂ) • (Z + Zb), (-(Complex.I / 2)) • (Z - Zb), ?_, ?_, ?_⟩
  · rw [conjTranspose_smul, conjTranspose_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add,
      hA, hB]
    have : star (1 / 2 : ℂ) = 1 / 2 := by simp
    rw [this, ← smul_add]
    rw [show Zᴴ * H + -(H * Z) + (H * Z + -(Zᴴ * H)) = 0 by abel, smul_zero]
  · rw [conjTranspose_smul, conjTranspose_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub,
      hA, hB]
    have : star (-(Complex.I / 2)) = Complex.I / 2 := by
      simp [Complex.conj_I]
      ring
    rw [this]
    rw [show Zᴴ * H - -(H * Z) = H * Z + Zᴴ * H by abel, show H * Z - -(Zᴴ * H) = H * Z + Zᴴ * H by abel]
    rw [← add_smul]
    simp
  · rw [smul_smul, smul_add, smul_sub]
    have h1 : Complex.I * -(Complex.I / 2) = 1 / 2 := by
      have := Complex.I_sq
      linear_combination (-(1 / 2 : ℂ)) * this
    rw [h1]
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    ring

/- English proof (translation)
Introduce `D V τ Fm hF`. Establish `hFd : IsUnit Fm.det` using `(Matrix.isUnit_iff_isUnit_det Fm).1 hF`. Establish `hd : (gramAt D V τ).det ≠ 0`. Rewrite using `[gramAt, ← RingHom.mapMatrix_apply, ← RingHom.map_det]`. Conclude with `(map_ne_zero _).2 (Formalism.L2.Theta.gram_det_ne V)`.

Rewrite using `[eq_top_iff]`. Introduce `Z' _`. Take `⟨X, Y, hX, hY, hZ⟩` from `GlobalTheory.LieSpanConj.exists_decomp (gramAt D V τ) (SmoothForms.RealPts.gramAt_herm V τ) hd (Fm⁻¹ * Z' * Fm)`. Establish `hmX : Fm * X * Fm⁻¹ ∈ Submodule.span ℂ {Z : Matrix (Fin V.rank) (Fin V.rank) ℂ | ∃ Y ∈ lieAt V τ, Z = Fm * Y * Fm⁻¹}` using `Submodule.subset_span ⟨X, hX, rfl⟩`. Establish `hmY : Fm * Y * Fm⁻¹ ∈ Submodule.span ℂ {Z : Matrix (Fin V.rank) (Fin V.rank) ℂ | ∃ Y ∈ lieAt V τ, Z = Fm * Y * Fm⁻¹}` using `Submodule.subset_span ⟨Y, hY, rfl⟩`.

Establish `hZ' : Z' = Fm * X * Fm⁻¹ + Complex.I • (Fm * Y * Fm⁻¹)`. Establish `: Z' = Fm * (Fm⁻¹ * Z' * Fm) * Fm⁻¹`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hFd, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hFd, Matrix.mul_one]`. Rewrite using `[this, hZ, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]`. Rewrite using `[hZ']`.

Conclude with `Submodule.add_mem _ hmX (Submodule.smul_mem _ _ hmY)`.
-/
theorem span_conj_lieAt_eq_top : ∀ (D : D7) (V : HSp D) (τ : D.what₂.Tau) (Fm : Matrix (Fin V.rank) (Fin V.rank) ℂ),
    IsUnit Fm → Submodule.span ℂ {Z : Matrix (Fin V.rank) (Fin V.rank) ℂ | ∃ Y ∈ lieAt V τ, Z = Fm * Y * Fm⁻¹} = ⊤ := by
  intro D V τ Fm hF
  have hFd : IsUnit Fm.det := (Matrix.isUnit_iff_isUnit_det Fm).1 hF
  have hd : (gramAt D V τ).det ≠ 0 := by
    rw [gramAt, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero _).2 (Formalism.L2.Theta.gram_det_ne V)
  rw [eq_top_iff]
  intro Z' _
  obtain ⟨X, Y, hX, hY, hZ⟩ :=
    GlobalTheory.LieSpanConj.exists_decomp (gramAt D V τ) (SmoothForms.RealPts.gramAt_herm V τ) hd (Fm⁻¹ * Z' * Fm)
  have hmX : Fm * X * Fm⁻¹ ∈ Submodule.span ℂ {Z : Matrix (Fin V.rank) (Fin V.rank) ℂ | ∃ Y ∈ lieAt V τ, Z = Fm * Y * Fm⁻¹} :=
    Submodule.subset_span ⟨X, hX, rfl⟩
  have hmY : Fm * Y * Fm⁻¹ ∈ Submodule.span ℂ {Z : Matrix (Fin V.rank) (Fin V.rank) ℂ | ∃ Y ∈ lieAt V τ, Z = Fm * Y * Fm⁻¹} :=
    Submodule.subset_span ⟨Y, hY, rfl⟩
  have hZ' : Z' = Fm * X * Fm⁻¹ + Complex.I • (Fm * Y * Fm⁻¹) := by
    have : Z' = Fm * (Fm⁻¹ * Z' * Fm) * Fm⁻¹ := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hFd, Matrix.one_mul, Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ hFd, Matrix.mul_one]
    rw [this, hZ, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
  rw [hZ']
  exact Submodule.add_mem _ hmX (Submodule.smul_mem _ _ hmY)

end GlobalTheory.LieSpanConj
