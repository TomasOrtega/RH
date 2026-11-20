import Mathlib
import Formalism.LatticeTheta.ThetaShiftInversion

open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors
open scoped FourierTransform RealInnerProductSpace SchwartzMap

namespace GlobalTheory

/- English proof (translation)
Rewrite using `[Real.fourier_eq', Real.fourier_eq']`. Establish `h` using `Measure.integral_comp_smul (volume : Measure V) (fun u : V => cexp (((-2 * Real.pi * ⟪u, t⁻¹ • w⟫ : ℝ) : ℂ) * I) • f u) t`. Rewrite `h` using `[abs_of_pos (by positivity), Complex.real_smul]`. Rewrite using `[← h]`. Use `congr 1`.

Use extensionality with `v`. Rewrite using `[real_inner_smul_left, real_inner_smul_right, ← mul_assoc t, mul_inv_cancel₀ ht.ne', one_mul]`.
-/
theorem fourier_comp_smul_of_pos {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (f : V → ℂ) {t : ℝ} (ht : 0 < t)
    (w : V) :
    (𝓕 (fun x => f (t • x)) : V → ℂ) w
      = (((t ^ Module.finrank ℝ V)⁻¹ : ℝ) : ℂ) * (𝓕 f : V → ℂ) (t⁻¹ • w) := by
  rw [Real.fourier_eq', Real.fourier_eq']
  have h := Measure.integral_comp_smul (volume : Measure V)
    (fun u : V => cexp (((-2 * Real.pi * ⟪u, t⁻¹ • w⟫ : ℝ) : ℂ) * I) • f u) t
  rw [abs_of_pos (by positivity), Complex.real_smul] at h
  rw [← h]
  congr 1
  ext v
  rw [real_inner_smul_left, real_inner_smul_right, ← mul_assoc t, mul_inv_cancel₀ ht.ne', one_mul]

/- English proof (translation)
Take `⟨hD, -⟩` from `Formalism.H.dualIsLattice V L`. Use `set d := Module.finrank ℝ V with hd`. Use `set k := A + d + Module.finrank ℤ (Formalism.H.dual L) + 1 with hk`. Use `set F : 𝓢(V, ℂ) := hc.toSchwartzMap hf with hF`. Establish `hFf : (F : V → ℂ) = f` using `rfl`.

Take `⟨C, hC0, hC⟩` from `(𝓕 F : 𝓢(V, ℂ)).decay k 0`. Establish `hs` using `ZLattice.summable_norm_pow_inv (Formalism.H.dual L) k (by omega)`. Establish `hcov : 0 < ZLattice.covolume L` using `ZLattice.covolume_pos L volume`. Use `⟨(ZLattice.covolume L)⁻¹ * (C * ∑' y : Formalism.H.dual L, ‖y‖⁻¹ ^ k), ?_⟩` and prove the remaining obligations. Introduce `x₀ t ht ht1`.

Establish `hft : ContDiff ℝ ∞ (fun x : V => f (t • x))` using `hf.comp (contDiff_const_smul t)`. Establish `hct : HasCompactSupport (fun x : V => f (t • x))` using `hc.comp_homeomorph (Homeomorph.smulOfNeZero t ht.ne')`. Take `⟨G, hG⟩ : ∃ G : 𝓢(V, ℂ), (G : V → ℂ) = fun x : V => f (t • x)` from `⟨hct.toSchwartzMap hft, rfl⟩`. Take `⟨h1, h2⟩` from `Formalism.H.poissonSchwartz V L G x₀`. Rewrite `h1`, `h2` using `[hG]`.

Rewrite using `[h2.tsum_eq, h1.tsum_eq_add_tsum_ite 0]`. Establish `h0 : (𝓕 (fun x : V => f (t • x)) : V → ℂ) ((0 : Formalism.H.dual L) : V) * Complex.exp (2 * Real.pi * Complex.I * (⟪((0 : Formalism.H.dual L) : V), x₀⟫ : ℝ)) = (((t ^ d)⁻¹ : ℝ) : ℂ) * ∫ x, f x`. Rewrite using `[fourier_comp_smul_of_pos f ht, Real.fourier_eq']`. Simplify using `[hd]`. Rewrite using `[h0, mul_add]`.

Establish `h3 : ∀ S : ℂ, (ZLattice.covolume L : ℂ)⁻¹ * ((((t ^ d)⁻¹ : ℝ) : ℂ) * ∫ x, f x) + S - (∫ x, f x) / ((ZLattice.covolume L * t ^ d : ℝ) : ℂ) = S`. Introduce `S`. Use `push_cast`. Rewrite using `[div_eq_mul_inv, mul_inv]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[h3, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hcov.le, mul_assoc (ZLattice.covolume L volume)⁻¹]`. Use `mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hcov.le)` and prove the remaining obligations. Rewrite using `[← tsum_mul_left, ← tsum_mul_right]`. Use `tsum_of_norm_bounded (((hs.mul_left C).mul_right (t ^ A)).hasSum) ?_` and prove the remaining obligations. Introduce `y`.

Use `split_ifs with hy`. Rewrite using `[norm_zero]`. Check the signs of the components of the expression. Establish `hn : 0 < ‖(y : V)‖` using `norm_pos_iff.2 (fun h => hy (Subtype.ext h))`. Establish `he : ‖Complex.exp (2 * Real.pi * Complex.I * (⟪(y : V), x₀⟫ : ℝ))‖ = 1`.

Rewrite using `[Complex.norm_exp]`. Simplify using the standard rewrite rules. Rewrite using `[norm_mul, he, mul_one, fourier_comp_smul_of_pos f ht, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]`. Establish `h4` using `hC (t⁻¹ • (y : V))`. Rewrite `h4` using `[norm_iteratedFDeriv_zero, _root_.norm_smul, Real.norm_of_nonneg (by positivity), SchwartzMap.fourier_coe, hFf]`.

Express the relevant statement in the definitionally equal form `_ ≤ C * ‖(y : V)‖⁻¹ ^ k * t ^ A`. Establish `h5 : ‖(𝓕 f : V → ℂ) (t⁻¹ • (y : V))‖ ≤ C * ‖(y : V)‖⁻¹ ^ k * t ^ k`. Rewrite `h4` using `[mul_comm, ← le_div_iff₀ (by positivity)]`. Use `h4.trans_eq ?_` and prove the remaining obligations. Rewrite using `[mul_pow, inv_pow, inv_pow]`.

Clear the denominators using the available nonvanishing facts. Establish `h6 : t ^ k ≤ t ^ (A + d)` using `pow_le_pow_of_le_one ht.le ht1 (by omega)`. Combine the equalities or inequalities in the displayed calculation. Use `mul_le_mul_of_nonneg_left (h5.trans ?_) (by positivity)` and prove the remaining obligations. Conclude with `mul_le_mul_of_nonneg_left h6 (by positivity)`.

Use `_ = _ := by rw [pow_add t A d]; field_simp`.
-/
theorem latticeSum_dilate_sub_integral_le (V : Type) [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L] (f : V → ℂ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (A : ℕ) :
    ∃ C : ℝ, ∀ (x₀ : V) (t : ℝ), 0 < t → t ≤ 1 →
      ‖∑' l : L, f (t • ((l : V) + x₀)) - (∫ x, f x) /
        ((ZLattice.covolume L * t ^ Module.finrank ℝ V : ℝ) : ℂ)‖ ≤ C * t ^ A := by
  obtain ⟨hD, -⟩ := Formalism.H.dualIsLattice V L
  set d := Module.finrank ℝ V with hd
  set k := A + d + Module.finrank ℤ (Formalism.H.dual L) + 1 with hk
  set F : 𝓢(V, ℂ) := hc.toSchwartzMap hf with hF
  have hFf : (F : V → ℂ) = f := rfl
  obtain ⟨C, hC0, hC⟩ := (𝓕 F : 𝓢(V, ℂ)).decay k 0
  have hs := ZLattice.summable_norm_pow_inv (Formalism.H.dual L) k (by omega)
  have hcov : 0 < ZLattice.covolume L := ZLattice.covolume_pos L volume
  refine ⟨(ZLattice.covolume L)⁻¹ * (C * ∑' y : Formalism.H.dual L, ‖y‖⁻¹ ^ k), ?_⟩
  intro x₀ t ht ht1
  have hft : ContDiff ℝ ∞ (fun x : V => f (t • x)) := hf.comp (contDiff_const_smul t)
  have hct : HasCompactSupport (fun x : V => f (t • x)) :=
    hc.comp_homeomorph (Homeomorph.smulOfNeZero t ht.ne')
  obtain ⟨G, hG⟩ : ∃ G : 𝓢(V, ℂ), (G : V → ℂ) = fun x : V => f (t • x) :=
    ⟨hct.toSchwartzMap hft, rfl⟩
  obtain ⟨h1, h2⟩ := Formalism.H.poissonSchwartz V L G x₀
  rw [hG] at h1 h2
  rw [h2.tsum_eq, h1.tsum_eq_add_tsum_ite 0]
  have h0 : (𝓕 (fun x : V => f (t • x)) : V → ℂ) ((0 : Formalism.H.dual L) : V) *
      Complex.exp (2 * Real.pi * Complex.I * (⟪((0 : Formalism.H.dual L) : V), x₀⟫ : ℝ))
      = (((t ^ d)⁻¹ : ℝ) : ℂ) * ∫ x, f x := by
    rw [fourier_comp_smul_of_pos f ht, Real.fourier_eq']
    simp [hd]
  rw [h0, mul_add]
  have h3 : ∀ S : ℂ, (ZLattice.covolume L : ℂ)⁻¹ * ((((t ^ d)⁻¹ : ℝ) : ℂ) * ∫ x, f x) + S -
      (∫ x, f x) / ((ZLattice.covolume L * t ^ d : ℝ) : ℂ) = S := by
    intro S
    push_cast
    rw [div_eq_mul_inv, mul_inv]
    ring
  rw [h3, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hcov.le,
    mul_assoc (ZLattice.covolume L volume)⁻¹]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hcov.le)
  rw [← tsum_mul_left, ← tsum_mul_right]
  refine tsum_of_norm_bounded (((hs.mul_left C).mul_right (t ^ A)).hasSum) ?_
  intro y
  split_ifs with hy
  · rw [norm_zero]; positivity
  have hn : 0 < ‖(y : V)‖ := norm_pos_iff.2 (fun h => hy (Subtype.ext h))
  have he : ‖Complex.exp (2 * Real.pi * Complex.I * (⟪(y : V), x₀⟫ : ℝ))‖ = 1 := by
    rw [Complex.norm_exp]; simp
  rw [norm_mul, he, mul_one, fourier_comp_smul_of_pos f ht, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (by positivity)]
  have h4 := hC (t⁻¹ • (y : V))
  rw [norm_iteratedFDeriv_zero, _root_.norm_smul, Real.norm_of_nonneg (by positivity),
    SchwartzMap.fourier_coe, hFf] at h4
  change _ ≤ C * ‖(y : V)‖⁻¹ ^ k * t ^ A
  have h5 : ‖(𝓕 f : V → ℂ) (t⁻¹ • (y : V))‖ ≤ C * ‖(y : V)‖⁻¹ ^ k * t ^ k := by
    rw [mul_comm, ← le_div_iff₀ (by positivity)] at h4
    refine h4.trans_eq ?_
    rw [mul_pow, inv_pow, inv_pow]
    field_simp
  have h6 : t ^ k ≤ t ^ (A + d) := pow_le_pow_of_le_one ht.le ht1 (by omega)
  calc (t ^ d)⁻¹ * ‖(𝓕 f : V → ℂ) (t⁻¹ • (y : V))‖
      ≤ (t ^ d)⁻¹ * (C * ‖(y : V)‖⁻¹ ^ k * t ^ (A + d)) := by
        refine mul_le_mul_of_nonneg_left (h5.trans ?_) (by positivity)
        exact mul_le_mul_of_nonneg_left h6 (by positivity)
    _ = _ := by rw [pow_add t A d]; field_simp

end GlobalTheory
