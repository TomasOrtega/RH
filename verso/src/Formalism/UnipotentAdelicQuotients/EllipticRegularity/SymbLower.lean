import Formalism.UnipotentAdelicQuotients.EllRegCut

namespace ZetaZeros.D.EllReg

open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal

noncomputable section

/- English proof (translation)
Unfold `ZetaZeros.D.EllReg.Sys.symb`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations. Establish `hc : ∀ l, (((t • ξ) (w l) : ℝ) : ℂ) = (t : ℂ) * ((ξ (w l) : ℝ) : ℂ)` using `fun l => by simp`. Simplify using `only [hc, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]`.

Expand and normalize the polynomial expressions, which then agree.
-/
private theorem symb_smul_covector_eq_pow_ord_mul {d : ℕ} {ι : Type} (P : Sys d ι) (i : ι)
    (x ξ : E d) (t : ℝ) :
    P.symb i x (t • ξ) = (t : ℂ) ^ (P.ord i) * P.symb i x ξ := by
  unfold ZetaZeros.D.EllReg.Sys.symb
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hc : ∀ l, (((t • ξ) (w l) : ℝ) : ℂ) = (t : ℂ) * ((ξ (w l) : ℝ) : ℂ) := fun l => by simp
  simp only [hc, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  ring

/- English proof (translation)
Unfold `ZetaZeros.D.EllReg.Sys.symb`. Use `fun_prop`.
-/
private theorem continuous_symb_covector {d : ℕ} {ι : Type} (P : Sys d ι) (i : ι)
    (x : E d) : Continuous fun ξ : E d => P.symb i x ξ := by
  unfold ZetaZeros.D.EllReg.Sys.symb
  fun_prop

/- English proof (translation)
Introduce `d ι _ P x0 k hk hell`. Take `⟨f, hf⟩ : ∃ f : E d → ℝ, f = fun ξ => ∑ i, ‖ξ‖ ^ (2 * (k - P.ord i)) * ‖P.symb i x0 ξ‖ ^ 2` from `⟨_, rfl⟩`. Establish `hfξ : ∀ ξ, f ξ = ∑ i, ‖ξ‖ ^ (2 * (k - P.ord i)) * ‖P.symb i x0 ξ‖ ^ 2`. Introduce `ξ`. Rewrite using `[hf]`.

Establish `hcont : Continuous f`. Rewrite using `[hf]`. Use `continuous_finsetSum _ fun i _ => ?_` and prove the remaining obligations. Conclude with `(continuous_norm.pow _).mul ((continuous_symb_covector P i x0).norm.pow 2)`. Establish `hhom : ∀ t : ℝ, 0 ≤ t → ∀ ξ : E d, f (t • ξ) = t ^ (2 * k) * f ξ`.

Introduce `t ht ξ`. Rewrite using `[hfξ, hfξ, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `h1 : ‖t • ξ‖ = t * ‖ξ‖` using `by rw [norm_smul, Real.norm_of_nonneg ht]`. Establish `h2 : ‖(t : ℂ) ^ (P.ord i) * P.symb i x0 ξ‖ = t ^ (P.ord i) * ‖P.symb i x0 ξ‖`.

Rewrite using `[norm_mul, norm_pow, Complex.norm_of_nonneg ht]`. Rewrite using `[symb_smul_covector_eq_pow_ord_mul, h1, h2]`. Establish `hk' : 2 * k = 2 * (k - P.ord i) + 2 * P.ord i` using `by have := hk i; omega`. Rewrite using `[hk', pow_add]`. Expand and normalize the polynomial expressions, which then agree.

Break down `(sphere (0 : E d) 1).eq_empty_or_nonempty with hS | hS` into its components or cases. Use `⟨1, one_pos, fun ξ hξ => ?_⟩` and prove the remaining obligations. It suffices to derive a contradiction. Establish `hmem : ‖ξ‖⁻¹ • ξ ∈ sphere (0 : E d) 1`. Rewrite using `[mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hξ)]`.

Rewrite `hmem` using `[hS]`. Conclude with `hmem`. Take `⟨η0, hη0S, hmin⟩` from `(isCompact_sphere (0 : E d) 1).exists_isMinOn hS hcont.continuousOn`. Establish `hη0n : ‖η0‖ = 1` using `mem_sphere_zero_iff_norm.mp hη0S`. Establish `hne : η0 ≠ 0`.

Introduce `h`. Rewrite `hη0n` using `[h, norm_zero]`. Conclude with `zero_ne_one hη0n`. Take `⟨i, hi⟩` from `hell η0 hne`. Establish `hpos : 0 < f η0`.

Establish `hle : ‖η0‖ ^ (2 * (k - P.ord i)) * ‖P.symb i x0 η0‖ ^ 2 ≤ f η0`. Rewrite using `[hfξ]`. Conclude with `Finset.single_le_sum (f := fun j => ‖η0‖ ^ (2 * (k - P.ord j)) * ‖P.symb j x0 η0‖ ^ 2) (fun j _ => by positivity) (Finset.mem_univ i)`. Establish `hlt : 0 < ‖η0‖ ^ (2 * (k - P.ord i)) * ‖P.symb i x0 η0‖ ^ 2`. Rewrite using `[hη0n, one_pow, one_mul]`.

Conclude with `pow_pos (norm_pos_iff.mpr hi) 2`. Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨f η0, hpos, fun ξ hξ => ?_⟩` and prove the remaining obligations. Establish `ht : 0 < ‖ξ‖` using `norm_pos_iff.mpr hξ`. Establish `hηS : ‖ξ‖⁻¹ • ξ ∈ sphere (0 : E d) 1`.

Rewrite using `[mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ ht.ne']`. Establish `hξη : ξ = ‖ξ‖ • (‖ξ‖⁻¹ • ξ)`. Rewrite using `[smul_smul, mul_inv_cancel₀ ht.ne', one_smul]`. Establish `hle : f η0 ≤ f (‖ξ‖⁻¹ • ξ)` using `hmin hηS`. Establish `hfx : f ξ = ‖ξ‖ ^ (2 * k) * f (‖ξ‖⁻¹ • ξ)` using `by conv_lhs => rw [hξη]`.

Conclude with `hhom _ ht.le _`. Rewrite using `[← hfξ, hfx, mul_comm]`. Conclude with `mul_le_mul_of_nonneg_left hle (by positivity)`.
-/
theorem symbolLowerBound : SymbLower := by
  intro d ι _ P x0 k hk hell
  obtain ⟨f, hf⟩ : ∃ f : E d → ℝ,
      f = fun ξ => ∑ i, ‖ξ‖ ^ (2 * (k - P.ord i)) * ‖P.symb i x0 ξ‖ ^ 2 := ⟨_, rfl⟩
  have hfξ : ∀ ξ, f ξ = ∑ i, ‖ξ‖ ^ (2 * (k - P.ord i)) * ‖P.symb i x0 ξ‖ ^ 2 := by
    intro ξ; rw [hf]
  have hcont : Continuous f := by
    rw [hf]
    refine continuous_finsetSum _ fun i _ => ?_
    exact (continuous_norm.pow _).mul
      ((continuous_symb_covector P i x0).norm.pow 2)
  have hhom : ∀ t : ℝ, 0 ≤ t → ∀ ξ : E d, f (t • ξ) = t ^ (2 * k) * f ξ := by
    intro t ht ξ
    rw [hfξ, hfξ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 : ‖t • ξ‖ = t * ‖ξ‖ := by rw [norm_smul, Real.norm_of_nonneg ht]
    have h2 : ‖(t : ℂ) ^ (P.ord i) * P.symb i x0 ξ‖
        = t ^ (P.ord i) * ‖P.symb i x0 ξ‖ := by
      rw [norm_mul, norm_pow, Complex.norm_of_nonneg ht]
    rw [symb_smul_covector_eq_pow_ord_mul, h1, h2]
    have hk' : 2 * k = 2 * (k - P.ord i) + 2 * P.ord i := by have := hk i; omega
    rw [hk', pow_add]
    ring
  rcases (sphere (0 : E d) 1).eq_empty_or_nonempty with hS | hS
  · refine ⟨1, one_pos, fun ξ hξ => ?_⟩
    exfalso
    have hmem : ‖ξ‖⁻¹ • ξ ∈ sphere (0 : E d) 1 := by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hξ)]
    rw [hS] at hmem
    exact hmem
  · obtain ⟨η0, hη0S, hmin⟩ := (isCompact_sphere (0 : E d) 1).exists_isMinOn hS hcont.continuousOn
    have hη0n : ‖η0‖ = 1 := mem_sphere_zero_iff_norm.mp hη0S
    have hne : η0 ≠ 0 := by
      intro h
      rw [h, norm_zero] at hη0n
      exact zero_ne_one hη0n
    obtain ⟨i, hi⟩ := hell η0 hne
    have hpos : 0 < f η0 := by
      have hle : ‖η0‖ ^ (2 * (k - P.ord i)) * ‖P.symb i x0 η0‖ ^ 2 ≤ f η0 := by
        rw [hfξ]
        exact Finset.single_le_sum
          (f := fun j => ‖η0‖ ^ (2 * (k - P.ord j)) * ‖P.symb j x0 η0‖ ^ 2)
          (fun j _ => by positivity) (Finset.mem_univ i)
      have hlt : 0 < ‖η0‖ ^ (2 * (k - P.ord i)) * ‖P.symb i x0 η0‖ ^ 2 := by
        rw [hη0n, one_pow, one_mul]
        exact pow_pos (norm_pos_iff.mpr hi) 2
      linarith
    refine ⟨f η0, hpos, fun ξ hξ => ?_⟩
    have ht : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
    have hηS : ‖ξ‖⁻¹ • ξ ∈ sphere (0 : E d) 1 := by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ ht.ne']
    have hξη : ξ = ‖ξ‖ • (‖ξ‖⁻¹ • ξ) := by
      rw [smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
    have hle : f η0 ≤ f (‖ξ‖⁻¹ • ξ) := hmin hηS
    have hfx : f ξ = ‖ξ‖ ^ (2 * k) * f (‖ξ‖⁻¹ • ξ) := by
      conv_lhs => rw [hξη]
      exact hhom _ ht.le _
    rw [← hfξ, hfx, mul_comm]
    exact mul_le_mul_of_nonneg_left hle (by positivity)

end

end ZetaZeros.D.EllReg
