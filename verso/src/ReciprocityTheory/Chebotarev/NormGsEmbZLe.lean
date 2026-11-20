import ReciprocityTheory.Chebotarev.Support
import ReciprocityTheory.Chebotarev.DiscreteTopologyLatOf

open NumberField NumberField.mixedEmbedding NumberField.Units

open scoped Classical

namespace ReciprocityTheory.Cheb

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Unfold `Gs`. Rewrite using `[show -(s : ℂ) = ((-s : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cpow (mixedEmbedding.norm_nonneg x)]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gs_eq_ofReal {l : ℕ} (χ : DirichletCharacter ℂ l) (s : ℝ) (x : mixedSpace E) :
    Gs χ s x = χ (rsgn x : ZMod l) * ((uphi x * (mixedEmbedding.norm x) ^ (-s) : ℝ) : ℂ) := by
  unfold Gs
  rw [show -(s : ℂ) = ((-s : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_cpow (mixedEmbedding.norm_nonneg x)]
  push_cast; ring

/- English proof (translation)
Rewrite using `[gs_eq_ofReal, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (uphi_nonneg x) (Real.rpow_nonneg (mixedEmbedding.norm_nonneg x) _))]`. Conclude with `mul_le_of_le_one_left (mul_nonneg (uphi_nonneg x) (Real.rpow_nonneg (mixedEmbedding.norm_nonneg x) _)) (DirichletCharacter.norm_le_one χ _)`.
-/
theorem norm_gs_le {l : ℕ} (χ : DirichletCharacter ℂ l) (s : ℝ) (x : mixedSpace E) :
    ‖Gs χ s x‖ ≤ uphi x * (mixedEmbedding.norm x) ^ (-s) := by
  rw [gs_eq_ofReal, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (uphi_nonneg x) (Real.rpow_nonneg (mixedEmbedding.norm_nonneg x) _))]
  exact mul_le_of_le_one_left (mul_nonneg (uphi_nonneg x) (Real.rpow_nonneg (mixedEmbedding.norm_nonneg x) _))
    (DirichletCharacter.norm_le_one χ _)

/- English proof (translation)
Use `(norm_gs_le χ s _).trans ?_` and prove the remaining obligations. Establish `h1 : (mixedEmbedding.norm (embZ α)) ^ (-s) ≤ 1`. Rewrite using `[norm_embZ]`. Distinguish the cases in `h0 : Algebra.norm ℤ α = 0`. Rewrite using `[h0]`.

Simplify using `only [Int.cast_zero, abs_zero]`. Rewrite using `[Real.zero_rpow (by linarith)]; norm_num`. Apply `Real.rpow_le_one_of_one_le_of_nonpos _ (by linarith)` to reduce the goal to its premises. Establish `: (1 : ℤ) ≤ |Algebra.norm ℤ α|` using `Int.one_le_abs h0`. Conclude with `this` after adjusting the coercions.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_gs_embZ_le {l : ℕ} (χ : DirichletCharacter ℂ l) {s : ℝ} (hs : 1 ≤ s) (α : 𝓞 E) :
    ‖Gs χ s (embZ α)‖ ≤ 1 := by
  refine (norm_gs_le χ s _).trans ?_
  have h1 : (mixedEmbedding.norm (embZ α)) ^ (-s) ≤ 1 := by
    rw [norm_embZ]
    by_cases h0 : Algebra.norm ℤ α = 0
    · rw [h0]; simp only [Int.cast_zero, abs_zero]
      rw [Real.zero_rpow (by linarith)]; norm_num
    · apply Real.rpow_le_one_of_one_le_of_nonpos _ (by linarith)
      have : (1 : ℤ) ≤ |Algebra.norm ℤ α| := Int.one_le_abs h0
      exact_mod_cast this
  calc uphi (embZ α) * (mixedEmbedding.norm (embZ α)) ^ (-s) ≤ 1 * 1 :=
        mul_le_mul (uphi_le_one _) h1 (Real.rpow_nonneg (mixedEmbedding.norm_nonneg _) _) zero_le_one
    _ = 1 := one_mul 1

/- English proof (translation)
Repeatedly rewrite using `[gs_eq_ofReal]`. Distinguish the cases in `h : mixedEmbedding.norm x = 0`. Simplify using `only [uphi_of_norm_eq_zero h, zero_mul, Complex.ofReal_zero, mul_zero]`. Conclude with `continuous_const`. Use `continuous_const.mul (Complex.continuous_ofReal.comp (continuous_const.mul ?_))` and prove the remaining obligations.

Conclude with `(Real.continuous_const_rpow h).comp continuous_neg`.
-/
theorem continuous_gs {l : ℕ} (χ : DirichletCharacter ℂ l) (x : mixedSpace E) :
    Continuous fun s : ℝ => Gs χ s x := by
  simp_rw [gs_eq_ofReal]
  by_cases h : mixedEmbedding.norm x = 0
  · simp only [uphi_of_norm_eq_zero h, zero_mul, Complex.ofReal_zero, mul_zero]
    exact continuous_const
  · refine continuous_const.mul (Complex.continuous_ofReal.comp (continuous_const.mul ?_))
    exact (Real.continuous_const_rpow h).comp continuous_neg

/- English proof (translation)
Take `⟨c₀, hc₀, -, hb⟩` from `exists_support_bound (E := E)`. Use `set d := Module.finrank ℚ E`. Establish `hd : (1 : ℝ) ≤ d` using `by exact_mod_cast Module.finrank_pos`. Use `set r : ℝ := -((d : ℝ) * s)`. Establish `hr : r < -(Module.finrank ℤ Λ : ℝ)`.

Rewrite using `[hΛ]`. Simplify using `only [r, neg_lt_neg_iff]`. Use the polynomial consequences of the given equalities and inequalities. Use `Summable.of_norm_bounded ((ZLattice.summable_norm_rpow Λ r hr).mul_left (c₀ ^ r)) fun x => ?_` and prove the remaining obligations. Use `(norm_gs_le χ s _).trans ?_` and prove the remaining obligations.

Establish `hpos : 0 ≤ c₀ ^ r * ‖x‖ ^ r` using `mul_nonneg (Real.rpow_nonneg hc₀.le _) (Real.rpow_nonneg (norm_nonneg _) _)`. Distinguish the cases in `hu : uphi (x : mixedSpace E) = 0`. Rewrite using `[hu, zero_mul]`. Conclude with `hpos`. Take `⟨-, hN⟩` from `hb _ hu`.

Establish `hN0 : mixedEmbedding.norm (x : mixedSpace E) ≠ 0`. Introduce `h`. Conclude with `hu (uphi_of_norm_eq_zero h)`. Establish `hx0 : (x : mixedSpace E) ≠ 0`. Introduce and unpack `h`.

Apply `hN0` to reduce the goal to its premises. Rewrite using `[h]`. Conclude with `mixedEmbedding.norm_eq_zero_iff.mpr ⟨Classical.arbitrary _, by simp⟩`. Establish `hxn : 0 < ‖(x : mixedSpace E)‖` using `norm_pos_iff.mpr hx0`. Establish `hcx : 0 < c₀ * ‖(x : mixedSpace E)‖` using `mul_pos hc₀ hxn`.

Establish `key : (mixedEmbedding.norm (x : mixedSpace E)) ^ (-s) ≤ (c₀ * ‖(x : mixedSpace E)‖) ^ r`. Establish `: (c₀ * ‖(x : mixedSpace E)‖) ^ r = ((c₀ * ‖(x : mixedSpace E)‖) ^ d) ^ (-s)`. Rewrite using `[← Real.rpow_natCast, ← Real.rpow_mul hcx.le]`. Simplify using `[r]`. Rewrite using `[this]`.

Conclude with `Real.rpow_le_rpow_of_nonpos (pow_pos hcx _) (by rw [mul_pow]; exact hN) (by linarith)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem summable_gs {l : ℕ} (χ : DirichletCharacter ℂ l) (Λ : Submodule ℤ (mixedSpace E)) [DiscreteTopology Λ]
    (hΛ : Module.finrank ℤ Λ = Module.finrank ℚ E) {s : ℝ} (hs : 1 < s) :
    Summable fun x : Λ => Gs χ s (x : mixedSpace E) := by
  obtain ⟨c₀, hc₀, -, hb⟩ := exists_support_bound (E := E)
  set d := Module.finrank ℚ E
  have hd : (1 : ℝ) ≤ d := by exact_mod_cast Module.finrank_pos
  set r : ℝ := -((d : ℝ) * s)
  have hr : r < -(Module.finrank ℤ Λ : ℝ) := by
    rw [hΛ]; simp only [r, neg_lt_neg_iff]; nlinarith
  refine Summable.of_norm_bounded ((ZLattice.summable_norm_rpow Λ r hr).mul_left (c₀ ^ r)) fun x => ?_
  refine (norm_gs_le χ s _).trans ?_
  have hpos : 0 ≤ c₀ ^ r * ‖x‖ ^ r := mul_nonneg (Real.rpow_nonneg hc₀.le _) (Real.rpow_nonneg (norm_nonneg _) _)
  by_cases hu : uphi (x : mixedSpace E) = 0
  · rw [hu, zero_mul]; exact hpos
  obtain ⟨-, hN⟩ := hb _ hu
  have hN0 : mixedEmbedding.norm (x : mixedSpace E) ≠ 0 := by
    intro h; exact hu (uphi_of_norm_eq_zero h)
  have hx0 : (x : mixedSpace E) ≠ 0 := by
    rintro h; apply hN0; rw [h]
    exact mixedEmbedding.norm_eq_zero_iff.mpr ⟨Classical.arbitrary _, by simp⟩
  have hxn : 0 < ‖(x : mixedSpace E)‖ := norm_pos_iff.mpr hx0
  have hcx : 0 < c₀ * ‖(x : mixedSpace E)‖ := mul_pos hc₀ hxn
  have key : (mixedEmbedding.norm (x : mixedSpace E)) ^ (-s) ≤ (c₀ * ‖(x : mixedSpace E)‖) ^ r := by
    have : (c₀ * ‖(x : mixedSpace E)‖) ^ r = ((c₀ * ‖(x : mixedSpace E)‖) ^ d) ^ (-s) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hcx.le]; simp [r]
    rw [this]
    exact Real.rpow_le_rpow_of_nonpos (pow_pos hcx _) (by rw [mul_pow]; exact hN) (by linarith)
  calc uphi (x : mixedSpace E) * (mixedEmbedding.norm (x : mixedSpace E)) ^ (-s)
      ≤ 1 * (c₀ * ‖(x : mixedSpace E)‖) ^ r :=
        mul_le_mul (uphi_le_one _) key (Real.rpow_nonneg (mixedEmbedding.norm_nonneg _) _) zero_le_one
    _ = c₀ ^ r * ‖x‖ ^ r := by rw [one_mul, Real.mul_rpow hc₀.le (norm_nonneg _)]; rfl

end ReciprocityTheory.Cheb
