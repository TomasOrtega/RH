import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.KerPNonzero

noncomputable section
open scoped BigOperators ComplexConjugate Nat
open MeasureTheory

namespace Formalism.L2.Th1.H

/- English proof (translation)
Establish `h1 : s ^ n / (n ! : ℝ) ≤ Real.exp s` using `Real.pow_div_factorial_le_exp s hs.le n`. Establish `hf : (0 : ℝ) < (n ! : ℝ)` using `by exact_mod_cast n.factorial_pos`. Establish `hp : 0 < s ^ n` using `pow_pos hs n`. Rewrite using `[Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos s) hp]`. Rewrite `h1` using `[div_le_iff₀ hf]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exp_neg_le_factorial_div {s : ℝ} (hs : 0 < s) (n : ℕ) : Real.exp (-s) ≤ (n ! : ℝ) / s ^ n := by
  have h1 : s ^ n / (n ! : ℝ) ≤ Real.exp s := Real.pow_div_factorial_le_exp s hs.le n
  have hf : (0 : ℝ) < (n ! : ℝ) := by exact_mod_cast n.factorial_pos
  have hp : 0 < s ^ n := pow_pos hs n
  rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos s) hp]
  rw [div_le_iff₀ hf] at h1
  linarith

/- English proof (translation)
Establish `h : ‖x‖ ≤ ‖x - z₀‖ + ‖z₀‖`. Simplify using `using norm_add_le (x - z₀) z₀`. Establish `h0` using `norm_nonneg x`. Establish `h1` using `norm_nonneg (x - z₀)`. Establish `h2` using `norm_nonneg z₀`.

Establish `h3 : ‖x‖ ^ 2 ≤ (‖x - z₀‖ + ‖z₀‖) ^ 2` using `pow_le_pow_left₀ h0 h 2`. Use polynomial arithmetic with `[sq_nonneg (‖x - z₀‖ - ‖z₀‖)]`.
-/
theorem half_sq_sub_le {V : Type*} [NormedAddCommGroup V] (x z₀ : V) :
    ‖x‖ ^ 2 / 2 - ‖z₀‖ ^ 2 ≤ ‖x - z₀‖ ^ 2 := by
  have h : ‖x‖ ≤ ‖x - z₀‖ + ‖z₀‖ := by
    simpa using norm_add_le (x - z₀) z₀
  have h0 := norm_nonneg x
  have h1 := norm_nonneg (x - z₀)
  have h2 := norm_nonneg z₀
  have h3 : ‖x‖ ^ 2 ≤ (‖x - z₀‖ + ‖z₀‖) ^ 2 := pow_le_pow_left₀ h0 h 2
  nlinarith [sq_nonneg (‖x - z₀‖ - ‖z₀‖)]

/- English proof (translation)
Set `L : Submodule ℤ V` to `AddSubgroup.toIntSubmodule Λ`. Establish `: DiscreteTopology L` using `hd`. Use `set n : ℕ := Module.finrank ℤ L + 1 with hn`. Establish `hsum : Summable fun z : L => ‖z‖⁻¹ ^ (2 * n)` using `ZLattice.summable_norm_pow_inv L (2 * n) (by omega)`. Establish `hsum' : Summable fun x : Λ => ‖(x : V)‖⁻¹ ^ (2 * n)` using `hsum`.

Establish `hite : Summable fun x : Λ => if x = 0 then (1 : ℝ) else 0` using `(hasSum_ite_eq (0 : Λ) (1 : ℝ)).summable`. Use `Summable.of_nonneg_of_le (fun x => (Real.exp_pos _).le) (fun x => ?_) ((hsum'.mul_left ((n ! : ℝ) / a ^ n)).add hite)` and prove the remaining obligations. Distinguish the cases in `hx : x = 0`. Substitute `hx` using the available equality. Simplify using the standard rewrite rules.

Establish `hx' : 0 < ‖(x : V)‖`. Rewrite using `[norm_pos_iff]`. Conclude with `fun h => hx (Subtype.ext h)`. Establish `hs : 0 < a * ‖(x : V)‖ ^ 2` using `by positivity`. Establish `h1` using `exp_neg_le_factorial_div hs n`.

Rewrite using `[if_neg hx, add_zero]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_pow, ← pow_mul, inv_pow]`. Clear the denominators using the available nonvanishing facts.
-/
theorem summable_gauss_of_discrete {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (Λ : AddSubgroup V) [hd : DiscreteTopology Λ] {a : ℝ} (ha : 0 < a) :
    Summable fun x : Λ => Real.exp (-a * ‖(x : V)‖ ^ 2) := by
  classical
  let L : Submodule ℤ V := AddSubgroup.toIntSubmodule Λ
  have : DiscreteTopology L := hd
  set n : ℕ := Module.finrank ℤ L + 1 with hn
  have hsum : Summable fun z : L => ‖z‖⁻¹ ^ (2 * n) :=
    ZLattice.summable_norm_pow_inv L (2 * n) (by omega)
  have hsum' : Summable fun x : Λ => ‖(x : V)‖⁻¹ ^ (2 * n) := hsum
  have hite : Summable fun x : Λ => if x = 0 then (1 : ℝ) else 0 := (hasSum_ite_eq (0 : Λ) (1 : ℝ)).summable
  refine Summable.of_nonneg_of_le (fun x => (Real.exp_pos _).le) (fun x => ?_)
    ((hsum'.mul_left ((n ! : ℝ) / a ^ n)).add hite)
  by_cases hx : x = 0
  · subst hx
    simp
  · have hx' : 0 < ‖(x : V)‖ := by
      rw [norm_pos_iff]
      exact fun h => hx (Subtype.ext h)
    have hs : 0 < a * ‖(x : V)‖ ^ 2 := by positivity
    have h1 := exp_neg_le_factorial_div hs n
    rw [if_neg hx, add_zero]
    calc Real.exp (-a * ‖(x : V)‖ ^ 2) = Real.exp (-(a * ‖(x : V)‖ ^ 2)) := by rw [neg_mul]
      _ ≤ (n ! : ℝ) / (a * ‖(x : V)‖ ^ 2) ^ n := h1
      _ = (n ! : ℝ) / a ^ n * ‖(x : V)‖⁻¹ ^ (2 * n) := by
          rw [mul_pow, ← pow_mul, inv_pow]
          field_simp

/- English proof (translation)
Introduce `V _ _ _ Λ hΛ c r hc`. Establish `: DiscreteTopology Λ` using `hΛ.1`. Establish `hs : Summable fun x : Λ => Real.exp (-(c / 2) * ‖(x : V)‖ ^ 2)` using `summable_gauss_of_discrete Λ (by positivity)`. Use `⟨fun x => Real.exp (c * r ^ 2) * Real.exp (-(c / 2) * ‖(x : V)‖ ^ 2), hs.mul_left _, ?_⟩` and prove the remaining obligations. Introduce `x z₀ hz`.

Use `show _ ≤ Real.exp (c * r ^ 2) * Real.exp (-(c / 2) * ‖(x : V)‖ ^ 2)`. Rewrite using `[← Real.exp_add]`. Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises. Establish `h1` using `half_sq_sub_le (x : V) z₀`. Establish `h2 : ‖z₀‖ ^ 2 ≤ r ^ 2` using `pow_le_pow_left₀ (norm_nonneg z₀) hz 2`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem latticeGaussSummable : LatGaussSummable := by
  intro V _ _ _ Λ hΛ c r hc
  have : DiscreteTopology Λ := hΛ.1
  have hs : Summable fun x : Λ => Real.exp (-(c / 2) * ‖(x : V)‖ ^ 2) :=
    summable_gauss_of_discrete Λ (by positivity)
  refine ⟨fun x => Real.exp (c * r ^ 2) * Real.exp (-(c / 2) * ‖(x : V)‖ ^ 2), hs.mul_left _, ?_⟩
  intro x z₀ hz
  show _ ≤ Real.exp (c * r ^ 2) * Real.exp (-(c / 2) * ‖(x : V)‖ ^ 2)
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h1 := half_sq_sub_le (x : V) z₀
  have h2 : ‖z₀‖ ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (norm_nonneg z₀) hz 2
  nlinarith

/- English proof (translation)
Set `b` to `Module.finBasis ℂ V`. Establish `h : (fun z => H z z) = fun z => ∑ j, conj (b.coord j z) * H.flip (b j) z`. Use function extensionality and compare the values at `z`. Establish `e : H z z = H z (∑ j, b.repr z j • b j)` using `by rw [b.sum_repr z]`. Rewrite using `[e]`.

Simplify using `only [map_sum, map_smulₛₗ, smul_eq_mul, LinearMap.flip_apply, Module.Basis.coord_apply]`. Rewrite using `[h]`. Use `continuous_finsetSum _ fun j _ => ?_` and prove the remaining obligations. Conclude with `(Complex.continuous_conj.comp (LinearMap.continuous_of_finiteDimensional (b.coord j))).mul (LinearMap.continuous_of_finiteDimensional (H.flip (b j)))`.
-/
theorem continuous_diag {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (H : Sesq V) :
    Continuous fun z => H z z := by
  let b := Module.finBasis ℂ V
  have h : (fun z => H z z) = fun z => ∑ j, conj (b.coord j z) * H.flip (b j) z := by
    funext z
    have e : H z z = H z (∑ j, b.repr z j • b j) := by rw [b.sum_repr z]
    rw [e]
    simp only [map_sum, map_smulₛₗ, smul_eq_mul, LinearMap.flip_apply, Module.Basis.coord_apply]
  rw [h]
  refine continuous_finsetSum _ fun j _ => ?_
  exact (Complex.continuous_conj.comp (LinearMap.continuous_of_finiteDimensional (b.coord j))).mul
    (LinearMap.continuous_of_finiteDimensional (H.flip (b j)))

/- English proof (translation)
Establish `hs : 0 < a * (1 + t ^ 2)` using `by positivity`. Establish `h1` using `exp_neg_le_factorial_div hs m`. Establish `h2 : (1 + t) ^ 2 ≤ 2 * (1 + t ^ 2)` using `by nlinarith [sq_nonneg (1 - t)]`. Establish `h3 : (1 + t) ^ (2 * m) ≤ 2 ^ m * (1 + t ^ 2) ^ m`. Rewrite using `[pow_mul, ← mul_pow]`.

Conclude with `pow_le_pow_left₀ (by positivity) h2 m`. Establish `h4 : 0 < (1 + t) ^ (2 * m)` using `by positivity`. Establish `h5 : 0 < (1 + t ^ 2) ^ m` using `by positivity`. Establish `ham : 0 < a ^ m` using `pow_pos ha m`. Establish `hf : (0 : ℝ) < (m ! : ℝ)` using `by exact_mod_cast m.factorial_pos`.

Rewrite using `[Real.rpow_neg (by positivity), Real.rpow_natCast]`. Establish `e : -a * t ^ 2 = a + -(a * (1 + t ^ 2))` using `by ring`. Rewrite using `[e, Real.exp_add]`. Establish `h6 : ((1 + t ^ 2) ^ m)⁻¹ ≤ 2 ^ m * ((1 + t) ^ (2 * m))⁻¹`. Rewrite using `[← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ h5 h4]`.

Combine the linear equalities and inequalities to obtain the conclusion. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_pow]`. Clear the denominators using the available nonvanishing facts. Use `_ ≤ Real.exp a * (m ! : ℝ) / a ^ m * (2 ^ m * ((1 + t) ^ (2 * m))⁻¹) := mul_le_mul_of_nonneg_left h6 (by positivity)`.

Use `_ = Real.exp a * (m ! : ℝ) * 2 ^ m / a ^ m * ((1 + t) ^ (2 * m))⁻¹ := by ring`.
-/
theorem exp_neg_sq_le_japanese {a : ℝ} (ha : 0 < a) (m : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (-a * t ^ 2) ≤ Real.exp a * (m ! : ℝ) * 2 ^ m / a ^ m * (1 + t) ^ (-((2 * m : ℕ) : ℝ)) := by
  have hs : 0 < a * (1 + t ^ 2) := by positivity
  have h1 := exp_neg_le_factorial_div hs m
  have h2 : (1 + t) ^ 2 ≤ 2 * (1 + t ^ 2) := by nlinarith [sq_nonneg (1 - t)]
  have h3 : (1 + t) ^ (2 * m) ≤ 2 ^ m * (1 + t ^ 2) ^ m := by
    rw [pow_mul, ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) h2 m
  have h4 : 0 < (1 + t) ^ (2 * m) := by positivity
  have h5 : 0 < (1 + t ^ 2) ^ m := by positivity
  have ham : 0 < a ^ m := pow_pos ha m
  have hf : (0 : ℝ) < (m ! : ℝ) := by exact_mod_cast m.factorial_pos
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast]
  have e : -a * t ^ 2 = a + -(a * (1 + t ^ 2)) := by ring
  rw [e, Real.exp_add]
  have h6 : ((1 + t ^ 2) ^ m)⁻¹ ≤ 2 ^ m * ((1 + t) ^ (2 * m))⁻¹ := by
    rw [← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ h5 h4]
    linarith
  calc Real.exp a * Real.exp (-(a * (1 + t ^ 2)))
      ≤ Real.exp a * ((m ! : ℝ) / (a * (1 + t ^ 2)) ^ m) :=
        mul_le_mul_of_nonneg_left h1 (Real.exp_pos a).le
    _ = Real.exp a * (m ! : ℝ) / a ^ m * ((1 + t ^ 2) ^ m)⁻¹ := by
        rw [mul_pow]; field_simp
    _ ≤ Real.exp a * (m ! : ℝ) / a ^ m * (2 ^ m * ((1 + t) ^ (2 * m))⁻¹) :=
        mul_le_mul_of_nonneg_left h6 (by positivity)
    _ = Real.exp a * (m ! : ℝ) * 2 ^ m / a ^ m * ((1 + t) ^ (2 * m))⁻¹ := by ring

/- English proof (translation)
Introduce `V _ _ _ _ _ μ _ H hH hP c hc`. Take `⟨c₀, C, hc₀, _, hb⟩` from `h V H hH hP`. Establish `hcont : Continuous fun z => Real.exp (-c * (H z z).re)` using `Real.continuous_exp.comp (continuous_const.mul (Complex.continuous_re.comp (continuous_diag H)))`. Use `set m : ℕ := Module.finrank ℝ V + 1 with hm`. Establish `hJ : Integrable (fun z : V => (1 + ‖z‖) ^ (-((2 * m : ℕ) : ℝ))) μ` using `integrable_one_add_norm (by`.

Establish `: Module.finrank ℝ V < 2 * m` using `by omega`. Conclude with `this)` after adjusting the coercions. Establish `ha : 0 < c * c₀` using `by positivity`. Establish `hint : Integrable (fun z => Real.exp (-c * (H z z).re)) μ`. Use `Integrable.mono' (hJ.const_mul (Real.exp (c * c₀) * (m ! : ℝ) * 2 ^ m / (c * c₀) ^ m)) hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun z => ?_)` and prove the remaining obligations.

Rewrite using `[Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]`. Use `le_trans (Real.exp_le_exp.mpr ?_) (exp_neg_sq_le_japanese ha m (norm_nonneg z))` and prove the remaining obligations. Use `(hb z).1` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Use `⟨hint, ?_⟩` and prove the remaining obligations.

Rewrite using `[integral_pos_iff_support_of_nonneg (fun z => (Real.exp_pos _).le) hint]`. Establish `hsupp : Function.support (fun z => Real.exp (-c * (H z z).re)) = Set.univ`. Use extensionality with `z`. Simplify using `[Real.exp_ne_zero]`. Rewrite using `[hsupp]`.

Conclude with `isOpen_univ.measure_pos μ Set.univ_nonempty`.
-/
theorem GaussIntegrable_of (h : FormNorm) : GaussIntegrable := by
  intro V _ _ _ _ _ μ _ H hH hP c hc
  obtain ⟨c₀, C, hc₀, _, hb⟩ := h V H hH hP
  have hcont : Continuous fun z => Real.exp (-c * (H z z).re) :=
    Real.continuous_exp.comp (continuous_const.mul (Complex.continuous_re.comp (continuous_diag H)))
  set m : ℕ := Module.finrank ℝ V + 1 with hm
  have hJ : Integrable (fun z : V => (1 + ‖z‖) ^ (-((2 * m : ℕ) : ℝ))) μ :=
    integrable_one_add_norm (by
      have : Module.finrank ℝ V < 2 * m := by omega
      exact_mod_cast this)
  have ha : 0 < c * c₀ := by positivity
  have hint : Integrable (fun z => Real.exp (-c * (H z z).re)) μ := by
    refine Integrable.mono' (hJ.const_mul (Real.exp (c * c₀) * (m ! : ℝ) * 2 ^ m / (c * c₀) ^ m))
      hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine le_trans (Real.exp_le_exp.mpr ?_) (exp_neg_sq_le_japanese ha m (norm_nonneg z))
    have := (hb z).1
    nlinarith
  refine ⟨hint, ?_⟩
  rw [integral_pos_iff_support_of_nonneg (fun z => (Real.exp_pos _).le) hint]
  have hsupp : Function.support (fun z => Real.exp (-c * (H z z).re)) = Set.univ := by
    ext z
    simp [Real.exp_ne_zero]
  rw [hsupp]
  exact isOpen_univ.measure_pos μ Set.univ_nonempty

end Formalism.L2.Th1.H
