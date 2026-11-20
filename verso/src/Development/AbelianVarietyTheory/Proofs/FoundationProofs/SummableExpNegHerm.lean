import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsPosHermFormV
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
open Complex MeasureTheory GlobalTheory.UnitaryTheta
open scoped BigOperators ComplexConjugate Real Classical

namespace GlobalTheory.UnitaryTheta.GaussSumm

/- English proof (translation)
Establish `hcont : Continuous fun x : V => (H x x).re`. Set `b` to `Module.finBasis ℂ V`. Establish `e : (fun x : V => H x x) = fun x => ∑ i, H x (b i) * conj (b.repr x i)`. Use function extensionality and compare the values at `x`. Use `conv_lhs => rw [show H x x = H x (∑ i, b.repr x i • b i) by rw [b.sum_repr]]`.

Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.map_smulₛₗ, smul_eq_mul, mul_comm]`. Establish `: Continuous fun x : V => H x x`. Rewrite using `[e]`.

Use `continuous_finset_sum _ fun i _ => ?_` and prove the remaining obligations. Establish `h1 : Continuous fun x : V => H x (b i)` using `(H.flip (b i)).continuous_of_finiteDimensional`. Establish `h2 : Continuous fun x : V => b.repr x i` using `(b.coord i).continuous_of_finiteDimensional`. Conclude with `h1.mul (continuous_conj.comp h2)`. Conclude with `continuous_re.comp this`.

Use `haveI : ProperSpace V := FiniteDimensional.proper ℂ V`. Choose the witnesses or unpack the hypotheses as in `⟨c, hc, hle⟩ : ∃ c : ℝ, 0 < c ∧ ∀ x ∈ Metric.sphere (0 : V) 1, c ≤ (H x x).re := by`. Use `(isCompact_sphere (0 : V) 1).exists_forall_le' hcont.continuousOn fun x hx => hH.2 x ?_` and prove the remaining obligations. Introduce and unpack `rfl`. Simplify using `at hx`.

Use `⟨c, hc, fun x => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hx : x = 0`. Substitute `hx` using the available equality. Simplify using the standard rewrite rules. Establish `hn : 0 < ‖x‖` using `norm_pos_iff.2 hx`.

Establish `h1` using `hle (((‖x‖⁻¹ : ℝ) : ℂ) • x) (by`. Rewrite using `[mem_sphere_zero_iff_norm, norm_smul, Complex.norm_real, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne'])`. Establish `e : H (((‖x‖⁻¹ : ℝ) : ℂ) • x) (((‖x‖⁻¹ : ℝ) : ℂ) • x) = ((‖x‖⁻¹ ^ 2 : ℝ) : ℂ) * H x x`. Rewrite using `[LinearMap.map_smulₛₗ, map_smul, LinearMap.smul_apply, conj_ofReal, smul_eq_mul, smul_eq_mul]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite `h1` using `[e, re_ofReal_mul]`. Establish `h2` using `mul_le_mul_of_nonneg_right h1 (sq_nonneg ‖x‖)`. Establish `e2 : ‖x‖⁻¹ ^ 2 * (H x x).re * ‖x‖ ^ 2 = (H x x).re` using `by field_simp`. Rewrite `h2` using `[e2]`. Then use the resulting hypothesis.
-/
theorem exists_mul_norm_sq_le {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    (H : Sesq V) (hH : IsPosHerm H) : ∃ c : ℝ, 0 < c ∧ ∀ x : V, c * ‖x‖ ^ 2 ≤ (H x x).re := by
  have hcont : Continuous fun x : V => (H x x).re := by
    let b := Module.finBasis ℂ V
    have e : (fun x : V => H x x) = fun x => ∑ i, H x (b i) * conj (b.repr x i) := by
      funext x
      conv_lhs => rw [show H x x = H x (∑ i, b.repr x i • b i) by rw [b.sum_repr]]
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [LinearMap.map_smulₛₗ, smul_eq_mul, mul_comm]
    have : Continuous fun x : V => H x x := by
      rw [e]
      refine continuous_finset_sum _ fun i _ => ?_
      have h1 : Continuous fun x : V => H x (b i) :=
        (H.flip (b i)).continuous_of_finiteDimensional
      have h2 : Continuous fun x : V => b.repr x i :=
        (b.coord i).continuous_of_finiteDimensional
      exact h1.mul (continuous_conj.comp h2)
    exact continuous_re.comp this
  haveI : ProperSpace V := FiniteDimensional.proper ℂ V
  obtain ⟨c, hc, hle⟩ : ∃ c : ℝ, 0 < c ∧ ∀ x ∈ Metric.sphere (0 : V) 1, c ≤ (H x x).re := by
    refine (isCompact_sphere (0 : V) 1).exists_forall_le' hcont.continuousOn fun x hx => hH.2 x ?_
    rintro rfl
    simp at hx
  refine ⟨c, hc, fun x => ?_⟩
  by_cases hx : x = 0
  · subst hx
    simp
  have hn : 0 < ‖x‖ := norm_pos_iff.2 hx
  have h1 := hle (((‖x‖⁻¹ : ℝ) : ℂ) • x) (by
    rw [mem_sphere_zero_iff_norm, norm_smul, Complex.norm_real, norm_inv, norm_norm,
      inv_mul_cancel₀ hn.ne'])
  have e : H (((‖x‖⁻¹ : ℝ) : ℂ) • x) (((‖x‖⁻¹ : ℝ) : ℂ) • x) = ((‖x‖⁻¹ ^ 2 : ℝ) : ℂ) * H x x := by
    rw [LinearMap.map_smulₛₗ, map_smul, LinearMap.smul_apply, conj_ofReal, smul_eq_mul, smul_eq_mul]
    push_cast
    ring
  rw [e, re_ofReal_mul] at h1
  have h2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg ‖x‖)
  have e2 : ‖x‖⁻¹ ^ 2 * (H x x).re * ‖x‖ ^ 2 = (H x x).re := by field_simp
  rwa [e2] at h2

/- English proof (translation)
Establish `h1 : t ^ k / k.factorial ≤ Real.exp t` using `Real.pow_div_factorial_le_exp t ht.le k`. Establish `hk : (0 : ℝ) < k.factorial` using `by exact_mod_cast k.factorial_pos`. Rewrite `h1` using `[div_le_iff₀ hk]`. Establish `h2 : -(a * t ^ 2) + C * t + t ≤ (C + 1) ^ 2 / (4 * a)`. Rewrite using `[le_div_iff₀ (by positivity)]`.

Use polynomial arithmetic with `[sq_nonneg (2 * a * t - (C + 1))]`. Rewrite using `[inv_pow, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem exp_le_inv_pow {a : ℝ} (ha : 0 < a) (C : ℝ) (k : ℕ) {t : ℝ} (ht : 0 < t) :
    Real.exp (-(a * t ^ 2) + C * t) ≤ (k.factorial * Real.exp ((C + 1) ^ 2 / (4 * a))) * t⁻¹ ^ k := by
  have h1 : t ^ k / k.factorial ≤ Real.exp t := Real.pow_div_factorial_le_exp t ht.le k
  have hk : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
  rw [div_le_iff₀ hk] at h1
  have h2 : -(a * t ^ 2) + C * t + t ≤ (C + 1) ^ 2 / (4 * a) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (2 * a * t - (C + 1))]
  rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  calc Real.exp (-(a * t ^ 2) + C * t) * t ^ k
      ≤ Real.exp (-(a * t ^ 2) + C * t) * (Real.exp t * k.factorial) := by gcongr
    _ = k.factorial * Real.exp (-(a * t ^ 2) + C * t + t) := by rw [Real.exp_add _ t]; ring
    _ ≤ _ := by gcongr

/- English proof (translation)
Introduce `V _ _ _ H hH Λ _ C`. Take `⟨c, hc, hle⟩` from `exists_mul_norm_sq_le H hH`. Use `letI : NormedSpace ℝ V := NormedSpace.complexToReal`. Use `haveI : FiniteDimensional ℝ V := FiniteDimensional.complexToReal V`. Set `L : Submodule ℤ V` to `AddSubgroup.toIntSubmodule Λ`.

Use `haveI : DiscreteTopology L := ‹DiscreteTopology Λ›`. Establish `hs : Summable fun x : Λ => ‖(x : V)‖⁻¹ ^ (Module.finrank ℤ L + 1)` using `ZLattice.summable_norm_pow_inv L (Module.finrank ℤ L + 1) (Nat.lt_succ_self _)`. Establish `ha : 0 < π / 2 * c` using `by have := Real.pi_pos; positivity`. Use `Summable.of_norm_bounded_eventually (hs.mul_left ((Module.finrank ℤ L + 1).factorial * Real.exp ((C + 1) ^ 2 / (4 * (π / 2 * c))))) ?_` and prove the remaining obligations. Use `filter_upwards [Filter.eventually_cofinite_ne (0 : Λ)] with x hx`.

Establish `hn : 0 < ‖(x : V)‖` using `norm_pos_iff.2 fun h => hx (Subtype.ext h)`. Rewrite using `[Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]`. Use `le_trans (Real.exp_le_exp.2 ?_) (exp_le_inv_pow ha C _ hn)` and prove the remaining obligations. Use `mul_le_mul_of_nonneg_left (hle x) (by have := Real.pi_pos; positivity : 0 ≤ π / 2)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem summable_exp_neg_herm : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (H : Sesq V), IsPosHerm H → ∀ (Λ : AddSubgroup V) [DiscreteTopology Λ] (C : ℝ), Summable (fun x : Λ => Real.exp (-(π / 2) * (H x x).re + C * ‖(x : V)‖)) := by
  intro V _ _ _ H hH Λ _ C
  obtain ⟨c, hc, hle⟩ := exists_mul_norm_sq_le H hH
  letI : NormedSpace ℝ V := NormedSpace.complexToReal
  haveI : FiniteDimensional ℝ V := FiniteDimensional.complexToReal V
  let L : Submodule ℤ V := AddSubgroup.toIntSubmodule Λ
  haveI : DiscreteTopology L := ‹DiscreteTopology Λ›
  have hs : Summable fun x : Λ => ‖(x : V)‖⁻¹ ^ (Module.finrank ℤ L + 1) :=
    ZLattice.summable_norm_pow_inv L (Module.finrank ℤ L + 1) (Nat.lt_succ_self _)
  have ha : 0 < π / 2 * c := by have := Real.pi_pos; positivity
  refine Summable.of_norm_bounded_eventually (hs.mul_left
    ((Module.finrank ℤ L + 1).factorial * Real.exp ((C + 1) ^ 2 / (4 * (π / 2 * c))))) ?_
  filter_upwards [Filter.eventually_cofinite_ne (0 : Λ)] with x hx
  have hn : 0 < ‖(x : V)‖ := norm_pos_iff.2 fun h => hx (Subtype.ext h)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  refine le_trans (Real.exp_le_exp.2 ?_) (exp_le_inv_pow ha C _ hn)
  have := mul_le_mul_of_nonneg_left (hle x) (by have := Real.pi_pos; positivity : 0 ≤ π / 2)
  linarith

end GlobalTheory.UnitaryTheta.GaussSumm
