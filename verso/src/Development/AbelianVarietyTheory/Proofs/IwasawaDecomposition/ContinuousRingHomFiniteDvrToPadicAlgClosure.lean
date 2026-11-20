import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SplitRep
open Formalism.ConjugateSelfDual Formalism.MainNotions.N Polynomial

noncomputable section

namespace GlobalTheory.AdicCont

/- English proof (translation)
Assume the negation of the conclusion as `h`. Use `push_neg at h`. Establish `hn : 0 < P.natDegree`. Break down `Nat.eq_zero_or_pos P.natDegree with h0 | h0` into its components or cases. It suffices to derive a contradiction.

Establish `h1 : P = 1` using `Polynomial.eq_one_of_monic_natDegree_zero hm h0`. Rewrite `hy` using `[h1, eval_one]`. Conclude with `one_ne_zero hy`. Conclude with `h0`. Use `set n := P.natDegree with hndef`.

Establish `hsum` using `eval_eq_sum_range (p := P) y`. Rewrite `hsum` using `[Finset.sum_range_succ, ← hndef, hm.coeff_natDegree, one_mul, hy]`. Establish `hyn : y ^ n = -∑ i ∈ Finset.range n, P.coeff i * y ^ i`. Rewrite using `[eq_neg_iff_add_eq_zero, add_comm]`. Conclude with `hsum.symm`.

Establish `hle : ‖∑ i ∈ Finset.range n, P.coeff i * y ^ i‖ ≤ ‖y‖ ^ (n - 1)`. Apply `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)` to reduce the goal to its premises. Introduce `i hi`. Rewrite using `[norm_mul, norm_pow]`. Establish `hi' : i ≤ n - 1` using `by have := Finset.mem_range.1 hi; omega`.

Combine the equalities or inequalities in the displayed calculation. Establish `h2 : ‖y‖ ^ n ≤ ‖y‖ ^ (n - 1)` using `by rw [← norm_pow, hyn, norm_neg]; exact hle`. Establish `h3 : ‖y‖ ^ (n - 1) < ‖y‖ ^ n` using `pow_lt_pow_right₀ h (by omega)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem norm_le_one_of_monic_root_ultra {K : Type} [NormedField K] [IsUltrametricDist K]
    (P : K[X]) (hm : P.Monic) (hc : ∀ i, ‖P.coeff i‖ ≤ 1) {y : K} (hy : P.eval y = 0) : ‖y‖ ≤ 1 := by
  by_contra h
  push_neg at h
  have hn : 0 < P.natDegree := by
    rcases Nat.eq_zero_or_pos P.natDegree with h0 | h0
    · exfalso
      have h1 : P = 1 := Polynomial.eq_one_of_monic_natDegree_zero hm h0
      rw [h1, eval_one] at hy
      exact one_ne_zero hy
    · exact h0
  set n := P.natDegree with hndef
  have hsum := eval_eq_sum_range (p := P) y
  rw [Finset.sum_range_succ, ← hndef, hm.coeff_natDegree, one_mul, hy] at hsum
  have hyn : y ^ n = -∑ i ∈ Finset.range n, P.coeff i * y ^ i := by
    rw [eq_neg_iff_add_eq_zero, add_comm]; exact hsum.symm
  have hle : ‖∑ i ∈ Finset.range n, P.coeff i * y ^ i‖ ≤ ‖y‖ ^ (n - 1) := by
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
    intro i hi
    rw [norm_mul, norm_pow]
    have hi' : i ≤ n - 1 := by have := Finset.mem_range.1 hi; omega
    calc ‖P.coeff i‖ * ‖y‖ ^ i ≤ 1 * ‖y‖ ^ (n - 1) :=
          mul_le_mul (hc i) (pow_le_pow_right₀ h.le hi') (by positivity) zero_le_one
      _ = _ := one_mul _
  have h2 : ‖y‖ ^ n ≤ ‖y‖ ^ (n - 1) := by rw [← norm_pow, hyn, norm_neg]; exact hle
  have h3 : ‖y‖ ^ (n - 1) < ‖y‖ ^ n := pow_lt_pow_right₀ h (by omega)
  linarith

/- English proof (translation)
Use `set f : O →+* Qbar l := iq.comp (algebraMap O (FractionRing O)) with hf`. Establish `hfz : ∀ z : ℤ_[l], f (algebraMap ℤ_[l] O z) = algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l])` using `hiq`. Establish `h1 : ∀ x : O, ‖f x‖ ≤ 1`. Introduce `x`. Take `⟨p, hpm, hpx⟩` from `Algebra.IsIntegral.isIntegral (R := ℤ_[l]) x`.

Set `g : ℤ_[l] →+* Qbar l` to `f.comp (algebraMap ℤ_[l] O)`. Use `norm_le_one_of_monic_root_ultra (p.map g) (hpm.map g) (fun i => ?_) ?_` and prove the remaining obligations. Rewrite using `[coeff_map]`. Simplify using `only [g, RingHom.comp_apply, hfz, PadicAlgCl.norm_extends]`. Conclude with `(p.coeff i).2`.

Use `congrArg f hpx` as an intermediate fact. Rewrite `this` using `[hom_eval₂, map_zero]`. Rewrite using `[eval_map]`. Conclude with `this`. Establish `hlnorm : ‖f (l : O)‖ = (l : ℝ)⁻¹`.

Rewrite using `[map_natCast, ← map_natCast (algebraMap ℚ_[l] (Qbar l)), PadicAlgCl.norm_extends, Padic.norm_p]`. Establish `hl1 : (1 : ℝ) < l` using `by exact_mod_cast (Fact.out : l.Prime).one_lt`. Establish `hl0 : (l : O) ≠ 0`. Introduce `h`. Rewrite `hlnorm` using `[h, map_zero, norm_zero]`.

Establish `: (0 : ℝ) < (l : ℝ)⁻¹` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible O`. Take `⟨e, u, hlu⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl0 hϖ`. Establish `hr : ‖f ϖ‖ < 1`.

Establish `he : ϖ ^ e = ((u⁻¹ : Oˣ) : O) * (l : O)`. Rewrite using `[hlu, ← mul_assoc, Units.inv_mul, one_mul]`. Establish `hnorm : ‖f ϖ‖ ^ e ≤ (l : ℝ)⁻¹`. Rewrite using `[← norm_pow, ← map_pow, he, map_mul, norm_mul, hlnorm]`. Combine the equalities or inequalities in the displayed calculation.

Establish `hlinv : (l : ℝ)⁻¹ < 1` using `inv_lt_one_of_one_lt₀ hl1`. Assume the negation of the conclusion as `hge`. Use `push_neg at hge`. Establish `: 1 ≤ ‖f ϖ‖ ^ e` using `one_le_pow₀ hge`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hcont : ContinuousAt f 0`. Rewrite using `[ContinuousAt, map_zero, Metric.tendsto_nhds]`. Introduce `ε hε`. Take `⟨n, hn⟩` from `exists_pow_lt_of_lt_one hε hr`. Establish `hopen : IsOpen ((IsLocalRing.maximalIdeal O ^ n : Ideal O) : Set O)` using `(isAdic_iff.1 hO).1 n`.

Use `filter_upwards [hopen.mem_nhds (Ideal.zero_mem _)] with x hx`. Rewrite using `[dist_zero_right]`. Rewrite `hx` using `[hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, SetLike.mem_coe, Ideal.mem_span_singleton']`. Take `⟨a, rfl⟩` from `hx`. Rewrite using `[map_mul, norm_mul, map_pow, norm_pow]`.

Combine the equalities or inequalities in the displayed calculation. Conclude with `continuous_of_continuousAt_zero f hcont`.
-/
theorem continuous_adic (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [TopologicalSpace O] [IsTopologicalRing O]
    (hO : IsAdic (IsLocalRing.maximalIdeal O)) (iq : FractionRing O →+* Qbar l)
    (hiq : ∀ z : ℤ_[l], iq (algebraMap O (FractionRing O) (algebraMap ℤ_[l] O z)) =
      algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l])) :
    Continuous (fun x : O => iq (algebraMap O (FractionRing O) x)) := by
  set f : O →+* Qbar l := iq.comp (algebraMap O (FractionRing O)) with hf
  have hfz : ∀ z : ℤ_[l], f (algebraMap ℤ_[l] O z) = algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l]) := hiq

  have h1 : ∀ x : O, ‖f x‖ ≤ 1 := by
    intro x
    obtain ⟨p, hpm, hpx⟩ := Algebra.IsIntegral.isIntegral (R := ℤ_[l]) x
    let g : ℤ_[l] →+* Qbar l := f.comp (algebraMap ℤ_[l] O)
    refine norm_le_one_of_monic_root_ultra (p.map g) (hpm.map g) (fun i => ?_) ?_
    · rw [coeff_map]
      simp only [g, RingHom.comp_apply, hfz, PadicAlgCl.norm_extends]
      exact (p.coeff i).2
    · have := congrArg f hpx
      rw [hom_eval₂, map_zero] at this
      rw [eval_map]
      exact this

  have hlnorm : ‖f (l : O)‖ = (l : ℝ)⁻¹ := by
    rw [map_natCast, ← map_natCast (algebraMap ℚ_[l] (Qbar l)), PadicAlgCl.norm_extends, Padic.norm_p]
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (l : O) ≠ 0 := by
    intro h
    rw [h, map_zero, norm_zero] at hlnorm
    have : (0 : ℝ) < (l : ℝ)⁻¹ := by positivity
    linarith
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨e, u, hlu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl0 hϖ
  have hr : ‖f ϖ‖ < 1 := by
    have he : ϖ ^ e = ((u⁻¹ : Oˣ) : O) * (l : O) := by
      rw [hlu, ← mul_assoc, Units.inv_mul, one_mul]
    have hnorm : ‖f ϖ‖ ^ e ≤ (l : ℝ)⁻¹ := by
      rw [← norm_pow, ← map_pow, he, map_mul, norm_mul, hlnorm]
      calc ‖f ((u⁻¹ : Oˣ) : O)‖ * (l : ℝ)⁻¹ ≤ 1 * (l : ℝ)⁻¹ :=
            mul_le_mul_of_nonneg_right (h1 _) (by positivity)
        _ = _ := one_mul _
    have hlinv : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl1
    by_contra hge
    push_neg at hge
    have : 1 ≤ ‖f ϖ‖ ^ e := one_le_pow₀ hge
    linarith
  have hcont : ContinuousAt f 0 := by
    rw [ContinuousAt, map_zero, Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hr
    have hopen : IsOpen ((IsLocalRing.maximalIdeal O ^ n : Ideal O) : Set O) := (isAdic_iff.1 hO).1 n
    filter_upwards [hopen.mem_nhds (Ideal.zero_mem _)] with x hx
    rw [dist_zero_right]
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, SetLike.mem_coe, Ideal.mem_span_singleton'] at hx
    obtain ⟨a, rfl⟩ := hx
    rw [map_mul, norm_mul, map_pow, norm_pow]
    calc ‖f a‖ * ‖f ϖ‖ ^ n ≤ 1 * ‖f ϖ‖ ^ n := mul_le_mul_of_nonneg_right (h1 a) (by positivity)
      _ < ε := by rwa [one_mul]
  exact continuous_of_continuousAt_zero f hcont

end GlobalTheory.AdicCont

end
