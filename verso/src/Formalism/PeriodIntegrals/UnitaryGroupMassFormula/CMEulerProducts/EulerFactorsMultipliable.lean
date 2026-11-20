import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CMEulerProducts.StepRegroup

open NumberField

noncomputable section

namespace CMEul.Mult

open Formalism.HermitianLatticesTheory

/- English proof (translation)
Establish `h0 : Ideal.absNorm P ≠ 0`. Rewrite using `[Ne, Ideal.absNorm_eq_zero_iff]`. Conclude with `Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField K)`. Establish `h1 : Ideal.absNorm P ≠ 1`. Rewrite using `[Ne, Ideal.absNorm_eq_one_iff]`.

Conclude with `hP.ne_top`. Use linear arithmetic over natural numbers and integers.
-/
theorem two_le_absNorm {K : Type} [Field K] [NumberField K] (P : Ideal (𝓞 K)) (hP : P.IsMaximal) :
    2 ≤ Ideal.absNorm P := by
  have h0 : Ideal.absNorm P ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField K)
  have h1 : Ideal.absNorm P ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact hP.ne_top
  omega

/- English proof (translation)
Establish `hdvd : ∏ P ∈ s, P.1 ∣ Ideal.span {algebraMap ℤ (𝓞 K) (n : ℤ)}`. Use `Finset.prod_dvd_of_coprime ?_ ?_` and prove the remaining obligations. Introduce `P _ Q _ hPQ`. Conclude with `Ideal.isCoprime_iff_sup_eq.mpr (P.2.coprime_of_ne Q.2 (fun h => hPQ (Subtype.ext h)))`. Introduce `P hP`.

Rewrite using `[Ideal.dvd_span_singleton]`. Establish `hm` using `Ideal.absNorm_mem P.1`. Rewrite `hm` using `[hs P hP]`. Simplify using `using hm`. Establish `h2` using `map_dvd Ideal.absNorm hdvd`.

Rewrite `h2` using `[map_prod, Ideal.absNorm_span_singleton, Algebra.norm_algebraMap]`. Establish `h3 : ∏ P ∈ s, Ideal.absNorm P.1 = n ^ s.card`. Rewrite using `[Finset.prod_congr rfl hs, Finset.prod_const]`. Rewrite `h2` using `[h3, Int.natAbs_pow, Int.natAbs_natCast]`. Conclude with `(Nat.pow_dvd_pow_iff_le_right (by omega)).mp h2`.
-/
theorem card_le {K : Type} [Field K] [NumberField K] (n : ℕ) (hn : 2 ≤ n)
    (s : Finset {P : Ideal (𝓞 K) // P.IsMaximal}) (hs : ∀ P ∈ s, Ideal.absNorm P.1 = n) :
    s.card ≤ Module.finrank ℤ (𝓞 K) := by
  classical
  have hdvd : ∏ P ∈ s, P.1 ∣ Ideal.span {algebraMap ℤ (𝓞 K) (n : ℤ)} := by
    refine Finset.prod_dvd_of_coprime ?_ ?_
    · intro P _ Q _ hPQ
      exact Ideal.isCoprime_iff_sup_eq.mpr (P.2.coprime_of_ne Q.2 (fun h => hPQ (Subtype.ext h)))
    · intro P hP
      rw [Ideal.dvd_span_singleton]
      have hm := Ideal.absNorm_mem P.1
      rw [hs P hP] at hm
      simpa using hm
  have h2 := map_dvd Ideal.absNorm hdvd
  rw [map_prod, Ideal.absNorm_span_singleton, Algebra.norm_algebraMap] at h2
  have h3 : ∏ P ∈ s, Ideal.absNorm P.1 = n ^ s.card := by
    rw [Finset.prod_congr rfl hs, Finset.prod_const]
  rw [h3, Int.natAbs_pow, Int.natAbs_natCast] at h2
  exact (Nat.pow_dvd_pow_iff_le_right (by omega)).mp h2

/- English proof (translation)
Establish `hsum : Summable (fun n : ℕ => (n : ℝ) ^ (-s))` using `Real.summable_nat_rpow.mpr (by linarith)`. Use `summable_of_sum_le (c := (Module.finrank ℤ (𝓞 K) : ℝ) * ∑' n : ℕ, (n : ℝ) ^ (-s)) (fun P => by positivity) ?_` and prove the remaining obligations. Introduce `u`. Establish `hmap : ∀ P ∈ u, Ideal.absNorm P.1 ∈ u.image (fun P => Ideal.absNorm P.1)` using `fun P hP => Finset.mem_image_of_mem _ hP`. Combine the equalities or inequalities in the displayed calculation.

Use `Finset.sum_congr rfl (fun n _ => ?_)` and prove the remaining obligations. Rewrite using `[Finset.sum_congr rfl (fun P hP => by rw [(Finset.mem_filter.mp hP).2]), Finset.sum_const, nsmul_eq_mul]`. Use `_ ≤ ∑ n ∈ u.image (fun P => Ideal.absNorm P.1), (Module.finrank ℤ (𝓞 K) : ℝ) * (n : ℝ) ^ (-s) := by`. Use `Finset.sum_le_sum (fun n hn => ?_)` and prove the remaining obligations. Take `⟨P, hPu, rfl⟩` from `Finset.mem_image.mp hn`.

Establish `hc` using `card_le (Ideal.absNorm P.1) (two_le_absNorm P.1 P.2) (u.filter (fun Q => Ideal.absNorm Q.1 = Ideal.absNorm P.1)) (fun Q hQ => (Finset.mem_filter.mp hQ).2)`. Establish `hc' : ((u.filter (fun Q => Ideal.absNorm Q.1 = Ideal.absNorm P.1)).card : ℝ) ≤ (Module.finrank ℤ (𝓞 K) : ℝ)`. Conclude with `hc` after adjusting the coercions. Conclude with `mul_le_mul_of_nonneg_right hc' (by positivity)`. Use `_ = (Module.finrank ℤ (𝓞 K) : ℝ) * ∑ n ∈ u.image (fun P => Ideal.absNorm P.1), (n : ℝ) ^ (-s) := by`.

Rewrite using `[Finset.mul_sum]`. Use `_ ≤ (Module.finrank ℤ (𝓞 K) : ℝ) * ∑' n : ℕ, (n : ℝ) ^ (-s) := by gcongr`. Conclude with `hsum.sum_le_tsum _ (fun n _ => by positivity)`.
-/
theorem summable_norm_rpow {K : Type} [Field K] [NumberField K] {s : ℝ} (hs : 1 < s) :
    Summable (fun P : {P : Ideal (𝓞 K) // P.IsMaximal} => ((Ideal.absNorm P.1 : ℕ) : ℝ) ^ (-s)) := by
  classical
  have hsum : Summable (fun n : ℕ => (n : ℝ) ^ (-s)) := Real.summable_nat_rpow.mpr (by linarith)
  refine summable_of_sum_le (c := (Module.finrank ℤ (𝓞 K) : ℝ) * ∑' n : ℕ, (n : ℝ) ^ (-s))
    (fun P => by positivity) ?_
  intro u
  have hmap : ∀ P ∈ u, Ideal.absNorm P.1 ∈ u.image (fun P => Ideal.absNorm P.1) :=
    fun P hP => Finset.mem_image_of_mem _ hP
  calc ∑ P ∈ u, ((Ideal.absNorm P.1 : ℕ) : ℝ) ^ (-s)
      = ∑ n ∈ u.image (fun P => Ideal.absNorm P.1),
        ∑ P ∈ u with Ideal.absNorm P.1 = n, ((Ideal.absNorm P.1 : ℕ) : ℝ) ^ (-s) :=
        (Finset.sum_fiberwise_of_maps_to hmap (fun P => ((Ideal.absNorm P.1 : ℕ) : ℝ) ^ (-s))).symm
    _ = ∑ n ∈ u.image (fun P => Ideal.absNorm P.1),
          ((u.filter (fun P => Ideal.absNorm P.1 = n)).card : ℝ) * (n : ℝ) ^ (-s) := by
        refine Finset.sum_congr rfl (fun n _ => ?_)
        rw [Finset.sum_congr rfl (fun P hP => by rw [(Finset.mem_filter.mp hP).2]),
          Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ n ∈ u.image (fun P => Ideal.absNorm P.1),
          (Module.finrank ℤ (𝓞 K) : ℝ) * (n : ℝ) ^ (-s) := by
        refine Finset.sum_le_sum (fun n hn => ?_)
        obtain ⟨P, hPu, rfl⟩ := Finset.mem_image.mp hn
        have hc := card_le (Ideal.absNorm P.1) (two_le_absNorm P.1 P.2)
          (u.filter (fun Q => Ideal.absNorm Q.1 = Ideal.absNorm P.1))
          (fun Q hQ => (Finset.mem_filter.mp hQ).2)
        have hc' : ((u.filter (fun Q => Ideal.absNorm Q.1 = Ideal.absNorm P.1)).card : ℝ) ≤ (Module.finrank ℤ (𝓞 K) : ℝ) := by
          exact_mod_cast hc
        exact mul_le_mul_of_nonneg_right hc' (by positivity)
    _ = (Module.finrank ℤ (𝓞 K) : ℝ) * ∑ n ∈ u.image (fun P => Ideal.absNorm P.1), (n : ℝ) ^ (-s) := by
        rw [Finset.mul_sum]
    _ ≤ (Module.finrank ℤ (𝓞 K) : ℝ) * ∑' n : ℕ, (n : ℝ) ^ (-s) := by
        gcongr
        exact hsum.sum_le_tsum _ (fun n _ => by positivity)

/- English proof (translation)
Establish `h1 : x ^ (-(3 / 2 : ℝ)) ≤ x ^ (-1 : ℝ)` using `Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)`. Rewrite `h1` using `[Real.rpow_neg_one]`. Establish `h2 : x⁻¹ ≤ 1 / 2`. Rewrite using `[one_div]`. Conclude with `inv_anti₀ (by norm_num) hx`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem rpow_le_half {x : ℝ} (hx : 2 ≤ x) : x ^ (-(3 / 2 : ℝ)) ≤ 1 / 2 := by
  have h1 : x ^ (-(3 / 2 : ℝ)) ≤ x ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  rw [Real.rpow_neg_one] at h1
  have h2 : x⁻¹ ≤ 1 / 2 := by
    rw [one_div]
    exact inv_anti₀ (by norm_num) hx
  linarith

/- English proof (translation)
The claim follows from `|eulerFac K M P - 1| ≤ 2 * ((Ideal.absNorm P : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) := by have hN : (2 : ℝ) ≤ ((Ideal.absNorm P : ℕ) : ℝ) := by exact_mod_cast two_le_absNorm P hP set x : ℝ := ((Ideal.absNorm P : ℕ) : ℝ) with hx have hx0 : 0 < x := by linarith have hMz : -(M : ℤ) ≤ -3 := by o …`.
-/
theorem abs_eulerFac_sub_one_le {K : Type} [Field K] [NumberField K] [StarRing K] (M : ℕ)
    (hM : 3 ≤ M) (P : Ideal (𝓞 K)) (hP : P.IsMaximal) :
    |eulerFac K M P - 1| ≤ 2 * ((Ideal.absNorm P : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) := by
  have hN : (2 : ℝ) ≤ ((Ideal.absNorm P : ℕ) : ℝ) := by exact_mod_cast two_le_absNorm P hP
  set x : ℝ := ((Ideal.absNorm P : ℕ) : ℝ) with hx
  have hx0 : 0 < x := by linarith
  have hMz : -(M : ℤ) ≤ -3 := by omega
  have hhalf := rpow_le_half hN
  unfold eulerFac
  split_ifs with h
  ·
    set a : ℝ := (-1 : ℝ) ^ M * Real.sqrt x ^ (-(M : ℤ)) with ha
    have hsq1 : 1 ≤ Real.sqrt x := by
      rw [Real.one_le_sqrt]
      linarith
    have e : Real.sqrt x ^ (-3 : ℤ) = x ^ (-(3 / 2 : ℝ)) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_intCast, ← Real.rpow_mul hx0.le]
      norm_num
    have hab : |a| ≤ x ^ (-(3 / 2 : ℝ)) := by
      rw [ha, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
        abs_of_pos (zpow_pos (by linarith) _), ← e]
      exact zpow_le_zpow_right₀ hsq1 hMz
    have hale : a ≤ 1 / 2 := le_trans (le_abs_self a) (hab.trans hhalf)
    have hne : 1 - a ≠ 0 := by linarith
    have heq : (1 - a)⁻¹ - 1 = a / (1 - a) := by
      field_simp
      ring
    rw [heq, abs_div, abs_of_pos (by linarith : (0 : ℝ) < 1 - a), div_le_iff₀ (by linarith)]
    have h0 : 0 ≤ |a| := abs_nonneg a
    nlinarith [le_abs_self a, neg_abs_le a]
  ·
    set b : ℝ := x ^ (-(M : ℤ)) with hb
    have hb0 : 0 < b := zpow_pos hx0 _
    have hb3 : b ≤ x ^ (-(3 / 2 : ℝ)) := by
      have h1 : b ≤ x ^ (-3 : ℤ) := zpow_le_zpow_right₀ (by linarith) hMz
      have h2 : x ^ (-3 : ℤ) = x ^ (-3 : ℝ) := by
        rw [← Real.rpow_intCast]
        norm_num
      have h3 : x ^ (-3 : ℝ) ≤ x ^ (-(3 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      linarith
    have hbh : b ≤ 1 / 2 := hb3.trans hhalf
    have hpos : 0 < 1 - b := by linarith
    have hle1 : 1 - b ≤ 1 := by linarith
    have hlo : 1 ≤ (1 - b) ^ (-(1 : ℝ) / 2) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hpos hle1 (by norm_num)
    have hup1 : (1 - b) ^ (-(1 : ℝ) / 2) ≤ (1 - b) ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hpos hle1 (by norm_num)
    rw [Real.rpow_neg_one] at hup1
    have hup2 : (1 - b)⁻¹ ≤ 1 + 2 * b := by
      rw [inv_eq_one_div, div_le_iff₀ hpos]
      nlinarith
    rw [abs_of_nonneg (by linarith)]
    linarith

end CMEul.Mult

/- English proof (translation)
Introduce `K _ _ _ M hM`. Establish `hs : Summable (fun P : {P : Ideal (𝓞 K) // P.IsMaximal} => Formalism.HermitianLatticesTheory.eulerFac K M P.1 - 1)`. Use `Summable.of_norm_bounded ((CMEul.Mult.summable_norm_rpow (K := K) (s := 3 / 2) (by norm_num)).mul_left 2) ?_` and prove the remaining obligations. Introduce `P`. Rewrite using `[Real.norm_eq_abs]`.

Conclude with `CMEul.Mult.abs_eulerFac_sub_one_le M hM P.1 P.2`. Simplify using `using Real.multipliable_one_add_of_summable hs`.
-/
theorem euler_factors_multipliable : CMEul.StepMult := by
  intro K _ _ _ M hM
  have hs : Summable (fun P : {P : Ideal (𝓞 K) // P.IsMaximal} => Formalism.HermitianLatticesTheory.eulerFac K M P.1 - 1) := by
    refine Summable.of_norm_bounded
      ((CMEul.Mult.summable_norm_rpow (K := K) (s := 3 / 2) (by norm_num)).mul_left 2) ?_
    intro P
    rw [Real.norm_eq_abs]
    exact CMEul.Mult.abs_eulerFac_sub_one_le M hM P.1 P.2
  simpa using Real.multipliable_one_add_of_summable hs
