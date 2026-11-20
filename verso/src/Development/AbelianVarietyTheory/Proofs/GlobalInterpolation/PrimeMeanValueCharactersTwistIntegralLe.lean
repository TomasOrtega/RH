import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ZerosDisc
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IntegralNormSqLp
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.BrunTitchmarshExistsConstStatement
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical

namespace GlobalTheory.PrimeMeanValue

/- English proof (translation)
Establish `hi : ∀ i ∈ s, Integrable (f i) μ` using `fun i hi => by`. Use `hG.mono' (hm i) ?_` and prove the remaining obligations. Use `filter_upwards [h0, h] with x hx0 hx`. Rewrite using `[Real.norm_of_nonneg (hx0 i)]`. Conclude with `(Finset.single_le_sum (f := fun i => f i x) (fun j _ => hx0 j) hi).trans hx`.

Rewrite using `[← integral_finsetSum s hi]`. Conclude with `integral_mono_ae (integrable_finsetSum s hi) hG h`.
-/
theorem sum_integral_le {ι : Type*} (s : Finset ι) (μ : Measure ℝ) (f : ι → ℝ → ℝ) (G : ℝ → ℝ)
    (hm : ∀ i, AEStronglyMeasurable (f i) μ) (h0 : ∀ᵐ x ∂μ, ∀ i, 0 ≤ f i x)
    (hG : Integrable G μ) (h : ∀ᵐ x ∂μ, ∑ i ∈ s, f i x ≤ G x) :
    ∑ i ∈ s, ∫ x, f i x ∂μ ≤ ∫ x, G x ∂μ := by
  have hi : ∀ i ∈ s, Integrable (f i) μ := fun i hi => by
    refine hG.mono' (hm i) ?_
    filter_upwards [h0, h] with x hx0 hx
    rw [Real.norm_of_nonneg (hx0 i)]
    exact (Finset.single_le_sum (f := fun i => f i x) (fun j _ => hx0 j) hi).trans hx
  rw [← integral_finsetSum s hi]
  exact integral_mono_ae (integrable_finsetSum s hi) hG h

/- English proof (translation)
Rewrite using `[Set.indicator_apply]`. Use `if_congr ?_ rfl rfl` and prove the remaining obligations. Rewrite using `[Set.mem_Ico, div_le_iff₀ (Real.exp_pos δ), and_comm]`.
-/
theorem kernel_eq (n δ x : ℝ) :
    (if x < n ∧ n ≤ x * Real.exp δ then 1 / x else 0) =
      (Set.Ico (n / Real.exp δ) n).indicator (fun x => 1 / x) x := by
  rw [Set.indicator_apply]
  refine if_congr ?_ rfl rfl
  rw [Set.mem_Ico, div_le_iff₀ (Real.exp_pos δ), and_comm]

/- English proof (translation)
Repeatedly rewrite using `[kernel_eq]`. Establish `he` using `Real.exp_pos δ`. Establish `ha : 0 < n / Real.exp δ` using `by positivity`. Establish `hle : n / Real.exp δ ≤ n` using `div_le_self hn.le (Real.one_le_exp hδ)`. Establish `hsub : Set.Ico (n / Real.exp δ) n ⊆ Set.Ioi 0` using `fun x hx => lt_of_lt_of_le ha hx.1`.

Prove the components needed by the constructor for the conclusion. Use `Integrable.integrableOn ?_` and prove the remaining obligations. Rewrite using `[integrable_indicator_iff measurableSet_Ico]`. Use `IntegrableOn.mono_set ?_ Set.Ico_subset_Icc_self` and prove the remaining obligations. Use `ContinuousOn.integrableOn_Icc ?_` and prove the remaining obligations.

Conclude with `continuousOn_const.div continuousOn_id fun x hx => (lt_of_lt_of_le ha hx.1).ne'`. Rewrite using `[setIntegral_indicator measurableSet_Ico, Set.inter_eq_right.2 hsub, integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle, integral_one_div_of_pos ha hn]`. Rewrite using `[div_div_cancel₀ hn.ne', Real.log_exp]`.
-/
theorem kernel_integral (n δ : ℝ) (hn : 0 < n) (hδ : 0 ≤ δ) :
    IntegrableOn (fun x : ℝ => if x < n ∧ n ≤ x * Real.exp δ then 1 / x else 0) (Set.Ioi 0) ∧
    ∫ x in Set.Ioi (0 : ℝ), (if x < n ∧ n ≤ x * Real.exp δ then 1 / x else 0) = δ := by
  simp_rw [kernel_eq]
  have he := Real.exp_pos δ
  have ha : 0 < n / Real.exp δ := by positivity
  have hle : n / Real.exp δ ≤ n := div_le_self hn.le (Real.one_le_exp hδ)
  have hsub : Set.Ico (n / Real.exp δ) n ⊆ Set.Ioi 0 := fun x hx => lt_of_lt_of_le ha hx.1
  constructor
  · refine Integrable.integrableOn ?_
    rw [integrable_indicator_iff measurableSet_Ico]
    refine IntegrableOn.mono_set ?_ Set.Ico_subset_Icc_self
    refine ContinuousOn.integrableOn_Icc ?_
    exact continuousOn_const.div continuousOn_id fun x hx => (lt_of_lt_of_le ha hx.1).ne'
  · rw [setIntegral_indicator measurableSet_Ico, Set.inter_eq_right.2 hsub,
      integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle,
      integral_one_div_of_pos ha hn]
    rw [div_div_cancel₀ hn.ne', Real.log_exp]

/- English proof (translation)
Establish `h1 : χ u * χ u⁻¹ = 1` using `by rw [← map_mul, ZMod.mul_inv_of_unit u hu, map_one]`. Establish `h2 : ‖χ u‖ = 1`. Take `⟨v, rfl⟩` from `hu`. Conclude with `χ.unit_norm_eq_one v`. Establish `h3 : χ u * (starRingEnd ℂ) (χ u) = 1`.

Rewrite using `[Complex.mul_conj, Complex.normSq_eq_norm_sq, h2]`. Simplify using the standard rewrite rules. Establish `h0 : χ u ≠ 0` using `left_ne_zero_of_mul_eq_one h1`. Conclude with `mul_left_cancel₀ h0 (h3.trans h1.symm)`.
-/
theorem conj_char {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {u : ZMod q} (hu : IsUnit u) :
    (starRingEnd ℂ) (χ u) = χ u⁻¹ := by
  have h1 : χ u * χ u⁻¹ = 1 := by rw [← map_mul, ZMod.mul_inv_of_unit u hu, map_one]
  have h2 : ‖χ u‖ = 1 := by
    obtain ⟨v, rfl⟩ := hu
    exact χ.unit_norm_eq_one v
  have h3 : χ u * (starRingEnd ℂ) (χ u) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, h2]; simp
  have h0 : χ u ≠ 0 := left_ne_zero_of_mul_eq_one h1
  exact mul_left_cancel₀ h0 (h3.trans h1.symm)

/- English proof (translation)
Establish `e1 : ((∑ χ : DirichletCharacter ℂ q, ‖∑ n ∈ S, a n * χ (n : ZMod q)‖ ^ 2 : ℝ) : ℂ) = ∑ n ∈ S, ∑ m ∈ S, (starRingEnd ℂ) (a n) * a m * (if (n : ZMod q) = (m : ZMod q) then (q.totient : ℂ) else 0)`. Use `push_cast`. Establish `: ∀ χ : DirichletCharacter ℂ q, ((‖∑ n ∈ S, a n * χ (n : ZMod q)‖ : ℝ) : ℂ) ^ 2 = ∑ n ∈ S, ∑ m ∈ S, (starRingEnd ℂ) (a n) * a m * (χ (n : ZMod q)⁻¹ * χ (m : ZMod q))`. Introduce `χ`. Rewrite using `[← Complex.conj_mul', map_sum, Finset.sum_mul_sum]`.

Use `Finset.sum_congr rfl fun n hn => Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, conj_char χ ((ZMod.isUnit_iff_coprime n q).2 (hS n hn))]`. Expand and normalize the polynomial expressions, which then agree. Repeatedly rewrite using `[this]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun n hn => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.mul_sum, DirichletCharacter.sum_char_inv_mul_char_eq ℂ ((ZMod.isUnit_iff_coprime n q).2 (hS n hn))]`. Use `set g : ℕ → ℕ → ℝ := fun n m => if (n : ZMod q) = (m : ZMod q) then (q.totient : ℝ) else 0 with hg`.

Establish `hsym : ∀ n m, g n m = g m n` using `fun n m => by simp only [hg, eq_comm]`. Apply the tactic sequence `have hg0 : ∀ n m, 0 ≤ g n m := fun n m => by simp only [hg]; split_ifs <;> positivity`. Establish `e2 : ∑ χ : DirichletCharacter ℂ q, ‖∑ n ∈ S, a n * χ (n : ZMod q)‖ ^ 2 ≤ ∑ n ∈ S, ∑ m ∈ S, (‖a n‖ ^ 2 * g n m / 2 + ‖a m‖ ^ 2 * g n m / 2)`. Use `(le_abs_self _).trans ?_` and prove the remaining obligations. Rewrite using `[← Real.norm_eq_abs, ← Complex.norm_real, e1]`.

Use `(norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)` and prove the remaining obligations. Use `(norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => ?_)` and prove the remaining obligations. Establish `: ‖(if (n : ZMod q) = (m : ZMod q) then (q.totient : ℂ) else 0)‖ = g n m`. Apply the tactic sequence `simp only [hg]; split_ifs <;> simp`. Rewrite using `[norm_mul, norm_mul, this, Complex.norm_conj]`.

Use `hg0 n m` as an intermediate fact. Use polynomial arithmetic with `[mul_nonneg this (sq_nonneg (‖a n‖ - ‖a m‖))]`. Use `e2.trans (le_of_eq ?_)` and prove the remaining obligations. Repeatedly rewrite using `[Finset.sum_add_distrib]`. Rewrite using `[Finset.sum_comm (f := fun n m => ‖a m‖ ^ 2 * g n m / 2), ← Finset.sum_add_distrib]`.

Use `Finset.sum_congr rfl fun n _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_add_distrib, Finset.card_filter]`. Use `push_cast`. Rewrite using `[Finset.mul_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations.

Rewrite using `[hsym n m]`. Simplify using `only [hg, ZMod.natCast_eq_natCast_iff]`. Apply the tactic sequence `split_ifs <;> ring`.
-/
theorem orth (q : ℕ) [NeZero q] (S : Finset ℕ) (a : ℕ → ℂ) (hS : ∀ n ∈ S, Nat.Coprime n q) :
    ∑ χ : DirichletCharacter ℂ q, ‖∑ n ∈ S, a n * χ (n : ZMod q)‖ ^ 2 ≤
      ∑ n ∈ S, (q.totient : ℝ) * ((S.filter (fun m => m ≡ n [MOD q])).card : ℝ) * ‖a n‖ ^ 2 := by
  have e1 : ((∑ χ : DirichletCharacter ℂ q, ‖∑ n ∈ S, a n * χ (n : ZMod q)‖ ^ 2 : ℝ) : ℂ) =
      ∑ n ∈ S, ∑ m ∈ S, (starRingEnd ℂ) (a n) * a m *
        (if (n : ZMod q) = (m : ZMod q) then (q.totient : ℂ) else 0) := by
    push_cast
    have : ∀ χ : DirichletCharacter ℂ q, ((‖∑ n ∈ S, a n * χ (n : ZMod q)‖ : ℝ) : ℂ) ^ 2 =
        ∑ n ∈ S, ∑ m ∈ S, (starRingEnd ℂ) (a n) * a m * (χ (n : ZMod q)⁻¹ * χ (m : ZMod q)) := by
      intro χ
      rw [← Complex.conj_mul', map_sum, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun n hn => Finset.sum_congr rfl fun m _ => ?_
      rw [map_mul, conj_char χ ((ZMod.isUnit_iff_coprime n q).2 (hS n hn))]
      ring
    simp_rw [this]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← Finset.mul_sum, DirichletCharacter.sum_char_inv_mul_char_eq ℂ
      ((ZMod.isUnit_iff_coprime n q).2 (hS n hn))]
  set g : ℕ → ℕ → ℝ := fun n m => if (n : ZMod q) = (m : ZMod q) then (q.totient : ℝ) else 0
    with hg
  have hsym : ∀ n m, g n m = g m n := fun n m => by simp only [hg, eq_comm]
  have hg0 : ∀ n m, 0 ≤ g n m := fun n m => by simp only [hg]; split_ifs <;> positivity
  have e2 : ∑ χ : DirichletCharacter ℂ q, ‖∑ n ∈ S, a n * χ (n : ZMod q)‖ ^ 2 ≤
      ∑ n ∈ S, ∑ m ∈ S, (‖a n‖ ^ 2 * g n m / 2 + ‖a m‖ ^ 2 * g n m / 2) := by
    refine (le_abs_self _).trans ?_
    rw [← Real.norm_eq_abs, ← Complex.norm_real, e1]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => ?_)
    have : ‖(if (n : ZMod q) = (m : ZMod q) then (q.totient : ℂ) else 0)‖ = g n m := by
      simp only [hg]; split_ifs <;> simp
    rw [norm_mul, norm_mul, this, Complex.norm_conj]
    have := hg0 n m
    nlinarith [mul_nonneg this (sq_nonneg (‖a n‖ - ‖a m‖))]
  refine e2.trans (le_of_eq ?_)
  simp_rw [Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun n m => ‖a m‖ ^ 2 * g n m / 2), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← Finset.sum_add_distrib, Finset.card_filter]
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [hsym n m]
  simp only [hg, ZMod.natCast_eq_natCast_iff]
  split_ifs <;> ring

/- English proof (translation)
Rewrite using `[primesIoc, Finset.mem_filter, Finset.mem_Ioc, Nat.floor_lt hx]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨h1, h2⟩, h3⟩`. Conclude with `⟨h1, (Nat.le_floor_iff' h3.ne_zero).1 h2, h3⟩`. Introduce and unpack `⟨h1, h2, h3⟩`.

Conclude with `⟨⟨h1, Nat.le_floor h2⟩, h3⟩`.
-/
theorem mem_primesIoc {x y : ℝ} (hx : 0 ≤ x) {p : ℕ} :
    p ∈ primesIoc x y ↔ x < p ∧ (p : ℝ) ≤ y ∧ p.Prime := by
  rw [primesIoc, Finset.mem_filter, Finset.mem_Ioc, Nat.floor_lt hx]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, (Nat.le_floor_iff' h3.ne_zero).1 h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, Nat.le_floor h2⟩, h3⟩

/- English proof (translation)
Establish `hq : 1 ≤ q` using `Nat.pos_of_ne_zero (NeZero.ne q)`. Establish `hq' : (1 : ℝ) ≤ q` using `by exact_mod_cast hq`. Establish `hT0 : 0 < T` using `by linarith`. Establish `hδ : 0 ≤ 1 / T` using `by positivity`. Establish `hqT : (q : ℝ) ≤ q * T` using `le_mul_of_one_le_right (by positivity) hT`.

Establish `hcop : ∀ n ∈ S, Nat.Coprime n q` using `fun n hn => by`. Take `⟨hp, h1, -, -⟩` from `hS n hn`. Establish `: (q : ℝ) < n` using `by nlinarith`. Establish `hlt : q < n` using `by exact_mod_cast this`. Conclude with `(Nat.Prime.coprime_iff_not_dvd hp).2 (Nat.not_dvd_of_pos_of_lt hq hlt)`.

Establish `e3` using `Real.abs_exp_sub_one_le (x := 1 / T) (by rw [abs_of_nonneg hδ, div_le_one hT0]; exact hT)`. Rewrite `e3` using `[abs_of_nonneg hδ]`. Establish `e4 : Real.exp (1 / T) - 1 ≤ 2 * (1 / T)` using `(le_abs_self _).trans e3`. Establish `e5 : x * Real.exp (1 / T) ≤ x + 2 * x / T`. Use `mul_le_mul_of_nonneg_left e4 hx.le` as an intermediate fact.

Establish `e : x * (2 * (1 / T)) = 2 * x / T` using `by ring`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `e6 : 2 * x / T ≤ 2 * x` using `div_le_self (by positivity) hT`. Use `(orth q S a hcop).trans (Finset.sum_le_sum fun n hn => ?_)` and prove the remaining obligations. Take `⟨hp, h1, h2, h3⟩` from `hS n hn`.

Use `mul_le_mul_of_nonneg_right ?_ (by positivity)` and prove the remaining obligations. Establish `hn3 : (n : ℝ) ≤ 3 * x` using `by linarith`. Establish `hx3 : (2 * q * T) ^ 2 ≤ 3 * x` using `by linarith`. Establish `hY : 2 * (q : ℝ) ≤ 2 * x / T`. Rewrite using `[le_div_iff₀ hT0]`.

Use the polynomial consequences of the given equalities and inequalities. Establish `hb` using `hB q n x (2 * x / T) hq (hcop n hn) hx.le hY`. Establish `hsub : S.filter (fun m => m ≡ n [MOD q]) ⊆ (primesIoc x (x + 2 * x / T)).filter (fun p => p ≡ n [MOD q])`. Use `Finset.filter_subset_filter _ fun m hm => ?_` and prove the remaining obligations. Take `⟨hp', -, h2', h3'⟩` from `hS m hm`.

Conclude with `(mem_primesIoc hx.le).2 ⟨h2', h3'.trans e5, hp'⟩`. Establish `hc : ((S.filter (fun m => m ≡ n [MOD q])).card : ℝ) ≤ (((primesIoc x (x + 2 * x / T)).filter (fun p => p ≡ n [MOD q])).card : ℝ)`. Conclude with `Finset.card_le_card hsub` after adjusting the coercions. Establish `hφ : (0 : ℝ) < q.totient` using `by exact_mod_cast Nat.totient_pos.2 hq`. Establish `hn1 : (1 : ℝ) < n` using `by exact_mod_cast hp.one_lt`.

Establish `hlog : 0 < Real.log n` using `Real.log_pos hn1`. Establish `hsq : (n : ℝ) ≤ (2 * x / T / q) ^ 2`. Rewrite using `[div_div, div_pow, le_div_iff₀ (by positivity)]`. Establish `h4 : (T * q) ^ 2 ≤ 3 * x / 4` using `by nlinarith`. Combine the equalities or inequalities in the displayed calculation.

Establish `hl : Real.log n / 2 ≤ Real.log (2 * x / T / q)`. Use `Real.log_le_log (by linarith) hsq` as an intermediate fact. Rewrite `this` using `[Real.log_pow]`. Move the coercions through the operations in `at this`. Combine the linear equalities and inequalities to obtain the conclusion.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem window (C : ℝ) (hC : 0 < C)
    (hB : ∀ (q a : ℕ) (x y : ℝ), 1 ≤ q → Nat.Coprime a q → 0 ≤ x → 2 * (q : ℝ) ≤ y →
      (((primesIoc x (x + y)).filter (fun p => p ≡ a [MOD q])).card : ℝ) ≤
        C * y / (q.totient * Real.log (y / q)))
    (q : ℕ) [NeZero q] (T N x : ℝ) (a : ℕ → ℂ) (S : Finset ℕ) (hT : 1 ≤ T)
    (hN : (2 * q * T) ^ 2 ≤ N) (hx : 0 < x)
    (hS : ∀ n ∈ S, n.Prime ∧ N < n ∧ x < n ∧ (n : ℝ) ≤ x * Real.exp (1 / T)) :
    ∑ χ : DirichletCharacter ℂ q, ‖∑ n ∈ S, a n * χ (n : ZMod q)‖ ^ 2 ≤
      ∑ n ∈ S, 4 * C * n / (T * Real.log n) * ‖a n‖ ^ 2 := by
  have hq : 1 ≤ q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hT0 : 0 < T := by linarith
  have hδ : 0 ≤ 1 / T := by positivity
  have hqT : (q : ℝ) ≤ q * T := le_mul_of_one_le_right (by positivity) hT
  have hcop : ∀ n ∈ S, Nat.Coprime n q := fun n hn => by
    obtain ⟨hp, h1, -, -⟩ := hS n hn
    have : (q : ℝ) < n := by nlinarith
    have hlt : q < n := by exact_mod_cast this
    exact (Nat.Prime.coprime_iff_not_dvd hp).2 (Nat.not_dvd_of_pos_of_lt hq hlt)
  have e3 := Real.abs_exp_sub_one_le (x := 1 / T)
    (by rw [abs_of_nonneg hδ, div_le_one hT0]; exact hT)
  rw [abs_of_nonneg hδ] at e3
  have e4 : Real.exp (1 / T) - 1 ≤ 2 * (1 / T) := (le_abs_self _).trans e3
  have e5 : x * Real.exp (1 / T) ≤ x + 2 * x / T := by
    have := mul_le_mul_of_nonneg_left e4 hx.le
    have e : x * (2 * (1 / T)) = 2 * x / T := by ring
    linarith
  have e6 : 2 * x / T ≤ 2 * x := div_le_self (by positivity) hT
  refine (orth q S a hcop).trans (Finset.sum_le_sum fun n hn => ?_)
  obtain ⟨hp, h1, h2, h3⟩ := hS n hn
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  have hn3 : (n : ℝ) ≤ 3 * x := by linarith
  have hx3 : (2 * q * T) ^ 2 ≤ 3 * x := by linarith
  have hY : 2 * (q : ℝ) ≤ 2 * x / T := by
    rw [le_div_iff₀ hT0]; nlinarith
  have hb := hB q n x (2 * x / T) hq (hcop n hn) hx.le hY
  have hsub : S.filter (fun m => m ≡ n [MOD q]) ⊆
      (primesIoc x (x + 2 * x / T)).filter (fun p => p ≡ n [MOD q]) := by
    refine Finset.filter_subset_filter _ fun m hm => ?_
    obtain ⟨hp', -, h2', h3'⟩ := hS m hm
    exact (mem_primesIoc hx.le).2 ⟨h2', h3'.trans e5, hp'⟩
  have hc : ((S.filter (fun m => m ≡ n [MOD q])).card : ℝ) ≤
      (((primesIoc x (x + 2 * x / T)).filter (fun p => p ≡ n [MOD q])).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.2 hq
  have hn1 : (1 : ℝ) < n := by exact_mod_cast hp.one_lt
  have hlog : 0 < Real.log n := Real.log_pos hn1
  have hsq : (n : ℝ) ≤ (2 * x / T / q) ^ 2 := by
    rw [div_div, div_pow, le_div_iff₀ (by positivity)]
    have h4 : (T * q) ^ 2 ≤ 3 * x / 4 := by nlinarith
    calc (n : ℝ) * (T * q) ^ 2 ≤ (3 * x) * (3 * x / 4) := by gcongr
      _ ≤ (2 * x) ^ 2 := by nlinarith
  have hl : Real.log n / 2 ≤ Real.log (2 * x / T / q) := by
    have := Real.log_le_log (by linarith) hsq
    rw [Real.log_pow] at this
    push_cast at this
    linarith
  calc (q.totient : ℝ) * ((S.filter (fun m => m ≡ n [MOD q])).card : ℝ)
      ≤ q.totient * (C * (2 * x / T) / (q.totient * Real.log (2 * x / T / q))) :=
        mul_le_mul_of_nonneg_left (hc.trans hb) hφ.le
    _ ≤ q.totient * (C * (2 * n / T) / (q.totient * (Real.log n / 2))) := by gcongr
    _ = 4 * C * n / (T * Real.log n) := by field_simp; ring

/- English proof (translation)
Take `⟨C, hC, hG⟩` from `GlobalTheory.GallagherLemma.gallagher`. Take `⟨B, hB0, hB⟩` from `GlobalTheory.T.brunTitchmarsh_exists_const`. Use `⟨C * (4 * B), by positivity, fun q _ T N y a hT hN => ?_⟩` and prove the remaining obligations. Establish `hT0 : 0 < T` using `by linarith`. Establish `hδ : 0 ≤ 1 / T` using `by positivity`.

Establish `hN0 : 0 ≤ N` using `(sq_nonneg _).trans hN`. Use `set P := primesIoc N y with hP`. Establish `hmem : ∀ p ∈ P, N < p ∧ (p : ℝ) ≤ y ∧ p.Prime` using `fun p hp => (mem_primesIoc hN0).1 hp`. Establish `hsub : P ⊆ Finset.Icc 1 ⌊y⌋₊` using `fun p hp => Finset.mem_Icc.2 ⟨(hmem p hp).2.2.one_le, Nat.le_floor (hmem p hp).2.1⟩`. Establish `hgal : ∀ χ : DirichletCharacter ℂ q, (∫ t in (-T)..T, ‖∑ p ∈ P, a p * χ (p : ZMod q) * (p : ℂ) ^ (-(t * I))‖ ^ 2) ≤ C * T ^ 2 * ∫ x in Set.Ioi (0 : ℝ), ‖∑ n ∈ P.filter (fun n : ℕ => x < n ∧ (n : ℝ) ≤ x * Real.exp (1 / T)), a n * χ (n : ZMod q)‖ ^ 2 / x`.

Introduce `χ`. Establish `h` using `hG ⌊y⌋₊ (fun n => if n ∈ P then a n * χ (n : ZMod q) else 0) T hT`. Establish `r1 : ∀ t : ℝ, ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, (if n ∈ P then a n * χ (n : ZMod q) else 0) * (n : ℂ) ^ (-(t * I)) = ∑ p ∈ P, a p * χ (p : ZMod q) * (p : ℂ) ^ (-(t * I))`. Introduce `t`. Repeatedly rewrite using `[ite_mul, zero_mul]`.

Rewrite using `[Finset.sum_ite_mem, Finset.inter_eq_right.2 hsub]`. Establish `r2 : ∀ x : ℝ, ∑ n ∈ (Finset.Icc 1 ⌊y⌋₊).filter (fun n : ℕ => x < n ∧ (n : ℝ) ≤ x * Real.exp (1 / T)), (if n ∈ P then a n * χ (n : ZMod q) else 0) = ∑ n ∈ P.filter (fun n : ℕ => x < n ∧ (n : ℝ) ≤ x * Real.exp (1 / T)), a n * χ (n : ZMod q)`. Introduce `x`. Rewrite using `[Finset.sum_ite_mem, Finset.filter_inter, Finset.inter_eq_right.2 hsub]`. Rewrite `h` using `[r1, r2]`.

Conclude with `h`. Use `(Finset.sum_le_sum fun χ _ => hgal χ).trans ?_` and prove the remaining obligations. Rewrite using `[← Finset.mul_sum]`. Use `set w : ℕ → ℝ := fun n => 4 * B * n / (T * Real.log n) * ‖a n‖ ^ 2 with hw`. Establish `hk : ∀ n ∈ P, (0 : ℝ) < n` using `fun n hn => by exact_mod_cast (hmem n hn).2.2.pos`.

Establish `hint : ∀ n ∈ P, Integrable (fun x : ℝ => w n * (if x < n ∧ (n : ℝ) ≤ x * Real.exp (1 / T) then 1 / x else 0)) (volume.restrict (Set.Ioi 0))` using `fun n hn => (kernel_integral n (1 / T) (hk n hn) hδ).1.const_mul _`. Establish `key` using `sum_integral_le (Finset.univ : Finset (DirichletCharacter ℂ q)) (volume.restrict (Set.Ioi 0)) (fun χ x => ‖∑ n ∈ P.filter (fun n : ℕ => x < n ∧ (n : ℝ) ≤ x * Real.exp (1 / T)), a n * χ (n : ZMod q)‖ ^ 2 / x) (fun x => ∑ n ∈ P, w n * (if x < n ∧ (n : ℝ) ≤ x * Real.exp (1 / T) then …`. Use `Measurable.aestronglyMeasurable ?_` and prove the remaining obligations. Repeatedly rewrite using `[Finset.sum_filter]`. Use `Measurable.div (Measurable.pow_const (Measurable.norm ?_) 2) measurable_id` and prove the remaining obligations.

Use `Finset.measurable_sum _ fun n _ => Measurable.ite ?_ measurable_const measurable_const` and prove the remaining obligations. Conclude with `(measurableSet_lt measurable_id measurable_const).inter (measurableSet_le measurable_const (measurable_id.mul_const _)))`. Use the proof step `(by filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx p`. Establish `hx' : 0 < x` using `hx`. Use the proof step `positivity)`.

Use the proof step `(integrable_finsetSum _ hint)`. Use the proof step `(by filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx`. Establish `hx' : 0 < x` using `hx`. Establish `hwin` using `window B hB0 hB q T N x a (P.filter (fun n : ℕ => x < n ∧ (n : ℝ) ≤ x * Real.exp (1 / T))) hT hN hx' (fun n hn => by`. Take `⟨h1, h2⟩` from `Finset.mem_filter.1 hn`.

Conclude with `⟨(hmem n h1).2.2, (hmem n h1).1, h2.1, h2.2⟩)`. Rewrite using `[← Finset.sum_div]`. Use `(div_le_div_of_nonneg_right hwin hx'.le).trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[Finset.sum_filter, Finset.sum_div]`. Use `Finset.sum_congr rfl fun n _ => ?_` and prove the remaining obligations.

Use `split_ifs`. Rewrite using `[mul_one_div]`. Use the proof step `simp)`. Use `(mul_le_mul_of_nonneg_left key (by positivity)).trans ?_` and prove the remaining obligations. Rewrite using `[integral_finsetSum _ hint, mul_assoc, mul_assoc, Finset.mul_sum, Finset.mul_sum _ _ (4 * B)]`.

Use `mul_le_mul_of_nonneg_left (le_of_eq (Finset.sum_congr rfl fun n hn => ?_)) hC.le` and prove the remaining obligations. Rewrite using `[integral_const_mul, (kernel_integral n (1 / T) (hk n hn) hδ).2]`. Simplify using `only [hw]`. Establish `hlog : 0 < Real.log n` using `Real.log_pos (by exact_mod_cast (hmem n hn).2.2.one_lt)`. Clear the denominators using the available nonvanishing facts.
-/
theorem prime_mean_value : ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (T N y : ℝ) (a : ℕ → ℂ), 1 ≤ T →
    (2 * q * T) ^ 2 ≤ N → ∑ χ : DirichletCharacter ℂ q, (∫ t in (-T)..T,
      ‖∑ p ∈ primesIoc N y, a p * χ (p : ZMod q) * (p : ℂ) ^ (-(t * I))‖ ^ 2) ≤
      C * ∑ p ∈ primesIoc N y, (p : ℝ) * ‖a p‖ ^ 2 / Real.log p := by
  obtain ⟨C, hC, hG⟩ := GlobalTheory.GallagherLemma.gallagher
  obtain ⟨B, hB0, hB⟩ := GlobalTheory.T.brunTitchmarsh_exists_const
  refine ⟨C * (4 * B), by positivity, fun q _ T N y a hT hN => ?_⟩
  have hT0 : 0 < T := by linarith
  have hδ : 0 ≤ 1 / T := by positivity
  have hN0 : 0 ≤ N := (sq_nonneg _).trans hN
  set P := primesIoc N y with hP
  have hmem : ∀ p ∈ P, N < p ∧ (p : ℝ) ≤ y ∧ p.Prime := fun p hp => (mem_primesIoc hN0).1 hp
  have hsub : P ⊆ Finset.Icc 1 ⌊y⌋₊ := fun p hp =>
    Finset.mem_Icc.2 ⟨(hmem p hp).2.2.one_le, Nat.le_floor (hmem p hp).2.1⟩
  have hgal : ∀ χ : DirichletCharacter ℂ q, (∫ t in (-T)..T,
      ‖∑ p ∈ P, a p * χ (p : ZMod q) * (p : ℂ) ^ (-(t * I))‖ ^ 2) ≤
      C * T ^ 2 * ∫ x in Set.Ioi (0 : ℝ), ‖∑ n ∈ P.filter
        (fun n : ℕ => x < n ∧ (n : ℝ) ≤ x * Real.exp (1 / T)), a n * χ (n : ZMod q)‖ ^ 2 / x := by
    intro χ
    have h := hG ⌊y⌋₊ (fun n => if n ∈ P then a n * χ (n : ZMod q) else 0) T hT
    have r1 : ∀ t : ℝ, ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, (if n ∈ P then a n * χ (n : ZMod q) else 0) *
        (n : ℂ) ^ (-(t * I)) = ∑ p ∈ P, a p * χ (p : ZMod q) * (p : ℂ) ^ (-(t * I)) := by
      intro t
      simp_rw [ite_mul, zero_mul]
      rw [Finset.sum_ite_mem, Finset.inter_eq_right.2 hsub]
    have r2 : ∀ x : ℝ, ∑ n ∈ (Finset.Icc 1 ⌊y⌋₊).filter
        (fun n : ℕ => x < n ∧ (n : ℝ) ≤ x * Real.exp (1 / T)),
        (if n ∈ P then a n * χ (n : ZMod q) else 0) = ∑ n ∈ P.filter
        (fun n : ℕ => x < n ∧ (n : ℝ) ≤ x * Real.exp (1 / T)), a n * χ (n : ZMod q) := by
      intro x
      rw [Finset.sum_ite_mem, Finset.filter_inter, Finset.inter_eq_right.2 hsub]
    simp_rw [r1, r2] at h
    exact h
  refine (Finset.sum_le_sum fun χ _ => hgal χ).trans ?_
  rw [← Finset.mul_sum]
  set w : ℕ → ℝ := fun n => 4 * B * n / (T * Real.log n) * ‖a n‖ ^ 2 with hw
  have hk : ∀ n ∈ P, (0 : ℝ) < n := fun n hn => by exact_mod_cast (hmem n hn).2.2.pos
  have hint : ∀ n ∈ P, Integrable (fun x : ℝ => w n *
      (if x < n ∧ (n : ℝ) ≤ x * Real.exp (1 / T) then 1 / x else 0))
      (volume.restrict (Set.Ioi 0)) := fun n hn =>
    (kernel_integral n (1 / T) (hk n hn) hδ).1.const_mul _
  have key := sum_integral_le (Finset.univ : Finset (DirichletCharacter ℂ q))
    (volume.restrict (Set.Ioi 0))
    (fun χ x => ‖∑ n ∈ P.filter
        (fun n : ℕ => x < n ∧ (n : ℝ) ≤ x * Real.exp (1 / T)), a n * χ (n : ZMod q)‖ ^ 2 / x)
    (fun x => ∑ n ∈ P, w n *
      (if x < n ∧ (n : ℝ) ≤ x * Real.exp (1 / T) then 1 / x else 0))
    (fun p => by
      refine Measurable.aestronglyMeasurable ?_
      simp_rw [Finset.sum_filter]
      refine Measurable.div (Measurable.pow_const (Measurable.norm ?_) 2) measurable_id
      refine Finset.measurable_sum _ fun n _ => Measurable.ite ?_ measurable_const measurable_const
      exact (measurableSet_lt measurable_id measurable_const).inter
        (measurableSet_le measurable_const (measurable_id.mul_const _)))
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx p
      have hx' : 0 < x := hx
      positivity)
    (integrable_finsetSum _ hint)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx' : 0 < x := hx
      have hwin := window B hB0 hB q T N x a (P.filter
        (fun n : ℕ => x < n ∧ (n : ℝ) ≤ x * Real.exp (1 / T))) hT hN hx' (fun n hn => by
          obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hn
          exact ⟨(hmem n h1).2.2, (hmem n h1).1, h2.1, h2.2⟩)
      rw [← Finset.sum_div]
      refine (div_le_div_of_nonneg_right hwin hx'.le).trans (le_of_eq ?_)
      rw [Finset.sum_filter, Finset.sum_div]
      refine Finset.sum_congr rfl fun n _ => ?_
      split_ifs
      · rw [mul_one_div]
      · simp)
  refine (mul_le_mul_of_nonneg_left key (by positivity)).trans ?_
  rw [integral_finsetSum _ hint, mul_assoc, mul_assoc, Finset.mul_sum, Finset.mul_sum _ _ (4 * B)]
  refine mul_le_mul_of_nonneg_left (le_of_eq (Finset.sum_congr rfl fun n hn => ?_)) hC.le
  rw [integral_const_mul, (kernel_integral n (1 / T) (hk n hn) hδ).2]
  simp only [hw]
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (hmem n hn).2.2.one_lt)
  field_simp

end GlobalTheory.PrimeMeanValue
