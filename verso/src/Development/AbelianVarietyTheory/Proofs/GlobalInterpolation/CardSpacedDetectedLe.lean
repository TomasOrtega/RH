import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HybridLargeSieve
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EnormSqLeLintegralDisc
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology

namespace GlobalTheory.SpacedDetected

noncomputable def poly (Q : ℕ) (c : ℕ → ℂ) (x : Σ N : ℕ, DirichletCharacter ℂ (N + 1)) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Ioc (Q ^ 3) (Q ^ 6), c n * x.2 (n : ZMod (x.1 + 1)) * (n : ℂ) ^ (-s)

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology in
/- English proof (translation)
Establish `hl2 : 0 < Real.log 2` using `Real.log_pos one_lt_two`. Establish `hp' : (2 : ℝ) ≤ p` using `by exact_mod_cast hp`. Establish `hp0 : (0 : ℝ) < p` using `by linarith`. Establish `key : ((p : ℝ) ^ a) ^ ε = Real.exp (a * ε * Real.log p)`. Rewrite using `[← Real.rpow_natCast, ← Real.rpow_mul hp0.le, Real.rpow_def_of_pos hp0]`.

Put the polynomial expressions in normal form. Establish `hlogp : Real.log 2 ≤ Real.log p` using `Real.log_le_log two_pos hp'`. Prove the components needed by the constructor for the conclusion. Rewrite using `[key]`. Establish `h1 : 1 + a * ε * Real.log 2 ≤ Real.exp (a * ε * Real.log p)`.

Use `Real.add_one_le_exp (a * ε * Real.log p)` as an intermediate fact. Establish `: a * ε * Real.log 2 ≤ a * ε * Real.log p` using `mul_le_mul_of_nonneg_left hlogp (by positivity)`. Combine the linear equalities and inequalities to obtain the conclusion. Use `set M := max 1 (1 / (ε * Real.log 2))`. Establish `hM1 : 1 ≤ M` using `le_max_left _ _`.

Establish `hM2 : 1 / (ε * Real.log 2) ≤ M` using `le_max_right _ _`. Establish `hMa : (a : ℝ) ≤ M * (a * ε * Real.log 2)`. Establish `hpos : 0 < ε * Real.log 2` using `by positivity`. Establish `h0 : (0 : ℝ) ≤ a * ε * Real.log 2` using `by positivity`. Combine the equalities or inequalities in the displayed calculation.

Use the polynomial consequences of the given equalities and inequalities. Introduce `hbig`. Establish `h2 : (2 : ℝ) ≤ (p : ℝ) ^ ε`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Real.rpow_mul (by norm_num), one_div, inv_mul_cancel₀ hε.ne', Real.rpow_one]`.

Use `_ ≤ (p : ℝ) ^ ε := Real.rpow_le_rpow (by positivity) hbig hε.le`. Establish `: ((p : ℝ) ^ a) ^ ε = ((p : ℝ) ^ ε) ^ a`. Rewrite using `[← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hp0.le, ← Real.rpow_mul hp0.le, mul_comm]`. Rewrite using `[this]`. Combine the equalities or inequalities in the displayed calculation.

Use `Nat.lt_two_pow_self (n := a)` as an intermediate fact. Conclude with `this` after adjusting the coercions. Use `_ ≤ ((p : ℝ) ^ ε) ^ a := pow_le_pow_left₀ (by norm_num) h2 a`.
-/
private theorem succ_le_mul_pow_rpow_of_two_le (ε : ℝ) (hε : 0 < ε) (p a : ℕ) (hp : 2 ≤ p) :
    ((a : ℝ) + 1) ≤ max 1 (1 / (ε * Real.log 2)) * ((p : ℝ) ^ a) ^ ε ∧
      ((2 : ℝ) ^ (1 / ε) ≤ p → ((a : ℝ) + 1) ≤ ((p : ℝ) ^ a) ^ ε) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have key : ((p : ℝ) ^ a) ^ ε = Real.exp (a * ε * Real.log p) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le, Real.rpow_def_of_pos hp0]; ring_nf
  have hlogp : Real.log 2 ≤ Real.log p := Real.log_le_log two_pos hp'
  constructor
  · rw [key]
    have h1 : 1 + a * ε * Real.log 2 ≤ Real.exp (a * ε * Real.log p) := by
      have := Real.add_one_le_exp (a * ε * Real.log p)
      have : a * ε * Real.log 2 ≤ a * ε * Real.log p :=
        mul_le_mul_of_nonneg_left hlogp (by positivity)
      linarith
    set M := max 1 (1 / (ε * Real.log 2))
    have hM1 : 1 ≤ M := le_max_left _ _
    have hM2 : 1 / (ε * Real.log 2) ≤ M := le_max_right _ _
    have hMa : (a : ℝ) ≤ M * (a * ε * Real.log 2) := by
      have hpos : 0 < ε * Real.log 2 := by positivity
      have h0 : (0 : ℝ) ≤ a * ε * Real.log 2 := by positivity
      calc (a : ℝ) = 1 / (ε * Real.log 2) * (a * ε * Real.log 2) := by field_simp
        _ ≤ M * (a * ε * Real.log 2) := mul_le_mul_of_nonneg_right hM2 h0
    nlinarith
  · intro hbig
    have h2 : (2 : ℝ) ≤ (p : ℝ) ^ ε := by
      calc (2 : ℝ) = ((2 : ℝ) ^ (1 / ε)) ^ ε := by
              rw [← Real.rpow_mul (by norm_num), one_div, inv_mul_cancel₀ hε.ne', Real.rpow_one]
        _ ≤ (p : ℝ) ^ ε := Real.rpow_le_rpow (by positivity) hbig hε.le
    have : ((p : ℝ) ^ a) ^ ε = ((p : ℝ) ^ ε) ^ a := by
      rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hp0.le, ← Real.rpow_mul hp0.le, mul_comm]
    rw [this]
    calc ((a : ℝ) + 1) ≤ 2 ^ a := by
          have := Nat.lt_two_pow_self (n := a)
          exact_mod_cast this
      _ ≤ ((p : ℝ) ^ ε) ^ a := pow_le_pow_left₀ (by norm_num) h2 a

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology in
/- English proof (translation)
Use `set M := max 1 (1 / (ε * Real.log 2)) with hM`. Use `set B := ⌈(2 : ℝ) ^ (1 / ε)⌉₊`. Use `⟨M ^ B, by positivity, fun n hn => ?_⟩` and prove the remaining obligations. Establish `hn' : (n : ℝ) = ∏ p ∈ n.primeFactors, ((p : ℝ) ^ n.factorization p)`. Conclude with `(Nat.prod_primeFactors_pow_factorization hn)` after adjusting the coercions.

Rewrite using `[Nat.card_divisors hn]`. Use `push_cast`. Rewrite using `[hn', ← Real.finset_prod_rpow _ _ (fun p _ => by positivity)]`. Use `set f : ℕ → ℝ := fun p => if (p : ℝ) < (2 : ℝ) ^ (1 / ε) then M else 1`. Establish `hf : ∏ p ∈ n.primeFactors, f p ≤ M ^ B`.

Establish `hM1 : 1 ≤ M` using `le_max_left _ _`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.prod_filter]`. Use `_ = M ^ (n.primeFactors.filter (fun p : ℕ => (p : ℝ) < (2 : ℝ) ^ (1 / ε))).card := Finset.prod_const _`. Use `_ ≤ M ^ B := by`.

Apply `pow_le_pow_right₀ hM1` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Apply `Finset.card_le_card` to reduce the goal to its premises. Introduce `p hp`. Simplify using `only [Finset.mem_filter] at hp`.

Simplify using `only [Finset.mem_range]`. Use `lt_of_lt_of_le hp.2 (Nat.le_ceil _)` as an intermediate fact. Conclude with `this` after adjusting the coercions. Use `_ = B := Finset.card_range B`. Combine the equalities or inequalities in the displayed calculation.

Apply `Finset.prod_le_prod (fun p _ => by positivity)` to reduce the goal to its premises. Introduce `p hp`. Establish `h2` using `(Nat.prime_of_mem_primeFactors hp).two_le`. Take `⟨hA, hB⟩` from `succ_le_mul_pow_rpow_of_two_le ε hε p (n.factorization p) h2`. Simplify using `only [f]`.

Use `split_ifs with h`. Conclude with `hA`. Rewrite using `[one_mul]`. Conclude with `hB (not_lt.mp h)`. Use `_ = (∏ p ∈ n.primeFactors, f p) * ∏ p ∈ n.primeFactors, ((p : ℝ) ^ n.factorization p) ^ ε := Finset.prod_mul_distrib`.

Use `_ ≤ M ^ B * ∏ p ∈ n.primeFactors, ((p : ℝ) ^ n.factorization p) ^ ε := mul_le_mul_of_nonneg_right hf (Finset.prod_nonneg (fun p _ => by positivity))`.
-/
private theorem exists_card_divisors_le_mul_rpow (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, n ≠ 0 → (n.divisors.card : ℝ) ≤ K * (n : ℝ) ^ ε := by
  set M := max 1 (1 / (ε * Real.log 2)) with hM
  set B := ⌈(2 : ℝ) ^ (1 / ε)⌉₊
  refine ⟨M ^ B, by positivity, fun n hn => ?_⟩
  have hn' : (n : ℝ) = ∏ p ∈ n.primeFactors, ((p : ℝ) ^ n.factorization p) := by
    exact_mod_cast (Nat.prod_primeFactors_pow_factorization hn)
  rw [Nat.card_divisors hn]
  push_cast
  rw [hn', ← Real.finset_prod_rpow _ _ (fun p _ => by positivity)]
  set f : ℕ → ℝ := fun p => if (p : ℝ) < (2 : ℝ) ^ (1 / ε) then M else 1
  have hf : ∏ p ∈ n.primeFactors, f p ≤ M ^ B := by
    have hM1 : 1 ≤ M := le_max_left _ _
    calc ∏ p ∈ n.primeFactors, f p = ∏ p ∈ n.primeFactors.filter (fun p : ℕ => (p : ℝ) < (2 : ℝ) ^ (1 / ε)), M := by
            rw [Finset.prod_filter]
      _ = M ^ (n.primeFactors.filter (fun p : ℕ => (p : ℝ) < (2 : ℝ) ^ (1 / ε))).card := Finset.prod_const _
      _ ≤ M ^ B := by
            apply pow_le_pow_right₀ hM1
            calc _ ≤ (Finset.range B).card := by
                  apply Finset.card_le_card
                  intro p hp
                  simp only [Finset.mem_filter] at hp
                  simp only [Finset.mem_range]
                  have := lt_of_lt_of_le hp.2 (Nat.le_ceil _)
                  exact_mod_cast this
              _ = B := Finset.card_range B
  calc ∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1)
      ≤ ∏ p ∈ n.primeFactors, (f p * ((p : ℝ) ^ n.factorization p) ^ ε) := by
        apply Finset.prod_le_prod (fun p _ => by positivity)
        intro p hp
        have h2 := (Nat.prime_of_mem_primeFactors hp).two_le
        obtain ⟨hA, hB⟩ := succ_le_mul_pow_rpow_of_two_le ε hε p (n.factorization p) h2
        simp only [f]
        split_ifs with h
        · exact hA
        · rw [one_mul]; exact hB (not_lt.mp h)
    _ = (∏ p ∈ n.primeFactors, f p) * ∏ p ∈ n.primeFactors, ((p : ℝ) ^ n.factorization p) ^ ε :=
        Finset.prod_mul_distrib
    _ ≤ M ^ B * ∏ p ∈ n.primeFactors, ((p : ℝ) ^ n.factorization p) ^ ε :=
        mul_le_mul_of_nonneg_right hf (Finset.prod_nonneg (fun p _ => by positivity))

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology in
/- English proof (translation)
Rewrite using `[intervalIntegral.integral_of_le hTT]`. Establish `hwin : ∀ a ∈ S, ∫ t in (a - r)..(a + r), h t = ∫ t in Set.Ioc (a - r) (a + r), h t` using `fun a _ => intervalIntegral.integral_of_le (by linarith)`. Rewrite using `[Finset.sum_congr rfl hwin]`. Rewrite using `[← MeasureTheory.integral_biUnion_finset S (fun a _ => measurableSet_Ioc)]`. Apply `MeasureTheory.setIntegral_mono_set` to reduce the goal to its premises.

Conclude with `hc.integrableOn_Ioc`. Conclude with `Filter.Eventually.of_forall (fun t => hpos t)`. Use `Filter.Eventually.of_forall (fun t ht => ?_)` and prove the remaining obligations. Establish `ht' : t ∈ ⋃ a ∈ S, Set.Ioc (a - r) (a + r)` using `ht`. Rewrite `ht'` using `[Set.mem_iUnion₂]`.

Take `⟨a, ha, hta⟩` from `ht'`. Use `show t ∈ Set.Ioc (-T) T`. Conclude with `⟨by linarith [(hin a ha).1, hta.1], by linarith [(hin a ha).2, hta.2]⟩`. Introduce `a ha b hb hab`. Rewrite using `[Function.onFun, Set.disjoint_left]`.

Introduce `t hta htb`. Use `hsep a ha b hb hab` as an intermediate fact. Apply the tactic sequence `rcases abs_cases (a - b) with ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e] at this <;>`. Combine the linear relations using `[hta.1, hta.2, htb.1, htb.2]`. Introduce `a _`.

Conclude with `hc.integrableOn_Ioc`.
-/
private theorem sum_integral_separated_windows_le (h : ℝ → ℝ) (hc : Continuous h) (hpos : ∀ t, 0 ≤ h t)
    (S : Finset ℝ) (r T : ℝ) (hr : 0 < r)
    (hsep : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → 2 * r ≤ |a - b|)
    (hin : ∀ a ∈ S, -T ≤ a - r ∧ a + r ≤ T) (hTT : -T ≤ T) :
    ∑ a ∈ S, ∫ t in (a - r)..(a + r), h t ≤ ∫ t in (-T)..T, h t := by
  rw [intervalIntegral.integral_of_le hTT]
  have hwin : ∀ a ∈ S, ∫ t in (a - r)..(a + r), h t = ∫ t in Set.Ioc (a - r) (a + r), h t :=
    fun a _ => intervalIntegral.integral_of_le (by linarith)
  rw [Finset.sum_congr rfl hwin]
  rw [← MeasureTheory.integral_biUnion_finset S (fun a _ => measurableSet_Ioc)]
  · apply MeasureTheory.setIntegral_mono_set
    · exact hc.integrableOn_Ioc
    · exact Filter.Eventually.of_forall (fun t => hpos t)
    · refine Filter.Eventually.of_forall (fun t ht => ?_)
      have ht' : t ∈ ⋃ a ∈ S, Set.Ioc (a - r) (a + r) := ht
      rw [Set.mem_iUnion₂] at ht'
      obtain ⟨a, ha, hta⟩ := ht'
      show t ∈ Set.Ioc (-T) T
      exact ⟨by linarith [(hin a ha).1, hta.1], by linarith [(hin a ha).2, hta.2]⟩
  · intro a ha b hb hab
    rw [Function.onFun, Set.disjoint_left]
    intro t hta htb
    have := hsep a ha b hb hab
    rcases abs_cases (a - b) with ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e] at this <;>
      linarith [hta.1, hta.2, htb.1, htb.2]
  · intro a _
    exact hc.integrableOn_Ioc

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology in
/- English proof (translation)
Establish `hx0 : 0 < x` using `by linarith`. Establish `hb : (1 + (-(1 / x))) ^ θ ≤ 1 + θ * (-(1 / x))` using `rpow_one_add_le_one_add_mul_self (by rw [neg_le_neg_iff, div_le_one hx0]; exact hx) h0.le h1`. Establish `hsplit : (x - 1) ^ θ = x ^ θ * (1 + (-(1 / x))) ^ θ`. Rewrite using `[← Real.mul_rpow hx0.le (by rw [← sub_eq_add_neg, sub_nonneg, div_le_one hx0]; exact hx)]`. Use `congr 1`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hpow : x ^ (θ - 1) = x ^ θ / x` using `by rw [Real.rpow_sub hx0, Real.rpow_one]`. Rewrite using `[hsplit, hpow]`. Establish `hxθ : 0 ≤ x ^ θ` using `by positivity`.

Use `mul_le_mul_of_nonneg_left hb hxθ` as an intermediate fact. Establish `e : x ^ θ * (1 + θ * -(1 / x)) = x ^ θ - θ * (x ^ θ / x)` using `by field_simp; ring`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem mul_rpow_sub_one_le_rpow_sub_rpow (θ : ℝ) (h0 : 0 < θ) (h1 : θ ≤ 1) (x : ℝ) (hx : 1 ≤ x) :
    θ * x ^ (θ - 1) ≤ x ^ θ - (x - 1) ^ θ := by
  have hx0 : 0 < x := by linarith
  have hb : (1 + (-(1 / x))) ^ θ ≤ 1 + θ * (-(1 / x)) :=
    rpow_one_add_le_one_add_mul_self (by rw [neg_le_neg_iff, div_le_one hx0]; exact hx) h0.le h1
  have hsplit : (x - 1) ^ θ = x ^ θ * (1 + (-(1 / x))) ^ θ := by
    rw [← Real.mul_rpow hx0.le (by rw [← sub_eq_add_neg, sub_nonneg, div_le_one hx0]; exact hx)]
    congr 1; field_simp; ring
  have hpow : x ^ (θ - 1) = x ^ θ / x := by rw [Real.rpow_sub hx0, Real.rpow_one]
  rw [hsplit, hpow]
  have hxθ : 0 ≤ x ^ θ := by positivity
  have := mul_le_mul_of_nonneg_left hb hxθ
  have e : x ^ θ * (1 + θ * -(1 / x)) = x ^ θ - θ * (x ^ θ / x) := by field_simp; ring
  linarith

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology in
/- English proof (translation)
Rewrite using `[le_div_iff₀ h0, Finset.sum_mul]`. Combine the equalities or inequalities in the displayed calculation. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `k _`. Use `mul_rpow_sub_one_le_rpow_sub_rpow θ h0 h1 ((k : ℝ) + 1) (by linarith [k.cast_nonneg (α := ℝ)])` as an intermediate fact.

Use `push_cast`. Rewrite `this` using `[add_sub_cancel_right]`. Combine the linear equalities and inequalities to obtain the conclusion. Use `_ = (N : ℝ) ^ θ := by`. Rewrite using `[Finset.sum_range_sub (fun k : ℕ => ((k : ℝ)) ^ θ) N]`.

Simplify using `[Real.zero_rpow h0.ne']`.
-/
private theorem sum_range_succ_rpow_sub_one_le (θ : ℝ) (h0 : 0 < θ) (h1 : θ ≤ 1) (N : ℕ) :
    ∑ k ∈ Finset.range N, ((k : ℝ) + 1) ^ (θ - 1) ≤ (N : ℝ) ^ θ / θ := by
  rw [le_div_iff₀ h0, Finset.sum_mul]
  calc ∑ k ∈ Finset.range N, ((k : ℝ) + 1) ^ (θ - 1) * θ
      ≤ ∑ k ∈ Finset.range N, ((((k + 1 : ℕ) : ℝ)) ^ θ - ((k : ℕ) : ℝ) ^ θ) := by
        apply Finset.sum_le_sum
        intro k _
        have := mul_rpow_sub_one_le_rpow_sub_rpow θ h0 h1 ((k : ℝ) + 1) (by linarith [k.cast_nonneg (α := ℝ)])
        push_cast
        rw [add_sub_cancel_right] at this
        linarith
    _ = (N : ℝ) ^ θ := by
        rw [Finset.sum_range_sub (fun k : ℕ => ((k : ℝ)) ^ θ) N]
        simp [Real.zero_rpow h0.ne']

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology in
/- English proof (translation)
Establish `hθ : ∑ n ∈ Finset.Icc 1 (Q ^ 6), ((n : ℝ)) ^ ((1 : ℝ) / 80 - 1) ≤ 80 * (Q : ℝ) ^ ((1 : ℝ) / 8)`. Establish `h` using `sum_range_succ_rpow_sub_one_le (1 / 80) (by norm_num) (by norm_num) (Q ^ 6)`. Establish `hre : ∑ n ∈ Finset.Icc 1 (Q ^ 6), ((n : ℝ)) ^ ((1 : ℝ) / 80 - 1) = ∑ k ∈ Finset.range (Q ^ 6), ((k : ℝ) + 1) ^ ((1 : ℝ) / 80 - 1)`. Rewrite using `[← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]`. Simplify using `only [Nat.add_sub_cancel]`.

Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `k _`. Use `push_cast`. Put the polynomial expressions in normal form. Rewrite using `[hre]`.

Use `h.trans ?_` and prove the remaining obligations. Establish `hQ0 : (0 : ℝ) ≤ Q` using `by positivity`. Establish `hQ1 : (1 : ℝ) ≤ Q` using `by exact_mod_cast (by omega : 1 ≤ Q)`. Rewrite using `[div_eq_mul_inv, mul_comm]`. Establish `: ((Q ^ 6 : ℕ) : ℝ) ^ ((1 : ℝ) / 80) = (Q : ℝ) ^ ((6 : ℝ) / 80)`.

Use `push_cast`. Rewrite using `[← Real.rpow_natCast, ← Real.rpow_mul hQ0]`. Evaluate the numerical expressions. Rewrite using `[this]`. Evaluate the numerical expressions.

Conclude with `Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num)`. Use `le_trans ?_ ((mul_le_mul_of_nonneg_left hθ (by positivity : (0 : ℝ) ≤ 3 * K ^ 2)).trans_eq (by ring))` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `n hn`.

Establish `hn1 : 1 ≤ n` using `(Finset.mem_Icc.mp hn).1`. Establish `hn0 : (0 : ℝ) < n` using `by exact_mod_cast hn1`. Use `split_ifs with hI`. Establish `hnQ : Q ^ 3 < n` using `(Finset.mem_Ioc.mp hI).1`. Establish `hweight : (Q : ℝ) ^ 2 * ((Q : ℝ) + 1) + n ≤ 3 * n`.

Establish `: ((Q ^ 3 : ℕ) : ℝ) < n` using `by exact_mod_cast hnQ`. Move the coercions through the operations in `at this`. Establish `hQ1 : (1 : ℝ) ≤ Q` using `by exact_mod_cast (by omega : 1 ≤ Q)`. Use polynomial arithmetic with `[pow_le_pow_right₀ hQ1 (show 2 ≤ 3 by norm_num)]`. Establish `hcoef : ‖((∑ d ∈ n.divisors.filter (fun d => d ≤ Q ^ 3), (ArithmeticFunction.moebius d : ℤ) : ℤ) : ℂ)‖ ≤ K * (n : ℝ) ^ ((1 : ℝ) / 400)`.

Use `le_trans ?_ (hdiv n (by omega))` and prove the remaining obligations. Establish `hz : |∑ d ∈ n.divisors.filter (fun d => d ≤ Q ^ 3), (ArithmeticFunction.moebius d : ℤ)| ≤ (n.divisors.filter (fun d => d ≤ Q ^ 3)).card`. Use `(Finset.abs_sum_le_sum_abs _ _).trans ?_` and prove the remaining obligations. Use `(Finset.sum_le_card_nsmul _ _ 1 (fun d _ => ArithmeticFunction.abs_moebius_le_one)).trans ?_` and prove the remaining obligations. Simplify using the standard rewrite rules.

Establish `hz'` using `hz.trans (by exact_mod_cast Finset.card_filter_le _ _ : ((n.divisors.filter (fun d => d ≤ Q ^ 3)).card : ℤ) ≤ n.divisors.card)`. Rewrite using `[Complex.norm_intCast, ← Int.cast_abs]`. Conclude with `hz'` after adjusting the coercions. Establish `hpow : ‖(n : ℂ) ^ (-(σ : ℂ))‖ = (n : ℝ) ^ (-σ)`. Rewrite using `[← Complex.ofReal_natCast, ← Complex.ofReal_neg, ← Complex.ofReal_cpow hn0.le, Complex.norm_real, Real.norm_of_nonneg (by positivity)]`.

Rewrite using `[norm_mul, hpow, mul_pow]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[show (1 : ℝ) / 200 + 1 - 2 * σ = (1 / 400) * 2 + 1 + (-σ) * 2 by ring, Real.rpow_add hn0, Real.rpow_add hn0, Real.rpow_one, Real.rpow_mul hn0.le, Real.rpow_mul hn0.le, Real.rpow_two, Real.rpow_two]`. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ 3 * K ^ 2 * ((n : ℝ) ^ ((1 : ℝ) / 80 - 1)) := by`.

Use `mul_le_mul_of_nonneg_left ?_ (by positivity)` and prove the remaining obligations. Conclude with `Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn1) (by linarith)`. Simplify using `only [norm_zero]`. Evaluate the numerical expressions. Check the signs of the components of the expression.
-/
private theorem sum_weighted_moebius_coeff_sq_le (K : ℝ) (hK : 0 < K)
    (hdiv : ∀ n : ℕ, n ≠ 0 → (n.divisors.card : ℝ) ≤ K * (n : ℝ) ^ ((1 : ℝ) / 400))
    (Q : ℕ) (hQ : 2 ≤ Q) (σ : ℝ) (hσ : 1 - 3 / 800 ≤ σ) :
    ∑ n ∈ Finset.Icc 1 (Q ^ 6), ((Q : ℝ) ^ 2 * ((Q : ℝ) + 1) + n) *
      ‖(if n ∈ Finset.Ioc (Q ^ 3) (Q ^ 6) then
        ((∑ d ∈ n.divisors.filter (fun d => d ≤ Q ^ 3), (ArithmeticFunction.moebius d : ℤ) : ℤ) : ℂ) *
          (n : ℂ) ^ (-(σ : ℂ)) else 0)‖ ^ 2 ≤ 3 * K ^ 2 * 80 * (Q : ℝ) ^ ((1 : ℝ) / 8) := by
  have hθ : ∑ n ∈ Finset.Icc 1 (Q ^ 6), ((n : ℝ)) ^ ((1 : ℝ) / 80 - 1) ≤ 80 * (Q : ℝ) ^ ((1 : ℝ) / 8) := by
    have h := sum_range_succ_rpow_sub_one_le (1 / 80) (by norm_num) (by norm_num) (Q ^ 6)
    have hre : ∑ n ∈ Finset.Icc 1 (Q ^ 6), ((n : ℝ)) ^ ((1 : ℝ) / 80 - 1) =
        ∑ k ∈ Finset.range (Q ^ 6), ((k : ℝ) + 1) ^ ((1 : ℝ) / 80 - 1) := by
      rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
      simp only [Nat.add_sub_cancel]
      apply Finset.sum_congr rfl
      intro k _
      push_cast; ring_nf
    rw [hre]
    refine h.trans ?_
    have hQ0 : (0 : ℝ) ≤ Q := by positivity
    have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast (by omega : 1 ≤ Q)
    rw [div_eq_mul_inv, mul_comm]
    have : ((Q ^ 6 : ℕ) : ℝ) ^ ((1 : ℝ) / 80) = (Q : ℝ) ^ ((6 : ℝ) / 80) := by
      push_cast
      rw [← Real.rpow_natCast, ← Real.rpow_mul hQ0]; norm_num
    rw [this]
    norm_num
    exact Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num)
  refine le_trans ?_ ((mul_le_mul_of_nonneg_left hθ (by positivity : (0 : ℝ) ≤ 3 * K ^ 2)).trans_eq (by ring))
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  split_ifs with hI
  · have hnQ : Q ^ 3 < n := (Finset.mem_Ioc.mp hI).1
    have hweight : (Q : ℝ) ^ 2 * ((Q : ℝ) + 1) + n ≤ 3 * n := by
      have : ((Q ^ 3 : ℕ) : ℝ) < n := by exact_mod_cast hnQ
      push_cast at this
      have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast (by omega : 1 ≤ Q)
      nlinarith [pow_le_pow_right₀ hQ1 (show 2 ≤ 3 by norm_num)]
    have hcoef : ‖((∑ d ∈ n.divisors.filter (fun d => d ≤ Q ^ 3), (ArithmeticFunction.moebius d : ℤ) : ℤ) : ℂ)‖ ≤ K * (n : ℝ) ^ ((1 : ℝ) / 400) := by
      refine le_trans ?_ (hdiv n (by omega))
      have hz : |∑ d ∈ n.divisors.filter (fun d => d ≤ Q ^ 3), (ArithmeticFunction.moebius d : ℤ)| ≤
          (n.divisors.filter (fun d => d ≤ Q ^ 3)).card := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        refine (Finset.sum_le_card_nsmul _ _ 1 (fun d _ => ArithmeticFunction.abs_moebius_le_one)).trans ?_
        simp
      have hz' := hz.trans (by exact_mod_cast Finset.card_filter_le _ _ : ((n.divisors.filter (fun d => d ≤ Q ^ 3)).card : ℤ) ≤ n.divisors.card)
      rw [Complex.norm_intCast, ← Int.cast_abs]
      exact_mod_cast hz'
    have hpow : ‖(n : ℂ) ^ (-(σ : ℂ))‖ = (n : ℝ) ^ (-σ) := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_neg, ← Complex.ofReal_cpow hn0.le, Complex.norm_real,
        Real.norm_of_nonneg (by positivity)]
    rw [norm_mul, hpow, mul_pow]
    calc ((Q : ℝ) ^ 2 * ((Q : ℝ) + 1) + n) * (‖((∑ d ∈ n.divisors.filter (fun d => d ≤ Q ^ 3), (ArithmeticFunction.moebius d : ℤ) : ℤ) : ℂ)‖ ^ 2 * ((n : ℝ) ^ (-σ)) ^ 2)
        ≤ (3 * n) * ((K * (n : ℝ) ^ ((1 : ℝ) / 400)) ^ 2 * ((n : ℝ) ^ (-σ)) ^ 2) := by
          gcongr
      _ = 3 * K ^ 2 * ((n : ℝ) ^ ((1 : ℝ) / 200 + 1 - 2 * σ)) := by
          rw [show (1 : ℝ) / 200 + 1 - 2 * σ = (1 / 400) * 2 + 1 + (-σ) * 2 by ring,
            Real.rpow_add hn0, Real.rpow_add hn0, Real.rpow_one, Real.rpow_mul hn0.le,
            Real.rpow_mul hn0.le, Real.rpow_two, Real.rpow_two]
          ring
      _ ≤ 3 * K ^ 2 * ((n : ℝ) ^ ((1 : ℝ) / 80 - 1)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn1) (by linarith)
  · simp only [norm_zero]
    norm_num
    positivity

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology in

/- English proof (translation)
Take `⟨C₁, hC₁, hmv⟩` from `_root_.GlobalTheory.norm_sq_le_integral_square`. Take `⟨C₂, hC₂, hls⟩` from `_root_.GlobalTheory.HybridLargeSieve.hybrid_large_sieve`. Take `⟨K, hK, hdiv⟩` from `exists_card_divisors_le_mul_rpow (1 / 400) (by norm_num)`. Use `⟨4 * (C₁ / (1 / 800) ^ 2) * ((1 / 200) * (C₂ * (3 * K ^ 2 * 80))), by positivity, ?_⟩` and prove the remaining obligations. Introduce `Q hQ T hT hsep`.

Use `set r : ℝ := 1 / 800 with hr`. Use `set c : ℕ → ℂ := fun n => ((∑ d ∈ n.divisors.filter (fun d => d ≤ Q ^ 3), (moebius d : ℤ) : ℤ) : ℂ) with hc`. Use `set F : (Σ N : ℕ, DirichletCharacter ℂ (N + 1)) → ℂ → ℂ := fun x s => _root_.GlobalTheory.SpacedDetected.poly Q c x s with hF`. Establish `hFdiff : ∀ x, Differentiable ℂ (F x)`. Introduce `x`.

Simplify using `only [hF, _root_.GlobalTheory.SpacedDetected.poly]`. Introduce `s`. Apply `DifferentiableAt.fun_sum` to reduce the goal to its premises. Introduce `n hn`. Establish `hn0 : (n : ℂ) ≠ 0`.

Use `(Finset.mem_Ioc.mp hn).1` as an intermediate fact. Conclude with `(show n ≠ 0 by omega)` after adjusting the coercions. Conclude with `(differentiableAt_id.neg.const_cpow (Or.inl hn0)).const_mul _`. Use `set Tm : ℝ := Q + 1 with hTm`. Use `set σ₀ : ℝ := 1 - 1 / 400 - r with hσ₀`.

Use `set σ₁ : ℝ := 1 + r with hσ₁`. Use `set G : (Σ N : ℕ, DirichletCharacter ℂ (N + 1)) → ℝ → ℝ := fun x σ => ∫ t in (-Tm)..Tm, ‖F x (σ + t * I)‖ ^ 2 with hG`. Establish `hGcont : ∀ x, Continuous (G x)`. Introduce `x`. Apply `intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'` to reduce the goal to its premises.

Use `(hFdiff x).continuous` as an intermediate fact. Use `fun_prop`. Establish `hQ1 : (1 : ℝ) ≤ Q` using `by exact_mod_cast (by omega : 1 ≤ Q)`. Establish `hpt : ∀ p ∈ T, (1 / 4 : ℝ) ≤ C₁ / r ^ 2 * ∫ σ in σ₀..σ₁, ∫ t in (p.2.2.im - r)..(p.2.2.im + r), ‖F ⟨p.1, p.2.1⟩ (σ + t * I)‖ ^ 2`. Introduce `p hp`.

Take `⟨-, -, hre1, hre2, -, hbig⟩` from `hT p hp`. Establish `hval : F ⟨p.1, p.2.1⟩ p.2.2 = ∑ n ∈ Finset.Ioc (Q ^ 3) (Q ^ 6), ((∑ d ∈ n.divisors.filter (fun d => d ≤ Q ^ 3), (moebius d : ℤ) : ℤ) : ℂ) * p.2.1 (n : ZMod (p.1 + 1)) * (n : ℂ) ^ (-p.2.2)` using `rfl`. Establish `h14 : (1 / 4 : ℝ) ≤ ‖F ⟨p.1, p.2.1⟩ p.2.2‖ ^ 2`. Rewrite using `[hval]`. Use the polynomial consequences of the given equalities and inequalities.

Use `h14.trans ((hmv _ p.2.2 r (hFdiff _) (by rw [hr]; norm_num)).trans ?_)` and prove the remaining obligations. Use `mul_le_mul_of_nonneg_left ?_ (by positivity)` and prove the remaining obligations. Establish `hcont : Continuous (fun σ : ℝ => ∫ t in (p.2.2.im - r)..(p.2.2.im + r), ‖F ⟨p.1, p.2.1⟩ (σ + t * I)‖ ^ 2)`. Apply `intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'` to reduce the goal to its premises. Use `(hFdiff ⟨p.1, p.2.1⟩).continuous` as an intermediate fact.

Use `fun_prop`. Apply `intervalIntegral.integral_mono_interval` to reduce the goal to its premises. Rewrite using `[hσ₀]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[hr]`.

Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[hσ₁]`. Combine the linear equalities and inequalities to obtain the conclusion. Use `Filter.Eventually.of_forall (fun σ => ?_)` and prove the remaining obligations. Conclude with `intervalIntegral.integral_nonneg (by rw [hr]; linarith) (fun t _ => by positivity)`.

Conclude with `hcont.intervalIntegrable _ _`. Use `set P := T.image (fun p => (⟨p.1, p.2.1⟩ : Σ N : ℕ, DirichletCharacter ℂ (N + 1))) with hP`. Establish `hgroup : ∑ p ∈ T, ∫ σ in σ₀..σ₁, ∫ t in (p.2.2.im - r)..(p.2.2.im + r), ‖F ⟨p.1, p.2.1⟩ (σ + t * I)‖ ^ 2 ≤ ∑ x ∈ P, ∫ σ in σ₀..σ₁, G x σ`. Establish `hW : ∀ (x : Σ N : ℕ, DirichletCharacter ℂ (N + 1)) (a : ℝ), Continuous (fun σ : ℝ => ∫ t in (a - r)..(a + r), ‖F x (σ + t * I)‖ ^ 2)`. Introduce `x a`.

Apply `intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'` to reduce the goal to its premises. Use `(hFdiff x).continuous` as an intermediate fact. Use `fun_prop`. Establish `hle : σ₀ ≤ σ₁` using `by rw [hσ₀, hσ₁, hr]; norm_num`. Rewrite using `[← Finset.sum_fiberwise_of_maps_to (s := T) (t := P) (g := fun p => (⟨p.1, p.2.1⟩ : Σ N : ℕ, DirichletCharacter ℂ (N + 1))) (fun p hp => Finset.mem_image_of_mem _ hp)]`.

Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `x _`. Rewrite using `[← intervalIntegral.integral_finset_sum (fun p _ => (hW _ _).intervalIntegrable _ _)]`. Apply `intervalIntegral.integral_mono_on hle` to reduce the goal to its premises. Conclude with `(continuous_finset_sum _ (fun p _ => hW _ _)).intervalIntegrable _ _`.

Conclude with `(hGcont x).intervalIntegrable _ _`. Introduce `σ _`. Use `set fib := T.filter (fun p => (⟨p.1, p.2.1⟩ : Σ N : ℕ, DirichletCharacter ℂ (N + 1)) = x) with hfib`. Establish `hrw : ∀ p ∈ fib, (∫ t in (p.2.2.im - r)..(p.2.2.im + r), ‖F ⟨p.1, p.2.1⟩ (σ + t * I)‖ ^ 2) = ∫ t in (p.2.2.im - r)..(p.2.2.im + r), ‖F x (σ + t * I)‖ ^ 2`. Introduce `p hp`.

Rewrite `hp` using `[hfib, Finset.mem_filter]`. Rewrite using `[hp.2]`. Rewrite using `[Finset.sum_congr rfl hrw]`. Establish `hinj : Set.InjOn (fun p : (Σ N : ℕ, DirichletCharacter ℂ (N + 1) × ℂ) => p.2.2.im) fib`. Introduce `p hp p' hp' him`.

Rewrite `hp`, `hp'` using `[Finset.mem_coe, hfib, Finset.mem_filter]`. Take `⟨N, χ, ρ⟩` from `p`. Take `⟨N', χ', ρ'⟩` from `p'`. Establish `hkey : (⟨N, χ⟩ : Σ N : ℕ, DirichletCharacter ℂ (N + 1)) = ⟨N', χ'⟩` using `hp.2.trans hp'.2.symm`. Take `⟨rfl, h⟩` from `Sigma.mk.inj_iff.mp hkey`.

Consider the cases of `h`. Assume the negation of the conclusion as `hne`. Establish `hρ : ρ ≠ ρ'` using `fun e => hne (by rw [e])`. Use `hsep N χ ρ ρ' hp.1 hp'.1 hρ` as an intermediate fact. Simplify using `only at him`.

Rewrite `this` using `[him, sub_self, abs_zero]`. Evaluate the numerical expressions using `at this`. Rewrite using `[← Finset.sum_image (f := fun a => ∫ t in (a - r)..(a + r), ‖F x (σ + t * I)‖ ^ 2) hinj]`. Apply `sum_integral_separated_windows_le (fun t => ‖F x (σ + t * I)‖ ^ 2) (by have := (hFdiff x).continuous; fun_prop) (fun t => by positivity) _ r Tm (by rw [hr]; norm_num)` to reduce the goal to its premises. Introduce `a ha b hb hab`.

Rewrite `ha`, `hb` using `[Finset.mem_image]`. Take `⟨p, hp, rfl⟩` from `ha`. Take `⟨p', hp', rfl⟩` from `hb`. Rewrite `hp`, `hp'` using `[hfib, Finset.mem_filter]`. Take `⟨N, χ, ρ⟩` from `p`.

Take `⟨N', χ', ρ'⟩` from `p'`. Establish `hkey : (⟨N, χ⟩ : Σ N : ℕ, DirichletCharacter ℂ (N + 1)) = ⟨N', χ'⟩` using `hp.2.trans hp'.2.symm`. Take `⟨rfl, h⟩` from `Sigma.mk.inj_iff.mp hkey`. Consider the cases of `h`. Establish `hρ : ρ ≠ ρ'` using `fun e => hab (by rw [e])`.

Use `hsep N χ ρ ρ' hp.1 hp'.1 hρ` as an intermediate fact. Simplify using `only`. Rewrite using `[hr]`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `a ha`.

Rewrite `ha` using `[Finset.mem_image]`. Take `⟨p, hp, rfl⟩` from `ha`. Rewrite `hp` using `[hfib, Finset.mem_filter]`. Establish `hb` using `(hT p hp.1).2.2.2.2.1`. Rewrite `hb` using `[abs_le]`.

Rewrite using `[hTm, hr]`. Apply the tactic sequence `constructor <;> linarith [hb.1, hb.2]`. Rewrite using `[hTm]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hsieve : ∀ σ ∈ Set.Icc σ₀ σ₁, ∑ x ∈ P, G x σ ≤ C₂ * (3 * K ^ 2 * 80) * (Q : ℝ) ^ ((1 : ℝ) / 8)`.

Introduce `σ hσ`. Use `set a : ℕ → ℂ := fun n => if n ∈ Finset.Ioc (Q ^ 3) (Q ^ 6) then ((∑ d ∈ n.divisors.filter (fun d => d ≤ Q ^ 3), (moebius d : ℤ) : ℤ) : ℂ) * (n : ℂ) ^ (-(σ : ℂ)) else 0 with ha`. Establish `hsub : Finset.Ioc (Q ^ 3) (Q ^ 6) ⊆ Finset.Icc 1 (Q ^ 6)`. Introduce `n hn`. Rewrite `hn` using `[Finset.mem_Ioc]`.

Rewrite using `[Finset.mem_Icc]`. Conclude with `⟨by have := Nat.zero_le (Q ^ 3); omega, hn.2⟩`. Establish `hrepr : ∀ (x : Σ N : ℕ, DirichletCharacter ℂ (N + 1)) (t : ℝ), F x (σ + t * I) = ∑ n ∈ Finset.Icc 1 (Q ^ 6), a n * x.2 (n : ZMod (x.1 + 1)) * (n : ℂ) ^ (-(t * I))`. Introduce `x t`. Rewrite using `[← Finset.sum_subset hsub (fun n _ hn => by rw [ha]; simp [hn])]`.

Simplify using `only [hF, _root_.GlobalTheory.SpacedDetected.poly, hc]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `n hn`. Establish `hn0 : (n : ℂ) ≠ 0`. Use `(Finset.mem_Ioc.mp hn).1` as an intermediate fact.

Conclude with `(show n ≠ 0 by omega)` after adjusting the coercions. Rewrite using `[ha]`. Simplify using `only [if_pos hn]`. Rewrite using `[neg_add, Complex.cpow_add _ _ hn0]`. Expand and normalize the polynomial expressions, which then agree.

Use `set H : (Σ N : ℕ, DirichletCharacter ℂ (N + 1)) → ℝ := fun x => ∫ t in (-Tm)..Tm, ‖∑ n ∈ Finset.Icc 1 (Q ^ 6), a n * x.2 (n : ZMod (x.1 + 1)) * (n : ℂ) ^ (-(t * I))‖ ^ 2 with hH`. Establish `hGH : ∀ x, G x σ = H x`. Introduce `x`. Simplify using `only [hG, hH, hrepr]`. Establish `hTm1 : (1 : ℝ) ≤ Tm` using `by rw [hTm]; linarith`.

Establish `hHnn : ∀ x, 0 ≤ H x` using `fun x => intervalIntegral.integral_nonneg (by linarith) (fun t _ => by positivity)`. Simplify using `only [hGH]`. Establish `hPsub : P ⊆ (Finset.range Q).sigma (fun q => Finset.univ.filter (fun χ : DirichletCharacter ℂ (q + 1) => χ.IsPrimitive))`. Introduce `x hx`. Rewrite `hx` using `[hP, Finset.mem_image]`.

Take `⟨p, hp, rfl⟩` from `hx`. Take `⟨h1, h2, -⟩` from `hT p hp`. Rewrite using `[Finset.mem_sigma, Finset.mem_range, Finset.mem_filter]`. Conclude with `⟨by show p.1 < Q; omega, Finset.mem_univ _, h2⟩`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Finset.sum_sigma]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `q _`. Rewrite using `[finsum_mem_eq_toFinset_sum, Set.toFinset_setOf]`. Use `_ ≤ C₂ * ∑ n ∈ Finset.Icc 1 (Q ^ 6), ((Q : ℝ) ^ 2 * Tm + n) * ‖a n‖ ^ 2 := hls Q (Q ^ 6) a Tm (by omega) hTm1`.

Use `_ ≤ C₂ * (3 * K ^ 2 * 80 * (Q : ℝ) ^ ((1 : ℝ) / 8)) := by`. Use `mul_le_mul_of_nonneg_left ?_ hC₂.le` and prove the remaining obligations. Establish `hσ' : 1 - 3 / 800 ≤ σ`. Use `hσ.1` as an intermediate fact. Rewrite `this` using `[hσ₀, hr]`.

Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `sum_weighted_moebius_coeff_sq_le K hK hdiv Q hQ σ hσ'`. Use `_ = C₂ * (3 * K ^ 2 * 80) * (Q : ℝ) ^ ((1 : ℝ) / 8) := by ring`. Establish `hint : ∑ x ∈ P, ∫ σ in σ₀..σ₁, G x σ ≤ (1 / 200) * (C₂ * (3 * K ^ 2 * 80) * (Q : ℝ) ^ ((1 : ℝ) / 8))`. Rewrite using `[← intervalIntegral.integral_finset_sum (fun x _ => (hGcont x).intervalIntegrable _ _)]`.

Establish `hle : σ₀ ≤ σ₁` using `by rw [hσ₀, hσ₁, hr]; norm_num`. Combine the equalities or inequalities in the displayed calculation. Apply `intervalIntegral.integral_mono_on hle` to reduce the goal to its premises. Conclude with `(continuous_finset_sum _ (fun x _ => hGcont x)).intervalIntegrable _ _`. Conclude with `intervalIntegrable_const`.

Conclude with `hsieve`. Use `_ = (1 / 200) * (C₂ * (3 * K ^ 2 * 80) * (Q : ℝ) ^ ((1 : ℝ) / 8)) := by`. Rewrite using `[intervalIntegral.integral_const, smul_eq_mul, hσ₀, hσ₁, hr]`. Evaluate the numerical expressions. Establish `hsum : (T.card : ℝ) * (1 / 4) ≤ C₁ / r ^ 2 * ∑ p ∈ T, ∫ σ in σ₀..σ₁, ∫ t in (p.2.2.im - r)..(p.2.2.im + r), ‖F ⟨p.1, p.2.1⟩ (σ + t * I)‖ ^ 2`.

Rewrite using `[Finset.mul_sum]`. Combine the equalities or inequalities in the displayed calculation. Establish `hCr : 0 ≤ C₁ / r ^ 2` using `by positivity`. Combine the equalities or inequalities in the displayed calculation. Use `mul_le_mul_of_nonneg_left ?_ (by norm_num)` and prove the remaining obligations.

Conclude with `hsum.trans (mul_le_mul_of_nonneg_left (hgroup.trans hint) hCr)`. Use `_ = _ := by rw [hr]; ring`.
-/
theorem _root_.GlobalTheory.SpacedDetected.card_spaced_detected_le : ∃ C : ℝ, 0 < C ∧ ∀ Q : ℕ, 2 ≤ Q → ∀ T : Finset (Σ N : ℕ, DirichletCharacter ℂ (N + 1) × ℂ), (∀ p ∈ T, p.1 + 1 ≤ Q ∧ p.2.1.IsPrimitive ∧ 1 - 1 / 400 ≤ p.2.2.re ∧ p.2.2.re ≤ 1 ∧ |p.2.2.im| ≤ Q ∧ (1 / 2 : ℝ) ≤ ‖∑ n ∈ Finset.Ioc (Q ^ 3) (Q ^ 6), ((∑ d ∈ n.divisors.filter (fun d => d ≤ Q ^ 3), (moebius d : ℤ) : ℤ) : ℂ) * p.2.1 (n : ZMod (p.1 + 1)) * (n : ℂ) ^ (-p.2.2)‖) → (∀ (N : ℕ) (χ : DirichletCharacter ℂ (N + 1)) (ρ ρ' : ℂ), (⟨N, χ, ρ⟩ : (Σ N : ℕ, DirichletCharacter ℂ (N + 1) × ℂ)) ∈ T → (⟨N, χ, ρ'⟩ : (Σ N : ℕ, DirichletCharacter ℂ (N + 1) × ℂ)) ∈ T → ρ ≠ ρ' → 1 ≤ |ρ.im - ρ'.im|) → (T.card : ℝ) ≤ C * (Q : ℝ) ^ ((1 : ℝ) / 8) := by
  classical
  obtain ⟨C₁, hC₁, hmv⟩ := _root_.GlobalTheory.norm_sq_le_integral_square
  obtain ⟨C₂, hC₂, hls⟩ := _root_.GlobalTheory.HybridLargeSieve.hybrid_large_sieve
  obtain ⟨K, hK, hdiv⟩ := exists_card_divisors_le_mul_rpow (1 / 400) (by norm_num)
  refine ⟨4 * (C₁ / (1 / 800) ^ 2) * ((1 / 200) * (C₂ * (3 * K ^ 2 * 80))), by positivity, ?_⟩
  intro Q hQ T hT hsep
  set r : ℝ := 1 / 800 with hr
  set c : ℕ → ℂ := fun n => ((∑ d ∈ n.divisors.filter (fun d => d ≤ Q ^ 3), (moebius d : ℤ) : ℤ) : ℂ)
    with hc
  set F : (Σ N : ℕ, DirichletCharacter ℂ (N + 1)) → ℂ → ℂ :=
    fun x s => _root_.GlobalTheory.SpacedDetected.poly Q c x s with hF
  have hFdiff : ∀ x, Differentiable ℂ (F x) := by
    intro x
    simp only [hF, _root_.GlobalTheory.SpacedDetected.poly]
    intro s
    apply DifferentiableAt.fun_sum
    intro n hn
    have hn0 : (n : ℂ) ≠ 0 := by
      have := (Finset.mem_Ioc.mp hn).1
      exact_mod_cast (show n ≠ 0 by omega)
    exact (differentiableAt_id.neg.const_cpow (Or.inl hn0)).const_mul _
  set Tm : ℝ := Q + 1 with hTm
  set σ₀ : ℝ := 1 - 1 / 400 - r with hσ₀
  set σ₁ : ℝ := 1 + r with hσ₁
  set G : (Σ N : ℕ, DirichletCharacter ℂ (N + 1)) → ℝ → ℝ :=
    fun x σ => ∫ t in (-Tm)..Tm, ‖F x (σ + t * I)‖ ^ 2 with hG
  have hGcont : ∀ x, Continuous (G x) := by
    intro x
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    have := (hFdiff x).continuous
    fun_prop
  have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast (by omega : 1 ≤ Q)
  have hpt : ∀ p ∈ T, (1 / 4 : ℝ) ≤ C₁ / r ^ 2 * ∫ σ in σ₀..σ₁,
      ∫ t in (p.2.2.im - r)..(p.2.2.im + r), ‖F ⟨p.1, p.2.1⟩ (σ + t * I)‖ ^ 2 := by
    intro p hp
    obtain ⟨-, -, hre1, hre2, -, hbig⟩ := hT p hp
    have hval : F ⟨p.1, p.2.1⟩ p.2.2 = ∑ n ∈ Finset.Ioc (Q ^ 3) (Q ^ 6), ((∑ d ∈ n.divisors.filter (fun d => d ≤ Q ^ 3), (moebius d : ℤ) : ℤ) : ℂ) * p.2.1 (n : ZMod (p.1 + 1)) * (n : ℂ) ^ (-p.2.2) := rfl
    have h14 : (1 / 4 : ℝ) ≤ ‖F ⟨p.1, p.2.1⟩ p.2.2‖ ^ 2 := by
      rw [hval]; nlinarith
    refine h14.trans ((hmv _ p.2.2 r (hFdiff _) (by rw [hr]; norm_num)).trans ?_)
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hcont : Continuous (fun σ : ℝ => ∫ t in (p.2.2.im - r)..(p.2.2.im + r), ‖F ⟨p.1, p.2.1⟩ (σ + t * I)‖ ^ 2) := by
      apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      have := (hFdiff ⟨p.1, p.2.1⟩).continuous
      fun_prop
    apply intervalIntegral.integral_mono_interval
    · rw [hσ₀]; linarith
    · rw [hr]; linarith
    · rw [hσ₁]; linarith
    · refine Filter.Eventually.of_forall (fun σ => ?_)
      exact intervalIntegral.integral_nonneg (by rw [hr]; linarith) (fun t _ => by positivity)
    · exact hcont.intervalIntegrable _ _
  set P := T.image (fun p => (⟨p.1, p.2.1⟩ : Σ N : ℕ, DirichletCharacter ℂ (N + 1))) with hP
  have hgroup : ∑ p ∈ T, ∫ σ in σ₀..σ₁,
      ∫ t in (p.2.2.im - r)..(p.2.2.im + r), ‖F ⟨p.1, p.2.1⟩ (σ + t * I)‖ ^ 2 ≤
      ∑ x ∈ P, ∫ σ in σ₀..σ₁, G x σ := by
    have hW : ∀ (x : Σ N : ℕ, DirichletCharacter ℂ (N + 1)) (a : ℝ), Continuous (fun σ : ℝ =>
        ∫ t in (a - r)..(a + r), ‖F x (σ + t * I)‖ ^ 2) := by
      intro x a
      apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      have := (hFdiff x).continuous
      fun_prop
    have hle : σ₀ ≤ σ₁ := by rw [hσ₀, hσ₁, hr]; norm_num
    rw [← Finset.sum_fiberwise_of_maps_to (s := T) (t := P)
      (g := fun p => (⟨p.1, p.2.1⟩ : Σ N : ℕ, DirichletCharacter ℂ (N + 1)))
      (fun p hp => Finset.mem_image_of_mem _ hp)]
    apply Finset.sum_le_sum
    intro x _
    rw [← intervalIntegral.integral_finset_sum (fun p _ => (hW _ _).intervalIntegrable _ _)]
    apply intervalIntegral.integral_mono_on hle
    · exact (continuous_finset_sum _ (fun p _ => hW _ _)).intervalIntegrable _ _
    · exact (hGcont x).intervalIntegrable _ _
    intro σ _
    set fib := T.filter (fun p => (⟨p.1, p.2.1⟩ : Σ N : ℕ, DirichletCharacter ℂ (N + 1)) = x) with hfib
    have hrw : ∀ p ∈ fib, (∫ t in (p.2.2.im - r)..(p.2.2.im + r), ‖F ⟨p.1, p.2.1⟩ (σ + t * I)‖ ^ 2) =
        ∫ t in (p.2.2.im - r)..(p.2.2.im + r), ‖F x (σ + t * I)‖ ^ 2 := by
      intro p hp
      rw [hfib, Finset.mem_filter] at hp
      rw [hp.2]
    rw [Finset.sum_congr rfl hrw]
    have hinj : Set.InjOn (fun p : (Σ N : ℕ, DirichletCharacter ℂ (N + 1) × ℂ) => p.2.2.im) fib := by
      intro p hp p' hp' him
      rw [Finset.mem_coe, hfib, Finset.mem_filter] at hp hp'
      obtain ⟨N, χ, ρ⟩ := p
      obtain ⟨N', χ', ρ'⟩ := p'
      have hkey : (⟨N, χ⟩ : Σ N : ℕ, DirichletCharacter ℂ (N + 1)) = ⟨N', χ'⟩ := hp.2.trans hp'.2.symm
      obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.mp hkey
      cases h
      by_contra hne
      have hρ : ρ ≠ ρ' := fun e => hne (by rw [e])
      have := hsep N χ ρ ρ' hp.1 hp'.1 hρ
      simp only at him
      rw [him, sub_self, abs_zero] at this
      norm_num at this
    rw [← Finset.sum_image (f := fun a => ∫ t in (a - r)..(a + r), ‖F x (σ + t * I)‖ ^ 2) hinj]
    apply sum_integral_separated_windows_le (fun t => ‖F x (σ + t * I)‖ ^ 2)
      (by have := (hFdiff x).continuous; fun_prop) (fun t => by positivity) _ r Tm (by rw [hr]; norm_num)
    · intro a ha b hb hab
      rw [Finset.mem_image] at ha hb
      obtain ⟨p, hp, rfl⟩ := ha
      obtain ⟨p', hp', rfl⟩ := hb
      rw [hfib, Finset.mem_filter] at hp hp'
      obtain ⟨N, χ, ρ⟩ := p
      obtain ⟨N', χ', ρ'⟩ := p'
      have hkey : (⟨N, χ⟩ : Σ N : ℕ, DirichletCharacter ℂ (N + 1)) = ⟨N', χ'⟩ := hp.2.trans hp'.2.symm
      obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.mp hkey
      cases h
      have hρ : ρ ≠ ρ' := fun e => hab (by rw [e])
      have := hsep N χ ρ ρ' hp.1 hp'.1 hρ
      simp only
      rw [hr]; linarith
    · intro a ha
      rw [Finset.mem_image] at ha
      obtain ⟨p, hp, rfl⟩ := ha
      rw [hfib, Finset.mem_filter] at hp
      have hb := (hT p hp.1).2.2.2.2.1
      rw [abs_le] at hb
      rw [hTm, hr]
      constructor <;> linarith [hb.1, hb.2]
    · rw [hTm]; linarith
  have hsieve : ∀ σ ∈ Set.Icc σ₀ σ₁, ∑ x ∈ P, G x σ ≤ C₂ * (3 * K ^ 2 * 80) * (Q : ℝ) ^ ((1 : ℝ) / 8) := by
    intro σ hσ
    set a : ℕ → ℂ := fun n => if n ∈ Finset.Ioc (Q ^ 3) (Q ^ 6) then
      ((∑ d ∈ n.divisors.filter (fun d => d ≤ Q ^ 3), (moebius d : ℤ) : ℤ) : ℂ) * (n : ℂ) ^ (-(σ : ℂ)) else 0
      with ha
    have hsub : Finset.Ioc (Q ^ 3) (Q ^ 6) ⊆ Finset.Icc 1 (Q ^ 6) := by
      intro n hn
      rw [Finset.mem_Ioc] at hn
      rw [Finset.mem_Icc]
      exact ⟨by have := Nat.zero_le (Q ^ 3); omega, hn.2⟩
    have hrepr : ∀ (x : Σ N : ℕ, DirichletCharacter ℂ (N + 1)) (t : ℝ),
        F x (σ + t * I) = ∑ n ∈ Finset.Icc 1 (Q ^ 6), a n * x.2 (n : ZMod (x.1 + 1)) * (n : ℂ) ^ (-(t * I)) := by
      intro x t
      rw [← Finset.sum_subset hsub (fun n _ hn => by rw [ha]; simp [hn])]
      simp only [hF, _root_.GlobalTheory.SpacedDetected.poly, hc]
      apply Finset.sum_congr rfl
      intro n hn
      have hn0 : (n : ℂ) ≠ 0 := by
        have := (Finset.mem_Ioc.mp hn).1
        exact_mod_cast (show n ≠ 0 by omega)
      rw [ha]
      simp only [if_pos hn]
      rw [neg_add, Complex.cpow_add _ _ hn0]
      ring
    set H : (Σ N : ℕ, DirichletCharacter ℂ (N + 1)) → ℝ := fun x =>
      ∫ t in (-Tm)..Tm, ‖∑ n ∈ Finset.Icc 1 (Q ^ 6), a n * x.2 (n : ZMod (x.1 + 1)) * (n : ℂ) ^ (-(t * I))‖ ^ 2
      with hH
    have hGH : ∀ x, G x σ = H x := by
      intro x
      simp only [hG, hH, hrepr]
    have hTm1 : (1 : ℝ) ≤ Tm := by rw [hTm]; linarith
    have hHnn : ∀ x, 0 ≤ H x := fun x =>
      intervalIntegral.integral_nonneg (by linarith) (fun t _ => by positivity)
    simp only [hGH]
    have hPsub : P ⊆ (Finset.range Q).sigma (fun q => Finset.univ.filter (fun χ : DirichletCharacter ℂ (q + 1) => χ.IsPrimitive)) := by
      intro x hx
      rw [hP, Finset.mem_image] at hx
      obtain ⟨p, hp, rfl⟩ := hx
      obtain ⟨h1, h2, -⟩ := hT p hp
      rw [Finset.mem_sigma, Finset.mem_range, Finset.mem_filter]
      exact ⟨by show p.1 < Q; omega, Finset.mem_univ _, h2⟩
    calc ∑ x ∈ P, H x ≤ ∑ x ∈ (Finset.range Q).sigma (fun q => Finset.univ.filter (fun χ : DirichletCharacter ℂ (q + 1) => χ.IsPrimitive)), H x :=
          Finset.sum_le_sum_of_subset_of_nonneg hPsub (fun x _ _ => hHnn x)
      _ = ∑ q ∈ Finset.range Q, ∑ᶠ (χ : DirichletCharacter ℂ (q + 1)) (_ : χ ∈ {χ : DirichletCharacter ℂ (q + 1) | χ.IsPrimitive}),
            ∫ t in (-Tm)..Tm, ‖∑ n ∈ Finset.Icc 1 (Q ^ 6), a n * χ n * (n : ℂ) ^ (-(t * I))‖ ^ 2 := by
          rw [Finset.sum_sigma]
          apply Finset.sum_congr rfl
          intro q _
          rw [finsum_mem_eq_toFinset_sum, Set.toFinset_setOf]
      _ ≤ C₂ * ∑ n ∈ Finset.Icc 1 (Q ^ 6), ((Q : ℝ) ^ 2 * Tm + n) * ‖a n‖ ^ 2 :=
          hls Q (Q ^ 6) a Tm (by omega) hTm1
      _ ≤ C₂ * (3 * K ^ 2 * 80 * (Q : ℝ) ^ ((1 : ℝ) / 8)) := by
          refine mul_le_mul_of_nonneg_left ?_ hC₂.le
          have hσ' : 1 - 3 / 800 ≤ σ := by
            have := hσ.1; rw [hσ₀, hr] at this; linarith
          exact sum_weighted_moebius_coeff_sq_le K hK hdiv Q hQ σ hσ'
      _ = C₂ * (3 * K ^ 2 * 80) * (Q : ℝ) ^ ((1 : ℝ) / 8) := by ring
  have hint : ∑ x ∈ P, ∫ σ in σ₀..σ₁, G x σ ≤ (1 / 200) * (C₂ * (3 * K ^ 2 * 80) * (Q : ℝ) ^ ((1 : ℝ) / 8)) := by
    rw [← intervalIntegral.integral_finset_sum (fun x _ => (hGcont x).intervalIntegrable _ _)]
    have hle : σ₀ ≤ σ₁ := by rw [hσ₀, hσ₁, hr]; norm_num
    calc ∫ σ in σ₀..σ₁, ∑ x ∈ P, G x σ ≤ ∫ σ in σ₀..σ₁, C₂ * (3 * K ^ 2 * 80) * (Q : ℝ) ^ ((1 : ℝ) / 8) := by
          apply intervalIntegral.integral_mono_on hle
          · exact (continuous_finset_sum _ (fun x _ => hGcont x)).intervalIntegrable _ _
          · exact intervalIntegrable_const
          · exact hsieve
      _ = (1 / 200) * (C₂ * (3 * K ^ 2 * 80) * (Q : ℝ) ^ ((1 : ℝ) / 8)) := by
          rw [intervalIntegral.integral_const, smul_eq_mul, hσ₀, hσ₁, hr]; norm_num
  have hsum : (T.card : ℝ) * (1 / 4) ≤ C₁ / r ^ 2 * ∑ p ∈ T, ∫ σ in σ₀..σ₁,
      ∫ t in (p.2.2.im - r)..(p.2.2.im + r), ‖F ⟨p.1, p.2.1⟩ (σ + t * I)‖ ^ 2 := by
    rw [Finset.mul_sum]
    calc (T.card : ℝ) * (1 / 4) = ∑ p ∈ T, (1 / 4 : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum hpt
  have hCr : 0 ≤ C₁ / r ^ 2 := by positivity
  calc (T.card : ℝ) = 4 * ((T.card : ℝ) * (1 / 4)) := by ring
    _ ≤ 4 * (C₁ / r ^ 2 * ((1 / 200) * (C₂ * (3 * K ^ 2 * 80) * (Q : ℝ) ^ ((1 : ℝ) / 8)))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        exact hsum.trans (mul_le_mul_of_nonneg_left (hgroup.trans hint) hCr)
    _ = _ := by rw [hr]; ring

end GlobalTheory.SpacedDetected
