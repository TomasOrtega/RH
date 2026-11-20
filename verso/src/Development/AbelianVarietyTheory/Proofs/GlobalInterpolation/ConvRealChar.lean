import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LamIdealOfNotPrimePow

open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical

noncomputable section

namespace GlobalTheory.Hk.RaySq

variable {K : Type} [Field K] [NumberField K]

def normEq (K : Type) [Field K] [NumberField K] (n : ℕ) : Finset (Ideal (𝓞 K)) :=
  (Ideal.finite_setOf_absNorm_eq (S := 𝓞 K) n).toFinset

/- English proof (translation)
Simplify using `[normEq]`.
-/
lemma mem_normEq {n : ℕ} {I : Ideal (𝓞 K)} : I ∈ normEq K n ↔ Ideal.absNorm I = n := by
  simp [normEq]

def dv (C : Ideal (𝓞 K)) : Finset (Ideal (𝓞 K)) :=
  ((Ideal.finite_setOf_absNorm_le (S := 𝓞 K) (Ideal.absNorm C)).toFinset).filter (· ∣ C)

/- English proof (translation)
Simplify using `only [dv, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq, and_iff_right_iff_imp]`. Introduce `h`. Establish `hC' : Ideal.absNorm C ≠ 0`. Rewrite using `[Ne, Ideal.absNorm_eq_zero_iff]`. Conclude with `hC`.

Conclude with `Nat.le_of_dvd (Nat.pos_of_ne_zero hC') (map_dvd Ideal.absNorm h)`.
-/
lemma mem_dv {C J : Ideal (𝓞 K)} (hC : C ≠ 0) : J ∈ dv C ↔ J ∣ C := by
  simp only [dv, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq, and_iff_right_iff_imp]
  intro h
  have hC' : Ideal.absNorm C ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact hC
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero hC') (map_dvd Ideal.absNorm h)

def r (f : Ideal (𝓞 K) → ℝ) (C : Ideal (𝓞 K)) : ℝ := ∑ J ∈ dv C, f J

/- English proof (translation)
Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Introduce `h`.

Apply `ih` to reduce the goal to its premises. Take `⟨Y, hY⟩` from `h`. Establish `hPY : P ∣ J * Y` using `⟨P ^ k * C, by rw [← hY]; ring⟩`. Break down `hP.dvd_or_dvd hPY with h1 | ⟨Y', rfl⟩` into its components or cases. Conclude with `absurd h1 hJ`.

Use `⟨Y', ?_⟩` and prove the remaining obligations. Apply `mul_left_cancel₀ hP.ne_zero` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation.
-/
private lemma dvd_of_dvd_prime_pow_mul' {P C J : Ideal (𝓞 K)} (hP : Prime P) (hJ : ¬ P ∣ J) :
    ∀ k : ℕ, J ∣ P ^ k * C → J ∣ C := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    intro h
    apply ih
    obtain ⟨Y, hY⟩ := h
    have hPY : P ∣ J * Y := ⟨P ^ k * C, by rw [← hY]; ring⟩
    rcases hP.dvd_or_dvd hPY with h1 | ⟨Y', rfl⟩
    · exact absurd h1 hJ
    · refine ⟨Y', ?_⟩
      apply mul_left_cancel₀ hP.ne_zero
      calc P * (P ^ k * C) = P ^ (k + 1) * C := by ring
        _ = J * (P * Y') := hY
        _ = P * (J * Y') := by ring

/- English proof (translation)
Establish `hP0 : P ≠ 0` using `hP.ne_zero`. Establish `hA : P ^ (k + 1) * C ≠ 0` using `mul_ne_zero (pow_ne_zero _ hP0) hC`. Establish `hB : P ^ k * C ≠ 0` using `mul_ne_zero (pow_ne_zero _ hP0) hC`. Establish `hsplit : dv (P ^ (k + 1) * C) = dv C ∪ (dv (P ^ k * C)).image (P * ·)`. Use extensionality with `J`.

Rewrite using `[Finset.mem_union, Finset.mem_image, mem_dv hA, mem_dv hC]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Distinguish the cases in `hJ : P ∣ J`. Use `right`.

Take `⟨J', rfl⟩` from `hJ`. Use `⟨J', (mem_dv hB).2 ?_, rfl⟩` and prove the remaining obligations. Take `⟨Y, hY⟩` from `h`. Use `⟨Y, mul_left_cancel₀ hP0 ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Use `left`. Conclude with `dvd_of_dvd_prime_pow_mul' hP hJ (k + 1) h`. Introduce and unpack `(h | ⟨J', hJ', rfl⟩)`. Conclude with `h.trans ⟨P ^ (k + 1), by ring⟩`. Rewrite `hJ'` using `[mem_dv hB]`.

Establish `e : P * (P ^ k * C) = P ^ (k + 1) * C` using `by ring`. Rewrite using `[← e]`. Conclude with `mul_dvd_mul_left P hJ'`. Establish `hdisj : Disjoint (dv C) ((dv (P ^ k * C)).image (P * ·))`. Rewrite using `[Finset.disjoint_left]`.

Introduce `J hJ hJ'`. Rewrite `hJ` using `[mem_dv hC]`. Take `⟨J', -, rfl⟩` from `Finset.mem_image.1 hJ'`. Conclude with `hPC ((dvd_mul_right P J').trans hJ)`. Unfold `r`.

Rewrite using `[hsplit, Finset.sum_union hdisj, Finset.sum_image (fun a _ b _ hab => mul_left_cancel₀ hP0 hab)]`. Simplify using `only [hf, ← Finset.mul_sum]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma r_step (f : Ideal (𝓞 K) → ℝ) (hf : ∀ I J, f (I * J) = f I * f J) {P C : Ideal (𝓞 K)} (hP : Prime P) (hC : C ≠ 0)
    (hPC : ¬ P ∣ C) (k : ℕ) : r f (P ^ (k + 1) * C) = f P * r f (P ^ k * C) + r f C := by
  have hP0 : P ≠ 0 := hP.ne_zero
  have hA : P ^ (k + 1) * C ≠ 0 := mul_ne_zero (pow_ne_zero _ hP0) hC
  have hB : P ^ k * C ≠ 0 := mul_ne_zero (pow_ne_zero _ hP0) hC
  have hsplit : dv (P ^ (k + 1) * C) = dv C ∪ (dv (P ^ k * C)).image (P * ·) := by
    ext J
    rw [Finset.mem_union, Finset.mem_image, mem_dv hA, mem_dv hC]
    constructor
    · intro h
      by_cases hJ : P ∣ J
      · right
        obtain ⟨J', rfl⟩ := hJ
        refine ⟨J', (mem_dv hB).2 ?_, rfl⟩
        obtain ⟨Y, hY⟩ := h
        refine ⟨Y, mul_left_cancel₀ hP0 ?_⟩
        calc P * (P ^ k * C) = P ^ (k + 1) * C := by ring
          _ = P * J' * Y := hY
          _ = P * (J' * Y) := by ring
      · left
        exact dvd_of_dvd_prime_pow_mul' hP hJ (k + 1) h
    · rintro (h | ⟨J', hJ', rfl⟩)
      · exact h.trans ⟨P ^ (k + 1), by ring⟩
      · rw [mem_dv hB] at hJ'
        have e : P * (P ^ k * C) = P ^ (k + 1) * C := by ring
        rw [← e]
        exact mul_dvd_mul_left P hJ'
  have hdisj : Disjoint (dv C) ((dv (P ^ k * C)).image (P * ·)) := by
    rw [Finset.disjoint_left]
    intro J hJ hJ'
    rw [mem_dv hC] at hJ
    obtain ⟨J', -, rfl⟩ := Finset.mem_image.1 hJ'
    exact hPC ((dvd_mul_right P J').trans hJ)
  unfold r
  rw [hsplit, Finset.sum_union hdisj, Finset.sum_image (fun a _ b _ hab => mul_left_cancel₀ hP0 hab)]
  simp only [hf, ← Finset.mul_sum]
  ring

/- English proof (translation)
Establish `hg : ∀ m : ℕ, ∑ i ∈ Finset.range (m + 1), f P ^ i = f P * ∑ i ∈ Finset.range m, f P ^ i + 1`. Introduce `m`. Rewrite using `[Finset.sum_range_succ', Finset.mul_sum]`. Simplify using `only [pow_succ', pow_zero]`. Proceed by induction on `k with`.

Consider the case `zero => simp`. Consider the case `succ k ih`. Rewrite using `[r_step f hf hP hC hPC k, ih, hg (k + 1)]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma r_pow (f : Ideal (𝓞 K) → ℝ) (hf : ∀ I J, f (I * J) = f I * f J) {P C : Ideal (𝓞 K)} (hP : Prime P) (hC : C ≠ 0)
    (hPC : ¬ P ∣ C) (k : ℕ) : r f (P ^ k * C) = (∑ i ∈ Finset.range (k + 1), f P ^ i) * r f C := by
  have hg : ∀ m : ℕ, ∑ i ∈ Finset.range (m + 1), f P ^ i = f P * ∑ i ∈ Finset.range m, f P ^ i + 1 := by
    intro m
    rw [Finset.sum_range_succ', Finset.mul_sum]
    simp only [pow_succ', pow_zero]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [r_step f hf hP hC hPC k, ih, hg (k + 1)]
    ring

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[Finset.sum_range_succ, ih]`. Distinguish the cases in `h : Even n`.

Establish `h' : ¬ Even (n + 1)` using `by rw [Nat.even_add_one]; exact not_not.2 h`. Rewrite using `[if_pos h, if_neg h', h.neg_one_pow]`. Evaluate the numerical expressions. Establish `h' : Even (n + 1)` using `Nat.even_add_one.2 h`. Rewrite using `[if_neg h, if_pos h', (Nat.not_even_iff_odd.1 h).neg_one_pow]`.

Evaluate the numerical expressions.
-/
private lemma sum_range_neg_one_pow_eq_ite (n : ℕ) :
    ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i = if Even n then 0 else 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    by_cases h : Even n
    · have h' : ¬ Even (n + 1) := by rw [Nat.even_add_one]; exact not_not.2 h
      rw [if_pos h, if_neg h', h.neg_one_pow]
      norm_num
    · have h' : Even (n + 1) := Nat.even_add_one.2 h
      rw [if_neg h, if_pos h', (Nat.not_even_iff_odd.1 h).neg_one_pow]
      norm_num

/- English proof (translation)
Break down `hx with rfl | rfl | rfl` into its components or cases. Simplify using `[Finset.sum_range_succ']`. Simplify using `only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]`. Use `⟨by positivity, ?_⟩` and prove the remaining obligations. Use `push_cast`.

Combine the linear relations using `[(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]`. Rewrite using `[sum_range_neg_one_pow_eq_ite, sum_range_neg_one_pow_eq_ite]`. Establish `h : ¬ Even (2 * k + 1)`. Rewrite using `[Nat.even_add_one, not_not]`. Conclude with `even_two_mul k`.

Rewrite using `[if_neg h]`. Use `⟨?_, le_refl _⟩` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> norm_num`.
-/
lemma geom_bounds {x : ℝ} (hx : x = 0 ∨ x = 1 ∨ x = -1) (k : ℕ) :
    0 ≤ ∑ i ∈ Finset.range (k + 1), x ^ i ∧ 1 ≤ ∑ i ∈ Finset.range (2 * k + 1), x ^ i := by
  rcases hx with rfl | rfl | rfl
  · simp [Finset.sum_range_succ']
  · simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    refine ⟨by positivity, ?_⟩
    push_cast
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  · rw [sum_range_neg_one_pow_eq_ite, sum_range_neg_one_pow_eq_ite]
    have h : ¬ Even (2 * k + 1) := by
      rw [Nat.even_add_one, not_not]
      exact even_two_mul k
    rw [if_neg h]
    refine ⟨?_, le_refl _⟩
    split_ifs <;> norm_num

/- English proof (translation)
Establish `hd : dv (1 : Ideal (𝓞 K)) = {1}`. Use extensionality with `J`. Rewrite using `[mem_dv one_ne_zero, Finset.mem_singleton, Ideal.dvd_iff_le, Ideal.one_eq_top, top_le_iff]`. Unfold `r`. Rewrite using `[hd, Finset.sum_singleton, h1]`.
-/
lemma r_one (f : Ideal (𝓞 K) → ℝ) (h1 : f 1 = 1) : r f 1 = 1 := by
  have hd : dv (1 : Ideal (𝓞 K)) = {1} := by
    ext J
    rw [mem_dv one_ne_zero, Finset.mem_singleton, Ideal.dvd_iff_le, Ideal.one_eq_top, top_le_iff]
  unfold r
  rw [hd, Finset.sum_singleton, h1]

/- English proof (translation)
It suffices to establish `h : ∀ N : ℕ, ∀ C : Ideal (𝓞 K), C ≠ 0 → Ideal.absNorm C = N → 0 ≤ r f C ∧ 1 ≤ r f (C ^ 2) from h _ C hC rfl`. Introduce `N`. Proceed by induction on `N using Nat.strong_induction_on with`. Consider the case `_ N ih`. Introduce `C hC hN`.

Distinguish the cases in `hu : IsUnit C`. Take `rfl : C = 1` from `isUnit_iff_eq_one.1 hu`. Rewrite using `[one_pow, r_one f h1]`. Evaluate the numerical expressions. Take `⟨P, hPirr, hPC⟩` from `WfDvdMonoid.exists_irreducible_factor hu hC`.

Establish `hP : Prime P` using `UniqueFactorizationMonoid.irreducible_iff_prime.1 hPirr`. Take `⟨k, D, hPD, rfl⟩` from `WfDvdMonoid.max_power_factor hC hPirr`. Establish `hD : D ≠ 0`. Introduce and unpack `rfl`. Conclude with `hC (mul_zero _)`.

Establish `hk : k ≠ 0`. Introduce and unpack `rfl`. Rewrite `hPC` using `[pow_zero, one_mul]`. Conclude with `hPD hPC`. Establish `hN2 : 2 ≤ Ideal.absNorm P`.

Establish `h0 : Ideal.absNorm P ≠ 0`. Rewrite using `[Ne, Ideal.absNorm_eq_zero_iff]`. Conclude with `hP.ne_zero`. Establish `h1' : Ideal.absNorm P ≠ 1`. Rewrite using `[Ne, Ideal.absNorm_eq_one_iff]`.

Introduce `h`. Apply `hPirr.not_isUnit` to reduce the goal to its premises. Rewrite using `[h, ← Ideal.one_eq_top]`. Conclude with `isUnit_one`. Use linear arithmetic over natural numbers and integers.

Establish `hD0 : 0 < Ideal.absNorm D`. Apply `Nat.pos_of_ne_zero` to reduce the goal to its premises. Rewrite using `[Ne, Ideal.absNorm_eq_zero_iff]`. Conclude with `hD`. Establish `hlt : Ideal.absNorm D < N`.

Rewrite using `[← hN, map_mul, map_pow]`. Establish `h2 : 2 ≤ Ideal.absNorm P ^ k` using `le_trans hN2 (Nat.le_self_pow hk _)`. Use the polynomial consequences of the given equalities and inequalities. Take `⟨ihD1, ihD2⟩` from `ih _ hlt D hD rfl`. Establish `hPD2 : ¬ P ∣ D ^ 2`.

Rewrite using `[pow_two]`. Introduce `h`. Apply the tactic sequence `rcases hP.dvd_or_dvd h with h | h <;> exact hPD h`. Establish `hD2 : D ^ 2 ≠ 0` using `pow_ne_zero _ hD`. Take `⟨g1, g2⟩` from `geom_bounds (hv P) k`.

Prove the components needed by the constructor for the conclusion. Rewrite using `[r_pow f hf hP hD hPD k]`. Conclude with `mul_nonneg g1 ihD1`. Establish `e : (P ^ k * D) ^ 2 = P ^ (2 * k) * D ^ 2` using `by ring`. Rewrite using `[e, r_pow f hf hP hD2 hPD2 (2 * k)]`.

Conclude with `one_le_mul_of_one_le_of_one_le g2 ihD2`.
-/
lemma r_bounds (f : Ideal (𝓞 K) → ℝ) (h1 : f 1 = 1) (hf : ∀ I J, f (I * J) = f I * f J)
    (hv : ∀ I, f I = 0 ∨ f I = 1 ∨ f I = -1) (C : Ideal (𝓞 K)) (hC : C ≠ 0) : 0 ≤ r f C ∧ 1 ≤ r f (C ^ 2) := by
  suffices h : ∀ N : ℕ, ∀ C : Ideal (𝓞 K), C ≠ 0 → Ideal.absNorm C = N →
      0 ≤ r f C ∧ 1 ≤ r f (C ^ 2) from h _ C hC rfl
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro C hC hN
  by_cases hu : IsUnit C
  · obtain rfl : C = 1 := isUnit_iff_eq_one.1 hu
    rw [one_pow, r_one f h1]
    norm_num
  · obtain ⟨P, hPirr, hPC⟩ := WfDvdMonoid.exists_irreducible_factor hu hC
    have hP : Prime P := UniqueFactorizationMonoid.irreducible_iff_prime.1 hPirr
    obtain ⟨k, D, hPD, rfl⟩ := WfDvdMonoid.max_power_factor hC hPirr
    have hD : D ≠ 0 := by
      rintro rfl
      exact hC (mul_zero _)
    have hk : k ≠ 0 := by
      rintro rfl
      rw [pow_zero, one_mul] at hPC
      exact hPD hPC
    have hN2 : 2 ≤ Ideal.absNorm P := by
      have h0 : Ideal.absNorm P ≠ 0 := by
        rw [Ne, Ideal.absNorm_eq_zero_iff]
        exact hP.ne_zero
      have h1' : Ideal.absNorm P ≠ 1 := by
        rw [Ne, Ideal.absNorm_eq_one_iff]
        intro h
        apply hPirr.not_isUnit
        rw [h, ← Ideal.one_eq_top]
        exact isUnit_one
      omega
    have hD0 : 0 < Ideal.absNorm D := by
      apply Nat.pos_of_ne_zero
      rw [Ne, Ideal.absNorm_eq_zero_iff]
      exact hD
    have hlt : Ideal.absNorm D < N := by
      rw [← hN, map_mul, map_pow]
      have h2 : 2 ≤ Ideal.absNorm P ^ k := le_trans hN2 (Nat.le_self_pow hk _)
      nlinarith
    obtain ⟨ihD1, ihD2⟩ := ih _ hlt D hD rfl
    have hPD2 : ¬ P ∣ D ^ 2 := by
      rw [pow_two]
      intro h
      rcases hP.dvd_or_dvd h with h | h <;> exact hPD h
    have hD2 : D ^ 2 ≠ 0 := pow_ne_zero _ hD
    obtain ⟨g1, g2⟩ := geom_bounds (hv P) k
    constructor
    · rw [r_pow f hf hP hD hPD k]
      exact mul_nonneg g1 ihD1
    · have e : (P ^ k * D) ^ 2 = P ^ (2 * k) * D ^ 2 := by ring
      rw [e, r_pow f hf hP hD2 hPD2 (2 * k)]
      exact one_le_mul_of_one_le_of_one_le g2 ihD2

/- English proof (translation)
Establish `L : (∑ p ∈ n.divisorsAntidiagonal, ∑ I ∈ normEq K p.1, ∑ J ∈ normEq K p.2, F (I * J) J) = ∑ y ∈ n.divisorsAntidiagonal.sigma (fun p => normEq K p.1 ×ˢ normEq K p.2), F (y.2.1 * y.2.2) y.2.2`. Rewrite using `[Finset.sum_sigma]`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_product]`. Establish `R : (∑ C ∈ normEq K n, ∑ J ∈ dv C, F C J) = ∑ y ∈ (normEq K n).sigma (fun C => dv C), F y.1 y.2`.

Rewrite using `[Finset.sum_sigma]`. Rewrite using `[L, R]`. Use `Finset.sum_nbij' (fun y : (Σ _ : ℕ × ℕ, Ideal (𝓞 K) × Ideal (𝓞 K)) => (⟨y.2.1 * y.2.2, y.2.2⟩ : Σ _ : Ideal (𝓞 K), Ideal (𝓞 K))) (fun y : (Σ _ : Ideal (𝓞 K), Ideal (𝓞 K)) => (⟨(Ideal.absNorm y.1 / Ideal.absNorm y.2, Ideal.absNorm y.2), ((if h : y.2 ∣ y.1 then Exists.choose h else …` and prove the remaining obligations. Introduce and unpack `⟨⟨a, b⟩, I, J⟩ hy`. Simplify using `only [Finset.mem_sigma, Finset.mem_product, Nat.mem_divisorsAntidiagonal, mem_normEq] at hy ⊢`.

Take `⟨⟨hab, -⟩, hI, hJ⟩` from `hy`. Establish `hIJ0 : I * J ≠ 0`. Introduce `h`. Establish `e` using `congrArg Ideal.absNorm h`. Rewrite `e` using `[map_mul, _root_.map_zero, hI, hJ, hab]`.

Conclude with `hn e`. Conclude with `⟨by rw [map_mul, hI, hJ, hab], (mem_dv hIJ0).2 (dvd_mul_left J I)⟩`. Introduce and unpack `⟨C, J⟩ hy`. Simplify using `only [Finset.mem_sigma, mem_normEq] at hy`. Take `⟨hCn, hJ⟩` from `hy`.

Establish `hC0 : C ≠ 0`. Introduce and unpack `rfl`. Rewrite `hCn` using `[_root_.map_zero]`. Conclude with `hn hCn.symm`. Take `⟨c, rfl⟩` from `(mem_dv hC0).1 hJ`.

Establish `hJ0 : J ≠ 0`. Introduce and unpack `rfl`. Conclude with `hC0 (zero_mul c)`. Establish `hch : (if h : J ∣ J * c then Exists.choose h else 0) = c`. Rewrite using `[dif_pos (dvd_mul_right J c)]`.

Conclude with `mul_left_cancel₀ hJ0 (Exists.choose_spec (dvd_mul_right J c)).symm`. Establish `hNJ : 0 < Ideal.absNorm J`. Apply `Nat.pos_of_ne_zero` to reduce the goal to its premises. Rewrite using `[Ne, Ideal.absNorm_eq_zero_iff]`. Conclude with `hJ0`.

Simplify using `only [Finset.mem_sigma, Finset.mem_product, Nat.mem_divisorsAntidiagonal, mem_normEq]`. Rewrite using `[hch, map_mul, Nat.mul_div_cancel_left _ hNJ]`. Rewrite `hCn` using `[map_mul]`. Conclude with `⟨⟨by rw [mul_comm]; exact hCn, hn⟩, rfl, trivial⟩`. Introduce and unpack `⟨⟨a, b⟩, I, J⟩ hy`.

Simplify using `only [Finset.mem_sigma, Finset.mem_product, Nat.mem_divisorsAntidiagonal, mem_normEq] at hy`. Take `⟨⟨hab, -⟩, hI, hJ⟩` from `hy`. Establish `hJ0 : J ≠ 0`. Introduce and unpack `rfl`. Rewrite `hJ` using `[_root_.map_zero]`.

Substitute `hJ` using the available equality. Conclude with `hn (by rw [← hab, mul_zero])`. Establish `hNJ : 0 < Ideal.absNorm J`. Apply `Nat.pos_of_ne_zero` to reduce the goal to its premises. Rewrite using `[Ne, Ideal.absNorm_eq_zero_iff]`.

Conclude with `hJ0`. Establish `hch : (if h : J ∣ I * J then Exists.choose h else 0) = I`. Rewrite using `[dif_pos (dvd_mul_left J I)]`. Apply `mul_left_cancel₀ hJ0` to reduce the goal to its premises. Rewrite using `[← Exists.choose_spec (dvd_mul_left J I), mul_comm]`.

Simplify using `only`. Rewrite using `[hch, map_mul, Nat.mul_div_cancel _ hNJ, hI, hJ]`. Introduce and unpack `⟨C, J⟩ hy`. Simplify using `only [Finset.mem_sigma, mem_normEq] at hy`. Take `⟨hCn, hJ⟩` from `hy`.

Establish `hC0 : C ≠ 0`. Introduce and unpack `rfl`. Rewrite `hCn` using `[_root_.map_zero]`. Conclude with `hn hCn.symm`. Take `⟨c, rfl⟩` from `(mem_dv hC0).1 hJ`.

Establish `hJ0 : J ≠ 0`. Introduce and unpack `rfl`. Conclude with `hC0 (zero_mul c)`. Establish `hch : (if h : J ∣ J * c then Exists.choose h else 0) = c`. Rewrite using `[dif_pos (dvd_mul_right J c)]`.

Conclude with `mul_left_cancel₀ hJ0 (Exists.choose_spec (dvd_mul_right J c)).symm`. Simplify using `only`. Rewrite using `[hch, mul_comm]`. Introduce and unpack `⟨p, I, J⟩ _`. Both sides reduce to the same expression.
-/
lemma conv_eq (F : Ideal (𝓞 K) → Ideal (𝓞 K) → ℝ) {n : ℕ} (hn : n ≠ 0) :
    ∑ p ∈ n.divisorsAntidiagonal, ∑ I ∈ normEq K p.1, ∑ J ∈ normEq K p.2, F (I * J) J =
      ∑ C ∈ normEq K n, ∑ J ∈ dv C, F C J := by
  have L : (∑ p ∈ n.divisorsAntidiagonal, ∑ I ∈ normEq K p.1, ∑ J ∈ normEq K p.2, F (I * J) J) =
      ∑ y ∈ n.divisorsAntidiagonal.sigma (fun p => normEq K p.1 ×ˢ normEq K p.2),
        F (y.2.1 * y.2.2) y.2.2 := by
    rw [Finset.sum_sigma]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_product]
  have R : (∑ C ∈ normEq K n, ∑ J ∈ dv C, F C J) =
      ∑ y ∈ (normEq K n).sigma (fun C => dv C), F y.1 y.2 := by
    rw [Finset.sum_sigma]
  rw [L, R]
  refine Finset.sum_nbij'
    (fun y : (Σ _ : ℕ × ℕ, Ideal (𝓞 K) × Ideal (𝓞 K)) =>
      (⟨y.2.1 * y.2.2, y.2.2⟩ : Σ _ : Ideal (𝓞 K), Ideal (𝓞 K)))
    (fun y : (Σ _ : Ideal (𝓞 K), Ideal (𝓞 K)) =>
      (⟨(Ideal.absNorm y.1 / Ideal.absNorm y.2, Ideal.absNorm y.2),
        ((if h : y.2 ∣ y.1 then Exists.choose h else 0), y.2)⟩ :
        Σ _ : ℕ × ℕ, Ideal (𝓞 K) × Ideal (𝓞 K))) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨⟨a, b⟩, I, J⟩ hy
    simp only [Finset.mem_sigma, Finset.mem_product, Nat.mem_divisorsAntidiagonal, mem_normEq] at hy ⊢
    obtain ⟨⟨hab, -⟩, hI, hJ⟩ := hy
    have hIJ0 : I * J ≠ 0 := by
      intro h
      have e := congrArg Ideal.absNorm h
      rw [map_mul, _root_.map_zero, hI, hJ, hab] at e
      exact hn e
    exact ⟨by rw [map_mul, hI, hJ, hab], (mem_dv hIJ0).2 (dvd_mul_left J I)⟩
  · rintro ⟨C, J⟩ hy
    simp only [Finset.mem_sigma, mem_normEq] at hy
    obtain ⟨hCn, hJ⟩ := hy
    have hC0 : C ≠ 0 := by
      rintro rfl
      rw [_root_.map_zero] at hCn
      exact hn hCn.symm
    obtain ⟨c, rfl⟩ := (mem_dv hC0).1 hJ
    have hJ0 : J ≠ 0 := by
      rintro rfl
      exact hC0 (zero_mul c)
    have hch : (if h : J ∣ J * c then Exists.choose h else 0) = c := by
      rw [dif_pos (dvd_mul_right J c)]
      exact mul_left_cancel₀ hJ0 (Exists.choose_spec (dvd_mul_right J c)).symm
    have hNJ : 0 < Ideal.absNorm J := by
      apply Nat.pos_of_ne_zero
      rw [Ne, Ideal.absNorm_eq_zero_iff]
      exact hJ0
    simp only [Finset.mem_sigma, Finset.mem_product, Nat.mem_divisorsAntidiagonal, mem_normEq]
    rw [hch, map_mul, Nat.mul_div_cancel_left _ hNJ]
    rw [map_mul] at hCn
    exact ⟨⟨by rw [mul_comm]; exact hCn, hn⟩, rfl, trivial⟩
  · rintro ⟨⟨a, b⟩, I, J⟩ hy
    simp only [Finset.mem_sigma, Finset.mem_product, Nat.mem_divisorsAntidiagonal, mem_normEq] at hy
    obtain ⟨⟨hab, -⟩, hI, hJ⟩ := hy
    have hJ0 : J ≠ 0 := by
      rintro rfl
      rw [_root_.map_zero] at hJ
      subst hJ
      exact hn (by rw [← hab, mul_zero])
    have hNJ : 0 < Ideal.absNorm J := by
      apply Nat.pos_of_ne_zero
      rw [Ne, Ideal.absNorm_eq_zero_iff]
      exact hJ0
    have hch : (if h : J ∣ I * J then Exists.choose h else 0) = I := by
      rw [dif_pos (dvd_mul_left J I)]
      apply mul_left_cancel₀ hJ0
      rw [← Exists.choose_spec (dvd_mul_left J I), mul_comm]
    dsimp only
    rw [hch, map_mul, Nat.mul_div_cancel _ hNJ, hI, hJ]
  · rintro ⟨C, J⟩ hy
    simp only [Finset.mem_sigma, mem_normEq] at hy
    obtain ⟨hCn, hJ⟩ := hy
    have hC0 : C ≠ 0 := by
      rintro rfl
      rw [_root_.map_zero] at hCn
      exact hn hCn.symm
    obtain ⟨c, rfl⟩ := (mem_dv hC0).1 hJ
    have hJ0 : J ≠ 0 := by
      rintro rfl
      exact hC0 (zero_mul c)
    have hch : (if h : J ∣ J * c then Exists.choose h else 0) = c := by
      rw [dif_pos (dvd_mul_right J c)]
      exact mul_left_cancel₀ hJ0 (Exists.choose_spec (dvd_mul_right J c)).symm
    dsimp only
    rw [hch, mul_comm]
  · rintro ⟨p, I, J⟩ _
    rfl

variable {M : ℕ} (D : RayData K M)

def chi (ε : D.G → ℝ) (I : Ideal (𝓞 K)) : ℝ :=
  if I ≠ ⊥ ∧ IsCoprime I (Ideal.span {(M : 𝓞 K)}) then ε (D.cls I) else 0

/- English proof (translation)
Establish `hcard : ∀ g, aRay D g n = (((normEq K n).filter (fun I => (I ≠ ⊥ ∧ IsCoprime I (Ideal.span {(M : 𝓞 K)})) ∧ D.cls I = g)).card : ℝ)`. Introduce `g`. Unfold `aRay`. Use `congr 1`. Rewrite using `[← Set.ncard_coe_finset]`.

Use `congr 1`. Use extensionality with `I`. Simplify using `only [idealsIn, Finset.coe_filter, Set.mem_setOf_eq, mem_normEq]`. The claim follows by propositional logic. Establish `hchi : ∀ I, chi D ε I = ∑ g, if (I ≠ ⊥ ∧ IsCoprime I (Ideal.span {(M : 𝓞 K)})) ∧ D.cls I = g then ε g else 0`.

Introduce `I`. Distinguish the cases in `h : I ≠ ⊥ ∧ IsCoprime I (Ideal.span {(M : 𝓞 K)})`. Rewrite using `[chi, if_pos h]`. Simplify using `only [ite_and, if_pos h]`. Simplify using the standard rewrite rules.

Rewrite using `[chi, if_neg h]`. Simplify using `only [ite_and, if_neg h, Finset.sum_const_zero]`. Rewrite using `[Finset.sum_congr rfl (fun I _ => hchi I), Finset.sum_comm]`. Use `Finset.sum_congr rfl fun g _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hcard g, mul_comm]`.
-/
lemma sum_aRay (ε : D.G → ℝ) (n : ℕ) : ∑ g, ε g * aRay D g n = ∑ I ∈ normEq K n, chi D ε I := by
  have hcard : ∀ g, aRay D g n = (((normEq K n).filter (fun I =>
      (I ≠ ⊥ ∧ IsCoprime I (Ideal.span {(M : 𝓞 K)})) ∧ D.cls I = g)).card : ℝ) := by
    intro g
    unfold aRay
    congr 1
    rw [← Set.ncard_coe_finset]
    congr 1
    ext I
    simp only [idealsIn, Finset.coe_filter, Set.mem_setOf_eq, mem_normEq]
    tauto
  have hchi : ∀ I, chi D ε I = ∑ g, if (I ≠ ⊥ ∧ IsCoprime I (Ideal.span {(M : 𝓞 K)})) ∧ D.cls I = g
      then ε g else 0 := by
    intro I
    by_cases h : I ≠ ⊥ ∧ IsCoprime I (Ideal.span {(M : 𝓞 K)})
    · rw [chi, if_pos h]
      simp only [ite_and, if_pos h]
      simp
    · rw [chi, if_neg h]
      simp only [ite_and, if_neg h, Finset.sum_const_zero]
  rw [Finset.sum_congr rfl (fun I _ => hchi I), Finset.sum_comm]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hcard g, mul_comm]

/- English proof (translation)
Distinguish the cases in `hI : I ≠ ⊥ ∧ IsCoprime I (Ideal.span {(M : 𝓞 K)})`. Distinguish the cases in `hJ : J ≠ ⊥ ∧ IsCoprime J (Ideal.span {(M : 𝓞 K)})`. Establish `hIJ : I * J ≠ ⊥ ∧ IsCoprime (I * J) (Ideal.span {(M : 𝓞 K)})` using `⟨mul_ne_zero hI.1 hJ.1, hI.2.mul_left hJ.2⟩`. Simplify using `only [chi]`. Rewrite using `[if_pos hIJ, if_pos hI, if_pos hJ, D.cls_mul I J hI.2 hJ.2 hI.1 hJ.1, hε]`.

Establish `hIJ : ¬ (I * J ≠ ⊥ ∧ IsCoprime (I * J) (Ideal.span {(M : 𝓞 K)}))`. Introduce and unpack `⟨h1, h2⟩`. Conclude with `hJ ⟨fun h => h1 (by rw [h, Ideal.mul_bot]), h2.of_mul_left_right⟩`. Simplify using `only [chi]`. Rewrite using `[if_pos hI, if_neg hJ, if_neg hIJ, mul_zero]`.

Establish `hIJ : ¬ (I * J ≠ ⊥ ∧ IsCoprime (I * J) (Ideal.span {(M : 𝓞 K)}))`. Introduce and unpack `⟨h1, h2⟩`. Conclude with `hI ⟨fun h => h1 (by rw [h, Ideal.bot_mul]), h2.of_mul_left_left⟩`. Simplify using `only [chi]`. Rewrite using `[if_neg hI, if_neg hIJ, zero_mul]`.
-/
lemma chi_mul (ε : D.G → ℝ) (hε : ∀ g h, ε (g * h) = ε g * ε h) (I J : Ideal (𝓞 K)) :
    chi D ε (I * J) = chi D ε I * chi D ε J := by
  by_cases hI : I ≠ ⊥ ∧ IsCoprime I (Ideal.span {(M : 𝓞 K)})
  · by_cases hJ : J ≠ ⊥ ∧ IsCoprime J (Ideal.span {(M : 𝓞 K)})
    · have hIJ : I * J ≠ ⊥ ∧ IsCoprime (I * J) (Ideal.span {(M : 𝓞 K)}) :=
        ⟨mul_ne_zero hI.1 hJ.1, hI.2.mul_left hJ.2⟩
      simp only [chi]
      rw [if_pos hIJ, if_pos hI, if_pos hJ, D.cls_mul I J hI.2 hJ.2 hI.1 hJ.1, hε]
    · have hIJ : ¬ (I * J ≠ ⊥ ∧ IsCoprime (I * J) (Ideal.span {(M : 𝓞 K)})) := by
        rintro ⟨h1, h2⟩
        exact hJ ⟨fun h => h1 (by rw [h, Ideal.mul_bot]), h2.of_mul_left_right⟩
      simp only [chi]
      rw [if_pos hI, if_neg hJ, if_neg hIJ, mul_zero]
  · have hIJ : ¬ (I * J ≠ ⊥ ∧ IsCoprime (I * J) (Ideal.span {(M : 𝓞 K)})) := by
      rintro ⟨h1, h2⟩
      exact hI ⟨fun h => h1 (by rw [h, Ideal.bot_mul]), h2.of_mul_left_left⟩
    simp only [chi]
    rw [if_neg hI, if_neg hIJ, zero_mul]

/- English proof (translation)
Establish `hc : IsCoprime (1 : Ideal (𝓞 K)) (Ideal.span {(M : 𝓞 K)})` using `isCoprime_one_left`. Establish `hb : (1 : Ideal (𝓞 K)) ≠ ⊥`. Rewrite using `[Ideal.one_eq_top]`. Conclude with `top_ne_bot`. Establish `hcls : D.cls 1 = 1`.

Establish `e` using `D.cls_mul 1 1 hc hc hb hb`. Rewrite `e` using `[one_mul]`. Conclude with `mul_left_cancel (by rw [mul_one]; exact e.symm : D.cls 1 * D.cls 1 = D.cls 1 * 1)`. Rewrite using `[chi, if_pos ⟨hb, hc⟩, hcls, h1]`.
-/
lemma chi_one (ε : D.G → ℝ) (h1 : ε 1 = 1) : chi D ε 1 = 1 := by
  have hc : IsCoprime (1 : Ideal (𝓞 K)) (Ideal.span {(M : 𝓞 K)}) := isCoprime_one_left
  have hb : (1 : Ideal (𝓞 K)) ≠ ⊥ := by
    rw [Ideal.one_eq_top]
    exact top_ne_bot
  have hcls : D.cls 1 = 1 := by
    have e := D.cls_mul 1 1 hc hc hb hb
    rw [one_mul] at e
    exact mul_left_cancel (by rw [mul_one]; exact e.symm : D.cls 1 * D.cls 1 = D.cls 1 * 1)
  rw [chi, if_pos ⟨hb, hc⟩, hcls, h1]

/- English proof (translation)
Establish `h1 : ∀ m, ∑ g, aRay D g m = ∑ I ∈ normEq K m, chi D (fun _ => 1) I`. Introduce `m`. Rewrite using `[← sum_aRay D (fun _ => 1) m]`. Simplify using the standard rewrite rules. Establish `hkey : ∀ I J : Ideal (𝓞 K), chi D (fun _ => 1) I * chi D ε J = chi D (fun _ => 1) (I * J) * chi D ε J`.

Introduce `I J`. Rewrite using `[chi_mul D (fun _ => 1) (fun _ _ => (mul_one 1).symm) I J, mul_assoc]`. Use `congr 1`. Simplify using `only [chi]`. Apply the tactic sequence `split_ifs <;> simp`.

Combine the equalities or inequalities in the displayed calculation. Repeatedly rewrite using `[h1, sum_aRay D ε, Finset.sum_mul, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun I _ => Finset.sum_congr rfl fun J _ => hkey I J`. Use `_ = _ := (conv_eq (fun C J => chi D (fun _ => 1) C * chi D ε J) hn).trans (by simp only [r, Finset.mul_sum])`.
-/
lemma conv_aRay (ε : D.G → ℝ) {n : ℕ} (hn : n ≠ 0) :
    ∑ p ∈ n.divisorsAntidiagonal, (∑ g, aRay D g p.1) * ∑ g, ε g * aRay D g p.2 =
      ∑ C ∈ normEq K n, chi D (fun _ => 1) C * r (chi D ε) C := by
  have h1 : ∀ m, ∑ g, aRay D g m = ∑ I ∈ normEq K m, chi D (fun _ => 1) I := by
    intro m
    rw [← sum_aRay D (fun _ => 1) m]
    simp
  have hkey : ∀ I J : Ideal (𝓞 K),
      chi D (fun _ => 1) I * chi D ε J = chi D (fun _ => 1) (I * J) * chi D ε J := by
    intro I J
    rw [chi_mul D (fun _ => 1) (fun _ _ => (mul_one 1).symm) I J, mul_assoc]
    congr 1
    simp only [chi]
    split_ifs <;> simp
  calc _ = ∑ p ∈ n.divisorsAntidiagonal, ∑ I ∈ normEq K p.1, ∑ J ∈ normEq K p.2,
        chi D (fun _ => 1) (I * J) * chi D ε J := by
        simp_rw [h1, sum_aRay D ε, Finset.sum_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun I _ =>
          Finset.sum_congr rfl fun J _ => hkey I J
    _ = _ := (conv_eq (fun C J => chi D (fun _ => 1) C * chi D ε J) hn).trans
        (by simp only [r, Finset.mul_sum])

/- English proof (translation)
Introduce `K _ _ M _ D ε h1 hmul hpm n`. Establish `hv : ∀ I, chi D ε I = 0 ∨ chi D ε I = 1 ∨ chi D ε I = -1`. Introduce `I`. Unfold `chi`. Use `split_ifs`.

Apply the tactic sequence `rcases hpm (D.cls I) with h | h <;> simp [h]`. Simplify using the standard rewrite rules. Establish `hr : ∀ C : Ideal (𝓞 K), C ≠ 0 → 0 ≤ r (chi D ε) C ∧ 1 ≤ r (chi D ε) (C ^ 2)` using `fun C hC => r_bounds (chi D ε) (chi_one D ε h1) (chi_mul D ε hmul) hv C hC`. Establish `h01 : ∀ I, chi D (fun _ => 1) I = if I ≠ ⊥ ∧ IsCoprime I (Ideal.span {(M : 𝓞 K)}) then 1 else 0` using `fun I => rfl`. Establish `hterm : ∀ C : Ideal (𝓞 K), 0 ≤ chi D (fun _ => 1) C * r (chi D ε) C`.

Introduce `C`. Rewrite using `[h01]`. Use `split_ifs with h`. Rewrite using `[one_mul]`. Conclude with `(hr C h.1).1`.

Rewrite using `[zero_mul]`. Establish `hsum1 : ∀ m, ∑ g, aRay D g m = ∑ I ∈ normEq K m, chi D (fun _ => 1) I`. Introduce `m`. Rewrite using `[← sum_aRay D (fun _ => 1) m]`. Simplify using the standard rewrite rules.

Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases. Use `⟨by simp, ?_⟩` and prove the remaining obligations. Establish `h0 : ∑ I ∈ normEq K 0, chi D (fun _ => 1) I = 0`. Use `Finset.sum_eq_zero fun I hI => ?_` and prove the remaining obligations. Rewrite `hI` using `[mem_normEq, Ideal.absNorm_eq_zero_iff]`.

Simplify using `[chi, hI]`. Rewrite using `[hsum1, h0]`. Simplify using the standard rewrite rules. Establish `hn0 : n ≠ 0` using `hn.ne'`. Rewrite using `[conv_aRay D ε hn0, conv_aRay D ε (pow_ne_zero 2 hn0), hsum1]`.

Use `⟨Finset.sum_nonneg fun C _ => hterm C, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_le_sum fun I _ => ?_` and prove the remaining obligations. Distinguish the cases in `h : I ≠ ⊥ ∧ IsCoprime I (Ideal.span {(M : 𝓞 K)})`. Establish `h2 : I ^ 2 ≠ ⊥ ∧ IsCoprime (I ^ 2) (Ideal.span {(M : 𝓞 K)})` using `⟨pow_ne_zero 2 h.1, h.2.pow_left⟩`.

Rewrite using `[h01, h01, if_pos h, if_pos h2, one_mul]`. Conclude with `(hr I h.1).2`. Rewrite using `[h01 I, if_neg h]`. Conclude with `hterm (I ^ 2)`. Use `_ = ∑ C ∈ (normEq K n).image (· ^ 2), chi D (fun _ => 1) C * r (chi D ε) C := by`.

Rewrite using `[Finset.sum_image]`. Introduce `a _ b _ hab`. Establish `hab' : a ^ 2 = b ^ 2` using `hab`. Conclude with `dvd_antisymm ((UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd two_ne_zero).1 hab'.dvd) ((UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd two_ne_zero).1 hab'.symm.dvd)`. Use `_ ≤ ∑ C ∈ normEq K (n ^ 2), chi D (fun _ => 1) C * r (chi D ε) C := by`.

Use `Finset.sum_le_sum_of_subset_of_nonneg ?_ fun C _ _ => hterm C` and prove the remaining obligations. Introduce `C hC`. Take `⟨I, hI, rfl⟩` from `Finset.mem_image.1 hC`. Rewrite `hI`, the goal using `[mem_normEq]`. Rewrite using `[map_pow, hI]`.
-/
theorem conv_real_char : ∀ (K : Type) [Field K] [NumberField K] (M : ℕ), 2 ≤ M → ∀ (D : RayData K M) (ε : D.G → ℝ), ε 1 = 1 → (∀ g h, ε (g * h) = ε g * ε h) → (∀ g, ε g = 1 ∨ ε g = -1) → ∀ n : ℕ, 0 ≤ ∑ p ∈ n.divisorsAntidiagonal, (∑ g, aRay D g p.1) * ∑ g, ε g * aRay D g p.2 ∧ ∑ g, aRay D g n ≤ ∑ p ∈ (n ^ 2).divisorsAntidiagonal, (∑ g, aRay D g p.1) * ∑ g, ε g * aRay D g p.2 := by
  intro K _ _ M _ D ε h1 hmul hpm n
  have hv : ∀ I, chi D ε I = 0 ∨ chi D ε I = 1 ∨ chi D ε I = -1 := by
    intro I
    unfold chi
    split_ifs
    · rcases hpm (D.cls I) with h | h <;> simp [h]
    · simp
  have hr : ∀ C : Ideal (𝓞 K), C ≠ 0 → 0 ≤ r (chi D ε) C ∧ 1 ≤ r (chi D ε) (C ^ 2) :=
    fun C hC => r_bounds (chi D ε) (chi_one D ε h1) (chi_mul D ε hmul) hv C hC
  have h01 : ∀ I, chi D (fun _ => 1) I =
      if I ≠ ⊥ ∧ IsCoprime I (Ideal.span {(M : 𝓞 K)}) then 1 else 0 := fun I => rfl
  have hterm : ∀ C : Ideal (𝓞 K), 0 ≤ chi D (fun _ => 1) C * r (chi D ε) C := by
    intro C
    rw [h01]
    split_ifs with h
    · rw [one_mul]
      exact (hr C h.1).1
    · rw [zero_mul]
  have hsum1 : ∀ m, ∑ g, aRay D g m = ∑ I ∈ normEq K m, chi D (fun _ => 1) I := by
    intro m
    rw [← sum_aRay D (fun _ => 1) m]
    simp
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨by simp, ?_⟩
    have h0 : ∑ I ∈ normEq K 0, chi D (fun _ => 1) I = 0 := by
      refine Finset.sum_eq_zero fun I hI => ?_
      rw [mem_normEq, Ideal.absNorm_eq_zero_iff] at hI
      simp [chi, hI]
    rw [hsum1, h0]
    simp
  · have hn0 : n ≠ 0 := hn.ne'
    rw [conv_aRay D ε hn0, conv_aRay D ε (pow_ne_zero 2 hn0), hsum1]
    refine ⟨Finset.sum_nonneg fun C _ => hterm C, ?_⟩
    calc ∑ I ∈ normEq K n, chi D (fun _ => 1) I
        ≤ ∑ I ∈ normEq K n, chi D (fun _ => 1) (I ^ 2) * r (chi D ε) (I ^ 2) := by
          refine Finset.sum_le_sum fun I _ => ?_
          by_cases h : I ≠ ⊥ ∧ IsCoprime I (Ideal.span {(M : 𝓞 K)})
          · have h2 : I ^ 2 ≠ ⊥ ∧ IsCoprime (I ^ 2) (Ideal.span {(M : 𝓞 K)}) :=
              ⟨pow_ne_zero 2 h.1, h.2.pow_left⟩
            rw [h01, h01, if_pos h, if_pos h2, one_mul]
            exact (hr I h.1).2
          · rw [h01 I, if_neg h]
            exact hterm (I ^ 2)
      _ = ∑ C ∈ (normEq K n).image (· ^ 2), chi D (fun _ => 1) C * r (chi D ε) C := by
          rw [Finset.sum_image]
          intro a _ b _ hab
          have hab' : a ^ 2 = b ^ 2 := hab
          exact dvd_antisymm ((UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd two_ne_zero).1 hab'.dvd)
            ((UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd two_ne_zero).1 hab'.symm.dvd)
      _ ≤ ∑ C ∈ normEq K (n ^ 2), chi D (fun _ => 1) C * r (chi D ε) C := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun C _ _ => hterm C
          intro C hC
          obtain ⟨I, hI, rfl⟩ := Finset.mem_image.1 hC
          rw [mem_normEq] at hI ⊢
          rw [map_pow, hI]

end GlobalTheory.Hk.RaySq

end
