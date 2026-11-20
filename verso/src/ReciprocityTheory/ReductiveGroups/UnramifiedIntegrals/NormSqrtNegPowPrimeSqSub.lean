import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ExistsTeichmullerRepModPrime
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.KurNewton

noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open Formalism.L2.Th1.CM

variable (l : ℕ) [Fact l.Prime]

/- English proof (translation)
Establish `e : (l : ℂ_[l]) = algebraMap ℚ_[l] ℂ_[l] (l : ℚ_[l])` using `(map_natCast _ _).symm`. Rewrite using `[e, norm_algebraMap']`. Use `first`. Consider the case `exact Padic.norm_p_lt_one`. Consider the case `(rw [Padic.norm_p]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt))`.
-/
theorem kq_norm_l_lt : ‖(l : ℂ_[l])‖ < 1 := by
  have e : (l : ℂ_[l]) = algebraMap ℚ_[l] ℂ_[l] (l : ℚ_[l]) := (map_natCast _ _).symm
  rw [e, norm_algebraMap']
  first
  | exact Padic.norm_p_lt_one
  | (rw [Padic.norm_p]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt))

/- English proof (translation)
The claim follows from `(IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)`.
-/
theorem kq_add_le (x y : ℂ_[l]) (r : ℝ) (hx : ‖x‖ ≤ r) (hy : ‖y‖ ≤ r) : ‖x + y‖ ≤ r := (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)

/- English proof (translation)
The claim follows from `(IsUltrametricDist.norm_add_le_max x y).trans_lt (max_lt hx hy)`.
-/
theorem kq_add_lt (x y : ℂ_[l]) (r : ℝ) (hx : ‖x‖ < r) (hy : ‖y‖ < r) : ‖x + y‖ < r := (IsUltrametricDist.norm_add_le_max x y).trans_lt (max_lt hx hy)

/- English proof (translation)
Rewrite using `[← map_intCast (algebraMap ℚ_[l] ℂ_[l]), norm_algebraMap']`.
-/
private theorem kq_intnorm_lemma (n : ℤ) : ‖(n : ℂ_[l])‖ = ‖(n : ℚ_[l])‖ := by
  rw [← map_intCast (algebraMap ℚ_[l] ℂ_[l]), norm_algebraMap']

/- English proof (translation)
Rewrite using `[kq_intnorm_lemma]`. Use `first`. Consider the case `exact padicNormE.norm_int_le_one n`. Consider the case `exact Padic.norm_int_le_one n`.
-/
theorem kq_int_le (n : ℤ) : ‖(n : ℂ_[l])‖ ≤ 1 := by
  rw [kq_intnorm_lemma]
  first
  | exact padicNormE.norm_int_le_one n
  | exact Padic.norm_int_le_one n

/- English proof (translation)
Take `⟨m, rfl⟩` from `h`. Use `push_cast`. Rewrite using `[norm_mul]`. Conclude with `mul_le_of_le_one_right (norm_nonneg _) (kq_int_le l m)`.
-/
theorem kq_int_dvd (n : ℤ) (h : (l : ℤ) ∣ n) : ‖(n : ℂ_[l])‖ ≤ ‖(l : ℂ_[l])‖ := by
  obtain ⟨m, rfl⟩ := h
  push_cast
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (kq_int_le l m)

/- English proof (translation)
Use `le_antisymm (kq_int_le l n) ?_` and prove the remaining obligations. Establish `hp : Prime (l : ℤ)` using `Nat.prime_iff_prime_int.mp (Fact.out : l.Prime)`. Establish `hc : IsCoprime (l : ℤ) n` using `by first`. Consider the case `exact (Irreducible.coprime_iff_not_dvd hp.irreducible).mpr h`. Consider the case `exact (Prime.coprime_iff_not_dvd hp).mpr h`.

Take `⟨a, b, hab⟩` from `hc`. Establish `e : (a : ℂ_[l]) * (l : ℂ_[l]) + (b : ℂ_[l]) * (n : ℂ_[l]) = 1` using `by exact_mod_cast hab`. Establish `h1` using `IsUltrametricDist.norm_add_le_max ((a : ℂ_[l]) * (l : ℂ_[l])) ((b : ℂ_[l]) * (n : ℂ_[l]))`. Rewrite `h1` using `[e, norm_one, norm_mul, norm_mul]`. Break down `le_max_iff.mp h1 with h2 | h2` into its components or cases.

Conclude with `absurd (h2.trans (mul_le_of_le_one_left (norm_nonneg _) (kq_int_le l a))) (not_le.mpr (kq_norm_l_lt l))`. Conclude with `h2.trans (mul_le_of_le_one_left (norm_nonneg _) (kq_int_le l b))`.
-/
theorem kq_int_unit (n : ℤ) (h : ¬ (l : ℤ) ∣ n) : ‖(n : ℂ_[l])‖ = 1 := by
  refine le_antisymm (kq_int_le l n) ?_
  have hp : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp (Fact.out : l.Prime)
  have hc : IsCoprime (l : ℤ) n := by
    first
    | exact (Irreducible.coprime_iff_not_dvd hp.irreducible).mpr h
    | exact (Prime.coprime_iff_not_dvd hp).mpr h
  obtain ⟨a, b, hab⟩ := hc
  have e : (a : ℂ_[l]) * (l : ℂ_[l]) + (b : ℂ_[l]) * (n : ℂ_[l]) = 1 := by exact_mod_cast hab
  have h1 := IsUltrametricDist.norm_add_le_max ((a : ℂ_[l]) * (l : ℂ_[l])) ((b : ℂ_[l]) * (n : ℂ_[l]))
  rw [e, norm_one, norm_mul, norm_mul] at h1
  rcases le_max_iff.mp h1 with h2 | h2
  · exact absurd (h2.trans (mul_le_of_le_one_left (norm_nonneg _) (kq_int_le l a)))
      (not_le.mpr (kq_norm_l_lt l))
  · exact h2.trans (mul_le_of_le_one_left (norm_nonneg _) (kq_int_le l b))

/- English proof (translation)
The claim follows from `kq_int_dvd l n ((ZMod.intCast_zmod_eq_zero_iff_dvd n l).mp h)`.
-/
theorem kq_zmod (n : ℤ) (h : (n : ZMod l) = 0) : ‖(n : ℂ_[l])‖ ≤ ‖(l : ℂ_[l])‖ := kq_int_dvd l n ((ZMod.intCast_zmod_eq_zero_iff_dvd n l).mp h)

/- English proof (translation)
Establish `hd0 : (-(d : ZMod l)) ≠ 0`. Rewrite using `[neg_ne_zero]`. Introduce `h0`. Apply `hld` to reduce the goal to its premises. Conclude with `(CharP.cast_eq_zero_iff (ZMod l) l d).mp h0`.

Break down `ZMod.pow_div_two_eq_neg_one_or_one l hd0 with h | h` into its components or cases. Apply the tactic sequence `all_goals first`. Consider the case `exact h`. Consider the case `(exfalso`. Take `⟨a, ha⟩` from `(ZMod.euler_criterion l hd0).mpr h`.

Conclude with `hin ⟨a, by rw [ha, sq]⟩)`.
-/
theorem kq_euler (d : ℕ) (hld : ¬ l ∣ d)
    (hin : ¬ ∃ a : ZMod l, a ^ 2 = -(d : ZMod l)) : (-(d : ZMod l)) ^ (l / 2) = -1 := by
  have hd0 : (-(d : ZMod l)) ≠ 0 := by
    rw [neg_ne_zero]
    intro h0
    apply hld
    exact (CharP.cast_eq_zero_iff (ZMod l) l d).mp h0
  rcases ZMod.pow_div_two_eq_neg_one_or_one l hd0 with h | h
  all_goals first
    | exact h
    | (exfalso
       obtain ⟨a, ha⟩ := (ZMod.euler_criterion l hd0).mpr h
       exact hin ⟨a, by rw [ha, sq]⟩)

variable {l}

/- English proof (translation)
Rewrite using `[h, pow_succ, pow_mul, hδ, mul_comm]`.
-/
theorem kq_pow_odd (δ c : ℂ_[l]) (hδ : δ ^ 2 = c) (n m : ℕ) (h : n = 2 * m + 1) :
    δ ^ n = δ * c ^ m := by
  rw [h, pow_succ, pow_mul, hδ, mul_comm]

/- English proof (translation)
Establish `hodd : l = 2 * (l / 2) + 1`. Establish `h2` using `(Fact.out : l.Prime).mod_two_eq_one_iff_ne_two.mpr hl`. Establish `h3` using `Nat.div_add_mod l 2`. Use linear arithmetic over natural numbers and integers. Rewrite using `[kq_pow_odd δ _ hδ l (l / 2) hodd]`.

Establish `e : δ * (-(d : ℂ_[l])) ^ (l / 2) + δ = δ * ((((-(d : ℤ)) ^ (l / 2) + 1 : ℤ)) : ℂ_[l])`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, norm_mul, hn, one_mul]`. Apply `kq_zmod` to reduce the goal to its premises.

Use `push_cast`. Rewrite using `[kq_euler l d hld hin]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem kq_pow_l (d : ℕ) (hl : l ≠ 2) (hld : ¬ l ∣ d)
    (hin : ¬ ∃ a : ZMod l, a ^ 2 = -(d : ZMod l)) (δ : ℂ_[l]) (hδ : δ ^ 2 = -(d : ℂ_[l]))
    (hn : ‖δ‖ = 1) : ‖δ ^ l + δ‖ ≤ ‖(l : ℂ_[l])‖ := by
  have hodd : l = 2 * (l / 2) + 1 := by
    have h2 := (Fact.out : l.Prime).mod_two_eq_one_iff_ne_two.mpr hl
    have h3 := Nat.div_add_mod l 2
    omega
  rw [kq_pow_odd δ _ hδ l (l / 2) hodd]
  have e : δ * (-(d : ℂ_[l])) ^ (l / 2) + δ = δ * ((((-(d : ℤ)) ^ (l / 2) + 1 : ℤ)) : ℂ_[l]) := by
    push_cast
    ring
  rw [e, norm_mul, hn, one_mul]
  apply kq_zmod
  push_cast
  rw [kq_euler l d hld hin]
  ring

/- English proof (translation)
Establish `hodd : l = 2 * (l / 2) + 1`. Use `(Fact.out : l.Prime).eq_two_or_odd` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `e0 : δ ^ l = δ * (((-(d : ℤ)) ^ (l / 2) : ℤ) : ℂ_[l])`. Rewrite using `[kq_pow_odd δ _ hδ l (l / 2) hodd]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `e : δ ^ (l ^ 2) - δ = δ * ((((-(d : ℤ)) ^ (l / 2)) ^ (l + 1) - 1 : ℤ) : ℂ_[l])`. Rewrite using `[sq, pow_mul, e0, mul_pow, e0]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, norm_mul, hn, one_mul]`. Apply `kq_zmod` to reduce the goal to its premises. Use `push_cast`. Rewrite using `[kq_euler l d hld hin]`.

Establish `: l + 1 = 2 * (l / 2 + 1)` using `by omega`. Rewrite using `[this, pow_mul]`. Simplify using the standard rewrite rules.
-/
theorem norm_sqrtNeg_pow_prime_sq_sub (d : ℕ) (hl : l ≠ 2) (hld : ¬ l ∣ d)
    (hin : ¬ ∃ a : ZMod l, a ^ 2 = -(d : ZMod l)) (δ : ℂ_[l]) (hδ : δ ^ 2 = -(d : ℂ_[l]))
    (hn : ‖δ‖ = 1) : ‖δ ^ (l ^ 2) - δ‖ ≤ ‖(l : ℂ_[l])‖ := by
  have hodd : l = 2 * (l / 2) + 1 := by
    have := (Fact.out : l.Prime).eq_two_or_odd
    omega
  have e0 : δ ^ l = δ * (((-(d : ℤ)) ^ (l / 2) : ℤ) : ℂ_[l]) := by
    rw [kq_pow_odd δ _ hδ l (l / 2) hodd]
    push_cast
    ring
  have e : δ ^ (l ^ 2) - δ = δ * ((((-(d : ℤ)) ^ (l / 2)) ^ (l + 1) - 1 : ℤ) : ℂ_[l]) := by
    rw [sq, pow_mul, e0, mul_pow, e0]
    push_cast
    ring
  rw [e, norm_mul, hn, one_mul]
  apply kq_zmod
  push_cast
  rw [kq_euler l d hld hin]
  have : l + 1 = 2 * (l / 2 + 1) := by omega
  rw [this, pow_mul]
  simp

/- English proof (translation)
Take `⟨ξ, hξ, hξδ⟩` from `tch_near l δ hn.le 2 (by norm_num) ‖(l : ℂ_[l])‖ (kq_norm_l_lt l) (norm_sqrtNeg_pow_prime_sq_sub d hl hld hin δ hδ hn)`. Establish `hlt : ‖δ - ξ‖ < 1` using `hξδ.trans_lt (kq_norm_l_lt l)`. Establish `hξ1 : ‖ξ‖ = 1`. Use `le_antisymm (tch_norm_le l hξ) (not_lt.mp fun h => ?_)` and prove the remaining obligations. Establish `: ‖(δ - ξ) + ξ‖ < 1` using `kq_add_lt l _ _ 1 hlt h`.

Rewrite `this` using `[sub_add_cancel, hn]`. Conclude with `lt_irrefl _ this`. Establish `h2 : ‖(2 : ℂ_[l])‖ = 1`. Use `kq_int_unit l 2 (by` as an intermediate fact. Introduce `h`.

Establish `h' : l ∣ 2` using `by exact_mod_cast h`. Conclude with `hl ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h'))`. Simplify using `using this`. Establish `: CompleteSpace (MaximalUnramifiedExtension l)` using `kur_complete l`. Set `x₀ : MaximalUnramifiedExtension l` to `⟨ξ, tch_mem_kur l hξ⟩`.

Set `P : Polynomial (MaximalUnramifiedExtension l)` to `Polynomial.X ^ 2 + Polynomial.C (d : MaximalUnramifiedExtension l)`. Establish `hev : ((P.eval x₀ : MaximalUnramifiedExtension l) : ℂ_[l]) = (ξ - δ) * (ξ + δ)`. Establish `: (ξ - δ) * (ξ + δ) = ξ ^ 2 - δ ^ 2` using `by ring`. Rewrite using `[this, hδ]`. Simplify using `[P, x₀]`.

Establish `hdv : ((P.derivative.eval x₀ : MaximalUnramifiedExtension l) : ℂ_[l]) = 2 * ξ`. Simplify using `[P, x₀]`. Use `left`. Evaluate the numerical expressions. Establish `hd1 : ‖(d : ℂ_[l])‖ ≤ 1` using `by simpa using kq_int_le l (d : ℤ)`.

Take `⟨x, hx, -⟩` from `newton_root P (by`. Introduce `i`. Express the relevant statement in the definitionally equal form `‖((P.coeff i : MaximalUnramifiedExtension l) : ℂ_[l])‖ ≤ 1`. Simplify using `only [P, Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_C]`. Distinguish the cases in `h2i : i = 2`.

Substitute `h2i` using the available equality. Simplify using the standard rewrite rules. Distinguish the cases in `h0 : i = 0`. Substitute `h0` using the available equality. Simplify using `using hd1`.

Simplify using `[h2i, h0])`. Use `x₀ hξ1.le`. Use the proof step `(by`. Express the relevant statement in the definitionally equal form `‖((P.eval x₀ : MaximalUnramifiedExtension l) : ℂ_[l])‖ < 1`. Rewrite using `[hev, norm_mul, norm_sub_rev]`.

Establish `: ‖ξ + δ‖ ≤ 1` using `kq_add_le l _ _ 1 hξ1.le hn.le`. Conclude with `(mul_le_of_le_one_right (norm_nonneg _) this).trans_lt hlt)`. Use the proof step `(by`. Express the relevant statement in the definitionally equal form `‖((P.derivative.eval x₀ : MaximalUnramifiedExtension l) : ℂ_[l])‖ = 1`. Rewrite using `[hdv, norm_mul, h2, hξ1, one_mul])`.

Establish `hx' : (x : ℂ_[l]) ^ 2 = δ ^ 2`. Establish `: ((P.eval x : MaximalUnramifiedExtension l) : ℂ_[l]) = 0` using `by rw [hx]; rfl`. Simplify using `only [P, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at this`. Move the coercions through the operations in `at this`. Rewrite using `[hδ]`.

Take the linear combination `this`. Break down `sq_eq_sq_iff_eq_or_eq_neg.mp hx' with h | h` into its components or cases. Rewrite using `[← h]`. Conclude with `x.2`. Establish `: δ = -(x : ℂ_[l])` using `by rw [h, neg_neg]`.

Rewrite using `[this]`. Conclude with `neg_mem x.2`.
-/
theorem kq_mem (d : ℕ) (hl : l ≠ 2) (hld : ¬ l ∣ d)
    (hin : ¬ ∃ a : ZMod l, a ^ 2 = -(d : ZMod l)) (δ : ℂ_[l]) (hδ : δ ^ 2 = -(d : ℂ_[l]))
    (hn : ‖δ‖ = 1) : δ ∈ MaximalUnramifiedExtension l := by
  obtain ⟨ξ, hξ, hξδ⟩ := tch_near l δ hn.le 2 (by norm_num) ‖(l : ℂ_[l])‖ (kq_norm_l_lt l)
    (norm_sqrtNeg_pow_prime_sq_sub d hl hld hin δ hδ hn)
  have hlt : ‖δ - ξ‖ < 1 := hξδ.trans_lt (kq_norm_l_lt l)
  have hξ1 : ‖ξ‖ = 1 := by
    refine le_antisymm (tch_norm_le l hξ) (not_lt.mp fun h => ?_)
    have : ‖(δ - ξ) + ξ‖ < 1 := kq_add_lt l _ _ 1 hlt h
    rw [sub_add_cancel, hn] at this
    exact lt_irrefl _ this
  have h2 : ‖(2 : ℂ_[l])‖ = 1 := by
    have := kq_int_unit l 2 (by
      intro h
      have h' : l ∣ 2 := by exact_mod_cast h
      exact hl ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h'))
    simpa using this
  have : CompleteSpace (MaximalUnramifiedExtension l) := kur_complete l
  let x₀ : MaximalUnramifiedExtension l := ⟨ξ, tch_mem_kur l hξ⟩
  let P : Polynomial (MaximalUnramifiedExtension l) := Polynomial.X ^ 2 + Polynomial.C (d : MaximalUnramifiedExtension l)
  have hev : ((P.eval x₀ : MaximalUnramifiedExtension l) : ℂ_[l]) = (ξ - δ) * (ξ + δ) := by
    have : (ξ - δ) * (ξ + δ) = ξ ^ 2 - δ ^ 2 := by ring
    rw [this, hδ]
    simp [P, x₀]
  have hdv : ((P.derivative.eval x₀ : MaximalUnramifiedExtension l) : ℂ_[l]) = 2 * ξ := by
    simp [P, x₀]
    left; norm_num
  have hd1 : ‖(d : ℂ_[l])‖ ≤ 1 := by simpa using kq_int_le l (d : ℤ)
  obtain ⟨x, hx, -⟩ := newton_root P
    (by
      intro i
      change ‖((P.coeff i : MaximalUnramifiedExtension l) : ℂ_[l])‖ ≤ 1
      simp only [P, Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_C]
      by_cases h2i : i = 2
      · subst h2i; simp
      · by_cases h0 : i = 0
        · subst h0; simpa using hd1
        · simp [h2i, h0])
    x₀ hξ1.le
    (by
      change ‖((P.eval x₀ : MaximalUnramifiedExtension l) : ℂ_[l])‖ < 1
      rw [hev, norm_mul, norm_sub_rev]
      have : ‖ξ + δ‖ ≤ 1 := kq_add_le l _ _ 1 hξ1.le hn.le
      exact (mul_le_of_le_one_right (norm_nonneg _) this).trans_lt hlt)
    (by
      change ‖((P.derivative.eval x₀ : MaximalUnramifiedExtension l) : ℂ_[l])‖ = 1
      rw [hdv, norm_mul, h2, hξ1, one_mul])
  have hx' : (x : ℂ_[l]) ^ 2 = δ ^ 2 := by
    have : ((P.eval x : MaximalUnramifiedExtension l) : ℂ_[l]) = 0 := by rw [hx]; rfl
    simp only [P, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C] at this
    push_cast at this
    rw [hδ]
    linear_combination this
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hx' with h | h
  · rw [← h]; exact x.2
  · have : δ = -(x : ℂ_[l]) := by rw [h, neg_neg]
    rw [this]; exact neg_mem x.2

variable (l)

/- English proof (translation)
Establish `h4 : (((d + 1) / 4 : ℕ) : ℂ_[l]) * 4 = (d : ℂ_[l]) + 1`. Establish `h44 : (d + 1) / 4 * 4 = d + 1` using `by omega`. Conclude with `h44` after adjusting the coercions. Take `⟨δ, hδdef⟩ : ∃ δ : ℂ_[l], δ = 1 - 2 * a` from `⟨_, rfl⟩`. Establish `hδ : δ ^ 2 = -(d : ℂ_[l])`.

Rewrite using `[hδdef]`. Take the linear combination `4 * ha - h4`. Establish `hd1 : ‖(d : ℂ_[l])‖ = 1`. Establish `hu` using `kq_int_unit l (d : ℤ) (by exact_mod_cast hld)`. Conclude with `hu` after adjusting the coercions.

Establish `hn : ‖δ‖ = 1`. Establish `hh` using `congrArg norm hδ`. Rewrite `hh` using `[norm_pow, norm_neg, hd1]`. Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp hh`. Establish `h2 : ‖(2 : ℂ_[l])‖ = 1`.

Establish `hu` using `kq_int_unit l 2 (by`. Introduce `h2d`. Establish `h2n : l ∣ 2` using `by exact_mod_cast h2d`. Conclude with `hl ((Nat.prime_dvd_prime_iff_eq (Fact.out : l.Prime) Nat.prime_two).mp h2n))`. Conclude with `hu` after adjusting the coercions.

Establish `ha2 : a * 2 = 1 - δ`. Rewrite using `[hδdef]`. Expand and normalize the polynomial expressions, which then agree. Establish `hna : ‖a‖ ≤ 1`. Establish `hh : ‖a‖ = ‖1 - δ‖` using `by rw [← ha2, norm_mul, h2, mul_one]`.

Rewrite using `[hh, sub_eq_add_neg]`. Conclude with `kq_add_le l _ _ 1 (by simp) (by rw [norm_neg, hn])`. Establish `hδK : δ ∈ MaximalUnramifiedExtension l` using `kq_mem d hl hld hin δ hδ hn`. Establish `h2K : (2 : ℂ_[l]) ∈ MaximalUnramifiedExtension l` using `by simpa using natCast_mem (MaximalUnramifiedExtension l) 2`. Establish `h20 : (2 : ℂ_[l]) ≠ 0` using `two_ne_zero`.

Establish `haK : a ∈ MaximalUnramifiedExtension l`. Establish `hh : a = (1 - δ) / 2` using `by rw [eq_div_iff h20, ha2]`. Rewrite using `[hh]`. Conclude with `div_mem (sub_mem (one_mem _) hδK) h2K`. Use `⟨hna, by rw [← hδdef]; exact hn, haK, fun σ hσ => ?_⟩` and prove the remaining obligations.

Take `⟨-, -, -, f4⟩` from `hσ`. Establish `hh : a = (1 - δ) / 2` using `by rw [eq_div_iff h20, ha2]`. Take `⟨D, hD⟩ : ∃ D : MaximalUnramifiedExtension l, (D : ℂ_[l]) = δ` from `⟨⟨δ, hδK⟩, rfl⟩`. Establish `hD2 : D ^ 2 = -((d : ℕ) : MaximalUnramifiedExtension l)` using `Subtype.ext (by simp [hD, hδ])`. Establish `hDn : ‖D‖ = 1`.

Rewrite using `[← hn, ← hD]`. Both sides reduce to the same expression. Establish `hσD : σ D ^ 2 = D ^ 2` using `by rw [← map_pow, hD2, map_neg, map_natCast]`. Establish `hneg : σ D = -D`. Break down `sq_eq_sq_iff_eq_or_eq_neg.mp hσD with h | h` into its components or cases.

It suffices to derive a contradiction. Establish `hf' : ‖δ - δ ^ l‖ ≤ ‖(l : ℂ_[l])‖`. Establish `h5` using `f4 D (le_of_eq hDn)`. Rewrite `h5` using `[h]`. Rewrite using `[← hD]`.

Conclude with `h5`. Establish `hsum : (2 : ℂ_[l]) * δ = (δ - δ ^ l) + (δ ^ l + δ)` using `by ring`. Establish `h2d : ‖(2 : ℂ_[l]) * δ‖ = 1` using `by rw [norm_mul, h2, hn, one_mul]`. Establish `hlt` using `kq_add_lt l _ _ 1 (hf'.trans_lt (kq_norm_l_lt l)) ((kq_pow_l d hl hld hin δ hδ hn).trans_lt (kq_norm_l_lt l))`. Rewrite `hlt` using `[← hsum, h2d]`.

Conclude with `lt_irrefl 1 hlt`. Conclude with `h`. Establish `e2 : ((2 : MaximalUnramifiedExtension l) : ℂ_[l]) = 2` using `by first`. Consider the case `rfl`. Consider the case `norm_cast`.

Consider the case `simp`. Establish `hA2 : (⟨a, haK⟩ : MaximalUnramifiedExtension l) * 2 = 1 - D`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show a * ((2 : MaximalUnramifiedExtension l) : ℂ_[l]) = ((1 - D : MaximalUnramifiedExtension l) : ℂ_[l])`. Rewrite using `[e2, ha2, ← hD]`.

Both sides reduce to the same expression. Establish `h2ne : (2 : MaximalUnramifiedExtension l) ≠ 0` using `fun h0 => h20 (by rw [← e2, h0]; rfl)`. Establish `hs : σ ⟨a, haK⟩ * 2 = 1 + D`. Establish `h6` using `congrArg σ hA2`. Rewrite `h6` using `[map_mul, map_ofNat, map_sub, map_one, hneg]`.

Rewrite using `[h6]`. Expand and normalize the polynomial expressions, which then agree. Apply `mul_right_cancel₀ h2ne` to reduce the goal to its premises. Rewrite using `[hs, sub_mul, hA2]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem kur_quad (d : ℕ) (hd : d % 4 = 3) (hl : l ≠ 2) (hld : ¬ l ∣ d)
    (hin : ¬ ∃ a : ZMod l, a ^ 2 = -(d : ZMod l)) (a : ℂ_[l])
    (ha : a ^ 2 - a + (((d + 1) / 4 : ℕ) : ℂ_[l]) = 0) :
    ‖a‖ ≤ 1 ∧ ‖1 - 2 * a‖ = 1 ∧ ∃ ha' : a ∈ MaximalUnramifiedExtension l, ∀ σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l, FrobField (MaximalUnramifiedExtension l) l σ →
      σ ⟨a, ha'⟩ = 1 - ⟨a, ha'⟩ := by
  have h4 : (((d + 1) / 4 : ℕ) : ℂ_[l]) * 4 = (d : ℂ_[l]) + 1 := by
    have h44 : (d + 1) / 4 * 4 = d + 1 := by omega
    exact_mod_cast h44
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℂ_[l], δ = 1 - 2 * a := ⟨_, rfl⟩
  have hδ : δ ^ 2 = -(d : ℂ_[l]) := by
    rw [hδdef]
    linear_combination 4 * ha - h4
  have hd1 : ‖(d : ℂ_[l])‖ = 1 := by
    have hu := kq_int_unit l (d : ℤ) (by exact_mod_cast hld)
    exact_mod_cast hu
  have hn : ‖δ‖ = 1 := by
    have hh := congrArg norm hδ
    rw [norm_pow, norm_neg, hd1] at hh
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp hh
  have h2 : ‖(2 : ℂ_[l])‖ = 1 := by
    have hu := kq_int_unit l 2 (by
      intro h2d
      have h2n : l ∣ 2 := by exact_mod_cast h2d
      exact hl ((Nat.prime_dvd_prime_iff_eq (Fact.out : l.Prime) Nat.prime_two).mp h2n))
    exact_mod_cast hu
  have ha2 : a * 2 = 1 - δ := by
    rw [hδdef]
    ring
  have hna : ‖a‖ ≤ 1 := by
    have hh : ‖a‖ = ‖1 - δ‖ := by rw [← ha2, norm_mul, h2, mul_one]
    rw [hh, sub_eq_add_neg]
    exact kq_add_le l _ _ 1 (by simp) (by rw [norm_neg, hn])
  have hδK : δ ∈ MaximalUnramifiedExtension l := kq_mem d hl hld hin δ hδ hn
  have h2K : (2 : ℂ_[l]) ∈ MaximalUnramifiedExtension l := by simpa using natCast_mem (MaximalUnramifiedExtension l) 2
  have h20 : (2 : ℂ_[l]) ≠ 0 := two_ne_zero
  have haK : a ∈ MaximalUnramifiedExtension l := by
    have hh : a = (1 - δ) / 2 := by rw [eq_div_iff h20, ha2]
    rw [hh]
    exact div_mem (sub_mem (one_mem _) hδK) h2K
  refine ⟨hna, by rw [← hδdef]; exact hn, haK, fun σ hσ => ?_⟩
  obtain ⟨-, -, -, f4⟩ := hσ
  have hh : a = (1 - δ) / 2 := by rw [eq_div_iff h20, ha2]
  obtain ⟨D, hD⟩ : ∃ D : MaximalUnramifiedExtension l, (D : ℂ_[l]) = δ := ⟨⟨δ, hδK⟩, rfl⟩
  have hD2 : D ^ 2 = -((d : ℕ) : MaximalUnramifiedExtension l) := Subtype.ext (by simp [hD, hδ])
  have hDn : ‖D‖ = 1 := by
    rw [← hn, ← hD]
    rfl
  have hσD : σ D ^ 2 = D ^ 2 := by rw [← map_pow, hD2, map_neg, map_natCast]
  have hneg : σ D = -D := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hσD with h | h
    · exfalso
      have hf' : ‖δ - δ ^ l‖ ≤ ‖(l : ℂ_[l])‖ := by
        have h5 := f4 D (le_of_eq hDn)
        rw [h] at h5
        rw [← hD]
        exact h5
      have hsum : (2 : ℂ_[l]) * δ = (δ - δ ^ l) + (δ ^ l + δ) := by ring
      have h2d : ‖(2 : ℂ_[l]) * δ‖ = 1 := by rw [norm_mul, h2, hn, one_mul]
      have hlt := kq_add_lt l _ _ 1 (hf'.trans_lt (kq_norm_l_lt l))
        ((kq_pow_l d hl hld hin δ hδ hn).trans_lt (kq_norm_l_lt l))
      rw [← hsum, h2d] at hlt
      exact lt_irrefl 1 hlt
    · exact h
  have e2 : ((2 : MaximalUnramifiedExtension l) : ℂ_[l]) = 2 := by
    first
    | rfl
    | norm_cast
    | simp
  have hA2 : (⟨a, haK⟩ : MaximalUnramifiedExtension l) * 2 = 1 - D := by
    apply Subtype.ext
    show a * ((2 : MaximalUnramifiedExtension l) : ℂ_[l]) = ((1 - D : MaximalUnramifiedExtension l) : ℂ_[l])
    rw [e2, ha2, ← hD]
    rfl
  have h2ne : (2 : MaximalUnramifiedExtension l) ≠ 0 := fun h0 => h20 (by rw [← e2, h0]; rfl)
  have hs : σ ⟨a, haK⟩ * 2 = 1 + D := by
    have h6 := congrArg σ hA2
    rw [map_mul, map_ofNat, map_sub, map_one, hneg] at h6
    rw [h6]
    ring
  apply mul_right_cancel₀ h2ne
  rw [hs, sub_mul, hA2]
  ring

end ReciprocityTheory.ChartRestriction.L1
