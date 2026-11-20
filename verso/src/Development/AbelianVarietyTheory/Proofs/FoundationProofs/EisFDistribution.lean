import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.Integral

open Finset GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory.EisDist

/- English proof (translation)
Establish `hp0 : (p : ℝ) ≠ 0` using `by exact_mod_cast hp.ne'`. Establish `hcast : ∀ x : ℚ, bernoulliFun j (x : ℝ) = (((Polynomial.bernoulli j).eval x : ℚ) : ℝ)` using `fun x => by`. Rewrite using `[bernoulliFun, Polynomial.eval_map, ← eq_ratCast (algebraMap ℚ ℝ) x, Polynomial.eval₂_at_apply, eq_ratCast]`. Establish `key` using `bernoulliFun_mul j hp.ne' ((y : ℝ) / p)`. Rewrite `key` using `[show (p : ℝ) * ((y : ℝ) / p) = y by field_simp]`.

Establish `h2 : ∑ k ∈ range p, bernoulliFun j (((y + k) / p : ℚ) : ℝ) = (p : ℝ) ^ ((1 : ℤ) - j) * bernoulliFun j (y : ℝ)`. Establish `e : ∀ k : ℕ, (((y + k) / p : ℚ) : ℝ) = (y : ℝ) / p + k / p` using `fun k => by push_cast; ring`. Simplify using `only [e]`. Rewrite using `[key, zpow_sub₀ hp0, zpow_one, zpow_natCast]`. Clear the denominators using the available nonvanishing facts.

Apply `Rat.cast_injective (α := ℝ)` to reduce the goal to its premises. Rewrite using `[Rat.cast_sum, Rat.cast_mul, Rat.cast_zpow, Rat.cast_natCast]`. Simplify using `only [← hcast]`. Conclude with `h2`.
-/
theorem dist_raabe (p : ℕ) (hp : 0 < p) (j : ℕ) (y : ℚ) :
    ∑ k ∈ range p, (Polynomial.bernoulli j).eval ((y + k) / p) =
      (p : ℚ) ^ ((1 : ℤ) - j) * (Polynomial.bernoulli j).eval y := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have hcast : ∀ x : ℚ, bernoulliFun j (x : ℝ) = (((Polynomial.bernoulli j).eval x : ℚ) : ℝ) := fun x => by
    rw [bernoulliFun, Polynomial.eval_map, ← eq_ratCast (algebraMap ℚ ℝ) x, Polynomial.eval₂_at_apply,
      eq_ratCast]
  have key := bernoulliFun_mul j hp.ne' ((y : ℝ) / p)
  rw [show (p : ℝ) * ((y : ℝ) / p) = y by field_simp] at key
  have h2 : ∑ k ∈ range p, bernoulliFun j (((y + k) / p : ℚ) : ℝ) =
      (p : ℝ) ^ ((1 : ℤ) - j) * bernoulliFun j (y : ℝ) := by
    have e : ∀ k : ℕ, (((y + k) / p : ℚ) : ℝ) = (y : ℝ) / p + k / p := fun k => by push_cast; ring
    simp only [e]
    rw [key, zpow_sub₀ hp0, zpow_one, zpow_natCast]
    field_simp
  apply Rat.cast_injective (α := ℝ)
  rw [Rat.cast_sum, Rat.cast_mul, Rat.cast_zpow, Rat.cast_natCast]
  simp only [← hcast]
  exact h2

/- English proof (translation)
Take `⟨n, rfl⟩ : ∃ n, p = n + 1` from `⟨p - 1, by omega⟩`. Establish `step : ∀ q : ℤ, ∑ i ∈ range (n + 1), g ((q + 1 + i) % ((n + 1 : ℕ) : ℤ)) = ∑ i ∈ range (n + 1), g ((q + i) % ((n + 1 : ℕ) : ℤ))`. Introduce `q`. Rewrite using `[Finset.sum_range_succ, Finset.sum_range_succ' (fun i => g ((q + i) % ((n + 1 : ℕ) : ℤ)))]`. Use `congr 1`.

Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `i _`. Use `congr 2`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Use `congr 1`. Rewrite using `[show q + 1 + ((n : ℕ) : ℤ) = q + ((n + 1 : ℕ) : ℤ) * 1 by push_cast; ring, Int.add_mul_emod_self_left]`. Simplify using the standard rewrite rules. Establish `key : ∀ q : ℤ, ∑ i ∈ range (n + 1), g ((q + i) % ((n + 1 : ℕ) : ℤ)) = ∑ i ∈ range (n + 1), g ((0 + i) % ((n + 1 : ℕ) : ℤ))`. Introduce `q`.

Use `Int.induction_on q rfl ?_ ?_` and prove the remaining obligations. Introduce `i ih`. Rewrite using `[step]`. Conclude with `ih`. Introduce `i ih`.

Establish `h` using `step (-(i : ℤ) - 1)`. Rewrite `h` using `[sub_add_cancel]`. Rewrite using `[← h]`. Conclude with `ih`. Rewrite using `[key q]`.

Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `i hi`. Rewrite using `[zero_add, Int.emod_eq_of_lt (by positivity) (by exact_mod_cast Finset.mem_range.mp hi)]`.
-/
theorem dist_shift {α : Type} [AddCommMonoid α] (p : ℕ) (hp : 0 < p) (q : ℤ) (g : ℤ → α) :
    ∑ i ∈ range p, g ((q + i) % p) = ∑ k ∈ range p, g k := by
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, by omega⟩
  have step : ∀ q : ℤ, ∑ i ∈ range (n + 1), g ((q + 1 + i) % ((n + 1 : ℕ) : ℤ)) =
      ∑ i ∈ range (n + 1), g ((q + i) % ((n + 1 : ℕ) : ℤ)) := by
    intro q
    rw [Finset.sum_range_succ, Finset.sum_range_succ' (fun i => g ((q + i) % ((n + 1 : ℕ) : ℤ)))]
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      congr 2
      push_cast
      ring
    · congr 1
      rw [show q + 1 + ((n : ℕ) : ℤ) = q + ((n + 1 : ℕ) : ℤ) * 1 by push_cast; ring,
        Int.add_mul_emod_self_left]
      simp
  have key : ∀ q : ℤ, ∑ i ∈ range (n + 1), g ((q + i) % ((n + 1 : ℕ) : ℤ)) =
      ∑ i ∈ range (n + 1), g ((0 + i) % ((n + 1 : ℕ) : ℤ)) := by
    intro q
    refine Int.induction_on q rfl ?_ ?_
    · intro i ih
      rw [step]
      exact ih
    · intro i ih
      have h := step (-(i : ℤ) - 1)
      rw [sub_add_cancel] at h
      rw [← h]
      exact ih
  rw [key q]
  apply Finset.sum_congr rfl
  intro i hi
  rw [zero_add, Int.emod_eq_of_lt (by positivity) (by exact_mod_cast Finset.mem_range.mp hi)]

/- English proof (translation)
Establish `hM' : (0 : ℤ) < M` using `by exact_mod_cast hM`. Establish `hp' : (0 : ℤ) < p` using `by exact_mod_cast hp`. Take `⟨t, ht⟩ : ∃ t, t = a / M + i` from `⟨_, rfl⟩`. Establish `h1` using `Int.emod_add_mul_ediv a M`. Establish `h2` using `Int.emod_add_mul_ediv t p`.

Establish `e1 : a + M * i = (a % M + M * (t % p)) + ((p * M : ℕ) : ℤ) * (t / p)`. Use `push_cast`. Take the linear combination `(-1 : ℤ) * h1 - (M : ℤ) * h2 - (M : ℤ) * ht`. Rewrite using `[← ht, e1, Int.add_mul_emod_self_left]`. Establish `h3` using `Int.emod_nonneg a hM'.ne'`.

Establish `h4` using `Int.emod_lt_of_pos a hM'`. Establish `h5` using `Int.emod_nonneg t hp'.ne'`. Establish `h6` using `Int.emod_lt_of_pos t hp'`. Apply `Int.emod_eq_of_lt` to reduce the goal to its premises. Use polynomial arithmetic with `[mul_nonneg hM'.le h5]`.

Use `push_cast`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left (show t % p ≤ p - 1 by omega) hM'.le]`.
-/
theorem dist_emod (p M : ℕ) (hp : 0 < p) (hM : 0 < M) (a : ℤ) (i : ℤ) :
    (a + M * i) % ((p * M : ℕ) : ℤ) = a % M + M * ((a / M + i) % p) := by
  have hM' : (0 : ℤ) < M := by exact_mod_cast hM
  have hp' : (0 : ℤ) < p := by exact_mod_cast hp
  obtain ⟨t, ht⟩ : ∃ t, t = a / M + i := ⟨_, rfl⟩
  have h1 := Int.emod_add_mul_ediv a M
  have h2 := Int.emod_add_mul_ediv t p
  have e1 : a + M * i = (a % M + M * (t % p)) + ((p * M : ℕ) : ℤ) * (t / p) := by
    push_cast
    linear_combination (-1 : ℤ) * h1 - (M : ℤ) * h2 - (M : ℤ) * ht
  rw [← ht, e1, Int.add_mul_emod_self_left]
  have h3 := Int.emod_nonneg a hM'.ne'
  have h4 := Int.emod_lt_of_pos a hM'
  have h5 := Int.emod_nonneg t hp'.ne'
  have h6 := Int.emod_lt_of_pos t hp'
  apply Int.emod_eq_of_lt
  · nlinarith [mul_nonneg hM'.le h5]
  · push_cast
    nlinarith [mul_le_mul_of_nonneg_left (show t % p ≤ p - 1 by omega) hM'.le]

/- English proof (translation)
Establish `hMq : (M : ℚ) ≠ 0` using `by exact_mod_cast hM.ne'`. Establish `hpq : (p : ℚ) ≠ 0` using `by exact_mod_cast hp.ne'`. Establish `hterm : ∀ i : ℕ, frc (p * M) (a + M * i) = (frc M a + (((a / M + i) % p : ℤ) : ℚ)) / p`. Introduce `i`. Simplify using `only [frc]`.

Rewrite using `[dist_emod p M hp hM a i]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Simplify using `only [hterm]`. Conclude with `(dist_shift p hp (a / M) fun n : ℤ => g ((frc M a + n) / p)).trans (by simp)`.
-/
theorem dist_frc_perm {α : Type} [AddCommMonoid α] (p M : ℕ) (hp : 0 < p) (hM : 0 < M) (a : ℤ) (g : ℚ → α) :
    ∑ i ∈ range p, g (frc (p * M) (a + M * i)) = ∑ k ∈ range p, g ((frc M a + k) / p) := by
  have hMq : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne'
  have hterm : ∀ i : ℕ, frc (p * M) (a + M * i) = (frc M a + (((a / M + i) % p : ℤ) : ℚ)) / p := by
    intro i
    simp only [frc]
    rw [dist_emod p M hp hM a i]
    push_cast
    field_simp
  simp only [hterm]
  exact (dist_shift p hp (a / M) fun n : ℤ => g ((frc M a + n) / p)).trans (by simp)

/- English proof (translation)
Establish `hMz : (M : ℤ) ≠ 0` using `by exact_mod_cast hM.ne'`. Establish `hp' : (0 : ℤ) < p` using `by exact_mod_cast hp`. Distinguish the cases in `h : A ≡ a [ZMOD M]`. Rewrite using `[if_pos h]`. Take `⟨t, ht⟩ : (M : ℤ) ∣ A - a` from `Int.ModEq.dvd h.symm`.

Establish `hcond : ∀ i : ℕ, i < p → (A ≡ a + M * i [ZMOD ((p * M : ℕ) : ℤ)] ↔ (i : ℤ) = t % p)`. Introduce `i hi`. Rewrite using `[Int.modEq_iff_dvd]`. Establish `e : a + M * i - A = M * (i - t)` using `by linear_combination -ht`. Rewrite using `[e, show ((p * M : ℕ) : ℤ) = M * p by push_cast; ring, mul_dvd_mul_iff_left hMz]`.

Prove the components needed by the constructor for the conclusion. Introduce `hd`. Establish `h1 : t % p = (i : ℤ) % p` using `Int.modEq_iff_dvd.mpr hd`. Rewrite using `[h1, Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hi)]`. Introduce `he`.

Rewrite using `[he]`. Conclude with `(Int.mod_modEq t p).symm.dvd`. Take `⟨i0, hi0⟩ : ∃ i0 : ℕ, (i0 : ℤ) = t % p` from `⟨(t % p).toNat, Int.toNat_of_nonneg (Int.emod_nonneg t hp'.ne')⟩`. Establish `hi0lt : i0 < p`. Use `Int.emod_lt_of_pos t hp'` as an intermediate fact.

Rewrite `this` using `[← hi0]`. Conclude with `this` after adjusting the coercions. Rewrite using `[Finset.sum_eq_single_of_mem i0 (Finset.mem_range.mpr hi0lt)]`. Rewrite using `[if_pos ((hcond i0 hi0lt).mpr hi0)]`. Introduce `i hi hne`.

Rewrite using `[if_neg]`. Introduce `hc`. Apply `hne` to reduce the goal to its premises. Use `(hcond i (Finset.mem_range.mp hi)).mp hc` as an intermediate fact. Conclude with `this.trans hi0.symm` after adjusting the coercions.

Rewrite using `[if_neg h]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `i _`. Rewrite using `[if_neg]`. Introduce `hc`.

Apply `h` to reduce the goal to its premises. Establish `hc' : A ≡ a + M * i [ZMOD (p : ℤ) * M]`. Move the coercions through the operations in `at hc`. Conclude with `hc`. Establish `h1 : A ≡ a + M * i [ZMOD M]` using `Int.ModEq.of_mul_left _ hc'`.

Establish `h2 : a + M * i ≡ a [ZMOD M]` using `by show (a + M * i) % M = a % M`. Conclude with `Int.add_mul_emod_self_left _ _ _`. Conclude with `h1.trans h2`.
-/
theorem dist_sel {α : Type} [AddCommMonoid α] (p M : ℕ) (hp : 0 < p) (hM : 0 < M) (A a : ℤ) (f : α) :
    ∑ i ∈ range p, (if A ≡ a + M * i [ZMOD ((p * M : ℕ) : ℤ)] then f else 0) =
      if A ≡ a [ZMOD M] then f else 0 := by
  have hMz : (M : ℤ) ≠ 0 := by exact_mod_cast hM.ne'
  have hp' : (0 : ℤ) < p := by exact_mod_cast hp
  by_cases h : A ≡ a [ZMOD M]
  · rw [if_pos h]
    obtain ⟨t, ht⟩ : (M : ℤ) ∣ A - a := Int.ModEq.dvd h.symm
    have hcond : ∀ i : ℕ, i < p →
        (A ≡ a + M * i [ZMOD ((p * M : ℕ) : ℤ)] ↔ (i : ℤ) = t % p) := by
      intro i hi
      rw [Int.modEq_iff_dvd]
      have e : a + M * i - A = M * (i - t) := by linear_combination -ht
      rw [e, show ((p * M : ℕ) : ℤ) = M * p by push_cast; ring, mul_dvd_mul_iff_left hMz]
      constructor
      · intro hd
        have h1 : t % p = (i : ℤ) % p := Int.modEq_iff_dvd.mpr hd
        rw [h1, Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hi)]
      · intro he
        rw [he]
        exact (Int.mod_modEq t p).symm.dvd
    obtain ⟨i0, hi0⟩ : ∃ i0 : ℕ, (i0 : ℤ) = t % p :=
      ⟨(t % p).toNat, Int.toNat_of_nonneg (Int.emod_nonneg t hp'.ne')⟩
    have hi0lt : i0 < p := by
      have := Int.emod_lt_of_pos t hp'
      rw [← hi0] at this
      exact_mod_cast this
    rw [Finset.sum_eq_single_of_mem i0 (Finset.mem_range.mpr hi0lt)]
    · rw [if_pos ((hcond i0 hi0lt).mpr hi0)]
    · intro i hi hne
      rw [if_neg]
      intro hc
      apply hne
      have := (hcond i (Finset.mem_range.mp hi)).mp hc
      exact_mod_cast this.trans hi0.symm
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro i _
    rw [if_neg]
    intro hc
    apply h
    have hc' : A ≡ a + M * i [ZMOD (p : ℤ) * M] := by
      push_cast at hc
      exact hc
    have h1 : A ≡ a + M * i [ZMOD M] := Int.ModEq.of_mul_left _ hc'
    have h2 : a + M * i ≡ a [ZMOD M] := by
      show (a + M * i) % M = a % M
      exact Int.add_mul_emod_self_left _ _ _
    exact h1.trans h2

open scoped Classical in
/- English proof (translation)
Use `split_ifs with h`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[geom_sum_eq h, hω]`. Simplify using the standard rewrite rules.
-/
theorem dist_geom0 (p : ℕ) {K : Type} [Field K] (ω : K) (hω : ω ^ p = 1) :
    ∑ i ∈ range p, ω ^ i = if ω = 1 then (p : K) else 0 := by
  split_ifs with h
  · subst h
    simp
  · rw [geom_sum_eq h, hω]
    simp

/- English proof (translation)
Establish `hζ0 : ζ ≠ 0` using `hζ.ne_zero (Nat.mul_pos hp hM).ne'`. Establish `e : ∀ i : ℕ, ζ ^ ((a + M * i) * d) = ζ ^ (a * d) * (ζ ^ ((M : ℤ) * d)) ^ i`. Introduce `i`. Rewrite using `[← zpow_natCast, ← zpow_mul, ← zpow_add₀ hζ0]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Simplify using `only [e, ← Finset.mul_sum]`. Establish `hω : (ζ ^ ((M : ℤ) * d)) ^ p = 1`. Rewrite using `[← zpow_natCast, ← zpow_mul]`. Conclude with `(hζ.zpow_eq_one_iff_dvd _).mpr ⟨d, by push_cast; ring⟩`.

Rewrite using `[dist_geom0 p _ hω]`. Establish `hiff : ζ ^ ((M : ℤ) * d) = 1 ↔ (p : ℤ) ∣ d`. Rewrite using `[hζ.zpow_eq_one_iff_dvd]`. Use `push_cast`. Rewrite using `[mul_comm (p : ℤ) M]`.

Conclude with `mul_dvd_mul_iff_left (by exact_mod_cast hM.ne')`. Distinguish the cases in `hd : (p : ℤ) ∣ d`. Rewrite using `[if_pos (hiff.mpr hd), if_pos hd]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[if_neg (mt hiff.mp hd), if_neg hd]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem dist_geom (p M : ℕ) {K : Type} [Field K] (ζ : K) (hζ : IsPrimitiveRoot ζ (p * M)) (hp : 0 < p)
    (hM : 0 < M) (a d : ℤ) :
    ∑ i ∈ range p, ζ ^ ((a + M * i) * d) = if (p : ℤ) ∣ d then (p : K) * ζ ^ (a * d) else 0 := by
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (Nat.mul_pos hp hM).ne'
  have e : ∀ i : ℕ, ζ ^ ((a + M * i) * d) = ζ ^ (a * d) * (ζ ^ ((M : ℤ) * d)) ^ i := by
    intro i
    rw [← zpow_natCast, ← zpow_mul, ← zpow_add₀ hζ0]
    congr 1
    ring
  simp only [e, ← Finset.mul_sum]
  have hω : (ζ ^ ((M : ℤ) * d)) ^ p = 1 := by
    rw [← zpow_natCast, ← zpow_mul]
    exact (hζ.zpow_eq_one_iff_dvd _).mpr ⟨d, by push_cast; ring⟩
  rw [dist_geom0 p _ hω]
  have hiff : ζ ^ ((M : ℤ) * d) = 1 ↔ (p : ℤ) ∣ d := by
    rw [hζ.zpow_eq_one_iff_dvd]
    push_cast
    rw [mul_comm (p : ℤ) M]
    exact mul_dvd_mul_iff_left (by exact_mod_cast hM.ne')
  by_cases hd : (p : ℤ) ∣ d
  · rw [if_pos (hiff.mpr hd), if_pos hd]
    ring
  · rw [if_neg (mt hiff.mp hd), if_neg hd]
    ring

/- English proof (translation)
Establish `hζ0 : ζ ≠ 0` using `hζ.ne_zero (Nat.mul_pos hp hM).ne'`. Take `⟨w, hwdef⟩ : ∃ w, w = (ζ ^ p) ^ a` from `⟨_, rfl⟩`. Rewrite using `[← hwdef]`. Establish `hw1 : w ≠ 1`. Introduce `h`.

Apply `ha` to reduce the goal to its premises. Establish `h' : ζ ^ ((p : ℤ) * a) = 1`. Rewrite using `[zpow_mul, zpow_natCast, ← hwdef]`. Conclude with `h`. Rewrite `h'` using `[hζ.zpow_eq_one_iff_dvd]`.

Move the coercions through the operations in `at h'`. Conclude with `(mul_dvd_mul_iff_left (by exact_mod_cast hp.ne' : (p : ℤ) ≠ 0)).mp h'`. Establish `hxp : ∀ i : ℕ, (ζ ^ (a + M * i)) ^ p = w`. Introduce `i`. Establish `hpm : ζ ^ (((p * M : ℕ) : ℤ) * i) = 1`.

Rewrite using `[zpow_mul, zpow_natCast ζ (p * M), hζ.pow_eq_one, one_zpow]`. Rewrite using `[← zpow_natCast, ← zpow_mul, show (a + M * i) * (p : ℤ) = p * a + ((p * M : ℕ) : ℤ) * i by push_cast; ring, zpow_add₀ hζ0, hpm, mul_one, zpow_mul, zpow_natCast, hwdef]`. Establish `hx1 : ∀ i : ℕ, 1 - ζ ^ (a + M * i) ≠ 0` using `fun i h => hw1 (by rw [← hxp i, ← sub_eq_zero.mp h, one_pow])`. Establish `hw0 : 1 - w ≠ 0` using `sub_ne_zero.mpr hw1.symm`. Establish `hinv : ∀ i : ℕ, 1 / (1 - ζ ^ (a + M * i)) = (∑ k ∈ range p, ζ ^ ((a + M * i) * (k : ℤ))) / (1 - w)`.

Introduce `i`. Establish `hk : ∀ k : ℕ, ζ ^ ((a + M * i) * (k : ℤ)) = (ζ ^ (a + M * i)) ^ k` using `fun k => by`. Rewrite using `[zpow_mul, zpow_natCast]`. Simplify using `only [hk]`. Rewrite using `[div_eq_div_iff (hx1 i) hw0, one_mul, ← hxp i, geom_sum_mul_neg]`.

Establish `hsplit : ∀ i : ℕ, (1 / 2 : K) * (1 + ζ ^ (a + M * i)) / (1 - ζ ^ (a + M * i)) = 1 / (1 - ζ ^ (a + M * i)) - 1 / 2`. Introduce `i`. Clear denominators, using `[hx1 i]` for the nonvanishing conditions. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [hsplit, Finset.sum_sub_distrib, hinv, ← Finset.sum_div]`.

Rewrite using `[Finset.sum_comm]`. Establish `hinner : ∀ k ∈ range p, ∑ i ∈ range p, ζ ^ ((a + M * i) * (k : ℤ)) = if k = 0 then (p : K) else 0`. Introduce `k hk`. Rewrite using `[dist_geom p M ζ hζ hp hM a k]`. Distinguish the cases in `h0 : k = 0`.

Substitute `h0` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[if_neg, if_neg h0]`. Introduce `hd`. Establish `hd' : p ∣ k` using `by exact_mod_cast hd`.

Conclude with `absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero h0) hd') (Nat.not_le.mpr (Finset.mem_range.mp hk))`. Rewrite using `[Finset.sum_congr rfl hinner, Finset.sum_ite_eq', if_pos (Finset.mem_range.mpr hp), Finset.sum_const, Finset.card_range, nsmul_eq_mul]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dist_roots (p M : ℕ) {K : Type} [Field K] [CharZero K] (ζ : K) (hζ : IsPrimitiveRoot ζ (p * M)) (hp : 0 < p)
    (hM : 0 < M) (a : ℤ) (ha : ¬ (M : ℤ) ∣ a) :
    ∑ i ∈ range p, (1 / 2 : K) * (1 + ζ ^ (a + M * i)) / (1 - ζ ^ (a + M * i)) =
      (p : K) * ((1 / 2 : K) * (1 + (ζ ^ p) ^ a) / (1 - (ζ ^ p) ^ a)) := by
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (Nat.mul_pos hp hM).ne'
  obtain ⟨w, hwdef⟩ : ∃ w, w = (ζ ^ p) ^ a := ⟨_, rfl⟩
  rw [← hwdef]
  have hw1 : w ≠ 1 := by
    intro h
    apply ha
    have h' : ζ ^ ((p : ℤ) * a) = 1 := by
      rw [zpow_mul, zpow_natCast, ← hwdef]
      exact h
    rw [hζ.zpow_eq_one_iff_dvd] at h'
    push_cast at h'
    exact (mul_dvd_mul_iff_left (by exact_mod_cast hp.ne' : (p : ℤ) ≠ 0)).mp h'
  have hxp : ∀ i : ℕ, (ζ ^ (a + M * i)) ^ p = w := by
    intro i
    have hpm : ζ ^ (((p * M : ℕ) : ℤ) * i) = 1 := by
      rw [zpow_mul, zpow_natCast ζ (p * M), hζ.pow_eq_one, one_zpow]
    rw [← zpow_natCast, ← zpow_mul,
      show (a + M * i) * (p : ℤ) = p * a + ((p * M : ℕ) : ℤ) * i by push_cast; ring,
      zpow_add₀ hζ0, hpm, mul_one, zpow_mul, zpow_natCast, hwdef]
  have hx1 : ∀ i : ℕ, 1 - ζ ^ (a + M * i) ≠ 0 := fun i h =>
    hw1 (by rw [← hxp i, ← sub_eq_zero.mp h, one_pow])
  have hw0 : 1 - w ≠ 0 := sub_ne_zero.mpr hw1.symm
  have hinv : ∀ i : ℕ, 1 / (1 - ζ ^ (a + M * i)) =
      (∑ k ∈ range p, ζ ^ ((a + M * i) * (k : ℤ))) / (1 - w) := by
    intro i
    have hk : ∀ k : ℕ, ζ ^ ((a + M * i) * (k : ℤ)) = (ζ ^ (a + M * i)) ^ k := fun k => by
      rw [zpow_mul, zpow_natCast]
    simp only [hk]
    rw [div_eq_div_iff (hx1 i) hw0, one_mul, ← hxp i, geom_sum_mul_neg]
  have hsplit : ∀ i : ℕ, (1 / 2 : K) * (1 + ζ ^ (a + M * i)) / (1 - ζ ^ (a + M * i)) =
      1 / (1 - ζ ^ (a + M * i)) - 1 / 2 := by
    intro i
    field_simp [hx1 i]
    ring
  simp only [hsplit, Finset.sum_sub_distrib, hinv, ← Finset.sum_div]
  rw [Finset.sum_comm]
  have hinner : ∀ k ∈ range p, ∑ i ∈ range p, ζ ^ ((a + M * i) * (k : ℤ)) = if k = 0 then (p : K) else 0 := by
    intro k hk
    rw [dist_geom p M ζ hζ hp hM a k]
    by_cases h0 : k = 0
    · subst h0
      simp
    · rw [if_neg, if_neg h0]
      intro hd
      have hd' : p ∣ k := by exact_mod_cast hd
      exact absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero h0) hd') (Nat.not_le.mpr (Finset.mem_range.mp hk))
  rw [Finset.sum_congr rfl hinner, Finset.sum_ite_eq', if_pos (Finset.mem_range.mpr hp),
    Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp
  ring

/- English proof (translation)
Take `⟨j', rfl⟩ : ∃ j', j = j' + 1` from `⟨j - 1, by omega⟩`. Establish `hpK : (p : K) ≠ 0` using `by exact_mod_cast hp.ne'`. Establish `hMK : (M : K) ≠ 0` using `by exact_mod_cast hM.ne'`. Simplify using `only [Nat.add_sub_cancel]`. Establish `hz : (p : K) ^ ((2 : ℤ) - ((j' + 1 : ℕ) : ℤ)) = p / p ^ j'`.

Rewrite using `[show (2 : ℤ) - ((j' + 1 : ℕ) : ℤ) = 1 - (j' : ℤ) by push_cast; ring, zpow_sub₀ hpK, zpow_one, zpow_natCast]`. Rewrite using `[hz]`. Distinguish the cases in `hpn : p ∣ n`. Rewrite using `[if_pos hpn]`. Take `⟨m, rfl⟩` from `hpn`.

Establish `hm : m ≠ 0`. Introduce and unpack `rfl`. Simplify using `at hn`. Rewrite using `[Nat.mul_div_cancel_left m hp]`. Simplify using `only [coefPos, Nat.add_sub_cancel]`.

Rewrite using `[← Finset.sum_filter, Finset.mul_sum]`. Apply `Finset.sum_nbij' (fun d => d / p) (fun e => p * e)` to reduce the goal to its premises. Introduce `d hd`. Simplify using `only [Finset.mem_filter, Nat.mem_divisors, Int.natCast_dvd_natCast] at hd`. Take `⟨⟨hdn, -⟩, e, rfl⟩` from `hd`.

Rewrite using `[Nat.mul_div_cancel_left e hp]`. Simplify using `only [Nat.mem_divisors]`. Conclude with `⟨Nat.dvd_of_mul_dvd_mul_left hp hdn, hm⟩`. Introduce `e he`. Simplify using `only [Nat.mem_divisors] at he`.

Simplify using `only [Finset.mem_filter, Nat.mem_divisors, Int.natCast_dvd_natCast]`. Conclude with `⟨⟨mul_dvd_mul_left p he.1, Nat.mul_ne_zero hp.ne' hm⟩, dvd_mul_right p e⟩`. Introduce `d hd`. Simplify using `only [Finset.mem_filter, Nat.mem_divisors, Int.natCast_dvd_natCast] at hd`. Conclude with `Nat.mul_div_cancel' hd.2`.

Introduce `e _`. Conclude with `Nat.mul_div_cancel_left e hp`. Introduce `d hd`. Simplify using `only [Finset.mem_filter, Nat.mem_divisors, Int.natCast_dvd_natCast] at hd`. Take `⟨-, e, rfl⟩` from `hd`.

Rewrite using `[Nat.mul_div_cancel_left e hp, Nat.mul_div_mul_left m e hp]`. Establish `hz1 : ζ ^ (a₂ * ((p * e : ℕ) : ℤ)) = (ζ ^ p) ^ (a₂ * e)`. Rewrite using `[← zpow_natCast ζ p, ← zpow_mul]`. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `hz2 : ζ ^ (-(a₂ * ((p * e : ℕ) : ℤ))) = (ζ ^ p) ^ (-(a₂ * e))`. Rewrite using `[← zpow_natCast ζ p, ← zpow_mul]`. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `hq1 : ∀ x : K, (x / ((p * M : ℕ) : K)) ^ j' = (x / M) ^ j' / p ^ j'` using `fun x => by`. Use `push_cast`. Rewrite using `[mul_comm (p : K) M, ← div_div, div_pow]`. Establish `hq2 : ∀ x : K, (-(x / ((p * M : ℕ) : K))) ^ j' = (-(x / M)) ^ j' / p ^ j'` using `fun x => by`.

Use `push_cast`. Rewrite using `[mul_comm (p : K) M, ← div_div, ← neg_div, div_pow]`. Rewrite using `[hz1, hz2]`. Simplify using `only [hq1, hq2]`. Apply the tactic sequence `split_ifs <;> ring`.

Rewrite using `[if_neg hpn, mul_zero]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `d hd`. Rewrite using `[if_neg]`. Introduce `hd'`.

Apply `hpn` to reduce the goal to its premises. Establish `: p ∣ d` using `by exact_mod_cast hd'`. Conclude with `this.trans (Nat.dvd_of_mem_divisors hd)`.
-/
theorem dist_reindex (p M j : ℕ) (hp : 0 < p) {K : Type} [Field K] [CharZero K] (ζ : K) (hM : 0 < M)
    (hj : 1 ≤ j) (a₁ a₂ : ℤ) (n : ℕ) (hn : n ≠ 0) :
    ∑ d ∈ n.divisors, (if (p : ℤ) ∣ (d : ℤ) then (p : K) *
      ((if ((n / d : ℕ) : ℤ) ≡ a₁ [ZMOD M] then (((n / d : ℕ) : K) / ((p * M : ℕ) : K)) ^ (j - 1) * ζ ^ (a₂ * d) else 0) -
       (if -((n / d : ℕ) : ℤ) ≡ a₁ [ZMOD M] then (-(((n / d : ℕ) : K) / ((p * M : ℕ) : K))) ^ (j - 1) * ζ ^ (-(a₂ * d)) else 0))
      else 0) =
    (p : K) ^ ((2 : ℤ) - j) * (if p ∣ n then coefPos j M (ζ ^ p) a₁ a₂ (n / p) else 0) := by
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  have hpK : (p : K) ≠ 0 := by exact_mod_cast hp.ne'
  have hMK : (M : K) ≠ 0 := by exact_mod_cast hM.ne'
  simp only [Nat.add_sub_cancel]
  have hz : (p : K) ^ ((2 : ℤ) - ((j' + 1 : ℕ) : ℤ)) = p / p ^ j' := by
    rw [show (2 : ℤ) - ((j' + 1 : ℕ) : ℤ) = 1 - (j' : ℤ) by push_cast; ring, zpow_sub₀ hpK, zpow_one,
      zpow_natCast]
  rw [hz]
  by_cases hpn : p ∣ n
  · rw [if_pos hpn]
    obtain ⟨m, rfl⟩ := hpn
    have hm : m ≠ 0 := by
      rintro rfl
      simp at hn
    rw [Nat.mul_div_cancel_left m hp]
    simp only [coefPos, Nat.add_sub_cancel]
    rw [← Finset.sum_filter, Finset.mul_sum]
    apply Finset.sum_nbij' (fun d => d / p) (fun e => p * e)
    · intro d hd
      simp only [Finset.mem_filter, Nat.mem_divisors, Int.natCast_dvd_natCast] at hd
      obtain ⟨⟨hdn, -⟩, e, rfl⟩ := hd
      rw [Nat.mul_div_cancel_left e hp]
      simp only [Nat.mem_divisors]
      exact ⟨Nat.dvd_of_mul_dvd_mul_left hp hdn, hm⟩
    · intro e he
      simp only [Nat.mem_divisors] at he
      simp only [Finset.mem_filter, Nat.mem_divisors, Int.natCast_dvd_natCast]
      exact ⟨⟨mul_dvd_mul_left p he.1, Nat.mul_ne_zero hp.ne' hm⟩, dvd_mul_right p e⟩
    · intro d hd
      simp only [Finset.mem_filter, Nat.mem_divisors, Int.natCast_dvd_natCast] at hd
      exact Nat.mul_div_cancel' hd.2
    · intro e _
      exact Nat.mul_div_cancel_left e hp
    · intro d hd
      simp only [Finset.mem_filter, Nat.mem_divisors, Int.natCast_dvd_natCast] at hd
      obtain ⟨-, e, rfl⟩ := hd
      rw [Nat.mul_div_cancel_left e hp, Nat.mul_div_mul_left m e hp]
      have hz1 : ζ ^ (a₂ * ((p * e : ℕ) : ℤ)) = (ζ ^ p) ^ (a₂ * e) := by
        rw [← zpow_natCast ζ p, ← zpow_mul]
        congr 1
        push_cast
        ring
      have hz2 : ζ ^ (-(a₂ * ((p * e : ℕ) : ℤ))) = (ζ ^ p) ^ (-(a₂ * e)) := by
        rw [← zpow_natCast ζ p, ← zpow_mul]
        congr 1
        push_cast
        ring
      have hq1 : ∀ x : K, (x / ((p * M : ℕ) : K)) ^ j' = (x / M) ^ j' / p ^ j' := fun x => by
        push_cast
        rw [mul_comm (p : K) M, ← div_div, div_pow]
      have hq2 : ∀ x : K, (-(x / ((p * M : ℕ) : K))) ^ j' = (-(x / M)) ^ j' / p ^ j' := fun x => by
        push_cast
        rw [mul_comm (p : K) M, ← div_div, ← neg_div, div_pow]
      rw [hz1, hz2]
      simp only [hq1, hq2]
      split_ifs <;> ring
  · rw [if_neg hpn, mul_zero]
    apply Finset.sum_eq_zero
    intro d hd
    rw [if_neg]
    intro hd'
    apply hpn
    have : p ∣ d := by exact_mod_cast hd'
    exact this.trans (Nat.dvd_of_mem_divisors hd)

/- English proof (translation)
Establish `h` using `dist_frc_perm p M hp hM a (fun x : ℚ => (1 / 2 : ℚ) - x)`. Rewrite using `[h]`. Take `⟨q, rfl⟩ : ∃ q, p = q + 1` from `⟨p - 1, by omega⟩`. Establish `hsum : (∑ k ∈ range (q + 1), (k : ℚ)) = (q + 1) * q / 2`. Establish `h0` using `Finset.sum_range_id_mul_two (q + 1)`.

Simplify using `only [Nat.add_sub_cancel] at h0`. Establish `h' : ((∑ i ∈ range (q + 1), i : ℕ) : ℚ) * 2 = ((q + 1) * q : ℕ)` using `by exact_mod_cast h0`. Move the coercions through the operations in `at h'`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, ← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, hsum]`.

Simplify using `only [nsmul_eq_mul]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dist_half (p M : ℕ) (hp : 0 < p) (hM : 0 < M) (a : ℤ) :
    ∑ i ∈ range p, ((1 / 2 : ℚ) - frc (p * M) (a + M * i)) = 1 / 2 - frc M a := by
  have h := dist_frc_perm p M hp hM a (fun x : ℚ => (1 / 2 : ℚ) - x)
  rw [h]
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  have hsum : (∑ k ∈ range (q + 1), (k : ℚ)) = (q + 1) * q / 2 := by
    have h0 := Finset.sum_range_id_mul_two (q + 1)
    simp only [Nat.add_sub_cancel] at h0
    have h' : ((∑ i ∈ range (q + 1), i : ℕ) : ℚ) * 2 = ((q + 1) * q : ℕ) := by exact_mod_cast h0
    push_cast at h'
    linarith
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, ← Finset.sum_div,
    Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, hsum]
  simp only [nsmul_eq_mul]
  push_cast
  field_simp
  ring

/- English proof (translation)
Establish `hinner : ∀ i₁ ∈ range p, ∑ i₂ ∈ range p, (if A ≡ a₁ + M * i₁ [ZMOD ((p * M : ℕ) : ℤ)] then X * ζ ^ ((a₂ + M * i₂) * d) else 0) = if A ≡ a₁ + M * i₁ [ZMOD ((p * M : ℕ) : ℤ)] then X * (if (p : ℤ) ∣ d then (p : K) * ζ ^ (a₂ * d) else 0) else 0`. Introduce `i₁ _`. Distinguish the cases in `hc : A ≡ a₁ + M * i₁ [ZMOD ((p * M : ℕ) : ℤ)]`. Simplify using `only [if_pos hc]`. Rewrite using `[← Finset.mul_sum, dist_geom p M ζ hζ hp hM a₂ d]`.

Simplify using `only [if_neg hc, Finset.sum_const_zero]`. Rewrite using `[Finset.sum_congr rfl hinner, dist_sel p M hp hM A a₁]`. Apply the tactic sequence `split_ifs <;> ring`.
-/
theorem dist_term (p M : ℕ) {K : Type} [Field K] (ζ : K) (hζ : IsPrimitiveRoot ζ (p * M)) (hp : 0 < p)
    (hM : 0 < M) (A a₁ a₂ d : ℤ) (X : K) :
    ∑ i₁ ∈ range p, ∑ i₂ ∈ range p,
      (if A ≡ a₁ + M * i₁ [ZMOD ((p * M : ℕ) : ℤ)] then X * ζ ^ ((a₂ + M * i₂) * d) else 0) =
      if (p : ℤ) ∣ d then (p : K) * (if A ≡ a₁ [ZMOD M] then X * ζ ^ (a₂ * d) else 0) else 0 := by
  have hinner : ∀ i₁ ∈ range p, ∑ i₂ ∈ range p,
      (if A ≡ a₁ + M * i₁ [ZMOD ((p * M : ℕ) : ℤ)] then X * ζ ^ ((a₂ + M * i₂) * d) else 0) =
      if A ≡ a₁ + M * i₁ [ZMOD ((p * M : ℕ) : ℤ)] then
        X * (if (p : ℤ) ∣ d then (p : K) * ζ ^ (a₂ * d) else 0) else 0 := by
    intro i₁ _
    by_cases hc : A ≡ a₁ + M * i₁ [ZMOD ((p * M : ℕ) : ℤ)]
    · simp only [if_pos hc]
      rw [← Finset.mul_sum, dist_geom p M ζ hζ hp hM a₂ d]
    · simp only [if_neg hc, Finset.sum_const_zero]
  rw [Finset.sum_congr rfl hinner, dist_sel p M hp hM A a₁]
  split_ifs <;> ring

/- English proof (translation)
Rewrite using `[← dist_reindex p M j hp ζ hM hj a₁ a₂ n hn]`. Simplify using `only [coefPos]`. Establish `hswap : ∀ F : ℕ → ℕ → ℕ → K, ∑ i₁ ∈ range p, ∑ i₂ ∈ range p, ∑ d ∈ n.divisors, F i₁ i₂ d = ∑ d ∈ n.divisors, ∑ i₁ ∈ range p, ∑ i₂ ∈ range p, F i₁ i₂ d`. Introduce `F`. Combine the equalities or inequalities in the displayed calculation.

Use `(hswap _).trans (Finset.sum_congr rfl fun d _ => ?_)` and prove the remaining obligations. Simplify using `only [Finset.sum_sub_distrib]`. Establish `h2 : ∀ i₂ : ℕ, ζ ^ (-((a₂ + M * i₂) * (d : ℤ))) = ζ ^ ((a₂ + M * i₂) * (-(d : ℤ)))` using `fun i₂ => by rw [mul_neg]`. Simplify using `only [h2]`. Rewrite using `[dist_term p M ζ hζ hp hM _ a₁ a₂ (d : ℤ), dist_term p M ζ hζ hp hM _ a₁ a₂ (-(d : ℤ))]`.

Simplify using `only [dvd_neg, mul_neg]`. Apply the tactic sequence `split_ifs <;> ring`.
-/
theorem dist_pos (p M j : ℕ) (hp : 0 < p) {K : Type} [Field K] [CharZero K] (ζ : K)
    (hζ : IsPrimitiveRoot ζ (p * M)) (hM : 0 < M) (hj : 1 ≤ j) (a₁ a₂ : ℤ) (n : ℕ) (hn : n ≠ 0) :
    ∑ i₁ ∈ range p, ∑ i₂ ∈ range p, coefPos j (p * M) ζ (a₁ + M * i₁) (a₂ + M * i₂) n =
      (p : K) ^ ((2 : ℤ) - j) * (if p ∣ n then coefPos j M (ζ ^ p) a₁ a₂ (n / p) else 0) := by
  rw [← dist_reindex p M j hp ζ hM hj a₁ a₂ n hn]
  simp only [coefPos]
  have hswap : ∀ F : ℕ → ℕ → ℕ → K, ∑ i₁ ∈ range p, ∑ i₂ ∈ range p, ∑ d ∈ n.divisors, F i₁ i₂ d =
      ∑ d ∈ n.divisors, ∑ i₁ ∈ range p, ∑ i₂ ∈ range p, F i₁ i₂ d := by
    intro F
    calc _ = ∑ i₁ ∈ range p, ∑ d ∈ n.divisors, ∑ i₂ ∈ range p, F i₁ i₂ d :=
          Finset.sum_congr rfl fun i₁ _ => Finset.sum_comm
      _ = _ := Finset.sum_comm
  refine (hswap _).trans (Finset.sum_congr rfl fun d _ => ?_)
  simp only [Finset.sum_sub_distrib]
  have h2 : ∀ i₂ : ℕ, ζ ^ (-((a₂ + M * i₂) * (d : ℤ))) = ζ ^ ((a₂ + M * i₂) * (-(d : ℤ))) :=
    fun i₂ => by rw [mul_neg]
  simp only [h2]
  rw [dist_term p M ζ hζ hp hM _ a₁ a₂ (d : ℤ), dist_term p M ζ hζ hp hM _ a₁ a₂ (-(d : ℤ))]
  simp only [dvd_neg, mul_neg]
  split_ifs <;> ring

/- English proof (translation)
Establish `hpK : (p : K) ≠ 0` using `by exact_mod_cast hp.ne'`. Distinguish the cases in `hj : j = 1`. Substitute `hj` using the available equality. Simplify using `only [const0, ↓reduceIte]`. Establish `hp1 : (p : K) ^ ((2 : ℤ) - ((1 : ℕ) : ℤ)) = p` using `by norm_num`.

Rewrite using `[hp1]`. Distinguish the cases in `hM1 : (M : ℤ) ∣ a₁`. Rewrite using `[if_pos hM1]`. Establish `hM2 : ¬ (M : ℤ) ∣ a₂` using `fun h => hx ⟨hM1, h⟩`. Establish `hrow : ∀ i₁ ∈ range p, ∑ i₂ ∈ range p, (if ((p * M : ℕ) : ℤ) ∣ a₁ + M * i₁ then (1 / 2 : K) * (1 + ζ ^ (a₂ + M * i₂)) / (1 - ζ ^ (a₂ + M * i₂)) else (((1 / 2 - frc (p * M) (a₁ + M * i₁) : ℚ)) : K)) = (p : K) * ((1 / 2 : K) - ((frc (p * M) (a₁ + M * i₁) : ℚ) : K)) + (if (0 : ℤ) ≡ …`.

Introduce `i₁ _`. Distinguish the cases in `hd : ((p * M : ℕ) : ℤ) ∣ a₁ + M * i₁`. Establish `h0 : (0 : ℤ) ≡ a₁ + M * i₁ [ZMOD ((p * M : ℕ) : ℤ)]` using `(Int.modEq_zero_iff_dvd.mpr hd).symm`. Establish `hf : frc (p * M) (a₁ + M * i₁) = 0`. Simplify using `only [frc, Int.emod_eq_zero_of_dvd hd, Int.cast_zero, zero_div]`.

Rewrite using `[if_pos h0, hf]`. Simplify using `only [if_pos hd]`. Rewrite using `[dist_roots p M ζ hζ hp hM a₂ hM2]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `h0 : ¬ (0 : ℤ) ≡ a₁ + M * i₁ [ZMOD ((p * M : ℕ) : ℤ)]` using `fun h => hd (Int.modEq_zero_iff_dvd.mp h.symm)`. Rewrite using `[if_neg h0]`. Simplify using `only [if_neg hd, Finset.sum_const, Finset.card_range, nsmul_eq_mul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Use `(Finset.sum_congr rfl hrow).trans ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_add_distrib, dist_sel p M hp hM 0 a₁, if_pos ((Int.modEq_zero_iff_dvd.mpr hM1).symm), ← Finset.mul_sum]`. Establish `hhalf : ∑ i₁ ∈ range p, ((1 / 2 : K) - ((frc (p * M) (a₁ + M * i₁) : ℚ) : K)) = 1 / 2`. Establish `h` using `congrArg (Rat.cast : ℚ → K) (dist_half p M hp hM a₁)`. Establish `hf0 : frc M a₁ = 0` using `by simp only [frc, Int.emod_eq_zero_of_dvd hM1, Int.cast_zero, zero_div]`.

Rewrite `h` using `[hf0, sub_zero]`. Move the coercions through the operations in `at h`. Conclude with `h`. Rewrite using `[hhalf]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[if_neg hM1]`. Establish `hrow : ∀ i₁ ∈ range p, ∑ i₂ ∈ range p, (if ((p * M : ℕ) : ℤ) ∣ a₁ + M * i₁ then (1 / 2 : K) * (1 + ζ ^ (a₂ + M * i₂)) / (1 - ζ ^ (a₂ + M * i₂)) else (((1 / 2 - frc (p * M) (a₁ + M * i₁) : ℚ)) : K)) = (p : K) * (((1 / 2 - frc (p * M) (a₁ + M * i₁) : ℚ)) : K)`. Introduce `i₁ _`. Establish `hd : ¬ ((p * M : ℕ) : ℤ) ∣ a₁ + M * i₁` using `fun h => hM1 (by`. Establish `h' : (M : ℤ) ∣ a₁ + M * i₁` using `Dvd.dvd.trans ⟨p, by push_cast; ring⟩ h`.

Conclude with `(dvd_add_left (dvd_mul_right (M : ℤ) (i₁ : ℤ))).mp h')`. Simplify using `only [if_neg hd, Finset.sum_const, Finset.card_range, nsmul_eq_mul]`. Use `(Finset.sum_congr rfl hrow).trans ?_` and prove the remaining obligations. Rewrite using `[← Finset.mul_sum, ← Rat.cast_sum, dist_half p M hp hM a₁]`. Simplify using `only [const0, if_neg hj, Finset.sum_const, Finset.card_range, nsmul_eq_mul]`.

Rewrite using `[← Finset.mul_sum]`. Establish `h1` using `dist_frc_perm p M hp hM a₁ (fun x : ℚ => -((((Polynomial.bernoulli j).eval x / j : ℚ)) : K))`. Rewrite using `[h1]`. Establish `h2` using `dist_raabe p hp j (frc M a₁)`. Establish `h3 : ∑ k ∈ range p, -((((Polynomial.bernoulli j).eval ((frc M a₁ + k) / p) / j : ℚ)) : K) = -(((((p : ℚ) ^ ((1 : ℤ) - j) * (Polynomial.bernoulli j).eval (frc M a₁)) / j : ℚ)) : K)`.

Rewrite using `[← h2]`. Use `push_cast`. Rewrite using `[Finset.sum_neg_distrib, Finset.sum_div]`. Establish `hzp : (p : K) ^ ((2 : ℤ) - j) = p * (p : K) ^ ((1 : ℤ) - j)`. Rewrite using `[← zpow_one_add₀ hpK]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h3, hzp]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dist_const (p M j : ℕ) (hp : 0 < p) {K : Type} [Field K] [CharZero K] (ζ : K)
    (hζ : IsPrimitiveRoot ζ (p * M)) (hM : 0 < M) (a₁ a₂ : ℤ)
    (hx : ¬ ((M : ℤ) ∣ a₁ ∧ (M : ℤ) ∣ a₂)) :
    ∑ i₁ ∈ range p, ∑ i₂ ∈ range p, const0 j (p * M) ζ (a₁ + M * i₁) (a₂ + M * i₂) =
      (p : K) ^ ((2 : ℤ) - j) * const0 j M (ζ ^ p) a₁ a₂ := by
  have hpK : (p : K) ≠ 0 := by exact_mod_cast hp.ne'
  by_cases hj : j = 1
  · subst hj
    simp only [const0, ↓reduceIte]
    have hp1 : (p : K) ^ ((2 : ℤ) - ((1 : ℕ) : ℤ)) = p := by norm_num
    rw [hp1]
    by_cases hM1 : (M : ℤ) ∣ a₁
    · rw [if_pos hM1]
      have hM2 : ¬ (M : ℤ) ∣ a₂ := fun h => hx ⟨hM1, h⟩
      have hrow : ∀ i₁ ∈ range p, ∑ i₂ ∈ range p,
          (if ((p * M : ℕ) : ℤ) ∣ a₁ + M * i₁ then
            (1 / 2 : K) * (1 + ζ ^ (a₂ + M * i₂)) / (1 - ζ ^ (a₂ + M * i₂))
          else (((1 / 2 - frc (p * M) (a₁ + M * i₁) : ℚ)) : K)) =
          (p : K) * ((1 / 2 : K) - ((frc (p * M) (a₁ + M * i₁) : ℚ) : K)) +
            (if (0 : ℤ) ≡ a₁ + M * i₁ [ZMOD ((p * M : ℕ) : ℤ)] then
              (p : K) * ((1 / 2 : K) * (1 + (ζ ^ p) ^ a₂) / (1 - (ζ ^ p) ^ a₂)) - (p : K) * (1 / 2)
            else 0) := by
        intro i₁ _
        by_cases hd : ((p * M : ℕ) : ℤ) ∣ a₁ + M * i₁
        · have h0 : (0 : ℤ) ≡ a₁ + M * i₁ [ZMOD ((p * M : ℕ) : ℤ)] :=
            (Int.modEq_zero_iff_dvd.mpr hd).symm
          have hf : frc (p * M) (a₁ + M * i₁) = 0 := by
            simp only [frc, Int.emod_eq_zero_of_dvd hd, Int.cast_zero, zero_div]
          rw [if_pos h0, hf]
          simp only [if_pos hd]
          rw [dist_roots p M ζ hζ hp hM a₂ hM2]
          push_cast
          ring
        · have h0 : ¬ (0 : ℤ) ≡ a₁ + M * i₁ [ZMOD ((p * M : ℕ) : ℤ)] :=
            fun h => hd (Int.modEq_zero_iff_dvd.mp h.symm)
          rw [if_neg h0]
          simp only [if_neg hd, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
      refine (Finset.sum_congr rfl hrow).trans ?_
      rw [Finset.sum_add_distrib, dist_sel p M hp hM 0 a₁,
        if_pos ((Int.modEq_zero_iff_dvd.mpr hM1).symm), ← Finset.mul_sum]
      have hhalf : ∑ i₁ ∈ range p, ((1 / 2 : K) - ((frc (p * M) (a₁ + M * i₁) : ℚ) : K)) = 1 / 2 := by
        have h := congrArg (Rat.cast : ℚ → K) (dist_half p M hp hM a₁)
        have hf0 : frc M a₁ = 0 := by simp only [frc, Int.emod_eq_zero_of_dvd hM1, Int.cast_zero, zero_div]
        rw [hf0, sub_zero] at h
        push_cast at h
        exact h
      rw [hhalf]
      ring
    · rw [if_neg hM1]
      have hrow : ∀ i₁ ∈ range p, ∑ i₂ ∈ range p,
          (if ((p * M : ℕ) : ℤ) ∣ a₁ + M * i₁ then
            (1 / 2 : K) * (1 + ζ ^ (a₂ + M * i₂)) / (1 - ζ ^ (a₂ + M * i₂))
          else (((1 / 2 - frc (p * M) (a₁ + M * i₁) : ℚ)) : K)) =
          (p : K) * (((1 / 2 - frc (p * M) (a₁ + M * i₁) : ℚ)) : K) := by
        intro i₁ _
        have hd : ¬ ((p * M : ℕ) : ℤ) ∣ a₁ + M * i₁ := fun h => hM1 (by
          have h' : (M : ℤ) ∣ a₁ + M * i₁ := Dvd.dvd.trans ⟨p, by push_cast; ring⟩ h
          exact (dvd_add_left (dvd_mul_right (M : ℤ) (i₁ : ℤ))).mp h')
        simp only [if_neg hd, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      refine (Finset.sum_congr rfl hrow).trans ?_
      rw [← Finset.mul_sum, ← Rat.cast_sum, dist_half p M hp hM a₁]
  · simp only [const0, if_neg hj, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [← Finset.mul_sum]
    have h1 := dist_frc_perm p M hp hM a₁
      (fun x : ℚ => -((((Polynomial.bernoulli j).eval x / j : ℚ)) : K))
    rw [h1]
    have h2 := dist_raabe p hp j (frc M a₁)
    have h3 : ∑ k ∈ range p, -((((Polynomial.bernoulli j).eval ((frc M a₁ + k) / p) / j : ℚ)) : K) =
        -(((((p : ℚ) ^ ((1 : ℤ) - j) * (Polynomial.bernoulli j).eval (frc M a₁)) / j : ℚ)) : K) := by
      rw [← h2]
      push_cast
      rw [Finset.sum_neg_distrib, Finset.sum_div]
    have hzp : (p : K) ^ ((2 : ℤ) - j) = p * (p : K) ^ ((1 : ℤ) - j) := by
      rw [← zpow_one_add₀ hpK]
      congr 1
      ring
    rw [h3, hzp]
    push_cast
    ring

/- English proof (translation)
Introduce `p hpf M j K _ _ ζ hζ hM hj a₁ a₂ hx r`. Establish `hp : 0 < p` using `hpf.out.pos`. Distinguish the cases in `hr : r = 0`. Substitute `hr` using the available equality. Simplify using `only [eisF, vp, dvd_zero, Nat.zero_div, ↓reduceIte]`.

Conclude with `dist_const p M j hp ζ hζ hM a₁ a₂ hx`. Simplify using `only [eisF, vp, if_neg hr]`. Rewrite using `[dist_pos p M j hp ζ hζ hM hj a₁ a₂ r hr]`. Distinguish the cases in `hpr : p ∣ r`. Establish `hne : ¬ r / p = 0`.

Introduce `h0`. Take `⟨m, rfl⟩` from `hpr`. Rewrite `h0` using `[Nat.mul_div_cancel_left m hp]`. Substitute `h0` using the available equality. Simplify using `at hr`.

Simplify using `only [if_pos hpr, if_neg hne]`. Simplify using `only [if_neg hpr]`.
-/
theorem eisF_distribution : ∀ (p : ℕ) [Fact p.Prime] (M j : ℕ) (K : Type) [Field K] [CharZero K] (ζ : K), IsPrimitiveRoot ζ (p * M) → 0 < M → 1 ≤ j → ∀ a₁ a₂ : ℤ, ¬ ((M : ℤ) ∣ a₁ ∧ (M : ℤ) ∣ a₂) → ∀ r : ℕ, ∑ i₁ ∈ Finset.range p, ∑ i₂ ∈ Finset.range p, eisF j (p * M) ζ (a₁ + M * i₁) (a₂ + M * i₂) r = (p : K) ^ ((2 : ℤ) - j) * vp p (eisF j M (ζ ^ p) a₁ a₂) r := by
  intro p hpf M j K _ _ ζ hζ hM hj a₁ a₂ hx r
  have hp : 0 < p := hpf.out.pos
  by_cases hr : r = 0
  · subst hr
    simp only [eisF, vp, dvd_zero, Nat.zero_div, ↓reduceIte]
    exact dist_const p M j hp ζ hζ hM a₁ a₂ hx
  · simp only [eisF, vp, if_neg hr]
    rw [dist_pos p M j hp ζ hζ hM hj a₁ a₂ r hr]
    by_cases hpr : p ∣ r
    · have hne : ¬ r / p = 0 := by
        intro h0
        obtain ⟨m, rfl⟩ := hpr
        rw [Nat.mul_div_cancel_left m hp] at h0
        subst h0
        simp at hr
      simp only [if_pos hpr, if_neg hne]
    · simp only [if_neg hpr]

end GlobalTheory.EisDist
