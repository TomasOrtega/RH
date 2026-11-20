import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EisensteinS2LimitFormula
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.Taylor
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.TaylorWp

noncomputable section
open scoped BigOperators
open Formalism.L2.Th1.CM (cW wpNum wpDen)
open PowerSeries

namespace Formalism.L2.Th1.F.POf

variable {K : Type} [Field K]

/- English proof (translation)
Unfold `cW`. Rewrite using `[Nat.strongRecOn_eq]`. Apply the tactic sequence `split_ifs <;> rfl`.
-/
theorem cW_eq (g2 g3 : K) (k : ℕ) : cW g2 g3 k =
    if k = 2 then g2 / 20 else if k = 3 then g3 / 28 else
    if 4 ≤ k then
      3 / ((2 * (k : K) + 1) * ((k : K) - 3)) *
        ∑ m : Fin (k - 3), cW g2 g3 (m.val + 2) * cW g2 g3 (k - (m.val + 2))
    else 0 := by
  unfold cW
  rw [Nat.strongRecOn_eq]
  split_ifs <;> rfl

/- English proof (translation)
Rewrite using `[cW_eq]`. Simplify using the standard rewrite rules.
-/
theorem cW_one (g2 g3 : K) : cW g2 g3 1 = 0 := by rw [cW_eq]; simp
/- English proof (translation)
Rewrite using `[cW_eq]`. Simplify using the standard rewrite rules.
-/
theorem cW_two (g2 g3 : K) : cW g2 g3 2 = g2 / 20 := by rw [cW_eq]; simp
/- English proof (translation)
Rewrite using `[cW_eq]`. Simplify using the standard rewrite rules.
-/
theorem cW_three (g2 g3 : K) : cW g2 g3 3 = g3 / 28 := by rw [cW_eq]; simp

/- English proof (translation)
Rewrite using `[cW_eq, if_neg (by omega), if_neg (by omega), if_pos (by omega)]`. Use `congr 1`. Rewrite using `[Fin.sum_univ_eq_sum_range (fun j => cW g2 g3 (j + 2) * cW g2 g3 (m + 2 - (j + 2))) (m + 2 - 3)]`. Take `⟨t, rfl⟩ : ∃ t, m = t + 1` from `⟨m - 1, by omega⟩`. Rewrite using `[Finset.sum_range_succ, Finset.sum_range_succ']`.

Simplify using `only [Nat.sub_self, zero_add, cW_one, mul_zero, zero_mul, add_zero]`. Establish `: t + 1 + 2 - 3 = t` using `by omega`. Rewrite using `[this]`. Use `Finset.sum_congr rfl fun j hj => ?_` and prove the remaining obligations. Establish `hj'` using `Finset.mem_range.mp hj`.

Use `congr 2`. Use linear arithmetic over natural numbers and integers.
-/
theorem cW_rec (g2 g3 : K) (m : ℕ) (hm : 2 ≤ m) : cW g2 g3 (m + 2) =
    3 / ((2 * ((m + 2 : ℕ) : K) + 1) * (((m + 2 : ℕ) : K) - 3)) *
      ∑ a ∈ Finset.range (m + 1), cW g2 g3 (a + 1) * cW g2 g3 (m - a + 1) := by
  rw [cW_eq, if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  congr 1
  rw [Fin.sum_univ_eq_sum_range (fun j => cW g2 g3 (j + 2) * cW g2 g3 (m + 2 - (j + 2))) (m + 2 - 3)]
  obtain ⟨t, rfl⟩ : ∃ t, m = t + 1 := ⟨m - 1, by omega⟩
  rw [Finset.sum_range_succ, Finset.sum_range_succ']
  simp only [Nat.sub_self, zero_add, cW_one, mul_zero, zero_mul, add_zero]
  have : t + 1 + 2 - 3 = t := by omega
  rw [this]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.mp hj
  congr 2
  omega

/- English proof (translation)
Unfold `pOf wpNum`. Rewrite using `[coeff_mk, coeff_mk, if_neg (by omega)]`. Establish `h1 : Even (n + 2) ↔ Even n` using `by simp [Nat.even_add]`. Establish `h2 : (n + 2) / 2 = n / 2 + 1` using `by omega`. Simplify using `only [h1, h2]`.
-/
theorem coeff_pOf (g2 g3 : K) (n : ℕ) :
    coeff n (pOf g2 g3) = if Even n then cW g2 g3 (n / 2 + 1) else 0 := by
  unfold pOf wpNum
  rw [coeff_mk, coeff_mk, if_neg (by omega)]
  have h1 : Even (n + 2) ↔ Even n := by simp [Nat.even_add]
  have h2 : (n + 2) / 2 = n / 2 + 1 := by omega
  simp only [h1, h2]

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simp`. Consider the case `succ m ih`. Establish `: 2 * (m + 1) + 1 = 2 * m + 1 + 1 + 1` using `by ring`. Rewrite using `[this, Finset.sum_range_succ, Finset.sum_range_succ, ih, Finset.sum_range_succ _ (m + 1)]`.

Establish `e1 : ¬ Even (2 * m + 1)` using `by simp`. Establish `e2 : Even (2 * m + 1 + 1)` using `⟨m + 1, by ring⟩`. Establish `e3 : (2 * m + 1 + 1) / 2 = m + 1` using `by omega`. Rewrite using `[if_neg e1, if_pos e2, e3, add_zero]`.
-/
theorem sum_even_range (F : ℕ → K) (m : ℕ) :
    ∑ i ∈ Finset.range (2 * m + 1), (if Even i then F (i / 2) else 0)
      = ∑ a ∈ Finset.range (m + 1), F a := by
  induction m with
  | zero => simp
  | succ m ih =>
    have : 2 * (m + 1) + 1 = 2 * m + 1 + 1 + 1 := by ring
    rw [this, Finset.sum_range_succ, Finset.sum_range_succ, ih, Finset.sum_range_succ _ (m + 1)]
    have e1 : ¬ Even (2 * m + 1) := by simp
    have e2 : Even (2 * m + 1 + 1) := ⟨m + 1, by ring⟩
    have e3 : (2 * m + 1 + 1) / 2 = m + 1 := by omega
    rw [if_neg e1, if_pos e2, e3, add_zero]

/- English proof (translation)
Rewrite using `[sq, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, ← sum_even_range (fun a => cW g2 g3 (a + 1) * cW g2 g3 (m - a + 1))]`. Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations. Establish `hi'` using `Finset.mem_range.mp hi`. Simplify using `only [coeff_pOf]`. Distinguish the cases in `he : Even i`.

Establish `he' : Even (2 * m - i)`. Take `⟨a, rfl⟩` from `he`. Conclude with `⟨m - a, by omega⟩`. Establish `: (2 * m - i) / 2 = m - i / 2`. Take `⟨a, rfl⟩` from `he`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[if_pos he, if_pos he', if_pos he, this]`. Rewrite using `[if_neg he, if_neg he, zero_mul]`.
-/
theorem coeff_pOf_sq_even (g2 g3 : K) (m : ℕ) :
    coeff (2 * m) (pOf g2 g3 ^ 2)
      = ∑ a ∈ Finset.range (m + 1), cW g2 g3 (a + 1) * cW g2 g3 (m - a + 1) := by
  rw [sq, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    ← sum_even_range (fun a => cW g2 g3 (a + 1) * cW g2 g3 (m - a + 1))]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.mp hi
  simp only [coeff_pOf]
  by_cases he : Even i
  · have he' : Even (2 * m - i) := by
      obtain ⟨a, rfl⟩ := he
      exact ⟨m - a, by omega⟩
    have : (2 * m - i) / 2 = m - i / 2 := by
      obtain ⟨a, rfl⟩ := he
      omega
    rw [if_pos he, if_pos he', if_pos he, this]
  · rw [if_neg he, if_neg he, zero_mul]

/- English proof (translation)
Rewrite using `[sq, coeff_mul]`. Use `Finset.sum_eq_zero fun p hp => ?_` and prove the remaining obligations. Establish `hp'` using `Finset.HasAntidiagonal.mem_antidiagonal.mp hp`. Simplify using `only [coeff_pOf]`. Distinguish the cases in `he : Even p.1`.

Establish `: ¬ Even p.2` using `fun h2 => hn (hp' ▸ he.add h2)`. Rewrite using `[if_neg this, mul_zero]`. Rewrite using `[if_neg he, zero_mul]`.
-/
theorem coeff_pOf_sq_odd (g2 g3 : K) (n : ℕ) (hn : ¬ Even n) :
    coeff n (pOf g2 g3 ^ 2) = 0 := by
  rw [sq, coeff_mul]
  refine Finset.sum_eq_zero fun p hp => ?_
  have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  simp only [coeff_pOf]
  by_cases he : Even p.1
  · have : ¬ Even p.2 := fun h2 => hn (hp' ▸ he.add h2)
    rw [if_neg this, mul_zero]
  · rw [if_neg he, zero_mul]

section CharZero
variable [CharZero K]

/- English proof (translation)
Use extensionality with `n`. Establish `h12 : (12 : PowerSeries K) = C (12 : K)` using `(map_ofNat C 12).symm`. Establish `h6 : (6 : PowerSeries K) = C (6 : K)` using `(map_ofNat C 6).symm`. Rewrite using `[h12, h6]`. Simplify using `only [map_add, map_sub, coeff_C_mul, coeff_X_pow_mul', coeff_X_pow]`.

Distinguish the cases in `hn : 2 ≤ n`. Take `⟨j, rfl⟩ : ∃ j, n = j + 2` from `⟨n - 2, by omega⟩`. Simplify using `only [if_pos hn, Nat.add_sub_cancel, coeff_derivative]`. Distinguish the cases in `he : Even j`. Choose the witnesses or unpack the hypotheses as in `⟨m, rfl⟩ : ∃ m, j = 2 * m := by`.

Take `⟨a, rfl⟩` from `he`. Conclude with `⟨a, by ring⟩`. Rewrite using `[coeff_pOf_sq_even, coeff_pOf, if_pos (by simp [Nat.even_add])]`. Establish `e : (2 * m + 1 + 1) / 2 + 1 = m + 2` using `by omega`. Establish `e' : (2 * m + 2) / 2 + 1 = m + 2` using `by omega`.

Rewrite using `[e]`. Break down `m with _ | _ | m` into its components or cases. Simplify using `[cW_one, cW_two]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `[Finset.sum_range_succ, cW_one]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[cW_rec g2 g3 (m + 2) (by omega), if_neg (by omega)] set S := ∑ a ∈ Finset.range (m + 2 + 1), cW g2 g3 (a + 1) * cW g2 g3 (m + 2 - a + 1)`. Establish `h1 : (2 * ((m + 2 + 2 : ℕ) : K) + 1) ≠ 0`. Establish `: (2 * ((m + 2 + 2 : ℕ) : K) + 1) = ((2 * (m + 2 + 2) + 1 : ℕ) : K)` using `by push_cast; ring`. Rewrite using `[this]; exact Nat.cast_ne_zero.mpr (by omega)`.

Establish `h2 : (((m + 2 + 2 : ℕ) : K) - 3) ≠ 0`. Establish `: (((m + 2 + 2 : ℕ) : K) - 3) = ((m + 1 : ℕ) : K)` using `by push_cast; ring`. Rewrite using `[this]; exact Nat.cast_ne_zero.mpr (by omega)`. Clear the denominators using the available nonvanishing facts. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `he2 : ¬ Even (j + 2)` using `by simpa [Nat.even_add] using he`. Rewrite using `[coeff_pOf_sq_odd _ _ _ he, coeff_pOf, if_neg he2, if_neg (by`. Introduce and unpack `h; apply he; have : j = 0 := by omega`. Simplify using `[this])]`.

Simplify using the standard rewrite rules. Rewrite using `[if_neg hn, if_neg hn, if_neg (by omega), coeff_pOf]`. Establish `: n = 0 ∨ n = 1` using `by omega`. Apply the tactic sequence `rcases this with rfl | rfl <;> simp [cW_one]`.
-/
theorem second_order (g2 g3 : K) :
    X ^ 2 * derivative K (derivative K (pOf g2 g3))
      = 12 * pOf g2 g3 + 6 * (X ^ 2 * pOf g2 g3 ^ 2) - C (g2 / 2) * X ^ 2 := by
  ext n
  have h12 : (12 : PowerSeries K) = C (12 : K) := (map_ofNat C 12).symm
  have h6 : (6 : PowerSeries K) = C (6 : K) := (map_ofNat C 6).symm
  rw [h12, h6]
  simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow_mul', coeff_X_pow]
  by_cases hn : 2 ≤ n
  · obtain ⟨j, rfl⟩ : ∃ j, n = j + 2 := ⟨n - 2, by omega⟩
    simp only [if_pos hn, Nat.add_sub_cancel, coeff_derivative]
    by_cases he : Even j
    · obtain ⟨m, rfl⟩ : ∃ m, j = 2 * m := by
        obtain ⟨a, rfl⟩ := he
        exact ⟨a, by ring⟩
      rw [coeff_pOf_sq_even, coeff_pOf, if_pos (by simp [Nat.even_add])]
      have e : (2 * m + 1 + 1) / 2 + 1 = m + 2 := by omega
      have e' : (2 * m + 2) / 2 + 1 = m + 2 := by omega
      rw [e]
      rcases m with _ | _ | m
      · simp [cW_one, cW_two]; ring
      · simp [Finset.sum_range_succ, cW_one]; ring
      · rw [cW_rec g2 g3 (m + 2) (by omega), if_neg (by omega)]
        set S := ∑ a ∈ Finset.range (m + 2 + 1), cW g2 g3 (a + 1) * cW g2 g3 (m + 2 - a + 1)
        have h1 : (2 * ((m + 2 + 2 : ℕ) : K) + 1) ≠ 0 := by
          have : (2 * ((m + 2 + 2 : ℕ) : K) + 1) = ((2 * (m + 2 + 2) + 1 : ℕ) : K) := by push_cast; ring
          rw [this]; exact Nat.cast_ne_zero.mpr (by omega)
        have h2 : (((m + 2 + 2 : ℕ) : K) - 3) ≠ 0 := by
          have : (((m + 2 + 2 : ℕ) : K) - 3) = ((m + 1 : ℕ) : K) := by push_cast; ring
          rw [this]; exact Nat.cast_ne_zero.mpr (by omega)
        field_simp
        push_cast
        ring
    · have he2 : ¬ Even (j + 2) := by simpa [Nat.even_add] using he
      rw [coeff_pOf_sq_odd _ _ _ he, coeff_pOf, if_neg he2, if_neg (by
        rintro h; apply he; have : j = 0 := by omega
        simp [this])]
      simp
  · rw [if_neg hn, if_neg hn, if_neg (by omega), coeff_pOf]
    have : n = 0 ∨ n = 1 := by omega
    rcases this with rfl | rfl <;> simp [cW_one]

end CharZero

section CharZero2
variable [CharZero K]

def defect (g2 g3 : K) (P : PowerSeries K) : PowerSeries K :=
  (-2 + X ^ 3 * derivative K P) ^ 2 - 4 * (1 + X ^ 2 * P) ^ 3
    + C g2 * X ^ 4 * (1 + X ^ 2 * P) + C g3 * X ^ 6

/- English proof (translation)
Establish `h4 : (4 : PowerSeries K) = C (4 : K)` using `(map_ofNat C 4).symm`. Establish `h2 : (2 : PowerSeries K) = C (2 : K)` using `(map_ofNat C 2).symm`. Unfold `defect`. Simplify using `only [map_add, map_sub, map_neg, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, derivative_X, derivative_C, h4, h2, Derivation.map_one_eq_zero]`. Rewrite using `[← h4, ← h2]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem deriv_defect (g2 g3 : K) (P : PowerSeries K) :
    derivative K (defect g2 g3 P) =
      2 * (-2 + X ^ 3 * derivative K P) * (3 * X ^ 2 * derivative K P
          + X ^ 3 * derivative K (derivative K P))
        - 12 * (1 + X ^ 2 * P) ^ 2 * (2 * X * P + X ^ 2 * derivative K P)
        + C g2 * (4 * X ^ 3 * (1 + X ^ 2 * P) + X ^ 4 * (2 * X * P + X ^ 2 * derivative K P))
        + C g3 * (6 * X ^ 5) := by
  have h4 : (4 : PowerSeries K) = C (4 : K) := (map_ofNat C 4).symm
  have h2 : (2 : PowerSeries K) = C (2 : K) := (map_ofNat C 2).symm
  unfold defect
  simp only [map_add, map_sub, map_neg, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul,
    derivative_X, derivative_C, h4, h2, Derivation.map_one_eq_zero]
  rw [← h4, ← h2]
  ring

/- English proof (translation)
Establish `h2 : (2 : PowerSeries K) = C (2 : K)` using `(map_ofNat C 2).symm`. Establish `hg : C g2 = 2 * C (g2 / 2)`. Rewrite using `[h2, ← map_mul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Establish `h` using `second_order g2 g3`. Rewrite using `[deriv_defect]`. Unfold `defect`. Rewrite using `[hg]`. Take the linear combination `2 * (-2 + X ^ 3 * derivative K (pOf g2 g3)) * X ^ 2 * h`.
-/
theorem euler_defect (g2 g3 : K) :
    X * derivative K (defect g2 g3 (pOf g2 g3)) = 6 * defect g2 g3 (pOf g2 g3) := by
  have h2 : (2 : PowerSeries K) = C (2 : K) := (map_ofNat C 2).symm
  have hg : C g2 = 2 * C (g2 / 2) := by
    rw [h2, ← map_mul]; congr 1; ring
  have h := second_order g2 g3
  rw [deriv_defect]
  unfold defect
  rw [hg]
  linear_combination 2 * (-2 + X ^ 3 * derivative K (pOf g2 g3)) * X ^ 2 * h

/- English proof (translation)
Break down `n with _ | n` into its components or cases. Simplify using the standard rewrite rules. Rewrite using `[coeff_succ_X_mul, coeff_derivative]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem coeff_X_mul_derivative (f : PowerSeries K) (n : ℕ) :
    coeff n (X * derivative K f) = (n : K) * coeff n f := by
  rcases n with _ | n
  · simp
  · rw [coeff_succ_X_mul, coeff_derivative]; push_cast; ring

/- English proof (translation)
Use extensionality with `n`. Simplify using `only [map_add, coeff_C_mul, coeff_X_pow_mul', coeff_X_pow, coeff_mk]`. Break down `n with _ | _ | _ | _ | _ | _ | n` into its components or cases. Simplify using `[coeff_pOf, cW_one]`. Simplify using `[coeff_pOf]`.

Simplify using `[coeff_pOf, cW_two]`. Simplify using `[coeff_pOf]; exact fun h => absurd h (by decide)`. Simplify using `[coeff_pOf, cW_three]; exact fun h => absurd h (by decide)`. Simplify using `[coeff_pOf]; exact fun h => absurd h (by decide)`. Simplify using the standard rewrite rules.
-/
theorem pOf_split (g2 g3 : K) :
    pOf g2 g3 = C (g2 / 20) * X ^ 2 + C (g3 / 28) * X ^ 4
      + X ^ 6 * PowerSeries.mk fun n => coeff (n + 6) (pOf g2 g3) := by
  ext n
  simp only [map_add, coeff_C_mul, coeff_X_pow_mul', coeff_X_pow, coeff_mk]
  rcases n with _ | _ | _ | _ | _ | _ | n
  · simp [coeff_pOf, cW_one]
  · simp [coeff_pOf]
  · simp [coeff_pOf, cW_two]
  · simp [coeff_pOf]; exact fun h => absurd h (by decide)
  · simp [coeff_pOf, cW_three]; exact fun h => absurd h (by decide)
  · simp [coeff_pOf]; exact fun h => absurd h (by decide)
  · simp

/- English proof (translation)
Use `set T : PowerSeries K := PowerSeries.mk fun n => coeff (n + 6) (pOf g2 g3) with hT`. Establish `hP` using `pOf_split g2 g3`. Rewrite `hP` using `[← hT]`. Establish `h20 : (20 : PowerSeries K) = C (20 : K)` using `(map_ofNat C 20).symm`. Establish `h28 : (28 : PowerSeries K) = C (28 : K)` using `(map_ofNat C 28).symm`.

Establish `hg2 : C g2 = 20 * C (g2 / 20)`. Rewrite using `[h20, ← map_mul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `hg3 : C g3 = 28 * C (g3 / 28)`.

Rewrite using `[h28, ← map_mul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Use `set c2 : PowerSeries K := C (g2 / 20) with hc2`. Use `set c3 : PowerSeries K := C (g3 / 28) with hc3`.

Establish `hd : derivative K (pOf g2 g3) = X * (2 * c2 + 4 * c3 * X ^ 2 + 6 * X ^ 4 * T + X ^ 5 * derivative K T)`. Rewrite using `[hP, hc2, hc3]`. Simplify using `only [map_add, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, derivative_X, derivative_C]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨-4 * (6 * T + X * derivative K T) - 12 * T + (2 * c2 + 4 * c3 * X ^ 2 + 6 * X ^ 4 * T + X ^ 5 * derivative K T) ^ 2 - 12 * (c2 + c3 * X ^ 2 + X ^ 4 * T) ^ 2 - 4 * X ^ 4 * (c2 + c3 * X ^ 2 + X ^ 4 * T) ^ 3 + 20 * c2 * (c2 + c3 * X ^ 2 + X ^ 4 * T), ?_⟩` and prove the remaining obligations.

Unfold `defect`. Rewrite using `[hd, hg2, hg3]`. Generalize the expression as in `derivative K T = T' at *`. Rewrite using `[hP]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem defect_split (g2 g3 : K) : ∃ S : PowerSeries K, defect g2 g3 (pOf g2 g3) = X ^ 8 * S := by
  set T : PowerSeries K := PowerSeries.mk fun n => coeff (n + 6) (pOf g2 g3) with hT
  have hP := pOf_split g2 g3
  rw [← hT] at hP
  have h20 : (20 : PowerSeries K) = C (20 : K) := (map_ofNat C 20).symm
  have h28 : (28 : PowerSeries K) = C (28 : K) := (map_ofNat C 28).symm
  have hg2 : C g2 = 20 * C (g2 / 20) := by
    rw [h20, ← map_mul]; congr 1; ring
  have hg3 : C g3 = 28 * C (g3 / 28) := by
    rw [h28, ← map_mul]; congr 1; ring
  set c2 : PowerSeries K := C (g2 / 20) with hc2
  set c3 : PowerSeries K := C (g3 / 28) with hc3
  have hd : derivative K (pOf g2 g3)
      = X * (2 * c2 + 4 * c3 * X ^ 2 + 6 * X ^ 4 * T + X ^ 5 * derivative K T) := by
    rw [hP, hc2, hc3]
    simp only [map_add, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul,
      derivative_X, derivative_C]
    ring
  refine ⟨-4 * (6 * T + X * derivative K T) - 12 * T
    + (2 * c2 + 4 * c3 * X ^ 2 + 6 * X ^ 4 * T + X ^ 5 * derivative K T) ^ 2
    - 12 * (c2 + c3 * X ^ 2 + X ^ 4 * T) ^ 2 - 4 * X ^ 4 * (c2 + c3 * X ^ 2 + X ^ 4 * T) ^ 3
    + 20 * c2 * (c2 + c3 * X ^ 2 + X ^ 4 * T), ?_⟩
  unfold defect
  rw [hd, hg2, hg3]
  generalize derivative K T = T' at *
  rw [hP]
  ring

/- English proof (translation)
Use extensionality with `n`. Rewrite using `[map_zero]`. Distinguish the cases in `hn : n = 6`. Take `⟨S, hS⟩` from `defect_split g2 g3`. Rewrite using `[hS, hn, coeff_X_pow_mul', if_neg (by omega)]`.

Establish `h` using `congrArg (coeff n) (euler_defect g2 g3)`. Establish `h6 : (6 : PowerSeries K) = C (6 : K)` using `(map_ofNat C 6).symm`. Rewrite `h` using `[coeff_X_mul_derivative, h6, coeff_C_mul]`. Establish `h' : ((n : K) - 6) * coeff n (defect g2 g3 (pOf g2 g3)) = 0` using `by linear_combination h`. Break down `mul_eq_zero.mp h' with h0 | h0` into its components or cases.

It suffices to derive a contradiction. Apply `hn` to reduce the goal to its premises. Establish `: (n : K) = ((6 : ℕ) : K)` using `by push_cast; linear_combination h0`. Conclude with `Nat.cast_injective this`. Conclude with `h0`.
-/
theorem defect_eq_zero (g2 g3 : K) : defect g2 g3 (pOf g2 g3) = 0 := by
  ext n
  rw [map_zero]
  by_cases hn : n = 6
  · obtain ⟨S, hS⟩ := defect_split g2 g3
    rw [hS, hn, coeff_X_pow_mul', if_neg (by omega)]
  · have h := congrArg (coeff n) (euler_defect g2 g3)
    have h6 : (6 : PowerSeries K) = C (6 : K) := (map_ofNat C 6).symm
    rw [coeff_X_mul_derivative, h6, coeff_C_mul] at h
    have h' : ((n : K) - 6) * coeff n (defect g2 g3 (pOf g2 g3)) = 0 := by linear_combination h
    rcases mul_eq_zero.mp h' with h0 | h0
    · exfalso; apply hn
      have : (n : K) = ((6 : ℕ) : K) := by push_cast; linear_combination h0
      exact Nat.cast_injective this
    · exact h0

end CharZero2

end Formalism.L2.Th1.F.POf

namespace Formalism.L2.Th1.F
open POf

/- English proof (translation)
Introduce `K _ _ g2 g3`. Prove the components needed by the constructor for the conclusion. Use extensionality with `n`. Rewrite using `[map_add, coeff_X_pow_mul', coeff_one]`. Break down `n with _ | _ | n` into its components or cases.

Simplify using `[wpNum]`. Simplify using `[wpNum]`. Rewrite using `[if_neg (by omega), if_pos (by omega), zero_add, show n + 1 + 1 - 2 = n from rfl]`. Simplify using `[pOf]`. Use extensionality with `n`.

Rewrite using `[map_sub, mul_assoc, coeff_C_mul, coeff_X_pow_mul', coeff_one]`. Break down `n with _ | _ | _ | n` into its components or cases. Simplify using `[wpDen]`. Simplify using `[wpDen]`. Simplify using `[wpDen]`.

Rewrite using `[if_neg (by omega), if_pos (by omega), show n + 1 + 1 + 1 - 3 = n from rfl, coeff_derivative, coeff_pOf]`. Unfold `wpDen`. Rewrite using `[coeff_mk, if_neg (by omega)]`. Establish `e1 : Even (n + 1 + 1 + 1) ↔ Even (n + 1)` using `by simp [Nat.even_add]`. Simplify using `only [e1]`.

Distinguish the cases in `he : Even (n + 1)`. Rewrite using `[if_pos he, if_pos he]`. Take `⟨a, ha⟩` from `he`. Establish `e2 : (n + 1 + 1 + 1) / 2 = a + 1` using `by omega`. Establish `e3 : (n + 1) / 2 + 1 = a + 1` using `by omega`.

Establish `e4 : (n : K) + 1 = 2 * a`. Establish `: ((n + 1 : ℕ) : K) = ((a + a : ℕ) : K)` using `by rw [ha]`. Move the coercions through the operations in `at this`. Take the linear combination `this`. Rewrite using `[e2, e3, e4]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[if_neg he, if_neg he]`. Simplify using the standard rewrite rules.
-/
theorem weierstrass_numerator_denominator : WpNumDen := by
  intro K _ _ g2 g3
  constructor
  · ext n
    rw [map_add, coeff_X_pow_mul', coeff_one]
    rcases n with _ | _ | n
    · simp [wpNum]
    · simp [wpNum]
    · rw [if_neg (by omega), if_pos (by omega), zero_add, show n + 1 + 1 - 2 = n from rfl]
      simp [pOf]
  · ext n
    rw [map_sub, mul_assoc, coeff_C_mul, coeff_X_pow_mul', coeff_one]
    rcases n with _ | _ | _ | n
    · simp [wpDen]
    · simp [wpDen]
    · simp [wpDen]
    · rw [if_neg (by omega), if_pos (by omega), show n + 1 + 1 + 1 - 3 = n from rfl, coeff_derivative, coeff_pOf]
      unfold wpDen
      rw [coeff_mk, if_neg (by omega)]
      have e1 : Even (n + 1 + 1 + 1) ↔ Even (n + 1) := by simp [Nat.even_add]
      simp only [e1]
      by_cases he : Even (n + 1)
      · rw [if_pos he, if_pos he]
        obtain ⟨a, ha⟩ := he
        have e2 : (n + 1 + 1 + 1) / 2 = a + 1 := by omega
        have e3 : (n + 1) / 2 + 1 = a + 1 := by omega
        have e4 : (n : K) + 1 = 2 * a := by
          have : ((n + 1 : ℕ) : K) = ((a + a : ℕ) : K) := by rw [ha]
          push_cast at this; linear_combination this
        rw [e2, e3, e4]
        push_cast
        ring
      · rw [if_neg he, if_neg he]; simp

/- English proof (translation)
Introduce `K _ _ g2 g3`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← coeff_zero_eq_constantCoeff_apply, coeff_pOf]`. Simplify using `[cW_one]`. Introduce `n hn`.

Rewrite using `[coeff_pOf, if_neg (Nat.not_even_iff_odd.mpr hn)]`. Establish `h` using `defect_eq_zero g2 g3`. Unfold `defect at h`. Unfold `Formalism.L2.Th1.B.dz`. Take the linear combination `h`.
-/
theorem weierstrass_p_of_series : POfIsWp := by
  intro K _ _ g2 g3
  refine ⟨?_, ?_, ?_⟩
  · rw [← coeff_zero_eq_constantCoeff_apply, coeff_pOf]; simp [cW_one]
  · intro n hn
    rw [coeff_pOf, if_neg (Nat.not_even_iff_odd.mpr hn)]
  · have h := defect_eq_zero g2 g3
    unfold defect at h
    unfold Formalism.L2.Th1.B.dz
    linear_combination h

/- English proof (translation)
Introduce `L` and use `hu ℂ L.g₂ L.g₃ _ _ (h L) (hp ℂ L.g₂ L.g₃)`.
-/
theorem pOfLattice_of (h : TaylorIsWp) (hu : IsWpUnique) (hp : POfIsWp) : POfLattice :=
  fun L => hu ℂ L.g₂ L.g₃ _ _ (h L) (hp ℂ L.g₂ L.g₃)

/- English proof (translation)
The claim follows from `pOfLattice_of (taylorIsWp_of taylor_ring taylor_deriv) weierstrass_series_unique weierstrass_p_of_series`.
-/
theorem weierstrass_p_of_lattice : POfLattice :=
  pOfLattice_of (taylorIsWp_of taylor_ring taylor_deriv) weierstrass_series_unique weierstrass_p_of_series

end Formalism.L2.Th1.F
