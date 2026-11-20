import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.IsHolVOf

noncomputable section

open NumberField IsDedekindDomain UpperTheory.V.Sd.Wc
open scoped NNReal

namespace UpperTheory.Esk.NormOneUnitsLemmas

/- English proof (translation)
Rewrite using `[← geom_sum_mul, Valuation.map_mul]`. Use `mul_le_of_le_one_left zero_le ?_` and prove the remaining obligations. Use `Valuation.map_sum_le _ fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Valuation.map_pow]`. Conclude with `pow_le_one₀ zero_le hb`.
-/
theorem pow_sub (ν : Valuation ℂ ℝ≥0) {b : ℂ} (hb : ν b ≤ 1) (m : ℕ) : ν (b ^ m - 1) ≤ ν (b - 1) := by
  rw [← geom_sum_mul, Valuation.map_mul]
  refine mul_le_of_le_one_left zero_le ?_
  refine Valuation.map_sum_le _ fun i _ => ?_
  rw [Valuation.map_pow]
  exact pow_le_one₀ zero_le hb

/- English proof (translation)
Rewrite using `[← geom_sum_mul, Valuation.map_mul]`. Use `mul_le_mul_of_nonneg_right ?_ zero_le` and prove the remaining obligations. Establish `e : ∑ i ∈ Finset.range l, b ^ i = ∑ i ∈ Finset.range l, (b ^ i - 1) + (l : ℂ)`. Rewrite using `[Finset.sum_sub_distrib]`. Simplify using the standard rewrite rules.

Rewrite using `[e]`. Use `(Valuation.map_add _ _ _).trans (max_le ?_ le_rfl)` and prove the remaining obligations. Conclude with `Valuation.map_sum_le _ fun i _ => (pow_sub ν hb i).trans hbp`.
-/
theorem pow_l (ν : Valuation ℂ ℝ≥0) (l : ℕ) {b : ℂ} (hb : ν b ≤ 1) (hbp : ν (b - 1) ≤ ν (l : ℂ)) :
    ν (b ^ l - 1) ≤ ν (l : ℂ) * ν (b - 1) := by
  rw [← geom_sum_mul, Valuation.map_mul]
  refine mul_le_mul_of_nonneg_right ?_ zero_le
  have e : ∑ i ∈ Finset.range l, b ^ i = ∑ i ∈ Finset.range l, (b ^ i - 1) + (l : ℂ) := by
    rw [Finset.sum_sub_distrib]; simp
  rw [e]
  refine (Valuation.map_add _ _ _).trans (max_le ?_ le_rfl)
  exact Valuation.map_sum_le _ fun i _ => (pow_sub ν hb i).trans hbp

/- English proof (translation)
The claim follows from `| 0 => by simp | N + 1 => by have hb' : ν (b ^ (l ^ N)) ≤ 1 := by rw [Valuation.map_pow]; exact pow_le_one₀ zero_le hb have e : b ^ (l ^ (N + 1)) = (b ^ (l ^ N)) ^ l := by rw [pow_succ, pow_mul] rw [e] refine (pow_l ν l hb' ((pow_sub ν hb _).trans hbp)).trans ?_ calc ν (l : ℂ) * …`.
-/
theorem pow_lN (ν : Valuation ℂ ℝ≥0) (l : ℕ) {b : ℂ} (hb : ν b ≤ 1) (hbp : ν (b - 1) ≤ ν (l : ℂ)) :
    ∀ N : ℕ, ν (b ^ (l ^ N) - 1) ≤ ν (l : ℂ) ^ N * ν (b - 1)
  | 0 => by simp
  | N + 1 => by
    have hb' : ν (b ^ (l ^ N)) ≤ 1 := by rw [Valuation.map_pow]; exact pow_le_one₀ zero_le hb
    have e : b ^ (l ^ (N + 1)) = (b ^ (l ^ N)) ^ l := by rw [pow_succ, pow_mul]
    rw [e]
    refine (pow_l ν l hb' ((pow_sub ν hb _).trans hbp)).trans ?_
    calc ν (l : ℂ) * ν (b ^ (l ^ N) - 1) ≤ ν (l : ℂ) * (ν (l : ℂ) ^ N * ν (b - 1)) :=
          mul_le_mul_of_nonneg_left (pow_lN ν l hb hbp N) zero_le
      _ = ν (l : ℂ) ^ (N + 1) * ν (b - 1) := by ring

/- English proof (translation)
Distinguish the cases in `h0 : a = 0`. Rewrite using `[h0]`. Conclude with `zero_le`. Rewrite `h`, the goal using `[← WithZero.exp_log h0]`. Rewrite `h` using `[← WithZero.exp_zero, WithZero.exp_lt_exp]`.

Rewrite using `[WithZero.exp_le_exp]`. Use linear arithmetic over natural numbers and integers.
-/
theorem lt_one_le (a : WithZero (Multiplicative ℤ)) (h : a < 1) : a ≤ WithZero.exp (-1 : ℤ) := by
  by_cases h0 : a = 0
  · rw [h0]; exact zero_le
  · rw [← WithZero.exp_log h0] at h ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h
    rw [WithZero.exp_le_exp]
    omega

end UpperTheory.Esk.NormOneUnitsLemmas

open UpperTheory.Esk.NormOneUnitsLemmas in
/- English proof (translation)
Introduce `F _ _ l _ ι D v x hx N t ht`. Take `⟨m, rfl⟩` from `ht`. Use `set L : (D.pl v).adicCompletion F := ((l : ℕ) : (D.pl v).adicCompletion F) with hL`. Establish `hLv : Valued.v L = WithZero.exp (-1 : ℤ)` using `D.unif v`. Establish `hL0 : L ≠ 0` using `fun h => by rw [h, map_zero] at hLv; exact WithZero.exp_ne_zero hLv.symm`.

Establish `hemL : D.em v L = (l : ℂ)` using `map_natCast _ l`. Establish `hxle : nu ι (D.em v x) ≤ 1` using `(D.le v x).2 hx.le`. Use `set y := x ^ (l - 1) - 1 with hy`. Establish `hemy : D.em v y = D.em v x ^ (l - 1) - 1` using `by rw [hy, map_sub, map_pow, map_one]`. Establish `hylt : Valued.v y < 1` using `(D.lt v y).1 (by rw [hemy]; exact D.res v x hx)`.

Establish `hyL : Valued.v (y / L) ≤ 1`. Rewrite using `[map_div₀, hLv, div_le_one₀ (by simp)]`. Conclude with `lt_one_le _ hylt`. Establish `hnuy : nu ι (D.em v y) ≤ nu ι (l : ℂ)`. Establish `e : y = L * (y / L)` using `by field_simp`.

Rewrite using `[e, map_mul, map_mul, hemL]`. Conclude with `mul_le_of_le_one_right zero_le ((D.le v _).2 hyL)`. Rewrite `hnuy` using `[hemy]`. Use `set a := D.em v x ^ (l - 1) with ha`. Establish `hale : nu ι a ≤ 1` using `by rw [ha, Valuation.map_pow]; exact pow_le_one₀ zero_le hxle`.

Establish `ha1 : nu ι (a - 1) ≤ 1` using `by rw [← hemy]; exact ((D.lt v y).2 hylt).le`. Establish `e : D.em v x ^ ((l - 1) * l ^ N * m) = (a ^ (l ^ N)) ^ m` using `by rw [ha, ← pow_mul, ← pow_mul, mul_assoc]`. Rewrite using `[e]`. Establish `hb : nu ι (a ^ (l ^ N)) ≤ 1` using `by rw [Valuation.map_pow]; exact pow_le_one₀ zero_le hale`. Use `(pow_sub _ hb m).trans ((pow_lN _ l hale hnuy N).trans ?_)` and prove the remaining obligations.

Conclude with `mul_le_of_le_one_right zero_le ha1`.
-/
theorem UpperTheory.Esk.pf_GUnit : UpperTheory.Esk.GUnit := by
  intro F _ _ l _ ι D v x hx N t ht
  obtain ⟨m, rfl⟩ := ht
  set L : (D.pl v).adicCompletion F := ((l : ℕ) : (D.pl v).adicCompletion F) with hL
  have hLv : Valued.v L = WithZero.exp (-1 : ℤ) := D.unif v
  have hL0 : L ≠ 0 := fun h => by rw [h, map_zero] at hLv; exact WithZero.exp_ne_zero hLv.symm
  have hemL : D.em v L = (l : ℂ) := map_natCast _ l
  have hxle : nu ι (D.em v x) ≤ 1 := (D.le v x).2 hx.le
  set y := x ^ (l - 1) - 1 with hy
  have hemy : D.em v y = D.em v x ^ (l - 1) - 1 := by rw [hy, map_sub, map_pow, map_one]
  have hylt : Valued.v y < 1 := (D.lt v y).1 (by rw [hemy]; exact D.res v x hx)
  have hyL : Valued.v (y / L) ≤ 1 := by
    rw [map_div₀, hLv, div_le_one₀ (by simp)]
    exact lt_one_le _ hylt
  have hnuy : nu ι (D.em v y) ≤ nu ι (l : ℂ) := by
    have e : y = L * (y / L) := by field_simp
    rw [e, map_mul, map_mul, hemL]
    exact mul_le_of_le_one_right zero_le ((D.le v _).2 hyL)
  rw [hemy] at hnuy
  set a := D.em v x ^ (l - 1) with ha
  have hale : nu ι a ≤ 1 := by rw [ha, Valuation.map_pow]; exact pow_le_one₀ zero_le hxle
  have ha1 : nu ι (a - 1) ≤ 1 := by rw [← hemy]; exact ((D.lt v y).2 hylt).le
  have e : D.em v x ^ ((l - 1) * l ^ N * m) = (a ^ (l ^ N)) ^ m := by rw [ha, ← pow_mul, ← pow_mul, mul_assoc]
  rw [e]
  have hb : nu ι (a ^ (l ^ N)) ≤ 1 := by rw [Valuation.map_pow]; exact pow_le_one₀ zero_le hale
  refine (pow_sub _ hb m).trans ((pow_lN _ l hale hnuy N).trans ?_)
  exact mul_le_of_le_one_right zero_le ha1
