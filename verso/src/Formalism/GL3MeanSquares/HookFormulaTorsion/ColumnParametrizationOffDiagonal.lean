import Mathlib
import Formalism.GL3MeanSquares.IntegralMultipleNormLowerBound

namespace Formalism.HermitianLattices.ExplicitEstimates

open Finset
open Formalism.HermitianLattices.TraceIntegrality
open Formalism.LogVandermondeBounds.flipTwoThree (hookF)

/- English proof (translation)
Establish `hi` using `i.isLt`. Use `Finset.prod_nbij' (fun j => (j : ℕ) - (i : ℕ) - 1) (fun t => if h : t + 1 + (i : ℕ) < N + 1 then (⟨t + 1 + (i : ℕ), h⟩ : Fin (N + 1)) else 0) ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `j hj`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_iff_val_lt_val] at hj`. Establish `hj2` using `j.isLt`.

Simplify using `only [Finset.mem_range]`. Use linear arithmetic over natural numbers and integers. Introduce `t ht`. Simplify using `only [Finset.mem_range] at ht`. Establish `h : t + 1 + (i : ℕ) < N + 1` using `by omega`.

Simplify using `only [dif_pos h, Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_iff_val_lt_val, Fin.val_mk]`. Use linear arithmetic over natural numbers and integers. Introduce `j hj`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_iff_val_lt_val] at hj`. Establish `hj2` using `j.isLt`.

Establish `h : (j : ℕ) - (i : ℕ) - 1 + 1 + (i : ℕ) < N + 1` using `by omega`. Simplify using `only [dif_pos h, Fin.ext_iff, Fin.val_mk]`. Use linear arithmetic over natural numbers and integers. Introduce `t ht`. Simplify using `only [Finset.mem_range] at ht`.

Establish `h : t + 1 + (i : ℕ) < N + 1` using `by omega`. Simplify using `only [dif_pos h, Fin.val_mk]`. Use linear arithmetic over natural numbers and integers. Introduce `j hj`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_iff_val_lt_val] at hj`.

Use `show g ((j : ℕ) - (i : ℕ)) = g ((j : ℕ) - (i : ℕ) - 1 + 1)`. Use `congr 1`. Use linear arithmetic over natural numbers and integers.
-/
private theorem g4w9_prod_gt (N : ℕ) (i : Fin (N + 1)) (g : ℕ → ℝ) :
    ∏ j ∈ univ.filter (fun j : Fin (N + 1) => i < j), g ((j : ℕ) - i)
      = ∏ t ∈ range (N - i), g (t + 1) := by
  have hi := i.isLt
  refine Finset.prod_nbij' (fun j => (j : ℕ) - (i : ℕ) - 1)
    (fun t => if h : t + 1 + (i : ℕ) < N + 1 then (⟨t + 1 + (i : ℕ), h⟩ : Fin (N + 1)) else 0)
    ?_ ?_ ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_iff_val_lt_val] at hj
    have hj2 := j.isLt
    simp only [Finset.mem_range]
    omega
  · intro t ht
    simp only [Finset.mem_range] at ht
    have h : t + 1 + (i : ℕ) < N + 1 := by omega
    simp only [dif_pos h, Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_iff_val_lt_val,
      Fin.val_mk]
    omega
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_iff_val_lt_val] at hj
    have hj2 := j.isLt
    have h : (j : ℕ) - (i : ℕ) - 1 + 1 + (i : ℕ) < N + 1 := by omega
    simp only [dif_pos h, Fin.ext_iff, Fin.val_mk]
    omega
  · intro t ht
    simp only [Finset.mem_range] at ht
    have h : t + 1 + (i : ℕ) < N + 1 := by omega
    simp only [dif_pos h, Fin.val_mk]
    omega
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_iff_val_lt_val] at hj
    show g ((j : ℕ) - (i : ℕ)) = g ((j : ℕ) - (i : ℕ) - 1 + 1)
    congr 1
    omega

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simp`. Consider the case `succ m ih`. Establish `e : a + (m + 1) = (a + m) + 1` using `by omega`. Rewrite using `[e, Nat.factorial_succ, Nat.cast_mul, ih, Finset.prod_range_succ]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem g4w9_fact_range (a m : ℕ) :
    ((a + m).factorial : ℝ) = (a.factorial : ℝ) * ∏ t ∈ range m, ((a : ℝ) + ((t + 1 : ℕ) : ℝ)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have e : a + (m + 1) = (a + m) + 1 := by omega
    rw [e, Nat.factorial_succ, Nat.cast_mul, ih, Finset.prod_range_succ]
    push_cast
    ring

/- English proof (translation)
Use `(Fin.sum_univ_eq_sum_range (fun i => N - i) (N + 1)).trans ?_` and prove the remaining obligations. Establish `h1 : ∑ i ∈ range (N + 1), (N - i) = ∑ j ∈ range (N + 1), (N + 1 - 1 - j)` using `Finset.sum_congr rfl (fun i _ => by omega)`. Establish `h2 : ∑ j ∈ range (N + 1), (N + 1 - 1 - j) = ∑ j ∈ range (N + 1), j` using `Finset.sum_range_reflect (fun i => i) (N + 1)`. Use `show ∑ i ∈ range (N + 1), (N - i) = _`. Rewrite using `[h1, h2, Finset.sum_range_id]`.

Simplify using the standard rewrite rules.
-/
private theorem g4w9_sum_count (N : ℕ) :
    ∑ i : Fin (N + 1), (N - (i : ℕ)) = (N + 1) * N / 2 := by
  refine (Fin.sum_univ_eq_sum_range (fun i => N - i) (N + 1)).trans ?_
  have h1 : ∑ i ∈ range (N + 1), (N - i) = ∑ j ∈ range (N + 1), (N + 1 - 1 - j) :=
    Finset.sum_congr rfl (fun i _ => by omega)
  have h2 : ∑ j ∈ range (N + 1), (N + 1 - 1 - j) = ∑ j ∈ range (N + 1), j :=
    Finset.sum_range_reflect (fun i => i) (N + 1)
  show ∑ i ∈ range (N + 1), (N - i) = _
  rw [h1, h2, Finset.sum_range_id]
  simp

/- English proof (translation)
Introduce `N nu hnu`. Unfold `hookF`. Establish `hd : ∀ i j : Fin (N + 1), i < j → (1:ℝ) ≤ ((((nu i : ℤ) - (nu j : ℤ) + ((j : ℕ) : ℤ) - ((i : ℕ) : ℤ)) : ℤ) : ℝ) ∧ ((((nu i : ℤ) - (nu j : ℤ) + ((j : ℕ) : ℤ) - ((i : ℕ) : ℤ)) : ℤ) : ℝ) ≤ (nu i : ℝ) + (((j : ℕ) - (i : ℕ) : ℕ) : ℝ)`. Introduce `i j hij`. Establish `h1` using `hnu (le_of_lt hij)`.

Establish `h2 : (i : ℕ) < j` using `Fin.lt_iff_val_lt_val.mp hij`. Prove the components needed by the constructor for the conclusion. Establish `h3 : (1:ℤ) ≤ (nu i : ℤ) - (nu j : ℤ) + ((j : ℕ) : ℤ) - ((i : ℕ) : ℤ)` using `by omega`. Conclude with `h3` after adjusting the coercions. Establish `h3 : (nu i : ℤ) - (nu j : ℤ) + ((j : ℕ) : ℤ) - ((i : ℕ) : ℤ) ≤ (nu i : ℤ) + (((j : ℕ) - (i : ℕ) : ℕ) : ℤ)` using `by omega`.

Conclude with `h3` after adjusting the coercions. Establish `hper : ∀ i : Fin (N + 1), ((nu i).factorial : ℝ) ≤ ((nu i + (N + 1) - 1 - (i : ℕ)).factorial : ℝ) / ∏ j ∈ univ.filter (fun j : Fin (N + 1) => i < j), ((((nu i : ℤ) - (nu j : ℤ) + ((j : ℕ) : ℤ) - ((i : ℕ) : ℤ)) : ℤ) : ℝ) ∧ ((nu i + (N + 1) - 1 - (i : ℕ)).factorial : ℝ) / ∏ j ∈ uni …`. Introduce `i`. Establish `hi` using `i.isLt`. Establish `e1 : nu i + (N + 1) - 1 - (i : ℕ) = nu i + (N - (i : ℕ))` using `by omega`.

Establish `hF : ((nu i + (N + 1) - 1 - (i : ℕ)).factorial : ℝ) = ((nu i).factorial : ℝ) * ∏ t ∈ range (N - (i : ℕ)), ((nu i : ℝ) + ((t + 1 : ℕ) : ℝ))`. Rewrite using `[e1]`. Conclude with `g4w9_fact_range (nu i) (N - (i : ℕ))`. Establish `hAle : ∏ j ∈ univ.filter (fun j : Fin (N + 1) => i < j), ((((nu i : ℤ) - (nu j : ℤ) + ((j : ℕ) : ℤ) - ((i : ℕ) : ℤ)) : ℤ) : ℝ) ≤ ∏ t ∈ range (N - (i : ℕ)), ((nu i : ℝ) + ((t + 1 : ℕ) : ℝ))`. Combine the equalities or inequalities in the displayed calculation.

Establish `hA1 : (1:ℝ) ≤ ∏ j ∈ univ.filter (fun j : Fin (N + 1) => i < j), ((((nu i : ℤ) - (nu j : ℤ) + ((j : ℕ) : ℤ) - ((i : ℕ) : ℤ)) : ℤ) : ℝ)`. Combine the equalities or inequalities in the displayed calculation. Establish `hPle : ∏ t ∈ range (N - (i : ℕ)), ((nu i : ℝ) + ((t + 1 : ℕ) : ℝ)) ≤ ((nu 0 : ℝ) + N + 1) ^ (N - (i : ℕ))`. Establish `h0i : nu i ≤ nu 0` using `hnu (by simp [Fin.le_iff_val_le_val])`. Combine the equalities or inequalities in the displayed calculation.

Establish `ht'` using `Finset.mem_range.mp ht`. Establish `h5 : nu i + (t + 1) ≤ nu 0 + N + 1` using `by omega`. Conclude with `h5)` after adjusting the coercions. Use `_ = _ := by rw [Finset.prod_const, Finset.card_range]`. Establish `hApos` using `lt_of_lt_of_le zero_lt_one hA1`.

Establish `hfac : (0:ℝ) ≤ ((nu i).factorial : ℝ)` using `by positivity`. Prove the components needed by the constructor for the conclusion. Rewrite using `[le_div_iff₀ hApos, hF]`. Conclude with `mul_le_mul_of_nonneg_left hAle hfac`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← Finset.prod_div_distrib]`. Prove the components needed by the constructor for the conclusion. Conclude with `Finset.prod_le_prod (fun i _ => by positivity) (fun i _ => (hper i).1)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem lemma_c_explicit_bounds : LemC_bounds := by
  intro N nu hnu
  unfold hookF
  have hd : ∀ i j : Fin (N + 1), i < j →
      (1:ℝ) ≤ ((((nu i : ℤ) - (nu j : ℤ) + ((j : ℕ) : ℤ) - ((i : ℕ) : ℤ)) : ℤ) : ℝ) ∧
      ((((nu i : ℤ) - (nu j : ℤ) + ((j : ℕ) : ℤ) - ((i : ℕ) : ℤ)) : ℤ) : ℝ)
        ≤ (nu i : ℝ) + (((j : ℕ) - (i : ℕ) : ℕ) : ℝ) := by
    intro i j hij
    have h1 := hnu (le_of_lt hij)
    have h2 : (i : ℕ) < j := Fin.lt_iff_val_lt_val.mp hij
    constructor
    · have h3 : (1:ℤ) ≤ (nu i : ℤ) - (nu j : ℤ) + ((j : ℕ) : ℤ) - ((i : ℕ) : ℤ) := by omega
      exact_mod_cast h3
    · have h3 : (nu i : ℤ) - (nu j : ℤ) + ((j : ℕ) : ℤ) - ((i : ℕ) : ℤ)
          ≤ (nu i : ℤ) + (((j : ℕ) - (i : ℕ) : ℕ) : ℤ) := by omega
      exact_mod_cast h3
  have hper : ∀ i : Fin (N + 1),
      ((nu i).factorial : ℝ) ≤ ((nu i + (N + 1) - 1 - (i : ℕ)).factorial : ℝ) /
          ∏ j ∈ univ.filter (fun j : Fin (N + 1) => i < j),
            ((((nu i : ℤ) - (nu j : ℤ) + ((j : ℕ) : ℤ) - ((i : ℕ) : ℤ)) : ℤ) : ℝ) ∧
      ((nu i + (N + 1) - 1 - (i : ℕ)).factorial : ℝ) /
          ∏ j ∈ univ.filter (fun j : Fin (N + 1) => i < j),
            ((((nu i : ℤ) - (nu j : ℤ) + ((j : ℕ) : ℤ) - ((i : ℕ) : ℤ)) : ℤ) : ℝ)
        ≤ ((nu i).factorial : ℝ) * ((nu 0 : ℝ) + N + 1) ^ (N - (i : ℕ)) := by
    intro i
    have hi := i.isLt
    have e1 : nu i + (N + 1) - 1 - (i : ℕ) = nu i + (N - (i : ℕ)) := by omega
    have hF : ((nu i + (N + 1) - 1 - (i : ℕ)).factorial : ℝ)
        = ((nu i).factorial : ℝ) * ∏ t ∈ range (N - (i : ℕ)), ((nu i : ℝ) + ((t + 1 : ℕ) : ℝ)) := by
      rw [e1]
      exact g4w9_fact_range (nu i) (N - (i : ℕ))
    have hAle : ∏ j ∈ univ.filter (fun j : Fin (N + 1) => i < j),
            ((((nu i : ℤ) - (nu j : ℤ) + ((j : ℕ) : ℤ) - ((i : ℕ) : ℤ)) : ℤ) : ℝ)
        ≤ ∏ t ∈ range (N - (i : ℕ)), ((nu i : ℝ) + ((t + 1 : ℕ) : ℝ)) := by
      calc _ ≤ ∏ j ∈ univ.filter (fun j : Fin (N + 1) => i < j),
              ((nu i : ℝ) + (((j : ℕ) - (i : ℕ) : ℕ) : ℝ)) :=
            Finset.prod_le_prod
              (fun j hj => le_trans zero_le_one (hd i j (Finset.mem_filter.mp hj).2).1)
              (fun j hj => (hd i j (Finset.mem_filter.mp hj).2).2)
        _ = _ := g4w9_prod_gt N i (fun x => (nu i : ℝ) + (x : ℝ))
    have hA1 : (1:ℝ) ≤ ∏ j ∈ univ.filter (fun j : Fin (N + 1) => i < j),
            ((((nu i : ℤ) - (nu j : ℤ) + ((j : ℕ) : ℤ) - ((i : ℕ) : ℤ)) : ℤ) : ℝ) := by
      calc (1:ℝ) = ∏ j ∈ univ.filter (fun j : Fin (N + 1) => i < j), (1:ℝ) :=
            Finset.prod_const_one.symm
        _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one)
              (fun j hj => (hd i j (Finset.mem_filter.mp hj).2).1)
    have hPle : ∏ t ∈ range (N - (i : ℕ)), ((nu i : ℝ) + ((t + 1 : ℕ) : ℝ))
        ≤ ((nu 0 : ℝ) + N + 1) ^ (N - (i : ℕ)) := by
      have h0i : nu i ≤ nu 0 := hnu (by simp [Fin.le_iff_val_le_val])
      calc _ ≤ ∏ t ∈ range (N - (i : ℕ)), ((nu 0 : ℝ) + N + 1) :=
            Finset.prod_le_prod (fun t _ => by positivity)
              (fun t ht => by
                have ht' := Finset.mem_range.mp ht
                have h5 : nu i + (t + 1) ≤ nu 0 + N + 1 := by omega
                exact_mod_cast h5)
        _ = _ := by rw [Finset.prod_const, Finset.card_range]
    have hApos := lt_of_lt_of_le zero_lt_one hA1
    have hfac : (0:ℝ) ≤ ((nu i).factorial : ℝ) := by positivity
    constructor
    · rw [le_div_iff₀ hApos, hF]
      exact mul_le_mul_of_nonneg_left hAle hfac
    · calc _ ≤ ((nu i + (N + 1) - 1 - (i : ℕ)).factorial : ℝ) := div_le_self (by positivity) hA1
        _ = _ := hF
        _ ≤ _ := mul_le_mul_of_nonneg_left hPle hfac
  rw [← Finset.prod_div_distrib]
  constructor
  · exact Finset.prod_le_prod (fun i _ => by positivity) (fun i _ => (hper i).1)
  · calc _ ≤ ∏ i : Fin (N + 1), (((nu i).factorial : ℝ) * ((nu 0 : ℝ) + N + 1) ^ (N - (i : ℕ))) :=
          Finset.prod_le_prod (fun i _ => le_trans (by positivity) (hper i).1) (fun i _ => (hper i).2)
      _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, g4w9_sum_count N]

/- English proof (translation)
Introduce `d k h v hd hk hv hpos hcol`. Establish `hdpos : (0:ℝ) < d` using `Nat.cast_pos.mpr (by omega)`. Establish `hXpos : ∀ τ, 0 < ∑ c, h τ c`. Introduce `τ`. Conclude with `Finset.sum_pos (fun c _ => hpos τ c) ⟨⟨0, by omega⟩, Finset.mem_univ _⟩`.

Establish `hcol' : ∀ c, ∑ τ, h τ c ≤ d * ((k:ℝ) ^ 2 * (2 * v) ^ 2)`. Introduce `c`. Establish `h1` using `hcol c`. Rewrite `h1` using `[div_le_iff₀ hdpos]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hT : ∑ τ, ∑ c, h τ c ≤ d * ((k:ℝ) ^ 3 * (2 * v) ^ 2)`. Rewrite using `[Finset.sum_comm]`. Establish `h1 : ∑ c : Fin k, ∑ τ : Fin d, h τ c ≤ ∑ c : Fin k, ((d:ℝ) * ((k:ℝ) ^ 2 * (2 * v) ^ 2))` using `Finset.sum_le_sum (fun c _ => hcol' c)`. Rewrite `h1` using `[Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]`. Combine the equalities or inequalities in the displayed calculation.

Establish `hTpos : 0 < ∑ τ, ∑ c, h τ c` using `Finset.sum_pos (fun τ _ => hXpos τ) ⟨⟨0, by omega⟩, Finset.mem_univ _⟩`. Take `⟨M, hM⟩ : ∃ M : ℝ, M = (∑ τ, ∑ c, h τ c) / d` from `⟨_, rfl⟩`. Establish `hMpos : 0 < M` using `by rw [hM]; exact div_pos hTpos hdpos`. Establish `hstep : ∀ τ, Real.log (∑ c, h τ c) ≤ Real.log M + (∑ c, h τ c) / M - 1`. Introduce `τ`.

Establish `h1` using `Real.log_le_sub_one_of_pos (div_pos (hXpos τ) hMpos)`. Rewrite `h1` using `[Real.log_div (hXpos τ).ne' hMpos.ne']`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hsum1 : ∑ τ, Real.log (∑ c, h τ c) ≤ ∑ τ : Fin d, (Real.log M + (∑ c, h τ c) / M - 1)` using `Finset.sum_le_sum (fun τ _ => hstep τ)`. Establish `hsum2 : ∑ τ : Fin d, (Real.log M + (∑ c, h τ c) / M - 1) = d * Real.log M + (∑ τ, ∑ c, h τ c) / M - d`.

Rewrite using `[Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_div]`. Simplify using `only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]`. Establish `hsum3 : (∑ τ, ∑ c, h τ c) / M = d`. Establish `h1` using `hTpos.ne'`. Establish `h2` using `hdpos.ne'`.

Rewrite using `[hM]`. Clear the denominators using the available nonvanishing facts. Establish `hMle : M ≤ (k:ℝ) ^ 3 * (2 * v) ^ 2`. Rewrite using `[hM, div_le_iff₀ hdpos]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hlog` using `Real.log_le_log hMpos hMle`. Establish `hfin` using `mul_le_mul_of_nonneg_left hlog hdpos.le`. Rewrite using `[div_le_iff₀ hdpos]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem mean_log_explicit : MeanLogExplicit := by
  intro d k h v hd hk hv hpos hcol
  have hdpos : (0:ℝ) < d := Nat.cast_pos.mpr (by omega)
  have hXpos : ∀ τ, 0 < ∑ c, h τ c := by
    intro τ
    exact Finset.sum_pos (fun c _ => hpos τ c) ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  have hcol' : ∀ c, ∑ τ, h τ c ≤ d * ((k:ℝ) ^ 2 * (2 * v) ^ 2) := by
    intro c
    have h1 := hcol c
    rw [div_le_iff₀ hdpos] at h1
    linarith
  have hT : ∑ τ, ∑ c, h τ c ≤ d * ((k:ℝ) ^ 3 * (2 * v) ^ 2) := by
    rw [Finset.sum_comm]
    have h1 : ∑ c : Fin k, ∑ τ : Fin d, h τ c ≤ ∑ c : Fin k, ((d:ℝ) * ((k:ℝ) ^ 2 * (2 * v) ^ 2)) :=
      Finset.sum_le_sum (fun c _ => hcol' c)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
    calc _ ≤ _ := h1
      _ = _ := by ring
  have hTpos : 0 < ∑ τ, ∑ c, h τ c :=
    Finset.sum_pos (fun τ _ => hXpos τ) ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = (∑ τ, ∑ c, h τ c) / d := ⟨_, rfl⟩
  have hMpos : 0 < M := by rw [hM]; exact div_pos hTpos hdpos
  have hstep : ∀ τ, Real.log (∑ c, h τ c) ≤ Real.log M + (∑ c, h τ c) / M - 1 := by
    intro τ
    have h1 := Real.log_le_sub_one_of_pos (div_pos (hXpos τ) hMpos)
    rw [Real.log_div (hXpos τ).ne' hMpos.ne'] at h1
    linarith
  have hsum1 : ∑ τ, Real.log (∑ c, h τ c) ≤ ∑ τ : Fin d, (Real.log M + (∑ c, h τ c) / M - 1) :=
    Finset.sum_le_sum (fun τ _ => hstep τ)
  have hsum2 : ∑ τ : Fin d, (Real.log M + (∑ c, h τ c) / M - 1)
      = d * Real.log M + (∑ τ, ∑ c, h τ c) / M - d := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_div]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have hsum3 : (∑ τ, ∑ c, h τ c) / M = d := by
    have h1 := hTpos.ne'
    have h2 := hdpos.ne'
    rw [hM]
    field_simp
  have hMle : M ≤ (k:ℝ) ^ 3 * (2 * v) ^ 2 := by
    rw [hM, div_le_iff₀ hdpos]
    linarith
  have hlog := Real.log_le_log hMpos hMle
  have hfin := mul_le_mul_of_nonneg_left hlog hdpos.le
  rw [div_le_iff₀ hdpos]
  linarith

/- English proof (translation)
Introduce `κ lam v logT logB logc muB mu hv hanti hB hc hmuB hmu`. Establish `hW0 : 0 ≤ wt (plus lam)`. Simplify using `only [wt, plus]`. Conclude with `Finset.sum_nonneg (fun i _ => by have := hanti (Fin.le_last i); linarith)`. Establish `hW : (0:ℝ) ≤ (wt (plus lam) : ℝ)` using `by exact_mod_cast hW0`.

Establish `hk : (0:ℝ) < (κ:ℝ) + 1` using `by positivity`. Establish `hv0 : (0:ℝ) < v` using `by linarith`. Establish `hkey : Real.log ((κ:ℝ) + 1) + Real.log (4 * ((κ:ℝ) + 1) ^ 3 * v ^ 2) ≤ 4 * Real.log (((κ:ℝ) + 1) * v)`. Establish `hpos2 : (4 * ((κ:ℝ) + 1) ^ 3 * v ^ 2) ≠ 0` using `by positivity`. Establish `e4 : 4 * Real.log (((κ:ℝ) + 1) * v) = Real.log ((((κ:ℝ) + 1) * v) ^ 4)`.

Rewrite using `[Real.log_pow]`. Evaluate the numerical expressions. Rewrite using `[← Real.log_mul hk.ne' hpos2, e4]`. Apply `Real.log_le_log (by positivity)` to reduce the goal to its premises. Establish `hv2 : (4:ℝ) ≤ v ^ 2` using `by nlinarith`.

Establish `hP : (0:ℝ) ≤ ((κ:ℝ) + 1) ^ 4 * v ^ 2` using `by positivity`. Establish `e1 : ((κ:ℝ) + 1) * (4 * ((κ:ℝ) + 1) ^ 3 * v ^ 2) = 4 * (((κ:ℝ) + 1) ^ 4 * v ^ 2)` using `by ring`. Establish `e2 : (((κ:ℝ) + 1) * v) ^ 4 = (((κ:ℝ) + 1) ^ 4 * v ^ 2) * v ^ 2` using `by ring`. Rewrite using `[e1, e2]`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left hv2 hP]`.

Establish `h1` using `mul_le_mul_of_nonneg_left hB hW`. Establish `h2` using `mul_le_mul_of_nonneg_left hkey hW`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem explicit_zeta_bound_rank_five : AntitoneWeightLogBoundExplicit := by
  intro κ lam v logT logB logc muB mu hv hanti hB hc hmuB hmu
  have hW0 : 0 ≤ wt (plus lam) := by
    simp only [wt, plus]
    exact Finset.sum_nonneg (fun i _ => by have := hanti (Fin.le_last i); linarith)
  have hW : (0:ℝ) ≤ (wt (plus lam) : ℝ) := by exact_mod_cast hW0
  have hk : (0:ℝ) < (κ:ℝ) + 1 := by positivity
  have hv0 : (0:ℝ) < v := by linarith
  have hkey : Real.log ((κ:ℝ) + 1) + Real.log (4 * ((κ:ℝ) + 1) ^ 3 * v ^ 2)
      ≤ 4 * Real.log (((κ:ℝ) + 1) * v) := by
    have hpos2 : (4 * ((κ:ℝ) + 1) ^ 3 * v ^ 2) ≠ 0 := by positivity
    have e4 : 4 * Real.log (((κ:ℝ) + 1) * v) = Real.log ((((κ:ℝ) + 1) * v) ^ 4) := by
      rw [Real.log_pow]
      norm_num
    rw [← Real.log_mul hk.ne' hpos2, e4]
    apply Real.log_le_log (by positivity)
    have hv2 : (4:ℝ) ≤ v ^ 2 := by nlinarith
    have hP : (0:ℝ) ≤ ((κ:ℝ) + 1) ^ 4 * v ^ 2 := by positivity
    have e1 : ((κ:ℝ) + 1) * (4 * ((κ:ℝ) + 1) ^ 3 * v ^ 2) = 4 * (((κ:ℝ) + 1) ^ 4 * v ^ 2) := by ring
    have e2 : (((κ:ℝ) + 1) * v) ^ 4 = (((κ:ℝ) + 1) ^ 4 * v ^ 2) * v ^ 2 := by ring
    rw [e1, e2]
    nlinarith [mul_le_mul_of_nonneg_left hv2 hP]
  have h1 := mul_le_mul_of_nonneg_left hB hW
  have h2 := mul_le_mul_of_nonneg_left hkey hW
  linarith

/- English proof (translation)
Introduce `d`. Proceed by induction on `d with`. Consider the case `zero => intro i _`. Simplify using the standard rewrite rules. Consider the case `succ d ih`.

Introduce `i hi`. Establish `h1` using `ih i (by omega)`. Establish `h2` using `L.chain (i + d) (by omega)`. Establish `e : i + (d + 1) = i + d + 1` using `by omega`. Rewrite using `[e]`.

Use `push_cast`. Combine the linear relations using `[h2.1, h2.2]`.
-/
private theorem g4w9_dec (K m s : ℕ) (U v b e : ℕ → ℤ) (S eta : ℤ) (L : Layout K m s U v b e S eta) :
    ∀ d i, i + d < 2 * K → U (i + d) + (d : ℤ) ≤ U i := by
  intro d
  induction d with
  | zero => intro i _; simp
  | succ d ih =>
    intro i hi
    have h1 := ih i (by omega)
    have h2 := L.chain (i + d) (by omega)
    have e : i + (d + 1) = i + d + 1 := by omega
    rw [e]
    push_cast
    linarith [h2.1, h2.2]

/- English proof (translation)
Take `⟨d, rfl⟩` from `Nat.exists_eq_add_of_le hij`. Establish `h` using `g4w9_dec K m s U v b e S eta L d i (by omega)`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem g4w9_dec' (K m s : ℕ) (U v b e : ℕ → ℤ) (S eta : ℤ) (L : Layout K m s U v b e S eta)
    (i j : ℕ) (hij : i ≤ j) (hj : j < 2 * K) : U j + (j : ℤ) ≤ U i + (i : ℤ) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  have h := g4w9_dec K m s U v b e S eta L d i (by omega)
  push_cast
  linarith

/- English proof (translation)
Introduce `i j hij`. Establish `hj : (j : ℕ) < 2 * K` using `by have := j.isLt; omega`. Establish `h` using `g4w9_dec' K m s U v b e S eta L i j (Fin.le_iff_val_le_val.mp hij) hj`. Simplify using `only [colW]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem g4w9_anti (K m s κ : ℕ) (U v b e : ℕ → ℤ) (S eta : ℤ) (L : Layout K m s U v b e S eta)
    (hκ : κ + 1 = 2 * K) : Antitone (colW K U (k := κ + 1)) := by
  intro i j hij
  have hj : (j : ℕ) < 2 * K := by have := j.isLt; omega
  have h := g4w9_dec' K m s U v b e S eta L i j (Fin.le_iff_val_le_val.mp hij) hj
  simp only [colW]
  linarith

/- English proof (translation)
Introduce `K m s κ U v b e S eta A bt L hT hκ`. Establish `hK` using `L.one_le_K`. Establish `hKz : (1:ℤ) ≤ K` using `by exact_mod_cast hK`. Establish `hκz : (κ:ℤ) + 1 = 2 * K` using `by exact_mod_cast hκ`. Establish `hcw : ∀ i : Fin (κ + 1), colW K U i = U i - K + ((i : ℕ) : ℤ) + 1` using `fun i => rfl`.

Use `⟨g4w9_anti K m s κ U v b e S eta L hκ, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hcw]`. Simplify using `only [Fin.val_zero, Nat.cast_zero]`. Combine the linear relations using `[hT.1]`. Rewrite using `[hcw, Fin.val_last]`.

Establish `e0 : 2 * K - 1 = κ` using `by omega`. Establish `h2` using `hT.2`. Rewrite `h2` using `[e0]`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `i hi0 hil`.

Establish `hi` using `i.isLt`. Establish `h0 : (i : ℕ) ≠ 0` using `fun h => hi0 (Fin.ext (by simpa using h))`. Establish `hl : (i : ℕ) ≠ κ` using `fun h => hil (Fin.ext (by simpa using h))`. Establish `hA` using `g4w9_dec' K m s U v b e S eta L 1 i (by omega) (by omega)`. Establish `hB` using `g4w9_dec' K m s U v b e S eta L i (2 * K - 2) (by omega) (by omega)`.

Establish `hc1` using `L.cloud_u 1 le_rfl (by omega)`. Establish `hc2` using `L.cloud_u (2 * K - 2) (by omega) (by omega)`. Establish `e2 : (((2 * K - 2 : ℕ)) : ℤ) = 2 * (K : ℤ) - 2` using `by omega`. Rewrite using `[hcw]`. Move the coercions through the operations in `at hA`.

Apply the tactic sequence `constructor <;> linarith [hc1.2, hc2.1]`.
-/
theorem column_parametrization_top_entry : ColumnParameterMaximalCondition := by
  intro K m s κ U v b e S eta A bt L hT hκ
  have hK := L.one_le_K
  have hKz : (1:ℤ) ≤ K := by exact_mod_cast hK
  have hκz : (κ:ℤ) + 1 = 2 * K := by exact_mod_cast hκ
  have hcw : ∀ i : Fin (κ + 1), colW K U i = U i - K + ((i : ℕ) : ℤ) + 1 := fun i => rfl
  refine ⟨g4w9_anti K m s κ U v b e S eta L hκ, ?_, ?_, ?_⟩
  · rw [hcw]
    simp only [Fin.val_zero, Nat.cast_zero]
    linarith [hT.1]
  · rw [hcw, Fin.val_last]
    have e0 : 2 * K - 1 = κ := by omega
    have h2 := hT.2
    rw [e0] at h2
    linarith
  · intro i hi0 hil
    have hi := i.isLt
    have h0 : (i : ℕ) ≠ 0 := fun h => hi0 (Fin.ext (by simpa using h))
    have hl : (i : ℕ) ≠ κ := fun h => hil (Fin.ext (by simpa using h))
    have hA := g4w9_dec' K m s U v b e S eta L 1 i (by omega) (by omega)
    have hB := g4w9_dec' K m s U v b e S eta L i (2 * K - 2) (by omega) (by omega)
    have hc1 := L.cloud_u 1 le_rfl (by omega)
    have hc2 := L.cloud_u (2 * K - 2) (by omega) (by omega)
    have e2 : (((2 * K - 2 : ℕ)) : ℤ) = 2 * (K : ℤ) - 2 := by omega
    rw [hcw]
    push_cast at hA
    constructor <;> linarith [hc1.2, hc2.1]

/- English proof (translation)
Introduce `K m s κ U v b e S eta L hO hκ`. Take `⟨hO1, hO2, hO3, hO4⟩` from `hO`. Establish `hK` using `L.one_le_K`. Establish `hKz : (1:ℤ) ≤ K` using `by exact_mod_cast hK`. Establish `hκz : (κ:ℤ) + 1 = 2 * K` using `by exact_mod_cast hκ`.

Establish `hκ1 : 1 ≤ κ` using `by omega`. Establish `hanti` using `g4w9_anti K m s κ U v b e S eta L hκ`. Establish `hv0` using `L.cloud_v 0 (by omega)`. Establish `hvl` using `L.cloud_v (2 * K - 2) (by omega)`. Establish `eK : 2 * K - 1 = κ` using `by omega`.

Rewrite `hO3` using `[eK]`. Establish `hU : ∀ j : ℕ, 1 ≤ j → j ≤ κ → U j + 1 ≤ S`. Introduce `j hj1 hjk`. Break down `Nat.lt_or_ge j κ with h | h` into its components or cases. Conclude with `(L.cloud_u j hj1 (by omega)).2`.

Establish `hjκ : j = κ` using `by omega`. Rewrite using `[hjκ]`. Combine the linear relations using `[hvl.2]`. Establish `hU0 : U 0 + 1 ≤ 3 * S` using `by linarith [hv0.2]`. Establish `hcw : ∀ i : Fin (κ + 1), colW K U i = U i - K + ((i : ℕ) : ℤ) + 1` using `fun i => rfl`.

Establish `hlast : colW K U (Fin.last κ) = v (2 * K - 2) + K - 1`. Rewrite using `[hcw, Fin.val_last, hO3]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hzero : colW K U (0 : Fin (κ + 1)) = U 0 - K + 1`. Rewrite using `[hcw]`.

Simplify using the standard rewrite rules. Establish `hlo : ∀ i : Fin (κ + 1), colW K U (Fin.last κ) ≤ colW K U i` using `fun i => hanti (Fin.le_last i)`. Establish `hhi : ∀ i : Fin (κ + 1), colW K U i ≤ colW K U 0` using `fun i => hanti (by simp [Fin.le_iff_val_le_val])`. Establish `hb : ∀ i : Fin (κ + 1), 0 ≤ colW K U i ∧ colW K U i ≤ 3 * S`. Introduce `i`.

Establish `h1` using `hlo i`. Establish `h2` using `hhi i`. Rewrite `h1` using `[hlast]`. Rewrite `h2` using `[hzero]`. Apply the tactic sequence `constructor <;> linarith [hvl.1]`.

Establish `hc : ∀ i : Fin (κ + 1), i ≠ 0 → colW K U i - colW K U (Fin.last κ) ≤ S`. Introduce `i hi`. Establish `h0 : (i : ℕ) ≠ 0` using `fun h => hi (Fin.ext (by simpa using h))`. Establish `hik : (i : ℕ) ≤ κ` using `by have := i.isLt; omega`. Establish `hikz : ((i : ℕ) : ℤ) ≤ κ` using `by exact_mod_cast hik`.

Establish `h2` using `hU i (by omega) hik`. Rewrite using `[hcw i, hlast]`. Combine the linear relations using `[hvl.1]`. Establish `hpair : ∀ i : Fin (κ + 1), colW K U i + colW K U (Fin.rev i) ≤ 4 * S`. Introduce `i`.

Establish `hi` using `i.isLt`. Establish `hjk : (i : ℕ) ≤ κ` using `by omega`. Rewrite using `[hcw, hcw, Fin.val_rev]`. Establish `e1 : κ + 1 - ((i : ℕ) + 1) = κ - (i : ℕ)` using `by omega`. Rewrite using `[e1]`.

Establish `e2 : (((κ - (i : ℕ) : ℕ)) : ℤ) = (κ : ℤ) - ((i : ℕ) : ℤ)` using `by omega`. Establish `hUk` using `hU κ hκ1 le_rfl`. Break down `Nat.eq_zero_or_pos (i : ℕ) with h0 | h0` into its components or cases. Establish `a1 : U (i : ℕ) = U 0` using `by rw [h0]`. Establish `a2 : U (κ - (i : ℕ)) = U κ` using `by rw [h0, Nat.sub_zero]`.

Establish `a3 : ((i : ℕ) : ℤ) = 0` using `by omega`. Combine the linear equalities and inequalities to obtain the conclusion. Break down `Nat.lt_or_ge (i : ℕ) κ with h1 | h1` into its components or cases. Establish `u1` using `hU i h0 hjk`. Establish `u2` using `hU (κ - (i : ℕ)) (by omega) (by omega)`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hik : (i : ℕ) = κ` using `by omega`. Establish `a1 : U (i : ℕ) = U κ` using `by rw [hik]`. Establish `a2 : U (κ - (i : ℕ)) = U 0` using `by rw [hik, Nat.sub_self]`. Establish `a3 : ((i : ℕ) : ℤ) = κ` using `by omega`.

Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨hanti, hb, hc, ?_, ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [wt, plus]`. Rewrite using `[Fin.sum_univ_succ]`. Establish `h1 : ∑ j : Fin κ, (colW K U j.succ - colW K U (Fin.last κ)) ≤ ∑ j : Fin κ, S` using `Finset.sum_le_sum (fun j _ => hc j.succ (Fin.succ_ne_zero j))`.

Establish `h2 : ∑ j : Fin κ, S = (κ : ℤ) * S`. Rewrite using `[Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]`. Establish `h3 : colW K U (0 : Fin (κ + 1)) - colW K U (Fin.last κ) ≤ 3 * S`. Rewrite using `[hzero, hlast]`. Combine the linear relations using `[hvl.1]`.

Combine the linear equalities and inequalities to obtain the conclusion. Simplify using `only [wt]`. Conclude with `Finset.sum_nonneg (fun i _ => (hb i).1)`. Establish `hrev : ∑ i : Fin (κ + 1), colW K U (Fin.rev i) = ∑ i : Fin (κ + 1), colW K U i` using `Equiv.sum_comp Fin.revPerm (colW K U)`. Establish `hs : ∑ i : Fin (κ + 1), (colW K U i + colW K U (Fin.rev i)) ≤ ∑ i : Fin (κ + 1), 4 * S` using `Finset.sum_le_sum (fun i _ => hpair i)`.

Rewrite `hs` using `[Finset.sum_add_distrib, hrev]`. Establish `h4 : ∑ i : Fin (κ + 1), (4 * S) = ((κ : ℤ) + 1) * (4 * S)`. Rewrite using `[Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only [wt]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem column_parametrization_off_diagonal : Col_param_off := by
  intro K m s κ U v b e S eta L hO hκ
  obtain ⟨hO1, hO2, hO3, hO4⟩ := hO
  have hK := L.one_le_K
  have hKz : (1:ℤ) ≤ K := by exact_mod_cast hK
  have hκz : (κ:ℤ) + 1 = 2 * K := by exact_mod_cast hκ
  have hκ1 : 1 ≤ κ := by omega
  have hanti := g4w9_anti K m s κ U v b e S eta L hκ
  have hv0 := L.cloud_v 0 (by omega)
  have hvl := L.cloud_v (2 * K - 2) (by omega)
  have eK : 2 * K - 1 = κ := by omega
  rw [eK] at hO3
  have hU : ∀ j : ℕ, 1 ≤ j → j ≤ κ → U j + 1 ≤ S := by
    intro j hj1 hjk
    rcases Nat.lt_or_ge j κ with h | h
    · exact (L.cloud_u j hj1 (by omega)).2
    · have hjκ : j = κ := by omega
      rw [hjκ]
      linarith [hvl.2]
  have hU0 : U 0 + 1 ≤ 3 * S := by linarith [hv0.2]
  have hcw : ∀ i : Fin (κ + 1), colW K U i = U i - K + ((i : ℕ) : ℤ) + 1 := fun i => rfl
  have hlast : colW K U (Fin.last κ) = v (2 * K - 2) + K - 1 := by
    rw [hcw, Fin.val_last, hO3]
    linarith
  have hzero : colW K U (0 : Fin (κ + 1)) = U 0 - K + 1 := by
    rw [hcw]
    simp
  have hlo : ∀ i : Fin (κ + 1), colW K U (Fin.last κ) ≤ colW K U i :=
    fun i => hanti (Fin.le_last i)
  have hhi : ∀ i : Fin (κ + 1), colW K U i ≤ colW K U 0 :=
    fun i => hanti (by simp [Fin.le_iff_val_le_val])
  have hb : ∀ i : Fin (κ + 1), 0 ≤ colW K U i ∧ colW K U i ≤ 3 * S := by
    intro i
    have h1 := hlo i
    have h2 := hhi i
    rw [hlast] at h1
    rw [hzero] at h2
    constructor <;> linarith [hvl.1]
  have hc : ∀ i : Fin (κ + 1), i ≠ 0 → colW K U i - colW K U (Fin.last κ) ≤ S := by
    intro i hi
    have h0 : (i : ℕ) ≠ 0 := fun h => hi (Fin.ext (by simpa using h))
    have hik : (i : ℕ) ≤ κ := by have := i.isLt; omega
    have hikz : ((i : ℕ) : ℤ) ≤ κ := by exact_mod_cast hik
    have h2 := hU i (by omega) hik
    rw [hcw i, hlast]
    linarith [hvl.1]
  have hpair : ∀ i : Fin (κ + 1), colW K U i + colW K U (Fin.rev i) ≤ 4 * S := by
    intro i
    have hi := i.isLt
    have hjk : (i : ℕ) ≤ κ := by omega
    rw [hcw, hcw, Fin.val_rev]
    have e1 : κ + 1 - ((i : ℕ) + 1) = κ - (i : ℕ) := by omega
    rw [e1]
    have e2 : (((κ - (i : ℕ) : ℕ)) : ℤ) = (κ : ℤ) - ((i : ℕ) : ℤ) := by omega
    have hUk := hU κ hκ1 le_rfl
    rcases Nat.eq_zero_or_pos (i : ℕ) with h0 | h0
    · have a1 : U (i : ℕ) = U 0 := by rw [h0]
      have a2 : U (κ - (i : ℕ)) = U κ := by rw [h0, Nat.sub_zero]
      have a3 : ((i : ℕ) : ℤ) = 0 := by omega
      linarith
    · rcases Nat.lt_or_ge (i : ℕ) κ with h1 | h1
      · have u1 := hU i h0 hjk
        have u2 := hU (κ - (i : ℕ)) (by omega) (by omega)
        linarith
      · have hik : (i : ℕ) = κ := by omega
        have a1 : U (i : ℕ) = U κ := by rw [hik]
        have a2 : U (κ - (i : ℕ)) = U 0 := by rw [hik, Nat.sub_self]
        have a3 : ((i : ℕ) : ℤ) = κ := by omega
        linarith
  refine ⟨hanti, hb, hc, ?_, ?_, ?_⟩
  · simp only [wt, plus]
    rw [Fin.sum_univ_succ]
    have h1 : ∑ j : Fin κ, (colW K U j.succ - colW K U (Fin.last κ)) ≤ ∑ j : Fin κ, S :=
      Finset.sum_le_sum (fun j _ => hc j.succ (Fin.succ_ne_zero j))
    have h2 : ∑ j : Fin κ, S = (κ : ℤ) * S := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have h3 : colW K U (0 : Fin (κ + 1)) - colW K U (Fin.last κ) ≤ 3 * S := by
      rw [hzero, hlast]
      linarith [hvl.1]
    linarith
  · simp only [wt]
    exact Finset.sum_nonneg (fun i _ => (hb i).1)
  · have hrev : ∑ i : Fin (κ + 1), colW K U (Fin.rev i) = ∑ i : Fin (κ + 1), colW K U i :=
      Equiv.sum_comp Fin.revPerm (colW K U)
    have hs : ∑ i : Fin (κ + 1), (colW K U i + colW K U (Fin.rev i)) ≤ ∑ i : Fin (κ + 1), 4 * S :=
      Finset.sum_le_sum (fun i _ => hpair i)
    rw [Finset.sum_add_distrib, hrev] at hs
    have h4 : ∑ i : Fin (κ + 1), (4 * S) = ((κ : ℤ) + 1) * (4 * S) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      ring
    simp only [wt]
    linarith

end Formalism.HermitianLattices.ExplicitEstimates
