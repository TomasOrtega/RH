import Mathlib
import Formalism.PolynomialDimension.DigitClassSize

noncomputable section

open scoped BigOperators
open Finset Filter Topology

namespace Formalism.CountingSumsFrames

/- English proof (translation)
Unfold `dimPol`. Conclude with `Nat.choose_pos (by omega)` after adjusting the coercions.
-/
theorem dimPol_pos_real (k' A : ℕ) : (0 : ℝ) < dimPol k' A := by
  unfold dimPol
  exact_mod_cast Nat.choose_pos (by omega)

/- English proof (translation)
Establish `h` using `Nat.choose_mul_succ_eq (A + k') k'`. Rewrite `h` using `[show A + k' + 1 - k' = A + 1 by omega]`. Establish `h3 : dimPol k' (A + 1) * (A + 1) = dimPol k' A * (A + 1 + k')`. Unfold `dimPol`. Rewrite using `[show A + 1 + k' = A + k' + 1 by omega]`.

Conclude with `h.symm`. Conclude with `h3` after adjusting the coercions.
-/
theorem dimPol_succ_mul_real (k' A : ℕ) :
    (dimPol k' (A + 1) : ℝ) * ((A : ℝ) + 1) = dimPol k' A * ((A : ℝ) + 1 + k') := by
  have h := Nat.choose_mul_succ_eq (A + k') k'
  rw [show A + k' + 1 - k' = A + 1 by omega] at h
  have h3 : dimPol k' (A + 1) * (A + 1) = dimPol k' A * (A + 1 + k') := by
    unfold dimPol
    rw [show A + 1 + k' = A + k' + 1 by omega]
    exact h.symm
  exact_mod_cast h3

/- English proof (translation)
Rewrite using `[eq_div_iff (by positivity)]`. Conclude with `dimPol_succ_mul_real k' A`.
-/
theorem dimPol_succ_eq_real (k' A : ℕ) :
    (dimPol k' (A + 1) : ℝ) = dimPol k' A * ((A : ℝ) + 1 + k') / ((A : ℝ) + 1) := by
  rw [eq_div_iff (by positivity)]
  exact dimPol_succ_mul_real k' A

/- English proof (translation)
Introduce `k' al j hal`. Establish `hal' : (0 : ℝ) < al` using `by exact_mod_cast hal`. Proceed by induction on `j with`. Consider the case `zero => simp [div_self (dimPol_pos_real k' al).ne']`. Consider the case `succ j ih`.

Establish `p0` using `dimPol_pos_real k' (al + j)`. Establish `pa` using `dimPol_pos_real k' al`. Establish `hrec` using `dimPol_succ_eq_real k' (al + j)`. Rewrite using `[show al + (j + 1) = al + j + 1 by omega, hrec]`. Move the coercions through the operations in `at ih ⊢`.

Use `set r : ℝ := (dimPol k' al : ℝ) / dimPol k' (al + j) with hr`. Establish `hr0 : 0 ≤ r` using `by positivity`. Establish `hkey : (dimPol k' al : ℝ) / (dimPol k' (al + j) * ((al : ℝ) + j + 1 + k') / ((al : ℝ) + j + 1)) = r * (((al : ℝ) + j + 1) / ((al : ℝ) + j + 1 + k'))`. Rewrite using `[hr]`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[hkey]`. Use `set t : ℝ := ((al : ℝ) + j + 1) / ((al : ℝ) + j + 1 + k') with ht`. Establish `hk0 : (0 : ℝ) ≤ k'` using `by positivity`. Establish `hj0 : (0 : ℝ) ≤ j` using `by positivity`. Establish `ht0 : 0 ≤ t` using `by positivity`.

Establish `ht1 : t ≤ 1` using `by rw [ht, div_le_one (by positivity)]; linarith`. Establish `h1t : 1 - t ≤ (k' : ℝ) / al`. Establish `: 1 - t = (k' : ℝ) / ((al : ℝ) + j + 1 + k')` using `by rw [ht]; field_simp; ring`. Rewrite using `[this]`. Conclude with `div_le_div_of_nonneg_left hk0 hal' (by linarith)`.

Establish `hexp : 1 - (k' : ℝ) * (j + 1) / al = (1 - (k' : ℝ) * j / al) - k' / al` using `by ring`. Rewrite using `[hexp]`. Distinguish the cases in `ha : 1 - (k' : ℝ) * j / al ≤ 0`. Establish `: (0 : ℝ) ≤ k' / al` using `by positivity`. Use polynomial arithmetic with `[mul_nonneg hr0 ht0]`.

Rewrite using `[not_le] at ha set a := 1 - (k' : ℝ) * j / al`. Establish `ha1 : a ≤ 1`. Establish `: (0 : ℝ) ≤ k' * j / al` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h2 : a * t ≤ r * t` using `mul_le_mul_of_nonneg_right ih ht0`.

Establish `h3 : a * (1 - t) ≤ 1 - t` using `by nlinarith`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem binomial_ratio_bound : BinomRatio := by
  intro k' al j hal
  have hal' : (0 : ℝ) < al := by exact_mod_cast hal
  induction j with
  | zero => simp [div_self (dimPol_pos_real k' al).ne']
  | succ j ih =>
    have p0 := dimPol_pos_real k' (al + j)
    have pa := dimPol_pos_real k' al
    have hrec := dimPol_succ_eq_real k' (al + j)
    rw [show al + (j + 1) = al + j + 1 by omega, hrec]
    push_cast at ih ⊢
    set r : ℝ := (dimPol k' al : ℝ) / dimPol k' (al + j) with hr
    have hr0 : 0 ≤ r := by positivity
    have hkey : (dimPol k' al : ℝ) / (dimPol k' (al + j) * ((al : ℝ) + j + 1 + k') / ((al : ℝ) + j + 1))
        = r * (((al : ℝ) + j + 1) / ((al : ℝ) + j + 1 + k')) := by
      rw [hr]; field_simp
    rw [hkey]
    set t : ℝ := ((al : ℝ) + j + 1) / ((al : ℝ) + j + 1 + k') with ht
    have hk0 : (0 : ℝ) ≤ k' := by positivity
    have hj0 : (0 : ℝ) ≤ j := by positivity
    have ht0 : 0 ≤ t := by positivity
    have ht1 : t ≤ 1 := by rw [ht, div_le_one (by positivity)]; linarith
    have h1t : 1 - t ≤ (k' : ℝ) / al := by
      have : 1 - t = (k' : ℝ) / ((al : ℝ) + j + 1 + k') := by rw [ht]; field_simp; ring
      rw [this]
      exact div_le_div_of_nonneg_left hk0 hal' (by linarith)
    have hexp : 1 - (k' : ℝ) * (j + 1) / al = (1 - (k' : ℝ) * j / al) - k' / al := by ring
    rw [hexp]
    by_cases ha : 1 - (k' : ℝ) * j / al ≤ 0
    · have : (0 : ℝ) ≤ k' / al := by positivity
      nlinarith [mul_nonneg hr0 ht0]
    · rw [not_le] at ha
      set a := 1 - (k' : ℝ) * j / al
      have ha1 : a ≤ 1 := by
        have : (0 : ℝ) ≤ k' * j / al := by positivity
        linarith
      have h2 : a * t ≤ r * t := mul_le_mul_of_nonneg_right ih ht0
      have h3 : a * (1 - t) ≤ 1 - t := by nlinarith
      nlinarith

/- English proof (translation)
Establish `hk2 : (2 : ℝ) ≤ k'` using `by exact_mod_cast hk`. Establish `hk1 : (0 : ℝ) < (k' : ℝ) - 1` using `by linarith`. Establish `pB` using `dimPol_pos_real k' B`. Use `set g : ℕ → ℝ := fun n => (dimPol k' B : ℝ) * ((B : ℝ) + n + k') / (((k' : ℝ) - 1) * dimPol k' (B + n)) with hg`. Establish `hrec : ∀ n, (dimPol k' (B + (n + 1)) : ℝ) = dimPol k' (B + n) * ((B : ℝ) + n + 1 + k') / ((B : ℝ) + n + 1)`.

Introduce `n`. Rewrite using `[show B + (n + 1) = B + n + 1 by omega, dimPol_succ_eq_real]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hstep : ∀ n, (dimPol k' B : ℝ) / dimPol k' (B + n) = g n - g (n + 1)`.

Introduce `n`. Establish `p0` using `dimPol_pos_real k' (B + n)`. Simplify using `only [hg]`. Rewrite using `[hrec n]`. Use `push_cast`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hsucc : ∀ n, g (n + 1) * ((B : ℝ) + n + k') = g n * ((B : ℝ) + n + 1)`. Introduce `n`. Establish `p0` using `dimPol_pos_real k' (B + n)`.

Simplify using `only [hg]`. Rewrite using `[hrec n]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Establish `hg0 : ∀ n, 0 ≤ g n` using `by intro n; simp only [hg]; positivity`. Establish `hgzero : g 0 = ((B : ℝ) + k') / ((k' : ℝ) - 1)`. Simplify using `only [hg]`. Simplify using the standard rewrite rules. Clear the denominators using the available nonvanishing facts.

Establish `hinv : ∀ n, g n * ((B : ℝ) + n + k' - 1) ≤ g 0 * ((B : ℝ) + k' - 1)`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`.

Use `push_cast`. Establish `h1 : g (n + 1) * ((B : ℝ) + (n + 1) + k' - 1) = g n * ((B : ℝ) + n + 1)`. Rewrite using `[← hsucc n]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h1]`.

Establish `: g n * ((B : ℝ) + n + 1) ≤ g n * ((B : ℝ) + n + k' - 1)` using `mul_le_mul_of_nonneg_left (by linarith) (hg0 n)`. Combine the linear equalities and inequalities to obtain the conclusion. Use `set C := g 0 * ((B : ℝ) + k' - 1) with hC`. Establish `hbound : ∀ n, g n ≤ C * (1 / ((n : ℝ) + 1))`. Introduce `n`.

Establish `hpos : (0 : ℝ) < (n : ℝ) + 1` using `by positivity`. Establish `hle : (n : ℝ) + 1 ≤ (B : ℝ) + n + k' - 1`. Establish `: (0 : ℝ) ≤ B` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[mul_one_div, le_div_iff₀ hpos]`.

Combine the equalities or inequalities in the displayed calculation. Establish `htend : Tendsto g atTop (𝓝 0)`. Establish `h` using `(tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul C`. Rewrite `h` using `[mul_zero]`. Conclude with `squeeze_zero hg0 hbound h`.

Establish `hnn : ∀ j, 0 ≤ (dimPol k' B : ℝ) / dimPol k' (B + j)`. Introduce `j`. Use `dimPol_pos_real k' (B + j)` as an intermediate fact. Check the signs of the components of the expression. Rewrite using `[hasSum_iff_tendsto_nat_of_nonneg hnn]`.

Establish `hps : ∀ n, ∑ i ∈ range n, (dimPol k' B : ℝ) / dimPol k' (B + i) = g 0 - g n`. Introduce `n`. Rewrite using `[Finset.sum_congr rfl (fun i _ => hstep i), Finset.sum_range_sub']`. Repeatedly rewrite using `[hps]`. Rewrite using `[← hgzero]`.

Use `(tendsto_const_nhds (x := g 0)).sub htend` as an intermediate fact. Simplify using `using this`.
-/
theorem binomSeries_gen (k' B : ℕ) (hk : 2 ≤ k') :
    HasSum (fun j : ℕ => (dimPol k' B : ℝ) / dimPol k' (B + j)) (((B : ℝ) + k') / ((k' : ℝ) - 1)) := by
  have hk2 : (2 : ℝ) ≤ k' := by exact_mod_cast hk
  have hk1 : (0 : ℝ) < (k' : ℝ) - 1 := by linarith
  have pB := dimPol_pos_real k' B
  set g : ℕ → ℝ := fun n => (dimPol k' B : ℝ) * ((B : ℝ) + n + k') / (((k' : ℝ) - 1) * dimPol k' (B + n))
    with hg
  have hrec : ∀ n, (dimPol k' (B + (n + 1)) : ℝ)
      = dimPol k' (B + n) * ((B : ℝ) + n + 1 + k') / ((B : ℝ) + n + 1) := by
    intro n
    rw [show B + (n + 1) = B + n + 1 by omega, dimPol_succ_eq_real]
    push_cast; ring
  have hstep : ∀ n, (dimPol k' B : ℝ) / dimPol k' (B + n) = g n - g (n + 1) := by
    intro n
    have p0 := dimPol_pos_real k' (B + n)
    simp only [hg]
    rw [hrec n]
    push_cast
    field_simp
    ring
  have hsucc : ∀ n, g (n + 1) * ((B : ℝ) + n + k') = g n * ((B : ℝ) + n + 1) := by
    intro n
    have p0 := dimPol_pos_real k' (B + n)
    simp only [hg]
    rw [hrec n]
    push_cast
    field_simp
    ring
  have hg0 : ∀ n, 0 ≤ g n := by intro n; simp only [hg]; positivity
  have hgzero : g 0 = ((B : ℝ) + k') / ((k' : ℝ) - 1) := by
    simp only [hg]; simp; field_simp
  have hinv : ∀ n, g n * ((B : ℝ) + n + k' - 1) ≤ g 0 * ((B : ℝ) + k' - 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      push_cast
      have h1 : g (n + 1) * ((B : ℝ) + (n + 1) + k' - 1) = g n * ((B : ℝ) + n + 1) := by
        rw [← hsucc n]; ring
      rw [h1]
      have : g n * ((B : ℝ) + n + 1) ≤ g n * ((B : ℝ) + n + k' - 1) :=
        mul_le_mul_of_nonneg_left (by linarith) (hg0 n)
      linarith
  set C := g 0 * ((B : ℝ) + k' - 1) with hC
  have hbound : ∀ n, g n ≤ C * (1 / ((n : ℝ) + 1)) := by
    intro n
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hle : (n : ℝ) + 1 ≤ (B : ℝ) + n + k' - 1 := by
      have : (0 : ℝ) ≤ B := by positivity
      linarith
    rw [mul_one_div, le_div_iff₀ hpos]
    calc g n * ((n : ℝ) + 1) ≤ g n * ((B : ℝ) + n + k' - 1) :=
          mul_le_mul_of_nonneg_left hle (hg0 n)
      _ ≤ C := hinv n
  have htend : Tendsto g atTop (𝓝 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul C
    rw [mul_zero] at h
    exact squeeze_zero hg0 hbound h
  have hnn : ∀ j, 0 ≤ (dimPol k' B : ℝ) / dimPol k' (B + j) := by
    intro j; have := dimPol_pos_real k' (B + j); positivity
  rw [hasSum_iff_tendsto_nat_of_nonneg hnn]
  have hps : ∀ n, ∑ i ∈ range n, (dimPol k' B : ℝ) / dimPol k' (B + i) = g 0 - g n := by
    intro n
    rw [Finset.sum_congr rfl (fun i _ => hstep i), Finset.sum_range_sub']
  simp_rw [hps]
  rw [← hgzero]
  have := (tendsto_const_nhds (x := g 0)).sub htend
  simpa using this

/- English proof (translation)
Introduce `k' be hk`. Conclude with `binomSeries_gen k' be hk`.
-/
theorem binomial_series_bound : BinomSeries := by
  intro k' be hk
  exact binomSeries_gen k' be hk

/- English proof (translation)
Establish `hk1 : (1 : ℝ) ≤ k'` using `by exact_mod_cast hk`. Establish `pb` using `dimPol_pos_real k' be`. Introduce `J`. Proceed by induction on `J with`. Consider the case `zero`.

Introduce `_`. Establish `e : (dimPol k' be : ℝ) * ((be : ℝ) + k') / dimPol k' be = (be : ℝ) + k'`. Clear the denominators using the available nonvanishing facts. Simplify using `using e.le`. Consider the case `succ J ih`.

Introduce `hJ`. Move the coercions through the operations in `at hJ ⊢`. Establish `ihJ` using `ih (by linarith)`. Establish `p0` using `dimPol_pos_real k' (be + J)`. Establish `hrec : (dimPol k' (be + (J + 1)) : ℝ) = dimPol k' (be + J) * ((be : ℝ) + J + 1 + k') / ((be : ℝ) + J + 1)`.

Rewrite using `[show be + (J + 1) = be + J + 1 by omega, dimPol_succ_eq_real]; push_cast; ring`. Rewrite using `[hrec]`. Use `set q := (dimPol k' be : ℝ) * ((be : ℝ) + J + k') / dimPol k' (be + J) with hq`. Establish `hq0 : 0 ≤ q` using `by positivity`. Establish `hpos : (0 : ℝ) < (be : ℝ) + J + k'` using `by positivity`.

Establish `hid : (dimPol k' be : ℝ) * ((be : ℝ) + (J + 1) + k') / (dimPol k' (be + J) * ((be : ℝ) + J + 1 + k') / ((be : ℝ) + J + 1)) = q * (((be : ℝ) + J + 1) / ((be : ℝ) + J + k'))`. Rewrite using `[hq]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hid]`.

Use `set t := ((be : ℝ) + J + 1) / ((be : ℝ) + J + k') with ht`. Establish `ht0 : 0 ≤ t` using `by positivity`. Establish `ht1 : t ≤ Real.exp (-((k' : ℝ) - 1) / (2 * b'))`. Establish `h1 : t = 1 - ((k' : ℝ) - 1) / ((be : ℝ) + J + k')` using `by rw [ht]; field_simp; ring`. Establish `h2 : ((k' : ℝ) - 1) / (2 * b') ≤ ((k' : ℝ) - 1) / ((be : ℝ) + J + k')` using `div_le_div_of_nonneg_left (by linarith) hpos (by linarith)`.

Establish `h3` using `Real.add_one_le_exp (-(((k' : ℝ) - 1) / (2 * b')))`. Establish `h4 : -((k' : ℝ) - 1) / (2 * b') = -(((k' : ℝ) - 1) / (2 * b'))` using `by ring`. Rewrite using `[h1, h4]`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[mul_assoc, ← Real.exp_add]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem tail_q_bound (k' be : ℕ) (b' : ℝ) (hk : 1 ≤ k') (_hb : 0 < b') :
    ∀ J : ℕ, (be : ℝ) + J + k' ≤ 2 * b' →
      (dimPol k' be : ℝ) * ((be : ℝ) + J + k') / dimPol k' (be + J)
        ≤ ((be : ℝ) + k') * Real.exp (-((k' : ℝ) - 1) * J / (2 * b')) := by
  have hk1 : (1 : ℝ) ≤ k' := by exact_mod_cast hk
  have pb := dimPol_pos_real k' be
  intro J
  induction J with
  | zero =>
    intro _
    have e : (dimPol k' be : ℝ) * ((be : ℝ) + k') / dimPol k' be = (be : ℝ) + k' := by
      field_simp
    simpa using e.le
  | succ J ih =>
    intro hJ
    push_cast at hJ ⊢
    have ihJ := ih (by linarith)
    have p0 := dimPol_pos_real k' (be + J)
    have hrec : (dimPol k' (be + (J + 1)) : ℝ)
        = dimPol k' (be + J) * ((be : ℝ) + J + 1 + k') / ((be : ℝ) + J + 1) := by
      rw [show be + (J + 1) = be + J + 1 by omega, dimPol_succ_eq_real]; push_cast; ring
    rw [hrec]
    set q := (dimPol k' be : ℝ) * ((be : ℝ) + J + k') / dimPol k' (be + J) with hq
    have hq0 : 0 ≤ q := by positivity
    have hpos : (0 : ℝ) < (be : ℝ) + J + k' := by positivity
    have hid : (dimPol k' be : ℝ) * ((be : ℝ) + (J + 1) + k')
        / (dimPol k' (be + J) * ((be : ℝ) + J + 1 + k') / ((be : ℝ) + J + 1))
        = q * (((be : ℝ) + J + 1) / ((be : ℝ) + J + k')) := by
      rw [hq]; field_simp; ring
    rw [hid]
    set t := ((be : ℝ) + J + 1) / ((be : ℝ) + J + k') with ht
    have ht0 : 0 ≤ t := by positivity
    have ht1 : t ≤ Real.exp (-((k' : ℝ) - 1) / (2 * b')) := by
      have h1 : t = 1 - ((k' : ℝ) - 1) / ((be : ℝ) + J + k') := by rw [ht]; field_simp; ring
      have h2 : ((k' : ℝ) - 1) / (2 * b') ≤ ((k' : ℝ) - 1) / ((be : ℝ) + J + k') :=
        div_le_div_of_nonneg_left (by linarith) hpos (by linarith)
      have h3 := Real.add_one_le_exp (-(((k' : ℝ) - 1) / (2 * b')))
      have h4 : -((k' : ℝ) - 1) / (2 * b') = -(((k' : ℝ) - 1) / (2 * b')) := by ring
      rw [h1, h4]; linarith
    calc q * t ≤ (((be : ℝ) + k') * Real.exp (-((k' : ℝ) - 1) * J / (2 * b')))
          * Real.exp (-((k' : ℝ) - 1) / (2 * b')) :=
          mul_le_mul ihJ ht1 ht0 (by positivity)
      _ = ((be : ℝ) + k') * Real.exp (-((k' : ℝ) - 1) * (J + 1) / (2 * b')) := by
          rw [mul_assoc, ← Real.exp_add]; congr 2; ring

/- English proof (translation)
Introduce `k' be J La b' hk hb hLa hJ hwin`. Establish `hk2 : 2 ≤ k'` using `by omega`. Establish `hk5 : (5 : ℝ) ≤ k'` using `by exact_mod_cast hk`. Establish `hk1 : (0 : ℝ) < (k' : ℝ) - 1` using `by linarith`. Establish `hs` using `binomSeries_gen k' (be + J) hk2`.

Establish `pJ` using `dimPol_pos_real k' (be + J)`. Establish `pb` using `dimPol_pos_real k' be`. Establish `hs2` using `hs.mul_left ((dimPol k' be : ℝ) / dimPol k' (be + J))`. Establish `hfun : (fun j : ℕ => (dimPol k' be : ℝ) / dimPol k' (be + J) * ((dimPol k' (be + J) : ℝ) / dimPol k' (be + J + j))) = fun j => (dimPol k' be : ℝ) / dimPol k' (be + J + j)`. Use function extensionality and compare the values at `j`.

Use `dimPol_pos_real k' (be + J + j)` as an intermediate fact. Clear the denominators using the available nonvanishing facts. Rewrite `hs2` using `[hfun]`. Rewrite using `[hs2.tsum_eq]`. Establish `hq` using `tail_q_bound k' be b' (by omega) hb J (by linarith)`.

Establish `hJ0 : (0 : ℝ) ≤ J` using `by positivity`. Establish `hexp : Real.exp (-((k' : ℝ) - 1) * J / (2 * b')) ≤ Real.exp (-La / 3)`. Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises. Establish `h1 : La * b' ≤ J * ((k' : ℝ) + 1)`. Use `(div_le_iff₀ (by positivity : (0 : ℝ) < k' + 1)).mp hJ; linarith` as an intermediate fact.

Rewrite using `[div_le_div_iff₀ (by positivity) (by norm_num)]`. Use polynomial arithmetic with `[mul_nonneg hJ0 (sub_nonneg.mpr hk5)]`. Use `push_cast`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem binomial_tail_bound : BinomTail := by
  intro k' be J La b' hk hb hLa hJ hwin
  have hk2 : 2 ≤ k' := by omega
  have hk5 : (5 : ℝ) ≤ k' := by exact_mod_cast hk
  have hk1 : (0 : ℝ) < (k' : ℝ) - 1 := by linarith
  have hs := binomSeries_gen k' (be + J) hk2
  have pJ := dimPol_pos_real k' (be + J)
  have pb := dimPol_pos_real k' be
  have hs2 := hs.mul_left ((dimPol k' be : ℝ) / dimPol k' (be + J))
  have hfun : (fun j : ℕ => (dimPol k' be : ℝ) / dimPol k' (be + J)
      * ((dimPol k' (be + J) : ℝ) / dimPol k' (be + J + j)))
      = fun j => (dimPol k' be : ℝ) / dimPol k' (be + J + j) := by
    funext j; have := dimPol_pos_real k' (be + J + j); field_simp
  rw [hfun] at hs2
  rw [hs2.tsum_eq]
  have hq := tail_q_bound k' be b' (by omega) hb J (by linarith)
  have hJ0 : (0 : ℝ) ≤ J := by positivity
  have hexp : Real.exp (-((k' : ℝ) - 1) * J / (2 * b')) ≤ Real.exp (-La / 3) := by
    apply Real.exp_le_exp.mpr
    have h1 : La * b' ≤ J * ((k' : ℝ) + 1) := by
      have := (div_le_iff₀ (by positivity : (0 : ℝ) < k' + 1)).mp hJ; linarith
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [mul_nonneg hJ0 (sub_nonneg.mpr hk5)]
  push_cast
  calc (dimPol k' be : ℝ) / dimPol k' (be + J) * (((be : ℝ) + J + k') / ((k' : ℝ) - 1))
      = ((dimPol k' be : ℝ) * ((be : ℝ) + J + k') / dimPol k' (be + J)) / ((k' : ℝ) - 1) := by ring
    _ ≤ (((be : ℝ) + k') * Real.exp (-((k' : ℝ) - 1) * J / (2 * b'))) / ((k' : ℝ) - 1) :=
        div_le_div_of_nonneg_right hq hk1.le
    _ ≤ (((be : ℝ) + k') * Real.exp (-La / 3)) / ((k' : ℝ) - 1) := by
        gcongr
    _ = Real.exp (-La / 3) * (((be : ℝ) + k') / ((k' : ℝ) - 1)) := by ring

/- English proof (translation)
Establish `hk2 : (2 : ℝ) ≤ k'` using `by exact_mod_cast hk`. Establish `hk1 : (0 : ℝ) < (k' : ℝ) - 1` using `by linarith`. Establish `pa` using `dimPol_pos_real k' al`. Establish `pb` using `dimPol_pos_real k' be`. Break down `Nat.eq_zero_or_pos be with h0 | hbe` into its components or cases.

Substitute `h0` using the available equality. Establish `: dimHar k' al 0 = dimPol k' al * dimPol k' 0` using `by simp [dimHar]`. Rewrite using `[this]`. Use `push_cast`. Rewrite using `[div_self (by positivity), one_mul, le_div_iff₀ hk1]; simp`.

Take `⟨a0, rfl⟩ : ∃ a0, al = a0 + 1` from `⟨al - 1, by omega⟩`. Take `⟨b0, rfl⟩ : ∃ b0, be = b0 + 1` from `⟨be - 1, by omega⟩`. Establish `hle : dimPol k' a0 * dimPol k' b0 ≤ dimPol k' (a0 + 1) * dimPol k' (b0 + 1)`. Unfold `dimPol`. Conclude with `Nat.mul_le_mul (Nat.choose_le_choose _ (by omega)) (Nat.choose_le_choose _ (by omega))`.

Establish `hH : dimHar k' (a0 + 1) (b0 + 1) = dimPol k' (a0 + 1) * dimPol k' (b0 + 1) - dimPol k' a0 * dimPol k' b0`. Simplify using `[dimHar]`. Rewrite using `[hH, Nat.cast_sub hle]`. Use `push_cast`. Establish `p0` using `dimPol_pos_real k' a0`.

Establish `p1` using `dimPol_pos_real k' b0`. Establish `eX` using `dimPol_succ_mul_real k' a0`. Establish `eY` using `dimPol_succ_mul_real k' b0`. Use `set X := (dimPol k' (a0 + 1) : ℝ)`. Use `set Y := (dimPol k' (b0 + 1) : ℝ)`.

Use `set x := (dimPol k' a0 : ℝ)`. Use `set y := (dimPol k' b0 : ℝ)`. Establish `hA : (0 : ℝ) < (a0 : ℝ) + 1` using `by positivity`. Establish `hB0 : (0 : ℝ) ≤ (b0 : ℝ)` using `by positivity`. Establish `hXx : x ≤ X`.

Establish `: x * ((a0 : ℝ) + 1) ≤ X * ((a0 : ℝ) + 1)`. Rewrite using `[eX]`. Use the polynomial consequences of the given equalities and inequalities. Conclude with `le_of_mul_le_mul_right this hA`. Rewrite using `[div_mul_div_comm, one_le_div (by positivity)]`.

Establish `hYB : 0 ≤ Y * ((b0 : ℝ) + 1)` using `by positivity`. Establish `h1 : x * (Y * ((b0 : ℝ) + 1)) ≤ X * (Y * ((b0 : ℝ) + 1))` using `mul_le_mul_of_nonneg_right hXx hYB`. Establish `hXY : 0 ≤ X * Y` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem dimHar_ratio_ge (k' al be : ℕ) (hk : 2 ≤ k') (hal : 0 < al) :
    1 ≤ (dimHar k' al be : ℝ) / ((dimPol k' al : ℝ) * dimPol k' be)
      * (((be : ℝ) + k') / ((k' : ℝ) - 1)) := by
  have hk2 : (2 : ℝ) ≤ k' := by exact_mod_cast hk
  have hk1 : (0 : ℝ) < (k' : ℝ) - 1 := by linarith
  have pa := dimPol_pos_real k' al
  have pb := dimPol_pos_real k' be
  rcases Nat.eq_zero_or_pos be with h0 | hbe
  · subst h0
    have : dimHar k' al 0 = dimPol k' al * dimPol k' 0 := by simp [dimHar]
    rw [this]; push_cast
    rw [div_self (by positivity), one_mul, le_div_iff₀ hk1]; simp
  · obtain ⟨a0, rfl⟩ : ∃ a0, al = a0 + 1 := ⟨al - 1, by omega⟩
    obtain ⟨b0, rfl⟩ : ∃ b0, be = b0 + 1 := ⟨be - 1, by omega⟩
    have hle : dimPol k' a0 * dimPol k' b0 ≤ dimPol k' (a0 + 1) * dimPol k' (b0 + 1) := by
      unfold dimPol
      exact Nat.mul_le_mul (Nat.choose_le_choose _ (by omega)) (Nat.choose_le_choose _ (by omega))
    have hH : dimHar k' (a0 + 1) (b0 + 1)
        = dimPol k' (a0 + 1) * dimPol k' (b0 + 1) - dimPol k' a0 * dimPol k' b0 := by
      simp [dimHar]
    rw [hH, Nat.cast_sub hle]
    push_cast
    have p0 := dimPol_pos_real k' a0
    have p1 := dimPol_pos_real k' b0
    have eX := dimPol_succ_mul_real k' a0
    have eY := dimPol_succ_mul_real k' b0
    set X := (dimPol k' (a0 + 1) : ℝ)
    set Y := (dimPol k' (b0 + 1) : ℝ)
    set x := (dimPol k' a0 : ℝ)
    set y := (dimPol k' b0 : ℝ)
    have hA : (0 : ℝ) < (a0 : ℝ) + 1 := by positivity
    have hB0 : (0 : ℝ) ≤ (b0 : ℝ) := by positivity
    have hXx : x ≤ X := by
      have : x * ((a0 : ℝ) + 1) ≤ X * ((a0 : ℝ) + 1) := by
        rw [eX]; nlinarith
      exact le_of_mul_le_mul_right this hA
    rw [div_mul_div_comm, one_le_div (by positivity)]
    have hYB : 0 ≤ Y * ((b0 : ℝ) + 1) := by positivity
    have h1 : x * (Y * ((b0 : ℝ) + 1)) ≤ X * (Y * ((b0 : ℝ) + 1)) := mul_le_mul_of_nonneg_right hXx hYB
    have hXY : 0 ≤ X * Y := by positivity
    nlinarith

/- English proof (translation)
Introduce `k' al be La b' hk hal hb hLa hwin`. Use `set J0 : ℝ := La * b' / (k' + 1) with hJ0`. Use `set N : ℕ := ⌊J0⌋₊ + 1 with hN`. Establish `hk2 : 2 ≤ k'` using `by omega`. Establish `hk5 : (5 : ℝ) ≤ k'` using `by exact_mod_cast hk`.

Establish `hk1 : (0 : ℝ) < (k' : ℝ) - 1` using `by linarith`. Establish `hal' : (0 : ℝ) < al` using `by exact_mod_cast hal`. Establish `hJ00 : 0 ≤ J0` using `by positivity`. Establish `he0 : 0 ≤ 1 - Real.exp (-La / 3)`. Establish `: Real.exp (-La / 3) ≤ 1` using `Real.exp_le_one_iff.mpr (by linarith)`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `pa` using `dimPol_pos_real k' al`. Establish `pb` using `dimPol_pos_real k' be`. Establish `hH0 : (0 : ℝ) ≤ dimHar k' al be` using `by positivity`. Use `set h : ℝ := (dimHar k' al be : ℝ) / ((dimPol k' al : ℝ) * dimPol k' be) with hh`.

Establish `hh0 : 0 ≤ h` using `by positivity`. Establish `hhS` using `dimHar_ratio_ge k' al be hk2 hal`. Use `set S : ℝ := ((be : ℝ) + k') / ((k' : ℝ) - 1) with hS`. Use `set f : ℕ → ℝ := fun j => (dimPol k' be : ℝ) / dimPol k' (be + j) with hf`. Establish `hser : HasSum f S` using `binomSeries_gen k' be hk2`.

Establish `hNJ : J0 ≤ (N : ℝ)` using `by rw [hN]; push_cast; exact (Nat.lt_floor_add_one J0).le`. Establish `htail` using `binomial_tail_bound k' be N La b' hk hb hLa hNJ hwin`. Establish `hsplit` using `hser.summable.sum_add_tsum_nat_add N`. Establish `htail' : ∑' i, f (i + N) = ∑' j : ℕ, (dimPol k' be : ℝ) / dimPol k' (be + N + j)`. Use `congr 1; funext i; simp only [hf]; rw [show be + (i + N) = be + N + i by omega]`.

Rewrite `hsplit` using `[hser.tsum_eq, htail']`. Establish `hpart : S * (1 - Real.exp (-La / 3)) ≤ ∑ j ∈ range N, f j`. Establish `: Real.exp (-La / 3) * S = S * Real.exp (-La / 3)` using `by ring`. Use polynomial arithmetic with `[htail]`. Distinguish the cases in `ha : 1 - (k' : ℝ) * J0 / al ≤ 0`.

Establish `: (0 : ℝ) ≤ ∑ j ∈ range N, (dimHar k' al be : ℝ) / ((dimPol k' (al + j) : ℝ) * dimPol k' (be + j))`. Apply `Finset.sum_nonneg` to reduce the goal to its premises. Introduce `j _`. Use `dimPol_pos_real k' (al + j)` as an intermediate fact. Use `dimPol_pos_real k' (be + j)` as an intermediate fact.

Check the signs of the components of the expression. Use polynomial arithmetic with `[mul_nonneg (neg_nonneg.mpr ha) he0]`. Rewrite using `[not_le] at ha set a := 1 - (k' : ℝ) * J0 / al with hadef`. Establish `hterm : ∀ j ∈ range N, h * a * f j ≤ (dimHar k' al be : ℝ) / ((dimPol k' (al + j) : ℝ) * dimPol k' (be + j))`. Introduce `j hj`.

Establish `hjN : j < N` using `Finset.mem_range.mp hj`. Establish `hjJ : (j : ℝ) ≤ J0`. Establish `: j ≤ ⌊J0⌋₊` using `by omega`. Conclude with `(Nat.cast_le.mpr this).trans (Nat.floor_le hJ00)`. Establish `hr` using `binomial_ratio_bound k' al j hal`.

Establish `hra : a ≤ (dimPol k' al : ℝ) / dimPol k' (al + j)`. Use `le_trans ?_ hr` and prove the remaining obligations. Establish `: (k' : ℝ) * j / al ≤ (k' : ℝ) * J0 / al` using `by gcongr`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `p1` using `dimPol_pos_real k' (al + j)`.

Establish `p2` using `dimPol_pos_real k' (be + j)`. Establish `heq : (dimHar k' al be : ℝ) / ((dimPol k' (al + j) : ℝ) * dimPol k' (be + j)) = h * ((dimPol k' al : ℝ) / dimPol k' (al + j)) * f j`. Simplify using `only [hh, hf]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[heq]`.

Establish `hf0 : 0 ≤ f j` using `by simp only [hf]; positivity`. Conclude with `mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hra hh0) hf0`. Establish `hsum` using `Finset.sum_le_sum hterm`. Rewrite `hsum` using `[← Finset.mul_sum]`. Establish `h1 : h * a * (S * (1 - Real.exp (-La / 3))) ≤ h * a * ∑ j ∈ range N, f j` using `mul_le_mul_of_nonneg_left hpart (by positivity)`.

Establish `h2 : a * (1 - Real.exp (-La / 3)) ≤ h * a * (S * (1 - Real.exp (-La / 3)))`. Establish `e : h * a * (S * (1 - Real.exp (-La / 3))) = (h * S) * (a * (1 - Real.exp (-La / 3)))`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Establish `hae : 0 ≤ a * (1 - Real.exp (-La / 3))` using `mul_nonneg ha.le he0`.

Use the polynomial consequences of the given equalities and inequalities. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem density_lower_bound : DensityLower := by
  intro k' al be La b' hk hal hb hLa hwin
  set J0 : ℝ := La * b' / (k' + 1) with hJ0
  set N : ℕ := ⌊J0⌋₊ + 1 with hN
  have hk2 : 2 ≤ k' := by omega
  have hk5 : (5 : ℝ) ≤ k' := by exact_mod_cast hk
  have hk1 : (0 : ℝ) < (k' : ℝ) - 1 := by linarith
  have hal' : (0 : ℝ) < al := by exact_mod_cast hal
  have hJ00 : 0 ≤ J0 := by positivity
  have he0 : 0 ≤ 1 - Real.exp (-La / 3) := by
    have : Real.exp (-La / 3) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    linarith
  have pa := dimPol_pos_real k' al
  have pb := dimPol_pos_real k' be
  have hH0 : (0 : ℝ) ≤ dimHar k' al be := by positivity
  set h : ℝ := (dimHar k' al be : ℝ) / ((dimPol k' al : ℝ) * dimPol k' be) with hh
  have hh0 : 0 ≤ h := by positivity
  have hhS := dimHar_ratio_ge k' al be hk2 hal
  set S : ℝ := ((be : ℝ) + k') / ((k' : ℝ) - 1) with hS
  set f : ℕ → ℝ := fun j => (dimPol k' be : ℝ) / dimPol k' (be + j) with hf
  have hser : HasSum f S := binomSeries_gen k' be hk2
  have hNJ : J0 ≤ (N : ℝ) := by rw [hN]; push_cast; exact (Nat.lt_floor_add_one J0).le
  have htail := binomial_tail_bound k' be N La b' hk hb hLa hNJ hwin
  have hsplit := hser.summable.sum_add_tsum_nat_add N
  have htail' : ∑' i, f (i + N) = ∑' j : ℕ, (dimPol k' be : ℝ) / dimPol k' (be + N + j) := by
    congr 1; funext i; simp only [hf]; rw [show be + (i + N) = be + N + i by omega]
  rw [hser.tsum_eq, htail'] at hsplit
  have hpart : S * (1 - Real.exp (-La / 3)) ≤ ∑ j ∈ range N, f j := by
    have : Real.exp (-La / 3) * S = S * Real.exp (-La / 3) := by ring
    nlinarith [htail]
  by_cases ha : 1 - (k' : ℝ) * J0 / al ≤ 0
  · have : (0 : ℝ) ≤ ∑ j ∈ range N,
        (dimHar k' al be : ℝ) / ((dimPol k' (al + j) : ℝ) * dimPol k' (be + j)) := by
      apply Finset.sum_nonneg; intro j _
      have := dimPol_pos_real k' (al + j); have := dimPol_pos_real k' (be + j); positivity
    nlinarith [mul_nonneg (neg_nonneg.mpr ha) he0]
  · rw [not_le] at ha
    set a := 1 - (k' : ℝ) * J0 / al with hadef
    have hterm : ∀ j ∈ range N, h * a * f j
        ≤ (dimHar k' al be : ℝ) / ((dimPol k' (al + j) : ℝ) * dimPol k' (be + j)) := by
      intro j hj
      have hjN : j < N := Finset.mem_range.mp hj
      have hjJ : (j : ℝ) ≤ J0 := by
        have : j ≤ ⌊J0⌋₊ := by omega
        exact (Nat.cast_le.mpr this).trans (Nat.floor_le hJ00)
      have hr := binomial_ratio_bound k' al j hal
      have hra : a ≤ (dimPol k' al : ℝ) / dimPol k' (al + j) := by
        refine le_trans ?_ hr
        have : (k' : ℝ) * j / al ≤ (k' : ℝ) * J0 / al := by gcongr
        linarith
      have p1 := dimPol_pos_real k' (al + j)
      have p2 := dimPol_pos_real k' (be + j)
      have heq : (dimHar k' al be : ℝ) / ((dimPol k' (al + j) : ℝ) * dimPol k' (be + j))
          = h * ((dimPol k' al : ℝ) / dimPol k' (al + j)) * f j := by
        simp only [hh, hf]; field_simp
      rw [heq]
      have hf0 : 0 ≤ f j := by simp only [hf]; positivity
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hra hh0) hf0
    have hsum := Finset.sum_le_sum hterm
    rw [← Finset.mul_sum] at hsum
    have h1 : h * a * (S * (1 - Real.exp (-La / 3))) ≤ h * a * ∑ j ∈ range N, f j :=
      mul_le_mul_of_nonneg_left hpart (by positivity)
    have h2 : a * (1 - Real.exp (-La / 3)) ≤ h * a * (S * (1 - Real.exp (-La / 3))) := by
      have e : h * a * (S * (1 - Real.exp (-La / 3))) = (h * S) * (a * (1 - Real.exp (-La / 3))) := by
        ring
      rw [e]
      have hae : 0 ≤ a * (1 - Real.exp (-La / 3)) := mul_nonneg ha.le he0
      nlinarith
    linarith

end Formalism.CountingSumsFrames
