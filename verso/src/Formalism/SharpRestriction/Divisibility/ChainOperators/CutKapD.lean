import Mathlib
import Formalism.SharpRestriction.Divisibility.RankTruncation.KapDLemmaBridge

namespace Formalism.MainNotions.DIV.CutKapD

open Finset ConditionalKappaBounds.KapD

def bbF (m : ℕ) (b : Fin m → ℚ) (n : ℕ) : ℚ := if h : n < m then b ⟨n, h⟩ else 0

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih => rw [sum_range_succ, ih]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
lemma aff (e X Y : ℚ) : ∀ n : ℕ, ∑ i ∈ range n, (e - (X - 1 - 2 * (i : ℚ)) / 2 - Y / 2) =
    n * e - n * (X - 1) / 2 + n * (n - 1) / 2 - n * Y / 2 := by
  intro n
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih]; push_cast; ring

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih => rw [sum_range_succ, ih]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
lemma aff2 (e T : ℚ) : ∀ n : ℕ, ∑ c ∈ range n, (-e - (T + 1 + 2 * (c : ℚ)) / 2) =
    -(n * e) - n * (n + T) / 2 := by
  intro n
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih]; push_cast; ring

/- English proof (translation)
Establish `hs : ∀ i : ℕ, aPlusC k m t j v b e i = sigParC k m v b i + (e - (((k + m - 1 + t : ℕ) : ℚ) - 1 - 2 * (i : ℚ)) / 2 - (((k : ℚ) + j - 1) - ((m : ℚ) - j)) / 2)`. Introduce `i`. Unfold `aPlusC`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Fin.sum_univ_eq_sum_range (fun i => aPlusC k m t j v b e i) (k + j - 1)]`.

Rewrite using `[sum_congr rfl (fun i _ => hs i), sum_add_distrib, aff]`. Establish `e1 : k + j - 1 = (k - 1) + j` using `by omega`. Rewrite using `[e1, sum_range_add]`. Establish `h1 : ∑ i ∈ range (k - 1), sigParC k m v b i = ∑ i : Fin (k - 1), v i`. Rewrite using `[← Fin.sum_univ_eq_sum_range (fun i => sigParC k m v b i)]`.

Use `sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `[sigParC, i.2]`. Establish `h2 : ∑ x ∈ range j, sigParC k m v b (k - 1 + x) = -∑ x ∈ range j, bbF m b x`. Rewrite using `[← sum_neg_distrib]`. Use `sum_congr rfl fun x hx => ?_` and prove the remaining obligations.

Establish `hx' : x < m` using `lt_of_lt_of_le (mem_range.mp hx) hj`. Simplify using `[sigParC, bbF, hx']`. Rewrite using `[h1, h2]`. Establish `c1 : ((k + m - 1 + t : ℕ) : ℚ) = (k : ℚ) + m - 1 + t`. Rewrite using `[Nat.cast_add, Nat.cast_sub (by omega)]; push_cast; ring`.

Establish `c2 : ((k - 1 + j : ℕ) : ℚ) = (k : ℚ) - 1 + j`. Rewrite using `[Nat.cast_add, Nat.cast_sub hk]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[c1, c2]`.

Expand and normalize the polynomial expressions, which then agree.
-/
lemma plusSum (k m t j : ℕ) (hk : 1 ≤ k) (hj : j ≤ m) (v : Fin (k - 1) → ℚ) (b : Fin m → ℚ) (e : ℚ) :
    ∑ i : Fin (k + j - 1), aPlusC k m t j v b e i =
      (∑ i : Fin (k - 1), v i) - (∑ x ∈ range j, bbF m b x) +
        ((k + j - 1 : ℕ) : ℚ) * e - ((k + j - 1 : ℕ) : ℚ) * (((k + j - 1 : ℕ) : ℚ) + t) / 2 := by
  have hs : ∀ i : ℕ, aPlusC k m t j v b e i = sigParC k m v b i +
      (e - (((k + m - 1 + t : ℕ) : ℚ) - 1 - 2 * (i : ℚ)) / 2 - (((k : ℚ) + j - 1) - ((m : ℚ) - j)) / 2) := by
    intro i; unfold aPlusC; ring
  rw [Fin.sum_univ_eq_sum_range (fun i => aPlusC k m t j v b e i) (k + j - 1)]
  rw [sum_congr rfl (fun i _ => hs i), sum_add_distrib, aff]
  have e1 : k + j - 1 = (k - 1) + j := by omega
  rw [e1, sum_range_add]
  have h1 : ∑ i ∈ range (k - 1), sigParC k m v b i = ∑ i : Fin (k - 1), v i := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => sigParC k m v b i)]
    refine sum_congr rfl fun i _ => ?_
    simp [sigParC, i.2]
  have h2 : ∑ x ∈ range j, sigParC k m v b (k - 1 + x) = -∑ x ∈ range j, bbF m b x := by
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun x hx => ?_
    have hx' : x < m := lt_of_lt_of_le (mem_range.mp hx) hj
    simp [sigParC, bbF, hx']
  rw [h1, h2]
  have c1 : ((k + m - 1 + t : ℕ) : ℚ) = (k : ℚ) + m - 1 + t := by
    rw [Nat.cast_add, Nat.cast_sub (by omega)]; push_cast; ring
  have c2 : ((k - 1 + j : ℕ) : ℚ) = (k : ℚ) - 1 + j := by
    rw [Nat.cast_add, Nat.cast_sub hk]; push_cast; ring
  rw [c1, c2]
  ring

/- English proof (translation)
Rewrite using `[Fin.sum_univ_eq_sum_range (fun c => aMinusC m t j b e c) (m - j)]`. Establish `hs : ∀ c : ℕ, aMinusC m t j b e c = bbF m b (j + c) + (-e - ((t : ℚ) + 1 + 2 * (c : ℚ)) / 2)`. Introduce `c`. Unfold `aMinusC bbF`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[sum_congr rfl (fun c _ => hs c), sum_add_distrib, aff2]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma minusSum (m t j : ℕ) (b : Fin m → ℚ) (e : ℚ) :
    ∑ c : Fin (m - j), aMinusC m t j b e c =
      (∑ c ∈ range (m - j), bbF m b (j + c)) - ((m - j : ℕ) : ℚ) * e -
        ((m - j : ℕ) : ℚ) * (((m - j : ℕ) : ℚ) + t) / 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun c => aMinusC m t j b e c) (m - j)]
  have hs : ∀ c : ℕ, aMinusC m t j b e c = bbF m b (j + c) + (-e - ((t : ℚ) + 1 + 2 * (c : ℚ)) / 2) := by
    intro c; unfold aMinusC bbF; ring
  rw [sum_congr rfl (fun c _ => hs c), sum_add_distrib, aff2]
  ring

/- English proof (translation)
Use `⟨3, ?_⟩` and prove the remaining obligations. Introduce `k m t j hk hj1 hjm v b e S η hv hb`. Establish `hk1 : 1 ≤ k` using `by omega`. Establish `i0 : 0 < k - 1` using `by omega`. Establish `hS : 0 ≤ S` using `le_trans (hv ⟨0, i0⟩).1 (hv ⟨0, i0⟩).2`.

Establish `hη : 0 ≤ η` using `le_trans (abs_nonneg _) (hb ⟨0, by omega⟩)`. Establish `hid : (∑ i : Fin (k + j - 1), aPlusC k m t j v b e i) + (∑ c : Fin (m - j), aMinusC m t j b e c) - ((k : ℚ) - 1) * e = (∑ i : Fin (k - 1), v i) + (∑ x ∈ range j, (e - bbF m b x)) + (∑ c ∈ range (m - j), (bbF m b (j + c) - e)) - (((k + j - 1 : ℕ) : ℚ) * (((k + j - 1 : ℕ) : ℚ) + t) …`. Rewrite using `[plusSum k m t j hk1 hjm v b e, minusSum m t j b e, sum_sub_distrib, sum_sub_distrib]`. Simplify using `only [sum_const, card_range, nsmul_eq_mul]`. Establish `c1 : ((k + j - 1 : ℕ) : ℚ) = (k : ℚ) - 1 + j`.

Rewrite using `[Nat.cast_sub (by omega)]; push_cast; ring`. Establish `c2 : ((m - j : ℕ) : ℚ) = (m : ℚ) - j` using `Nat.cast_sub hjm`. Rewrite using `[c1, c2]`. Expand and normalize the polynomial expressions, which then agree. Establish `hre : ((((∑ i : Fin (k + j - 1), aPlusC k m t j v b e i) + ∑ c : Fin (m - j), aMinusC m t j b e c : ℚ)) : ℝ) - ((k : ℝ) - 1) * ((e : ℚ) : ℝ) = (((∑ i : Fin (k + j - 1), aPlusC k m t j v b e i) + (∑ c : Fin (m - j), aMinusC m t j b e c) - ((k : ℚ) - 1) * e : ℚ) : ℝ)` using `by push_cast; ring`.

Rewrite using `[hre, hid]`. Take `⟨p, hp⟩ : ∃ p, k + j - 1 = p` from `⟨_, rfl⟩`. Take `⟨q, hq⟩ : ∃ q, m - j = q` from `⟨_, rfl⟩`. Rewrite using `[hp, hq]`. Use `set A : ℚ := ∑ i : Fin (k - 1), v i with hA`.

Use `set B1 : ℚ := ∑ x ∈ range j, (e - bbF m b x) with hB1`. Use `set B2 : ℚ := ∑ c ∈ range q, (bbF m b (j + c) - e) with hB2`. Establish `hA0 : 0 ≤ (A : ℝ)`. Rewrite using `[hA]`. Use `push_cast`.

Conclude with `sum_nonneg fun i _ => (hv i).1`. Establish `hA1 : (A : ℝ) ≤ ((k : ℝ) - 1) * S`. Rewrite using `[hA]`. Use `push_cast`. Combine the equalities or inequalities in the displayed calculation.

Establish `hB1' : |(B1 : ℝ)| ≤ (j : ℝ) * η`. Rewrite using `[hB1]`. Use `push_cast`. Combine the equalities or inequalities in the displayed calculation. Use `sum_le_sum fun x hx => ?_` and prove the remaining obligations.

Establish `hx' : x < m` using `lt_of_lt_of_le (mem_range.mp hx) hjm`. Use `hb ⟨x, hx'⟩` as an intermediate fact. Rewrite using `[abs_sub_comm]`. Simplify `this` using `[bbF, hx']`. Use `_ = (j : ℝ) * η := by simp`.

Establish `hB2' : |(B2 : ℝ)| ≤ (q : ℝ) * η`. Rewrite using `[hB2]`. Use `push_cast`. Combine the equalities or inequalities in the displayed calculation. Use `sum_le_sum fun c hc => ?_` and prove the remaining obligations.

Establish `hc' : j + c < m` using `by have := mem_range.mp hc; omega`. Use `hb ⟨j + c, hc'⟩` as an intermediate fact. Simplify `this` using `[bbF, hc']`. Use `_ = (q : ℝ) * η := by simp`. Establish `hn : p * (p + t) + q * (q + t) ≤ 3 * (k * ((k + m * (t + 1)) + t))`.

Establish `hm : m ≤ m * (t + 1)` using `by nlinarith`. Establish `a1 : p * (p + t) ≤ (2 * k) * ((k + m * (t + 1)) + t)` using `Nat.mul_le_mul (by omega) (by omega)`. Establish `a2 : q * (q + t) ≤ k * ((k + m * (t + 1)) + t)` using `Nat.mul_le_mul (by omega) (by omega)`. Use the polynomial consequences of the given equalities and inequalities. Establish `hnR : (p : ℝ) * ((p : ℝ) + t) + (q : ℝ) * ((q : ℝ) + t) ≤ 3 * ((k : ℝ) * (((k : ℝ) + m * (t + 1)) + t))`.

Conclude with `hn` after adjusting the coercions. Establish `hsh0 : 0 ≤ (p : ℝ) * ((p : ℝ) + t) + (q : ℝ) * ((q : ℝ) + t)` using `by positivity`. Establish `hqm : (q : ℝ) + j = m` using `by exact_mod_cast (show q + j = m by omega)`. Use `push_cast`. Rewrite `hB1'`, `hB2'`, the goal using `[abs_le]`.

Apply the tactic sequence `constructor <;> nlinarith [hB1'.1, hB1'.2, hB2'.1, hB2'.2]`.
-/
theorem dprop_true : DProp := by
  refine ⟨3, ?_⟩
  intro k m t j hk hj1 hjm v b e S η hv hb
  have hk1 : 1 ≤ k := by omega
  have i0 : 0 < k - 1 := by omega
  have hS : 0 ≤ S := le_trans (hv ⟨0, i0⟩).1 (hv ⟨0, i0⟩).2
  have hη : 0 ≤ η := le_trans (abs_nonneg _) (hb ⟨0, by omega⟩)
  have hid : (∑ i : Fin (k + j - 1), aPlusC k m t j v b e i) + (∑ c : Fin (m - j), aMinusC m t j b e c) -
      ((k : ℚ) - 1) * e =
      (∑ i : Fin (k - 1), v i) + (∑ x ∈ range j, (e - bbF m b x)) +
        (∑ c ∈ range (m - j), (bbF m b (j + c) - e)) -
        (((k + j - 1 : ℕ) : ℚ) * (((k + j - 1 : ℕ) : ℚ) + t) + ((m - j : ℕ) : ℚ) * (((m - j : ℕ) : ℚ) + t)) / 2 := by
    rw [plusSum k m t j hk1 hjm v b e, minusSum m t j b e, sum_sub_distrib, sum_sub_distrib]
    simp only [sum_const, card_range, nsmul_eq_mul]
    have c1 : ((k + j - 1 : ℕ) : ℚ) = (k : ℚ) - 1 + j := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    have c2 : ((m - j : ℕ) : ℚ) = (m : ℚ) - j := Nat.cast_sub hjm
    rw [c1, c2]
    ring
  have hre : ((((∑ i : Fin (k + j - 1), aPlusC k m t j v b e i) + ∑ c : Fin (m - j), aMinusC m t j b e c : ℚ)) : ℝ) -
      ((k : ℝ) - 1) * ((e : ℚ) : ℝ) =
      (((∑ i : Fin (k + j - 1), aPlusC k m t j v b e i) + (∑ c : Fin (m - j), aMinusC m t j b e c) -
        ((k : ℚ) - 1) * e : ℚ) : ℝ) := by push_cast; ring
  rw [hre, hid]
  obtain ⟨p, hp⟩ : ∃ p, k + j - 1 = p := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, m - j = q := ⟨_, rfl⟩
  rw [hp, hq]

  set A : ℚ := ∑ i : Fin (k - 1), v i with hA
  set B1 : ℚ := ∑ x ∈ range j, (e - bbF m b x) with hB1
  set B2 : ℚ := ∑ c ∈ range q, (bbF m b (j + c) - e) with hB2
  have hA0 : 0 ≤ (A : ℝ) := by
    rw [hA]; push_cast; exact sum_nonneg fun i _ => (hv i).1
  have hA1 : (A : ℝ) ≤ ((k : ℝ) - 1) * S := by
    rw [hA]; push_cast
    calc ∑ i : Fin (k - 1), ((v i : ℚ) : ℝ) ≤ ∑ _i : Fin (k - 1), S := sum_le_sum fun i _ => (hv i).2
      _ = ((k - 1 : ℕ) : ℝ) * S := by simp
      _ = ((k : ℝ) - 1) * S := by rw [Nat.cast_sub hk1]; push_cast; ring
  have hB1' : |(B1 : ℝ)| ≤ (j : ℝ) * η := by
    rw [hB1]; push_cast
    calc |∑ x ∈ range j, (((e : ℚ) : ℝ) - ((bbF m b x : ℚ) : ℝ))|
        ≤ ∑ x ∈ range j, |((e : ℚ) : ℝ) - ((bbF m b x : ℚ) : ℝ)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _x ∈ range j, η := by
          refine sum_le_sum fun x hx => ?_
          have hx' : x < m := lt_of_lt_of_le (mem_range.mp hx) hjm
          have := hb ⟨x, hx'⟩
          rw [abs_sub_comm]
          simpa [bbF, hx'] using this
      _ = (j : ℝ) * η := by simp
  have hB2' : |(B2 : ℝ)| ≤ (q : ℝ) * η := by
    rw [hB2]; push_cast
    calc |∑ c ∈ range q, (((bbF m b (j + c) : ℚ) : ℝ) - ((e : ℚ) : ℝ))|
        ≤ ∑ c ∈ range q, |((bbF m b (j + c) : ℚ) : ℝ) - ((e : ℚ) : ℝ)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _c ∈ range q, η := by
          refine sum_le_sum fun c hc => ?_
          have hc' : j + c < m := by have := mem_range.mp hc; omega
          have := hb ⟨j + c, hc'⟩
          simpa [bbF, hc'] using this
      _ = (q : ℝ) * η := by simp
  have hn : p * (p + t) + q * (q + t) ≤ 3 * (k * ((k + m * (t + 1)) + t)) := by
    have hm : m ≤ m * (t + 1) := by nlinarith
    have a1 : p * (p + t) ≤ (2 * k) * ((k + m * (t + 1)) + t) := Nat.mul_le_mul (by omega) (by omega)
    have a2 : q * (q + t) ≤ k * ((k + m * (t + 1)) + t) := Nat.mul_le_mul (by omega) (by omega)
    nlinarith
  have hnR : (p : ℝ) * ((p : ℝ) + t) + (q : ℝ) * ((q : ℝ) + t) ≤ 3 * ((k : ℝ) * (((k : ℝ) + m * (t + 1)) + t)) := by
    exact_mod_cast hn
  have hsh0 : 0 ≤ (p : ℝ) * ((p : ℝ) + t) + (q : ℝ) * ((q : ℝ) + t) := by positivity
  have hqm : (q : ℝ) + j = m := by exact_mod_cast (show q + j = m by omega)
  push_cast
  rw [abs_le] at hB1' hB2' ⊢
  constructor <;> nlinarith [hB1'.1, hB1'.2, hB2'.1, hB2'.2]

/- English proof (translation)
The claim follows from `ConditionalKappaBounds.KapD.kappa_bound_of_prop dprop_true`.
-/
theorem kappa_degree_bound_holds : ∃ C : ℝ, ∀ (D : Formalism.BasicNotions.D7) (L : Formalism.BasicNotions.SizeData₂ D), Formalism.MainNotions.LiftErrorLocal.ThetaAdjointPositiveScalar D L C :=
  ConditionalKappaBounds.KapD.kappa_bound_of_prop dprop_true

end Formalism.MainNotions.DIV.CutKapD
