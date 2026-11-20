import Formalism.HermitianCurvature.StatementSz

namespace Formalism.FourierDecayAlt.P.Sz3

open Finset Formalism.FourierDecayAlt.Sz

/- English proof (translation)
Introduce `j' hjj'`. Proceed by induction on `j', hjj' using Nat.le_induction with`. Consider the case `base`. Introduce `h`. Use `hc.hgap j hj (by omega)` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Consider the case `succ n hn ih`. Introduce `h`. Establish `h1` using `ih (by omega)`. Establish `h2` using `hc.hgap n (by omega) (by omega)`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma b_lt (c : Cfg) (hc : c.Ok) (j : ℕ) (hj : 1 ≤ j) :
    ∀ j' : ℕ, j < j' → j' ≤ c.m → c.b j < c.b j' := by
  intro j' hjj'
  induction j', hjj' using Nat.le_induction with
  | base =>
    intro h
    have := hc.hgap j hj (by omega)
    linarith
  | succ n hn ih =>
    intro h
    have h1 := ih (by omega)
    have h2 := hc.hgap n (by omega) (by omega)
    linarith

/- English proof (translation)
Break down `Nat.eq_or_lt_of_le hj with h | h` into its components or cases. Rewrite using `[← h]`. Conclude with `hc.hb1`. Use `b_lt c hc 1 le_rfl j h hjm` as an intermediate fact. Combine the linear relations using `[hc.hb1]`.
-/
lemma b_ge_one (c : Cfg) (hc : c.Ok) (j : ℕ) (hj : 1 ≤ j) (hjm : j ≤ c.m) : 1 ≤ c.b j := by
  rcases Nat.eq_or_lt_of_le hj with h | h
  · rw [← h]; exact hc.hb1
  · have := b_lt c hc 1 le_rfl j h hjm
    linarith [hc.hb1]

end Formalism.FourierDecayAlt.P.Sz3

namespace Formalism.FourierDecayAlt.P

open Finset Formalism.FourierDecayAlt.Sz

/- English proof (translation)
Introduce `c de hc hw`. Take `⟨hk, hm, hDel, hv0, hv1, hb1, hgap, ha, htop⟩` from `hc`. Establish `hkR : (4 : ℝ) ≤ c.k` using `by exact_mod_cast hk`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `i hi1 hik`.

Establish `hl : c.lam i = c.v i` using `by simp [Cfg.lam, hik]`. Rewrite using `[hl]`. Prove the components needed by the constructor for the conclusion. Distinguish the cases in `h1 : i = 1`. Substitute `h1` using the available equality.

Establish `: c.u de 1 = c.a` using `by simp [Cfg.u]`. Rewrite using `[this]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hne : i ≠ c.k` using `by omega`. Establish `: c.u de i = c.v (i - 1) - 1 / 2 - de (i - 1) * c.Del` using `by simp [Cfg.u, h1, hne]`.

Rewrite using `[this]`. Establish `hc1 : ((i - 1 : ℕ) : ℝ) = (i : ℝ) - 1`. Rewrite using `[Nat.cast_sub hi1]`. Simplify using the standard rewrite rules. Unfold `Cfg.v`.

Rewrite using `[hc1]`. Apply the tactic sequence `rcases hw.1 (i - 1) with h | h <;> rw [h] <;> nlinarith`. Establish `h1 : i + 1 ≠ 1` using `by omega`. Distinguish the cases in `hlast : i + 1 = c.k`. Establish `: c.u de (i + 1) = c.ulast`.

Unfold `Cfg.u`. Rewrite using `[if_neg h1, if_pos hlast]`. Rewrite using `[this]`. Establish `hiR : (i : ℝ) + 1 = c.k` using `by exact_mod_cast hlast`. Establish `hvi : c.v i = c.vlast` using `by unfold Cfg.v; rw [← hiR]; ring`.

Rewrite using `[hvi]`. Unfold `Cfg.ulast`. Distinguish the cases in `ht : c.top = true`. Use `htop ht` as an intermediate fact. Simplify using `[ht]`.

Combine the linear relations using `[this.1]`. Simplify using `[ht]`. Establish `: c.u de (i + 1) = c.v i - 1 / 2 - de i * c.Del`. Unfold `Cfg.u`. Rewrite using `[if_neg h1, if_neg hlast]`.

Simplify using the standard rewrite rules. Rewrite using `[this]`. Apply the tactic sequence `rcases hw.1 i with h | h <;> rw [h] <;> nlinarith`. Establish `hl : c.lam c.k = -c.b 1` using `by simp [Cfg.lam]`. Establish `hu : c.u de c.k = c.ulast`.

Establish `: c.k ≠ 1` using `by omega`. Simplify using `[Cfg.u, this]`. Rewrite using `[hl, hu]`. Unfold `Cfg.ulast`. Distinguish the cases in `ht : c.top = true`.

Use `htop ht` as an intermediate fact. Simplify using `[ht]`. Combine the linear relations using `[this.2]`. Simplify using `[ht]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem interlacing : Formalism.FourierDecayAlt.Sz.Interlacing := by
  intro c de hc hw
  obtain ⟨hk, hm, hDel, hv0, hv1, hb1, hgap, ha, htop⟩ := hc
  have hkR : (4 : ℝ) ≤ c.k := by exact_mod_cast hk
  refine ⟨?_, ?_⟩
  · intro i hi1 hik
    have hl : c.lam i = c.v i := by simp [Cfg.lam, hik]
    rw [hl]
    constructor
    · by_cases h1 : i = 1
      · subst h1
        have : c.u de 1 = c.a := by simp [Cfg.u]
        rw [this]; nlinarith
      · have hne : i ≠ c.k := by omega
        have : c.u de i = c.v (i - 1) - 1 / 2 - de (i - 1) * c.Del := by simp [Cfg.u, h1, hne]
        rw [this]
        have hc1 : ((i - 1 : ℕ) : ℝ) = (i : ℝ) - 1 := by
          rw [Nat.cast_sub hi1]; simp
        unfold Cfg.v; rw [hc1]
        rcases hw.1 (i - 1) with h | h <;> rw [h] <;> nlinarith
    · have h1 : i + 1 ≠ 1 := by omega
      by_cases hlast : i + 1 = c.k
      · have : c.u de (i + 1) = c.ulast := by
          unfold Cfg.u; rw [if_neg h1, if_pos hlast]
        rw [this]
        have hiR : (i : ℝ) + 1 = c.k := by exact_mod_cast hlast
        have hvi : c.v i = c.vlast := by unfold Cfg.v; rw [← hiR]; ring
        rw [hvi]; unfold Cfg.ulast
        by_cases ht : c.top = true
        · have := htop ht; simp [ht]; linarith [this.1]
        · simp [ht]
      · have : c.u de (i + 1) = c.v i - 1 / 2 - de i * c.Del := by
          unfold Cfg.u; rw [if_neg h1, if_neg hlast]; simp
        rw [this]
        rcases hw.1 i with h | h <;> rw [h] <;> nlinarith
  · have hl : c.lam c.k = -c.b 1 := by simp [Cfg.lam]
    have hu : c.u de c.k = c.ulast := by
      have : c.k ≠ 1 := by omega
      simp [Cfg.u, this]
    rw [hl, hu]; unfold Cfg.ulast
    by_cases ht : c.top = true
    · have := htop ht; simp [ht]; linarith [this.2]
    · simp [ht]; linarith

/- English proof (translation)
Introduce `c hc s t hs hst ht`. Establish `hDel` using `hc.hDel`. Establish `hstR : (s : ℝ) + 1 ≤ (t : ℝ)` using `by exact_mod_cast hst`. Distinguish the cases in `htk : t < c.k`. Establish `hsk : s < c.k` using `by omega`.

Establish `h1 : c.lam t = c.v t` using `by simp [Cfg.lam, htk]`. Establish `h2 : c.lam s = c.v s` using `by simp [Cfg.lam, hsk]`. Rewrite using `[h1, h2]`. Unfold `Cfg.v`. Use the polynomial consequences of the given equalities and inequalities.

Establish `h1 : c.lam t = -c.b (t + 1 - c.k)` using `by simp [Cfg.lam, htk]`. Rewrite using `[h1]`. Distinguish the cases in `hsk : s < c.k`. Establish `h2 : c.lam s = c.v s` using `by simp [Cfg.lam, hsk]`. Rewrite using `[h2]`.

Establish `hb` using `Sz3.b_ge_one c hc (t + 1 - c.k) (by omega) (by omega)`. Establish `hskR : (s : ℝ) + 1 ≤ (c.k : ℝ)` using `by exact_mod_cast hsk`. Establish `hv0` using `hc.hv0`. Unfold `Cfg.v`. Use the polynomial consequences of the given equalities and inequalities.

Establish `h2 : c.lam s = -c.b (s + 1 - c.k)` using `by simp [Cfg.lam, hsk]`. Rewrite using `[h2]`. Use `Sz3.b_lt c hc (s + 1 - c.k) (by omega) (t + 1 - c.k) (by omega) (by omega)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem lamStrictAnti : Formalism.FourierDecayAlt.Sz.LamAnti := by
  intro c hc s t hs hst ht
  have hDel := hc.hDel
  have hstR : (s : ℝ) + 1 ≤ (t : ℝ) := by exact_mod_cast hst
  by_cases htk : t < c.k
  · have hsk : s < c.k := by omega
    have h1 : c.lam t = c.v t := by simp [Cfg.lam, htk]
    have h2 : c.lam s = c.v s := by simp [Cfg.lam, hsk]
    rw [h1, h2]; unfold Cfg.v
    nlinarith
  · have h1 : c.lam t = -c.b (t + 1 - c.k) := by simp [Cfg.lam, htk]
    rw [h1]
    by_cases hsk : s < c.k
    · have h2 : c.lam s = c.v s := by simp [Cfg.lam, hsk]
      rw [h2]
      have hb := Sz3.b_ge_one c hc (t + 1 - c.k) (by omega) (by omega)
      have hskR : (s : ℝ) + 1 ≤ (c.k : ℝ) := by exact_mod_cast hsk
      have hv0 := hc.hv0
      unfold Cfg.v
      nlinarith
    · have h2 : c.lam s = -c.b (s + 1 - c.k) := by simp [Cfg.lam, hsk]
      rw [h2]
      have := Sz3.b_lt c hc (s + 1 - c.k) (by omega) (t + 1 - c.k) (by omega) (by omega)
      linarith

/- English proof (translation)
Introduce `c de hc hw i i' hi hii' hi'k hor`. Establish `h1 : c.u de (i + 1) = c.v i - 1 / 2 - de i * c.Del`. Unfold `Cfg.u`. Rewrite using `[if_neg (by omega), if_neg (by omega)]; simp`. Rewrite using `[h1]`.

Distinguish the cases in `hlast : i' + 1 = c.k`. Establish `htop : c.top = false`. Break down `hor with h | h` into its components or cases. Use linear arithmetic over natural numbers and integers. Conclude with `h`.

Establish `h2 : c.u de (i' + 1) = c.vlast - 1 / 2`. Unfold `Cfg.u`. Rewrite using `[if_neg (by omega), if_pos hlast]`. Simplify using `[Cfg.ulast, htop]`. Establish `hde : de i' = 0`.

Establish `: i' = c.k - 1` using `by omega`. Rewrite using `[this]`. Conclude with `hw.2`. Establish `hkR : (i' : ℝ) + 1 = (c.k : ℝ)` using `by exact_mod_cast hlast`. Rewrite using `[h2, hde]`.

Unfold `Cfg.v`. Rewrite using `[← hkR]`. Expand and normalize the polynomial expressions, which then agree. Establish `h2 : c.u de (i' + 1) = c.v i' - 1 / 2 - de i' * c.Del`. Unfold `Cfg.u`.

Rewrite using `[if_neg (by omega), if_neg hlast]; simp`. Rewrite using `[h2]`. Unfold `Cfg.v`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem positionDiff : Formalism.FourierDecayAlt.Sz.PositionDiff := by
  intro c de hc hw i i' hi hii' hi'k hor
  have h1 : c.u de (i + 1) = c.v i - 1 / 2 - de i * c.Del := by
    unfold Cfg.u
    rw [if_neg (by omega), if_neg (by omega)]; simp
  rw [h1]
  by_cases hlast : i' + 1 = c.k
  · have htop : c.top = false := by
      rcases hor with h | h
      · omega
      · exact h
    have h2 : c.u de (i' + 1) = c.vlast - 1 / 2 := by
      unfold Cfg.u
      rw [if_neg (by omega), if_pos hlast]
      simp [Cfg.ulast, htop]
    have hde : de i' = 0 := by
      have : i' = c.k - 1 := by omega
      rw [this]; exact hw.2
    have hkR : (i' : ℝ) + 1 = (c.k : ℝ) := by exact_mod_cast hlast
    rw [h2, hde]; unfold Cfg.v; rw [← hkR]; ring
  · have h2 : c.u de (i' + 1) = c.v i' - 1 / 2 - de i' * c.Del := by
      unfold Cfg.u
      rw [if_neg (by omega), if_neg hlast]; simp
    rw [h2]; unfold Cfg.v; ring

end Formalism.FourierDecayAlt.P

namespace Formalism.FourierDecayAlt.P.Sz3

open Finset Formalism.FourierDecayAlt.Sz

/- English proof (translation)
Establish `h` using `Real.abs_log_sub_add_sum_range_le (x := -x) (by rw [abs_neg]; linarith) 3`. Simplify using `only [Finset.sum_range_succ, Finset.sum_range_zero, abs_neg, sub_neg_eq_add] at h`. Establish `hy0 : 0 ≤ |x|` using `abs_nonneg x`. Establish `hx2 : |x| ^ 2 = x ^ 2` using `sq_abs x`. Establish `hB : |x| ^ (3 + 1) / (1 - |x|) ≤ x ^ 2 / 12`.

Rewrite using `[div_le_iff₀ (by linarith)]`. Establish `: |x| ^ (3 + 1) = x ^ 2 * |x| ^ 2` using `by rw [← hx2]; ring`. Rewrite using `[this]`. Establish `h2 : |x| ^ 2 ≤ 1 / 16` using `by nlinarith`. Establish `h3 : 0 ≤ x ^ 2` using `sq_nonneg x`.

Use the polynomial consequences of the given equalities and inequalities. Establish `h'` using `abs_le.mp (h.trans hB)`. Take `⟨hxl, hxu⟩` from `abs_le.mp hx`. Establish `h3 : 0 ≤ x ^ 2` using `sq_nonneg x`. Establish `hc1 : x ^ 3 ≤ x ^ 2 / 4` using `by nlinarith`.

Establish `hc2 : -(x ^ 2 / 4) ≤ x ^ 3` using `by nlinarith`. Evaluate the numerical expressions using `at h'`. Rewrite using `[abs_le]`. Apply the tactic sequence `constructor <;> nlinarith [h'.1, h'.2]`.
-/
lemma log_one_add_sub (x : ℝ) (hx : |x| ≤ 1 / 4) : |Real.log (1 + x) - x| ≤ 2 / 3 * x ^ 2 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := -x) (by rw [abs_neg]; linarith) 3
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, abs_neg, sub_neg_eq_add] at h
  have hy0 : 0 ≤ |x| := abs_nonneg x
  have hx2 : |x| ^ 2 = x ^ 2 := sq_abs x
  have hB : |x| ^ (3 + 1) / (1 - |x|) ≤ x ^ 2 / 12 := by
    rw [div_le_iff₀ (by linarith)]
    have : |x| ^ (3 + 1) = x ^ 2 * |x| ^ 2 := by rw [← hx2]; ring
    rw [this]
    have h2 : |x| ^ 2 ≤ 1 / 16 := by nlinarith
    have h3 : 0 ≤ x ^ 2 := sq_nonneg x
    nlinarith
  have h' := abs_le.mp (h.trans hB)
  obtain ⟨hxl, hxu⟩ := abs_le.mp hx
  have h3 : 0 ≤ x ^ 2 := sq_nonneg x
  have hc1 : x ^ 3 ≤ x ^ 2 / 4 := by nlinarith
  have hc2 : -(x ^ 2 / 4) ≤ x ^ 3 := by nlinarith
  norm_num at h'
  rw [abs_le]
  constructor <;> nlinarith [h'.1, h'.2]

/- English proof (translation)
Establish `h : ∀ i, ∑ i' ∈ Ioc i J, f i i' = ∑ d ∈ Icc 1 (J - i), f i (i + d)`. Introduce `i`. Apply `Finset.sum_nbij' (fun i' => i' - i) (fun d => i + d)` to reduce the goal to its premises. Introduce `a ha`. Simplify using `only [mem_Ioc, mem_Icc] at *`.

Use linear arithmetic over natural numbers and integers. Introduce `a ha`. Simplify using `only [mem_Ioc, mem_Icc] at *`. Use linear arithmetic over natural numbers and integers. Introduce `a ha`.

Simplify using `only [mem_Ioc] at *`. Use linear arithmetic over natural numbers and integers. Introduce `a ha`. Simplify using `only [mem_Icc] at *`. Use linear arithmetic over natural numbers and integers.

Introduce `a ha`. Simplify using `only [mem_Ioc] at ha`. Establish `: i + (a - i) = a` using `by omega`. Rewrite using `[this]`. Repeatedly rewrite using `[h]`.

Apply `Finset.sum_comm'` to reduce the goal to its premises. Introduce `i d`. Simplify using `only [mem_Icc]`. Use linear arithmetic over natural numbers and integers.
-/
lemma pair_reindex (J : ℕ) (f : ℕ → ℕ → ℝ) :
    ∑ i ∈ Icc 1 J, ∑ i' ∈ Ioc i J, f i i' = ∑ d ∈ Icc 1 J, ∑ i ∈ Icc 1 (J - d), f i (i + d) := by
  have h : ∀ i, ∑ i' ∈ Ioc i J, f i i' = ∑ d ∈ Icc 1 (J - i), f i (i + d) := by
    intro i
    apply Finset.sum_nbij' (fun i' => i' - i) (fun d => i + d)
    · intro a ha; simp only [mem_Ioc, mem_Icc] at *; omega
    · intro a ha; simp only [mem_Ioc, mem_Icc] at *; omega
    · intro a ha; simp only [mem_Ioc] at *; omega
    · intro a ha; simp only [mem_Icc] at *; omega
    · intro a ha
      simp only [mem_Ioc] at ha
      have : i + (a - i) = a := by omega
      rw [this]
  simp_rw [h]
  apply Finset.sum_comm'
  intro i d
  simp only [mem_Icc]
  omega

noncomputable def NF (J : ℕ) (de : ℕ → ℝ) : ℝ :=
  ∑ d ∈ Icc 1 J, (∑ i ∈ Ioc d J, de i - ∑ i ∈ Icc 1 (J - d), de i) / (d : ℝ)

/- English proof (translation)
Apply `Finset.sum_nbij' (fun i => i + d) (fun i => i - d)` to reduce the goal to its premises. Introduce `a ha`. Simplify using `only [mem_Ioc, mem_Icc] at *`. Use linear arithmetic over natural numbers and integers. Introduce `a ha`.

Simplify using `only [mem_Ioc, mem_Icc] at *`. Use linear arithmetic over natural numbers and integers. Introduce `a ha`. Simplify using `only [mem_Icc] at *`. Use linear arithmetic over natural numbers and integers.

Introduce `a ha`. Simplify using `only [mem_Ioc] at *`. Use linear arithmetic over natural numbers and integers. Introduce `a ha`. Both sides reduce to the same expression.
-/
lemma shift_sum (J d : ℕ) (hd : d ≤ J) (de : ℕ → ℝ) :
    ∑ i ∈ Icc 1 (J - d), de (i + d) = ∑ i ∈ Ioc d J, de i := by
  apply Finset.sum_nbij' (fun i => i + d) (fun i => i - d)
  · intro a ha; simp only [mem_Ioc, mem_Icc] at *; omega
  · intro a ha; simp only [mem_Ioc, mem_Icc] at *; omega
  · intro a ha; simp only [mem_Icc] at *; omega
  · intro a ha; simp only [mem_Ioc] at *; omega
  · intro a ha; rfl

/- English proof (translation)
Rewrite using `[pair_reindex, NF, Finset.mul_sum]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `d hd`. Simplify using `only [mem_Icc] at hd`. Rewrite using `[← shift_sum J d hd.2 de, ← Finset.sum_sub_distrib, Finset.sum_div, Finset.mul_sum]`.

Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `i _`. Establish `hd0 : (d : ℝ) ≠ 0`. Establish `: 0 < d` using `by omega`. Check the signs of the components of the expression.

Use `push_cast`. Establish `: 4 * ((i : ℝ) + d - i) = 4 * d` using `by ring`. Rewrite using `[this]`. Clear the denominators using the available nonvanishing facts.
-/
lemma pair_eq_NF (J : ℕ) (de : ℕ → ℝ) :
    ∑ i ∈ Icc 1 J, ∑ i' ∈ Ioc i J, (de i' - de i) / (4 * ((i' : ℝ) - (i : ℝ))) =
      (1 / 4) * NF J de := by
  rw [pair_reindex, NF, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [mem_Icc] at hd
  rw [← shift_sum J d hd.2 de, ← Finset.sum_sub_distrib, Finset.sum_div, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hd0 : (d : ℝ) ≠ 0 := by
    have : 0 < d := by omega
    positivity
  push_cast
  have : 4 * ((i : ℝ) + d - i) = 4 * d := by ring
  rw [this]
  field_simp

/- English proof (translation)
Rewrite using `[harmonic_eq_sum_Icc]`. Use `push_cast`. Simplify using the standard rewrite rules.
-/
lemma harmonic_real (n : ℕ) : ((harmonic n : ℚ) : ℝ) = ∑ d ∈ Icc 1 n, 1 / (d : ℝ) := by
  rw [harmonic_eq_sum_Icc]
  push_cast
  simp

/- English proof (translation)
Repeatedly rewrite using `[harmonic_real, mul_sub, Finset.mul_sum]`. Rewrite using `[Finset.sum_sub_distrib, NF]`. Repeatedly rewrite using `[sub_div, Finset.sum_div]`. Rewrite using `[Finset.sum_sub_distrib]`. Use `congr 1`.

Rewrite using `[Finset.sum_comm' (t' := Icc 1 J) (s' := fun d => Ioc d J)]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `d _`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `i _`.

Expand and normalize the polynomial expressions, which then agree. Introduce `i d`. Simplify using `only [mem_Icc, mem_Ioc]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[Finset.sum_comm' (t' := Icc 1 J) (s' := fun d => Icc 1 (J - d))]`.

Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `d _`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `i _`. Expand and normalize the polynomial expressions, which then agree.

Introduce `i d`. Simplify using `only [mem_Icc]`. Use linear arithmetic over natural numbers and integers.
-/
lemma harm_eq_NF (J : ℕ) (de : ℕ → ℝ) :
    ∑ i ∈ Icc 1 J, de i * (((harmonic (i - 1) : ℚ) : ℝ) - ((harmonic (J - i) : ℚ) : ℝ)) =
      NF J de := by
  simp_rw [harmonic_real, mul_sub, Finset.mul_sum]
  rw [Finset.sum_sub_distrib, NF]
  simp_rw [sub_div, Finset.sum_div]
  rw [Finset.sum_sub_distrib]
  congr 1
  · rw [Finset.sum_comm' (t' := Icc 1 J) (s' := fun d => Ioc d J)]
    · apply Finset.sum_congr rfl; intro d _; apply Finset.sum_congr rfl; intro i _; ring
    · intro i d; simp only [mem_Icc, mem_Ioc]; omega
  · rw [Finset.sum_comm' (t' := Icc 1 J) (s' := fun d => Icc 1 (J - d))]
    · apply Finset.sum_congr rfl; intro d _; apply Finset.sum_congr rfl; intro i _; ring
    · intro i d; simp only [mem_Icc]; omega

end Formalism.FourierDecayAlt.P.Sz3

namespace Formalism.FourierDecayAlt.P.Sz3

open Finset Formalism.FourierDecayAlt.Sz

noncomputable def hs (n : ℕ) : ℝ := ∑ d ∈ Ioc 0 n, 1 / (d : ℝ)

/- English proof (translation)
Unfold `hs`. Rewrite using `[Finset.sum_Ioc_succ_top (Nat.zero_le n)]`. Use `push_cast`. Both sides reduce to the same expression.
-/
lemma hs_succ (n : ℕ) : hs (n + 1) = hs n + 1 / ((n : ℝ) + 1) := by
  unfold hs
  rw [Finset.sum_Ioc_succ_top (Nat.zero_le n)]
  push_cast
  rfl

/- English proof (translation)
Simplify using `[hs]`.
-/
lemma hs_zero : hs 0 = 0 := by simp [hs]

/- English proof (translation)
Proceed by induction on `p, hp using Nat.le_induction with`. Consider the case `base`. Establish `h2 : hs (2 * 1) = hs 1 + 1 / ((1 : ℝ) + 1)`. Use `hs_succ 1` as an intermediate fact. Simplify using `using this`.

Rewrite using `[h2]`. Evaluate the numerical expressions. Consider the case `succ n hn ih`. Establish `h1 : 2 * (n + 1) = (2 * n + 1) + 1` using `by ring`. Rewrite using `[h1, hs_succ, hs_succ, hs_succ]`.

Use `push_cast`. Establish `hn0 : (1 : ℝ) ≤ n` using `by exact_mod_cast hn`. Establish `e1 : 1 / ((2 : ℝ) * n + 1) + 1 / (2 * n + 1 + 1) - 1 / (n + 1) = 1 / ((2 * n + 1) * (2 * n + 2))` using `by field_simp; ring`. Establish `e2 : 1 / (4 * (n : ℝ) + 1) - 1 / (4 * (n + 1) + 1) = 4 / ((4 * n + 1) * (4 * n + 5))` using `by field_simp; ring`. Establish `key : 1 / (((2 : ℝ) * n + 1) * (2 * n + 2)) ≤ 4 / ((4 * n + 1) * (4 * n + 5))`.

Rewrite using `[div_le_div_iff₀ (by positivity) (by positivity)]`. Use the polynomial consequences of the given equalities and inequalities. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma hs_tail (p : ℕ) (hp : 1 ≤ p) : hs (2 * p) - hs p ≤ 7 / 10 - 1 / (4 * (p : ℝ) + 1) := by
  induction p, hp using Nat.le_induction with
  | base =>
    have h2 : hs (2 * 1) = hs 1 + 1 / ((1 : ℝ) + 1) := by
      have := hs_succ 1
      simpa using this
    rw [h2]; norm_num
  | succ n hn ih =>
    have h1 : 2 * (n + 1) = (2 * n + 1) + 1 := by ring
    rw [h1, hs_succ, hs_succ, hs_succ]
    push_cast
    have hn0 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have e1 : 1 / ((2 : ℝ) * n + 1) + 1 / (2 * n + 1 + 1) - 1 / (n + 1) =
        1 / ((2 * n + 1) * (2 * n + 2)) := by
      field_simp; ring
    have e2 : 1 / (4 * (n : ℝ) + 1) - 1 / (4 * (n + 1) + 1) = 4 / ((4 * n + 1) * (4 * n + 5)) := by
      field_simp; ring
    have key : 1 / (((2 : ℝ) * n + 1) * (2 * n + 2)) ≤ 4 / ((4 * n + 1) * (4 * n + 5)) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith

/- English proof (translation)
Unfold `hs`. Rewrite using `[← Finset.sum_Ioc_consecutive _ (Nat.zero_le p) h]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma hs_sub (p J : ℕ) (h : p ≤ J) : ∑ d ∈ Ioc p J, 1 / (d : ℝ) = hs J - hs p := by
  unfold hs
  rw [← Finset.sum_Ioc_consecutive _ (Nat.zero_le p) h]
  ring

/- English proof (translation)
Use `hs_sub p J h` as an intermediate fact. Establish `h0 : 0 ≤ ∑ d ∈ Ioc p J, 1 / (d : ℝ)` using `Finset.sum_nonneg (fun d _ => by positivity)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma hs_mono (p J : ℕ) (h : p ≤ J) : hs p ≤ hs J := by
  have := hs_sub p J h
  have h0 : 0 ≤ ∑ d ∈ Ioc p J, 1 / (d : ℝ) := Finset.sum_nonneg (fun d _ => by positivity)
  linarith

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Apply `Finset.sum_nonneg` to reduce the goal to its premises. Introduce `i _`. Apply the tactic sequence `rcases hde i with h | h <;> linarith`. Establish `: ∑ i ∈ s, de i ≤ ∑ _i ∈ s, (1 : ℝ)`.

Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `i _`. Apply the tactic sequence `rcases hde i with h | h <;> linarith`. Simplify using `using this`.
-/
lemma sum_de_bd (de : ℕ → ℝ) (hde : ∀ i, de i = 0 ∨ de i = 1) (s : Finset ℕ) :
    0 ≤ ∑ i ∈ s, de i ∧ ∑ i ∈ s, de i ≤ (s.card : ℝ) := by
  constructor
  · apply Finset.sum_nonneg
    intro i _
    rcases hde i with h | h <;> linarith
  · have : ∑ i ∈ s, de i ≤ ∑ _i ∈ s, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      rcases hde i with h | h <;> linarith
    simpa using this

/- English proof (translation)
Use extensionality with `x`. Simplify using `only [mem_Icc, mem_Ioc]`. Use linear arithmetic over natural numbers and integers.
-/
lemma Icc_one_eq (n : ℕ) : Icc 1 n = Ioc 0 n := by
  ext x; simp only [mem_Icc, mem_Ioc]; omega

/- English proof (translation)
The claim follows from `|∑ i ∈ Ioc d J, de i - ∑ i ∈ Icc 1 (J - d), de i| ≤ (d : ℝ) ∧ |∑ i ∈ Ioc d J, de i - ∑ i ∈ Icc 1 (J - d), de i| ≤ (J : ℝ) - (d : ℝ) := by rw [Icc_one_eq] have c1 := Finset.sum_Ioc_consecutive de (Nat.zero_le d) hd have c2 := Finset.sum_Ioc_consecutive de (Nat.zero_le (J - d)) (Na …`.
-/
lemma diff_bd (J d : ℕ) (hd : d ≤ J) (de : ℕ → ℝ) (hde : ∀ i, de i = 0 ∨ de i = 1) :
    |∑ i ∈ Ioc d J, de i - ∑ i ∈ Icc 1 (J - d), de i| ≤ (d : ℝ) ∧
    |∑ i ∈ Ioc d J, de i - ∑ i ∈ Icc 1 (J - d), de i| ≤ (J : ℝ) - (d : ℝ) := by
  rw [Icc_one_eq]
  have c1 := Finset.sum_Ioc_consecutive de (Nat.zero_le d) hd
  have c2 := Finset.sum_Ioc_consecutive de (Nat.zero_le (J - d)) (Nat.sub_le J d)
  have b1 := sum_de_bd de hde (Ioc 0 d)
  have b2 := sum_de_bd de hde (Ioc d J)
  have b3 := sum_de_bd de hde (Ioc 0 (J - d))
  have b4 := sum_de_bd de hde (Ioc (J - d) J)
  simp only [Nat.card_Ioc] at b1 b2 b3 b4
  have e1 : ((J - d : ℕ) : ℝ) = (J : ℝ) - d := by rw [Nat.cast_sub hd]
  have e2 : ((J - (J - d) : ℕ) : ℝ) = (d : ℝ) := by
    have : J - (J - d) = d := by omega
    rw [this]
  rw [e1] at b2
  rw [Nat.sub_zero] at b1 b3
  rw [e1] at b3
  rw [e2] at b4
  constructor <;> rw [abs_le] <;> constructor <;> linarith [b1.1, b1.2, b2.1, b2.2, b3.1, b3.2, b4.1, b4.2]

/- English proof (translation)
The claim follows from `|NF J de| ≤ 7 / 10 * (J : ℝ) + 1 := by unfold NF refine (Finset.abs_sum_le_sum_abs _ _).trans ?_ obtain ⟨p, hp1, hp2, hp3, hp4⟩ : ∃ p : ℕ, 1 ≤ p ∧ p ≤ J ∧ J ≤ 2 * p ∧ 2 * p ≤ J + 1 := ⟨(J + 1) / 2, by omega, by omega, by omega, by omega⟩ rw [Icc_one_eq J, ← Finset.sum_Ioc_consecu …`.
-/
lemma NF_bd (J : ℕ) (hJ : 1 ≤ J) (de : ℕ → ℝ) (hde : ∀ i, de i = 0 ∨ de i = 1) :
    |NF J de| ≤ 7 / 10 * (J : ℝ) + 1 := by
  unfold NF
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  obtain ⟨p, hp1, hp2, hp3, hp4⟩ : ∃ p : ℕ, 1 ≤ p ∧ p ≤ J ∧ J ≤ 2 * p ∧ 2 * p ≤ J + 1 :=
    ⟨(J + 1) / 2, by omega, by omega, by omega, by omega⟩
  rw [Icc_one_eq J, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le p) hp2]
  have hA : ∑ d ∈ Ioc 0 p, |(∑ i ∈ Ioc d J, de i - ∑ i ∈ Icc 1 (J - d), de i) / (d : ℝ)| ≤
      ∑ _d ∈ Ioc 0 p, (1 : ℝ) := by
    apply Finset.sum_le_sum
    intro d hd
    simp only [mem_Ioc] at hd
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hd.1
    rw [abs_div, abs_of_pos hd0, div_le_one hd0]
    exact (diff_bd J d (by omega) de hde).1
  have hB : ∑ d ∈ Ioc p J, |(∑ i ∈ Ioc d J, de i - ∑ i ∈ Icc 1 (J - d), de i) / (d : ℝ)| ≤
      ∑ d ∈ Ioc p J, ((J : ℝ) * (1 / (d : ℝ)) - 1) := by
    apply Finset.sum_le_sum
    intro d hd
    simp only [mem_Ioc] at hd
    have hd0 : (0 : ℝ) < d := by
      have : 0 < d := by omega
      exact_mod_cast this
    rw [abs_div, abs_of_pos hd0, div_le_iff₀ hd0]
    have := (diff_bd J d hd.2 de hde).2
    have e : ((J : ℝ) * (1 / (d : ℝ)) - 1) * d = J - d := by field_simp
    rw [e]; exact this
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hs_sub p J hp2] at hB
  simp only [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul, mul_one, Nat.sub_zero] at hA hB
  rw [Nat.cast_sub hp2] at hB
  have ht := hs_tail p hp1
  have hm := hs_mono J (2 * p) hp3
  have hpos : (0 : ℝ) < 1 / (4 * (p : ℝ) + 1) := by positivity
  have hJ0 : (0 : ℝ) ≤ J := Nat.cast_nonneg J
  have h7 : hs J - hs p ≤ 7 / 10 := by linarith
  have hmul : (J : ℝ) * (hs J - hs p) ≤ J * (7 / 10) := mul_le_mul_of_nonneg_left h7 hJ0
  have hp4R : 2 * (p : ℝ) ≤ J + 1 := by exact_mod_cast hp4
  linarith

/- English proof (translation)
The claim follows from `sum_le_hasSum _ (fun i _ => by positivity) hasSum_zeta_two`.
-/
lemma sum_inv_sq (n : ℕ) : ∑ d ∈ Icc 1 n, 1 / (d : ℝ) ^ 2 ≤ Real.pi ^ 2 / 6 :=
  sum_le_hasSum _ (fun i _ => by positivity) hasSum_zeta_two

noncomputable def xx (de : ℕ → ℝ) (i i' : ℕ) : ℝ := (de i' - de i) / (4 * ((i' : ℝ) - (i : ℝ)))

/- English proof (translation)
The claim follows from `|xx de i i'| ≤ 1 / 4 ∧ (xx de i i') ^ 2 ≤ 1 / 16 * (1 / (((i' - i : ℕ) : ℝ)) ^ 2) := by have hR : (i : ℝ) + 1 ≤ (i' : ℝ) := by exact_mod_cast h have hc : ((i' - i : ℕ) : ℝ) = (i' : ℝ) - i := by rw [Nat.cast_sub h.le] have hpos : (0 : ℝ) < (i' : ℝ) - i := by linarith have hnum : | …`.
-/
lemma xx_bd (de : ℕ → ℝ) (hde : ∀ i, de i = 0 ∨ de i = 1) (i i' : ℕ) (h : i < i') :
    |xx de i i'| ≤ 1 / 4 ∧ (xx de i i') ^ 2 ≤ 1 / 16 * (1 / (((i' - i : ℕ) : ℝ)) ^ 2) := by
  have hR : (i : ℝ) + 1 ≤ (i' : ℝ) := by exact_mod_cast h
  have hc : ((i' - i : ℕ) : ℝ) = (i' : ℝ) - i := by rw [Nat.cast_sub h.le]
  have hpos : (0 : ℝ) < (i' : ℝ) - i := by linarith
  have hnum : |de i' - de i| ≤ 1 := by
    rcases hde i with h1 | h1 <;> rcases hde i' with h2 | h2 <;> rw [h1, h2] <;> norm_num
  constructor
  · unfold xx
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 4 * ((i' : ℝ) - i)),
      div_le_iff₀ (by positivity)]
    linarith
  · unfold xx
    rw [hc, div_pow, mul_pow, ← sq_abs (de i' - de i)]
    have : |de i' - de i| ^ 2 ≤ 1 := by
      have h0 := abs_nonneg (de i' - de i)
      nlinarith
    rw [div_le_iff₀ (by positivity)]
    have e : 1 / 16 * (1 / ((i' : ℝ) - i) ^ 2) * (4 ^ 2 * ((i' : ℝ) - i) ^ 2) = 1 := by
      field_simp; norm_num
    rw [e]; exact this

end Formalism.FourierDecayAlt.P.Sz3

namespace Formalism.FourierDecayAlt.P

open Finset Formalism.FourierDecayAlt.Sz Sz3

/- English proof (translation)
Introduce `J de hJ hde`. Establish `hfac : ∀ i i' : ℕ, i < i' → 0 < 1 + xx de i i'`. Introduce `i i' h`. Use `abs_le.mp (xx_bd de hde i i' h).1` as an intermediate fact. Combine the linear relations using `[this.1]`.

Establish `hR : Rde J de = ∏ i ∈ Icc 1 J, ∏ i' ∈ Ioc i J, (1 + xx de i i')` using `rfl`. Establish `hpos : 0 < Rde J de`. Rewrite using `[hR]`. Apply `Finset.prod_pos` to reduce the goal to its premises. Introduce `i _`.

Apply `Finset.prod_pos` to reduce the goal to its premises. Introduce `i' hi'`. Conclude with `hfac i i' (mem_Ioc.mp hi').1`. Establish `hlog : Real.log (Rde J de) = ∑ i ∈ Icc 1 J, ∑ i' ∈ Ioc i J, Real.log (1 + xx de i i')`. Rewrite using `[hR, Real.log_prod]`.

Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `i _`. Rewrite using `[Real.log_prod]`. Introduce `i' hi'`. Conclude with `(hfac i i' (mem_Ioc.mp hi').1).ne'`.

Introduce `i _`. Apply `ne_of_gt` to reduce the goal to its premises. Apply `Finset.prod_pos` to reduce the goal to its premises. Introduce `i' hi'`. Conclude with `hfac i i' (mem_Ioc.mp hi').1`.

Establish `hM : ∑ i ∈ Icc 1 J, ∑ i' ∈ Ioc i J, xx de i i' = (1 / 4) * NF J de` using `pair_eq_NF J de`. Establish `hE : |Real.log (Rde J de) - (1 / 4) * NF J de| ≤ Real.pi ^ 2 / 144 * J`. Rewrite using `[hlog, ← hM, ← Finset.sum_sub_distrib]`. Use `(Finset.abs_sum_le_sum_abs _ _).trans ?_` and prove the remaining obligations. Establish `: ∀ i ∈ Icc 1 J, |∑ i' ∈ Ioc i J, Real.log (1 + xx de i i') - ∑ i' ∈ Ioc i J, xx de i i'| ≤ Real.pi ^ 2 / 144`.

Introduce `i _`. Rewrite using `[← Finset.sum_sub_distrib]`. Use `(Finset.abs_sum_le_sum_abs _ _).trans ?_` and prove the remaining obligations. Establish `h1 : ∑ i' ∈ Ioc i J, |Real.log (1 + xx de i i') - xx de i i'| ≤ ∑ i' ∈ Ioc i J, 1 / 24 * (1 / (((i' - i : ℕ) : ℝ)) ^ 2)`. Apply `Finset.sum_le_sum` to reduce the goal to its premises.

Introduce `i' hi'`. Establish `hb` using `xx_bd de hde i i' (mem_Ioc.mp hi').1`. Use `log_one_add_sub _ hb.1` as an intermediate fact. Combine the linear relations using `[hb.2]`. Establish `h2 : ∑ i' ∈ Ioc i J, 1 / 24 * (1 / (((i' - i : ℕ) : ℝ)) ^ 2) = 1 / 24 * ∑ d ∈ Icc 1 (J - i), 1 / (d : ℝ) ^ 2`.

Rewrite using `[Finset.mul_sum]`. Apply `Finset.sum_nbij' (fun i' => i' - i) (fun d => i + d)` to reduce the goal to its premises. Introduce `a ha`. Simplify using `only [mem_Ioc, mem_Icc] at *`. Use linear arithmetic over natural numbers and integers.

Introduce `a ha`. Simplify using `only [mem_Ioc, mem_Icc] at *`. Use linear arithmetic over natural numbers and integers. Introduce `a ha`. Simplify using `only [mem_Ioc] at *`.

Use linear arithmetic over natural numbers and integers. Introduce `a ha`. Simplify using `only [mem_Icc] at *`. Use linear arithmetic over natural numbers and integers. Introduce `a ha`.

Both sides reduce to the same expression. Establish `h3` using `sum_inv_sq (J - i)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h4` using `Finset.sum_le_sum this`. Simplify using `only [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel] at h4`.

Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨hpos, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[harm_eq_NF]`. Conclude with `hE`. Establish `hN` using `NF_bd J hJ de hde`.

Establish `hpi : Real.pi ^ 2 ≤ 10.8`. Establish `h1` using `Real.pi_lt_d2`. Establish `h0` using `Real.pi_pos`. Use the polynomial consequences of the given equalities and inequalities. Establish `hJ0 : (0 : ℝ) ≤ J` using `Nat.cast_nonneg J`.

Establish `hE'` using `abs_le.mp hE`. Establish `hN'` using `abs_le.mp hN`. Establish `hpJ : Real.pi ^ 2 / 144 * J ≤ 10.8 / 144 * J`. Apply `mul_le_mul_of_nonneg_right _ hJ0` to reduce the goal to its premises. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite using `[abs_le]`. Apply the tactic sequence `constructor <;> linarith [hE'.1, hE'.2, hN'.1, hN'.2]`.
-/
theorem vandermondeRatioHarmonic : Formalism.FourierDecayAlt.Sz.HarmonicVand := by
  intro J de hJ hde
  have hfac : ∀ i i' : ℕ, i < i' → 0 < 1 + xx de i i' := by
    intro i i' h
    have := abs_le.mp (xx_bd de hde i i' h).1
    linarith [this.1]
  have hR : Rde J de = ∏ i ∈ Icc 1 J, ∏ i' ∈ Ioc i J, (1 + xx de i i') := rfl
  have hpos : 0 < Rde J de := by
    rw [hR]
    apply Finset.prod_pos; intro i _
    apply Finset.prod_pos; intro i' hi'
    exact hfac i i' (mem_Ioc.mp hi').1
  have hlog : Real.log (Rde J de) = ∑ i ∈ Icc 1 J, ∑ i' ∈ Ioc i J, Real.log (1 + xx de i i') := by
    rw [hR, Real.log_prod]
    · apply Finset.sum_congr rfl
      intro i _
      rw [Real.log_prod]
      intro i' hi'
      exact (hfac i i' (mem_Ioc.mp hi').1).ne'
    · intro i _
      apply ne_of_gt
      apply Finset.prod_pos; intro i' hi'
      exact hfac i i' (mem_Ioc.mp hi').1
  have hM : ∑ i ∈ Icc 1 J, ∑ i' ∈ Ioc i J, xx de i i' = (1 / 4) * NF J de := pair_eq_NF J de
  have hE : |Real.log (Rde J de) - (1 / 4) * NF J de| ≤ Real.pi ^ 2 / 144 * J := by
    rw [hlog, ← hM, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have : ∀ i ∈ Icc 1 J, |∑ i' ∈ Ioc i J, Real.log (1 + xx de i i') - ∑ i' ∈ Ioc i J, xx de i i'| ≤
        Real.pi ^ 2 / 144 := by
      intro i _
      rw [← Finset.sum_sub_distrib]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have h1 : ∑ i' ∈ Ioc i J, |Real.log (1 + xx de i i') - xx de i i'| ≤
          ∑ i' ∈ Ioc i J, 1 / 24 * (1 / (((i' - i : ℕ) : ℝ)) ^ 2) := by
        apply Finset.sum_le_sum
        intro i' hi'
        have hb := xx_bd de hde i i' (mem_Ioc.mp hi').1
        have := log_one_add_sub _ hb.1
        linarith [hb.2]
      have h2 : ∑ i' ∈ Ioc i J, 1 / 24 * (1 / (((i' - i : ℕ) : ℝ)) ^ 2) =
          1 / 24 * ∑ d ∈ Icc 1 (J - i), 1 / (d : ℝ) ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_nbij' (fun i' => i' - i) (fun d => i + d)
        · intro a ha; simp only [mem_Ioc, mem_Icc] at *; omega
        · intro a ha; simp only [mem_Ioc, mem_Icc] at *; omega
        · intro a ha; simp only [mem_Ioc] at *; omega
        · intro a ha; simp only [mem_Icc] at *; omega
        · intro a ha; rfl
      have h3 := sum_inv_sq (J - i)
      linarith
    have h4 := Finset.sum_le_sum this
    simp only [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel] at h4
    linarith
  refine ⟨hpos, ?_, ?_⟩
  · rw [harm_eq_NF]; exact hE
  · have hN := NF_bd J hJ de hde
    have hpi : Real.pi ^ 2 ≤ 10.8 := by
      have h1 := Real.pi_lt_d2
      have h0 := Real.pi_pos
      nlinarith
    have hJ0 : (0 : ℝ) ≤ J := Nat.cast_nonneg J
    have hE' := abs_le.mp hE
    have hN' := abs_le.mp hN
    have hpJ : Real.pi ^ 2 / 144 * J ≤ 10.8 / 144 * J := by
      apply mul_le_mul_of_nonneg_right _ hJ0
      linarith
    rw [abs_le]
    constructor <;> linarith [hE'.1, hE'.2, hN'.1, hN'.2]

end Formalism.FourierDecayAlt.P
