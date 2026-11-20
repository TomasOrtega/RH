import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.BiadditiveInSingleVariables
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PeriodValuation

open Formalism.L2.FormalSeriesBounds

namespace GlobalTheory

/- English proof (translation)
Rewrite using `[Finset.sum_range_succ' (fun s => ((y + 1).choose s : C) * f s)]`. Repeatedly rewrite using `[Nat.choose_succ_succ', Nat.cast_add, add_mul, Finset.sum_add_distrib]`. Rewrite using `[Finset.sum_range_succ' (fun s => (y.choose s : C) * f s), Finset.sum_range_succ (fun s => (y.choose (s + 1) : C) * f (s + 1)), Nat.choose_succ_self]`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma sum_range_succ_choose_mul_eq_add_shift {C : Type} [Field C] (f : ℕ → C) (y : ℕ) :
    ∑ s ∈ Finset.range (y + 1 + 1), ((y + 1).choose s : C) * f s =
      ∑ s ∈ Finset.range (y + 1), (y.choose s : C) * f s +
        ∑ s ∈ Finset.range (y + 1), (y.choose s : C) * f (s + 1) := by
  rw [Finset.sum_range_succ' (fun s => ((y + 1).choose s : C) * f s)]
  simp_rw [Nat.choose_succ_succ', Nat.cast_add, add_mul, Finset.sum_add_distrib]
  rw [Finset.sum_range_succ' (fun s => (y.choose s : C) * f s),
    Finset.sum_range_succ (fun s => (y.choose (s + 1) : C) * f (s + 1)), Nat.choose_succ_self]
  simp
  ring

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Unfold `_root_.Formalism.L2.FormalSeriesBounds.NewtonBoundPositive`. Introduce `l hl i n0 s hi hn hs`. Unfold `_root_.Formalism.L2.FormalSeriesBounds.S0 at hs`. Establish `hl' : (5:ℝ) ≤ l` using `by exact_mod_cast hl`.

Establish `hN : (1:ℝ) ≤ n0` using `by exact_mod_cast hn`. Establish `hi' : (1:ℝ) ≤ i` using `by exact_mod_cast hi`. Establish `hlogl : 1 ≤ Real.log l`. Rewrite using `[Real.le_log_iff_exp_le (by linarith)]`. Use `Real.exp_one_lt_d9` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hlbN1 : 0 ≤ Real.logb l ((n0:ℝ) + 1)` using `Real.logb_nonneg (by linarith) (by linarith)`. Establish `hsK : 64 * (n0:ℝ) ^ 2 * ((i:ℝ) + 3 + 3 * Real.logb l ((n0:ℝ) + 1)) ≤ (s:ℝ)` using `(Nat.le_ceil _).trans (by exact_mod_cast hs)`. Establish `hN2 : 0 < 64 * (n0:ℝ) ^ 2` using `by positivity`. Use `set t : ℝ := (s:ℝ) / (64 * (n0:ℝ) ^ 2) with ht`.

Establish `hst : (s:ℝ) = t * 64 * (n0:ℝ) ^ 2` using `by rw [ht]; field_simp`. Establish `htK : (i:ℝ) + 3 + 3 * Real.logb l ((n0:ℝ) + 1) ≤ t`. Rewrite using `[ht, le_div_iff₀ hN2]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `ht0 : 0 < t` using `by linarith`.

Establish `hlogs : Real.logb l s = Real.logb l t + Real.logb l 64 + 2 * Real.logb l n0`. Rewrite using `[hst, Real.logb_mul (by positivity) (by positivity), Real.logb_mul (by positivity) (by norm_num), Real.logb_pow]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hlbt : Real.logb l t ≤ t - 1`.

Establish `h1` using `Real.log_le_sub_one_of_pos ht0`. Establish `h2 : 0 ≤ Real.log t` using `Real.log_nonneg (by linarith)`. Rewrite using `[Real.logb, div_le_iff₀ (by linarith)]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hlb64 : Real.logb l 64 ≤ 3`.

Establish `h3 : Real.logb l ((l:ℝ) ^ 3) = 3`. Rewrite using `[Real.logb_pow, Real.logb_self_eq_one (by linarith)]`. Evaluate the numerical expressions. Rewrite using `[← h3]`. Apply `Real.logb_le_logb_of_le (by linarith) (by norm_num)` to reduce the goal to its premises.

Establish `hcube : (5:ℝ) ^ 3 ≤ (l:ℝ) ^ 3` using `pow_le_pow_left₀ (by norm_num) hl' 3`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hlbN : Real.logb l n0 ≤ Real.logb l ((n0:ℝ) + 1)` using `Real.logb_le_logb_of_le (by linarith) (by linarith) (by linarith)`. Establish `key : 3 * Real.logb l n0 + 2 * Real.logb l s + i + 3 < 8 * t`. Rewrite using `[hlogs]`.

Use the polynomial consequences of the given equalities and inequalities. Establish `hs8 : (s:ℝ) / 8 = 8 * t * (n0:ℝ) ^ 2` using `by rw [hst]; ring`. Rewrite using `[hs8]`. Establish `hpos : 0 < (n0:ℝ) ^ 2` using `by positivity`. Use polynomial arithmetic with `[mul_lt_mul_of_pos_left key hpos]`.

Unfold `_root_.Formalism.L2.FormalSeriesBounds.P7`. Introduce `C _ v S a hS ha0 hpos Y0`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Establish `hadd : ∀ x y : C, 0 < v x → 0 < v y → 0 < v (x + y)` using `fun x y hx hy => lt_of_lt_of_le (lt_min hx hy) (v.map_add x y)`.

Establish `hsub : ∀ x y : C, 0 < v x → 0 < v y → 0 < v (x - y)` using `fun x y hx hy => by`. Rewrite using `[sub_eq_add_neg]`. Conclude with `hadd _ _ hx (by rwa [v.map_neg])`. Establish `hnat : ∀ (c : ℕ) (x : C), 0 < v x → 0 < v ((c : C) * x)` using `fun c x hx => by`. Rewrite using `[v.map_mul]`.

Establish `h` using `_root_.ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps.intCast_nonneg v (c : ℤ)`. Rewrite `h` using `[Int.cast_natCast]`. Conclude with `lt_of_lt_of_le hx (le_add_of_nonneg_left h)`. Establish `hsum : ∀ (s : Finset ℕ) (f : ℕ → C), (∀ j ∈ s, 0 < v (f j)) → 0 < v (∑ j ∈ s, f j)`. Introduce `s f hf`.

Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert j s hj ih`. Rewrite using `[Finset.sum_insert hj]`. Conclude with `hadd _ _ (hf j (Finset.mem_insert_self _ _)) (ih fun x hx => hf x (Finset.mem_insert_of_mem hx))`.

Use `set B : ℕ → ℕ → C := fun k y => ∑ s ∈ Finset.range (y + 1), (y.choose s : C) * a (s + k) with hB`. Establish `hpascal : ∀ k y, B (k + 1) y = B k (y + 1) - B k y`. Introduce `k y`. Simplify using `only [hB]`. Rewrite using `[sum_range_succ_choose_mul_eq_add_shift (fun s => a (s + k)) y]`.

Establish `: ∀ s, a (s + 1 + k) = a (s + (k + 1))` using `fun s => by rw [add_assoc, add_comm 1 k]`. Simplify using `only [this]`. Expand and normalize the polynomial expressions, which then agree. Establish `hup : ∀ k, k < S → ∀ y, Y0 ≤ y → y + k < Y0 + S → 0 < v (B k y)`. Introduce `k`.

Proceed by induction on `k with`. Consider the case `zero`. Introduce `_ y h1 h2`. Simplify `hcon y h1 (by omega)` using `[hB]`. Consider the case `succ k ih`.

Introduce `hk y h1 h2`. Rewrite using `[hpascal]`. Conclude with `hsub _ _ (ih (by omega) (y + 1) (by omega) (by omega)) (ih (by omega) y h1 (by omega))`. Establish `hbig : ∀ k, S ≤ k → ∀ y, 0 < v (B k y)` using `fun k hk y => hsum _ _ fun s _ => hnat _ _ (hpos _ (by omega))`. Establish `hdown : ∀ d, d ≤ Y0 → ∀ k, 0 < v (B k (Y0 - d))`.

Introduce `d`. Proceed by induction on `d with`. Consider the case `zero`. Introduce `_ k`. Distinguish the cases in `hk : k < S`.

Conclude with `hup k hk Y0 le_rfl (by simpa using hk)`. Conclude with `hbig k (by omega) _`. Consider the case `succ d ih`. Introduce `hd`. Establish `hy : Y0 - d = Y0 - (d + 1) + 1` using `by omega`.

Establish `main : ∀ m k, S ≤ k + m → 0 < v (B k (Y0 - (d + 1)))`. Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => intro k hk; exact hbig k (by omega) _`. Consider the case `succ m ihm`.

Introduce `k hk`. Establish `e` using `hpascal k (Y0 - (d + 1))`. Establish `: B k (Y0 - (d + 1)) = B k (Y0 - (d + 1) + 1) - B (k + 1) (Y0 - (d + 1))`. Rewrite using `[e]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this, ← hy]`. Conclude with `hsub _ _ (ih (by omega) k) (ihm (k + 1) (by omega))`. Conclude with `fun k => main S k (by omega)`. Establish `h0` using `hdown Y0 le_rfl 0`. Simplify using `[hB, ha0] at h0`.
-/
theorem _root_.GlobalTheory.newtonBound_pos_and_newtonStep : _root_.Formalism.L2.FormalSeriesBounds.NewtonBoundPositive ∧ _root_.Formalism.L2.FormalSeriesBounds.P7 := by
  refine ⟨?_, ?_⟩
  · unfold _root_.Formalism.L2.FormalSeriesBounds.NewtonBoundPositive
    intro l hl i n0 s hi hn hs
    unfold _root_.Formalism.L2.FormalSeriesBounds.S0 at hs
    have hl' : (5:ℝ) ≤ l := by exact_mod_cast hl
    have hN : (1:ℝ) ≤ n0 := by exact_mod_cast hn
    have hi' : (1:ℝ) ≤ i := by exact_mod_cast hi
    have hlogl : 1 ≤ Real.log l := by
      rw [Real.le_log_iff_exp_le (by linarith)]
      have := Real.exp_one_lt_d9
      linarith
    have hlbN1 : 0 ≤ Real.logb l ((n0:ℝ) + 1) := Real.logb_nonneg (by linarith) (by linarith)
    have hsK : 64 * (n0:ℝ) ^ 2 * ((i:ℝ) + 3 + 3 * Real.logb l ((n0:ℝ) + 1)) ≤ (s:ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast hs)
    have hN2 : 0 < 64 * (n0:ℝ) ^ 2 := by positivity
    set t : ℝ := (s:ℝ) / (64 * (n0:ℝ) ^ 2) with ht
    have hst : (s:ℝ) = t * 64 * (n0:ℝ) ^ 2 := by rw [ht]; field_simp
    have htK : (i:ℝ) + 3 + 3 * Real.logb l ((n0:ℝ) + 1) ≤ t := by
      rw [ht, le_div_iff₀ hN2]; linarith
    have ht0 : 0 < t := by linarith
    have hlogs : Real.logb l s = Real.logb l t + Real.logb l 64 + 2 * Real.logb l n0 := by
      rw [hst, Real.logb_mul (by positivity) (by positivity), Real.logb_mul (by positivity) (by norm_num),
        Real.logb_pow]
      push_cast
      ring
    have hlbt : Real.logb l t ≤ t - 1 := by
      have h1 := Real.log_le_sub_one_of_pos ht0
      have h2 : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
      rw [Real.logb, div_le_iff₀ (by linarith)]
      nlinarith
    have hlb64 : Real.logb l 64 ≤ 3 := by
      have h3 : Real.logb l ((l:ℝ) ^ 3) = 3 := by
        rw [Real.logb_pow, Real.logb_self_eq_one (by linarith)]
        norm_num
      rw [← h3]
      apply Real.logb_le_logb_of_le (by linarith) (by norm_num)
      have hcube : (5:ℝ) ^ 3 ≤ (l:ℝ) ^ 3 := pow_le_pow_left₀ (by norm_num) hl' 3
      linarith
    have hlbN : Real.logb l n0 ≤ Real.logb l ((n0:ℝ) + 1) :=
      Real.logb_le_logb_of_le (by linarith) (by linarith) (by linarith)
    have key : 3 * Real.logb l n0 + 2 * Real.logb l s + i + 3 < 8 * t := by
      rw [hlogs]
      nlinarith
    have hs8 : (s:ℝ) / 8 = 8 * t * (n0:ℝ) ^ 2 := by rw [hst]; ring
    rw [hs8]
    have hpos : 0 < (n0:ℝ) ^ 2 := by positivity
    nlinarith [mul_lt_mul_of_pos_left key hpos]
  · unfold _root_.Formalism.L2.FormalSeriesBounds.P7
    intro C _ v S a hS ha0 hpos Y0
    by_contra hcon
    push_neg at hcon
    have hadd : ∀ x y : C, 0 < v x → 0 < v y → 0 < v (x + y) := fun x y hx hy =>
      lt_of_lt_of_le (lt_min hx hy) (v.map_add x y)
    have hsub : ∀ x y : C, 0 < v x → 0 < v y → 0 < v (x - y) := fun x y hx hy => by
      rw [sub_eq_add_neg]
      exact hadd _ _ hx (by rwa [v.map_neg])
    have hnat : ∀ (c : ℕ) (x : C), 0 < v x → 0 < v ((c : C) * x) := fun c x hx => by
      rw [v.map_mul]
      have h := _root_.ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps.intCast_nonneg v (c : ℤ)
      rw [Int.cast_natCast] at h
      exact lt_of_lt_of_le hx (le_add_of_nonneg_left h)
    have hsum : ∀ (s : Finset ℕ) (f : ℕ → C), (∀ j ∈ s, 0 < v (f j)) → 0 < v (∑ j ∈ s, f j) := by
      intro s f hf
      induction s using Finset.induction_on with
      | empty => simp
      | insert j s hj ih =>
        rw [Finset.sum_insert hj]
        exact hadd _ _ (hf j (Finset.mem_insert_self _ _))
          (ih fun x hx => hf x (Finset.mem_insert_of_mem hx))
    set B : ℕ → ℕ → C := fun k y => ∑ s ∈ Finset.range (y + 1), (y.choose s : C) * a (s + k) with hB
    have hpascal : ∀ k y, B (k + 1) y = B k (y + 1) - B k y := by
      intro k y
      simp only [hB]
      rw [sum_range_succ_choose_mul_eq_add_shift (fun s => a (s + k)) y]
      have : ∀ s, a (s + 1 + k) = a (s + (k + 1)) := fun s => by rw [add_assoc, add_comm 1 k]
      simp only [this]
      ring
    have hup : ∀ k, k < S → ∀ y, Y0 ≤ y → y + k < Y0 + S → 0 < v (B k y) := by
      intro k
      induction k with
      | zero =>
        intro _ y h1 h2
        simpa [hB] using hcon y h1 (by omega)
      | succ k ih =>
        intro hk y h1 h2
        rw [hpascal]
        exact hsub _ _ (ih (by omega) (y + 1) (by omega) (by omega)) (ih (by omega) y h1 (by omega))
    have hbig : ∀ k, S ≤ k → ∀ y, 0 < v (B k y) := fun k hk y =>
      hsum _ _ fun s _ => hnat _ _ (hpos _ (by omega))
    have hdown : ∀ d, d ≤ Y0 → ∀ k, 0 < v (B k (Y0 - d)) := by
      intro d
      induction d with
      | zero =>
        intro _ k
        by_cases hk : k < S
        · exact hup k hk Y0 le_rfl (by simpa using hk)
        · exact hbig k (by omega) _
      | succ d ih =>
        intro hd
        have hy : Y0 - d = Y0 - (d + 1) + 1 := by omega
        have main : ∀ m k, S ≤ k + m → 0 < v (B k (Y0 - (d + 1))) := by
          intro m
          induction m with
          | zero => intro k hk; exact hbig k (by omega) _
          | succ m ihm =>
            intro k hk
            have e := hpascal k (Y0 - (d + 1))
            have : B k (Y0 - (d + 1)) = B k (Y0 - (d + 1) + 1) - B (k + 1) (Y0 - (d + 1)) := by
              rw [e]; ring
            rw [this, ← hy]
            exact hsub _ _ (ih (by omega) k) (ihm (k + 1) (by omega))
        exact fun k => main S k (by omega)
    have h0 := hdown Y0 le_rfl 0
    simp [hB, ha0] at h0

end GlobalTheory
