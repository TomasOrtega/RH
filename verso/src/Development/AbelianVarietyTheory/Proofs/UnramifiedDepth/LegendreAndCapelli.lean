import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.BiadditiveInSingleVariables
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LegendreBoundsFactorialMultiIndexCapelli
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds

namespace GlobalTheory.LegendreFacts

open GlobalTheory.LegendreBounds

/- English proof (translation)
Unfold `mfact`. Conclude with `Finsupp.prod_fintype A _ (fun _ => Nat.factorial_zero)`.
-/
theorem mfact_eq_prod {σ : Type} [Fintype σ] (A : σ →₀ ℕ) :
    mfact A = ∏ j, (A j).factorial := by
  unfold mfact
  exact Finsupp.prod_fintype A _ (fun _ => Nat.factorial_zero)

/- English proof (translation)
Rewrite using `[Finsupp.degree_apply]`. Use `Finset.sum_subset (Finset.subset_univ _) ?_` and prove the remaining obligations. Introduce `j _ hj`. Simplify using `using hj`.
-/
theorem degree_eq_sum' {σ : Type} [Fintype σ] (A : σ →₀ ℕ) : A.degree = ∑ j, A j := by
  rw [Finsupp.degree_apply]
  refine Finset.sum_subset (Finset.subset_univ _) ?_
  intro j _ hj
  simpa using hj

/- English proof (translation)
Unfold `capNat`. Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl ?_` and prove the remaining obligations. Introduce `c _`. Conclude with `Nat.div_mul_cancel (Nat.factorial_dvd_factorial (Nat.le_add_left c x))`.
-/
theorem capNat_mul (n0 x : ℕ) :
    capNat n0 x * ∏ c ∈ Finset.range n0, c.factorial
      = ∏ c ∈ Finset.range n0, (x + c).factorial := by
  unfold capNat
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl ?_
  intro c _
  exact Nat.div_mul_cancel (Nat.factorial_dvd_factorial (Nat.le_add_left c x))

/- English proof (translation)
Establish `: Fact l.Prime` using `⟨hl⟩`. Break down `Nat.eq_zero_or_pos N with h0 | hpos` into its components or cases. Substitute `h0` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[padicValNat_factorial (b := 2) (Nat.log_lt_of_lt_pow hpos.ne' hN)]`.

Simplify using the standard rewrite rules.
-/
private lemma padicValNat_factorial_eq_div_of_lt_sq (l : ℕ) (hl : l.Prime) (N : ℕ) (hN : N < l ^ 2) :
    padicValNat l N.factorial = N / l := by
  have : Fact l.Prime := ⟨hl⟩
  rcases Nat.eq_zero_or_pos N with h0 | hpos
  · subst h0
    simp
  · rw [padicValNat_factorial (b := 2) (Nat.log_lt_of_lt_pow hpos.ne' hN)]
    simp

/- English proof (translation)
Introduce `l hl`. Establish `hl1 : (1 : ℝ) < l` using `by exact_mod_cast hl.one_lt`. Establish `hden : (0 : ℝ) < (l : ℝ) - 1` using `by linarith`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `N`.

Establish `h` using `legendre_real l hl N`. Simplify using `using h`. Introduce `N _`. Establish `h` using `digitSum_le l N hl.one_lt`. Rewrite using `[Real.natFloor_logb_natCast]`.

Establish `hc : (((Nat.digits l N).sum : ℕ) : ℝ) ≤ (((Nat.log l N + 1) * (l - 1) : ℕ) : ℝ)`. Conclude with `h` after adjusting the coercions. Rewrite `hc` using `[Nat.cast_mul, Nat.cast_sub hl.one_lt.le, Nat.cast_add, Nat.cast_one]`. Rewrite using `[mul_comm]`. Conclude with `hc`.

Introduce `σ _ A hA`. Rewrite using `[mfact_eq_prod, degree_eq_sum']`. Rewrite `hA` using `[degree_eq_sum']`. Prove the components needed by the constructor for the conclusion. Establish `h` using `((legendre_bounds l hl).2.1) σ (fun j => A j) hA`.

Simplify using `using h`. Rewrite using `[padicValNat_prod_factorial l hl Finset.univ (fun j => A j)]`. Establish `hterm : ∀ j ∈ (Finset.univ : Finset σ), (padicValNat l (A j).factorial : ℝ) ≤ (A j : ℝ) / ((l : ℝ) - 1)` using `fun j _ => upper l hl (A j)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Finset.sum_div]`.

Use `push_cast`. Both sides reduce to the same expression. Introduce `N hN`. Conclude with `padicValNat_factorial_eq_div_of_lt_sq l hl N hN`.
-/
theorem legendre_facts : F2 := by
  intro l hl
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.one_lt
  have hden : (0 : ℝ) < (l : ℝ) - 1 := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro N
    have h := legendre_real l hl N
    simpa using h
  · intro N _
    have h := digitSum_le l N hl.one_lt
    rw [Real.natFloor_logb_natCast]
    have hc : (((Nat.digits l N).sum : ℕ) : ℝ) ≤ (((Nat.log l N + 1) * (l - 1) : ℕ) : ℝ) := by
      exact_mod_cast h
    rw [Nat.cast_mul, Nat.cast_sub hl.one_lt.le, Nat.cast_add, Nat.cast_one] at hc
    rw [mul_comm]
    exact hc
  · intro σ _ A hA
    rw [mfact_eq_prod, degree_eq_sum']
    rw [degree_eq_sum'] at hA
    constructor
    · have h := ((legendre_bounds l hl).2.1) σ (fun j => A j) hA
      simpa using h
    · rw [padicValNat_prod_factorial l hl Finset.univ (fun j => A j)]
      have hterm : ∀ j ∈ (Finset.univ : Finset σ),
          (padicValNat l (A j).factorial : ℝ) ≤ (A j : ℝ) / ((l : ℝ) - 1) :=
        fun j _ => upper l hl (A j)
      calc ∑ j, (padicValNat l (A j).factorial : ℝ)
          ≤ ∑ j, (A j : ℝ) / ((l : ℝ) - 1) := Finset.sum_le_sum hterm
        _ = ((∑ j, A j : ℕ) : ℝ) / ((l : ℝ) - 1) := by
          rw [← Finset.sum_div]
          push_cast
          rfl
  · intro N hN
    exact padicValNat_factorial_eq_div_of_lt_sq l hl N hN

/- English proof (translation)
Introduce `l hl n0 n x hn hn0`. Establish `hl1 : (1 : ℝ) < l` using `by exact_mod_cast hl.one_lt`. Establish `: Fact l.Prime` using `⟨hl⟩`. Prove the components needed by the constructor for the conclusion. Establish `hP : (∏ c ∈ Finset.range n0, c.factorial) ≠ 0` using `Finset.prod_ne_zero_iff.mpr (fun c _ => Nat.factorial_ne_zero c)`.

Establish `hC : capNat n0 x ≠ 0`. Introduce `h0`. Establish `h` using `capNat_mul n0 x`. Rewrite `h` using `[h0, zero_mul]`. Conclude with `(Finset.prod_ne_zero_iff.mpr (fun c _ => Nat.factorial_ne_zero (x + c))) h.symm`.

Establish `hv : padicValNat l (capNat n0 x) + padicValNat l (∏ c ∈ Finset.range n0, c.factorial) = padicValNat l (∏ c ∈ Finset.range n0, (x + c).factorial)`. Rewrite using `[← padicValNat.mul hC hP, capNat_mul]`. Establish `hvR : (padicValNat l (capNat n0 x) : ℝ) = (padicValNat l (∏ c ∈ Finset.range n0, (x + c).factorial) : ℝ) - (padicValNat l (∏ c ∈ Finset.range n0, c.factorial) : ℝ)`. Rewrite using `[← hv]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `h` using `((legendre_bounds l hl).2.2) n0 x`. Rewrite using `[hvR]`. Conclude with `h`. Establish `hlogn : 0 ≤ Real.logb l n` using `Real.logb_nonneg hl1 (by exact_mod_cast hn)`.

Establish `hnn : (n0 : ℝ) ≤ n` using `by exact_mod_cast hn0`. Break down `Nat.eq_zero_or_pos n0 with h0 | hpos` into its components or cases. Substitute `h0` using the available equality. Establish `: (0 : ℝ) ≤ (n : ℝ) * (Real.logb l n + 1)` using `by positivity`. Simplify using `using this`.

Establish `hpos' : (0 : ℝ) < n0` using `by exact_mod_cast hpos`. Establish `hlog0 : 0 ≤ Real.logb l n0` using `Real.logb_nonneg hl1 (by exact_mod_cast hpos)`. Establish `hle : Real.logb l n0 ≤ Real.logb l n` using `Real.logb_le_logb_of_le hl1 hpos' hnn`. Establish `: (n0 : ℝ) * (Real.logb l n0 + 1) ≤ n * (Real.logb l n + 1)` using `mul_le_mul hnn (by linarith) (by linarith) (by positivity)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem capelli_bound : F3 := by
  intro l hl n0 n x hn hn0
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.one_lt
  have : Fact l.Prime := ⟨hl⟩
  constructor
  · have hP : (∏ c ∈ Finset.range n0, c.factorial) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun c _ => Nat.factorial_ne_zero c)
    have hC : capNat n0 x ≠ 0 := by
      intro h0
      have h := capNat_mul n0 x
      rw [h0, zero_mul] at h
      exact (Finset.prod_ne_zero_iff.mpr (fun c _ => Nat.factorial_ne_zero (x + c))) h.symm
    have hv : padicValNat l (capNat n0 x) + padicValNat l (∏ c ∈ Finset.range n0, c.factorial)
        = padicValNat l (∏ c ∈ Finset.range n0, (x + c).factorial) := by
      rw [← padicValNat.mul hC hP, capNat_mul]
    have hvR : (padicValNat l (capNat n0 x) : ℝ)
        = (padicValNat l (∏ c ∈ Finset.range n0, (x + c).factorial) : ℝ)
          - (padicValNat l (∏ c ∈ Finset.range n0, c.factorial) : ℝ) := by
      rw [← hv]
      push_cast
      ring
    have h := ((legendre_bounds l hl).2.2) n0 x
    rw [hvR]
    exact h
  · have hlogn : 0 ≤ Real.logb l n := Real.logb_nonneg hl1 (by exact_mod_cast hn)
    have hnn : (n0 : ℝ) ≤ n := by exact_mod_cast hn0
    rcases Nat.eq_zero_or_pos n0 with h0 | hpos
    · subst h0
      have : (0 : ℝ) ≤ (n : ℝ) * (Real.logb l n + 1) := by positivity
      simpa using this
    · have hpos' : (0 : ℝ) < n0 := by exact_mod_cast hpos
      have hlog0 : 0 ≤ Real.logb l n0 := Real.logb_nonneg hl1 (by exact_mod_cast hpos)
      have hle : Real.logb l n0 ≤ Real.logb l n := Real.logb_le_logb_of_le hl1 hpos' hnn
      have : (n0 : ℝ) * (Real.logb l n0 + 1) ≤ n * (Real.logb l n + 1) :=
        mul_le_mul hnn (by linarith) (by linarith) (by positivity)
      linarith

end GlobalTheory.LegendreFacts
