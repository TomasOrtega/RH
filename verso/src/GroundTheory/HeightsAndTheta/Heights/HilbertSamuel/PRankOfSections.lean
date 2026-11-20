import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsHilbert
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

namespace RankOfSections

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero`. Establish `h0` using `hf bs j 0 0`. Simplify using `only [add_zero] at h0`. Simplify using `only [zero_smul, Nat.cast_zero, zero_mul]`.

Combine the linear equalities and inequalities to obtain the conclusion. Consider the case `succ m ih`. Rewrite using `[succ_nsmul, hf, ih]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem position_nsmul {d : ℕ} {A : Type*} [AddCommGroup A] (f : (Fin d → A) → ℤ)
    (hf : ∀ (bs : Fin d → A) (j : Fin d) (x y : A),
      f (Function.update bs j (x + y)) = f (Function.update bs j x) + f (Function.update bs j y))
    (bs : Fin d → A) (j : Fin d) (m : ℕ) (y : A) :
    f (Function.update bs j (m • y)) = (m : ℤ) * f (Function.update bs j y) := by
  induction m with
  | zero =>
    have h0 := hf bs j 0 0
    simp only [add_zero] at h0
    simp only [zero_smul, Nat.cast_zero, zero_mul]
    linarith
  | succ m ih =>
    rw [succ_nsmul, hf, ih]
    push_cast
    ring

/- English proof (translation)
Establish `key : ∀ s : Finset (Fin d), f (fun i => if i ∈ s then n • x else x) = (n : ℤ) ^ s.card * f (fun _ => x)`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert j s hj ih`.

Establish `e : (fun i => if i ∈ insert j s then n • x else x) = Function.update (fun i => if i ∈ s then n • x else x) j (n • x)`. Use function extensionality and compare the values at `i`. Distinguish the cases in `hi : i = j`. Substitute `hi` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[hi]`. Establish `e2 : Function.update (fun i => if i ∈ s then n • x else x) j x = (fun i => if i ∈ s then n • x else x)`. Use function extensionality and compare the values at `i`. Distinguish the cases in `hi : i = j`. Substitute `hi` using the available equality.

Simplify using `[hj]`. Simplify using `[Function.update_of_ne hi]`. Rewrite using `[e, position_nsmul f hf, e2, ih, Finset.card_insert_of_notMem hj, pow_succ]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `using key Finset.univ`.
-/
theorem const_nsmul {d : ℕ} {A : Type*} [AddCommGroup A] (f : (Fin d → A) → ℤ)
    (hf : ∀ (bs : Fin d → A) (j : Fin d) (x y : A),
      f (Function.update bs j (x + y)) = f (Function.update bs j x) + f (Function.update bs j y))
    (n : ℕ) (x : A) :
    f (fun _ => n • x) = (n : ℤ) ^ d * f (fun _ => x) := by
  classical
  have key : ∀ s : Finset (Fin d),
      f (fun i => if i ∈ s then n • x else x) = (n : ℤ) ^ s.card * f (fun _ => x) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert j s hj ih =>
      have e : (fun i => if i ∈ insert j s then n • x else x) =
          Function.update (fun i => if i ∈ s then n • x else x) j (n • x) := by
        funext i
        by_cases hi : i = j
        · subst hi
          simp
        · simp [hi]
      have e2 : Function.update (fun i => if i ∈ s then n • x else x) j x =
          (fun i => if i ∈ s then n • x else x) := by
        funext i
        by_cases hi : i = j
        · subst hi
          simp [hj]
        · simp [Function.update_of_ne hi]
      rw [e, position_nsmul f hf, e2, ih, Finset.card_insert_of_notMem hj, pow_succ]
      ring
  simpa using key Finset.univ

/- English proof (translation)
Use `⟨max C (∑ k ∈ Finset.range a₀, |f k| / ((k : ℝ) + 1) ^ r), fun n => ?_⟩` and prove the remaining obligations. Establish `hp : 0 < ((n : ℝ) + 1) ^ r` using `by positivity`. Break down `le_or_gt a₀ n with hn | hn` into its components or cases. Conclude with `(h n hn).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hp.le)`. Establish `h1 : |f n| / ((n : ℝ) + 1) ^ r ≤ ∑ k ∈ Finset.range a₀, |f k| / ((k : ℝ) + 1) ^ r` using `Finset.single_le_sum (f := fun k => |f k| / ((k : ℝ) + 1) ^ r) (fun k _ => by positivity) (Finset.mem_range.2 hn)`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem bound_of_eventually (f : ℕ → ℝ) (r : ℝ) (a₀ : ℕ) (C : ℝ)
    (h : ∀ n, a₀ ≤ n → |f n| ≤ C * ((n : ℝ) + 1) ^ r) :
    ∃ C' : ℝ, ∀ n : ℕ, |f n| ≤ C' * ((n : ℝ) + 1) ^ r := by
  refine ⟨max C (∑ k ∈ Finset.range a₀, |f k| / ((k : ℝ) + 1) ^ r), fun n => ?_⟩
  have hp : 0 < ((n : ℝ) + 1) ^ r := by positivity
  rcases le_or_gt a₀ n with hn | hn
  · exact (h n hn).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hp.le)
  · have h1 : |f n| / ((n : ℝ) + 1) ^ r ≤ ∑ k ∈ Finset.range a₀, |f k| / ((k : ℝ) + 1) ^ r :=
      Finset.single_le_sum (f := fun k => |f k| / ((k : ℝ) + 1) ^ r)
        (fun k _ => by positivity) (Finset.mem_range.2 hn)
    calc |f n| = |f n| / ((n : ℝ) + 1) ^ r * ((n : ℝ) + 1) ^ r := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (h1.trans (le_max_right _ _)) hp.le

/- English proof (translation)
Introduce `ι₀ _ q D hq hdim`. Establish `hdim' : ringKrullDim (MRing (fun _ : Unit => ι₀) ℚ ⧸ q) = ((D + Fintype.card Unit : ℕ) : WithBot ℕ∞)`. Simplify using `using hdim`. Take `⟨a₀, C, hC⟩` from `hP D ℚ Unit (fun _ => ι₀) q hq hdim'`. Establish `hadd` using `(hM ℚ Unit (fun _ => ι₀) q D hq hdim').2`.

Establish `hhom : ∀ n : ℕ, intNum ℚ q (fun _ : Fin D => fun _ : Unit => (n : ℤ)) = (n : ℤ) ^ D * intNum ℚ q (fun _ : Fin D => fun _ : Unit => (1 : ℤ))`. Introduce `n`. Use `const_nsmul (fun bs => intNum ℚ q bs) hadd n (fun _ : Unit => (1 : ℤ))` as an intermediate fact. Establish `e : (n • fun _ : Unit => (1 : ℤ)) = fun _ : Unit => (n : ℤ)`. Use function extensionality and compare the values at `u`.

Simplify using the standard rewrite rules. Rewrite `this` using `[e]`. Conclude with `this`. Apply `bound_of_eventually _ _ a₀ C` to reduce the goal to its premises. Introduce `n hn`.

Establish `h` using `hC (fun _ => n) (fun _ => hn)`. Simplify using `only [Finset.univ_unique, Finset.sum_singleton] at h`. Rewrite `h` using `[hhom n]`. Use `h using 3` and compare the differences between its conclusion and the goal. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem proof (hP : HilbertPrime.Statement.{0}) (hM : MixedNumberPolynomial.Statement.{0}) :
    RankOfSections.Statement := by
  intro ι₀ _ q D hq hdim
  have hdim' : ringKrullDim (MRing (fun _ : Unit => ι₀) ℚ ⧸ q) =
      ((D + Fintype.card Unit : ℕ) : WithBot ℕ∞) := by
    simpa using hdim
  obtain ⟨a₀, C, hC⟩ := hP D ℚ Unit (fun _ => ι₀) q hq hdim'
  have hadd := (hM ℚ Unit (fun _ => ι₀) q D hq hdim').2
  have hhom : ∀ n : ℕ, intNum ℚ q (fun _ : Fin D => fun _ : Unit => (n : ℤ)) =
      (n : ℤ) ^ D * intNum ℚ q (fun _ : Fin D => fun _ : Unit => (1 : ℤ)) := by
    intro n
    have := const_nsmul (fun bs => intNum ℚ q bs) hadd n (fun _ : Unit => (1 : ℤ))
    have e : (n • fun _ : Unit => (1 : ℤ)) = fun _ : Unit => (n : ℤ) := by
      funext u
      simp
    rw [e] at this
    exact this
  apply bound_of_eventually _ _ a₀ C
  intro n hn
  have h := hC (fun _ => n) (fun _ => hn)
  simp only [Finset.univ_unique, Finset.sum_singleton] at h
  rw [hhom n] at h
  convert h using 3
  push_cast
  ring

end RankOfSections

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
