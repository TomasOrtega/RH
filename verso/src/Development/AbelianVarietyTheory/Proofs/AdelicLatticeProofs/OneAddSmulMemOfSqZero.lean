import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

/- English proof (translation)
Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C a => exact ⟨Polynomial.C (algebraMap ℚ ℂ a), fun t => by simp [ev]⟩`. Consider the case `add f g hf hg`. Take `⟨p, hp⟩` from `hf`. Take `⟨q, hq⟩` from `hg`.

Use `⟨p + q, fun t => ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.eval_add, hp, hq]`. Simplify using `[ev]`. Consider the case `mul_X f ij hf`. Take `⟨p, hp⟩` from `hf`.

Use `⟨p * (Polynomial.C (A ij.1 ij.2) + Polynomial.X * Polynomial.C (B ij.1 ij.2)), fun t => ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.eval_mul, hp, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_C, Polynomial.eval_X]`. Simplify using `[ev]`.
-/
theorem exists_poly_ev_line {ι : Type} [Fintype ι] [DecidableEq ι] (f : MvPolynomial (ι × ι) ℚ)
    (A B : Matrix ι ι ℂ) : ∃ p : Polynomial ℂ, ∀ t : ℂ, p.eval t = ev f (A + t • B) := by
  induction f using MvPolynomial.induction_on with
  | C a => exact ⟨Polynomial.C (algebraMap ℚ ℂ a), fun t => by simp [ev]⟩
  | add f g hf hg =>
    obtain ⟨p, hp⟩ := hf
    obtain ⟨q, hq⟩ := hg
    refine ⟨p + q, fun t => ?_⟩
    rw [Polynomial.eval_add, hp, hq]
    simp [ev]
  | mul_X f ij hf =>
    obtain ⟨p, hp⟩ := hf
    refine ⟨p * (Polynomial.C (A ij.1 ij.2) + Polynomial.X * Polynomial.C (B ij.1 ij.2)), fun t => ?_⟩
    rw [Polynomial.eval_mul, hp, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_C, Polynomial.eval_X]
    simp [ev]

/- English proof (translation)
Introduce `ι _ _ Γ hΓ ε hε h1 t`. Establish `hn : ∀ n : ℕ, 1 + (n : ℂ) • ε ∈ Γ`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simpa using hΓ.one_mem`.

Consider the case `succ n ih`. Establish `h` using `hΓ.mul_mem _ ih _ h1`. Establish `e : (1 + (n : ℂ) • ε) * (1 + ε) = 1 + ((n + 1 : ℕ) : ℂ) • ε`. Rewrite using `[mul_add, mul_one, add_mul, one_mul, smul_mul_assoc, hε, smul_zero, add_zero, Nat.cast_succ, add_smul, one_smul, add_assoc]`. Rewrite `h` using `[e]`. Then use the resulting hypothesis.

Apply `hΓ.closed` to reduce the goal to its premises. Introduce `f hf`. Take `⟨p, hp⟩` from `exists_poly_ev_line f 1 ε`. Establish `hp0 : p = 0`. Apply `Polynomial.eq_zero_of_infinite_isRoot` to reduce the goal to its premises.

Use `Set.infinite_of_injective_forall_mem (f := fun n : ℕ => (n : ℂ)) Nat.cast_injective ?_` and prove the remaining obligations. Introduce `n`. Use `show p.eval (n : ℂ) = 0`. Rewrite using `[hp]`. Conclude with `hf _ (hn n)`.

Rewrite using `[← hp, hp0, Polynomial.eval_zero]`.
-/
theorem one_add_smul_mem_of_sq_zero :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), IsQGroup Γ →
      ∀ ε : Matrix ι ι ℂ, ε * ε = 0 → 1 + ε ∈ Γ → ∀ t : ℂ, 1 + t • ε ∈ Γ := by
  intro ι _ _ Γ hΓ ε hε h1 t
  have hn : ∀ n : ℕ, 1 + (n : ℂ) • ε ∈ Γ := by
    intro n
    induction n with
    | zero => simpa using hΓ.one_mem
    | succ n ih =>
      have h := hΓ.mul_mem _ ih _ h1
      have e : (1 + (n : ℂ) • ε) * (1 + ε) = 1 + ((n + 1 : ℕ) : ℂ) • ε := by
        rw [mul_add, mul_one, add_mul, one_mul, smul_mul_assoc, hε, smul_zero, add_zero, Nat.cast_succ,
          add_smul, one_smul, add_assoc]
      rwa [e] at h
  apply hΓ.closed
  intro f hf
  obtain ⟨p, hp⟩ := exists_poly_ev_line f 1 ε
  have hp0 : p = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ => (n : ℂ)) Nat.cast_injective ?_
    intro n
    show p.eval (n : ℂ) = 0
    rw [hp]
    exact hf _ (hn n)
  rw [← hp, hp0, Polynomial.eval_zero]

end GlobalTheory.ClassFin
