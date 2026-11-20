import Mathlib

/- English proof (translation)
Introduce `Y _ _ A p hA q y hy`. Establish `hpow : ∀ n : ℕ, (A ^ n) y ∈ p`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simpa using hy`.

Consider the case `succ n ih`. Rewrite using `[pow_succ', Module.End.mul_apply]`. Conclude with `hA _ ih`. Rewrite using `[Polynomial.aeval_eq_sum_range, LinearMap.sum_apply]`. Use `p.sum_mem fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[LinearMap.smul_apply]`. Conclude with `p.smul_mem _ (hpow i)`.
-/
theorem UpperTheory.Reformulated.B.Qj11.aeval_mem_invariant_submodule.{u_1} :
    ∀ {Y : Type u_1} [inst : AddCommGroup Y] [inst_1 : _root_.Module ℂ Y]
    (A : Module.End ℂ Y) (p : Submodule ℂ Y),
    (∀ y ∈ p, (A : Y → Y) y ∈ p) →
      ∀ (q : Polynomial ℂ), ∀ y ∈ p, ((Polynomial.aeval A : Polynomial ℂ → Module.End ℂ Y) q : Y → Y) y ∈ p := by
  intro Y _ _ A p hA q y hy
  have hpow : ∀ n : ℕ, (A ^ n) y ∈ p := by
    intro n
    induction n with
    | zero => simpa using hy
    | succ n ih =>
      rw [pow_succ', Module.End.mul_apply]
      exact hA _ ih
  rw [Polynomial.aeval_eq_sum_range, LinearMap.sum_apply]
  refine p.sum_mem fun i _ => ?_
  rw [LinearMap.smul_apply]
  exact p.smul_mem _ (hpow i)
