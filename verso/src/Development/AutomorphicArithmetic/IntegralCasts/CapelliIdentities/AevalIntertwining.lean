import Mathlib

/- English proof (translation)
Introduce `K _ M N _ _ _ _ φ f f' h p`. Establish `hpow : ∀ (n : ℕ) (x : M), φ ((f ^ n) x) = (f' ^ n) (φ x)`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro x`.

Simplify using the standard rewrite rules. Consider the case `succ n ih`. Introduce `x`. Rewrite using `[pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, h]`. Proceed by induction on `p using Polynomial.induction_on' with`.

Consider the case `add p q hp hq`. Introduce `x`. Simplify using `only [map_add, LinearMap.add_apply, hp, hq]`. Consider the case `monomial n a`. Introduce `x`.

Simplify using `only [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply, map_smul, hpow]`.
-/
theorem UpperTheory.Reformulated.B.AevalIntertwining.aeval_intertwine :
    ∀ {K : Type} [inst : Field K] {M N : Type} [inst_1 : AddCommGroup M]
    [inst_2 : _root_.Module K M] [inst_3 : AddCommGroup N] [inst_4 : _root_.Module K N] (φ : M →ₗ[K] N)
    (f : Module.End K M) (f' : Module.End K N),
    (∀ (x : M), (φ : M → N) ((f : M → M) x) = (f' : N → N) ((φ : M → N) x)) →
      ∀ (p : Polynomial K) (x : M),
        (φ : M → N) (((Polynomial.aeval f : Polynomial K → Module.End K M) p : M → M) x) =
          ((Polynomial.aeval f' : Polynomial K → Module.End K N) p : N → N) ((φ : M → N) x) := by
  intro K _ M N _ _ _ _ φ f f' h p
  have hpow : ∀ (n : ℕ) (x : M), φ ((f ^ n) x) = (f' ^ n) (φ x) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, h]
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    intro x
    simp only [map_add, LinearMap.add_apply, hp, hq]
  | monomial n a =>
    intro x
    simp only [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply,
      map_smul, hpow]
