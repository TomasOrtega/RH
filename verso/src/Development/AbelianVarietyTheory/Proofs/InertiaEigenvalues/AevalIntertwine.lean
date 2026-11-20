import Mathlib

namespace GlobalTheory.AevalIntertwine

/- English proof (translation)
Introduce `K M N _ _ _ _ _ f A B h p`. Use `Polynomial.induction_on p ?_ ?_ ?_` and prove the remaining obligations. Introduce `a x`. Simplify using `[Polynomial.aeval_C, Module.algebraMap_end_apply]`. Introduce `p q hp hq x`.

Simplify using `only [map_add, LinearMap.add_apply, hp, hq]`. Introduce `n a ih x`. Establish `e : ∀ {V : Type} [AddCommGroup V] [Module K V] (E : Module.End K V) (y : V), Polynomial.aeval E (Polynomial.C a * Polynomial.X ^ (n + 1)) y = Polynomial.aeval E (Polynomial.C a * Polynomial.X ^ n) (E y)`. Introduce `V _ _ E y`. Rewrite using `[pow_succ, ← mul_assoc, map_mul, Polynomial.aeval_X, Module.End.mul_apply]`.

Rewrite using `[e, e, ih, h]`.
-/
theorem aeval_intertwine : ∀ {K M N : Type} [inst : Field K] [inst_1 : AddCommGroup M] [inst_2 : Module K M] [inst_3 : AddCommGroup N] [inst_4 : Module K N] (f : M →ₗ[K] N) (A : Module.End K M) (B : Module.End K N), (∀ (x : M), (f : M → N) ((A : M → M) x) = (B : N → N) ((f : M → N) x)) → ∀ (p : Polynomial K) (x : M), (f : M → N) (((Polynomial.aeval A : Polynomial K → Module.End K M) p : M → M) x) = ((Polynomial.aeval B : Polynomial K → Module.End K N) p : N → N) ((f : M → N) x) := by
  intro K M N _ _ _ _ _ f A B h p
  refine Polynomial.induction_on p ?_ ?_ ?_
  · intro a x
    simp [Polynomial.aeval_C, Module.algebraMap_end_apply]
  · intro p q hp hq x
    simp only [map_add, LinearMap.add_apply, hp, hq]
  · intro n a ih x
    have e : ∀ {V : Type} [AddCommGroup V] [Module K V] (E : Module.End K V) (y : V),
        Polynomial.aeval E (Polynomial.C a * Polynomial.X ^ (n + 1)) y
          = Polynomial.aeval E (Polynomial.C a * Polynomial.X ^ n) (E y) := by
      intro V _ _ E y
      rw [pow_succ, ← mul_assoc, map_mul, Polynomial.aeval_X, Module.End.mul_apply]
    rw [e, e, ih, h]

end GlobalTheory.AevalIntertwine
