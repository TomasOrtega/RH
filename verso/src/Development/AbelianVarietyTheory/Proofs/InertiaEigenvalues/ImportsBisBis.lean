import Mathlib

namespace GlobalTheory.PowerMembershipInertiaEigenvalues

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => intro y hy`. Simplify using `using hy`. Consider the case `succ n ih`. Introduce `y hy`.

Rewrite using `[pow_succ, Module.End.mul_apply]`. Conclude with `ih _ (hT y hy)`.
-/
theorem pow_mem {k U : Type} [Field k] [AddCommGroup U] [Module k U] (T : Module.End k U)
    (Q : Submodule k U) (hT : ∀ y ∈ Q, (T : U → U) y ∈ Q) (n : ℕ) :
    ∀ y ∈ Q, ((T ^ n : Module.End k U) : U → U) y ∈ Q := by
  induction n with
  | zero => intro y hy; simpa using hy
  | succ n ih =>
    intro y hy
    rw [pow_succ, Module.End.mul_apply]
    exact ih _ (hT y hy)

/- English proof (translation)
Introduce `k U _ _ _ T Q hT p`. Proceed by induction on `p using Polynomial.induction_on' with`. Consider the case `add p q hp hq`. Introduce `y hy`. Simplify using `only [map_add, LinearMap.add_apply]`.

Conclude with `Q.add_mem (hp y hy) (hq y hy)`. Consider the case `monomial n a`. Introduce `y hy`. Rewrite using `[Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]`. Conclude with `Q.smul_mem a (pow_mem T Q hT n y hy)`.
-/
theorem main : ∀ {k U : Type} [inst : Field k] [inst_1 : AddCommGroup U] [inst_2 : Module k U] (T : Module.End k U) (Q : Submodule k U), (∀ y ∈ Q, (T : U → U) y ∈ Q) → ∀ (p : Polynomial k), ∀ y ∈ Q, ((Polynomial.aeval T : Polynomial k → Module.End k U) p : U → U) y ∈ Q := by
  intro k U _ _ _ T Q hT p
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    intro y hy
    simp only [map_add, LinearMap.add_apply]
    exact Q.add_mem (hp y hy) (hq y hy)
  | monomial n a =>
    intro y hy
    rw [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
    exact Q.smul_mem a (pow_mem T Q hT n y hy)

end GlobalTheory.PowerMembershipInertiaEigenvalues
