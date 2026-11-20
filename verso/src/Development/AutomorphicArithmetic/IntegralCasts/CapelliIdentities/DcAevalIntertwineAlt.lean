import Mathlib

/- English proof (translation)
Introduce `Y Z _ _ _ _ ψ A B h p`. Establish `hpow : ∀ (n : ℕ) (y : Y), ψ ((A ^ n) y) = (B ^ n) (ψ y)`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro y`.

Simplify using the standard rewrite rules. Consider the case `succ n ih`. Introduce `y`. Rewrite using `[pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, h]`. Proceed by induction on `p using Polynomial.induction_on' with`.

Consider the case `add p q hp hq`. Introduce `y`. Rewrite using `[map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, map_add, hp, hq]`. Consider the case `monomial n a`. Introduce `y`.

Rewrite using `[Polynomial.aeval_monomial, Polynomial.aeval_monomial, Module.End.mul_apply, Module.End.mul_apply, Module.algebraMap_end_apply, Module.algebraMap_end_apply, map_smul, hpow]`.
-/
theorem UpperTheory.Reformulated.B.Qk13.dc_aeval_intertwine.{u_1, u_2} :
    ∀ {Y : Type u_1} {Z : Type u_2} [inst : AddCommGroup Y] [inst_1 : _root_.Module ℂ Y] [inst_2 : AddCommGroup Z]
    [inst_3 : _root_.Module ℂ Z] (ψ : Y →ₗ[ℂ] Z) (A : Module.End ℂ Y) (B : Module.End ℂ Z),
    (∀ (y : Y), (ψ : Y → Z) ((A : Y → Y) y) = (B : Z → Z) ((ψ : Y → Z) y)) →
      ∀ (p : Polynomial ℂ) (y : Y),
        (ψ : Y → Z) (((Polynomial.aeval A : Polynomial ℂ → Module.End ℂ Y) p : Y → Y) y) =
          ((Polynomial.aeval B : Polynomial ℂ → Module.End ℂ Z) p : Z → Z) ((ψ : Y → Z) y) := by
  intro Y Z _ _ _ _ ψ A B h p
  have hpow : ∀ (n : ℕ) (y : Y), ψ ((A ^ n) y) = (B ^ n) (ψ y) := by
    intro n
    induction n with
    | zero => intro y; simp
    | succ n ih =>
      intro y
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, h]
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    intro y
    rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, map_add, hp, hq]
  | monomial n a =>
    intro y
    rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, Module.End.mul_apply,
      Module.End.mul_apply, Module.algebraMap_end_apply, Module.algebraMap_end_apply,
      map_smul, hpow]
