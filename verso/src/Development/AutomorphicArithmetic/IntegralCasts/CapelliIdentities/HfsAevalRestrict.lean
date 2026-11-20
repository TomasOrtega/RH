import Mathlib

/- English proof (translation)
Introduce `L W _ _ _ f p h q x`. Establish `hpow : ∀ (n : ℕ) (y : p), ((((LinearMap.restrict f h) ^ n) y : p) : W) = (f ^ n) (y : W)`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro y`.

Both sides reduce to the same expression. Consider the case `succ n ih`. Introduce `y`. Rewrite using `[pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih]`. Both sides reduce to the same expression.

Proceed by induction on `q using Polynomial.induction_on' with`. Consider the case `add a b ha hb`. Rewrite using `[map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, Submodule.coe_add, ha, hb]`. Consider the case `monomial n a`. Rewrite using `[Polynomial.aeval_monomial, Polynomial.aeval_monomial, Module.End.mul_apply, Module.End.mul_apply, Module.algebraMap_end_apply, Module.algebraMap_end_apply, Submodule.coe_smul, hpow]`.
-/
theorem UpperTheory.Reformulated.B.Qh20.hfs_aeval_restrict :
    ∀ {L W : Type} [inst : Field L] [inst_1 : AddCommGroup W]
    [inst_2 : _root_.Module L W] (f : Module.End L W) {p : Submodule L W} (h : ∀ x ∈ p, (f : W → W) x ∈ p)
    (q : Polynomial L) (x : ↥p),
    (↑(((Polynomial.aeval (LinearMap.restrict f h) : Polynomial L → ↥p →ₗ[L] ↥p) q : ↥p → ↥p) x) : W) =
      ((Polynomial.aeval f : Polynomial L → Module.End L W) q : W → W) (↑x : W) := by
  intro L W _ _ _ f p h q x
  have hpow : ∀ (n : ℕ) (y : p), ((((LinearMap.restrict f h) ^ n) y : p) : W) = (f ^ n) (y : W) := by
    intro n
    induction n with
    | zero => intro y; rfl
    | succ n ih =>
      intro y
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih]
      rfl
  induction q using Polynomial.induction_on' with
  | add a b ha hb =>
    rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, Submodule.coe_add, ha, hb]
  | monomial n a =>
    rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, Module.End.mul_apply,
      Module.End.mul_apply, Module.algebraMap_end_apply, Module.algebraMap_end_apply,
      Submodule.coe_smul, hpow]
