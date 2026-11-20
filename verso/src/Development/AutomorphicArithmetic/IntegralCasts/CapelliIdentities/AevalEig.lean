import Mathlib

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qp10.Mat :
    Type → ℕ → Type :=
    fun (C : Type) (N : ℕ) ↦ Matrix (Fin N) (Fin N) C

/- English proof (translation)
Introduce `C _ N y μ v h Q`. Establish `hpow : ∀ n : ℕ, Matrix.mulVec (y ^ n) v = μ ^ n • v`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => rw [pow_zero, pow_zero, Matrix.one_mulVec, one_smul]`.

Consider the case `succ n ih`. Rewrite using `[pow_succ, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul, ih, smul_smul, pow_succ']`. Proceed by induction on `Q using Polynomial.induction_on' with`. Consider the case `add p q hp hq`. Rewrite using `[map_add, Matrix.add_mulVec, hp, hq, Polynomial.eval_add, add_smul]`.

Consider the case `monomial n a`. Rewrite using `[Polynomial.aeval_monomial, Polynomial.eval_monomial, ← Algebra.smul_def, Matrix.smul_mulVec, hpow, smul_smul]`.
-/
theorem UpperTheory.Reformulated.B.Qp10.aeval_eig :
    ∀ {C : Type} [inst : Field C] {N : ℕ} (y : UpperTheory.Reformulated.B.Qp10.Mat C N) (μ : C) (v : Fin N → C),
      Matrix.mulVec y v = μ • v →
        ∀ (Q : Polynomial C),
          Matrix.mulVec ((Polynomial.aeval y : Polynomial C → UpperTheory.Reformulated.B.Qp10.Mat C N) Q) v = Polynomial.eval μ Q • v := by
  intro C _ N y μ v h Q
  have hpow : ∀ n : ℕ, Matrix.mulVec (y ^ n) v = μ ^ n • v := by
    intro n
    induction n with
    | zero => rw [pow_zero, pow_zero, Matrix.one_mulVec, one_smul]
    | succ n ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul, ih, smul_smul, pow_succ']
  induction Q using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, Matrix.add_mulVec, hp, hq, Polynomial.eval_add, add_smul]
  | monomial n a =>
    rw [Polynomial.aeval_monomial, Polynomial.eval_monomial, ← Algebra.smul_def,
      Matrix.smul_mulVec, hpow, smul_smul]
