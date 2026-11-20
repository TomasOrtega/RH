import Mathlib

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qp8.Mat :
    Type → ℕ → Type :=
    fun (C : Type) (N : ℕ) ↦ Matrix (Fin N) (Fin N) C

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities.
-/
theorem UpperTheory.Reformulated.B.Qp8.pow_eig :
    ∀ {C : Type} [inst : Field C] {N : ℕ} (y : UpperTheory.Reformulated.B.Qp8.Mat C N) (l : C) (w : Fin N → C),
      Matrix.mulVec y w = l • w → ∀ (m : ℕ), Matrix.mulVec (y ^ m) w = l ^ m • w := by
  intro C _ N y l w h m
  induction m with
  | zero => rw [pow_zero, pow_zero, one_smul, Matrix.one_mulVec]
  | succ k ih =>
    rw [pow_succ, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul, ih, smul_smul, pow_succ']
