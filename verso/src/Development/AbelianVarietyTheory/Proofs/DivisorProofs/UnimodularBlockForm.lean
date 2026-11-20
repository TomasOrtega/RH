import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTriSelf
open GlobalTheory.TriFrame

namespace GlobalTheory.CornerExtend

def cornerExt {R : Type} [CommRing R] {r : ℕ} (A : Matrix (Fin r) (Fin r) R) :
    Matrix (Fin (r+1)) (Fin (r+1)) R :=
  Matrix.of fun l k =>
    Fin.cases (motive := fun _ => R) (Fin.cases (motive := fun _ => R) 1 (fun _ => 0) k)
      (fun l' => Fin.cases (motive := fun _ => R) 0 (fun k' => A l' k') k) l

/- English proof (translation)
By extensionality, compare the relevant components. Apply the first step, then apply the next step to every resulting obligation. Simplify using the standard rewrite rules.
-/
lemma cornerExt_mul {R : Type} [CommRing R] {r : ℕ} (A B : Matrix (Fin r) (Fin r) R) :
    cornerExt A * cornerExt B = cornerExt (A * B) := by
  ext l k
  refine Fin.cases ?_ (fun l' => ?_) l <;> refine Fin.cases ?_ (fun k' => ?_) k <;>
    simp [cornerExt, Matrix.mul_apply, Fin.sum_univ_succ]

/- English proof (translation)
By extensionality, compare the relevant components. Apply the first step, then apply the next step to every resulting obligation. Simplify using the standard rewrite rules.
-/
lemma cornerExt_one {R : Type} [CommRing R] {r : ℕ} :
    cornerExt (1 : Matrix (Fin r) (Fin r) R) = 1 := by
  ext l k
  refine Fin.cases ?_ (fun l' => ?_) l <;> refine Fin.cases ?_ (fun k' => ?_) k <;>
    simp [cornerExt, Matrix.one_apply, Fin.succ_ne_zero, (Fin.succ_ne_zero _).symm]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules.
-/
theorem exists_gl_corner_extend :
    ∀ {R : Type} [CommRing R] {r : ℕ} (P' : GL (Fin r) R), ∃ P : GL (Fin (r+1)) R, (P : Matrix (Fin (r+1)) (Fin (r+1)) R) 0 0 = 1 ∧ (∀ k : Fin r, (P : Matrix (Fin (r+1)) (Fin (r+1)) R) 0 k.succ = 0) ∧ (∀ l : Fin r, (P : Matrix (Fin (r+1)) (Fin (r+1)) R) l.succ 0 = 0) ∧ ∀ l k : Fin r, (P : Matrix (Fin (r+1)) (Fin (r+1)) R) l.succ k.succ = (P' : Matrix (Fin r) (Fin r) R) l k := by
  intro R _ r P'
  refine ⟨⟨cornerExt P'.val, cornerExt P'.inv, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rw [cornerExt_mul, P'.val_inv, cornerExt_one]
  · rw [cornerExt_mul, P'.inv_val, cornerExt_one]
  · simp [cornerExt]
  · intro k; simp [cornerExt]
  · intro l; simp [cornerExt]
  · intro l k; simp [cornerExt]

end GlobalTheory.CornerExtend
