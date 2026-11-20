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
Use extensionality with `l k`. Apply the tactic sequence `refine Fin.cases ?_ (fun l' => ?_) l <;> refine Fin.cases ?_ (fun k' => ?_) k <;>`. Simplify using `[cornerExt, Matrix.mul_apply, Fin.sum_univ_succ]`.
-/
lemma cornerExt_mul {R : Type} [CommRing R] {r : ℕ} (A B : Matrix (Fin r) (Fin r) R) :
    cornerExt A * cornerExt B = cornerExt (A * B) := by
  ext l k
  refine Fin.cases ?_ (fun l' => ?_) l <;> refine Fin.cases ?_ (fun k' => ?_) k <;>
    simp [cornerExt, Matrix.mul_apply, Fin.sum_univ_succ]

/- English proof (translation)
Use extensionality with `l k`. Apply the tactic sequence `refine Fin.cases ?_ (fun l' => ?_) l <;> refine Fin.cases ?_ (fun k' => ?_) k <;>`. Simplify using `[cornerExt, Matrix.one_apply, Fin.succ_ne_zero, (Fin.succ_ne_zero _).symm]`.
-/
lemma cornerExt_one {R : Type} [CommRing R] {r : ℕ} :
    cornerExt (1 : Matrix (Fin r) (Fin r) R) = 1 := by
  ext l k
  refine Fin.cases ?_ (fun l' => ?_) l <;> refine Fin.cases ?_ (fun k' => ?_) k <;>
    simp [cornerExt, Matrix.one_apply, Fin.succ_ne_zero, (Fin.succ_ne_zero _).symm]

/- English proof (translation)
Introduce `R _ r P'`. Use `⟨⟨cornerExt P'.val, cornerExt P'.inv, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[cornerExt_mul, P'.val_inv, cornerExt_one]`. Rewrite using `[cornerExt_mul, P'.inv_val, cornerExt_one]`. Simplify using `[cornerExt]`.

Introduce `k`. Simplify using `[cornerExt]`. Introduce `l`. Simplify using `[cornerExt]`. Introduce `l k`.

Simplify using `[cornerExt]`.
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
