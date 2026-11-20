import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx

namespace GlobalTheory.RootEx.BlockLevi

variable {k : Type*} [Field k] {ι : Type*} [Fintype ι] [DecidableEq ι]

def diagPart (f : ι → ℕ) (A : Matrix ι ι k) : Matrix ι ι k :=
  Matrix.of fun r s => if f r = f s then A r s else 0

/- English proof (translation)
Simplify using `only [Matrix.mul_apply, diagPart, Matrix.of_apply]`. Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Use `split_ifs with ht`. Both sides reduce to the same expression. Break down `lt_or_gt_of_ne ht with h1 | h1` into its components or cases.

Rewrite using `[hA (lt_of_lt_of_le h1 h)]`. Simplify using the standard rewrite rules. Rewrite using `[hB h1]`.
-/
theorem mul_diagPart_apply (f : ι → ℕ) {A B : Matrix ι ι k} (hA : A.BlockTriangular f)
    (hB : B.BlockTriangular f) {r s : ι} (h : f s ≤ f r) :
    (A * diagPart f B) r s = (A * B) r s := by
  simp only [Matrix.mul_apply, diagPart, Matrix.of_apply]
  refine Finset.sum_congr rfl fun t _ => ?_
  split_ifs with ht
  · rfl
  · rcases lt_or_gt_of_ne ht with h1 | h1
    · rw [hA (lt_of_lt_of_le h1 h)]; simp
    · rw [hB h1]

/- English proof (translation)
Use extensionality with `r s`. Distinguish the cases in `h : f r = f s`. Rewrite using `[← hAB, ← mul_diagPart_apply f hA hB h.ge]`. Simplify using `only [Matrix.mul_apply, diagPart, Matrix.of_apply]`. Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations.

Distinguish the cases in `ht : f t = f s`. Rewrite using `[if_pos (h.trans ht.symm)]`. Simplify using `[ht]`. Establish `hrs : r ≠ s` using `fun e => h (e ▸ rfl)`. Rewrite using `[Matrix.one_apply_ne hrs]`.

Simplify using `only [Matrix.mul_apply, diagPart, Matrix.of_apply]`. Use `Finset.sum_eq_zero fun t _ => ?_` and prove the remaining obligations. Distinguish the cases in `ht : f t = f s`. Rewrite using `[if_neg (fun e => h (e.trans ht))]`. Simplify using the standard rewrite rules.

Simplify using `[ht]`.
-/
theorem diagPart_mul_diagPart (f : ι → ℕ) {A B : Matrix ι ι k} (hA : A.BlockTriangular f)
    (hB : B.BlockTriangular f) (hAB : A * B = 1) :
    diagPart f A * diagPart f B = 1 := by
  ext r s
  by_cases h : f r = f s
  · rw [← hAB, ← mul_diagPart_apply f hA hB h.ge]
    simp only [Matrix.mul_apply, diagPart, Matrix.of_apply]
    refine Finset.sum_congr rfl fun t _ => ?_
    by_cases ht : f t = f s
    · rw [if_pos (h.trans ht.symm)]
    · simp [ht]
  · have hrs : r ≠ s := fun e => h (e ▸ rfl)
    rw [Matrix.one_apply_ne hrs]
    simp only [Matrix.mul_apply, diagPart, Matrix.of_apply]
    refine Finset.sum_eq_zero fun t _ => ?_
    by_cases ht : f t = f s
    · rw [if_neg (fun e => h (e.trans ht))]; simp
    · simp [ht]

/- English proof (translation)
Use `letI : Invertible b.val := b.invertible`. Rewrite using `[Matrix.coe_units_inv]`. Conclude with `Matrix.blockTriangular_inv_of_blockTriangular hb`.
-/
theorem blockTriangular_inv (f : ι → ℕ) (b : GL ι k) (hb : b.val.BlockTriangular f) :
    (b⁻¹).val.BlockTriangular f := by
  letI : Invertible b.val := b.invertible
  rw [Matrix.coe_units_inv]
  exact Matrix.blockTriangular_inv_of_blockTriangular hb

/- English proof (translation)
Introduce `k _ n _ _ c p b hb`. Establish `hi` using `blockTriangular_inv (lev p) b hb`. Set `m : GL (n ⊕ Fin c) k` to `⟨diagPart (lev p) b.val, diagPart (lev p) (b⁻¹).val, diagPart_mul_diagPart _ hb hi b.mul_inv, diagPart_mul_diagPart _ hi hb b.inv_mul⟩`. Use `⟨b * m⁻¹, Subgroup.subset_closure ?_, m, ?_, ?_, by simp⟩` and prove the remaining obligations. Introduce `r s h`.

Establish `: (b * m⁻¹).val = b.val * diagPart (lev p) (b⁻¹).val` using `rfl`. Rewrite using `[this, mul_diagPart_apply _ hb hi h, b.mul_inv]`. Introduce `r s h`. Simplify using `[m, diagPart, h]`. Introduce `r s h`.

Simplify using `[m, diagPart, h]`.
-/
theorem exists_unip_mul_levi : ∀ (k : Type) [Field k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ) (b : GL (n ⊕ Fin c) k), b.val.BlockTriangular (lev p) → ∃ u ∈ N k n c p, ∃ m : GL (n ⊕ Fin c) k, (∀ r s, lev p r ≠ lev p s → m.val r s = 0) ∧ (∀ r s, lev p r = lev p s → m.val r s = b.val r s) ∧ b = u * m := by
  intro k _ n _ _ c p b hb
  have hi := blockTriangular_inv (lev p) b hb
  let m : GL (n ⊕ Fin c) k := ⟨diagPart (lev p) b.val, diagPart (lev p) (b⁻¹).val,
    diagPart_mul_diagPart _ hb hi b.mul_inv, diagPart_mul_diagPart _ hi hb b.inv_mul⟩
  refine ⟨b * m⁻¹, Subgroup.subset_closure ?_, m, ?_, ?_, by simp⟩
  · intro r s h
    have : (b * m⁻¹).val = b.val * diagPart (lev p) (b⁻¹).val := rfl
    rw [this, mul_diagPart_apply _ hb hi h, b.mul_inv]
  · intro r s h
    simp [m, diagPart, h]
  · intro r s h
    simp [m, diagPart, h]

end GlobalTheory.RootEx.BlockLevi
