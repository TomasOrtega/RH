import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolyRep
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

namespace GlobalTheory

/- English proof (translation)
Set `p : ℕ → Polynomial ℂ` to `fun k => if hk : k ≤ n then (-(B.submatrix (Fin.castLE hk) (Fin.castLE hk))).charpoly else 1`. Establish `key : ∀ (k : ℕ) (hk : k ≤ n) (s : ℂ), ((B + s • (1 : Matrix (Fin n) (Fin n) ℂ)).submatrix (Fin.castLE hk) (Fin.castLE hk)).det = (p k).eval s`. Introduce `k hk s`. Simplify using `only [p, dif_pos hk, Matrix.eval_charpoly]`. Use `congr 1`.

Use extensionality with `i j`. Simplify using `only [Matrix.submatrix_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.neg_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply, Fin.castLE_inj, smul_eq_mul, sub_neg_eq_add]`. Apply the tactic sequence `split_ifs <;> ring`. Establish `hp : ∀ k, p k ≠ 0`. Introduce `k`.

Distinguish the cases in `hk : k ≤ n`. Simplify using `only [p, dif_pos hk]`. Conclude with `(Matrix.charpoly_monic _).ne_zero`. Simplify using `[p, dif_neg hk]`. Use `Set.Finite.subset ((Finset.range (n + 1)).finite_toSet.biUnion fun k _ => Polynomial.finite_setOf_isRoot (hp k)) ?_` and prove the remaining obligations.

Introduce `s hs`. Simplify using `only [Set.mem_setOf_eq, not_forall, not_not] at hs`. Take `⟨k, hk, h0⟩` from `hs`. Simplify using `only [Set.mem_iUnion, Finset.coe_range, Set.mem_Iio, Set.mem_setOf_eq]`. Conclude with `⟨k, Nat.lt_succ_of_le hk, by rw [Polynomial.IsRoot, ← key k hk s, h0]⟩`.
-/
theorem shift_minors_vanish_finite {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) :
    Set.Finite {s : ℂ | ¬ ∀ (k : ℕ) (hk : k ≤ n),
      ((B + s • (1 : Matrix (Fin n) (Fin n) ℂ)).submatrix (Fin.castLE hk) (Fin.castLE hk)).det ≠ 0} := by
  classical
  let p : ℕ → Polynomial ℂ := fun k =>
    if hk : k ≤ n then (-(B.submatrix (Fin.castLE hk) (Fin.castLE hk))).charpoly else 1
  have key : ∀ (k : ℕ) (hk : k ≤ n) (s : ℂ),
      ((B + s • (1 : Matrix (Fin n) (Fin n) ℂ)).submatrix (Fin.castLE hk) (Fin.castLE hk)).det
        = (p k).eval s := by
    intro k hk s
    simp only [p, dif_pos hk, Matrix.eval_charpoly]
    congr 1
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply,
      Matrix.neg_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply,
      Fin.castLE_inj, smul_eq_mul, sub_neg_eq_add]
    split_ifs <;> ring
  have hp : ∀ k, p k ≠ 0 := by
    intro k
    by_cases hk : k ≤ n
    · simp only [p, dif_pos hk]; exact (Matrix.charpoly_monic _).ne_zero
    · simp [p, dif_neg hk]
  refine Set.Finite.subset
    ((Finset.range (n + 1)).finite_toSet.biUnion fun k _ =>
      Polynomial.finite_setOf_isRoot (hp k)) ?_
  intro s hs
  simp only [Set.mem_setOf_eq, not_forall, not_not] at hs
  obtain ⟨k, hk, h0⟩ := hs
  simp only [Set.mem_iUnion, Finset.coe_range, Set.mem_Iio, Set.mem_setOf_eq]
  exact ⟨k, Nat.lt_succ_of_le hk, by rw [Polynomial.IsRoot, ← key k hk s, h0]⟩

end GlobalTheory
