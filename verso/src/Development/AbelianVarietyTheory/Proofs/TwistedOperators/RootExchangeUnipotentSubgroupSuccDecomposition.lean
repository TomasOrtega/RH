import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentRadicalBasic

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx

namespace GlobalTheory.RootEx.RadicalDecomp
open GlobalTheory.RootEx.Radical

variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c p : ℕ}

/- English proof (translation)
Rewrite `hg`, the goal using `[mem_N_iff]`. Introduce `r s hrs`. Apply the tactic sequence `rcases r with a | l <;> rcases s with b | j`. Conclude with `hg _ _ (by simp [lev])`. Conclude with `hg _ _ (by simp only [lev, Sum.elim_inl, Sum.elim_inr] at hrs ⊢; omega)`.

Simplify using `only [lev, Sum.elim_inl, Sum.elim_inr] at hrs`. Distinguish the cases in `hp : l.val + 1 = p`. Rewrite using `[h0 l b hp]`. Simplify using the standard rewrite rules. Conclude with `hg _ _ (by simp only [lev, Sum.elim_inl, Sum.elim_inr]; omega)`.

Conclude with `hg _ _ (by simpa [lev] using hrs)`.
-/
theorem mem_N_of_succ {g : GL (n ⊕ Fin c) k} (hg : g ∈ N k n c (p + 1))
    (h0 : ∀ (l : Fin c) (s : n), l.val + 1 = p → g.val (Sum.inr l) (Sum.inl s) = 0) :
    g ∈ N k n c p := by
  rw [mem_N_iff] at hg ⊢
  intro r s hrs
  rcases r with a | l <;> rcases s with b | j
  · exact hg _ _ (by simp [lev])
  · exact hg _ _ (by simp only [lev, Sum.elim_inl, Sum.elim_inr] at hrs ⊢; omega)
  · simp only [lev, Sum.elim_inl, Sum.elim_inr] at hrs
    by_cases hp : l.val + 1 = p
    · rw [h0 l b hp]
      simp
    · exact hg _ _ (by simp only [lev, Sum.elim_inl, Sum.elim_inr]; omega)
  · exact hg _ _ (by simpa [lev] using hrs)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem inv_rowE_val (u : n → k) : ((rowE c p u)⁻¹).val =
    fromBlocks 1 0 (-(Matrix.of fun (l : Fin c) s => if l.val + 1 = p then u s else 0)) 1 := rfl

/- English proof (translation)
Introduce `k _ n _ _ c p g hg`. Use `set u : n → k := fun s => ∑ l : Fin c, if l.val + 1 = p then g.val (Sum.inr l) (Sum.inl s) else 0 with hu`. Establish `hE : rowE c p u ∈ N k n c (p + 1)` using `rowE_mem u (Nat.lt_succ_self p)`. Establish `h1 : g * (rowE c p u)⁻¹ ∈ N k n c (p + 1)` using `Subgroup.mul_mem _ hg (Subgroup.inv_mem _ hE)`. Use `⟨g * (rowE c p u)⁻¹, ⟨?_, h1⟩, u, by simp⟩` and prove the remaining obligations.

Use `mem_N_of_succ h1 ?_` and prove the remaining obligations. Introduce `l s hl`. Establish `hg'` using `(mem_N_iff g).1 hg`. Establish `key : ∀ l' : Fin c, (l'.val + 1 = p ↔ l' = l)` using `fun l' => ⟨fun h => Fin.ext (by omega), fun h => h ▸ hl⟩`. Establish `hd : g.val (Sum.inr l) (Sum.inr l) = 1`.

Use `hg' (Sum.inr l) (Sum.inr l) le_rfl` as an intermediate fact. Simplify using `using this`. Establish `hus : u s = g.val (Sum.inr l) (Sum.inl s)`. Simplify using `only [hu, key, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Rewrite using `[Units.val_mul, inv_rowE_val, Matrix.mul_apply, Fintype.sum_sum_type]`.

Simplify using `only [fromBlocks_apply₁₁, fromBlocks_apply₂₁, Matrix.one_apply, Matrix.neg_apply, Matrix.of_apply, key, mul_ite, mul_one, mul_zero, mul_neg, Finset.sum_ite_eq', Finset.mem_univ, if_true, hus]`. Simplify using `only [Finset.sum_neg_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true, hd]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem succ_decomp : ∀ (k : Type) [Field k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ), ∀ g ∈ N k n c (p + 1), ∃ g₁ ∈ N k n c p ⊓ N k n c (p + 1), ∃ u : n → k, g = g₁ * rowE c p u := by
  intro k _ n _ _ c p g hg
  set u : n → k := fun s => ∑ l : Fin c, if l.val + 1 = p then g.val (Sum.inr l) (Sum.inl s) else 0
    with hu
  have hE : rowE c p u ∈ N k n c (p + 1) := rowE_mem u (Nat.lt_succ_self p)
  have h1 : g * (rowE c p u)⁻¹ ∈ N k n c (p + 1) := Subgroup.mul_mem _ hg (Subgroup.inv_mem _ hE)
  refine ⟨g * (rowE c p u)⁻¹, ⟨?_, h1⟩, u, by simp⟩
  refine mem_N_of_succ h1 ?_
  intro l s hl
  have hg' := (mem_N_iff g).1 hg
  have key : ∀ l' : Fin c, (l'.val + 1 = p ↔ l' = l) :=
    fun l' => ⟨fun h => Fin.ext (by omega), fun h => h ▸ hl⟩
  have hd : g.val (Sum.inr l) (Sum.inr l) = 1 := by
    have := hg' (Sum.inr l) (Sum.inr l) le_rfl
    simpa using this
  have hus : u s = g.val (Sum.inr l) (Sum.inl s) := by
    simp only [hu, key, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Units.val_mul, inv_rowE_val, Matrix.mul_apply, Fintype.sum_sum_type]
  simp only [fromBlocks_apply₁₁, fromBlocks_apply₂₁, Matrix.one_apply, Matrix.neg_apply,
    Matrix.of_apply, key, mul_ite, mul_one, mul_zero, mul_neg, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, hus]
  simp only [Finset.sum_neg_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true, hd]
  ring

end GlobalTheory.RootEx.RadicalDecomp
