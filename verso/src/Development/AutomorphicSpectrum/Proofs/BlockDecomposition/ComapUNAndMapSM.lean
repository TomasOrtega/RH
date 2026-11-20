import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UNInjective
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.LeviInt

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Rewrite using `[CtLevel.blk_val]`. Take `⟨i', rfl⟩` from `(CtLevel.blkEq h).surjective i`. Take `⟨j', rfl⟩` from `(CtLevel.blkEq h).surjective j`. Rewrite using `[reindex_apply, submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]`. Apply the tactic sequence `rcases i' with i' | i' <;> rcases j' with j' | j'`.

Simplify using `using h1 i' j'`. Simplify using `only [fromBlocks_apply₁₂, Matrix.mul_apply]`. Conclude with `Subring.sum_mem _ fun k _ => Subring.mul_mem _ (h1 _ _) (hX _ _)`. Simplify using the standard rewrite rules. Simplify using `using h2 i' j'`.
-/
theorem blk_entries_int {a b n : ℕ} (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w)
    (X : Matrix (Fin a) (Fin b) (w.adicCompletion E))
    (h1 : ∀ i j, (m.1.val i j) ∈ Ov E w) (h2 : ∀ i j, (m.2.val i j) ∈ Ov E w)
    (hX : ∀ i j, X i j ∈ Ov E w) (i j : Fin n) :
    ((blk h w m X : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j ∈ Ov E w := by
  rw [CtLevel.blk_val]
  obtain ⟨i', rfl⟩ := (CtLevel.blkEq h).surjective i
  obtain ⟨j', rfl⟩ := (CtLevel.blkEq h).surjective j
  rw [reindex_apply, submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  rcases i' with i' | i' <;> rcases j' with j' | j'
  · simpa using h1 i' j'
  · simp only [fromBlocks_apply₁₂, Matrix.mul_apply]
    exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (h1 _ _) (hX _ _)
  · simp
  · simpa using h2 i' j'

/- English proof (translation)
Rewrite using `[CtLevel.blk_val, reindex_apply, submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]`. Simplify using the standard rewrite rules.
-/
theorem blk_corner {a b n : ℕ} (h : a + b = n) (w : Pl E)
    (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) (i : Fin a) (j : Fin b) :
    ((blk h w 1 X : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E))
      (CtLevel.blkEq h (Sum.inl i)) (CtLevel.blkEq h (Sum.inr j)) = X i j := by
  rw [CtLevel.blk_val, reindex_apply, submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  simp

/- English proof (translation)
Introduce `E _ _ _ a b n h w`. Establish `hinv : ∀ X : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)), ((GlobalTheory.LeviFubini.uN h w X : GlobalTheory.LeviFubini.parB h w) : GLw n w)⁻¹ = blk h w 1 (Multiplicative.toAdd X⁻¹)` using `fun X => by`. Rewrite using `[← GlobalTheory.LeviFubini.uN_val, map_inv, Subgroup.coe_inv]`. Establish `hint : ∀ k : ℕ, ∀ i j : Fin k, ((1 : GLw k w).val i j) ∈ Ov E w` using `fun k i j => by`. Rewrite using `[Units.val_one, Matrix.one_apply]`.

Use `split_ifs`. Conclude with `Subring.one_mem _`. Conclude with `Subring.zero_mem _`. Use `⟨le_antisymm (fun X hX => ?_) ?_, ?_⟩` and prove the remaining obligations. Rewrite `hX` using `[Subgroup.mem_comap, Subgroup.mem_subgroupOf, GlobalTheory.LeviFubini.uN_val]`.

Use `Subgroup.subset_closure fun i j => ?_` and prove the remaining obligations. Establish `h1` using `(GlobalTheory.AdelicU.mem_GLint_iff.1 hX).1 (CtLevel.blkEq h (Sum.inl i)) (CtLevel.blkEq h (Sum.inr j))`. Rewrite `h1` using `[blk_corner]`. Conclude with `h1`. Use `(Subgroup.closure_le _).2 fun X hX => ?_` and prove the remaining obligations.

Establish `hX' : ∀ i j, Multiplicative.toAdd X i j ∈ Ov E w` using `hX`. Rewrite using `[SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_subgroupOf]`. Use `GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨fun i j => ?_, fun i j => ?_⟩` and prove the remaining obligations. Rewrite using `[GlobalTheory.LeviFubini.uN_val]`. Conclude with `blk_entries_int h w 1 _ (hint a) (hint b) hX' i j`.

Rewrite using `[hinv]`. Use `blk_entries_int h w 1 _ (hint a) (hint b) (fun i j => ?_) i j` and prove the remaining obligations. Simplify using `using Subring.neg_mem _ (hX' i j)`. Introduce and unpack `_ ⟨m, ⟨h1, h2⟩, rfl⟩`. Take `⟨h11, h12⟩` from `GlobalTheory.AdelicU.mem_GLint_iff.1 h1`.

Take `⟨h21, h22⟩` from `GlobalTheory.AdelicU.mem_GLint_iff.1 h2`. Rewrite using `[Subgroup.mem_subgroupOf]`. Use `GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨fun i j => ?_, fun i j => ?_⟩` and prove the remaining obligations. Rewrite using `[GlobalTheory.LeviFubini.sM_val]`. Conclude with `blk_entries_int h w m 0 h11 h21 (fun _ _ => Subring.zero_mem _) i j`.

Rewrite using `[← Subgroup.coe_inv, ← map_inv, GlobalTheory.LeviFubini.sM_val]`. Conclude with `blk_entries_int h w m⁻¹ 0 h12 h22 (fun _ _ => Subring.zero_mem _) i j`.
-/
theorem comap_uN_and_map_sM : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b n : ℕ) (h : a + b = n) (w : Pl E), ((GlobalTheory.LFun.KGL w n).subgroupOf (GlobalTheory.LeviFubini.parB h w)).comap (GlobalTheory.LeviFubini.uN h w) = intMat a b w ∧ ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b)).map (GlobalTheory.LeviFubini.sM h w) ≤ (GlobalTheory.LFun.KGL w n).subgroupOf (GlobalTheory.LeviFubini.parB h w) := by
  intro E _ _ _ a b n h w
  have hinv : ∀ X : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)),
      ((GlobalTheory.LeviFubini.uN h w X : GlobalTheory.LeviFubini.parB h w) : GLw n w)⁻¹ =
        blk h w 1 (Multiplicative.toAdd X⁻¹) := fun X => by
    rw [← GlobalTheory.LeviFubini.uN_val, map_inv, Subgroup.coe_inv]
  have hint : ∀ k : ℕ, ∀ i j : Fin k, ((1 : GLw k w).val i j) ∈ Ov E w := fun k i j => by
    rw [Units.val_one, Matrix.one_apply]
    split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _
  refine ⟨le_antisymm (fun X hX => ?_) ?_, ?_⟩
  · rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, GlobalTheory.LeviFubini.uN_val] at hX
    refine Subgroup.subset_closure fun i j => ?_
    have h1 := (GlobalTheory.AdelicU.mem_GLint_iff.1 hX).1 (CtLevel.blkEq h (Sum.inl i)) (CtLevel.blkEq h (Sum.inr j))
    rw [blk_corner] at h1
    exact h1
  · refine (Subgroup.closure_le _).2 fun X hX => ?_
    have hX' : ∀ i j, Multiplicative.toAdd X i j ∈ Ov E w := hX
    rw [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    refine GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨fun i j => ?_, fun i j => ?_⟩
    · rw [GlobalTheory.LeviFubini.uN_val]
      exact blk_entries_int h w 1 _ (hint a) (hint b) hX' i j
    · rw [hinv]
      refine blk_entries_int h w 1 _ (hint a) (hint b) (fun i j => ?_) i j
      simpa using Subring.neg_mem _ (hX' i j)
  · rintro _ ⟨m, ⟨h1, h2⟩, rfl⟩
    obtain ⟨h11, h12⟩ := GlobalTheory.AdelicU.mem_GLint_iff.1 h1
    obtain ⟨h21, h22⟩ := GlobalTheory.AdelicU.mem_GLint_iff.1 h2
    rw [Subgroup.mem_subgroupOf]
    refine GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨fun i j => ?_, fun i j => ?_⟩
    · rw [GlobalTheory.LeviFubini.sM_val]
      exact blk_entries_int h w m 0 h11 h21 (fun _ _ => Subring.zero_mem _) i j
    · rw [← Subgroup.coe_inv, ← map_inv, GlobalTheory.LeviFubini.sM_val]
      exact blk_entries_int h w m⁻¹ 0 h12 h22 (fun _ _ => Subring.zero_mem _) i j

end GlobalTheory.CompanionTheory.LeviInt
