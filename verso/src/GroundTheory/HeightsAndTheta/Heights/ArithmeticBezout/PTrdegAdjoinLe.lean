import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsTrdegAdjoinLe
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Algebra Cardinal Set AlgebraicIndependent

noncomputable section

section TrdegRank

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]

/- English proof (translation)
Use `Matroid.ext_indep (by simp) fun I _ => ?_` and prove the remaining obligations. Establish `hinj : InjOn ((↑) : S → Ω) I` using `Subtype.val_injective.injOn`. Rewrite using `[Matroid.comap_indep_iff, matroid_indep_iff, matroid_indep_iff]`. Simplify using `only [hinj, and_true]`. Express the relevant statement in the definitionally equal form `AlgebraicIndependent K (fun i : I => (i : S)) ↔ AlgebraicIndependent K (fun x : (((↑) : S → Ω) '' I) => (x : Ω))`.

Rewrite using `[← algebraicIndependent_image hinj]`. Conclude with `(S.val.algebraicIndependent_iff Subtype.val_injective).symm`.
-/
theorem matroid_subalgebra_eq_comap (S : Subalgebra K Ω) :
    AlgebraicIndependent.matroid K S = (AlgebraicIndependent.matroid K Ω).comap ((↑) : S → Ω) := by
  refine Matroid.ext_indep (by simp) fun I _ => ?_
  have hinj : InjOn ((↑) : S → Ω) I := Subtype.val_injective.injOn
  rw [Matroid.comap_indep_iff, matroid_indep_iff, matroid_indep_iff]
  simp only [hinj, and_true]
  change AlgebraicIndependent K (fun i : I => (i : S)) ↔
    AlgebraicIndependent K (fun x : (((↑) : S → Ω) '' I) => (x : Ω))
  rw [← algebraicIndependent_image hinj]
  exact (S.val.algebraicIndependent_iff Subtype.val_injective).symm

/- English proof (translation)
Rewrite using `[← matroid_cRank_eq, matroid_subalgebra_eq_comap, ← Matroid.cRk_ground, Matroid.comap_ground_eq, Matroid.cRk_comap, matroid_e, preimage_univ, image_univ, Subtype.range_coe]`. Use `le_antisymm ?_ (Matroid.cRk_le_of_subset _ Algebra.subset_adjoin)` and prove the remaining obligations. Use `(Matroid.cRk_le_of_subset _ ?_).trans_eq (Matroid.cRk_closure _ A)` and prove the remaining obligations. Introduce `x hx`. Rewrite using `[matroid_closure_eq]`.

Conclude with `isAlgebraic_algebraMap (⟨x, hx⟩ : Algebra.adjoin K A)`.
-/
theorem trdeg_adjoin_eq_cRk (A : Set Ω) :
    Algebra.trdeg K (Algebra.adjoin K A) = (AlgebraicIndependent.matroid K Ω).cRk A := by
  rw [← matroid_cRank_eq, matroid_subalgebra_eq_comap, ← Matroid.cRk_ground, Matroid.comap_ground_eq,
    Matroid.cRk_comap, matroid_e, preimage_univ, image_univ, Subtype.range_coe]
  refine le_antisymm ?_ (Matroid.cRk_le_of_subset _ Algebra.subset_adjoin)
  refine (Matroid.cRk_le_of_subset _ ?_).trans_eq (Matroid.cRk_closure _ A)
  intro x hx
  rw [matroid_closure_eq]
  exact isAlgebraic_algebraMap (⟨x, hx⟩ : Algebra.adjoin K A)

end TrdegRank

/- English proof (translation)
Introduce `K Ω _ _ _ s ι _ t ι' w hw`. Use `set M := AlgebraicIndependent.matroid K Ω`. Rewrite using `[trdeg_adjoin_eq_cRk, trdeg_adjoin_eq_cRk]`. Establish `hcl : range w ⊆ M.closure (s ∪ range t)`. Introduce and unpack `_ ⟨i, rfl⟩`.

Rewrite using `[matroid_closure_eq]`. Conclude with `hw i`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem TrdegAdjoinLe.proof : TrdegAdjoinLe.Statement := by
  intro K Ω _ _ _ s ι _ t ι' w hw
  set M := AlgebraicIndependent.matroid K Ω
  rw [trdeg_adjoin_eq_cRk, trdeg_adjoin_eq_cRk]
  have hcl : range w ⊆ M.closure (s ∪ range t) := by
    rintro _ ⟨i, rfl⟩
    rw [matroid_closure_eq]
    exact hw i
  calc M.cRk (range w) ≤ M.cRk (M.closure (s ∪ range t)) := M.cRk_le_of_subset hcl
    _ = M.cRk (s ∪ range t) := M.cRk_closure _
    _ ≤ M.cRk (s ∩ range t) + M.cRk (s ∪ range t) := le_add_self
    _ ≤ M.cRk s + M.cRk (range t) := M.cRk_inter_add_cRk_union_le s (range t)
    _ ≤ M.cRk s + #(range t) := by gcongr; exact M.cRk_le_cardinalMk _
    _ ≤ M.cRk s + #ι := by gcongr; exact mk_range_le
    _ = M.cRk s + Fintype.card ι := by rw [mk_fintype]

end

end GroundTheory.Heights₂.Heights
