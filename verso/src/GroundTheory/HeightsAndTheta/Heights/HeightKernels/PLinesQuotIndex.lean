import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsLines
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

namespace KLinesQuotIndex

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
theorem genIndex_comap_of_surjective {G G' : Type*} [AddCommGroup G] [AddCommGroup G']
    (f : G →+ G') (hf : Function.Surjective f) (H H' : AddSubgroup G') :
    genIndex (H.comap f) (H'.comap f) = genIndex H H' := by
  unfold genIndex
  rw [AddSubgroup.relIndex_comap, AddSubgroup.map_comap_eq_self_of_surjective hf,
    AddSubgroup.relIndex_comap, AddSubgroup.map_comap_eq_self_of_surjective hf]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem coordProj_surjective {K : Type*} [Field K] {n m k : ℕ}
    (B : Module.Basis (Fin m ⊕ Fin k) K (Fin n → K)) : Function.Surjective (coordProj B) :=
  (LinearMap.funLeft_surjective_of_injective K K Sum.inr Sum.inr_injective).comp
    B.equivFun.surjective

/- English proof (translation)
By extensionality, compare the relevant components. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities.

Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis. Supply the required witnesses or components. Fix the arbitrary inputs or assume the hypotheses.

Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Extract witnesses or component facts from the available result. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem ker_coordProj {K : Type*} [Field K] {n m k : ℕ}
    (B : Module.Basis (Fin m ⊕ Fin k) K (Fin n → K)) :
    LinearMap.ker (coordProj B) = Submodule.span K (Set.range fun i => B (Sum.inl i)) := by
  ext v
  have hr : (Set.range fun i => B (Sum.inl i)) = B '' Set.range Sum.inl := by
    rw [← Set.range_comp]; rfl
  rw [hr, Module.Basis.mem_span_image, LinearMap.mem_ker]
  constructor
  · intro h x hx
    rcases x with i | j
    · exact ⟨i, rfl⟩
    · exact absurd (congr_fun h j) (by simpa [coordProj] using hx)
  · intro h
    funext j
    have : Sum.inr j ∉ (B.repr v).support := fun hj => by
      obtain ⟨i, hi⟩ := h hj
      exact Sum.inl_ne_inr hi
    simpa [coordProj] using this

end KLinesQuotIndex

open KLinesQuotIndex in
/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem LinesQuotIndex.proof : LinesQuotIndex.Statement := by
  intro K _ n m k B L c
  set π' := (coordProj B).restrictScalars (𝓞 K) with hπ'
  set W := (Submodule.span K (Set.range fun i => B (Sum.inl i))).restrictScalars (𝓞 K) with hW
  have hker : LinearMap.ker π' = W := by
    rw [hπ', LinearMap.ker_restrictScalars, ker_coordProj]
  have hsurj : Function.Surjective π'.toAddMonoidHom := coordProj_surjective B
  have hcomap : ∀ N : Submodule (𝓞 K) (Fin n → K),
      (N ⊔ W).toAddSubgroup = (N.map π').toAddSubgroup.comap π'.toAddMonoidHom := by
    intro N
    rw [← hker, ← Submodule.comap_map_eq]
    rfl
  have hspan : (Submodule.span (𝓞 K) (Set.range c)).map π' =
      Submodule.span (𝓞 K) (Set.range (coordProj B ∘ c)) := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  rw [hcomap, hcomap, genIndex_comap_of_surjective _ hsurj, hspan]

end GroundTheory.Heights₂.Heights
