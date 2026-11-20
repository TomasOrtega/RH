import Mathlib
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StRegSectionParts
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.A (coordDiv)

/- English proof (translation)
Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

A detailed English derivation is pending.
-/
theorem dense_compl_coordDiv {D : ℕ} (S : Finset (Fin D)) : Dense (coordDiv S)ᶜ := by
  have h : (coordDiv S)ᶜ = ⋂ i ∈ (S : Set (Fin D)), (fun z : Fin D → ℂ => z i) ⁻¹' ({0}ᶜ) := by
    ext z
    simp [coordDiv]
  rw [h]
  refine dense_biInter_of_isOpen (fun i _ => ?_) S.countable_toSet (fun i _ => ?_)
  · exact isOpen_compl_singleton.preimage (continuous_apply i)
  · exact (dense_compl_singleton (0 : ℂ)).preimage (isOpenMap_eval i)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Supply the required witnesses or components.

A detailed English derivation is pending.
-/
theorem RegYoDense.proof : RegYoDense.Statement := by
  intro X _ D A R
  rw [dense_iff_inter_open]
  rintro U hU ⟨x, hxU⟩
  have hxj : x ∈ bdDom R (bdIdx R x) := mem_bdDom_bdIdx R x
  set j := bdIdx R x
  have hO : IsOpen ((R.ψ j) '' ((R.ψ j).source ∩ (U ∩ bdDom R j))) :=
    (R.ψ j).isOpen_image_source_inter (hU.inter (isOpen_bdDom R j))
  have hne : ((R.ψ j) '' ((R.ψ j).source ∩ (U ∩ bdDom R j))).Nonempty :=
    ⟨R.ψ j x, x, ⟨hxj.1, hxU, hxj⟩, rfl⟩
  obtain ⟨z, ⟨y, ⟨hys, hyU, hyD⟩, rfl⟩, hz⟩ :=
    (dense_compl_coordDiv (R.S j)).inter_open_nonempty _ hO hne
  have hYo := (R.mem_Yo_iff j (R.ψ j y) hyD.2).2 hz
  rw [(R.ψ j).left_inv hys] at hYo
  exact ⟨y, hyU, hYo⟩

end GroundTheory.Heights₂.Heights.AnalyticLimit
