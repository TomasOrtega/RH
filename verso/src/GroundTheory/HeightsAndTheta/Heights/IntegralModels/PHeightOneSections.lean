import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsGenericGerm
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsHeightOneSections
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PHeightOneIntersection
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PHeightOneSectionsLocal
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PVectorBundleRestrict
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem HeightOneSections.proof (h₁ : GenericGermInjective.Statement) :
    HeightOneSections.Statement := by
  intro X _ _ hN E hE U hU v hv
  have inj := h₁ X E hE

  have loc : ∀ x : U, ∃ (V : X.Opens) (_ : V ≤ U) (_ : (x : X) ∈ V) (σ : Γ(E, V)),
      ∀ hη : genericPoint X ∈ V, E.presheaf.germ V _ hη σ = v := by
    rintro ⟨x, hx⟩
    obtain ⟨W, -, hxW, n, s, hs⟩ := hE x
    obtain ⟨V, hVa, hxV, hVle⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
      (show x ∈ W ⊓ U from ⟨hxW, hx⟩)
    have hη := HeightOneSections.genericPoint_mem hxV
    obtain ⟨σ, hσ⟩ := HeightOneSections.exists_section_of_isBasisOn HeightOneIntersection.proof
      hN E hVa hη (hs.restrict (hVle.trans inf_le_left)) v
      (fun y hy hy1 => hv y (hVle hy).2 hy1)
    exact ⟨V, hVle.trans inf_le_right, hxV, σ, fun _ => hσ⟩
  choose V hVU hxV σ hσ using loc

  have hcomp : TopCat.Presheaf.IsCompatible E.presheaf V σ := by
    intro i j
    refine BundlesAgree.section_ext E inj fun hη => ?_
    rw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply, hσ, hσ]
  obtain ⟨t, ht, -⟩ := TopCat.Sheaf.existsUnique_gluing' ⟨E.presheaf, E.isSheaf⟩ V U
    (fun x => homOfLE (hVU x)) (fun x hx => Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩) σ hcomp
  refine ⟨t, ?_⟩
  let x : U := ⟨genericPoint X, hU⟩
  have hη := HeightOneSections.genericPoint_mem (hxV x)
  have hx : E.presheaf.map (homOfLE (hVU x)).op t = σ x := ht x
  rw [← hσ x hη, ← hx, TopCat.Presheaf.germ_res_apply]

end GroundTheory.Heights₂.Heights.Model
