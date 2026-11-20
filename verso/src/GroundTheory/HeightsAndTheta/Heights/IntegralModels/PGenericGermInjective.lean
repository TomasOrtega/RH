import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsGenericGerm
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

/- English proof (translation)
Introduce `X _ E hE U hU`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `s hs`. Use `TopCat.Presheaf.section_ext ⟨E.presheaf, E.isSheaf⟩ U s 0 fun x hx => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `E.presheaf.germ U x hx s = E.presheaf.germ U x hx 0`.

Rewrite using `[map_zero]`. Take `⟨Ux, -, hxUx, n, b, hb⟩` from `hE x`. Set `V : X.Opens` to `U ⊓ Ux`. Establish `hxV : x ∈ V` using `⟨hx, hxUx⟩`. Establish `hηV : genericPoint X ∈ V` using `((genericPoint_spec X).mem_open_set_iff V.isOpen).mpr ⟨x, trivial, hxV⟩`.

Set `iVU : V ⟶ U` to `homOfLE inf_le_left`. Set `sV` to `E.presheaf.map iVU.op s`. Take `⟨r, hr⟩` from `(hb V inf_le_right).2 sV`. Establish `hr0 : ∀ i, r i = 0`. Establish `h1 : E.presheaf.germ V (genericPoint X) hηV sV = E.presheaf.germ U (genericPoint X) hU 0`.

Rewrite using `[TopCat.Presheaf.germ_res_apply, hs, map_zero]`. Take `⟨W, hηW, iWV, iWU, e⟩` from `E.presheaf.germ_eq (genericPoint X) hηV hU sV 0 h1`. Establish `hWUx : W ≤ Ux` using `iWV.le.trans inf_le_right`. Establish `key : (fun i => X.presheaf.map iWV.op (r i)) = 0`. Apply `(hb W hWUx).1` to reduce the goal to its premises.

Simplify using `only [Pi.zero_apply, zero_smul, Finset.sum_const_zero]`. Rewrite `e` using `[map_zero]`. Rewrite using `[← e, ← hr, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Scheme.Modules.map_smul, ← ConcreteCategory.comp_apply, ← Functor.map_comp]`.

Both sides reduce to the same expression. Introduce `i`. Apply `germ_injective_of_isIntegral X (U := V) (genericPoint X) hηV` to reduce the goal to its premises. Rewrite using `[map_zero, ← X.presheaf.germ_res_apply iWV (genericPoint X) hηW, congrFun key i, Pi.zero_apply, map_zero]`. Establish `hsV : sV = 0`.

Rewrite using `[← hr]`. Simplify using `[hr0]`. Rewrite using `[← TopCat.Presheaf.germ_res_apply E.presheaf iVU x hxV s]`. Express the relevant statement in the definitionally equal form `E.presheaf.germ V x hxV sV = 0`. Rewrite using `[hsV, map_zero]`.
-/
theorem GenericGermInjective.proof : GenericGermInjective.Statement := by
  intro X _ E hE U hU
  rw [injective_iff_map_eq_zero]
  intro s hs
  refine TopCat.Presheaf.section_ext ⟨E.presheaf, E.isSheaf⟩ U s 0 fun x hx => ?_
  change E.presheaf.germ U x hx s = E.presheaf.germ U x hx 0
  rw [map_zero]
  obtain ⟨Ux, -, hxUx, n, b, hb⟩ := hE x
  let V : X.Opens := U ⊓ Ux
  have hxV : x ∈ V := ⟨hx, hxUx⟩
  have hηV : genericPoint X ∈ V :=
    ((genericPoint_spec X).mem_open_set_iff V.isOpen).mpr ⟨x, trivial, hxV⟩
  let iVU : V ⟶ U := homOfLE inf_le_left
  let sV := E.presheaf.map iVU.op s
  obtain ⟨r, hr⟩ := (hb V inf_le_right).2 sV
  have hr0 : ∀ i, r i = 0 := by
    have h1 : E.presheaf.germ V (genericPoint X) hηV sV = E.presheaf.germ U (genericPoint X) hU 0 := by
      rw [TopCat.Presheaf.germ_res_apply, hs, map_zero]
    obtain ⟨W, hηW, iWV, iWU, e⟩ := E.presheaf.germ_eq (genericPoint X) hηV hU sV 0 h1
    have hWUx : W ≤ Ux := iWV.le.trans inf_le_right
    have key : (fun i => X.presheaf.map iWV.op (r i)) = 0 := by
      apply (hb W hWUx).1
      simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero]
      rw [map_zero] at e
      rw [← e, ← hr, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Scheme.Modules.map_smul, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl
    intro i
    apply germ_injective_of_isIntegral X (U := V) (genericPoint X) hηV
    rw [map_zero, ← X.presheaf.germ_res_apply iWV (genericPoint X) hηW, congrFun key i,
      Pi.zero_apply, map_zero]
  have hsV : sV = 0 := by
    rw [← hr]
    simp [hr0]
  rw [← TopCat.Presheaf.germ_res_apply E.presheaf iVU x hxV s]
  change E.presheaf.germ V x hxV sV = 0
  rw [hsV, map_zero]

end GroundTheory.Heights₂.Heights.Model
