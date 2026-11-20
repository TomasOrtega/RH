import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ProfDefs

open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

/- English proof (translation)
Introduce `G _ _ _ _ hG`. Take `⟨s, hs, hden⟩` from `hG`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `H hH haveI : Finite (G ⧸ H) := H.quotient_finite_of_isOpen hH haveI : H.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient set D := Subgroup.closure s with hD haveI : Finite s := hs haveI : Group.FG D := Group.closure_finite_fg s haveI : (H.subgroupOf D).FiniteIndex := inferI …`. Establish `hfg : Group.FG (H.subgroupOf D)` using `inferInstance`.

Take `⟨t, ht, htf⟩` from `Group.fg_iff.mp hfg`. Set `φ : H.subgroupOf D →* H` to `(D.subtype.comp (H.subgroupOf D).subtype).codRestrict H (fun x => x.2)`. Use `⟨φ '' t, htf.image _, ?_⟩` and prove the remaining obligations. Unfold `TopGen`. Rewrite using `[← MonoidHom.map_closure, ht, ← MonoidHom.range_eq_map]`.

Rewrite using `[dense_iff_inter_open]`. Introduce `U hU hUne`. Establish `hVo : IsOpen ((Subtype.val : H → G) '' U)` using `hH.isOpenMap_subtype_val U hU`. Take `⟨x, ⟨y, hyU, rfl⟩, hxD⟩` from `hden.inter_open_nonempty _ hVo (hUne.image _)`. Use `⟨y, hyU, ⟨⟨y.1, hxD⟩, y.2⟩, ?_⟩` and prove the remaining obligations.

Both sides reduce to the same expression. Introduce `Z _ _ f hf hsurj`. Use `⟨f '' s, hs.image _, ?_⟩` and prove the remaining obligations. Unfold `TopGen at hden ⊢`. Rewrite using `[← MonoidHom.map_closure, Subgroup.coe_map]`.

Conclude with `hsurj.denseRange.dense_image hf hden`.
-/
theorem UpperTheory.V.AlgebraTools.TopFG.subgroup_quot :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G], TopFG G →
      (∀ H : Subgroup G, IsOpen (H : Set G) → TopFG H) ∧
      (∀ (Z : Type) [Group Z] [TopologicalSpace Z] (f : G →* Z), Continuous f → Function.Surjective f → TopFG Z) := by
  intro G _ _ _ _ hG
  obtain ⟨s, hs, hden⟩ := hG
  refine ⟨?_, ?_⟩
  · intro H hH
    haveI : Finite (G ⧸ H) := H.quotient_finite_of_isOpen hH
    haveI : H.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
    set D := Subgroup.closure s with hD
    haveI : Finite s := hs
    haveI : Group.FG D := Group.closure_finite_fg s
    haveI : (H.subgroupOf D).FiniteIndex := inferInstance
    have hfg : Group.FG (H.subgroupOf D) := inferInstance
    obtain ⟨t, ht, htf⟩ := Group.fg_iff.mp hfg
    let φ : H.subgroupOf D →* H :=
      (D.subtype.comp (H.subgroupOf D).subtype).codRestrict H (fun x => x.2)
    refine ⟨φ '' t, htf.image _, ?_⟩
    unfold TopGen
    rw [← MonoidHom.map_closure, ht, ← MonoidHom.range_eq_map]
    rw [dense_iff_inter_open]
    intro U hU hUne
    have hVo : IsOpen ((Subtype.val : H → G) '' U) := hH.isOpenMap_subtype_val U hU
    obtain ⟨x, ⟨y, hyU, rfl⟩, hxD⟩ := hden.inter_open_nonempty _ hVo (hUne.image _)
    refine ⟨y, hyU, ⟨⟨y.1, hxD⟩, y.2⟩, ?_⟩
    rfl
  · intro Z _ _ f hf hsurj
    refine ⟨f '' s, hs.image _, ?_⟩
    unfold TopGen at hden ⊢
    rw [← MonoidHom.map_closure, Subgroup.coe_map]
    exact hsurj.denseRange.dense_image hf hden
