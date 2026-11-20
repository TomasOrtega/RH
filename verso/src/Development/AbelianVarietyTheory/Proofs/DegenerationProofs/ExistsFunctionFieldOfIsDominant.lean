import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsHomOpenPart
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH

namespace GlobalTheory.ZH
open GlobalTheory.Points

/- English proof (translation)
Set `pt : Sp X.functionField ⟶ X` to `X.fromSpecStalk (genericPoint X)`. Use `⟨X.functionField, inferInstance, pt, fun w => ?_, fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[Subsingleton.elim w (IsLocalRing.closedPoint X.functionField)]`. Conclude with `Scheme.fromSpecStalk_closedPoint`. Take `⟨W, hW, g, rfl⟩` from `X.presheaf.germ_exist (x := genericPoint X) x`.

Take `⟨V, hV, hz, hle⟩` from `exists_isAffineOpen_mem_and_subset hW`. Establish `hle' : V ≤ W` using `hle`. Set `φ : Γ(X, V) ⟶ CommRingCat.of X.functionField` to `X.presheaf.germ V (genericPoint X) hz`. Establish `e : pt = Spec.map φ ≫ hV.fromSpec` using `(hV.fromSpecStalk_eq_fromSpecStalk hz).symm`. Use `⟨V, (X.presheaf.map (homOfLE hle').op).hom g, ⟨_, hz⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[e, valF_eq_valR, valR_eq _ V (le_preimage_specMap_fromSpec hV φ), valMap_specMap_fromSpec]`. Conclude with `X.presheaf.germ_res_apply (homOfLE hle') _ hz g`.
-/
theorem exists_functionField_point (X : Scheme.{0}) [IsIntegral X] :
    ∃ (K : Type) (_ : Field K) (pt : Sp K ⟶ X), (∀ w, pt w = genericPoint X) ∧
      ∀ x : K, ∃ (U : X.Opens) (f : Γ(X, U)), (U : Set X).Nonempty ∧ valF pt U f = x := by
  let pt : Sp X.functionField ⟶ X := X.fromSpecStalk (genericPoint X)
  refine ⟨X.functionField, inferInstance, pt, fun w => ?_, fun x => ?_⟩
  · rw [Subsingleton.elim w (IsLocalRing.closedPoint X.functionField)]
    exact Scheme.fromSpecStalk_closedPoint
  · obtain ⟨W, hW, g, rfl⟩ := X.presheaf.germ_exist (x := genericPoint X) x
    obtain ⟨V, hV, hz, hle⟩ := exists_isAffineOpen_mem_and_subset hW
    have hle' : V ≤ W := hle
    let φ : Γ(X, V) ⟶ CommRingCat.of X.functionField := X.presheaf.germ V (genericPoint X) hz
    have e : pt = Spec.map φ ≫ hV.fromSpec := (hV.fromSpecStalk_eq_fromSpecStalk hz).symm
    refine ⟨V, (X.presheaf.map (homOfLE hle').op).hom g, ⟨_, hz⟩, ?_⟩
    rw [e, valF_eq_valR, valR_eq _ V (le_preimage_specMap_fromSpec hV φ), valMap_specMap_fromSpec]
    exact X.presheaf.germ_res_apply (homOfLE hle') _ hz g

/- English proof (translation)
Take `⟨K, _, pt, hpt, honto⟩` from `exists_functionField_point X`. Establish `hq : q (genericPoint X) = genericPoint M.Z`. Establish `h` using `(genericPoint_spec X).image q.continuous`. Rewrite `h` using `[Set.image_univ, q.denseRange.closure_range]`. Conclude with `h.eq (genericPoint_spec M.Z)`.

Establish `hy : ∀ w, (pt ≫ q) w = genericPoint M.Z` using `fun w => by`. Rewrite using `[Scheme.Hom.comp_apply, hpt, hq]`. Establish `hs : ∀ w, (pt ≫ q) w ⤳ genericPoint M.Z` using `fun w => (hy w) ▸ specializes_rfl`. Establish `hm : ∀ x : Ω, x ∈ M.O (genericPoint M.Z)` using `fun x => by rw [RatModel.O_genericPoint]; trivial`. Set `β : Ω →+* K` to `(RatModel.valHomOf (pt ≫ q) _ hs).comp ((RingHom.id Ω).codRestrict (M.O (genericPoint M.Z)).toSubring hm)`.

Use `letI : Algebra o K := (β.comp (algebraMap o Ω)).toAlgebra`. Use `⟨K, inferInstance, inferInstance, { β with commutes' := fun _ => rfl }, pt, ?_, honto, ?_⟩` and prove the remaining obligations. Conclude with `Set.eq_singleton_iff_unique_mem.2 ⟨⟨_, hpt (IsLocalRing.closedPoint K)⟩, by`. Introduce and unpack `_ ⟨w, rfl⟩`. Conclude with `hpt w⟩`.

Take `⟨U, hU, hz, -⟩` from `exists_isAffineOpen_mem_and_subset (X := M.Z) (x := genericPoint M.Z) (U := ⊤) trivial`. Establish `h1` using `top_le_preimage_of_specializes hs hz`. Establish `h2 : ⊤ ≤ M.pt ⁻¹ᵁ U` using `M.top_le_preimage_pt ⟨_, hz⟩`. Use `ext_of_valR hU h1 (le_preimage_comp _ _ h2 (le_preimage_top _)) fun f => ?_` and prove the remaining obligations. Conclude with `((valR_spMap_comp β M.pt U h2 f).trans (RatModel.val_valF ((top_le_preimage_iff _ _).1 h1) f)).symm`.
-/
theorem RatModel.exists_functionField_of_isDominant (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω]
    (M : RatModel o Ω) (X : Scheme.{0}) [IsIntegral X] (q : X ⟶ M.Z) [IsDominant q] :
    ∃ (Ω' : Type) (_ : Field Ω') (_ : Algebra o Ω') (φ : Ω →ₐ[o] Ω') (pt : Sp Ω' ⟶ X),
      Set.range pt = {genericPoint X} ∧
      (∀ x : Ω', ∃ (U : X.Opens) (f : Γ(X, U)), (U : Set X).Nonempty ∧ valF pt U f = x) ∧
      pt ≫ q = spMap φ.toRingHom ≫ M.pt := by
  obtain ⟨K, _, pt, hpt, honto⟩ := exists_functionField_point X
  have hq : q (genericPoint X) = genericPoint M.Z := by
    have h := (genericPoint_spec X).image q.continuous
    rw [Set.image_univ, q.denseRange.closure_range] at h
    exact h.eq (genericPoint_spec M.Z)
  have hy : ∀ w, (pt ≫ q) w = genericPoint M.Z := fun w => by
    rw [Scheme.Hom.comp_apply, hpt, hq]
  have hs : ∀ w, (pt ≫ q) w ⤳ genericPoint M.Z := fun w => (hy w) ▸ specializes_rfl
  have hm : ∀ x : Ω, x ∈ M.O (genericPoint M.Z) := fun x => by rw [RatModel.O_genericPoint]; trivial
  let β : Ω →+* K := (RatModel.valHomOf (pt ≫ q) _ hs).comp
    ((RingHom.id Ω).codRestrict (M.O (genericPoint M.Z)).toSubring hm)
  letI : Algebra o K := (β.comp (algebraMap o Ω)).toAlgebra
  refine ⟨K, inferInstance, inferInstance, { β with commutes' := fun _ => rfl }, pt, ?_, honto, ?_⟩
  · exact Set.eq_singleton_iff_unique_mem.2 ⟨⟨_, hpt (IsLocalRing.closedPoint K)⟩, by
      rintro _ ⟨w, rfl⟩
      exact hpt w⟩
  · obtain ⟨U, hU, hz, -⟩ := exists_isAffineOpen_mem_and_subset (X := M.Z) (x := genericPoint M.Z) (U := ⊤) trivial
    have h1 := top_le_preimage_of_specializes hs hz
    have h2 : ⊤ ≤ M.pt ⁻¹ᵁ U := M.top_le_preimage_pt ⟨_, hz⟩
    refine ext_of_valR hU h1 (le_preimage_comp _ _ h2 (le_preimage_top _)) fun f => ?_
    exact ((valR_spMap_comp β M.pt U h2 f).trans (RatModel.val_valF ((top_le_preimage_iff _ _).1 h1) f)).symm

end GlobalTheory.ZH
