import Development.EtaleCohomology.EtaleSheaves.LeafExtendCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.E.LeafLocalExtendPf

/- English proof (translation)
Rewrite using `[← cancel_mono U.ι]`. Simplify using `only [Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]`.
-/
lemma specMap_comp_fromSpecStalkOfMem {C : Scheme.{0}} (U : C.Opens) {x y : C} (h : x ⤳ y)
    (hyU : y ∈ U) (hxU : x ∈ U) :
    Spec.map (C.presheaf.stalkSpecializes h) ≫ U.fromSpecStalkOfMem y hyU =
      U.fromSpecStalkOfMem x hxU := by
  rw [← cancel_mono U.ι]
  simp only [Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι,
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk]

/- English proof (translation)
Establish `: (ValuativeCriterion.Existence ⊓ @QuasiCompact) p`. Rewrite using `[← UniversallyClosed.eq_valuativeCriterion]`. Use `infer_instance`. Conclude with `this.1`.
-/
lemma existence_of_isProper {X S : Scheme.{0}} (p : X ⟶ S) [IsProper p] :
    ValuativeCriterion.Existence p := by
  have : (ValuativeCriterion.Existence ⊓ @QuasiCompact) p := by
    rw [← UniversallyClosed.eq_valuativeCriterion]; infer_instance
  exact this.1

/- English proof (translation)
Introduce `C X S _ sC p _ x y hx h hv hfr ψ hψ`. Establish `hdom : IsDomain (C.presheaf.stalk y)` using `inferInstance`. Set `alg : Algebra (C.presheaf.stalk y) (C.presheaf.stalk x)` to `(C.presheaf.stalkSpecializes h).hom.toAlgebra`. Set `fld : Field (C.presheaf.stalk x)` to `IsFractionRing.toField (C.presheaf.stalk y)`. Establish `hsq : CommSq ψ (Spec.map (C.presheaf.stalkSpecializes h)) p (C.fromSpecStalk y ≫ sC)` using `⟨by rw [Scheme.SpecMap_stalkSpecializes_fromSpecStalk_assoc, hψ]⟩`.

Set `sq : ValuativeCommSq p` to `@ValuativeCommSq.mk _ _ p (C.presheaf.stalk y) _ hdom hv (C.presheaf.stalk x) fld alg hfr ψ (C.fromSpecStalk y ≫ sC) hsq`. Take `⟨⟨l, hl1, hl2⟩⟩` from `(existence_of_isProper p sq).exists_lift`. Express the relevant statement in the definitionally equal form `Spec.map (C.presheaf.stalkSpecializes h) ≫ l = ψ at hl1`. Express the relevant statement in the definitionally equal form `l ≫ p = C.fromSpecStalk y ≫ sC at hl2`. Take `⟨U, hyU, f, hf1, hf2⟩` from `spread_out_of_isGermInjective' sC p l hl2`.

Establish `hxU : x ∈ U` using `h.mem_open U.2 hyU`. Use `⟨U, hyU, hxU, f, ?_, hf2⟩` and prove the remaining obligations. Rewrite using `[← hl1, hf1, ← Category.assoc, specMap_comp_fromSpecStalkOfMem U h hyU hxU]`.
-/
theorem LeafLocalExtend_of : LateralTheory.E.LeafExtendCut.LeafLocalExtend := by
  intro C X S _ sC p _ x y hx h hv hfr ψ hψ
  have hdom : IsDomain (C.presheaf.stalk y) := inferInstance
  let alg : Algebra (C.presheaf.stalk y) (C.presheaf.stalk x) :=
    (C.presheaf.stalkSpecializes h).hom.toAlgebra
  let fld : Field (C.presheaf.stalk x) := IsFractionRing.toField (C.presheaf.stalk y)
  have hsq : CommSq ψ (Spec.map (C.presheaf.stalkSpecializes h)) p (C.fromSpecStalk y ≫ sC) :=
    ⟨by rw [Scheme.SpecMap_stalkSpecializes_fromSpecStalk_assoc, hψ]⟩
  let sq : ValuativeCommSq p :=
    @ValuativeCommSq.mk _ _ p (C.presheaf.stalk y) _ hdom hv (C.presheaf.stalk x) fld alg hfr
      ψ (C.fromSpecStalk y ≫ sC) hsq
  obtain ⟨⟨l, hl1, hl2⟩⟩ := (existence_of_isProper p sq).exists_lift
  change Spec.map (C.presheaf.stalkSpecializes h) ≫ l = ψ at hl1
  change l ≫ p = C.fromSpecStalk y ≫ sC at hl2
  obtain ⟨U, hyU, f, hf1, hf2⟩ := spread_out_of_isGermInjective' sC p l hl2
  have hxU : x ∈ U := h.mem_open U.2 hyU
  refine ⟨U, hyU, hxU, f, ?_, hf2⟩
  rw [← hl1, hf1, ← Category.assoc, specMap_comp_fromSpecStalkOfMem U h hyU hxU]

end LateralTheory.E.LeafLocalExtendPf
