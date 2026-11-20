import Development.EtaleCohomology.EtaleSheaves.LeafExtendCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.E.LeafLocalExtendPf

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
lemma specMap_comp_fromSpecStalkOfMem {C : Scheme.{0}} (U : C.Opens) {x y : C} (h : x ⤳ y)
    (hyU : y ∈ U) (hxU : x ∈ U) :
    Spec.map (C.presheaf.stalkSpecializes h) ≫ U.fromSpecStalkOfMem y hyU =
      U.fromSpecStalkOfMem x hxU := by
  rw [← cancel_mono U.ι]
  simp only [Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι,
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk]

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
lemma existence_of_isProper {X S : Scheme.{0}} (p : X ⟶ S) [IsProper p] :
    ValuativeCriterion.Existence p := by
  have : (ValuativeCriterion.Existence ⊓ @QuasiCompact) p := by
    rw [← UniversallyClosed.eq_valuativeCriterion]; infer_instance
  exact this.1

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact.

Introduce a local definition for the expression. Extract witnesses or component facts from the available result. Express the relevant assertion in an equivalent form by its definition. Express the relevant assertion in an equivalent form by its definition. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
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
