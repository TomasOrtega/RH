import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendScalarsUliftHomAdditive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsExtAndGlueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistSectionsLocallyGeneratedStatement

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

section
variable {R S : Type} [CommRing R] [CommRing S]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem secMap_res' {F G : Shv R} (f : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map f x) = Sec.map f (Sec.res g x) :=
  (LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (f.hom.naturality g.op)) x).symm

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem secMap_nsmul' {F G : Shv R} (f : F ⟶ G) {U : Scheme.{0}} (c : ℕ) (x : Sec F U) :
    Sec.map f (c • x) = c • Sec.map f x :=
  map_nsmul (f.hom.app (op U)).hom c x

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem secMap_zero' {F G : Shv R} (f : F ⟶ G) {U : Scheme.{0}} :
    Sec.map f (0 : Sec F U) = 0 :=
  map_zero (f.hom.app (op U)).hom

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

By extensionality, compare the relevant components. A detailed English derivation is pending.
-/
theorem extSh_hom_ext (φ : R →+* S) {F : Shv R} {M : Shv S} (a b : (extSh φ).obj F ⟶ M)
    (h : ∀ (U : Scheme.{0}) (y : Sec F U), Sec.map a (extSh.sec φ F U y) = Sec.map b (extSh.sec φ F U y)) : a = b := by
  apply Sheaf.hom_ext
  refine sheafify_hom_ext (J := Scheme.etaleTopology) (P := F.obj ⋙ ModuleCat.extendScalars.{1, 1, 1} (uliftHom φ))
    a.hom b.hom M.cond ?_
  ext U : 2
  apply ((ModuleCat.extendRestrictScalarsAdj.{1, 1, 1} (uliftHom φ)).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  ext y
  exact h (unop U) y

end

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Simplify by unfolding definitions. Rewrite the conclusion using the stated equalities. Separate the alternatives or extract the components of the hypothesis.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Express the relevant assertion in an equivalent form by its definition. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem extAug_comp_ext : ∀ (Q q : ℕ) [NeZero Q] (hq : q ∣ Q) (i : ℤ) (K : Cx (ZMod q))
    (u u' : extCx (ZMod.castHom hq (ZMod q)) (res _ (tw Q i)) ⟶ K),
    (∀ (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤)),
      Sec.map (u.f 0) ((extπ (ZMod.castHom hq (ZMod q)) _).app U 0 (resGen i ζ)) =
        Sec.map (u'.f 0) ((extπ (ZMod.castHom hq (ZMod q)) _).app U 0 (resGen i ζ))) →
    extAug (ZMod.castHom hq (ZMod q)) (tw Q i) ≫ u = extAug (ZMod.castHom hq (ZMod q)) (tw Q i) ≫ u' := by
  intro Q q _ hq i K u u' h
  have e : ∀ (v : extCx (ZMod.castHom hq (ZMod q)) (res _ (tw Q i)) ⟶ K) (V : Scheme.{0}) (z : Sec (tw Q i) V),
      Sec.map ((extSh (ZMod.castHom hq (ZMod q))).map (resι _ (tw Q i)) ≫ v.f 0)
          (extSh.sec (ZMod.castHom hq (ZMod q)) (tw Q i) V z) =
        Sec.map (v.f 0) ((extπ (ZMod.castHom hq (ZMod q)) _).app V 0 (Sec.map (resι _ (tw Q i)) z)) := by
    intro v V z
    change Sec.map (v.f 0) (Sec.map ((extSh (ZMod.castHom hq (ZMod q))).map (resι _ (tw Q i))) _) = _
    rw [extSh.sec_map]
    rfl
  have key : (extSh (ZMod.castHom hq (ZMod q))).map (resι _ (tw Q i)) ≫ u.f 0 =
      (extSh (ZMod.castHom hq (ZMod q))).map (resι _ (tw Q i)) ≫ u'.f 0 := by
    apply extSh_hom_ext
    intro U y
    apply (GlobalTheory.T.etaleSheafSections_ext_and_glue _ (K.X 0) U).1
    obtain ⟨S, hS, hy⟩ := (GlobalTheory.T.tateTwist_sections_locally_generated Q i).1 U y
    refine ⟨S, hS, fun V g hg => ?_⟩
    dsimp only
    rw [secMap_res', secMap_res', extSh.sec_res, e, e]
    rcases hy V g hg with h0 | ⟨ζ, c, hc⟩
    · rw [h0, secMap_zero', map_zero, secMap_zero', secMap_zero']
    · rw [hc, secMap_nsmul', map_nsmul, secMap_nsmul', secMap_nsmul']
      exact congrArg (c • ·) (h V ζ)
  have hv : ∀ v : extCx (ZMod.castHom hq (ZMod q)) (res _ (tw Q i)) ⟶ K, (extAug (ZMod.castHom hq (ZMod q)) (tw Q i) ≫ v).f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 ((extSh (ZMod.castHom hq (ZMod q))).obj (tw Q i))).hom ≫
        (extSh (ZMod.castHom hq (ZMod q))).map (resι _ (tw Q i)) ≫ v.f 0 := by
    intro v
    have hs := HomologicalComplex.singleMapHomologicalComplex_inv_app_self (extSh (ZMod.castHom hq (ZMod q)))
      (ComplexShape.up ℤ) 0 (tw Q i)
    change (((HomologicalComplex.singleMapHomologicalComplex (extSh (ZMod.castHom hq (ZMod q)))
      (ComplexShape.up ℤ) 0).inv.app (tw Q i)).f 0 ≫ (extSh (ZMod.castHom hq (ZMod q))).map ((resAug (tw Q i)).f 0)) ≫
        v.f 0 = _
    have hs' : ((HomologicalComplex.singleMapHomologicalComplex (extSh (ZMod.castHom hq (ZMod q)))
        (ComplexShape.up ℤ) 0).inv.app (tw Q i)).f 0 ≫ (extSh (ZMod.castHom hq (ZMod q))).map ((resAug (tw Q i)).f 0) =
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 ((extSh (ZMod.castHom hq (ZMod q))).obj (tw Q i))).hom ≫
          (extSh (ZMod.castHom hq (ZMod q))).map (resι _ (tw Q i)) := by
      rw [hs]
      exact (Category.assoc _ _ _).trans (congrArg _ (Functor.map_comp _ _ _).symm)
    exact (congrArg (· ≫ v.f 0) hs').trans (Category.assoc _ _ _)
  apply HomologicalComplex.from_single_hom_ext
  rw [hv, hv, key]

end GlobalTheory.EtC
end
