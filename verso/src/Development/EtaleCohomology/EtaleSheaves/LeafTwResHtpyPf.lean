import Development.EtaleCohomology.EtaleSheaves.LeafTwPairHtpyPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafTwResHtpyPf

/- English proof (translation)
Unfold `res InjectiveResolution.cochainComplex`. Use `infer_instance`.
-/
theorem res_isKInj (R : Type) [CommRing R] (F : Shv R) : (res R F).IsKInjective := by
  unfold res InjectiveResolution.cochainComplex
  infer_instance

/- English proof (translation)
Establish `hY` using `IsKInjective.rightOrthogonal I`. Rewrite `hY` using `[← ObjectProperty.isLocal_trW]`. Establish `hf : (HomotopyCategory.subcategoryAcyclic C).trW ((HomotopyCategory.quotient C _).map f)`. Rewrite using `[← HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic, HomotopyCategory.quotient_map_mem_quasiIso_iff]`. Use the matching hypothesis.

Establish `hb` using `(hY _ hf).1`. Establish `: (HomotopyCategory.quotient C _).map u = (HomotopyCategory.quotient C _).map u'`. Apply `hb` to reduce the goal to its premises. Simplify using `only [← Functor.map_comp, h]`. Conclude with `⟨HomotopyCategory.homotopyOfEq _ _ this⟩`.
-/
theorem htpy_of_qiso {C : Type*} [Category C] [Abelian C] {K L I : CochainComplex C ℤ}
    (f : K ⟶ L) [QuasiIso f] [I.IsKInjective] (u u' : L ⟶ I) (h : f ≫ u = f ≫ u') :
    Nonempty (Homotopy u u') := by
  have hY := IsKInjective.rightOrthogonal I
  rw [← ObjectProperty.isLocal_trW] at hY
  have hf : (HomotopyCategory.subcategoryAcyclic C).trW
      ((HomotopyCategory.quotient C _).map f) := by
    rw [← HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic,
      HomotopyCategory.quotient_map_mem_quasiIso_iff]
    assumption
  have hb := (hY _ hf).1
  have : (HomotopyCategory.quotient C _).map u = (HomotopyCategory.quotient C _).map u' := by
    apply hb
    simp only [← Functor.map_comp, h]
  exact ⟨HomotopyCategory.homotopyOfEq _ _ this⟩

/- English proof (translation)
Apply `((sheafificationAdjunction Scheme.etaleTopology.{0} _).homEquiv P X).injective` to reduce the goal to its premises. Rewrite using `[Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]`. Conclude with `h`.
-/
theorem sh_ext {R : Type} [CommRing R] {P : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)} {X : Shv R}
    (φ ψ : (presheafToSheaf Scheme.etaleTopology.{0} _).obj P ⟶ X)
    (h : toSheafify Scheme.etaleTopology.{0} P ≫ φ.hom = toSheafify Scheme.etaleTopology.{0} P ≫ ψ.hom) : φ = ψ := by
  apply ((sheafificationAdjunction Scheme.etaleTopology.{0} _).homEquiv P X).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  exact h

/- English proof (translation)
Apply `sh_ext` to reduce the goal to its premises. Use extensionality with `U : 2`. Apply `ModuleCat.hom_ext` to reduce the goal to its premises. Use `Submodule.linearMap_qext _ (Finsupp.lhom_ext' fun ζ => LinearMap.ext_ring ?_)` and prove the remaining obligations. Conclude with `h U.unop ζ`.
-/
theorem tw_hom_ext (q : ℕ) (i : ℤ) {X : Shv (ZMod q)} (φ ψ : tw q i ⟶ X)
    (h : ∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)), Sec.map φ (twGen i ζ) = Sec.map ψ (twGen i ζ)) : φ = ψ := by
  apply sh_ext
  ext U : 2
  apply ModuleCat.hom_ext
  refine Submodule.linearMap_qext _ (Finsupp.lhom_ext' fun ζ => LinearMap.ext_ring ?_)
  exact h U.unop ζ

end LateralTheory.E.LeafTwResHtpyPf

open LateralTheory.E.LeafTwResHtpyPf in
/- English proof (translation)
Introduce `q _ k T e hT u u' hu`. Take `⟨_, ε, hε, he⟩` from `hT`. Use `res_isKInj (ZMod q) (tw q k)` as an intermediate fact. Use `htpy_of_qiso ε u u' ?_` and prove the remaining obligations. Apply `HomologicalComplex.from_single_hom_ext` to reduce the goal to its premises.

Rewrite using `[HomologicalComplex.comp_f, HomologicalComplex.comp_f]`. Establish `key : sglι (tw q k) ≫ ε.f 0 ≫ u.f 0 = sglι (tw q k) ≫ ε.f 0 ≫ u'.f 0`. Apply `tw_hom_ext` to reduce the goal to its premises. Introduce `U ζ`. Use `hu U ζ` as an intermediate fact.

Rewrite `this` using `[← he U ζ]`. Conclude with `this`. Establish `h1 : ε.f 0 ≫ u.f 0 = (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (tw q k)).hom ≫ (sglι (tw q k) ≫ ε.f 0 ≫ u.f 0)`. Unfold `sglι`. Conclude with `(Iso.hom_inv_id_assoc _ _).symm`.

Establish `h2 : ε.f 0 ≫ u'.f 0 = (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (tw q k)).hom ≫ (sglι (tw q k) ≫ ε.f 0 ≫ u'.f 0)`. Unfold `sglι`. Conclude with `(Iso.hom_inv_id_assoc _ _).symm`. Conclude with `h1.trans ((congrArg _ key).trans h2.symm)`.
-/
theorem LateralTheory.E.LeafTwPairHtpyPf.LeafTwResHtpy_of : LateralTheory.E.LeafTwPairHtpyPf.LeafTwResHtpy := by
  intro q _ k T e hT u u' hu
  obtain ⟨_, ε, hε, he⟩ := hT
  have := res_isKInj (ZMod q) (tw q k)
  refine htpy_of_qiso ε u u' ?_
  apply HomologicalComplex.from_single_hom_ext
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
  have key : sglι (tw q k) ≫ ε.f 0 ≫ u.f 0 = sglι (tw q k) ≫ ε.f 0 ≫ u'.f 0 := by
    apply tw_hom_ext
    intro U ζ
    have := hu U ζ
    rw [← he U ζ] at this
    exact this
  have h1 : ε.f 0 ≫ u.f 0 = (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (tw q k)).hom ≫
      (sglι (tw q k) ≫ ε.f 0 ≫ u.f 0) := by
    unfold sglι; exact (Iso.hom_inv_id_assoc _ _).symm
  have h2 : ε.f 0 ≫ u'.f 0 = (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (tw q k)).hom ≫
      (sglι (tw q k) ≫ ε.f 0 ≫ u'.f 0) := by
    unfold sglι; exact (Iso.hom_inv_id_assoc _ _).symm
  exact h1.trans ((congrArg _ key).trans h2.symm)
