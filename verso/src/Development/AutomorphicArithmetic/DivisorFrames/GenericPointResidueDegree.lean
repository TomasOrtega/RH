import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ConsAgree
import Development.AbelianVarietyTheory.Definitions.Divisors.ToIThCapDegOfAddNsmulDivP
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ChiLenPicPushforwardOfIsClosedImmersion
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ConsGeo

/- English proof (translation)
Use `⟨?_, IsLocalRing.residue_surjective⟩` and prove the remaining obligations. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `a ha`. Rewrite `ha` using `[IsLocalRing.residue_eq_zero_iff, (IsLocalRing.isField_iff_maximalIdeal_eq).1 h]`. Simplify using `using ha`.
-/
private theorem residue_bijective_of_isField {R : Type} [CommRing R] [IsLocalRing R] (h : IsField R) :
    Function.Bijective (IsLocalRing.residue R) := by
  refine ⟨?_, IsLocalRing.residue_surjective⟩
  rw [injective_iff_map_eq_zero]
  intro a ha
  rw [IsLocalRing.residue_eq_zero_iff, (IsLocalRing.isField_iff_maximalIdeal_eq).1 h] at ha
  simpa using ha

/- English proof (translation)
Substitute `e` using the available equality. Rewrite `h` using `[← Scheme.SpecMap_stalkMap_fromSpecStalk, cancel_mono]`. Establish `h' : f.stalkMap w = ψ` using `Spec.map_injective h`. Substitute `h'` using the available equality. Use `letI := (f.stalkMap w).hom.toAlgebra`.

Use `letI := (f.residueFieldMap w).hom.toAlgebra`. Use `symm`. Use `Algebra.finrank_eq_of_equiv_equiv (RingEquiv.ofBijective (X.residue (f w)).hom (residue_bijective_of_isField hx)) (RingEquiv.ofBijective (W.residue w).hom (residue_bijective_of_isField hw)) ?_` and prove the remaining obligations. Use extensionality with `a`. Conclude with `congrArg (fun g => CommRingCat.Hom.hom g a) (Scheme.residue_residueFieldMap f w)`.
-/
private theorem residueDegree_eq_of_isField {X W : Scheme.{0}} (f : W ⟶ X) (w : W) (x : X) (e : f w = x)
    (ψ : X.presheaf.stalk x ⟶ W.presheaf.stalk w)
    (h : W.fromSpecStalk w ≫ f = Spec.map ψ ≫ X.fromSpecStalk x)
    (hx : IsField (X.presheaf.stalk x)) (hw : IsField (W.presheaf.stalk w)) :
    f.residueDegree w =
      (letI := ψ.hom.toAlgebra; Module.finrank (X.presheaf.stalk x) (W.presheaf.stalk w)) := by
  subst e
  rw [← Scheme.SpecMap_stalkMap_fromSpecStalk, cancel_mono] at h
  have h' : f.stalkMap w = ψ := Spec.map_injective h
  subst h'
  letI := (f.stalkMap w).hom.toAlgebra
  letI := (f.residueFieldMap w).hom.toAlgebra
  symm
  refine Algebra.finrank_eq_of_equiv_equiv
    (RingEquiv.ofBijective (X.residue (f w)).hom (residue_bijective_of_isField hx))
    (RingEquiv.ofBijective (W.residue w).hom (residue_bijective_of_isField hw)) ?_
  ext a
  exact congrArg (fun g => CommRingCat.Hom.hom g a) (Scheme.residue_residueFieldMap f w)

/- English proof (translation)
Introduce `X W _ _ f ψ h`. Establish `h' : W.fromSpecStalk (genericPoint W) ≫ f = Spec.map (CommRingCat.ofHom ψ) ≫ X.fromSpecStalk (genericPoint X)` using `h`. Establish `e : f (genericPoint W) = genericPoint X`. Establish `h1` using `congrArg (fun g : Spec (W.presheaf.stalk (genericPoint W)) ⟶ X => g (closedPoint (W.presheaf.stalk (genericPoint W)))) h'`. Establish `h0 : f (W.fromSpecStalk (genericPoint W) (closedPoint (W.presheaf.stalk (genericPoint W)))) = X.fromSpecStalk (genericPoint X) (Spec.map (CommRingCat.ofHom ψ) (closedPoint (W.presheaf.stalk (genericPoint W))))` using `h1`.

Use `((congrArg f Scheme.fromSpecStalk_closedPoint).symm.trans h0).trans ?_` and prove the remaining obligations. Establish `h2 : Spec.map (CommRingCat.ofHom ψ) (closedPoint (W.presheaf.stalk (genericPoint W))) = closedPoint (X.presheaf.stalk (genericPoint X))` using `Subsingleton.elim (α := PrimeSpectrum X.functionField) _ _`. Conclude with `(congrArg (X.fromSpecStalk (genericPoint X)) h2).trans Scheme.fromSpecStalk_closedPoint`. Conclude with `⟨e, residueDegree_eq_of_isField f _ _ e (CommRingCat.ofHom ψ) h' (Field.toIsField X.functionField) (Field.toIsField W.functionField)⟩`.
-/
theorem UpperTheory.generic_point_residueDegree :
    ∀ (X W : Scheme.{0}) [IsIntegral X] [IsIntegral W] (f : W ⟶ X) (ψ : X.functionField →+* W.functionField), gpt W ≫ f = spMap ψ ≫ gpt X → f (genericPoint W) = genericPoint X ∧ f.residueDegree (genericPoint W) = embDeg ψ := by
  intro X W _ _ f ψ h
  have h' : W.fromSpecStalk (genericPoint W) ≫ f =
      Spec.map (CommRingCat.ofHom ψ) ≫ X.fromSpecStalk (genericPoint X) := h
  have e : f (genericPoint W) = genericPoint X := by
    have h1 := congrArg (fun g : Spec (W.presheaf.stalk (genericPoint W)) ⟶ X =>
      g (closedPoint (W.presheaf.stalk (genericPoint W)))) h'
    have h0 : f (W.fromSpecStalk (genericPoint W) (closedPoint (W.presheaf.stalk (genericPoint W)))) =
        X.fromSpecStalk (genericPoint X)
          (Spec.map (CommRingCat.ofHom ψ) (closedPoint (W.presheaf.stalk (genericPoint W)))) := h1
    refine ((congrArg f Scheme.fromSpecStalk_closedPoint).symm.trans h0).trans ?_
    have h2 : Spec.map (CommRingCat.ofHom ψ) (closedPoint (W.presheaf.stalk (genericPoint W))) =
        closedPoint (X.presheaf.stalk (genericPoint X)) :=
      Subsingleton.elim (α := PrimeSpectrum X.functionField) _ _
    exact (congrArg (X.fromSpecStalk (genericPoint X)) h2).trans Scheme.fromSpecStalk_closedPoint
  exact ⟨e, residueDegree_eq_of_isField f _ _ e (CommRingCat.ofHom ψ) h'
    (Field.toIsField X.functionField) (Field.toIsField W.functionField)⟩
