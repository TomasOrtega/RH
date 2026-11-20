import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoeffSpecAlgebraMapOfNeg
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LocM.FJ
open GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)

/- English proof (translation)
Take `⟨⟨p, φ⟩, rfl⟩` from `(Scheme.SpecToEquivOfField K X).symm.surjective y`. Take `⟨⟨p', φ'⟩, rfl⟩` from `(Scheme.SpecToEquivOfField K X).symm.surjective y'`. Simplify using `only [Scheme.SpecToEquivOfField_symm_apply] at h ⊢`. Establish `e : ∀ (q : X) (ψ : X.residueField q ⟶ CommRingCat.of K), spMap gam ≫ (Spec.map ψ ≫ X.fromSpecResidueField q) = (Scheme.SpecToEquivOfField C X).symm ⟨q, ψ ≫ CommRingCat.ofHom gam⟩`. Introduce `q ψ`.

Simplify using `only [Scheme.SpecToEquivOfField_symm_apply, spMap, Spec.map_comp, Category.assoc]`. Rewrite `h` using `[e, e]`. Establish `h2` using `(Scheme.SpecToEquivOfField C X).symm.injective h`. Simplify using `only [Sigma.mk.inj_iff] at h2`. Take `⟨rfl, h3⟩` from `h2`.

Establish `h4 : φ = φ'`. Establish `h5 : φ ≫ CommRingCat.ofHom gam = φ' ≫ CommRingCat.ofHom gam` using `eq_of_heq h3`. Use extensionality with `x`. Apply `gam.injective` to reduce the goal to its premises. Use `congrArg (fun f => f.hom x) h5` as an intermediate fact.

Simplify using `using this`. Rewrite using `[h4]`.
-/
theorem GlobalTheory.spec_map_field_cancel {K C : Type} [Field K] [Field C] (gam : K →+* C) {X : Scheme} (y y' : Sp K ⟶ X)
    (h : spMap gam ≫ y = spMap gam ≫ y') : y = y' := by
  obtain ⟨⟨p, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective y
  obtain ⟨⟨p', φ'⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective y'
  simp only [Scheme.SpecToEquivOfField_symm_apply] at h ⊢
  have e : ∀ (q : X) (ψ : X.residueField q ⟶ CommRingCat.of K),
      spMap gam ≫ (Spec.map ψ ≫ X.fromSpecResidueField q) =
        (Scheme.SpecToEquivOfField C X).symm ⟨q, ψ ≫ CommRingCat.ofHom gam⟩ := by
    intro q ψ
    simp only [Scheme.SpecToEquivOfField_symm_apply, spMap, Spec.map_comp, Category.assoc]
  rw [e, e] at h
  have h2 := (Scheme.SpecToEquivOfField C X).symm.injective h
  simp only [Sigma.mk.inj_iff] at h2
  obtain ⟨rfl, h3⟩ := h2
  have h4 : φ = φ' := by
    have h5 : φ ≫ CommRingCat.ofHom gam = φ' ≫ CommRingCat.ofHom gam := eq_of_heq h3
    ext x
    apply gam.injective
    have := congrArg (fun f => f.hom x) h5
    simpa using this
  rw [h4]

/- English proof (translation)
Introduce `gam _ y y' h` and use `GlobalTheory.spec_map_field_cancel gam y y' h`.
-/
theorem GlobalTheory.spec_map_field_epi : ∀ {K C : Type} [Field K] [Field C] (gam : K →+* C) {X : Scheme} (y y' : Sp K ⟶ X), spMap gam ≫ y = spMap gam ≫ y' → y = y' :=
  fun gam _ y y' h => GlobalTheory.spec_map_field_cancel gam y y' h
