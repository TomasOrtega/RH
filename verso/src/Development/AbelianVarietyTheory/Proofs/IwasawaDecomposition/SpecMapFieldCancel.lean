import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoeffSpecAlgebraMapOfNeg
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LocM.FJ
open GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Establish an intermediate fact. By extensionality, compare the relevant components. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. Rewrite the conclusion using the stated equalities.
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
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem GlobalTheory.spec_map_field_epi : ∀ {K C : Type} [Field K] [Field C] (gam : K →+* C) {X : Scheme} (y y' : Sp K ⟶ X), spMap gam ≫ y = spMap gam ≫ y' → y = y' :=
  fun gam _ y y' h => GlobalTheory.spec_map_field_cancel gam y y' h
