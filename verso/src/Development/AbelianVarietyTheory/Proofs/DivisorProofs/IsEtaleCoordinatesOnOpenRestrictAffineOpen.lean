import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageOfIsPullback
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Definitions.Divisors.SameDiv
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitMkOfFormallyUnramified
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

namespace GlobalTheory.LogPair

/- English proof (translation)
Introduce `R _ X f U W h d t hU hW ht`. Establish `h1 : (resG X h).Etale` using `GlobalTheory.TopForm.etale_resG hU hW h`. Establish `h2 : ((resG X h).comp (MvPolynomial.eval₂Hom (cstOn f U) t)).Etale` using `RingHom.Etale.stableUnderComposition _ _ ht h1`. Establish `h3 : MvPolynomial.eval₂Hom (cstOn f W) (fun a => resG X h (t a)) = (resG X h).comp (MvPolynomial.eval₂Hom (cstOn f U) t)`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises.

Introduce `r`. Establish `hc : cstOn f W = (resG X h).comp (cstOn f U)`. Unfold `cstOn resG`. Rewrite using `[← CommRingCat.hom_comp]`. Establish `e` using `Scheme.Hom.appLE_map f (U := ⊤) (V := U) (by simp) (homOfLE h).op`.

Conclude with `congrArg (fun g => ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ g).hom) e.symm`. Simplify using `only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C, hc]`. Introduce `i`. Simplify using the standard rewrite rules. Unfold `IsEtCoord`.

Rewrite using `[h3]`. Conclude with `h2`.
-/
theorem isEtCoord_res : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Sp R) (U W : X.Opens) (h : W ≤ U) (d : ℕ) (t : Fin d → Γ(X, U)), IsAffineOpen U → IsAffineOpen W → IsEtCoord f U t → IsEtCoord f W (fun a => resG X h (t a)) := by
  intro R _ X f U W h d t hU hW ht
  have h1 : (resG X h).Etale := GlobalTheory.TopForm.etale_resG hU hW h
  have h2 : ((resG X h).comp (MvPolynomial.eval₂Hom (cstOn f U) t)).Etale :=
    RingHom.Etale.stableUnderComposition _ _ ht h1
  have h3 : MvPolynomial.eval₂Hom (cstOn f W) (fun a => resG X h (t a)) =
      (resG X h).comp (MvPolynomial.eval₂Hom (cstOn f U) t) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      have hc : cstOn f W = (resG X h).comp (cstOn f U) := by
        unfold cstOn resG
        rw [← CommRingCat.hom_comp]
        have e := Scheme.Hom.appLE_map f (U := ⊤) (V := U) (by simp) (homOfLE h).op
        exact congrArg (fun g => ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ g).hom) e.symm
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C, hc]
    · intro i
      simp
  unfold IsEtCoord
  rw [h3]
  exact h2

end GlobalTheory.LogPair
