import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraCoefficientsRestrictionBijectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineCohomologyRestrictAffinePointPairsBijStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffinePointPairsCommaAcyclicDegreeLeTwoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictUpwardClosedSubcategoryPull1Bijective
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PDForm.AffPair

section

variable {R : Type} [CommRing R] {I : Ideal R} (κ : DividedPowers I) {X : Scheme.{0}} (t : X ⟶ Sp R)
  {Y : Scheme.{0}} (i : X ⟶ Y)

def smAff : ObjectProperty (IsSm κ t i).FullSubcategory := fun S ↦ IsAffineOpen S.obj.U

/- English proof (translation)
Break down `S'.obj.hU with h' | h'` into its components or cases. Conclude with `h'`. Establish `e : S'.obj.U = S.obj.U` using `le_antisymm f.hom.2 (h' ▸ le_top)`. Express the relevant statement in the definitionally equal form `IsAffineOpen S'.obj.U`. Rewrite using `[e]`.

Conclude with `h`.
-/
theorem smAff_up (S S' : (IsSm κ t i).FullSubcategory) (f : S ⟶ S') (h : smAff κ t i S) :
    smAff κ t i S' := by
  rcases S'.obj.hU with h' | h'
  · exact h'
  · have e : S'.obj.U = S.obj.U := le_antisymm f.hom.2 (h' ▸ le_top)
    change IsAffineOpen S'.obj.U
    rw [e]
    exact h

abbrev coefSm : (IsSm κ t i).FullSubcategory ⥤ CommAlgCat.{0} R := (IsSm κ t i).ι ⋙ Pr.fgt κ t i ⋙ O κ t

def toIter : EE κ t i ⥤ (smAff κ t i).FullSubcategory where
  obj a := ⟨⟨a.obj, ⟨⟨a.obj.U, a.property⟩, a.obj.mem⟩⟩, a.property⟩
  map f := ⟨⟨f.hom⟩⟩

def ofIter : (smAff κ t i).FullSubcategory ⥤ EE κ t i where
  obj a := ⟨a.obj.obj, a.property⟩
  map f := ⟨f.hom.hom⟩

def mapTo : CoefMap (RingHom.id R) ((smAff κ t i).ι ⋙ coefSm κ t i) (pE κ t i ⋙ O κ t) where
  G := toIter κ t i
  α _ := RingHom.id _
  naturality _ _ := rfl
  smul _ _ _ := rfl

def mapOf : CoefMap (RingHom.id R) (pE κ t i ⋙ O κ t) ((smAff κ t i).ι ⋙ coefSm κ t i) where
  G := ofIter κ t i
  α _ := RingHom.id _
  naturality _ _ := rfl
  smul _ _ _ := rfl

/- English proof (translation)
Use `Function.bijective_iff_has_inverse.2 ⟨(mapOf κ t i).pull1, fun c ↦ ?_, fun c ↦ ?_⟩` and prove the remaining obligations. Take `⟨a, rfl⟩` from `H1.mk_surjective _ c`. Both sides reduce to the same expression. Take `⟨a, rfl⟩` from `H1.mk_surjective _ c`. Both sides reduce to the same expression.
-/
theorem mapTo_pull1 : Function.Bijective (mapTo κ t i).pull1 := by
  refine Function.bijective_iff_has_inverse.2 ⟨(mapOf κ t i).pull1, fun c ↦ ?_, fun c ↦ ?_⟩
  · obtain ⟨a, rfl⟩ := H1.mk_surjective _ c; rfl
  · obtain ⟨a, rfl⟩ := H1.mk_surjective _ c; rfl

/- English proof (translation)
Use `Function.bijective_iff_has_inverse.2 ⟨(mapOf κ t i).pull2, fun c ↦ ?_, fun c ↦ ?_⟩` and prove the remaining obligations. Take `⟨a, rfl⟩` from `H2.mk_surjective _ c`. Both sides reduce to the same expression. Take `⟨a, rfl⟩` from `H2.mk_surjective _ c`. Both sides reduce to the same expression.
-/
theorem mapTo_pull2 : Function.Bijective (mapTo κ t i).pull2 := by
  refine Function.bijective_iff_has_inverse.2 ⟨(mapOf κ t i).pull2, fun c ↦ ?_, fun c ↦ ?_⟩
  · obtain ⟨a, rfl⟩ := H2.mk_surjective _ c; rfl
  · obtain ⟨a, rfl⟩ := H2.mk_surjective _ c; rfl

end

end GlobalTheory.PDForm.AffPair

namespace GlobalTheory.PDForm

open AffPair in

/- English proof (translation)
Introduce `R _ I κ X t Y i hY`. Establish `ha` using `GlobalTheory.T.crystallineCohomology_restrict_affinePointPairs_bijective R I κ X t Y i`. Establish `hc` using `GlobalTheory.T.affinePointPairs_comma_acyclic_degree_le_two.1 R I κ X t Y i hY`. Establish `hc2` using `GlobalTheory.T.affinePointPairs_comma_acyclic_degree_le_two.2 R I κ X t Y i hY`. Establish `h1 : Function.Bijective (CoefMap.restrict (coefSm κ t i) (smAff κ t i).ι).pull1` using `Desc.restrict_upwardClosed_subcategory_pull1_bijective R _ (coefSm κ t i) (smAff κ t i) (smAff_up κ t i) (fun T ↦ (hc T).1) (fun T ↦ (hc T).2.1) fun T ↦ (hc T).2.2`.

Establish `h2 : Function.Bijective (CoefMap.restrict (coefSm κ t i) (smAff κ t i).ι).pull2` using `⟨Desc.pull_restrict_small_injective (coefSm κ t i) (smAff κ t i) (smAff_up κ t i) (fun T ↦ (hc T).1) (fun T ↦ (hc T).2.1) fun T ↦ (hc T).2.2, Desc.descent_H2_surjective (coefSm κ t i) (smAff κ t i) (smAff_up κ t i) (fun T ↦ (hc T).1) (fun T ↦ (hc T).2.1) (fun T ↦ (hc T).2.2) hc2⟩`. Use `GlobalTheory.T.algebra_coefficients_restriction_bijective R _ _ (O κ t) (pE κ t i) ?_ ?_` and prove the remaining obligations. Establish `h` using `(mapTo_pull1 κ t i).comp (h1.comp ha.1)`. Establish `e : ⇑(CoefMap.restrict (O κ t) (pE κ t i)).pull1 = (mapTo κ t i).pull1 ∘ (CoefMap.restrict (coefSm κ t i) (smAff κ t i).ι).pull1 ∘ (CoefMap.restrict (O κ t) ((IsSm κ t i).ι ⋙ Pr.fgt κ t i)).pull1`. Use function extensionality and compare the values at `c`.

Take `⟨a, rfl⟩` from `H1.mk_surjective _ c`. Both sides reduce to the same expression. Rewrite using `[e]`. Conclude with `h`. Establish `h` using `(mapTo_pull2 κ t i).comp (h2.comp ha.2)`.

Establish `e : ⇑(CoefMap.restrict (O κ t) (pE κ t i)).pull2 = (mapTo κ t i).pull2 ∘ (CoefMap.restrict (coefSm κ t i) (smAff κ t i).ι).pull2 ∘ (CoefMap.restrict (O κ t) ((IsSm κ t i).ι ⋙ Pr.fgt κ t i)).pull2`. Use function extensionality and compare the values at `c`. Take `⟨a, rfl⟩` from `H2.mk_surjective _ c`. Both sides reduce to the same expression. Rewrite using `[e]`.

Conclude with `h`.
-/
theorem crystallineCohomology_computed_on_affinePairs : ∀ (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I) (X : Scheme.{0})
    (t : X ⟶ Sp R) (Y : Scheme.{0}) (i : X ⟶ Y),
    (∀ U V : Y.Opens, IsAffineOpen U → IsAffineOpen V → IsAffineOpen (U ⊓ V)) →
    ((Cx.single (Coef.ofAlg (O κ t))).resMap (pE κ t i)).PullbackBijectiveDegreesOneTwo := by
  intro R _ I κ X t Y i hY
  have ha := GlobalTheory.T.crystallineCohomology_restrict_affinePointPairs_bijective R I κ X t Y i
  have hc := GlobalTheory.T.affinePointPairs_comma_acyclic_degree_le_two.1 R I κ X t Y i hY
  have hc2 := GlobalTheory.T.affinePointPairs_comma_acyclic_degree_le_two.2 R I κ X t Y i hY
  have h1 : Function.Bijective (CoefMap.restrict (coefSm κ t i) (smAff κ t i).ι).pull1 :=
    Desc.restrict_upwardClosed_subcategory_pull1_bijective R _ (coefSm κ t i) (smAff κ t i) (smAff_up κ t i)
      (fun T ↦ (hc T).1) (fun T ↦ (hc T).2.1) fun T ↦ (hc T).2.2
  have h2 : Function.Bijective (CoefMap.restrict (coefSm κ t i) (smAff κ t i).ι).pull2 :=
    ⟨Desc.pull_restrict_small_injective (coefSm κ t i) (smAff κ t i) (smAff_up κ t i)
      (fun T ↦ (hc T).1) (fun T ↦ (hc T).2.1) fun T ↦ (hc T).2.2,
    Desc.descent_H2_surjective (coefSm κ t i) (smAff κ t i) (smAff_up κ t i)
      (fun T ↦ (hc T).1) (fun T ↦ (hc T).2.1) (fun T ↦ (hc T).2.2) hc2⟩
  refine GlobalTheory.T.algebra_coefficients_restriction_bijective R _ _ (O κ t) (pE κ t i) ?_ ?_
  · have h := (mapTo_pull1 κ t i).comp (h1.comp ha.1)
    have e : ⇑(CoefMap.restrict (O κ t) (pE κ t i)).pull1 = (mapTo κ t i).pull1 ∘
        (CoefMap.restrict (coefSm κ t i) (smAff κ t i).ι).pull1 ∘
        (CoefMap.restrict (O κ t) ((IsSm κ t i).ι ⋙ Pr.fgt κ t i)).pull1 := by
      funext c
      obtain ⟨a, rfl⟩ := H1.mk_surjective _ c; rfl
    rw [e]
    exact h
  · have h := (mapTo_pull2 κ t i).comp (h2.comp ha.2)
    have e : ⇑(CoefMap.restrict (O κ t) (pE κ t i)).pull2 = (mapTo κ t i).pull2 ∘
        (CoefMap.restrict (coefSm κ t i) (smAff κ t i).ι).pull2 ∘
        (CoefMap.restrict (O κ t) ((IsSm κ t i).ι ⋙ Pr.fgt κ t i)).pull2 := by
      funext c
      obtain ⟨a, rfl⟩ := H2.mk_surjective _ c; rfl
    rw [e]
    exact h

end GlobalTheory.PDForm
