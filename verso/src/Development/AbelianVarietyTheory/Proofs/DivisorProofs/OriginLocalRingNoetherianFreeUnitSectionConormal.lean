import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntDerApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalRingDualNumber
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupSchemeStalkEvalAtOriginOriginStalkConstants
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CotangentBidualToTangentFunctionInjective
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CoordsOrigin

noncomputable section

namespace GlobalTheory.CoordsOrigin
variable {R : Type} [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G]

/- English proof (translation)
Use extensionality with `r`. Rewrite using `[GlobalTheory.HodgeTateCompare.strMap_eq]`. Establish `h1 : (StructureSheaf.toStalk R (G.hom (origin G))).hom r = ((Spec (CommRingCat.of R)).presheaf.germ ⊤ (G.hom (origin G)) trivial).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)`. Rewrite using `[Scheme.ΓSpecIso_inv]`. Conclude with `(congrArg (fun q => q.hom r) (StructureSheaf.toOpen_germ (R := R) ⊤ (G.hom (origin G)) trivial)).symm`.

Establish `h2` using `congrArg (fun q => q.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) (Scheme.Hom.germ_stalkMap G.hom ⊤ (origin G) trivial)`. Simplify using `only [CommRingCat.hom_comp, RingHom.comp_apply] at h2`. Express the relevant statement in the definitionally equal form `_ = (G.hom.stalkMap (origin G)).hom ((StructureSheaf.toStalk R (G.hom (origin G))).hom r)`. Rewrite using `[h1, h2]`. Simplify using `[constO, Scheme.Hom.appLE]`.

Use `first`. Consider the case `(erw [CommRingCat.comp_apply, TopCat.Presheaf.germ_res_apply]; done)`. Consider the case `(erw [CommRingCat.comp_apply, TopCat.Presheaf.germ_res_apply]; rfl)`. Consider the case `(rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Category.assoc, TopCat.Presheaf.germ_res]; rfl)`. Consider the case `(simp only [← CommRingCat.comp_apply, Category.assoc, TopCat.Presheaf.germ_res]; rfl)`.
-/
theorem constO_eq_strMap : constO G = (GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateCharacterSystems.strMap G).hom := by
  ext r
  rw [GlobalTheory.HodgeTateCompare.strMap_eq]
  have h1 : (StructureSheaf.toStalk R (G.hom (origin G))).hom r =
      ((Spec (CommRingCat.of R)).presheaf.germ ⊤ (G.hom (origin G)) trivial).hom
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) := by
    rw [Scheme.ΓSpecIso_inv]
    exact (congrArg (fun q => q.hom r) (StructureSheaf.toOpen_germ (R := R) ⊤ (G.hom (origin G)) trivial)).symm
  have h2 := congrArg (fun q => q.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))
    (Scheme.Hom.germ_stalkMap G.hom ⊤ (origin G) trivial)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h2
  change _ = (G.hom.stalkMap (origin G)).hom ((StructureSheaf.toStalk R (G.hom (origin G))).hom r)
  rw [h1, h2]
  simp [constO, Scheme.Hom.appLE]
  first
    | (erw [CommRingCat.comp_apply, TopCat.Presheaf.germ_res_apply]; done)
    | (erw [CommRingCat.comp_apply, TopCat.Presheaf.germ_res_apply]; rfl)
    | (rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Category.assoc, TopCat.Presheaf.germ_res]; rfl)
    | (simp only [← CommRingCat.comp_apply, Category.assoc, TopCat.Presheaf.germ_res]; rfl)

/- English proof (translation)
Substitute `hφ` using the available equality. Take `⟨h1, h2⟩` from `GlobalTheory.HodgeTateCompare.finite_projective_of_smooth (G := G)`. Express the relevant statement in the definitionally equal form `Module.Free R (GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateCharacterSystems.Cotangent G) ∧ Module.Finite R (GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateCharacterSystems.Cotangent G)`. Conclude with `⟨Module.free_of_flat_of_isLocalRing, h1⟩`.
-/
theorem free_finite_cotangent_of_eq [Smooth G.hom] (φ : R →+* G.left.presheaf.stalk (origin G))
    (hφ : φ = (GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateCharacterSystems.strMap G).hom) :
    letI : Algebra R (G.left.presheaf.stalk (origin G)) := φ.toAlgebra
    Module.Free R (RingHom.ker (evO G)).Cotangent ∧ Module.Finite R (RingHom.ker (evO G)).Cotangent := by
  subst hφ
  obtain ⟨h1, h2⟩ := GlobalTheory.HodgeTateCompare.finite_projective_of_smooth (G := G)
  change Module.Free R (GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateCharacterSystems.Cotangent G) ∧ Module.Finite R (GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateCharacterSystems.Cotangent G)
  exact ⟨Module.free_of_flat_of_isLocalRing, h1⟩

end GlobalTheory.CoordsOrigin

/- English proof (translation)
Introduce `R _ _ _ G _ hs`. Use `haveI := hs`. Use `haveI : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom`. Conclude with `⟨inferInstance, GlobalTheory.CoordsOrigin.free_finite_cotangent_of_eq G _ (GlobalTheory.CoordsOrigin.constO_eq_strMap G)⟩`.
-/
theorem GlobalTheory.CoordsOrigin.noetherian_free_cotangent : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (G : Over (Sp R)) [GrpObj G], Smooth G.hom → IsNoetherianRing (G.left.presheaf.stalk (origin G)) ∧
      (letI : Algebra R (G.left.presheaf.stalk (origin G)) := (constO G).toAlgebra;
        Module.Free R (RingHom.ker (evO G)).Cotangent ∧ Module.Finite R (RingHom.ker (evO G)).Cotangent) := by
  intro R _ _ _ G _ hs
  haveI := hs
  haveI : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  exact ⟨inferInstance, GlobalTheory.CoordsOrigin.free_finite_cotangent_of_eq G _ (GlobalTheory.CoordsOrigin.constO_eq_strMap G)⟩
