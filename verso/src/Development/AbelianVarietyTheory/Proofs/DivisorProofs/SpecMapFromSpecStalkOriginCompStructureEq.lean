import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntDerApply
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FormalOrigin

/- English proof (translation)
Establish `e : G.left.fromSpecStalk (origin G) ≫ G.hom = spMap (constO G)`. Establish `e' : CommRingCat.ofHom (constO G) = (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ G.hom.appTop ≫ G.left.presheaf.germ ⊤ (origin G) trivial`. Express the relevant statement in the definitionally equal form `(Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ G.hom.appLE ⊤ ⊤ (fun _ _ => trivial) ≫ G.left.presheaf.germ ⊤ (origin G) trivial = _`. Establish `h : G.hom.appLE ⊤ ⊤ (fun _ _ => trivial) = G.hom.appTop` using `Scheme.Hom.appLE_eq_app _`. Rewrite using `[h]`.

Simplify using `only [spMap]`. Rewrite using `[e', Spec.map_comp, Spec.map_comp, ← Scheme.fromSpecStalk_toSpecΓ_assoc, Category.assoc, Category.assoc, ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]`. Rewrite using `[e]`. Simplify using `only [spMap]`. Rewrite using `[← Spec.map_comp]`.

Both sides reduce to the same expression.
-/
theorem spMap_fromSpecStalk_origin_hom (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] (Ω : Type)
    [CommRing Ω] (ψ : G.left.presheaf.stalk (origin G) →+* Ω) :
    spMap ψ ≫ G.left.fromSpecStalk (origin G) ≫ G.hom = spMap (ψ.comp (constO G)) := by
  have e : G.left.fromSpecStalk (origin G) ≫ G.hom = spMap (constO G) := by
    have e' : CommRingCat.ofHom (constO G) =
        (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ G.hom.appTop ≫ G.left.presheaf.germ ⊤ (origin G) trivial := by
      change (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ G.hom.appLE ⊤ ⊤ (fun _ _ => trivial) ≫
        G.left.presheaf.germ ⊤ (origin G) trivial = _
      have h : G.hom.appLE ⊤ ⊤ (fun _ _ => trivial) = G.hom.appTop := Scheme.Hom.appLE_eq_app _
      rw [h]
    simp only [spMap]
    rw [e', Spec.map_comp, Spec.map_comp, ← Scheme.fromSpecStalk_toSpecΓ_assoc, Category.assoc, Category.assoc,
      ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  rw [e]
  simp only [spMap]
  rw [← Spec.map_comp]
  rfl

end GlobalTheory.FormalOrigin
