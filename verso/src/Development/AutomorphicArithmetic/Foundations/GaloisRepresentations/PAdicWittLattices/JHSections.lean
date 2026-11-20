import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.GoodCoverEigenspaces.CubeCechEquivalences.CechCubeBaseChange.BcSumSingle

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR
open PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC

namespace UpperTheory.Gal.G3

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem secMap_eq_appLE {k : Type} [CommRing k] {X : Scheme.{0}} (s : X ⟶ Sp k) (U : X.Opens) :
    secMap s U = (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ s.appLE ⊤ U le_top := rfl

/- English proof (translation)
Establish `po` using `(isIso_pushoutSection_iff h (US := ⊤) (UT := ⊤) (UX := V) (UY := g ⁻¹ᵁ V) le_top le_top (by simp)).mp (isIso_pushoutSection_of_isAffineOpen h _ _ _ (isAffineOpen_top _) (isAffineOpen_top _) hV)`. Use `po.of_iso (Scheme.ΓSpecIso (.of k)) (Iso.refl _) (Scheme.ΓSpecIso (.of k')) (Iso.refl _) ?_ ?_ ?_ ?_` and prove the remaining obligations. Simplify using `[secMap_eq_appLE, Scheme.Hom.appLE]`. Rewrite using `[← Scheme.ΓSpecIso_naturality, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]`. Both sides reduce to the same expression.

Simplify using `[Scheme.Hom.app_eq_appLE]`. Simplify using `[secMap_eq_appLE, Scheme.Hom.appLE]`.
-/
private theorem pushout_secMap {k k' : Type} [CommRing k] [CommRing k'] [Algebra k k']
    {X X' : Scheme.{0}} {s : X ⟶ Sp k} {s' : X' ⟶ Sp k'} {g : X' ⟶ X}
    (h : IsPullback g s' s (spMap (algebraMap k k'))) {V : X.Opens} (hV : IsAffineOpen V) :
    IsPushout (secMap s V) (CommRingCat.ofHom (algebraMap k k')) (g.app V)
      (secMap s' (g ⁻¹ᵁ V)) := by
  have po := (isIso_pushoutSection_iff h (US := ⊤) (UT := ⊤) (UX := V) (UY := g ⁻¹ᵁ V) le_top le_top
    (by simp)).mp (isIso_pushoutSection_of_isAffineOpen h _ _ _ (isAffineOpen_top _)
      (isAffineOpen_top _) hV)
  refine po.of_iso (Scheme.ΓSpecIso (.of k)) (Iso.refl _) (Scheme.ΓSpecIso (.of k')) (Iso.refl _)
    ?_ ?_ ?_ ?_
  · simp [secMap_eq_appLE, Scheme.Hom.appLE]
  · rw [← Scheme.ΓSpecIso_naturality, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  · simp [Scheme.Hom.app_eq_appLE]
  · simp [secMap_eq_appLE, Scheme.Hom.appLE]

/- English proof (translation)
Use `letI : Algebra B B' := α.toAlgebra`. Use `letI : Algebra k B' := ((algebraMap k' B').comp (algebraMap k k')).toAlgebra`. Use `haveI : IsScalarTower k k' B' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl`. Use `haveI : IsScalarTower k B B' := IsScalarTower.of_algebraMap_eq fun r ↦ (congrArg (fun q ↦ q.hom r) H.w).symm`. Establish `P : Algebra.IsPushout k k' B B'` using `CommRingCat.isPushout_iff_isPushout.1 H.flip`.

Establish `key : (bcSum e (semiSl hα) : (J →₀ B) → B') = P.out.equiv ∘ (TensorProduct.equivFinsuppOfBasisLeft e).symm`. Use function extensionality and compare the values at `x`. Proceed by induction on `x using Finsupp.induction_linear with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, Function.comp_apply, hx, hy] at *`.

Consider the case `single j b`. Rewrite using `[bcSum_single, Function.comp_apply, TensorProduct.equivFinsuppOfBasisLeft_symm_apply, Finsupp.sum_single_index (by simp), IsBaseChange.equiv_tmul]`. Both sides reduce to the same expression. Unfold `IsBC`. Rewrite using `[key]`.

Conclude with `P.out.equiv.bijective.comp (TensorProduct.equivFinsuppOfBasisLeft e).symm.bijective`.
-/
private theorem isBC_semiSl_of_pushout {k k' : Type} [CommRing k] [CommRing k'] [Algebra k k'] {J : Type}
    (e : Module.Basis J k k') {B B' : Type} [CommRing B] [CommRing B'] [Algebra k B] [Algebra k' B']
    {α : B →+* B'} (hα : SemiHom (algebraMap k k') α)
    (H : IsPushout (CommRingCat.ofHom (algebraMap k B)) (CommRingCat.ofHom (algebraMap k k'))
      (CommRingCat.ofHom α) (CommRingCat.ofHom (algebraMap k' B'))) : IsBC e (semiSl hα) := by
  classical
  letI : Algebra B B' := α.toAlgebra
  letI : Algebra k B' := ((algebraMap k' B').comp (algebraMap k k')).toAlgebra
  haveI : IsScalarTower k k' B' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI : IsScalarTower k B B' := IsScalarTower.of_algebraMap_eq fun r ↦
    (congrArg (fun q ↦ q.hom r) H.w).symm
  have P : Algebra.IsPushout k k' B B' := CommRingCat.isPushout_iff_isPushout.1 H.flip
  have key : (bcSum e (semiSl hα) : (J →₀ B) → B') =
      P.out.equiv ∘ (TensorProduct.equivFinsuppOfBasisLeft e).symm := by
    funext x
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add x y hx hy => simp only [map_add, Function.comp_apply, hx, hy] at *
    | single j b =>
      rw [bcSum_single, Function.comp_apply, TensorProduct.equivFinsuppOfBasisLeft_symm_apply,
        Finsupp.sum_single_index (by simp), IsBaseChange.equiv_tmul]
      rfl
  unfold IsBC
  rw [key]
  exact P.out.equiv.bijective.comp (TensorProduct.equivFinsuppOfBasisLeft e).symm.bijective

/- English proof (translation)
Introduce `k k' _ _ _ J e X X' s s' g h V hV`. Conclude with `isBC_semiSl_of_pushout e (semiHom_appSecS h.w V) (pushout_secMap h hV)`.
-/
theorem jHSections : P_sections := by
  intro k k' _ _ _ J e X X' s s' g h V hV
  exact isBC_semiSl_of_pushout e (semiHom_appSecS h.w V) (pushout_secMap h hV)

end UpperTheory.Gal.G3

end
