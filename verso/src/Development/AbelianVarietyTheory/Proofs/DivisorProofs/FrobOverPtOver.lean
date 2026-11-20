import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Definitions.Degenerations.NotFrobGUnitRat
open CategoryTheory GlobalTheory.AV GlobalTheory.AV.AbVar

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry Limits MonObj GlobalTheory.Published.AbVarRed GlobalTheory.SS.FrobModel
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.AV.FrobEx

/- English proof (translation)
Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `absFrob (ptOver K (AlgebraicClosure K)) = Spec.map (CommRingCat.ofHom ((FiniteField.frobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K) : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) : AlgebraicClosure K →+* AlgebraicClosure K))`. Use `haveI : IsAffine (ptOver K (AlgebraicClosure K)).left := inferInstanceAs (IsAffine (Spec _))`. Apply `ext_of_isAffine` to reduce the goal to its premises. Rewrite using `[← cancel_epi (Scheme.ΓSpecIso (.of (AlgebraicClosure K))).inv]`.

Rewrite using `[← Scheme.ΓSpecIso_inv_naturality]`. Use extensionality with `c`. Simplify using `only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom]`. Establish `e : ((FiniteField.frobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K) : AlgebraicClosure K →+* AlgebraicClosure K) c) = c ^ Fintype.card K` using `FiniteField.frobeniusAlgEquivOfAlgebraic_apply K (AlgebraicClosure K) c`. Conclude with `((congrArg (Scheme.ΓSpecIso (CommRingCat.of (AlgebraicClosure K))).inv.hom e).trans (map_pow _ c _)).symm`.
-/
theorem frobOver_ptOver (K : Type) [Field K] [Fintype K] :
    frobOver (ptOver K (AlgebraicClosure K)) =
      specAut (FiniteField.frobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K)) := by
  apply Over.OverMorphism.ext
  change absFrob (ptOver K (AlgebraicClosure K)) = Spec.map (CommRingCat.ofHom
    ((FiniteField.frobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K) : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
      AlgebraicClosure K →+* AlgebraicClosure K))
  haveI : IsAffine (ptOver K (AlgebraicClosure K)).left := inferInstanceAs (IsAffine (Spec _))
  apply ext_of_isAffine
  rw [← cancel_epi (Scheme.ΓSpecIso (.of (AlgebraicClosure K))).inv]
  rw [← Scheme.ΓSpecIso_inv_naturality]
  ext c
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom]
  have e : ((FiniteField.frobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K) :
      AlgebraicClosure K →+* AlgebraicClosure K) c) = c ^ Fintype.card K :=
    FiniteField.frobeniusAlgEquivOfAlgebraic_apply K (AlgebraicClosure K) c
  exact ((congrArg (Scheme.ΓSpecIso (CommRingCat.of (AlgebraicClosure K))).inv.hom e).trans (map_pow _ c _)).symm

/- English proof (translation)
Use `letI : IsMonHom (frobOver A.X) := (frobG_frobOver A.X).1`. Introduce `x`. Rewrite using `[mk_hom, ← frobOver_comm, frobOver_ptOver]`. Both sides reduce to the same expression.
-/
theorem isFrob_frobOver (K : Type) [Field K] [Fintype K] (A : AbVar K) :
    letI : IsMonHom (frobOver A.X) := (frobG_frobOver A.X).1
    IsFrob (A := A) (Hom.mk (frobOver A.X)) := by
  letI : IsMonHom (frobOver A.X) := (frobG_frobOver A.X).1
  intro x
  rw [mk_hom, ← frobOver_comm, frobOver_ptOver]
  rfl

end GlobalTheory.AV.FrobEx
