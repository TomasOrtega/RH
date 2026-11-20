import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndOnId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGrpPullbackMapSemiAbelianNormalDomain
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8 GlobalTheory.Poinc.Sep.Spz Classical

noncomputable section

namespace GlobalTheory.Poinc.Sep.Spz

/- English proof (translation)
Establish `h1 : E.aA ≫ U.gen.inv = U.gen.inv ≫ (Over.pullback (jK V)).map E.aG`. Rewrite using `[Iso.comp_inv_eq, Category.assoc, E.ext, Iso.inv_hom_id_assoc]`. Establish `h1' : E.aA.left ≫ U.gen.inv.left = U.gen.inv.left ≫ ((Over.pullback (jK V)).map E.aG).left`. Use `congrArg CommaMorphism.left h1` as an intermediate fact. Simplify `this` using `only [Over.comp_left]`.

Establish `h2 : ((Over.pullback (jK V)).map E.aG).left ≫ pullback.fst G.hom (jK V) = pullback.fst G.hom (jK V) ≫ E.aG.left` using `pullback.lift_fst _ _ _`. Unfold `genMap`. Rewrite using `[← Category.assoc, h1', Category.assoc, h2, Category.assoc]`.
-/
theorem endU_genMap {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {D : DegData V (maximalIdeal V)}
    {A : PolAV (Sp (FractionRing V))} {G : Over (Sp V)} [GrpObj G] [IsCommMonObj G] (U : Unif (maximalIdeal V) D A G)
    (E : EndU U.toUnifPre) : E.aA.left ≫ genMap U = genMap U ≫ E.aG.left := by
  have h1 : E.aA ≫ U.gen.inv = U.gen.inv ≫ (Over.pullback (jK V)).map E.aG := by
    rw [Iso.comp_inv_eq, Category.assoc, E.ext, Iso.inv_hom_id_assoc]
  have h1' : E.aA.left ≫ U.gen.inv.left = U.gen.inv.left ≫ ((Over.pullback (jK V)).map E.aG).left := by
    have := congrArg CommaMorphism.left h1
    simpa only [Over.comp_left] using this
  have h2 : ((Over.pullback (jK V)).map E.aG).left ≫ pullback.fst G.hom (jK V) = pullback.fst G.hom (jK V) ≫ E.aG.left :=
    pullback.lift_fst _ _ _
  unfold genMap
  rw [← Category.assoc, h1', Category.assoc, h2, Category.assoc]

/- English proof (translation)
Introduce `B H _ _ hH V _ _ _ hV G _ _ hG D A U ξ gm hgm`. Take `⟨⟨hN, -, hIC, -⟩, -⟩` from `hV`. Use `haveI := hN`. Use `haveI := hIC`. Establish `gpA : IsGrpPullback A.A G (jK V) (genMap U)`.

Use `U.gen_hom` as an intermediate fact. Establish `: IsMonHom U.gen.symm.hom` using `by show IsMonHom U.gen.inv; infer_instance`. Conclude with `((isGrpPullback_of_iso U.gen.symm).comp (isGrpPullback_pullback G (jK V))).congr (Category.id_comp _) rfl`. Establish `: IsMonHom (Iso.refl H).hom` using `by show IsMonHom (𝟙 H); infer_instance`. Establish `hHH : IsGrpPullback H H (𝟙 B) (𝟙 H.left)` using `isGrpPullback_of_iso (Iso.refl H)`.

Take `⟨β, hβ, hβg⟩` from `GlobalTheory.SemiAbDesc.exists_grpPullback_map V (𝟙 B) H H (𝟙 _) hH hHH G hG ξ (jK V ≫ ξ) (Category.comp_id _) A.A (genMap U) gm gpA hgm`. Establish `hβg' : genMap U ≫ β = gm` using `by simpa using hβg`. Use `⟨β, hβ, hβg', ?_⟩` and prove the remaining obligations. Introduce `E Fm hE`. Take `⟨_, _⟩` from `GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian G hG`.

Take `⟨_, _⟩` from `GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian H hH`. Take `⟨_, _⟩` from `GlobalTheory.ExtUnique.spec_fractionRing V (FractionRing V)`. Use `haveI : IsSchemeTheoreticallyDominant (genMap U) := .of_isPullback gpA.1.flip`. Establish `key` using `endU_genMap U E`. Use `GlobalTheory.ExtUnique.hom_ext_of_dominant H.hom ?_ (genMap U) ?_` and prove the remaining obligations.

Rewrite using `[Category.assoc, Category.assoc, Over.w Fm, hβ.1.w, ← Category.assoc, Over.w E.aG]`. Rewrite using `[← Category.assoc, ← key, Category.assoc, hβg', hE, ← Category.assoc, hβg']`.
-/
theorem exists_ext : ∀ (B : Scheme.{0}) (H : Over B) [GrpObj H] [IsCommMonObj H], IsSemiAbelian H → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → ∀ (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (U : Unif (maximalIdeal V) D A G) (ξ : Sp V ⟶ B) (gm : A.A.left ⟶ H.left), IsGrpPullback A.A H (jK V ≫ ξ) gm → ∃ β : G.left ⟶ H.left, IsGrpPullback G H ξ β ∧ genMap U ≫ β = gm ∧ ∀ (E : EndU U.toUnifPre) (Fm : H ⟶ H), E.aA.left ≫ gm = gm ≫ Fm.left → E.aG.left ≫ β = β ≫ Fm.left := by
  intro B H _ _ hH V _ _ _ hV G _ _ hG D A U ξ gm hgm
  obtain ⟨⟨hN, -, hIC, -⟩, -⟩ := hV
  haveI := hN
  haveI := hIC
  have gpA : IsGrpPullback A.A G (jK V) (genMap U) := by
    have := U.gen_hom
    have : IsMonHom U.gen.symm.hom := by show IsMonHom U.gen.inv; infer_instance
    exact ((isGrpPullback_of_iso U.gen.symm).comp (isGrpPullback_pullback G (jK V))).congr
      (Category.id_comp _) rfl
  have : IsMonHom (Iso.refl H).hom := by show IsMonHom (𝟙 H); infer_instance
  have hHH : IsGrpPullback H H (𝟙 B) (𝟙 H.left) := isGrpPullback_of_iso (Iso.refl H)
  obtain ⟨β, hβ, hβg⟩ := GlobalTheory.SemiAbDesc.exists_grpPullback_map V (𝟙 B) H H (𝟙 _) hH hHH G hG ξ (jK V ≫ ξ)
    (Category.comp_id _) A.A (genMap U) gm gpA hgm
  have hβg' : genMap U ≫ β = gm := by simpa using hβg
  refine ⟨β, hβ, hβg', ?_⟩
  intro E Fm hE
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian G hG
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian H hH
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.spec_fractionRing V (FractionRing V)
  haveI : IsSchemeTheoreticallyDominant (genMap U) := .of_isPullback gpA.1.flip
  have key := endU_genMap U E
  refine GlobalTheory.ExtUnique.hom_ext_of_dominant H.hom ?_ (genMap U) ?_
  · rw [Category.assoc, Category.assoc, Over.w Fm, hβ.1.w, ← Category.assoc, Over.w E.aG]
  · rw [← Category.assoc, ← key, Category.assoc, hβg', hE, ← Category.assoc, hβg']

end GlobalTheory.Poinc.Sep.Spz
