import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GermSys
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeAt
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackCorrespondence
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SemiabelianHomLieExtendsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeEvalFractionFieldStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModelStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelBaseChangeMapStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenFrameIffEigenspaceBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint

/- English proof (translation)
Establish `e : (dualMap (algebraMap V K)).comp (algebraMap V (DualNumber V)) = (algebraMap K (DualNumber K)).comp (algebraMap V K)`. Apply the tactic sequence `ext r <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]`. Simplify using `only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, e]`.
-/
theorem spMap_dualMap_comp_alg (V K : Type) [CommRing V] [Field K] [Algebra V K] :
    spMap (dualMap (algebraMap V K)) ≫ spMap (algebraMap V (DualNumber V)) =
      spMap (algebraMap K (DualNumber K)) ≫ spMap (algebraMap V K) := by
  have e : (dualMap (algebraMap V K)).comp (algebraMap V (DualNumber V)) =
      (algebraMap K (DualNumber K)).comp (algebraMap V K) := by
    ext r <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, e]

/- English proof (translation)
Introduce `V K _ _ _ _ _ _ X Gx _ _ T _ _ GK _ z φ₀ φ₁ hG hT h₀ h₁ u hu`. Establish `hp` using `isGrpPullback_pullback Gx z`. Establish `hS : IsSemiAbelian ((Over.pullback z).obj Gx)` using `IsSemiAbelian.pullback z Gx hG`. Establish `wφ : φ₁ ≫ Gx.hom = (GK.hom ≫ spMap (algebraMap V K)) ≫ z`. Rewrite using `[h₁.1.w, Category.assoc]`.

Set `φ' : GK.left ⟶ ((Over.pullback z).obj Gx).left` to `hp.1.lift φ₁ (GK.hom ≫ spMap (algebraMap V K)) wφ`. Establish `eφ : φ' ≫ pullback.fst Gx.hom z = φ₁` using `hp.1.lift_fst _ _ _`. Establish `eσ : φ' ≫ ((Over.pullback z).obj Gx).hom = GK.hom ≫ spMap (algebraMap V K)` using `hp.1.lift_snd _ _ _`. Establish `hn : IsGrpPullback GK ((Over.pullback z).obj Gx) (spMap (algebraMap V K)) φ'` using `IsGrpPullback.cancel hp (h₁.congr rfl eφ.symm) eσ`. Take `⟨ET, _, _, ⟨MT⟩⟩` from `GlobalTheory.T.exists_lie_model (Sp V) T V (𝟙 _)`.

Take `⟨EG, _, _, ⟨MG⟩⟩` from `GlobalTheory.T.exists_lie_model X Gx V z`. Take `⟨M₀, hM₀⟩` from `(GlobalTheory.CompanionTheory.Ar.LieMove.main V X z Gx ((Over.pullback z).obj Gx) _ EG hp).1 MG`. Take `⟨f, hf⟩` from `GlobalTheory.T.semiabelian_hom_lie_extends V K T ((Over.pullback z).obj Gx) GK GK φ₀ φ' hT hS h₀ hn (𝟙 GK) ET EG MT M₀`. Take `⟨g, hg⟩` from `GlobalTheory.T.semiabelian_hom_lie_extends V K ((Over.pullback z).obj Gx) T GK GK φ' φ₀ hS hT hn h₀ (𝟙 GK) EG ET M₀ MT`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨a, ha, e⟩`. Take `⟨x, rfl⟩` from `MT.onto a ha`. Establish `l` using `hf x u e`. Use `⟨MG.pt (f x), MG.tan _, ?_⟩` and prove the remaining obligations. Establish `l' : u.left ≫ φ' = spMap (dualMap (algebraMap V K)) ≫ (M₀.pt (f x)).left`.

Simplify `l` using `[LieModel.Lifts]`. Rewrite using `[← eφ, ← Category.assoc, l', Category.assoc, hM₀]`. Introduce and unpack `⟨a, ha, e⟩`. Take `⟨x, rfl⟩` from `MG.onto a ha`. Establish `l : M₀.Lifts (algebraMap V K) φ' x u`.

Use `hp.1.hom_ext ?_ ?_` and prove the remaining obligations. Rewrite using `[Category.assoc, eφ, e, Category.assoc, hM₀]`. Rewrite using `[Category.assoc, eσ, ← Category.assoc, Over.w u, Category.assoc, Over.w (M₀.pt x)] show (spMap (algebraMap K (DualNumber K)) ≫ 𝟙 _) ≫ spMap (algebraMap V K) = spMap (dualMap (algebraMap V K)) ≫ spMap (algebraMap V (DualNumber V)) ≫ 𝟙 _`. Rewrite using `[Category.comp_id, Category.comp_id, spMap_dualMap_comp_alg]`. Establish `l₂` using `hg x u l`.

Use `⟨MT.pt (g x), MT.tan _, ?_⟩` and prove the remaining obligations. Simplify `l₂` using `[LieModel.Lifts]`.
-/
theorem tan_iff_of_generic : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K]
    (X : Scheme.{0}) (Gx : Over X) [GrpObj Gx] [IsCommMonObj Gx] (T : Over (Sp V)) [GrpObj T] [IsCommMonObj T]
    (GK : Over (Sp K)) [GrpObj GK] (z : Sp V ⟶ X) (φ₀ : GK.left ⟶ T.left) (φ₁ : GK.left ⟶ Gx.left),
    IsSemiAbelian Gx → IsSemiAbelian T → IsGrpPullback GK T (spMap (algebraMap V K)) φ₀ →
    IsGrpPullback GK Gx (spMap (algebraMap V K) ≫ z) φ₁ → ∀ u : epsAt (𝟙 (Sp K)) ⟶ GK, IsTanAt GK (𝟙 _) u →
    ((∃ a : epsAt (𝟙 (Sp V)) ⟶ T, IsTanAt T (𝟙 _) a ∧ u.left ≫ φ₀ = spMap (dualMap (algebraMap V K)) ≫ a.left) ↔
      ∃ a : epsAt z ⟶ Gx, IsTanAt Gx z a ∧ u.left ≫ φ₁ = spMap (dualMap (algebraMap V K)) ≫ a.left) := by
  intro V K _ _ _ _ _ _ X Gx _ _ T _ _ GK _ z φ₀ φ₁ hG hT h₀ h₁ u hu
  have hp := isGrpPullback_pullback Gx z
  have hS : IsSemiAbelian ((Over.pullback z).obj Gx) := IsSemiAbelian.pullback z Gx hG
  have wφ : φ₁ ≫ Gx.hom = (GK.hom ≫ spMap (algebraMap V K)) ≫ z := by
    rw [h₁.1.w, Category.assoc]
  let φ' : GK.left ⟶ ((Over.pullback z).obj Gx).left := hp.1.lift φ₁ (GK.hom ≫ spMap (algebraMap V K)) wφ
  have eφ : φ' ≫ pullback.fst Gx.hom z = φ₁ := hp.1.lift_fst _ _ _
  have eσ : φ' ≫ ((Over.pullback z).obj Gx).hom = GK.hom ≫ spMap (algebraMap V K) := hp.1.lift_snd _ _ _
  have hn : IsGrpPullback GK ((Over.pullback z).obj Gx) (spMap (algebraMap V K)) φ' :=
    IsGrpPullback.cancel hp (h₁.congr rfl eφ.symm) eσ
  obtain ⟨ET, _, _, ⟨MT⟩⟩ := GlobalTheory.T.exists_lie_model (Sp V) T V (𝟙 _)
  obtain ⟨EG, _, _, ⟨MG⟩⟩ := GlobalTheory.T.exists_lie_model X Gx V z
  obtain ⟨M₀, hM₀⟩ := (GlobalTheory.CompanionTheory.Ar.LieMove.main V X z Gx ((Over.pullback z).obj Gx) _ EG hp).1 MG
  obtain ⟨f, hf⟩ := GlobalTheory.T.semiabelian_hom_lie_extends V K T ((Over.pullback z).obj Gx) GK GK φ₀ φ' hT hS h₀ hn (𝟙 GK) ET EG MT M₀
  obtain ⟨g, hg⟩ := GlobalTheory.T.semiabelian_hom_lie_extends V K ((Over.pullback z).obj Gx) T GK GK φ' φ₀ hS hT hn h₀ (𝟙 GK) EG ET M₀ MT
  constructor
  · rintro ⟨a, ha, e⟩
    obtain ⟨x, rfl⟩ := MT.onto a ha
    have l := hf x u e
    refine ⟨MG.pt (f x), MG.tan _, ?_⟩
    have l' : u.left ≫ φ' = spMap (dualMap (algebraMap V K)) ≫ (M₀.pt (f x)).left := by
      simpa [LieModel.Lifts] using l
    rw [← eφ, ← Category.assoc, l', Category.assoc, hM₀]
  · rintro ⟨a, ha, e⟩
    obtain ⟨x, rfl⟩ := MG.onto a ha
    have l : M₀.Lifts (algebraMap V K) φ' x u := by
      refine hp.1.hom_ext ?_ ?_
      · rw [Category.assoc, eφ, e, Category.assoc, hM₀]
      · rw [Category.assoc, eσ, ← Category.assoc, Over.w u, Category.assoc, Over.w (M₀.pt x)]
        show (spMap (algebraMap K (DualNumber K)) ≫ 𝟙 _) ≫ spMap (algebraMap V K) =
          spMap (dualMap (algebraMap V K)) ≫ spMap (algebraMap V (DualNumber V)) ≫ 𝟙 _
        rw [Category.comp_id, Category.comp_id, spMap_dualMap_comp_alg]
    have l₂ := hg x u l
    refine ⟨MT.pt (g x), MT.tan _, ?_⟩
    simpa [LieModel.Lifts] using l₂

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint
