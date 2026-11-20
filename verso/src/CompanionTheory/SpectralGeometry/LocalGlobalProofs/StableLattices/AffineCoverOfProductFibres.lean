import Mathlib
import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.ObstructionLifting.H1StructureDimLe
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsLocalizedModuleResBasicOpenOfQcqs
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsAffineOpenBiInfOfLe
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechLBHomologyFiniteOfAffineCover
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsSmulHomologyEqZeroOfAcyclicFibre
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SubsingletonOfPoints
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MumfordBundleCechFiniteVanishesOffOrigin
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MumfordBundleCechCohomologyFinrank
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProjectiveOverRingByChartsAbelianVariety
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAmpleLBGenericOfSpecial
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FibAc
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.PointSurjectivity

noncomputable section

namespace GlobalTheory.CompanionTheory.PointSurjectivity

/- English proof (translation)
Introduce `k _ X T Z a b p q H V hV κ _ _ D hD hc G hG`. Set `π` to `pullback.fst q hV.fromSpec`. Set `f` to `pullback.snd q hV.fromSpec`. Establish `H₁ : IsPullback π f q hV.fromSpec` using `IsPullback.of_hasPullback _ _`. Establish `H' : IsPullback f (π ≫ p) (hV.fromSpec ≫ b) a` using `H₁.flip.paste_vert H.flip`.

Establish `hq : IsAffineHom (π ≫ p)` using `MorphismProperty.of_isPullback (P := @IsAffineHom) H' inferInstance`. Establish `hr : π.opensRange = q ⁻¹ᵁ V` using `by ext1`. Rewrite using `[Scheme.Hom.coe_opensRange]`. Use `erw [Scheme.Pullback.range_fst]`. Rewrite using `[hV.range_fromSpec]`.

Both sides reduce to the same expression. Establish `hE (i : κ) : π ⁻¹ᵁ (p ⁻¹ᵁ D i ⊓ q ⁻¹ᵁ V) = (π ≫ p) ⁻¹ᵁ D i`. Rewrite using `[← hr, Scheme.Hom.preimage_inf, Scheme.Hom.preimage_opensRange, inf_top_eq, Scheme.Hom.comp_preimage]`. Establish `hA (i : κ) : IsAffineOpen ((π ≫ p) ⁻¹ᵁ D i)` using `(hD i).preimage _`. Use `⟨fun i => ?_, _, π, f, fun i => π ⁻¹ᵁ (p ⁻¹ᵁ D i ⊓ q ⁻¹ᵁ V), H₁, fun i => (congrArg IsAffineOpen (hE i)).mpr (hA i), ?_, ?_⟩` and prove the remaining obligations.

Establish `h` using `(hA i).image_of_isOpenImmersion π`. Rewrite `h` using `[Scheme.Hom.comp_preimage, Scheme.Hom.image_preimage_eq_opensRange_inf, hr, inf_comm]`. Then use the resulting hypothesis. Simplify using `only [hE]`. Rewrite using `[← Scheme.Hom.preimage_iSup, hc, Scheme.Hom.preimage_top]`. Establish `e : f ≫ hV.fromSpec ≫ b = π ≫ p ≫ a`.

Rewrite using `[← H₁.w_assoc, H.w]`. Rewrite using `[e]`. Conclude with `cechLB_pull_iso_of_isOpenImmersion k _ _ G _ π κ _ hG fun i => hr ▸ inf_le_right`.
-/
theorem over_affineOpen_of_isPullback : ∀ {k : Type} [Field k] {X T Z : Scheme.{0}} (a : X ⟶ Sp k) (b : T ⟶ Sp k) (p : Z ⟶ X) (q : Z ⟶ T)
    (H : IsPullback p q a b) {V : T.Opens} (hV : IsAffineOpen V) {κ : Type} [LinearOrder κ] [Fintype κ]
    (D : κ → X.Opens) (hD : ∀ i, IsAffineOpen (D i)) (hc : ⨆ i, D i = ⊤) (G : LB Z) (hG : G.IsLB), (∀ i, IsAffineOpen (p ⁻¹ᵁ D i ⊓ q ⁻¹ᵁ V)) ∧
    ∃ (Y : Scheme.{0}) (π : Y ⟶ Z) (f : Y ⟶ Spec Γ(T, V)) (E : κ → Y.Opens),
      IsPullback π f q hV.fromSpec ∧ (∀ i, IsAffineOpen (E i)) ∧ ⨆ i, E i = ⊤ ∧
      Nonempty (cechLB (f ≫ hV.fromSpec ≫ b) (G.pull π) E ≅ cechLB (p ≫ a) G fun i => p ⁻¹ᵁ D i ⊓ q ⁻¹ᵁ V) := by
  intro k _ X T Z a b p q H V hV κ _ _ D hD hc G hG
  let π := pullback.fst q hV.fromSpec
  let f := pullback.snd q hV.fromSpec
  have H₁ : IsPullback π f q hV.fromSpec := IsPullback.of_hasPullback _ _
  have H' : IsPullback f (π ≫ p) (hV.fromSpec ≫ b) a := H₁.flip.paste_vert H.flip
  have hq : IsAffineHom (π ≫ p) :=
    MorphismProperty.of_isPullback (P := @IsAffineHom) H' inferInstance
  have hr : π.opensRange = q ⁻¹ᵁ V := by
    ext1
    rw [Scheme.Hom.coe_opensRange]
    erw [Scheme.Pullback.range_fst]
    rw [hV.range_fromSpec]
    rfl
  have hE (i : κ) : π ⁻¹ᵁ (p ⁻¹ᵁ D i ⊓ q ⁻¹ᵁ V) = (π ≫ p) ⁻¹ᵁ D i := by
    rw [← hr, Scheme.Hom.preimage_inf, Scheme.Hom.preimage_opensRange, inf_top_eq,
      Scheme.Hom.comp_preimage]
  have hA (i : κ) : IsAffineOpen ((π ≫ p) ⁻¹ᵁ D i) := (hD i).preimage _
  refine ⟨fun i => ?_, _, π, f, fun i => π ⁻¹ᵁ (p ⁻¹ᵁ D i ⊓ q ⁻¹ᵁ V), H₁,
    fun i => (congrArg IsAffineOpen (hE i)).mpr (hA i), ?_, ?_⟩
  · have h := (hA i).image_of_isOpenImmersion π
    rwa [Scheme.Hom.comp_preimage, Scheme.Hom.image_preimage_eq_opensRange_inf, hr, inf_comm] at h
  · simp only [hE]
    rw [← Scheme.Hom.preimage_iSup, hc, Scheme.Hom.preimage_top]
  · have e : f ≫ hV.fromSpec ≫ b = π ≫ p ≫ a := by
      rw [← H₁.w_assoc, H.w]
    rw [e]
    exact cechLB_pull_iso_of_isOpenImmersion k _ _ G _ π κ _ hG fun i => hr ▸ inf_le_right

end GlobalTheory.CompanionTheory.PointSurjectivity
