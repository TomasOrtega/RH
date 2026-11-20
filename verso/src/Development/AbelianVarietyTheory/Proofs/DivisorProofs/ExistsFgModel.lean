import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleOfGenericFibreNormalLocalDomain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDescendsFiniteType
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRefinementOfIsLimit
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsFiniteTypeSubringAdjoin
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleOfAmpleGeometricFibresAbelianScheme
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KTrivOfKTrivNonemptyOpenNormalCharZero

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AmpleFibreMove

/- English proof (translation)
Introduce `R _ G _ hG L hL`. Take `⟨S₀, B₀, _, φ₀, -, hft₀, hab₀, hpb₀⟩` from `GlobalTheory.AbelianLimit.abelianScheme_descends_to_fg_subring_anyDim R G ∅ hG`. Use `hab₀.comm` as an intermediate fact. Use `hab₀.smooth` as an intermediate fact. Use `hab₀.proper` as an intermediate fact.

Use `hab₀.geomConnected` as an intermediate fact. Take `⟨SP, hSP⟩` from `GlobalTheory.LBLimit.lb_descends_to_fg_subring R S₀ G.left B₀.left G.hom B₀.hom φ₀ L hpb₀.1 hL`. Take `⟨R₁, h, hT, hft⟩` from `GlobalTheory.KeyTf.exists_finiteType_subring_adjoin R S₀ SP hft₀`. Set `t : Sp R₁ ⟶ Sp S₀` to `spMap (Subring.inclusion h)`. Establish `e : spMap R₁.subtype ≫ t = spMap S₀.subtype`.

Rewrite using `[← Spec.map_comp, ← CommRingCat.ofHom_comp]`. Both sides reduce to the same expression. Set `G₁ : Over (Sp R₁)` to `(Over.pullback t).obj B₀`. Establish `hab₁ : IsAbelianScheme G₁` using `{ comm := inferInstance smooth := inferInstanceAs (Smooth (pullback.snd B₀.hom t)) proper := inferInstanceAs (IsProper (pullback.snd B₀.hom t)) geomConnected := inferInstanceAs (GeometricallyConnected (pullback.snd B₀.hom t)) }`. Establish `hpb₁ : IsPullback (pullback.fst B₀.hom t) G₁.hom B₀.hom t` using `IsPullback.of_hasPullback _ _`.

Establish `wφ : φ₀ ≫ B₀.hom = (G.hom ≫ spMap R₁.subtype) ≫ t`. Rewrite using `[Category.assoc, e]`. Conclude with `hpb₀.1.w`. Set `φ : G.left ⟶ G₁.left` to `pullback.lift φ₀ (G.hom ≫ spMap R₁.subtype) wφ`. Establish `hφ₁ : φ ≫ pullback.fst B₀.hom t = φ₀` using `pullback.lift_fst _ _ _`.

Establish `hφ₂ : φ ≫ G₁.hom = G.hom ≫ spMap R₁.subtype` using `pullback.lift_snd _ _ _`. Establish `hφ : IsGrpPullback G G₁ (spMap R₁.subtype) φ` using `(isGrpPullback_pullback B₀ t).cancel (hpb₀.congr e.symm hφ₁.symm) hφ₂`. Take `⟨L₁, hL₁, hiso⟩` from `hSP R₁ h hT G₁.left G₁.hom (pullback.fst B₀.hom t) φ hpb₁ hφ₁ hφ₂`. Conclude with `⟨R₁, G₁, inferInstance, φ, L₁, hft, hab₁, hφ, hL₁, hiso⟩`.
-/
theorem exists_fg_model :
    ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G], IsAbelianScheme G → ∀ L : LB G.left, L.IsLB →
    ∃ (S : Subring R) (G₀ : Over (Sp S)) (_ : GrpObj G₀) (φ : G.left ⟶ G₀.left) (L₀ : LB G₀.left),
      Algebra.FiniteType ℤ S ∧ IsAbelianScheme G₀ ∧ IsGrpPullback G G₀ (spMap S.subtype) φ ∧ L₀.IsLB ∧
        LBIso L (L₀.pull φ) := by
  intro R _ G _ hG L hL
  classical
  obtain ⟨S₀, B₀, _, φ₀, -, hft₀, hab₀, hpb₀⟩ :=
    GlobalTheory.AbelianLimit.abelianScheme_descends_to_fg_subring_anyDim R G ∅ hG
  have := hab₀.comm
  have := hab₀.smooth
  have := hab₀.proper
  have := hab₀.geomConnected
  obtain ⟨SP, hSP⟩ := GlobalTheory.LBLimit.lb_descends_to_fg_subring R S₀ G.left B₀.left
    G.hom B₀.hom φ₀ L hpb₀.1 hL
  obtain ⟨R₁, h, hT, hft⟩ := GlobalTheory.KeyTf.exists_finiteType_subring_adjoin R S₀ SP hft₀
  let t : Sp R₁ ⟶ Sp S₀ := spMap (Subring.inclusion h)
  have e : spMap R₁.subtype ≫ t = spMap S₀.subtype := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  let G₁ : Over (Sp R₁) := (Over.pullback t).obj B₀
  have hab₁ : IsAbelianScheme G₁ :=
    { comm := inferInstance
      smooth := inferInstanceAs (Smooth (pullback.snd B₀.hom t))
      proper := inferInstanceAs (IsProper (pullback.snd B₀.hom t))
      geomConnected := inferInstanceAs (GeometricallyConnected (pullback.snd B₀.hom t)) }
  have hpb₁ : IsPullback (pullback.fst B₀.hom t) G₁.hom B₀.hom t := IsPullback.of_hasPullback _ _
  have wφ : φ₀ ≫ B₀.hom = (G.hom ≫ spMap R₁.subtype) ≫ t := by
    rw [Category.assoc, e]; exact hpb₀.1.w
  let φ : G.left ⟶ G₁.left := pullback.lift φ₀ (G.hom ≫ spMap R₁.subtype) wφ
  have hφ₁ : φ ≫ pullback.fst B₀.hom t = φ₀ := pullback.lift_fst _ _ _
  have hφ₂ : φ ≫ G₁.hom = G.hom ≫ spMap R₁.subtype := pullback.lift_snd _ _ _
  have hφ : IsGrpPullback G G₁ (spMap R₁.subtype) φ :=
    (isGrpPullback_pullback B₀ t).cancel (hpb₀.congr e.symm hφ₁.symm) hφ₂
  obtain ⟨L₁, hL₁, hiso⟩ := hSP R₁ h hT G₁.left G₁.hom (pullback.fst B₀.hom t) φ hpb₁ hφ₁ hφ₂
  exact ⟨R₁, G₁, inferInstance, φ, L₁, hft, hab₁, hφ, hL₁, hiso⟩

end GlobalTheory.AmpleFibreMove
