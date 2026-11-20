import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianDeRhamStructure
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechDeRhamComparisonBijectiveCupSmooth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullOverOneEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafComparisonInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTangentVectorFunctionalGlobalFormsAbelianS
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormValueOnTangentVectorEqZeroOfGlobalFormZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieAlgebraFiniteProjectiveRank
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsDetEquivOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieInj

open GlobalTheory.CechDR

variable {R : Type} [CommRing R]

/- English proof (translation)
Introduce `ω`. Take `⟨-, hinj, -⟩` from `(hH R A g hab hdim).2.2.2.2.1`. Use `haveI := hab.smooth`. Use `haveI := hab.proper`. Establish `hb` using `(cechDeRham_comparison_bijective_cup_smooth hP R A.left (A.hom ≫ 𝟙 (Sp R)) inferInstance inferInstance inferInstance).1`.

Take `⟨c, hc⟩` from `hb.2 (clForm _ ω)`. Establish `hmem : clForm (A.hom ≫ 𝟙 (Sp R)) ω ∈ CechHodgeFiltration (A.hom ≫ 𝟙 (Sp R))`. Rewrite using `[cechHodgeFiltration_eq_range]`. Conclude with `⟨ω, rfl⟩`. Establish `h0 : toHO1 _ (cmp1 (A.hom ≫ 𝟙 (Sp R)) c) = 0` using `by rw [hc]; exact hmem`.

Rewrite `h0` using `[structureSheaf_comparison_comm]`. Establish `h1 : toH1O _ c = 0` using `GlobalTheory.CechDR.cmpO_injective R A.left _ (h0.trans (map_zero _).symm)`. Establish `h2 : c ∈ F1 (A.hom ≫ 𝟙 (Sp R))` using `h1`. Rewrite `h2` using `[hodgeFiltration_eq_range]`. Take `⟨f, rfl⟩` from `h2`.

Use `⟨f, hinj ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `clForm (A.hom ≫ 𝟙 (Sp R)) (cmpForm _ f) = clForm (A.hom ≫ 𝟙 (Sp R)) ω`. Rewrite using `[← comparison_formClass, hc]`.
-/
theorem cmpForm_surjective (hP : GlobalTheory.Published.CrystallineSmoothLift) (hH : GlobalTheory.Published.AbelianHodgeDeRham)
    (A : Over (Sp R)) [GrpObj A] (g : ℕ) (hab : IsAbelianScheme A)
    (hdim : SmoothOfRelativeDimension g A.hom) :
    Function.Surjective (cmpForm (A.hom ≫ 𝟙 (Sp R))) := by
  intro ω
  obtain ⟨-, hinj, -⟩ := (hH R A g hab hdim).2.2.2.2.1
  haveI := hab.smooth
  haveI := hab.proper
  have hb := (cechDeRham_comparison_bijective_cup_smooth hP R A.left (A.hom ≫ 𝟙 (Sp R)) inferInstance inferInstance
    inferInstance).1
  obtain ⟨c, hc⟩ := hb.2 (clForm _ ω)
  have hmem : clForm (A.hom ≫ 𝟙 (Sp R)) ω ∈ CechHodgeFiltration (A.hom ≫ 𝟙 (Sp R)) := by
    rw [cechHodgeFiltration_eq_range]; exact ⟨ω, rfl⟩
  have h0 : toHO1 _ (cmp1 (A.hom ≫ 𝟙 (Sp R)) c) = 0 := by rw [hc]; exact hmem
  rw [structureSheaf_comparison_comm] at h0
  have h1 : toH1O _ c = 0 := GlobalTheory.CechDR.cmpO_injective R A.left _ (h0.trans (map_zero _).symm)
  have h2 : c ∈ F1 (A.hom ≫ 𝟙 (Sp R)) := h1
  rw [hodgeFiltration_eq_range] at h2
  obtain ⟨f, rfl⟩ := h2
  refine ⟨f, hinj ?_⟩
  change clForm (A.hom ≫ 𝟙 (Sp R)) (cmpForm _ f) = clForm (A.hom ≫ 𝟙 (Sp R)) ω
  rw [← comparison_formClass, hc]

section Lie

open ReciprocityTheory.ChartRestriction.G MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

/- English proof (translation)
Use `haveI : Smooth A.hom := hdim.smooth`. Use `GlobalTheory.LieProj.finite_projective_of_localBasis (M := GlobalTheory.Serre.Lie a) g fun p ↦ ?_` and prove the remaining obligations. Take `⟨r, hr, ⟨C⟩, v, hv⟩` from `GlobalTheory.LieProj.exists_chart_lieBasis A g hdim p`. Use `⟨r, hr, ?_⟩` and prove the remaining obligations. Take `⟨a', -⟩` from `GlobalTheory.OActPull.exists_oAct_of_isGrpPullback a (isGrpPullback_pullback A (ReciprocityTheory.ChartRestriction.G.Chart.fB R (Localization.Away r)))`.

Take `⟨e⟩` from `GlobalTheory.LieAway.lie_away A a r a' ⟨C⟩`. Conclude with `⟨(GlobalTheory.Serre.Lie.basis a' hv).map e.symm⟩`.
-/
theorem lie_finite_projective (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (g : ℕ)
    (hdim : SmoothOfRelativeDimension g A.hom) (a : OAct ℤ A) :
    Module.Finite R (GlobalTheory.Serre.Lie a) ∧ Module.Projective R (GlobalTheory.Serre.Lie a) ∧
      ∀ p, Module.rankAtStalk (R := R) (GlobalTheory.Serre.Lie a) p = g := by
  haveI : Smooth A.hom := hdim.smooth
  refine GlobalTheory.LieProj.finite_projective_of_localBasis (M := GlobalTheory.Serre.Lie a) g fun p ↦ ?_
  obtain ⟨r, hr, ⟨C⟩, v, hv⟩ := GlobalTheory.LieProj.exists_chart_lieBasis A g hdim p
  refine ⟨r, hr, ?_⟩
  obtain ⟨a', -⟩ := GlobalTheory.OActPull.exists_oAct_of_isGrpPullback a
    (isGrpPullback_pullback A (ReciprocityTheory.ChartRestriction.G.Chart.fB R (Localization.Away r)))
  obtain ⟨e⟩ := GlobalTheory.LieAway.lie_away A a r a' ⟨C⟩
  exact ⟨(GlobalTheory.Serre.Lie.basis a' hv).map e.symm⟩

end Lie

def valMap (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (a : OAct ℤ A) :
    GlobalTheory.Serre.Lie a →ₗ[R] Module.Dual R (Form (A.hom ≫ 𝟙 (Sp R))) where
  toFun v := tanVal v.hom
  map_add' v w := LinearMap.ext fun f ↦ by
    rw [LinearMap.add_apply, ← tanVal_mul v.isTangent w.isTangent, GlobalTheory.Serre.Lie.hom_add]
  map_smul' r v := LinearMap.ext fun f ↦ by
    rw [LinearMap.smul_apply, RingHom.id_apply, smul_eq_mul, ← tanVal_epsScale, GlobalTheory.Serre.Lie.hom_smul]

/- English proof (translation)
Rewrite using `[Submodule.mem_dualAnnihilator]`. Introduce `f hf`. Conclude with `GlobalTheory.TanVanish.tanVal_eq_zero_of_cmpForm_eq_zero R A u.hom f hf`.
-/
theorem valMap_mem (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (a : OAct ℤ A) (u : GlobalTheory.Serre.Lie a) :
    valMap A a u ∈ (LinearMap.ker (cmpForm (A.hom ≫ 𝟙 (Sp R)))).dualAnnihilator := by
  rw [Submodule.mem_dualAnnihilator]
  intro f hf
  exact GlobalTheory.TanVanish.tanVal_eq_zero_of_cmpForm_eq_zero R A u.hom f hf

/- English proof (translation)
Establish `hex` using `GlobalTheory.LieDual.exists_tangent_of_functional hP hH R A g hab hdim`. Establish `key : ∀ φ : Module.Dual R (Form (A.hom ≫ 𝟙 (Sp R))), (∀ f, cmpForm (A.hom ≫ 𝟙 (Sp R)) f = 0 → φ f = 0) → ∃ u : GlobalTheory.Serre.Lie a, valMap A a u = φ`. Introduce `φ hφ`. Take `⟨u, hu, hu'⟩` from `hex φ hφ`. Conclude with `⟨GlobalTheory.Serre.Lie.mk a u hu, LinearMap.ext hu'⟩`.

Introduce `ψ`. Establish `hψ : ∀ f, cmpForm (A.hom ≫ 𝟙 (Sp R)) f = 0 → ψ.1 f = 0` using `fun f hf ↦ (Submodule.mem_dualAnnihilator ψ.1).1 ψ.2 f (LinearMap.mem_ker.2 hf)`. Conclude with `(key ψ.1 hψ).imp fun u hu ↦ Subtype.ext hu`.
-/
theorem valMap_surjective (hP : GlobalTheory.Published.CrystallineSmoothLift) (hH : GlobalTheory.Published.AbelianHodgeDeRham)
    (A : Over (Sp R)) [GrpObj A] (g : ℕ) (hab : IsAbelianScheme A)
    (hdim : SmoothOfRelativeDimension g A.hom) [IsCommMonObj A] (a : OAct ℤ A) :
    Function.Surjective ((valMap A a).codRestrict _ (valMap_mem A a)) := by
  have hex := GlobalTheory.LieDual.exists_tangent_of_functional hP hH R A g hab hdim
  have key : ∀ φ : Module.Dual R (Form (A.hom ≫ 𝟙 (Sp R))),
      (∀ f, cmpForm (A.hom ≫ 𝟙 (Sp R)) f = 0 → φ f = 0) → ∃ u : GlobalTheory.Serre.Lie a, valMap A a u = φ := by
    intro φ hφ
    obtain ⟨u, hu, hu'⟩ := hex φ hφ
    exact ⟨GlobalTheory.Serre.Lie.mk a u hu, LinearMap.ext hu'⟩
  intro ψ
  have hψ : ∀ f, cmpForm (A.hom ≫ 𝟙 (Sp R)) f = 0 → ψ.1 f = 0 := fun f hf ↦
    (Submodule.mem_dualAnnihilator ψ.1).1 ψ.2 f (LinearMap.mem_ker.2 hf)
  exact (key ψ.1 hψ).imp fun u hu ↦ Subtype.ext hu

/- English proof (translation)
Introduce `hP hH R _ A _ g hab hdim v w hv hw hvw`. Use `haveI : IsCommMonObj A := hab.comm`. Establish `hT` using `lie_finite_projective A g hdim (GlobalTheory.Serre.intAct A)`. Use `haveI := hT.1`. Use `haveI := hT.2.1`.

Establish `hcl : ClosedForm (A.hom ≫ 𝟙 (Sp R)) = ⊤` using `(hH R A g hab hdim).2.2.2.2.1.1`. Establish `hG` using `(hH R A g hab hdim).2.2.1`. Use `haveI : Module.Finite R (GlobForm (A.hom ≫ 𝟙 (Sp R))) := hG.1`. Use `haveI : Module.Projective R (GlobForm (A.hom ≫ 𝟙 (Sp R))) := hG.2.1`. Establish `e1 : (Form (A.hom ≫ 𝟙 (Sp R)) ⧸ LinearMap.ker (cmpForm (A.hom ≫ 𝟙 (Sp R)))) ≃ₗ[R] GlobForm (A.hom ≫ 𝟙 (Sp R))` using `((cmpForm (A.hom ≫ 𝟙 (Sp R))).quotKerEquivOfSurjective (cmpForm_surjective hP hH A g hab hdim)).trans (LinearEquiv.ofTop _ hcl)`.

Establish `eN : (LinearMap.ker (cmpForm (A.hom ≫ 𝟙 (Sp R)))).dualAnnihilator ≃ₗ[R] Module.Dual R (GlobForm (A.hom ≫ 𝟙 (Sp R)))` using `(Submodule.dualQuotEquivDualAnnihilator _).symm.trans e1.symm.dualMap`. Use `haveI : Module.Finite R (LinearMap.ker (cmpForm (A.hom ≫ 𝟙 (Sp R)))).dualAnnihilator := Module.Finite.equiv eN.symm`. Use `haveI : Module.Projective R (LinearMap.ker (cmpForm (A.hom ≫ 𝟙 (Sp R)))).dualAnnihilator := Module.Projective.of_equiv eN.symm`. Establish `hbij` using `Module.bijective_of_surjective_of_rankAtStalk_eq (valMap_surjective hP hH A g hab hdim (GlobalTheory.Serre.intAct A)) fun m _ ↦ by`. Rewrite using `[hT.2.2, congrFun (Module.rankAtStalk_eq_of_equiv eN) _, GlobalTheory.TopExt.rankAtStalk_dual]`.

Conclude with `(hG.2.2 _).symm`. Establish `h` using `hbij.1 (a₁ := GlobalTheory.Serre.Lie.mk (GlobalTheory.Serre.intAct A) v hv) (a₂ := GlobalTheory.Serre.Lie.mk (GlobalTheory.Serre.intAct A) w hw) (Subtype.ext (LinearMap.ext hvw))`. Conclude with `congrArg GlobalTheory.Serre.Lie.hom h`.
-/
theorem tangent_eq_of_tanVal_eq : GlobalTheory.Published.CrystallineSmoothLift → GlobalTheory.Published.AbelianHodgeDeRham →
    ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
      SmoothOfRelativeDimension g A.hom → ∀ v w : epsR R ⟶ A, IsTangent v → IsTangent w →
        (∀ f : Form (A.hom ≫ 𝟙 (Sp R)), tanVal v f = tanVal w f) → v = w := by
  intro hP hH R _ A _ g hab hdim v w hv hw hvw
  haveI : IsCommMonObj A := hab.comm
  have hT := lie_finite_projective A g hdim (GlobalTheory.Serre.intAct A)
  haveI := hT.1
  haveI := hT.2.1
  have hcl : ClosedForm (A.hom ≫ 𝟙 (Sp R)) = ⊤ := (hH R A g hab hdim).2.2.2.2.1.1
  have hG := (hH R A g hab hdim).2.2.1
  haveI : Module.Finite R (GlobForm (A.hom ≫ 𝟙 (Sp R))) := hG.1
  haveI : Module.Projective R (GlobForm (A.hom ≫ 𝟙 (Sp R))) := hG.2.1
  have e1 : (Form (A.hom ≫ 𝟙 (Sp R)) ⧸ LinearMap.ker (cmpForm (A.hom ≫ 𝟙 (Sp R)))) ≃ₗ[R]
      GlobForm (A.hom ≫ 𝟙 (Sp R)) :=
    ((cmpForm (A.hom ≫ 𝟙 (Sp R))).quotKerEquivOfSurjective
      (cmpForm_surjective hP hH A g hab hdim)).trans (LinearEquiv.ofTop _ hcl)
  have eN : (LinearMap.ker (cmpForm (A.hom ≫ 𝟙 (Sp R)))).dualAnnihilator ≃ₗ[R]
      Module.Dual R (GlobForm (A.hom ≫ 𝟙 (Sp R))) :=
    (Submodule.dualQuotEquivDualAnnihilator _).symm.trans e1.symm.dualMap
  haveI : Module.Finite R (LinearMap.ker (cmpForm (A.hom ≫ 𝟙 (Sp R)))).dualAnnihilator :=
    Module.Finite.equiv eN.symm
  haveI : Module.Projective R (LinearMap.ker (cmpForm (A.hom ≫ 𝟙 (Sp R)))).dualAnnihilator :=
    Module.Projective.of_equiv eN.symm
  have hbij := Module.bijective_of_surjective_of_rankAtStalk_eq
    (valMap_surjective hP hH A g hab hdim (GlobalTheory.Serre.intAct A)) fun m _ ↦ by
      rw [hT.2.2, congrFun (Module.rankAtStalk_eq_of_equiv eN) _, GlobalTheory.TopExt.rankAtStalk_dual]
      exact (hG.2.2 _).symm
  have h := hbij.1 (a₁ := GlobalTheory.Serre.Lie.mk (GlobalTheory.Serre.intAct A) v hv)
    (a₂ := GlobalTheory.Serre.Lie.mk (GlobalTheory.Serre.intAct A) w hw) (Subtype.ext (LinearMap.ext hvw))
  exact congrArg GlobalTheory.Serre.Lie.hom h

end GlobalTheory.LieInj
