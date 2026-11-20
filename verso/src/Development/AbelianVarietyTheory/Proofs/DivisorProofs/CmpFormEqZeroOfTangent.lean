import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianDeRhamStructure
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechDeRhamComparisonBijectiveCupSmooth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullOverOneEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianDeRhamFreeOfCrystallineComparisonStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafComparisonInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormValueOnTangentVectorEqZeroOfGlobalFormZeroStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieBasisSmoothCommGroupSchemeFieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineFormTangentValueMulAbelianSchemeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackFormVanishesTangentsOfLieBasisStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmpFormEqZeroOfPullbackVanishingStatement

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.LieInjField

open GlobalTheory.CechDR in

/- English proof (translation)
Establish `hsm : Smooth (A.hom ≫ 𝟙 (Sp R))` using `by haveI := hab.smooth; infer_instance`. Establish `hsep : IsSeparated (A.hom ≫ 𝟙 (Sp R))` using `by haveI := hab.proper; infer_instance`. Establish `hqc : QuasiCompact (A.hom ≫ 𝟙 (Sp R))` using `by haveI := hab.proper; infer_instance`. Establish `hcmp` using `(cechDeRham_comparison_bijective_cup_smooth hC R A.left _ hsm hsep hqc).1`. Establish `hcl : Function.Injective (clForm (A.hom ≫ 𝟙 (Sp R)))` using `(hH R A g hab hdim).2.2.2.2.1.2.1`.

Introduce `ω`. Take `⟨c, hc⟩` from `hcmp.2 (clForm _ ω)`. Establish `hF : clForm _ ω ∈ CechHodgeFiltration (A.hom ≫ 𝟙 (Sp R))` using `by rw [cechHodgeFiltration_eq_range]; exact ⟨ω, rfl⟩`. Establish `h1 : c ∈ F1 (A.hom ≫ 𝟙 (Sp R))`. Express the relevant statement in the definitionally equal form `toH1O _ c = 0`.

Apply `GlobalTheory.T.structure_sheaf_comparison_injective R A.left _` to reduce the goal to its premises. Rewrite using `[← structureSheaf_comparison_comm, map_zero, hc]`. Conclude with `hF`. Rewrite `h1` using `[hodgeFiltration_eq_range]`. Take `⟨f, rfl⟩` from `h1`.

Rewrite `hc` using `[comparison_formClass]`. Conclude with `⟨f, hcl hc⟩`.
-/
theorem cmpForm_surjective (hC : GlobalTheory.Published.CrystallineSmoothLift) (hH : GlobalTheory.Published.AbelianHodgeDeRham)
    (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ) (hab : IsAbelianScheme A)
    (hdim : SmoothOfRelativeDimension g A.hom) : Function.Surjective (cmpForm (A.hom ≫ 𝟙 (Sp R))) := by
  have hsm : Smooth (A.hom ≫ 𝟙 (Sp R)) := by haveI := hab.smooth; infer_instance
  have hsep : IsSeparated (A.hom ≫ 𝟙 (Sp R)) := by haveI := hab.proper; infer_instance
  have hqc : QuasiCompact (A.hom ≫ 𝟙 (Sp R)) := by haveI := hab.proper; infer_instance
  have hcmp := (cechDeRham_comparison_bijective_cup_smooth hC R A.left _ hsm hsep hqc).1
  have hcl : Function.Injective (clForm (A.hom ≫ 𝟙 (Sp R))) := (hH R A g hab hdim).2.2.2.2.1.2.1
  intro ω
  obtain ⟨c, hc⟩ := hcmp.2 (clForm _ ω)
  have hF : clForm _ ω ∈ CechHodgeFiltration (A.hom ≫ 𝟙 (Sp R)) := by rw [cechHodgeFiltration_eq_range]; exact ⟨ω, rfl⟩
  have h1 : c ∈ F1 (A.hom ≫ 𝟙 (Sp R)) := by
    change toH1O _ c = 0
    apply GlobalTheory.T.structure_sheaf_comparison_injective R A.left _
    rw [← structureSheaf_comparison_comm, map_zero, hc]
    exact hF
  rw [hodgeFiltration_eq_range] at h1
  obtain ⟨f, rfl⟩ := h1
  rw [comparison_formClass] at hc
  exact ⟨f, hcl hc⟩

/- English proof (translation)
Use `haveI := hab.comm`. Establish `hsm : Smooth B.hom` using `hab.smooth`. Take `⟨y, hy⟩` from `GlobalTheory.T.exists_lieBasis_smooth_commGroupScheme_field K B g hdim`. Use `GlobalTheory.T.cmpForm_eq_zero_of_pullback_vanishing K B hsm f fun L _ σ ↦ ?_` and prove the remaining obligations. Use `letI : GrpObj ((Over.pullback (spMap σ)).obj B) := Functor.grpObjObj`.

Establish `hG` using `isGrpPullback_pullback B (spMap σ)`. Establish `hab'` using `GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hab hG`. Use `haveI := hab'.comm`. Establish `hdim' : SmoothOfRelativeDimension g ((Over.pullback (spMap σ)).obj B).hom` using `(smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback hG.1 hdim`. Establish `m : IsMor (dp0 K) (B.hom ≫ 𝟙 (Sp K)) (dp0 L) (((Over.pullback (spMap σ)).obj B).hom ≫ 𝟙 (Sp L)) σ (Limits.pullback.fst B.hom (spMap σ))` using `IsMor.of_dividedPowersZeroIdeal _ (by simpa using hG.1.w)`.

Use `⟨_, _, m, hG.1, fun u ↦ ?_⟩` and prove the remaining obligations. Set `c : epsR L ⟶ (Over.pullback (spMap σ)).obj B` to `GlobalTheory.GrpTangent.epsScale 0 ≫ u`. Establish `hc : tanVal c (m.pullForm f) = 0`. Rewrite using `[tanVal_epsScale, zero_mul]`. Establish `ht : IsTangent (c⁻¹ * u)`.

Rewrite using `[GlobalTheory.GrpTangent.isTangent_iff, MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, GlobalTheory.GrpTangent.epsZero_epsScale, inv_mul_cancel]`. Establish `e : u = c * (c⁻¹ * u)` using `(mul_inv_cancel_left c u).symm`. Rewrite using `[e, GlobalTheory.T.crystallineForm_tangentValue_mul_abelianScheme hC hH L _ g hab' hdim', hc, zero_add]`. Conclude with `GlobalTheory.T.pullbackForm_vanishes_tangents_of_lieBasis K B hsm g y hy f (fun i ↦ hf _ (hy.1 i)) L σ _ _ hG m _ ht`.
-/
theorem cmpForm_eq_zero_of_tangent (hC : GlobalTheory.Published.CrystallineSmoothLift) (hH : GlobalTheory.Published.AbelianHodgeDeRham)
    (K : Type) [Field K] (B : Over (Sp K)) [GrpObj B] (g : ℕ) (hab : IsAbelianScheme B)
    (hdim : SmoothOfRelativeDimension g B.hom) (f : Form (B.hom ≫ 𝟙 (Sp K)))
    (hf : ∀ v : epsR K ⟶ B, IsTangent v → tanVal v f = 0) :
    GlobalTheory.CechDR.cmpForm (B.hom ≫ 𝟙 (Sp K)) f = 0 := by
  haveI := hab.comm
  have hsm : Smooth B.hom := hab.smooth
  obtain ⟨y, hy⟩ := GlobalTheory.T.exists_lieBasis_smooth_commGroupScheme_field K B g hdim
  refine GlobalTheory.T.cmpForm_eq_zero_of_pullback_vanishing K B hsm f fun L _ σ ↦ ?_
  letI : GrpObj ((Over.pullback (spMap σ)).obj B) := Functor.grpObjObj
  have hG := isGrpPullback_pullback B (spMap σ)
  have hab' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hab hG
  haveI := hab'.comm
  have hdim' : SmoothOfRelativeDimension g ((Over.pullback (spMap σ)).obj B).hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback hG.1 hdim
  have m : IsMor (dp0 K) (B.hom ≫ 𝟙 (Sp K)) (dp0 L) (((Over.pullback (spMap σ)).obj B).hom ≫ 𝟙 (Sp L)) σ
      (Limits.pullback.fst B.hom (spMap σ)) := IsMor.of_dividedPowersZeroIdeal _ (by simpa using hG.1.w)
  refine ⟨_, _, m, hG.1, fun u ↦ ?_⟩
  let c : epsR L ⟶ (Over.pullback (spMap σ)).obj B := GlobalTheory.GrpTangent.epsScale 0 ≫ u
  have hc : tanVal c (m.pullForm f) = 0 := by
    rw [tanVal_epsScale, zero_mul]
  have ht : IsTangent (c⁻¹ * u) := by
    rw [GlobalTheory.GrpTangent.isTangent_iff, MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc,
      GlobalTheory.GrpTangent.epsZero_epsScale, inv_mul_cancel]
  have e : u = c * (c⁻¹ * u) := (mul_inv_cancel_left c u).symm
  rw [e, GlobalTheory.T.crystallineForm_tangentValue_mul_abelianScheme hC hH L _ g hab' hdim', hc, zero_add]
  exact GlobalTheory.T.pullbackForm_vanishes_tangents_of_lieBasis K B hsm g y hy f (fun i ↦ hf _ (hy.1 i)) L σ _ _ hG m _ ht

def lieVal (K : Type) [Field K] (B : Over (Sp K)) [GrpObj B] [IsCommMonObj B] :
    Serre.Lie (Serre.intAct B) →ₗ[K] Module.Dual K (Form (B.hom ≫ 𝟙 (Sp K))) where
  toFun v := tanVal v.hom
  map_add' v w := LinearMap.ext fun f ↦ tanVal_mul v.isTangent w.isTangent f
  map_smul' r v := LinearMap.ext fun f ↦ tanVal_epsScale r v.hom f

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem lieVal_apply (K : Type) [Field K] (B : Over (Sp K)) [GrpObj B] [IsCommMonObj B]
    (v : Serre.Lie (Serre.intAct B)) : lieVal K B v = tanVal v.hom := rfl

/- English proof (translation)
Introduce `hC hH K _ B _ g hab hdim v w hv hw h`. Use `haveI := hab.comm`. Take `⟨y, hy⟩` from `GlobalTheory.T.exists_lieBasis_smooth_commGroupScheme_field K B g hdim`. Set `b` to `Serre.Lie.basis (Serre.intAct B) hy`. Use `haveI := Module.Finite.of_basis b`.

Establish `hL : Module.finrank K (Serre.Lie (Serre.intAct B)) = g`. Rewrite using `[Module.finrank_eq_card_basis b, Fintype.card_fin]`. Establish `htop : GlobalTheory.CechDR.ClosedForm (B.hom ≫ 𝟙 (Sp K)) = ⊤` using `(hH K B g hab hdim).2.2.2.2.1.1`. Take `⟨hfin, -, hrk⟩ : Module.Finite K (GlobalTheory.CechDR.GlobForm (B.hom ≫ 𝟙 (Sp K))) ∧ Module.Projective K (GlobalTheory.CechDR.GlobForm (B.hom ≫ 𝟙 (Sp K))) ∧ ∀ p : PrimeSpectrum K, Module.rankAtStalk (GlobalTheory.CechDR.GlobForm (B.hom ≫ 𝟙 (Sp K))) p = g` from `(hH K B g hab hdim).2.2.1`. Establish `hG : Module.finrank K (GlobalTheory.CechDR.GlobForm (B.hom ≫ 𝟙 (Sp K))) = g`.

Establish `h'` using `hrk (IsLocalRing.closedPoint K)`. Rewrite `h'` using `[Module.rankAtStalk_eq_finrank_of_free]`. Then use the resulting hypothesis. Set `eC : GlobalTheory.CechDR.ClosedForm (B.hom ≫ 𝟙 (Sp K)) ≃ₗ[K] GlobalTheory.CechDR.GlobForm (B.hom ≫ 𝟙 (Sp K))` to `LinearEquiv.ofTop _ htop`. Use `haveI : Module.Finite K (GlobalTheory.CechDR.ClosedForm (B.hom ≫ 𝟙 (Sp K))) := Module.Finite.equiv eC.symm`. Establish `hC' : Module.finrank K (GlobalTheory.CechDR.ClosedForm (B.hom ≫ 𝟙 (Sp K))) = g` using `by rw [eC.finrank_eq, hG]`.

Set `c` to `GlobalTheory.CechDR.cmpForm (B.hom ≫ 𝟙 (Sp K))`. Establish `hcs : Function.Surjective c` using `cmpForm_surjective hC hH K B g hab hdim`. Set `P` to `lieVal K B`. Establish `hker : LinearMap.ker c ≤ LinearMap.ker P.flip` using `fun f hf ↦ LinearMap.ext fun u ↦ GlobalTheory.T.formValueOnTangentVector_eq_zero_of_globalForm_zero K B u.hom f hf`. Set `T : GlobalTheory.CechDR.ClosedForm (B.hom ≫ 𝟙 (Sp K)) →ₗ[K] Module.Dual K (Serre.Lie (Serre.intAct B))` to `(LinearMap.ker c).liftQ P.flip hker ∘ₗ (c.quotKerEquivOfSurjective hcs).symm.toLinearMap`.

Establish `hT : ∀ f, T (c f) = P.flip f` using `fun f ↦ by`. Establish `: (c.quotKerEquivOfSurjective hcs).symm (c f) = Submodule.Quotient.mk f` using `(c.quotKerEquivOfSurjective hcs).symm_apply_eq.2 rfl`. Express the relevant statement in the definitionally equal form `(LinearMap.ker c).liftQ P.flip hker ((c.quotKerEquivOfSurjective hcs).symm (c f)) = _`. Rewrite using `[this]`. Both sides reduce to the same expression.

Establish `hTi : Function.Injective T`. Rewrite using `[← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]`. Introduce `ω hω`. Take `⟨f, rfl⟩` from `hcs ω`. Rewrite `hω` using `[LinearMap.mem_ker, hT]`.

Conclude with `cmpForm_eq_zero_of_tangent hC hH K B g hab hdim f fun v hv ↦ LinearMap.congr_fun hω (Serre.Lie.mk (Serre.intAct B) v hv)`. Establish `hTs : Function.Surjective T` using `(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by`. Rewrite using `[Subspace.dual_finrank_eq, hL, hC'])).1 hTi`. Set `V` to `Serre.Lie.mk (Serre.intAct B) v hv`. Set `W` to `Serre.Lie.mk (Serre.intAct B) w hw`.

Establish `hsurj : Function.Surjective (T ∘ₗ c)` using `hTs.comp hcs`. Establish `key : ∀ φ : Module.Dual K (Serre.Lie (Serre.intAct B)), φ V = φ W` using `fun φ ↦ by`. Take `⟨f, rfl⟩` from `hsurj φ`. Rewrite using `[LinearMap.comp_apply, hT]`. Conclude with `h f`.

Establish `hVW : V - W = 0` using `(Module.forall_dual_apply_eq_zero_iff K (V - W)).1 fun φ ↦ by rw [map_sub, key φ, sub_self]`. Conclude with `congrArg Serre.Lie.hom (sub_eq_zero.1 hVW)`.
-/
theorem eq_of_tanVal_eq : GlobalTheory.Published.CrystallineSmoothLift → GlobalTheory.Published.AbelianHodgeDeRham → ∀ (K : Type) [Field K] (B : Over (Sp K)) [GrpObj B] (g : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → ∀ v w : epsR K ⟶ B, IsTangent v → IsTangent w → (∀ f : Form (B.hom ≫ 𝟙 (Sp K)), tanVal v f = tanVal w f) → v = w := by
  intro hC hH K _ B _ g hab hdim v w hv hw h
  haveI := hab.comm
  obtain ⟨y, hy⟩ := GlobalTheory.T.exists_lieBasis_smooth_commGroupScheme_field K B g hdim
  let b := Serre.Lie.basis (Serre.intAct B) hy
  haveI := Module.Finite.of_basis b
  have hL : Module.finrank K (Serre.Lie (Serre.intAct B)) = g := by
    rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  have htop : GlobalTheory.CechDR.ClosedForm (B.hom ≫ 𝟙 (Sp K)) = ⊤ := (hH K B g hab hdim).2.2.2.2.1.1
  obtain ⟨hfin, -, hrk⟩ : Module.Finite K (GlobalTheory.CechDR.GlobForm (B.hom ≫ 𝟙 (Sp K))) ∧
      Module.Projective K (GlobalTheory.CechDR.GlobForm (B.hom ≫ 𝟙 (Sp K))) ∧
      ∀ p : PrimeSpectrum K, Module.rankAtStalk (GlobalTheory.CechDR.GlobForm (B.hom ≫ 𝟙 (Sp K))) p = g :=
    (hH K B g hab hdim).2.2.1
  have hG : Module.finrank K (GlobalTheory.CechDR.GlobForm (B.hom ≫ 𝟙 (Sp K))) = g := by
    have h' := hrk (IsLocalRing.closedPoint K)
    rwa [Module.rankAtStalk_eq_finrank_of_free] at h'
  let eC : GlobalTheory.CechDR.ClosedForm (B.hom ≫ 𝟙 (Sp K)) ≃ₗ[K] GlobalTheory.CechDR.GlobForm (B.hom ≫ 𝟙 (Sp K)) := LinearEquiv.ofTop _ htop
  haveI : Module.Finite K (GlobalTheory.CechDR.ClosedForm (B.hom ≫ 𝟙 (Sp K))) := Module.Finite.equiv eC.symm
  have hC' : Module.finrank K (GlobalTheory.CechDR.ClosedForm (B.hom ≫ 𝟙 (Sp K))) = g := by rw [eC.finrank_eq, hG]
  let c := GlobalTheory.CechDR.cmpForm (B.hom ≫ 𝟙 (Sp K))
  have hcs : Function.Surjective c := cmpForm_surjective hC hH K B g hab hdim
  let P := lieVal K B
  have hker : LinearMap.ker c ≤ LinearMap.ker P.flip := fun f hf ↦
    LinearMap.ext fun u ↦ GlobalTheory.T.formValueOnTangentVector_eq_zero_of_globalForm_zero K B u.hom f hf
  let T : GlobalTheory.CechDR.ClosedForm (B.hom ≫ 𝟙 (Sp K)) →ₗ[K] Module.Dual K (Serre.Lie (Serre.intAct B)) :=
    (LinearMap.ker c).liftQ P.flip hker ∘ₗ (c.quotKerEquivOfSurjective hcs).symm.toLinearMap
  have hT : ∀ f, T (c f) = P.flip f := fun f ↦ by
    have : (c.quotKerEquivOfSurjective hcs).symm (c f) = Submodule.Quotient.mk f :=
      (c.quotKerEquivOfSurjective hcs).symm_apply_eq.2 rfl
    change (LinearMap.ker c).liftQ P.flip hker ((c.quotKerEquivOfSurjective hcs).symm (c f)) = _
    rw [this]; rfl
  have hTi : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro ω hω
    obtain ⟨f, rfl⟩ := hcs ω
    rw [LinearMap.mem_ker, hT] at hω
    exact cmpForm_eq_zero_of_tangent hC hH K B g hab hdim f fun v hv ↦
      LinearMap.congr_fun hω (Serre.Lie.mk (Serre.intAct B) v hv)
  have hTs : Function.Surjective T :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by
      rw [Subspace.dual_finrank_eq, hL, hC'])).1 hTi
  let V := Serre.Lie.mk (Serre.intAct B) v hv
  let W := Serre.Lie.mk (Serre.intAct B) w hw
  have hsurj : Function.Surjective (T ∘ₗ c) := hTs.comp hcs
  have key : ∀ φ : Module.Dual K (Serre.Lie (Serre.intAct B)), φ V = φ W := fun φ ↦ by
    obtain ⟨f, rfl⟩ := hsurj φ
    rw [LinearMap.comp_apply, hT]
    exact h f
  have hVW : V - W = 0 :=
    (Module.forall_dual_apply_eq_zero_iff K (V - W)).1 fun φ ↦ by rw [map_sub, key φ, sub_self]
  exact congrArg Serre.Lie.hom (sub_eq_zero.1 hVW)

end GlobalTheory.LieInjField
