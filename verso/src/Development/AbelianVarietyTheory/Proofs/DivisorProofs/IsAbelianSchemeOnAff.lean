import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZeroSectionBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheaf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFrameOfForallExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VectorBundleOfFreeStalks
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullbackFactor
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
  GlobalTheory.DeRham

namespace GlobalTheory.DeRhamSheaf.VB

open GlobalTheory.Published.AbelianDeRham (bcMor)

variable {T : Scheme.{0}} (A : Over T) [GrpObj A]

/- English proof (translation)
The claim follows from `hU.map_fromSpec hW (homOfLE h).op`.
-/
theorem fromSpec_res {U W : T.Opens} (hU : IsAffineOpen U) (hW : IsAffineOpen W) (h : W ≤ U) :
    letI := resAlg h
    spMap (algebraMap Γ(T, U) Γ(T, W)) ≫ hU.fromSpec = hW.fromSpec :=
  hU.map_fromSpec hW (homOfLE h).op

/- English proof (translation)
The claim follows from `e ▸ h`.
-/
theorem isGrpPullback_congr {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G]
    {f₁ f₂ : S' ⟶ S} {φ : G'.left ⟶ G.left} (e : f₁ = f₂) (h : IsGrpPullback G' G f₁ φ) :
    IsGrpPullback G' G f₂ φ := e ▸ h

/- English proof (translation)
The claim follows from `GlobalTheory.isAbelianScheme_pullback_obj _ A hA`.
-/
theorem isAbelianScheme_onAff (hA : IsAbelianScheme A) {V : T.Opens} (hV : IsAffineOpen V) :
    IsAbelianScheme (onAff A hV) :=
  GlobalTheory.isAbelianScheme_pullback_obj _ A hA

/- English proof (translation)
Conclude with `(smoothOfRelativeDimension_isStableUnderBaseChange (n := g)).of_isPullback (isGrpPullback_pullback A hV.fromSpec).1 hg`.
-/
theorem smooth_onAff {g : ℕ} (hg : SmoothOfRelativeDimension g A.hom) {V : T.Opens}
    (hV : IsAffineOpen V) : SmoothOfRelativeDimension g (onAff A hV).hom := by
  exact (smoothOfRelativeDimension_isStableUnderBaseChange (n := g)).of_isPullback
    (isGrpPullback_pullback A hV.fromSpec).1 hg

/- English proof (translation)
The claim follows from `letI := resAlg h ⟨_, ReciprocityTheory.ChartRestriction.G.Chart.isGrpPullback_factor (G'' := onAff A hW) hU.fromSpec _ (isGrpPullback_congr (G' := onAff A hW) (fromSpec_res hU hW h).symm (isGrpPullback_pullback A hW.fromSpec)), pullback.lift_fst _ _ _⟩`.
-/
theorem exists_transition {U W : T.Opens} (hU : IsAffineOpen U) (hW : IsAffineOpen W) (h : W ≤ U) :
    letI := resAlg h
    ∃ φ : (onAff A hW).left ⟶ (onAff A hU).left,
      IsGrpPullback (onAff A hW) (onAff A hU) (spMap (algebraMap Γ(T, U) Γ(T, W))) φ ∧
      φ ≫ pullback.fst A.hom hU.fromSpec = pullback.fst A.hom hW.fromSpec :=
  letI := resAlg h
  ⟨_, ReciprocityTheory.ChartRestriction.G.Chart.isGrpPullback_factor (G'' := onAff A hW) hU.fromSpec _
    (isGrpPullback_congr (G' := onAff A hW) (fromSpec_res hU hW h).symm
      (isGrpPullback_pullback A hW.fromSpec)),
    pullback.lift_fst _ _ _⟩

def bcBasis {R R' : Type} {M M' : Type*} [CommRing R] [CommRing R'] [Algebra R R'] [AddCommGroup M]
    [Module R M] [AddCommGroup M'] [Module R' M'] (f : M →ₛₗ[algebraMap R R'] M')
    (hf : Function.Bijective (liftSemi f)) {ι : Type} (b : Module.Basis ι R M) :
    Module.Basis ι R' M' :=
  (Algebra.TensorProduct.basis R' b).map (LinearEquiv.ofBijective _ hf)

/- English proof (translation)
Rewrite using `[bcBasis, Module.Basis.map_apply, Algebra.TensorProduct.basis_apply, LinearEquiv.ofBijective_apply, liftSemi_tmul, one_smul]`.
-/
theorem bcBasis_apply {R R' : Type} {M M' : Type*} [CommRing R] [CommRing R'] [Algebra R R'] [AddCommGroup M]
    [Module R M] [AddCommGroup M'] [Module R' M'] (f : M →ₛₗ[algebraMap R R'] M')
    (hf : Function.Bijective (liftSemi f)) {ι : Type} (b : Module.Basis ι R M) (i : ι) :
    bcBasis f hf b i = f (b i) := by
  rw [bcBasis, Module.Basis.map_apply, Algebra.TensorProduct.basis_apply,
    LinearEquiv.ofBijective_apply, liftSemi_tmul, one_smul]

end GlobalTheory.DeRhamSheaf.VB

namespace GlobalTheory.DeRhamSheaf.VB

open GlobalTheory.Published.AbelianDeRham (bcMor)

/- English proof (translation)
Introduce `hP T A _ g hA hg H hH`. Take `⟨E, hE⟩` from `hH`. Establish `hBC` using `hP.2.2.1`. Establish `frame : ∀ (D : T.Opens) (hD : IsAffineOpen D) (c : Module.Basis (Fin (2 * g)) Γ(T, D) (primDR (onAff A hD))), GlobalTheory.VB.IsFrame (F` using `H) (U := D) fun i => (E D hD).symm (c i) := by`. Introduce `D hD c`.

Use `GlobalTheory.VB.isFrame_of_forall_exists fun V h y hy => ?_` and prove the remaining obligations. Take `⟨W, hW, hyW, hle⟩` from `GlobalTheory.QCoh.exists_affine_mem_le y hy`. Use `⟨W, hle, hyW, ?_⟩` and prove the remaining obligations. Use `letI := resAlg (hle.trans h)`. Take `⟨φ, hφ, hφ'⟩` from `exists_transition A hD hW (hle.trans h)`.

Establish `hbc : (bcMor hφ).IsBC` using `(hBC _ (onAff A hD) g (isAbelianScheme_onAff A hA hD) (smooth_onAff A hg hD) _ (onAff A hW) φ hφ).1`. Set `d` to `(bcBasis (bcMor hφ).pull hbc c).map (E W hW).symm`. Establish `hd (i : Fin (2 * g)) : d i = GlobalTheory.Twist.resM H (hle.trans h) ((E D hD).symm (c i))`. Apply `(E W hW).injective` to reduce the goal to its premises. Rewrite using `[hE D W hD hW (hle.trans h) φ hφ hφ', LinearEquiv.apply_symm_apply]`.

Simplify using `only [d, Module.Basis.map_apply, LinearEquiv.apply_symm_apply]`. Conclude with `bcBasis_apply _ hbc c i`. Establish `hl : Fintype.linearCombination Γ(T, W) (fun i => GlobalTheory.Twist.resM H (hle.trans h) ((E D hD).symm (c i))) = d.equivFun.symm.toLinearMap`. Use `LinearMap.ext fun a => ?_` and prove the remaining obligations. Rewrite using `[Fintype.linearCombination_apply, LinearEquiv.coe_coe, Module.Basis.equivFun_symm_apply]`.

Simplify using `only [hd]`. Rewrite using `[hl]`. Conclude with `d.equivFun.symm.bijective`. Introduce `x`. Take `⟨V, hV, hxV, -⟩` from `GlobalTheory.QCoh.exists_affine_mem_le (U := ⊤) x trivial`.

Take `⟨hfin, hproj, hrk⟩` from `GlobalTheory.Published.AbelianDeRham.Free.prim hP.1 (isAbelianScheme_onAff A hA hV) (smooth_onAff A hg hV)`. Take `⟨y, rfl⟩ : ∃ y : V, y.1 = x` from `⟨⟨x, hxV⟩, rfl⟩`. Use `set p := hV.primeIdealOf y`. Establish `: Module.FinitePresentation Γ(T, V) (primDR (onAff A hV))` using `Module.finitePresentation_of_projective _ _`. Use `haveI : Module.Free (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl (primDR (onAff A hV))) := Module.mem_freeLocus.1 (by rw [Module.freeLocus_eq_univ]; trivial)`.

Establish `hr : Module.finrank (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl (primDR (onAff A hV))) = 2 * g` using `hrk p`. Take `⟨r, hr', b', -⟩` from `Module.FinitePresentation.exists_basis_localizedModule_powers p.asIdeal.primeCompl (LocalizedModule.mkLinearMap p.asIdeal.primeCompl (primDR (onAff A hV))) (Localization.AtPrime p.asIdeal) (Module.finBasisOfFinrankEq _ _ hr)`. Establish `hD` using `hV.basicOpen r`. Use `letI := resAlg (T.basicOpen_le r)`. Take `⟨φ, hφ, -⟩` from `exists_transition A hV hD (T.basicOpen_le r)`.

Establish `hbc : (bcMor hφ).IsBC` using `(hBC _ (onAff A hV) g (isAbelianScheme_onAff A hA hV) (smooth_onAff A hg hV) _ (onAff A hD) φ hφ).1`. Use `letI : Module Γ(T, V) (primDR (onAff A hD)) := Module.compHom _ (algebraMap Γ(T, V) Γ(T, T.basicOpen r))`. Use `haveI : IsScalarTower Γ(T, V) Γ(T, T.basicOpen r) (primDR (onAff A hD)) := ⟨fun a b m => by show (a • b) • m = algebraMap Γ(T, V) Γ(T, T.basicOpen r) a • b • m`. Rewrite using `[Algebra.smul_def, mul_smul]⟩`. Set `f : primDR (onAff A hV) →ₗ[Γ(T, V)] primDR (onAff A hD)` to `{ toFun := (bcMor hφ).pull map_add' := map_add _ map_smul' := fun a m => (bcMor hφ).pull.map_smulₛₗ a m }`.

Establish `hf : IsBaseChange Γ(T, T.basicOpen r) f` using `IsBaseChange.of_equiv (LinearEquiv.ofBijective _ hbc) fun m => by`. Conclude with `(liftSemi_tmul _ 1 m).trans (one_smul _ _)`. Use `haveI := hV.isLocalization_basicOpen r`. Use `haveI : IsLocalizedModule (Submonoid.powers r) f := (isLocalizedModule_iff_isBaseChange (Submonoid.powers r) Γ(T, T.basicOpen r) f).2 hf`. Take `⟨c⟩` from `GlobalTheory.VB.nonempty_basis_of_localizedModule Γ(T, T.basicOpen r) (.powers r) f b'`.

Conclude with `⟨T.basicOpen r, _, (GlobalTheory.QCoh.mem_primeCompl_primeIdealOf_iff hV y r).1 hr', frame _ hD c⟩`.
-/
theorem isVB_of_isDeRhamSheaf : GlobalTheory.Published.AbelianDeRham → ∀ (T : Scheme.{0}) (A : Over T) [GrpObj A]
    (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ H : T.Modules,
      GlobalTheory.DeRhamSheaf.IsDeRhamSheaf A H → GlobalTheory.VB.IsVB H (2 * g) := by
  intro hP T A _ g hA hg H hH
  obtain ⟨E, hE⟩ := hH
  have hBC := hP.2.2.1

  have frame : ∀ (D : T.Opens) (hD : IsAffineOpen D)
      (c : Module.Basis (Fin (2 * g)) Γ(T, D) (primDR (onAff A hD))),
      GlobalTheory.VB.IsFrame (F := H) (U := D) fun i => (E D hD).symm (c i) := by
    intro D hD c
    refine GlobalTheory.VB.isFrame_of_forall_exists fun V h y hy => ?_
    obtain ⟨W, hW, hyW, hle⟩ := GlobalTheory.QCoh.exists_affine_mem_le y hy
    refine ⟨W, hle, hyW, ?_⟩
    letI := resAlg (hle.trans h)
    obtain ⟨φ, hφ, hφ'⟩ := exists_transition A hD hW (hle.trans h)
    have hbc : (bcMor hφ).IsBC :=
      (hBC _ (onAff A hD) g (isAbelianScheme_onAff A hA hD) (smooth_onAff A hg hD) _
        (onAff A hW) φ hφ).1
    let d := (bcBasis (bcMor hφ).pull hbc c).map (E W hW).symm
    have hd (i : Fin (2 * g)) : d i = GlobalTheory.Twist.resM H (hle.trans h) ((E D hD).symm (c i)) := by
      apply (E W hW).injective
      rw [hE D W hD hW (hle.trans h) φ hφ hφ', LinearEquiv.apply_symm_apply]
      simp only [d, Module.Basis.map_apply, LinearEquiv.apply_symm_apply]
      exact bcBasis_apply _ hbc c i
    have hl : Fintype.linearCombination Γ(T, W)
        (fun i => GlobalTheory.Twist.resM H (hle.trans h) ((E D hD).symm (c i))) =
          d.equivFun.symm.toLinearMap := by
      refine LinearMap.ext fun a => ?_
      rw [Fintype.linearCombination_apply, LinearEquiv.coe_coe, Module.Basis.equivFun_symm_apply]
      simp only [hd]
    rw [hl]
    exact d.equivFun.symm.bijective
  intro x
  obtain ⟨V, hV, hxV, -⟩ := GlobalTheory.QCoh.exists_affine_mem_le (U := ⊤) x trivial
  obtain ⟨hfin, hproj, hrk⟩ :=
    GlobalTheory.Published.AbelianDeRham.Free.prim hP.1 (isAbelianScheme_onAff A hA hV) (smooth_onAff A hg hV)
  obtain ⟨y, rfl⟩ : ∃ y : V, y.1 = x := ⟨⟨x, hxV⟩, rfl⟩
  set p := hV.primeIdealOf y
  have : Module.FinitePresentation Γ(T, V) (primDR (onAff A hV)) :=
    Module.finitePresentation_of_projective _ _
  haveI : Module.Free (Localization.AtPrime p.asIdeal)
      (LocalizedModule p.asIdeal.primeCompl (primDR (onAff A hV))) :=
    Module.mem_freeLocus.1 (by rw [Module.freeLocus_eq_univ]; trivial)
  have hr : Module.finrank (Localization.AtPrime p.asIdeal)
      (LocalizedModule p.asIdeal.primeCompl (primDR (onAff A hV))) = 2 * g := hrk p
  obtain ⟨r, hr', b', -⟩ := Module.FinitePresentation.exists_basis_localizedModule_powers
    p.asIdeal.primeCompl (LocalizedModule.mkLinearMap p.asIdeal.primeCompl (primDR (onAff A hV)))
    (Localization.AtPrime p.asIdeal) (Module.finBasisOfFinrankEq _ _ hr)
  have hD := hV.basicOpen r
  letI := resAlg (T.basicOpen_le r)
  obtain ⟨φ, hφ, -⟩ := exists_transition A hV hD (T.basicOpen_le r)
  have hbc : (bcMor hφ).IsBC :=
    (hBC _ (onAff A hV) g (isAbelianScheme_onAff A hA hV) (smooth_onAff A hg hV) _
      (onAff A hD) φ hφ).1
  letI : Module Γ(T, V) (primDR (onAff A hD)) :=
    Module.compHom _ (algebraMap Γ(T, V) Γ(T, T.basicOpen r))
  haveI : IsScalarTower Γ(T, V) Γ(T, T.basicOpen r) (primDR (onAff A hD)) :=
    ⟨fun a b m => by
      show (a • b) • m = algebraMap Γ(T, V) Γ(T, T.basicOpen r) a • b • m
      rw [Algebra.smul_def, mul_smul]⟩
  let f : primDR (onAff A hV) →ₗ[Γ(T, V)] primDR (onAff A hD) :=
    { toFun := (bcMor hφ).pull
      map_add' := map_add _
      map_smul' := fun a m => (bcMor hφ).pull.map_smulₛₗ a m }
  have hf : IsBaseChange Γ(T, T.basicOpen r) f :=
    IsBaseChange.of_equiv (LinearEquiv.ofBijective _ hbc) fun m => by
      exact (liftSemi_tmul _ 1 m).trans (one_smul _ _)
  haveI := hV.isLocalization_basicOpen r
  haveI : IsLocalizedModule (Submonoid.powers r) f :=
    (isLocalizedModule_iff_isBaseChange (Submonoid.powers r) Γ(T, T.basicOpen r) f).2 hf
  obtain ⟨c⟩ := GlobalTheory.VB.nonempty_basis_of_localizedModule Γ(T, T.basicOpen r) (.powers r) f b'
  exact ⟨T.basicOpen r, _, (GlobalTheory.QCoh.mem_primeCompl_primeIdealOf_iff hV y r).1 hr', frame _ hD c⟩

end GlobalTheory.DeRhamSheaf.VB
