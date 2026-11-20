import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegPull
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDvrExtensionClosedPoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PhiDivisorPullback
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTamePolyhedralFan
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonomialFormOnChartRing
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToricChartsGlobalConditions
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDvrLiftFiniteCoverStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SiegelPullbackDvrExtensionStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DegenerationDataNormalRingStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RigidifiedSymmetricLineBundleGroupPullbackStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrincipalPolarizationOfMumfordBundleSiegelFibreStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniformisationBaseChangeWithCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationLineBundleUnifIsoStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnifPolarizationSquareIsoStatement
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory.LN GlobalTheory
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.SiegLoc.TraitOrd

section Specialise

variable {o : Type} [CommRing o] {ζ : o} {g n : ℕ} {F : SFam g n ζ} {S : Scheme.{0}} {j : F.X ⟶ S} [IsOpenImmersion j]
  {G : Over S} [GrpObj G] {e : F.univ.A.left ⟶ G.left}

/- English proof (translation)
Take `⟨bc, mbc, -⟩` from `grpPullback_iso h (isGrpPullback_pullback G f)`. Conclude with `isSemiAbelian_of_grpIso bc (IsSemiAbelian.pullback f G hG)`.
-/
theorem isSemiAbelian_of_isGrpPullback {T : Scheme.{0}} {f : T ⟶ S} {G' : Over T} [GrpObj G'] [IsCommMonObj G']
    {π : G'.left ⟶ G.left} (h : IsGrpPullback G' G f π) (hG : IsSemiAbelian G) : IsSemiAbelian G' := by
  obtain ⟨bc, mbc, -⟩ := grpPullback_iso h (isGrpPullback_pullback G f)
  exact isSemiAbelian_of_grpIso bc (IsSemiAbelian.pullback f G hG)

/- English proof (translation)
Substitute `hξ` using the available equality. Establish `w : π'' ≫ G.hom = (G''.hom ≫ spMap ψ) ≫ ξ` using `by rw [Category.assoc]; exact h''.1.w`. Take `⟨β, hβ₁, hβ₂⟩ : ∃ β : G''.left ⟶ G'.left, β ≫ π = π'' ∧ β ≫ G'.hom = G''.hom ≫ spMap ψ` from `⟨hU.1.1.lift _ _ w, hU.1.1.lift_fst _ _ _, hU.1.1.lift_snd _ _ _⟩`. Establish `gβ : IsGrpPullback G'' G' (spMap ψ) β` using `hU.1.cancel (h''.congr rfl hβ₁.symm) hβ₂`. Establish `gB` using `(isGrpPullback_pullback G'' (jK V)).comp gβ`.

Establish `hΛ` using `GlobalTheory.T.degeneration_data_normal_ring o ζ g n F S j G e he R hR.1 hR.2.1 _ ξ G' π D A U hU _ (jK V ≫ spMap ψ) y _ _ α α₂ (hy.trans (Category.assoc _ _ _).symm) gB hα (by rw [hαe, Category.assoc, hβ₁]) hα₂`. Take `⟨hr, hs⟩` from `GlobalTheory.T.rigidified_symmetric_lineBundle_groupPullback _ _ _ G' _ _ gB U.LG U.symG U.symG_gen`. Take `⟨ha, hamp, hkt⟩` from `GlobalTheory.T.principalPolarization_of_mumfordBundle_siegelFibre o ζ g n F _ y _ α α₂ hα hα₂ _ (pull_isLB U.LG.isLB _) hr hs hΛ`. Take `⟨D', A', U', ε, hL, hc⟩` from `GlobalTheory.T.exists_uniformisation_baseChange_with_coordinates R V hR hV ψ hψ G' (isSemiAbelian_of_isGrpPullback hU.1 hG) D A U W hW hψW hk G'' β gβ ha hr hs hamp hkt`. Conclude with `⟨D', A', U', ε, _, pull_isLB U.LG.isLB _, hL, hΛ, hc⟩`.
-/
theorem exists_pull (hG : IsSemiAbelian G) (he : IsGrpPullback F.univ.A G j e) {R V : Type} [CommRing R] [IsDomain R]
    [IsLocalRing R] [CommRing V] [IsDomain V] [IsLocalRing V] (hR : IsCN R) (hV : IsCN V) (ψ : R →+* V) (hψ : IsLocalHom ψ)
    {ξ : Sp R ⟶ S} {G' : Over (Sp R)} [GrpObj G'] [IsCommMonObj G'] {π : G'.left ⟶ G.left} {D : DegData R (maximalIdeal R)}
    {A : PolAV (Sp (FractionRing R))} {U : Unif (maximalIdeal R) D A G'} (hU : IsUnifOf F j e ξ π U) (W : Set (Sp R))
    (hW : IsOpen W) (hψW : ∀ y, PsiUnitOn D.toPre y W)
    (hk : (⟨RingHom.ker ψ, RingHom.ker_isPrime ψ⟩ : PrimeSpectrum R) ∈ W)
    (G'' : Over (Sp V)) [GrpObj G''] [IsCommMonObj G''] (π'' : G''.left ⟶ G.left) (ξ'' : Sp V ⟶ S) (hξ : ξ'' = spMap ψ ≫ ξ)
    (h'' : IsGrpPullback G'' G ξ'' π'') (y : Sp (FractionRing V) ⟶ F.X) (hy : y ≫ j = jK V ≫ ξ'')
    (α : ((Over.pullback (jK V)).obj G'').left ⟶ F.univ.A.left)
    (α₂ : (G2 ((Over.pullback (jK V)).obj G'')).left ⟶ (G2 F.univ.A).left)
    (hα : IsGrpPullback ((Over.pullback (jK V)).obj G'') F.univ.A y α) (hαe : α ≫ e = pullback.fst G''.hom (jK V) ≫ π'')
    (hα₂ : IsSquare α α₂) :
    ∃ (D' : DegData V (maximalIdeal V)) (A' : PolAV (Sp (FractionRing V))) (U' : Unif (maximalIdeal V) D' A' G'')
      (ε : D'.toPre.X ≃+ D.toPre.X) (L : LB ((Over.pullback (jK V)).obj G'').left), L.IsLB ∧
      LBIso L (U'.LG.L.pull (pullback.fst G''.hom (jK V))) ∧
      LBIso (abelian₂ ((Over.pullback (jK V)).obj G'') L) (F.univ.P.pull α₂) ∧
      ∀ y r, PsiCoord D.toPre (ε y) r → ∃ u : Vˣ, PsiCoord D'.toPre y (u * ψ r) := by
  subst hξ
  have w : π'' ≫ G.hom = (G''.hom ≫ spMap ψ) ≫ ξ := by rw [Category.assoc]; exact h''.1.w
  obtain ⟨β, hβ₁, hβ₂⟩ : ∃ β : G''.left ⟶ G'.left, β ≫ π = π'' ∧ β ≫ G'.hom = G''.hom ≫ spMap ψ :=
    ⟨hU.1.1.lift _ _ w, hU.1.1.lift_fst _ _ _, hU.1.1.lift_snd _ _ _⟩
  have gβ : IsGrpPullback G'' G' (spMap ψ) β := hU.1.cancel (h''.congr rfl hβ₁.symm) hβ₂
  have gB := (isGrpPullback_pullback G'' (jK V)).comp gβ
  have hΛ := GlobalTheory.T.degeneration_data_normal_ring o ζ g n F S j G e he R hR.1 hR.2.1 _ ξ G' π D A U hU _ (jK V ≫ spMap ψ) y _ _ α α₂
    (hy.trans (Category.assoc _ _ _).symm) gB hα (by rw [hαe, Category.assoc, hβ₁]) hα₂
  obtain ⟨hr, hs⟩ := GlobalTheory.T.rigidified_symmetric_lineBundle_groupPullback _ _ _ G' _ _ gB U.LG U.symG U.symG_gen
  obtain ⟨ha, hamp, hkt⟩ := GlobalTheory.T.principalPolarization_of_mumfordBundle_siegelFibre o ζ g n F _ y _ α α₂ hα hα₂ _ (pull_isLB U.LG.isLB _) hr hs hΛ
  obtain ⟨D', A', U', ε, hL, hc⟩ := GlobalTheory.T.exists_uniformisation_baseChange_with_coordinates R V hR hV ψ hψ G' (isSemiAbelian_of_isGrpPullback hU.1 hG) D A U W hW hψW hk
    G'' β gβ ha hr hs hamp hkt
  exact ⟨D', A', U', ε, _, pull_isLB U.LG.isLB _, hL, hΛ, hc⟩

/- English proof (translation)
Establish `hy` using `IsOpenImmersion.lift_fac j (jK V ≫ ξ'') hr`. Use `set y := IsOpenImmersion.lift j (jK V ≫ ξ'') hr`. Establish `gB` using `((isGrpPullback_pullback G'' (jK V)).comp h'').congr hy.symm rfl`. Use `set B := (Over.pullback (jK V)).obj G''`. Establish `w : (pullback.fst G''.hom (jK V) ≫ π'') ≫ G.hom = (B.hom ≫ y) ≫ j` using `by rw [Category.assoc]; exact gB.1.w`.

Take `⟨α, h₁, h₂⟩ : ∃ α : B.left ⟶ F.univ.A.left, α ≫ e = pullback.fst G''.hom (jK V) ≫ π'' ∧ α ≫ F.univ.A.hom = B.hom ≫ y` from `⟨he.1.lift _ _ w, he.1.lift_fst _ _ _, he.1.lift_snd _ _ _⟩`. Use `⟨y, α, pullback.map B.hom B.hom F.univ.A.hom F.univ.A.hom α α y h₂.symm h₂.symm, hy, he.cancel (gB.congr rfl h₁.symm) h₂, h₁, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩` and prove the remaining obligations.
-/
theorem exists_generic (he : IsGrpPullback F.univ.A G j e) {V : Type} [CommRing V] [IsDomain V]
    (G'' : Over (Sp V)) [GrpObj G''] (π'' : G''.left ⟶ G.left) (ξ'' : Sp V ⟶ S)
    (h'' : IsGrpPullback G'' G ξ'' π'') (hr : Set.range (jK V ≫ ξ'') ⊆ Set.range j) :
    ∃ (y : Sp (FractionRing V) ⟶ F.X) (α : ((Over.pullback (jK V)).obj G'').left ⟶ F.univ.A.left)
      (α₂ : (G2 ((Over.pullback (jK V)).obj G'')).left ⟶ (G2 F.univ.A).left), y ≫ j = jK V ≫ ξ'' ∧
      IsGrpPullback ((Over.pullback (jK V)).obj G'') F.univ.A y α ∧ α ≫ e = pullback.fst G''.hom (jK V) ≫ π'' ∧
      IsSquare α α₂ := by
  have hy := IsOpenImmersion.lift_fac j (jK V ≫ ξ'') hr
  set y := IsOpenImmersion.lift j (jK V ≫ ξ'') hr
  have gB := ((isGrpPullback_pullback G'' (jK V)).comp h'').congr hy.symm rfl
  set B := (Over.pullback (jK V)).obj G''
  have w : (pullback.fst G''.hom (jK V) ≫ π'') ≫ G.hom = (B.hom ≫ y) ≫ j := by rw [Category.assoc]; exact gB.1.w
  obtain ⟨α, h₁, h₂⟩ : ∃ α : B.left ⟶ F.univ.A.left, α ≫ e = pullback.fst G''.hom (jK V) ≫ π'' ∧
      α ≫ F.univ.A.hom = B.hom ≫ y := ⟨he.1.lift _ _ w, he.1.lift_fst _ _ _, he.1.lift_snd _ _ _⟩
  refine ⟨y, α, pullback.map B.hom B.hom F.univ.A.hom F.univ.A.hom α α y h₂.symm h₂.symm, hy,
    he.cancel (gB.congr rfl h₁.symm) h₂, h₁, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

/- English proof (translation)
Set `G''` to `(Over.pullback (spMap ψ₁)).obj G₁`. Establish `h''` using `(isGrpPullback_pullback G₁ (spMap ψ₁)).comp hU₁.1`. Take `⟨y, α, α₂, hy, hα, hαe, hα₂⟩` from `exists_generic he G'' _ _ h'' hr`. Take `⟨E₁, B₁, T₁, ε₁, L₁, l₁, i₁, m₁, c₁⟩` from `exists_pull hG he hR₁ hV ψ₁ hψ₁ hU₁ W₁ hW₁ hψW₁ hk₁ G'' _ _ rfl h'' y hy α α₂ hα hαe hα₂`. Take `⟨E₂, B₂, T₂, ε₂, L₂, l₂, i₂, m₂, c₂⟩` from `exists_pull hG he hR₂ hV ψ₂ hψ₂ hU₂ W₂ hW₂ hψW₂ hk₂ G'' _ _ hc h'' y hy α α₂ hα hαe hα₂`.

Establish `hs` using `isSemiAbelian_of_isGrpPullback h'' hG`. Establish `hΛ : LBIso (abelian₂ _ L₂) (abelian₂ _ L₁)` using `LBIso.trans (DVR.linComb_isLB _ l₂ _ _) (pull_isLB F.univ.isLB _) (DVR.linComb_isLB _ l₁ _ _) m₂ m₁.symm`. Take `⟨ε, hε⟩` from `GlobalTheory.T.unif_polarization_square_iso V hV G'' hs E₂ E₁ B₂ B₁ T₂ T₁ (GlobalTheory.T.polarization_line_bundle_unif_iso V hV G'' hs E₂ E₁ B₂ B₁ T₂ T₁ L₂ L₁ l₂ l₁ i₂ i₁ hΛ)`. Use `⟨(ε₁.symm.trans ε).trans ε₂, fun z r₁ r₂ h₁ h₂ => ?_⟩` and prove the remaining obligations. Take `⟨u₁, k₁⟩` from `c₁ (ε₁.symm z) r₁ (by rwa [AddEquiv.apply_symm_apply])`.

Take `⟨u₂, k₂⟩` from `c₂ (ε (ε₁.symm z)) r₂ h₂`. Use `hε _ _ _ k₂ k₁` as an intermediate fact. Rewrite `this` using `[mul_pow, mul_pow]`. Conclude with `((associated_unit_mul_left _ _ (u₁.isUnit.pow 2)).symm.trans this.symm).trans (associated_unit_mul_left _ _ (u₂.isUnit.pow 2))`.
-/
theorem exists_compare (hG : IsSemiAbelian G) (he : IsGrpPullback F.univ.A G j e) {R₁ R₂ V : Type}
    [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁] [CommRing R₂] [IsDomain R₂] [IsLocalRing R₂]
    [CommRing V] [IsDomain V] [IsLocalRing V] (hR₁ : IsCN R₁) (hR₂ : IsCN R₂) (hV : IsCN V)
    (ψ₁ : R₁ →+* V) (hψ₁ : IsLocalHom ψ₁) (ψ₂ : R₂ →+* V) (hψ₂ : IsLocalHom ψ₂)
    {ξ₁ : Sp R₁ ⟶ S} {G₁ : Over (Sp R₁)} [GrpObj G₁] [IsCommMonObj G₁] {π₁ : G₁.left ⟶ G.left}
    {D₁ : DegData R₁ (maximalIdeal R₁)} {A₁ : PolAV (Sp (FractionRing R₁))} {U₁ : Unif (maximalIdeal R₁) D₁ A₁ G₁}
    (hU₁ : IsUnifOf F j e ξ₁ π₁ U₁) (W₁ : Set (Sp R₁)) (hW₁ : IsOpen W₁) (hψW₁ : ∀ y, PsiUnitOn D₁.toPre y W₁)
    (hk₁ : (⟨RingHom.ker ψ₁, RingHom.ker_isPrime ψ₁⟩ : PrimeSpectrum R₁) ∈ W₁)
    {ξ₂ : Sp R₂ ⟶ S} {G₂ : Over (Sp R₂)} [GrpObj G₂] [IsCommMonObj G₂] {π₂ : G₂.left ⟶ G.left}
    {D₂ : DegData R₂ (maximalIdeal R₂)} {A₂ : PolAV (Sp (FractionRing R₂))} {U₂ : Unif (maximalIdeal R₂) D₂ A₂ G₂}
    (hU₂ : IsUnifOf F j e ξ₂ π₂ U₂) (W₂ : Set (Sp R₂)) (hW₂ : IsOpen W₂) (hψW₂ : ∀ y, PsiUnitOn D₂.toPre y W₂)
    (hk₂ : (⟨RingHom.ker ψ₂, RingHom.ker_isPrime ψ₂⟩ : PrimeSpectrum R₂) ∈ W₂)
    (hc : spMap ψ₁ ≫ ξ₁ = spMap ψ₂ ≫ ξ₂) (hr : Set.range (jK V ≫ spMap ψ₁ ≫ ξ₁) ⊆ Set.range j) :
    ∃ ε : D₁.toPre.X ≃+ D₂.toPre.X, ∀ y r₁ r₂, PsiCoord D₁.toPre y r₁ → PsiCoord D₂.toPre (ε y) r₂ →
      Associated (ψ₁ r₁ ^ 2) (ψ₂ r₂ ^ 2) := by
  let G'' := (Over.pullback (spMap ψ₁)).obj G₁
  have h'' := (isGrpPullback_pullback G₁ (spMap ψ₁)).comp hU₁.1
  obtain ⟨y, α, α₂, hy, hα, hαe, hα₂⟩ := exists_generic he G'' _ _ h'' hr
  obtain ⟨E₁, B₁, T₁, ε₁, L₁, l₁, i₁, m₁, c₁⟩ := exists_pull hG he hR₁ hV ψ₁ hψ₁ hU₁ W₁ hW₁ hψW₁ hk₁ G'' _ _ rfl h'' y hy
    α α₂ hα hαe hα₂
  obtain ⟨E₂, B₂, T₂, ε₂, L₂, l₂, i₂, m₂, c₂⟩ := exists_pull hG he hR₂ hV ψ₂ hψ₂ hU₂ W₂ hW₂ hψW₂ hk₂ G'' _ _ hc h'' y hy
    α α₂ hα hαe hα₂
  have hs := isSemiAbelian_of_isGrpPullback h'' hG
  have hΛ : LBIso (abelian₂ _ L₂) (abelian₂ _ L₁) :=
    LBIso.trans (DVR.linComb_isLB _ l₂ _ _) (pull_isLB F.univ.isLB _) (DVR.linComb_isLB _ l₁ _ _) m₂ m₁.symm
  obtain ⟨ε, hε⟩ := GlobalTheory.T.unif_polarization_square_iso V hV G'' hs E₂ E₁ B₂ B₁ T₂ T₁ (GlobalTheory.T.polarization_line_bundle_unif_iso V hV G'' hs E₂ E₁ B₂ B₁ T₂ T₁ L₂ L₁ l₂ l₁ i₂ i₁ hΛ)
  refine ⟨(ε₁.symm.trans ε).trans ε₂, fun z r₁ r₂ h₁ h₂ => ?_⟩
  obtain ⟨u₁, k₁⟩ := c₁ (ε₁.symm z) r₁ (by rwa [AddEquiv.apply_symm_apply])
  obtain ⟨u₂, k₂⟩ := c₂ (ε (ε₁.symm z)) r₂ h₂
  have := hε _ _ _ k₂ k₁
  rw [mul_pow, mul_pow] at this
  exact ((associated_unit_mul_left _ _ (u₁.isUnit.pow 2)).symm.trans this.symm).trans
    (associated_unit_mul_left _ _ (u₂.isUnit.pow 2))

end Specialise

/- English proof (translation)
Establish `hr' : (r : ℝ) ≠ 0` using `by exact_mod_cast hr`. Set `εZ : X ≃ₗ[ℤ] X'` to `ε.toIntLinearEquiv`. Set `B₂ : LinearMap.BilinForm ℤ X` to `∑ i, ((w i : ℤ) * n) • (γ i).compl₁₂ εZ.toLinearMap εZ.toLinearMap`. Establish `hB₂ : ∀ y z, B₂ y z = ∑ i, (w i : ℤ) * (n * γ i (ε y) (ε z))`. Introduce `y z`.

Simplify using `[B₂, εZ, LinearMap.sum_apply, mul_assoc]`. Establish `hfull : ∀ y z, (r : ℤ) * be y z = ∑ i, (w i : ℤ) * (n * γ i (ε y) (ε z))`. Introduce `y z`. Use `GlobalTheory.GenFan.PhiOrder.eq_of_diag ((r : ℤ) • be) B₂ (fun y z => by simp [hbe y z]) (fun y z => by rw [hB₂, hB₂]; exact Finset.sum_congr rfl fun i _ => by rw [(hγ.mem i).1]) (fun y => by rw [hB₂, ← h y]; simp) y z` as an intermediate fact. Rewrite `this` using `[hB₂]`.

Simplify using `using this`. Establish `hφbe : φ.evalZ be = ∑ i, ((w i : ℝ) / r) * φ.evalZ ((n : ℤ) • γ i)`. Rewrite using `[← hγ.linearOn_smul n (fun i => (w i : ℝ) / r) (fun i => by positivity), ← φ.eval_equiv εZ]`. Unfold `InvFun.evalZ`. Use `congr 1`.

Use function extensionality and compare the values at `y z`. Establish `h` using `congrArg (fun n : ℤ => (n : ℝ)) (hfull y z)`. Move the coercions through the operations in `at h`. Rewrite using `[eq_comm, ← mul_right_inj' hr', Finset.mul_sum, h]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Simplify using `only [εZ, LinearMap.smul_apply, smul_eq_mul, AddEquiv.coe_toIntLinearEquiv]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Rewrite using `[hφbe, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Clear the denominators using the available nonvanishing facts.
-/
theorem mul_evalZ_eq (φ : InvFun ℤ) {X X' : Type} [AddCommGroup X] [Module.Finite ℤ X] [AddCommGroup X'] [Module.Finite ℤ X']
    (ε : X ≃+ X') {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X'} (hγ : IsCone id φ γ) (n : ℕ) (be : LinearMap.BilinForm ℤ X)
    (hbe : ∀ y z, be y z = be z y) {r : ℕ} (hr : r ≠ 0) (w : Fin m → ℕ)
    (h : ∀ y, (r : ℤ) * be y y = ∑ i, (w i : ℤ) * (n * γ i (ε y) (ε y))) :
    r * φ.evalZ be = ∑ i, (w i : ℝ) * φ.evalZ ((n : ℤ) • γ i) := by
  have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast hr
  let εZ : X ≃ₗ[ℤ] X' := ε.toIntLinearEquiv
  let B₂ : LinearMap.BilinForm ℤ X := ∑ i, ((w i : ℤ) * n) • (γ i).compl₁₂ εZ.toLinearMap εZ.toLinearMap
  have hB₂ : ∀ y z, B₂ y z = ∑ i, (w i : ℤ) * (n * γ i (ε y) (ε z)) := by
    intro y z
    simp [B₂, εZ, LinearMap.sum_apply, mul_assoc]
  have hfull : ∀ y z, (r : ℤ) * be y z = ∑ i, (w i : ℤ) * (n * γ i (ε y) (ε z)) := by
    intro y z
    have := GlobalTheory.GenFan.PhiOrder.eq_of_diag ((r : ℤ) • be) B₂ (fun y z => by simp [hbe y z])
      (fun y z => by rw [hB₂, hB₂]; exact Finset.sum_congr rfl fun i _ => by rw [(hγ.mem i).1])
      (fun y => by rw [hB₂, ← h y]; simp) y z
    rw [hB₂] at this
    simpa using this
  have hφbe : φ.evalZ be = ∑ i, ((w i : ℝ) / r) * φ.evalZ ((n : ℤ) • γ i) := by
    rw [← hγ.linearOn_smul n (fun i => (w i : ℝ) / r) (fun i => by positivity), ← φ.eval_equiv εZ]
    unfold InvFun.evalZ
    congr 1
    funext y z
    have h := congrArg (fun n : ℤ => (n : ℝ)) (hfull y z)
    push_cast at h
    rw [eq_comm, ← mul_right_inj' hr', Finset.mul_sum, h]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [εZ, LinearMap.smul_apply, smul_eq_mul, AddEquiv.coe_toIntLinearEquiv]
    push_cast
    field_simp
  rw [hφbe, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  field_simp

/- English proof (translation)
The claim follows from `le_antisymm ((pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit).1 h.dvd) ((pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit).1 h.symm.dvd)`.
-/
theorem eq_of_associated_pow {V : Type} [CommRing V] [IsDomain V] {ϖ : V} (hϖ : Irreducible ϖ) {a b : ℕ}
    (h : Associated (ϖ ^ a) (ϖ ^ b)) : a = b :=
  le_antisymm ((pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit).1 h.dvd) ((pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit).1 h.symm.dvd)

/- English proof (translation)
Take `⟨h₁, h₂, h₃⟩` from `h`. Conclude with `⟨inferInstance, inferInstance, h₂, h₃⟩`.
-/
theorem isCN_of_cdvr {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (h : CDvr V) : IsCN V := by
  obtain ⟨h₁, h₂, h₃⟩ := h
  exact ⟨inferInstance, inferInstance, h₂, h₃⟩

open GlobalTheory.TraitChartForm in

/- English proof (translation)
Introduce `E _ _ _ H D l Xo c n R _ b ω φ φs F S s j _ G _ e BD d N κ C π h _ _ _ _ _ hag hded _ _ hS _ hP`. Introduce `W _ _ _ hW ϖ hϖ χ t mχ P hr be hbe hmon`. Take `⟨-, -, -, -, hG, -, he, -, -, hch, -⟩` from `hS`. Take `⟨A, _, _, bA, ξ, m, τ, A', _, _, _, ρ, r, G', _, _, π', Dg, B, U, γ, a, ⟨hAc, -, hx, hEt, hFU⟩, ⟨-, -, hj⟩, ⟨hA', hA0, hρ, hρf, -, hrt⟩, ⟨hU, hX, hγ, hmonC⟩, ha, hid⟩` from `hch ((χ ≫ π) (closedPoint W))`. Take `⟨_, hAi⟩` from `GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing A`.

Establish `hCN : IsCN A` using `⟨inferInstance, hAi, hAc, RingHom.charZero ρ⟩`. Establish `hCN' : IsCN A'` using `⟨hA'.1, hA'.2.2.1, hA'.2.2.2, hA0⟩`. Take `⟨V₀, _, _, _, f₀, ψ₀, hV₀, hf₀, hf₀l, hψ₀l, -, hc₀⟩` from `GlobalTheory.TraitLift.exists_lift S A ξ hCN hEt hFU W hW ϖ hϖ (χ ≫ π) hx.symm`. Take `⟨V, _, _, _, f₁, ψ, hV, hf₁, hf₁l, hψl, hψ⟩` from `GlobalTheory.T.exists_dvr_lift_finite_cover A A' ρ hρ hρf V₀ hV₀ ψ₀ hψ₀l`. Take `⟨πP, hUP⟩` from `GlobalTheory.T.siegel_pullback_dvr_extension E H D l Xo c _ n R ω F S s j G e κ C π hded hP W _ χ t mχ P hr`.

Set `f` to `f₁.comp f₀`. Establish `hf : Function.Injective f` using `hf₁.comp hf₀`. Establish `hfl : IsLocalHom f` using `inferInstance`. Establish `hc : spMap f ≫ χ ≫ π = spMap ψ ≫ spMap ρ ≫ ξ`. Rewrite using `[spMap_comp, Category.assoc, hc₀, ← Category.assoc, ← spMap_comp, ← hψ, spMap_comp, Category.assoc]`.

Use `hW.1` as an intermediate fact. Use `hV.1` as an intermediate fact. Take `⟨ϖ', hϖ'⟩` from `IsDiscreteValuationRing.exists_irreducible V`. Establish `hfϖ : f ϖ ≠ 0` using `fun h => hϖ.ne_zero (hf (h.trans (map_zero f).symm))`. Take `⟨k, u, hu⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hfϖ hϖ'`.

Establish `hk : k ≠ 0`. Introduce and unpack `rfl`. Rewrite `hu` using `[pow_zero, mul_one]`. Conclude with `hϖ.not_isUnit (isUnit_of_map_unit f ϖ (hu ▸ u.isUnit))`. Establish `hfbot : spMap f (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum V) = (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum W)` using `PrimeSpectrum.ext (Ideal.comap_bot_of_injective f hf)`.

Establish `hgen : (spMap f ≫ χ ≫ π) (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum V) ∈ Set.range j`. Take `⟨-, y, -, -, hy, -⟩` from `hUP`. Set `p : Sp (FractionRing W)` to `(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing W))`. Use `⟨y p, ?_⟩` and prove the remaining obligations. Rewrite using `[← Scheme.Hom.comp_apply, hy, Scheme.Hom.comp_apply, jK_apply_eq_bot W p, ← hfbot]`.

Both sides reduce to the same expression. Establish `hrV : Set.range (jK V ≫ spMap f ≫ χ ≫ π) ⊆ Set.range j`. Introduce and unpack `_ ⟨p, rfl⟩`. Rewrite using `[Scheme.Hom.comp_apply, jK_apply_eq_bot V p]`. Conclude with `hgen`.

Establish `hτ : ∀ i, ψ (ρ (τ i)) = ψ (r i) ^ 2` using `fun i => by rw [← hrt, map_pow]`. Establish `hψr : ∀ i, ψ (r i) ≠ 0`. Rewrite `hgen` using `[hc]`. Establish `hp : ∏ i, τ i ∉ ((spMap ψ ≫ spMap ρ) (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum V)).asIdeal` using `(hj _).1 hgen`. Establish `hp' : ψ (ρ (∏ i, τ i)) ≠ 0` using `fun h => hp (by show ψ (ρ (∏ i, τ i)) ∈ (⊥ : Ideal V)`.

Rewrite using `[h]`. Conclude with `Ideal.zero_mem _)`. Rewrite `hp'` using `[map_prod, map_prod]`. Conclude with `fun i h => Finset.prod_ne_zero_iff.1 hp' i (Finset.mem_univ i) (by rw [hτ, h]; simp)`. Use `choose nn vv hvv using fun i => IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (hψr i) hϖ'`.

Take `⟨ε, hε⟩` from `exists_compare hG he (isCN_of_cdvr hW) hCN' (isCN_of_cdvr hV) f hfl ψ hψl hUP {p | ϖ ∉ p.asIdeal} (PrimeSpectrum.isOpen_basicOpen (a := ϖ)) (fun y => hmon.psiUnitOn y fun p hp => by simpa using hp) (fun h => hfϖ (RingHom.mem_ker.1 h)) hU {p | ∏ i, r i ∉ p.asIdeal} (PrimeSpectrum. …`. Establish `h' : ψ (∏ i, r i) = 0` using `RingHom.mem_ker.1 h`. Rewrite `h'` using `[map_prod]`. Conclude with `Finset.prod_ne_zero_iff.2 (fun i _ => hψr i) h') hc hrV`. Establish `hprod : ∀ x : Fin m → ℕ, Associated (∏ i, ψ (r i) ^ x i) (ϖ' ^ ∑ i, nn i * x i)` using `fun x => by`.

Rewrite using `[← Finset.prod_pow_eq_pow_sum]`. Use `Associated.prod _ _ _ fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hvv, pow_mul]`. Conclude with `(associated_unit_mul_left _ _ (vv i).isUnit).pow_pow`. Establish `hpow : ∀ x : ℕ, Associated (f ϖ ^ x) (ϖ' ^ (k * x))` using `fun x => by`.

Rewrite using `[hu, pow_mul]`. Conclude with `(associated_unit_mul_left _ _ u.isUnit).pow_pow`. Establish `hform : ∀ y, (k : ℤ) * be y y = ∑ i, ((2 * nn i : ℕ) : ℤ) * (n * γ i (ε y) (ε y))` using `fun y => by`. Take `⟨u₁, n₁, hn₁, c₁⟩` from `hmon y`. Take `⟨u₂, n₂, hn₂, c₂⟩` from `hmonC (ε y)`.

Establish `a₁ : Associated (f (u₁ * ∏ i, ![ϖ] i ^ n₁ i)) (ϖ' ^ (k * n₁ 0))`. Rewrite using `[Fin.prod_univ_one, Matrix.cons_val_zero, map_mul, map_pow]`. Conclude with `(associated_unit_mul_left _ _ (u₁.isUnit.map f)).trans (hpow _)`. Establish `a₂ : Associated (ψ (u₂ * ∏ i, r i ^ n₂ i)) (ϖ' ^ ∑ i, nn i * n₂ i)`. Rewrite using `[map_mul, map_prod]`.

Repeatedly rewrite using `[map_pow]`. Conclude with `(associated_unit_mul_left _ _ (u₂.isUnit.map ψ)).trans (hprod _)`. Establish `a₃` using `(a₁.pow_pow (n := 2)).symm.trans ((hε y _ _ c₁ c₂).trans (a₂.pow_pow (n := 2)))`. Rewrite `a₃` using `[← pow_mul, ← pow_mul]`. Establish `e₁ : k * n₁ 0 = ∑ i, nn i * n₂ i` using `by have := eq_of_associated_pow hϖ' a₃; omega`.

Establish `h0 : be y y = 2 * n₁ 0` using `by simpa using hn₁ 0`. Establish `h1 : ∀ i, (n : ℤ) * γ i (ε y) (ε y) = n₂ i` using `fun i => by`. Use `hn₂ i` as an intermediate fact. Simplify using `only [LinearMap.smul_apply, smul_eq_mul] at this`. Combine the linear equalities and inequalities to obtain the conclusion.

Repeatedly rewrite using `[h1]`. Rewrite using `[h0]`. Establish `e₂` using `congrArg (fun x : ℕ => (x : ℤ)) e₁`. Move the coercions through the operations in `at e₂ ⊢`. Repeatedly rewrite using `[mul_assoc]`.

Rewrite using `[← Finset.mul_sum, ← e₂]`. Expand and normalize the polynomial expressions, which then agree. Establish `hval` using `mul_evalZ_eq φ ε hγ n be hbe.1 hk _ hform`. Establish `hmapf : (idlAlong BD.idealSheaf (χ ≫ π)).map f = Ideal.span {ϖ' ^ ∑ i, nn i * (2 * a i)}`. Rewrite using `[← GlobalTheory.TraitOrder.idlAlong_comp, hc, GlobalTheory.TraitOrder.idlAlong_comp, GlobalTheory.TraitOrder.idlAlong_comp, hid, Ideal.map_span, Set.image_singleton, Ideal.map_span, Set.image_singleton, map_prod, map_prod]`.

Repeatedly rewrite using `[map_pow, hτ, ← pow_mul]`. Conclude with `Ideal.span_singleton_eq_span_singleton.2 (hprod _)`. Establish `hne : idlAlong BD.idealSheaf (χ ≫ π) ≠ ⊥`. Introduce `h`. Rewrite `hmapf` using `[h, Ideal.map_bot]`.

Conclude with `pow_ne_zero _ hϖ'.ne_zero (Ideal.span_singleton_eq_bot.1 hmapf.symm)`. Take `⟨n₀, hn₀⟩` from `IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hne hϖ`. Establish `hrN : k * n₀ = ∑ i, nn i * (2 * a i)`. Rewrite `hmapf` using `[hn₀, Ideal.map_span, Set.image_singleton, map_pow]`. Conclude with `eq_of_associated_pow hϖ' ((hpow _).symm.trans (Ideal.span_singleton_eq_span_singleton.1 hmapf))`.

Use `⟨n₀, ?_, (GlobalTheory.PolOrdPull.idlAlong_pull BD π h χ).trans hn₀⟩` and prove the remaining obligations. Establish `hres : (resInt (𝓞 E) φs).evalZ be = φs.evalZ be`. Take `⟨q, x, hx⟩` from `Module.Finite.exists_fin' (𝓞 E) P.D.toPre.X`. Unfold `InvFun.evalZ`. Rewrite using `[InvFun.eval_eq _ hx]`.

Conclude with `φs.eval_comp (r := x.restrictScalars ℤ) hx fun a b => (be a b : ℝ)`. Establish `hagr : φs.evalZ be = φ.evalZ be`. Rewrite using `[← evalR_toReal, ← evalR_toReal]`. Use `hag _ (ε.toIntLinearEquiv.finrank_eq.trans_le hX) _ (TameZ.toReal_mem_psdCone_int (mem_balForms_int.2 hbe.1) fun y => by simpa using hmon.nonneg 0 y)` and prove the remaining obligations. Establish `hk' : (k : ℝ) ≠ 0` using `by exact_mod_cast hk`.

Rewrite using `[GlobalTheory.GenFan.PhiOrder.comb_evalZ, hres, hagr, ← mul_right_inj' hk', mul_left_comm, hval, Finset.mul_sum]`. Establish `e₃` using `congrArg (fun x : ℕ => (x : ℝ)) hrN`. Move the coercions through the operations in `at e₃ ⊢`. Rewrite using `[e₃]`. Conclude with `Finset.sum_congr rfl fun i _ => by rw [ha]; ring`.
-/
theorem isPhiDiv_pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (n : ℕ) (R : Type) [CommRing R] (b : 𝓞 c.F →+* R) (ω : R →+* c.F) (φ φs : InvFun ℤ) (F : SFam (Module.finrank ℚ E / 2 * (D.p + D.q)) n (zetaAway n)) (S : Scheme.{0}) (s : S ⟶ Sp (cycAway n)) (j : F.X ⟶ S) [IsOpenImmersion j] (G : Over S) [GrpObj G] (e : F.univ.A.left ⟶ G.left) (BD : EffCartierData S) (d N : ℕ) (κ : cycAway n →+* R) (C : Model Xo c ω) (π : C.X ⟶ S) (h : BD.KeepsRegular π), 1 ≤ D.p + D.q → 3 ≤ n → Odd n → n ∣ l.M → IsPolFan id (Module.finrank ℚ E / 2 * (D.p + D.q)) φ → AgreesPsd (Module.finrank ℚ E / 2 * (D.p + D.q)) φs φ → IsDedFrac ω → ω.comp b = algebraMap (𝓞 c.F) c.F → @IsLocalization.Away (𝓞 c.F) _ (n : 𝓞 c.F) R _ b.toAlgebra → SiegData (Module.finrank ℚ E / 2 * (D.p + D.q)) φ n F S s j G e BD d N → (∀ x, ((ω (κ x) : c.F) : ℂ) = (x : ℂ)) → IsSiegPull s j G e κ C π → IsPhiDiv (comb 0 (resInt (𝓞 E) φs) d (resInt (𝓞 E) φs)) C (BD.pull π h) := by
  intro E _ _ _ H D l Xo c n R _ b ω φ φs F S s j _ G _ e BD d N κ C π h _ _ _ _ _ hag hded _ _ hS _ hP
  intro W _ _ _ hW ϖ hϖ χ t mχ P hr be hbe hmon
  obtain ⟨-, -, -, -, hG, -, he, -, -, hch, -⟩ := hS
  obtain ⟨A, _, _, bA, ξ, m, τ, A', _, _, _, ρ, r, G', _, _, π', Dg, B, U, γ, a, ⟨hAc, -, hx, hEt, hFU⟩, ⟨-, -, hj⟩,
    ⟨hA', hA0, hρ, hρf, -, hrt⟩, ⟨hU, hX, hγ, hmonC⟩, ha, hid⟩ := hch ((χ ≫ π) (closedPoint W))
  obtain ⟨_, hAi⟩ := GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing A
  have hCN : IsCN A := ⟨inferInstance, hAi, hAc, RingHom.charZero ρ⟩
  have hCN' : IsCN A' := ⟨hA'.1, hA'.2.2.1, hA'.2.2.2, hA0⟩
  obtain ⟨V₀, _, _, _, f₀, ψ₀, hV₀, hf₀, hf₀l, hψ₀l, -, hc₀⟩ :=
    GlobalTheory.TraitLift.exists_lift S A ξ hCN hEt hFU W hW ϖ hϖ (χ ≫ π) hx.symm
  obtain ⟨V, _, _, _, f₁, ψ, hV, hf₁, hf₁l, hψl, hψ⟩ := GlobalTheory.T.exists_dvr_lift_finite_cover A A' ρ hρ hρf V₀ hV₀ ψ₀ hψ₀l
  obtain ⟨πP, hUP⟩ := GlobalTheory.T.siegel_pullback_dvr_extension E H D l Xo c _ n R ω F S s j G e κ C π hded hP W _ χ t mχ P hr
  let f := f₁.comp f₀
  have hf : Function.Injective f := hf₁.comp hf₀
  have hfl : IsLocalHom f := inferInstance
  have hc : spMap f ≫ χ ≫ π = spMap ψ ≫ spMap ρ ≫ ξ := by
    rw [spMap_comp, Category.assoc, hc₀, ← Category.assoc, ← spMap_comp, ← hψ, spMap_comp, Category.assoc]
  have := hW.1
  have := hV.1
  obtain ⟨ϖ', hϖ'⟩ := IsDiscreteValuationRing.exists_irreducible V
  have hfϖ : f ϖ ≠ 0 := fun h => hϖ.ne_zero (hf (h.trans (map_zero f).symm))
  obtain ⟨k, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hfϖ hϖ'
  have hk : k ≠ 0 := by
    rintro rfl
    rw [pow_zero, mul_one] at hu
    exact hϖ.not_isUnit (isUnit_of_map_unit f ϖ (hu ▸ u.isUnit))

  have hfbot : spMap f (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum V) = (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum W) :=
    PrimeSpectrum.ext (Ideal.comap_bot_of_injective f hf)
  have hgen : (spMap f ≫ χ ≫ π) (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum V) ∈ Set.range j := by
    obtain ⟨-, y, -, -, hy, -⟩ := hUP
    let p : Sp (FractionRing W) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing W))
    refine ⟨y p, ?_⟩
    rw [← Scheme.Hom.comp_apply, hy, Scheme.Hom.comp_apply, jK_apply_eq_bot W p, ← hfbot]
    rfl
  have hrV : Set.range (jK V ≫ spMap f ≫ χ ≫ π) ⊆ Set.range j := by
    rintro _ ⟨p, rfl⟩
    rw [Scheme.Hom.comp_apply, jK_apply_eq_bot V p]
    exact hgen
  have hτ : ∀ i, ψ (ρ (τ i)) = ψ (r i) ^ 2 := fun i => by rw [← hrt, map_pow]
  have hψr : ∀ i, ψ (r i) ≠ 0 := by
    rw [hc] at hgen
    have hp : ∏ i, τ i ∉ ((spMap ψ ≫ spMap ρ) (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum V)).asIdeal := (hj _).1 hgen
    have hp' : ψ (ρ (∏ i, τ i)) ≠ 0 := fun h => hp (by
      show ψ (ρ (∏ i, τ i)) ∈ (⊥ : Ideal V)
      rw [h]; exact Ideal.zero_mem _)
    rw [map_prod, map_prod] at hp'
    exact fun i h => Finset.prod_ne_zero_iff.1 hp' i (Finset.mem_univ i) (by rw [hτ, h]; simp)
  choose nn vv hvv using fun i => IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (hψr i) hϖ'

  obtain ⟨ε, hε⟩ := exists_compare hG he (isCN_of_cdvr hW) hCN' (isCN_of_cdvr hV) f hfl ψ hψl hUP
    {p | ϖ ∉ p.asIdeal} (PrimeSpectrum.isOpen_basicOpen (a := ϖ))
    (fun y => hmon.psiUnitOn y fun p hp => by simpa using hp) (fun h => hfϖ (RingHom.mem_ker.1 h)) hU
    {p | ∏ i, r i ∉ p.asIdeal} (PrimeSpectrum.isOpen_basicOpen (a := ∏ i, r i))
    (fun y => hmonC.psiUnitOn y fun p hp => hp) (fun h => by
      have h' : ψ (∏ i, r i) = 0 := RingHom.mem_ker.1 h
      rw [map_prod] at h'
      exact Finset.prod_ne_zero_iff.2 (fun i _ => hψr i) h') hc hrV
  have hprod : ∀ x : Fin m → ℕ, Associated (∏ i, ψ (r i) ^ x i) (ϖ' ^ ∑ i, nn i * x i) := fun x => by
    rw [← Finset.prod_pow_eq_pow_sum]
    refine Associated.prod _ _ _ fun i _ => ?_
    rw [hvv, pow_mul]
    exact (associated_unit_mul_left _ _ (vv i).isUnit).pow_pow
  have hpow : ∀ x : ℕ, Associated (f ϖ ^ x) (ϖ' ^ (k * x)) := fun x => by
    rw [hu, pow_mul]
    exact (associated_unit_mul_left _ _ u.isUnit).pow_pow
  have hform : ∀ y, (k : ℤ) * be y y = ∑ i, ((2 * nn i : ℕ) : ℤ) * (n * γ i (ε y) (ε y)) := fun y => by
    obtain ⟨u₁, n₁, hn₁, c₁⟩ := hmon y
    obtain ⟨u₂, n₂, hn₂, c₂⟩ := hmonC (ε y)
    have a₁ : Associated (f (u₁ * ∏ i, ![ϖ] i ^ n₁ i)) (ϖ' ^ (k * n₁ 0)) := by
      rw [Fin.prod_univ_one, Matrix.cons_val_zero, map_mul, map_pow]
      exact (associated_unit_mul_left _ _ (u₁.isUnit.map f)).trans (hpow _)
    have a₂ : Associated (ψ (u₂ * ∏ i, r i ^ n₂ i)) (ϖ' ^ ∑ i, nn i * n₂ i) := by
      rw [map_mul, map_prod]
      simp_rw [map_pow]
      exact (associated_unit_mul_left _ _ (u₂.isUnit.map ψ)).trans (hprod _)
    have a₃ := (a₁.pow_pow (n := 2)).symm.trans ((hε y _ _ c₁ c₂).trans (a₂.pow_pow (n := 2)))
    rw [← pow_mul, ← pow_mul] at a₃
    have e₁ : k * n₁ 0 = ∑ i, nn i * n₂ i := by have := eq_of_associated_pow hϖ' a₃; omega
    have h0 : be y y = 2 * n₁ 0 := by simpa using hn₁ 0
    have h1 : ∀ i, (n : ℤ) * γ i (ε y) (ε y) = n₂ i := fun i => by
      have := hn₂ i
      simp only [LinearMap.smul_apply, smul_eq_mul] at this
      linarith
    simp_rw [h1]
    rw [h0]
    have e₂ := congrArg (fun x : ℕ => (x : ℤ)) e₁
    push_cast at e₂ ⊢
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum, ← e₂]
    ring
  have hval := mul_evalZ_eq φ ε hγ n be hbe.1 hk _ hform

  have hmapf : (idlAlong BD.idealSheaf (χ ≫ π)).map f = Ideal.span {ϖ' ^ ∑ i, nn i * (2 * a i)} := by
    rw [← GlobalTheory.TraitOrder.idlAlong_comp, hc, GlobalTheory.TraitOrder.idlAlong_comp, GlobalTheory.TraitOrder.idlAlong_comp, hid, Ideal.map_span,
      Set.image_singleton, Ideal.map_span, Set.image_singleton, map_prod, map_prod]
    simp_rw [map_pow, hτ, ← pow_mul]
    exact Ideal.span_singleton_eq_span_singleton.2 (hprod _)
  have hne : idlAlong BD.idealSheaf (χ ≫ π) ≠ ⊥ := by
    intro h
    rw [h, Ideal.map_bot] at hmapf
    exact pow_ne_zero _ hϖ'.ne_zero (Ideal.span_singleton_eq_bot.1 hmapf.symm)
  obtain ⟨n₀, hn₀⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hne hϖ
  have hrN : k * n₀ = ∑ i, nn i * (2 * a i) := by
    rw [hn₀, Ideal.map_span, Set.image_singleton, map_pow] at hmapf
    exact eq_of_associated_pow hϖ' ((hpow _).symm.trans (Ideal.span_singleton_eq_span_singleton.1 hmapf))
  refine ⟨n₀, ?_, (GlobalTheory.PolOrdPull.idlAlong_pull BD π h χ).trans hn₀⟩
  have hres : (resInt (𝓞 E) φs).evalZ be = φs.evalZ be := by
    obtain ⟨q, x, hx⟩ := Module.Finite.exists_fin' (𝓞 E) P.D.toPre.X
    unfold InvFun.evalZ
    rw [InvFun.eval_eq _ hx]
    exact φs.eval_comp (r := x.restrictScalars ℤ) hx fun a b => (be a b : ℝ)
  have hagr : φs.evalZ be = φ.evalZ be := by
    rw [← evalR_toReal, ← evalR_toReal]
    refine hag _ (ε.toIntLinearEquiv.finrank_eq.trans_le hX) _
      (TameZ.toReal_mem_psdCone_int (mem_balForms_int.2 hbe.1) fun y => by simpa using hmon.nonneg 0 y)
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  rw [GlobalTheory.GenFan.PhiOrder.comb_evalZ, hres, hagr, ← mul_right_inj' hk', mul_left_comm, hval, Finset.mul_sum]
  have e₃ := congrArg (fun x : ℕ => (x : ℝ)) hrN
  push_cast at e₃ ⊢
  rw [e₃]
  exact Finset.sum_congr rfl fun i _ => by rw [ha]; ring

end GlobalTheory.SiegLoc.TraitOrd
