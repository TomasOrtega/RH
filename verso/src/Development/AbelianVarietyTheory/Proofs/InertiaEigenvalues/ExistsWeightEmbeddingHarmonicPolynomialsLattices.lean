import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsetTwistExceptionalPlaces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameEquivApply
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleTwistOfTwistingCharacter
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TensorMapDescent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisConjDefiniteFormsSemilinearEquiv
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarmonicPolynomialEqZeroOfFunctionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockHarmonicValueSpaceMapEqDualWeylModuleFunctioStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffPolynomialEqZeroOfVanishingOnGLFamily
import Formalism.LocalToGlobal.Columns.CoefModAt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameKeepsMatricesMatchesRationalPointsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open GlobalTheory.FormInner (frameEquiv)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MtRead
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
noncomputable section

namespace GlobalTheory.MtRead.WtEmb

variable {D : D7}

/- English proof (translation)
Consider the cases of `a`. Consider the cases of `b`. Reduce the equality to equality of the corresponding arguments. Use function extensionality and compare the values at `i`. Conclude with `h i`.
-/
theorem domWeight_eq {N : ℕ} {a b : DomWeight N} (h : ∀ i, a.w i = b.w i) : a = b := by
  cases a; cases b; congr; funext i; exact h i

def mapK {K L : Type} [Field K] [Field L] (φ : K →+* L) {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) :
    VV K lam →ₛₗ[φ] VV L lam where
  toFun x := ⟨MvPolynomial.map φ x.1, GlobalTheory.Proof.TensorMapDescent.map_mem_VV φ lam _ x.2⟩
  map_add' x y := Subtype.ext (map_add _ _ _)
  map_smul' a x := Subtype.ext (by simp [MvPolynomial.smul_eq_C_mul])

/- English proof (translation)
The claim follows from `Subtype.ext (by change MvPolynomial.map ψ (MvPolynomial.map φ x.1) = MvPolynomial.map (ψ.comp φ) x.1 rw [MvPolynomial.map_map])`.
-/
theorem mapVV_mapK {K L : Type} [Field K] [Field L] (φ : K →+* L) (ψ : L →+* ℂ) {ι : Type} [Fintype ι] {n : ℕ}
    (lam : ι → DomWeight n) (x : VV K lam) :
    GlobalTheory.CoefModel.mapVV ψ lam (mapK φ lam x) = GlobalTheory.CoefModel.mapVV (ψ.comp φ) lam x :=
  Subtype.ext (by
    change MvPolynomial.map ψ (MvPolynomial.map φ x.1) = MvPolynomial.map (ψ.comp φ) x.1
    rw [MvPolynomial.map_map])

def cfn {n : ℕ} (lam : D.what₂.Tau → DomWeight n) : VV ℂ lam →ₗ[ℂ] (GLR D n → ℂ) where
  toFun F := coefFn (RingHom.id ℂ) lam (F : Pol ℂ D.what₂.Tau n)
  map_add' F G := by
    funext x
    simp only [coefFn, Submodule.coe_add, map_add, Pi.add_apply, mul_add]
  map_smul' c F := by
    funext x
    simp only [coefFn, Submodule.coe_smul, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval₂Hom_C, RingHom.id_apply,
      Pi.smul_apply, smul_eq_mul]
    ring

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cfn_apply {n : ℕ} (lam : D.what₂.Tau → DomWeight n) (F : VV ℂ lam) :
    cfn lam F = coefFn (RingHom.id ℂ) lam (F : Pol ℂ D.what₂.Tau n) := rfl

/- English proof (translation)
The claim follows from `(injective_iff_map_eq_zero _).2 fun F hF => Subtype.ext (GlobalTheory.ExportSeries.eq_zero_of_coefFn_id_eq_zero D n lam F (congrFun hF))`.
-/
theorem cfn_injective {n : ℕ} (lam : D.what₂.Tau → DomWeight n) : Function.Injective (cfn lam) :=
  (injective_iff_map_eq_zero _).2 fun F hF =>
    Subtype.ext (GlobalTheory.ExportSeries.eq_zero_of_coefFn_id_eq_zero D n lam F (congrFun hF))

/- English proof (translation)
Use function extensionality and compare the values at `x`. Express the relevant statement in the definitionally equal form `_ = coefFn (RingHom.id ℂ) lam (MvPolynomial.map σ F.1) x`. Simplify using `only [coefFn, MvPolynomial.eval₂Hom_map_hom, RingHom.id_comp]`.
-/
theorem coefFn_eq_cfn {n : ℕ} {K : Type} [Field K] (σ : K →+* ℂ) (lam : D.what₂.Tau → DomWeight n) (F : VV K lam) :
    coefFn σ lam (F : Pol K D.what₂.Tau n) = cfn lam (GlobalTheory.CoefModel.mapVV σ lam F) := by
  funext x
  change _ = coefFn (RingHom.id ℂ) lam (MvPolynomial.map σ F.1) x
  simp only [coefFn, MvPolynomial.eval₂Hom_map_hom, RingHom.id_comp]

/- English proof (translation)
Set `H` to `harm m w B`. Set `hf : H →ₗ[ℂ] (GLR D n → ℂ)` to `harmFn m w B ∘ₗ H.subtype`. Establish `hinj : Function.Injective hf`. Use `(injective_iff_map_eq_zero _).2 fun P hP => Subtype.ext ?_` and prove the remaining obligations. Conclude with `GlobalTheory.T.harmonic_polynomial_eq_zero_of_function D m n w B hw hm P P.2 hP`.

Establish `hr : LinearMap.range hf = LinearMap.range (cfn w.lam)`. Rewrite using `[LinearMap.range_comp, Submodule.range_subtype, GlobalTheory.T.fockHarmonicValueSpace_map_eq_dualWeylModuleFunctions D m n w B hw hm]`. Establish `: {φ | ∃ F : VV ℂ w.lam, φ = coefFn (RingHom.id ℂ) w.lam (F : Pol ℂ D.what₂.Tau n)} = (LinearMap.range (cfn w.lam) : Set (GLR D n → ℂ))`. Use extensionality with `φ`. Simplify using `only [Set.mem_setOf_eq, SetLike.mem_coe, LinearMap.mem_range, cfn_apply]`.

Conclude with `⟨fun ⟨F, h⟩ => ⟨F, h.symm⟩, fun ⟨F, h⟩ => ⟨F, h.symm⟩⟩`. Rewrite using `[this, Submodule.span_eq]`. Set `e1` to `LinearEquiv.ofInjective hf hinj`. Set `e2` to `LinearEquiv.ofInjective (cfn w.lam) (cfn_injective w.lam)`. Set `e3` to `LinearEquiv.ofEq _ _ hr.symm`.

Use `⟨H.subtype ∘ₗ (e1.symm.toLinearMap ∘ₗ e3.toLinearMap ∘ₗ e2.toLinearMap), fun F => ?_, fun F => ?_, fun P hP => ?_⟩` and prove the remaining obligations. Conclude with `(e1.symm (e3 (e2 F))).2`. Establish `h1 : (e1 (e1.symm (e3 (e2 F))) : GLR D n → ℂ) = hf (e1.symm (e3 (e2 F)))` using `LinearEquiv.ofInjective_apply _ _`. Rewrite `h1` using `[LinearEquiv.apply_symm_apply]`. Conclude with `h1.symm.trans (LinearEquiv.ofInjective_apply (cfn w.lam) (h := cfn_injective w.lam) F)`.

Use `⟨e2.symm (e3.symm (e1 ⟨P, hP⟩)), ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `((e1.symm (e3 (e2 (e2.symm (e3.symm (e1 ⟨P, hP⟩))))) : H) : PolF D m n) = P`. Rewrite using `[LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]`.
-/
theorem exists_psi {m n : ℕ} (w : Weight D n) (B : GLR D n) (hw : w.Good) (hm : ∀ τ, w.p τ + w.q τ ≤ m) :
    ∃ Ψ : VV ℂ w.lam →ₗ[ℂ] PolF D m n, (∀ F, Ψ F ∈ harm m w B) ∧ (∀ F, harmFn m w B (Ψ F) = cfn w.lam F) ∧
      ∀ P ∈ harm m w B, ∃ F, Ψ F = P := by
  let H := harm m w B
  let hf : H →ₗ[ℂ] (GLR D n → ℂ) := harmFn m w B ∘ₗ H.subtype
  have hinj : Function.Injective hf := by
    refine (injective_iff_map_eq_zero _).2 fun P hP => Subtype.ext ?_
    exact GlobalTheory.T.harmonic_polynomial_eq_zero_of_function D m n w B hw hm P P.2 hP
  have hr : LinearMap.range hf = LinearMap.range (cfn w.lam) := by
    rw [LinearMap.range_comp, Submodule.range_subtype, GlobalTheory.T.fockHarmonicValueSpace_map_eq_dualWeylModuleFunctions D m n w B hw hm]
    have : {φ | ∃ F : VV ℂ w.lam, φ = coefFn (RingHom.id ℂ) w.lam (F : Pol ℂ D.what₂.Tau n)} =
        (LinearMap.range (cfn w.lam) : Set (GLR D n → ℂ)) := by
      ext φ
      simp only [Set.mem_setOf_eq, SetLike.mem_coe, LinearMap.mem_range, cfn_apply]
      exact ⟨fun ⟨F, h⟩ => ⟨F, h.symm⟩, fun ⟨F, h⟩ => ⟨F, h.symm⟩⟩
    rw [this, Submodule.span_eq]
  let e1 := LinearEquiv.ofInjective hf hinj
  let e2 := LinearEquiv.ofInjective (cfn w.lam) (cfn_injective w.lam)
  let e3 := LinearEquiv.ofEq _ _ hr.symm
  refine ⟨H.subtype ∘ₗ (e1.symm.toLinearMap ∘ₗ e3.toLinearMap ∘ₗ e2.toLinearMap), fun F => ?_, fun F => ?_,
    fun P hP => ?_⟩
  · exact (e1.symm (e3 (e2 F))).2
  · have h1 : (e1 (e1.symm (e3 (e2 F))) : GLR D n → ℂ) = hf (e1.symm (e3 (e2 F))) :=
      LinearEquiv.ofInjective_apply _ _
    rw [LinearEquiv.apply_symm_apply] at h1
    exact h1.symm.trans (LinearEquiv.ofInjective_apply (cfn w.lam) (h := cfn_injective w.lam) F)
  · refine ⟨e2.symm (e3.symm (e1 ⟨P, hP⟩)), ?_⟩
    change ((e1.symm (e3 (e2 (e2.symm (e3.symm (e1 ⟨P, hP⟩))))) : H) : PolF D m n) = P
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]

/- English proof (translation)
Introduce `F G h` and use `cfn_injective w.lam (by rw [← h2, ← h2, h])`.
-/
theorem psi_inj {m n : ℕ} {w : Weight D n} {B : GLR D n} {Ψ : VV ℂ w.lam →ₗ[ℂ] PolF D m n}
    (h2 : ∀ F, harmFn m w B (Ψ F) = cfn w.lam F) : Function.Injective Ψ := fun F G h =>
  cfn_injective w.lam (by rw [← h2, ← h2, h])

/- English proof (translation)
Use `sub_eq_zero.1 (GlobalTheory.T.harmonic_polynomial_eq_zero_of_function D m n w B hw hm _ (sub_mem (h1 _) (fockGL_mem_harm w B _ (h1 _))) ?_)` and prove the remaining obligations. Use function extensionality and compare the values at `x`. Rewrite using `[map_sub, Pi.sub_apply, h2, harmFn_fockGL, h2, Pi.zero_apply, sub_eq_zero, cfn_apply, cfn_apply, coefFn_rhoVr (RingHom.id ℂ) (fun τ => RingHom.id_comp _)]`.
-/
theorem psi_rhoVr {m n : ℕ} {w : Weight D n} {B : GLR D n} (hw : w.Good) (hm : ∀ τ, w.p τ + w.q τ ≤ m)
    {Ψ : VV ℂ w.lam →ₗ[ℂ] PolF D m n} (h1 : ∀ F, Ψ F ∈ harm m w B) (h2 : ∀ F, harmFn m w B (Ψ F) = cfn w.lam F)
    (γ : GL (Fin n) D.host.E) (F : VV ℂ w.lam) :
    Ψ (rhoVr (tauE D) w.lam γ F) = fockGL m w B (embGL (tauE D) γ) (Ψ F) := by
  refine sub_eq_zero.1 (GlobalTheory.T.harmonic_polynomial_eq_zero_of_function D m n w B hw hm _ (sub_mem (h1 _) (fockGL_mem_harm w B _ (h1 _))) ?_)
  funext x
  rw [map_sub, Pi.sub_apply, h2, harmFn_fockGL, h2, Pi.zero_apply, sub_eq_zero, cfn_apply, cfn_apply,
    coefFn_rhoVr (RingHom.id ℂ) (fun τ => RingHom.id_comp _)]

def sumMap {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V] {ι : Type} [Fintype ι] (e : F →+* ℂ)
    (b : Module.Basis ι F V) {U : Type} [AddCommGroup U] [Module ℂ U] (v : ι → U) : V →ₛₗ[e] U where
  toFun w := ∑ x, e (b.repr w x) • v x
  map_add' w w' := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c w := by simp [Finset.smul_sum, mul_smul]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sumMap_apply {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V] {ι : Type} [Fintype ι] (e : F →+* ℂ)
    (b : Module.Basis ι F V) {U : Type} [AddCommGroup U] [Module ℂ U] (v : ι → U) (w : V) :
    sumMap e b v w = ∑ x, e (b.repr w x) • v x := rfl

/- English proof (translation)
Use `linearIndependent_of_top_le_span_of_card_eq_finrank ?_ ?_` and prove the remaining obligations. Rewrite using `[← GlobalTheory.CoefModel.span_mapVV φ lam, Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Simplify using `only`. Rewrite using `[← c.sum_repr (bVV K lam i), map_sum]`.

Use `Submodule.sum_mem _ fun x _ => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.map_smulₛₗ]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)`. Rewrite using `[← Module.finrank_eq_card_basis c, Module.finrank_eq_card_basis (bVV K lam), Module.finrank_eq_card_basis (bVV ℂ lam)]`.
-/
theorem linInd_mapVV {ι' : Type} [Fintype ι'] {n : ℕ} {K : Type} [Field K] (φ : K →+* ℂ) (lam : ι' → DomWeight n)
    {ι : Type} [Fintype ι] (c : Module.Basis ι K (VV K lam)) :
    LinearIndependent ℂ fun x => GlobalTheory.CoefModel.mapVV φ lam (c x) := by
  refine linearIndependent_of_top_le_span_of_card_eq_finrank ?_ ?_
  · rw [← GlobalTheory.CoefModel.span_mapVV φ lam, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    dsimp only
    rw [← c.sum_repr (bVV K lam i), map_sum]
    refine Submodule.sum_mem _ fun x _ => ?_
    rw [LinearMap.map_smulₛₗ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)
  · rw [← Module.finrank_eq_card_basis c, Module.finrank_eq_card_basis (bVV K lam),
      Module.finrank_eq_card_basis (bVV ℂ lam)]

end GlobalTheory.MtRead.WtEmb

end

noncomputable section

namespace GlobalTheory.MtRead.WtEmb

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_coefLat_iff {D : D7} {S T : HSp D} (B : Base S T) {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ)
    (emb : D.what₂.Tau → (D.host.E →+* K)) (O : Subring ℂ) (h : Bridge.Gf S) (P : PolF D T.rank S.rank) :
    P ∈ B.coefLat σ emb O h ↔
      P ∈ harm T.rank B.w B.F.BS ∧ harmFn T.rank B.w B.F.BS P ∈ coefLatFn σ emb O B.w.lam (B.latAt h) := Iff.rfl

/- English proof (translation)
Introduce `D S T B hB n hF P hP hn K₀ _ R _ _ e f s hs hc W₀ _ _ ρ₀ lam hlam T₀ hT₀ W _ _ ρ hW`. Substitute `hn` using the available equality. Take `rfl : lam = B.w.lam` from `funext fun τ => domWeight_eq fun a => hlam τ a`. Take `⟨ι, _, _, b₀, b₁, hmat⟩` from `hW`. Use `set O : Subring ℂ := (e.comp (algebraMap R (FractionRing R))).range with hO`.

Establish `hm : ∀ τ, B.w.p τ + B.w.q τ ≤ T.rank` using `fun τ => by`. Establish `h1` using `hB.sig τ`. Establish `h2` using `Formalism.BasicNotions.sig_sum _ hB.sigOK (tauE D τ)`. Rewrite `h2` using `[← h1]`. Conclude with `h2.le`.

Take `⟨Ψ, hΨ1, hΨ2, hΨ3⟩` from `exists_psi (m := T.rank) B.w B.F.BS hB.wt hm`. Establish `hΨinj` using `psi_inj hΨ2`. Set `c₀ : Module.Basis ι K₀ (VV K₀ B.w.lam)` to `b₀.map T₀`. Set `v : ι → VV ℂ B.w.lam` to `fun x => GlobalTheory.CoefModel.mapVV (e.comp f) B.w.lam (c₀ x)`. Establish `hv : LinearIndependent ℂ v` using `linInd_mapVV (e.comp f) B.w.lam c₀`.

Set `Ω : W →ₛₗ[e] VV ℂ B.w.lam` to `sumMap e b₁ v`. Establish `hΩ : ∀ (w : W) (y : VV K₀ B.w.lam), (∀ x, b₁.repr w x = f (c₀.repr y x)) → Ω w = GlobalTheory.CoefModel.mapVV (e.comp f) B.w.lam y`. Introduce `w y h`. Rewrite using `[show Ω w = sumMap e b₁ v w from rfl, sumMap_apply]`. Use `conv_rhs => rw [← c₀.sum_repr y]`.

Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.map_smulₛₗ, h x]`. Both sides reduce to the same expression. Establish `hΩb : ∀ y, Ω (b₁ y) = v y` using `fun y => by`.

Rewrite using `[show Ω (b₁ y) = sumMap e b₁ v (b₁ y) from rfl, sumMap_apply]`. Simplify using `[Module.Basis.repr_self, Finsupp.single_apply]`. Establish `hOinj : Function.Injective Ω`. Use `(injective_iff_map_eq_zero _).2 fun w hw => ?_` and prove the remaining obligations. Establish `h0` using `Fintype.linearIndependent_iff.1 hv (fun x => e (b₁.repr w x)) hw`.

Use `b₁.repr.injective (Finsupp.ext fun x => ?_)` and prove the remaining obligations. Rewrite using `[map_zero, Finsupp.zero_apply]`. Conclude with `(map_eq_zero_iff e e.injective).1 (h0 x)`. Establish `hrepr : ∀ a : ι → FractionRing R, ∀ x, b₁.repr (b₁.equivFun.symm a) x = a x` using `fun a x => by`. Use `congrFun (b₁.equivFun.apply_symm_apply a) x` as an intermediate fact.

Rewrite `this` using `[Module.Basis.equivFun_apply]`. Then use the resulting hypothesis. Establish `hsO : (e.comp f).comp s = embLL0 D` using `RingHom.ext hs`. Establish `hemb : ∀ τ, (e.comp f).comp (s.comp (labLL0 D τ)) = tauE D τ` using `fun τ => by`. Rewrite using `[← RingHom.comp_assoc, hsO]`. Conclude with `hc.emb τ`.

Use `⟨Ψ ∘ₛₗ Ω, hΨinj.comp hOinj, fun w => hΨ1 _, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `γ γ' hγγ' w`. Choose the witnesses or unpack the hypotheses as in `⟨γE, hγE⟩ : ∃ γE, Bridge.IsRatMat S γ' γE := by`. Take `⟨y, -, hy⟩` from `γ'.2`. Conclude with `⟨y, hy.symm⟩`.

Establish `hmγ` using `(GlobalTheory.T.frameKeepsMatrices_matches_rationalPoints D S S.rank hF P hP).2 rfl γ γ' γE hγγ' hγE`. Establish `hT` using `hT₀ γ γE (Matrix.ext fun a c => by simpa using hmγ a c)`. Establish `hact : B.act (γ' : GA D S) = fockGL T.rank B.w B.F.BS (embGL (tauE D) γE)`. Rewrite using `[Base.act, MonoidHom.comp_apply, realGL_rat hB.frame.vac.2.inf hγE]`. Establish `htau : (fun τ => (e.comp f).comp (s.comp (labLL0 D τ))) = tauE D` using `funext hemb`.

Establish `key : Ω.comp (ρ γ) = (rhoVr (tauE D) B.w.lam γE).comp Ω`. Use `b₁.ext fun y => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.comp_apply, LinearMap.comp_apply, hΩb]`. Establish `e1 : Ω (ρ γ (b₁ y)) = GlobalTheory.CoefModel.mapVV (e.comp f) B.w.lam (T₀ (ρ₀ γ (b₀ y)))`. Use `hΩ _ _ fun x => ?_` and prove the remaining obligations.

Use `congrFun (congrFun (hmat γ) x) y` as an intermediate fact. Rewrite `this` using `[LinearMap.toMatrix_apply, Matrix.map_apply, LinearMap.toMatrix_apply]`. Rewrite using `[this]`. Simplify using `[c₀]`. Rewrite using `[e1, hT, GlobalTheory.ConjTwist.mapVV_rhoVr, htau]`.

Both sides reduce to the same expression. Use `LinearMap.congr_fun key w` as an intermediate fact. Rewrite `this` using `[LinearMap.comp_apply, LinearMap.comp_apply]`. Express the relevant statement in the definitionally equal form `Ψ (Ω (ρ γ w)) = B.act γ' (Ψ (Ω w))`. Rewrite using `[this, hact, psi_rhoVr hB.wt hm hΨ1 hΨ2]`.

Introduce `h x hx`. Take `⟨hx1, hx2⟩` from `(mem_coefLat_iff B _ _ _ h x).1 hx`. Take `⟨G, rfl⟩` from `hΨ3 x hx1`. Rewrite `hx2` using `[hΨ2]`. It suffices to establish `∀ φ ∈ coefLatFn (embLL0 D) (labLL0 D) O B.w.lam (B.latAt h), ∃ w, cfn B.w.lam (Ω w) = φ by`.

Take `⟨w, hw⟩` from `this _ hx2`. Conclude with `⟨w, by change Ψ (Ω w) = Ψ G; rw [cfn_injective _ hw]⟩`. Introduce `φ hφ`. Proceed by induction on `hφ using Submodule.span_induction with`. Consider the case `mem φ hφ`.

Take `⟨F, -, rfl⟩` from `hφ`. Use `⟨b₁.equivFun.symm fun x => f (c₀.repr (mapK s B.w.lam F) x), ?_⟩` and prove the remaining obligations. Rewrite using `[hΩ _ (mapK s B.w.lam F) (hrepr _), mapVV_mapK, hsO, coefFn_eq_cfn]`. Consider the case `zero => exact ⟨0, by rw [map_zero, map_zero]⟩`. Consider the case `add φ₁ φ₂ _ _ h₁ h₂`.

Take `⟨w₁, rfl⟩` from `h₁`. Take `⟨w₂, rfl⟩` from `h₂`. Conclude with `⟨w₁ + w₂, by rw [map_add, map_add]⟩`. Consider the case `smul o φ _ h₁`. Take `⟨w₁, rfl⟩` from `h₁`.

Take `⟨_, r, rfl⟩` from `o`. Use `⟨algebraMap R (FractionRing R) r • w₁, ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.map_smulₛₗ, map_smul]`. Both sides reduce to the same expression. Introduce `h w`.

Establish `hL : Submodule.IsLattice D.host.E (B.latAt h)` using `Formalism.UG.P.csGlob_lattice _ (Module.Finite.iff_fg.2 hB.frame.sdS.1.fg) hB.frame.sdS.1.span_eq_top _`. Set `Lat : Submodule O (VV ℂ B.w.lam)` to `(coefLatFn (embLL0 D) (labLL0 D) O B.w.lam (B.latAt h)).comap ((cfn B.w.lam).restrictScalars O)`. Establish `hsmul : ∀ (c : R) {G : VV ℂ B.w.lam}, G ∈ Lat → e (algebraMap R (FractionRing R) c) • G ∈ Lat` using `fun c G hG => Lat.smul_mem (⟨_, c, rfl⟩ : O) hG`. Set `Q : VV K₀ B.w.lam → Prop` to `fun y => ∀ r : FractionRing R, ∃ c : R, c ≠ 0 ∧ e (algebraMap R (FractionRing R) c * r) • GlobalTheory.CoefModel.mapVV (e.comp f) B.w.lam y ∈ Lat`. Establish `hQ0 : Q 0` using `fun r => ⟨1, one_ne_zero, by rw [map_zero, smul_zero]; exact zero_mem _⟩`.

Establish `hQadd : ∀ y₁ y₂, Q y₁ → Q y₂ → Q (y₁ + y₂)` using `fun y₁ y₂ h₁ h₂ r => by`. Take `⟨c₁, hc₁, h₁⟩` from `h₁ r`. Take `⟨c₂, hc₂, h₂⟩` from `h₂ r`. Use `⟨c₂ * c₁, mul_ne_zero hc₂ hc₁, ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, smul_add, map_mul (algebraMap R (FractionRing R)) c₂ c₁, mul_assoc, map_mul e, ← smul_smul]`.

Use `add_mem (hsmul c₂ h₁) ?_` and prove the remaining obligations. Rewrite using `[← map_mul e, ← mul_assoc, ← map_mul (algebraMap R (FractionRing R)), mul_comm c₂ c₁, map_mul (algebraMap R (FractionRing R)), mul_assoc, map_mul e, ← smul_smul]`. Conclude with `hsmul c₁ h₂`. Establish `hQsmul : ∀ (k : K₀) y, Q y → Q (k • y)` using `fun k y hy r => by`. Take `⟨c, hc0, hc⟩` from `hy (r * f k)`.

Use `⟨c, hc0, ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.map_smulₛₗ, smul_smul, RingHom.comp_apply, ← map_mul, mul_assoc]`. Conclude with `hc`. Establish `hQbase : ∀ F ∈ nabAtr (labLL0 D) B.w.lam (B.latAt h), Q (mapK s B.w.lam F)` using `fun F hF r => by`. Take `⟨⟨a, d⟩, had⟩` from `IsLocalization.surj (nonZeroDivisors R) r`.

Use `⟨d, nonZeroDivisors.ne_zero d.2, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_comm (algebraMap R (FractionRing R) _) r, had, mapVV_mapK, hsO]`. Use `hsmul a ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `cfn B.w.lam (GlobalTheory.CoefModel.mapVV (embLL0 D) B.w.lam F) ∈ coefLatFn _ _ _ _ _`. Rewrite using `[← coefFn_eq_cfn]`.

Conclude with `Submodule.subset_span ⟨F, hF, rfl⟩`. Establish `hspanLL : ∀ G ∈ Submodule.span (↥D.LL0) (nabAtr (labLL0 D) B.w.lam (B.latAt h) : Set (VV (↥D.LL0) B.w.lam)), Q (mapK s B.w.lam G)`. Introduce `G hG`. Proceed by induction on `hG using Submodule.span_induction with`. Consider the case `mem F hF => exact hQbase F hF`.

Consider the case `zero => rw [map_zero]`. Conclude with `hQ0`. Consider the case `add _ _ _ _ h₁ h₂ => rw [map_add]`. Conclude with `hQadd _ _ h₁ h₂`. Consider the case `smul k _ _ h₁ => rw [LinearMap.map_smulₛₗ]`.

Conclude with `hQsmul _ _ h₁`. Establish `hlat` using `Formalism.L2.DIV.nabAtr_isLattice (labLL0 D) B.w.lam (B.latAt h) hL`. Establish `hg : ∀ i, Q (mapK s B.w.lam (bVV (↥D.LL0) B.w.lam i))` using `fun i => hspanLL _ (by rw [hlat.span_eq_top]; trivial)`. Establish `hgind : LinearIndependent K₀ fun i => mapK s B.w.lam (bVV (↥D.LL0) B.w.lam i)`. Use `Fintype.linearIndependent_iff.2 fun k hk i => ?_` and prove the remaining obligations.

Establish `h1` using `congrArg (GlobalTheory.CoefModel.mapVV (e.comp f) B.w.lam) hk`. Rewrite `h1` using `[map_sum, map_zero]`. Simplify using `only [LinearMap.map_smulₛₗ, mapVV_mapK] at h1`. Rewrite `h1` using `[hsO]`. Use `Fintype.linearIndependent_iff.1 (GlobalTheory.CoefModel.linearIndependent_mapVV (embLL0 D) B.w.lam) (fun i => (e.comp f) (k i)) h1 i` as an intermediate fact.

Conclude with `(map_eq_zero_iff (e.comp f) (e.comp f).injective).1 this`. Use `haveI : FiniteDimensional K₀ (VV K₀ B.w.lam) := Module.Finite.of_basis (bVV K₀ B.w.lam)`. Establish `hgspan` using `hgind.span_eq_top_of_card_eq_finrank' (Module.finrank_eq_card_basis (bVV K₀ B.w.lam)).symm`. Establish `hQall : ∀ y : VV K₀ B.w.lam, Q y`. Introduce `y`.

Establish `hy : y ∈ Submodule.span K₀ (Set.range fun i => mapK s B.w.lam (bVV (↥D.LL0) B.w.lam i))`. Rewrite using `[hgspan]`. Discharge the goal by the elementary cases of `trivial`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy`.

Take `⟨i, rfl⟩` from `hy`. Conclude with `hg i`. Consider the case `zero => exact hQ0`. Consider the case `add _ _ _ _ h₁ h₂ => exact hQadd _ _ h₁ h₂`. Consider the case `smul k _ _ h₁ => exact hQsmul _ _ h₁`.

Use `choose cx hcx0 hcx using fun x => hQall (c₀ x) (b₁.repr w x)`. Use `⟨∏ x, cx x, Finset.prod_ne_zero_iff.2 fun x _ => hcx0 x, ?_⟩` and prove the remaining obligations. Use `(mem_coefLat_iff B _ _ _ h _).2 ⟨hΨ1 _, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `harmFn T.rank B.w B.F.BS (Ψ (Ω _)) ∈ _`. Rewrite using `[hΨ2]`.

Express the relevant statement in the definitionally equal form `Ω _ ∈ Lat`. Rewrite using `[show Ω (algebraMap R (FractionRing R) (∏ x, cx x) • w) = sumMap e b₁ v (algebraMap R (FractionRing R) (∏ x, cx x) • w) from rfl, sumMap_apply]`. Use `Submodule.sum_mem _ fun x _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, Finsupp.smul_apply, smul_eq_mul]`. Establish `e1 : algebraMap R (FractionRing R) (∏ x, cx x) * b₁.repr w x = algebraMap R (FractionRing R) (∏ x' ∈ Finset.univ.erase x, cx x') * (algebraMap R (FractionRing R) (cx x) * b₁.repr w x)`.

Rewrite using `[← Finset.prod_erase_mul _ _ (Finset.mem_univ x), map_mul, mul_assoc]`. Rewrite using `[e1, map_mul e, ← smul_smul]`. Conclude with `hsmul _ (hcx x)`.
-/
theorem exists_wtMap : ∀ (D : D7) (S T : HSp D) (B : GlobalTheory.ExportSeries.Base S T), B.Good → ∀ (n : ℕ) (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi S n), IdFrame hF P → ∀ (hn : S.rank = n) (K₀ : Type) [Field K₀] (R : Type) [CommRing R] [IsDomain R] (e : FractionRing R →+* ℂ) (f : K₀ →+* FractionRing R) (s : ↥D.LL0 →+* K₀), (∀ x, e (f (s x)) = embLL0 D x) → IsCoefRing (embLL0 D) (labLL0 D) (e.comp (algebraMap R (FractionRing R))).range → ∀ (W₀ : Type) [AddCommGroup W₀] [Module K₀ W₀] (ρ₀ : Representation K₀ (ReciprocityTheory.Aut.GQ D.host.E n) W₀) (lam : D.what₂.Tau → DomWeight n), (∀ τ a, (lam τ).w (Fin.cast hn a) = (B.w.lam τ).w a) → ∀ T₀ : W₀ ≃ₗ[K₀] VV K₀ lam, (∀ (γ : ReciprocityTheory.Aut.GQ D.host.E n) (γ₀ : GL (Fin n) D.host.E), (((γ : GAf D.host.E n) : GL (Fin n) (ReciprocityTheory.Aut.AL D.host.E)) : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL D.host.E)) = (γ₀ : Matrix (Fin n) (Fin n) D.host.E).map Algebra.TensorProduct.includeLeftRingHom → ∀ x, T₀ (ρ₀ γ x) = rhoVr (fun τ => s.comp (labLL0 D τ)) lam γ₀ (T₀ x)) → ∀ (W : Type) [AddCommGroup W] [Module (FractionRing R) W] (ρ : Representation (FractionRing R) (ReciprocityTheory.Aut.GQ D.host.E n) W), (∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (b₀ : Module.Basis ι K₀ W₀) (b₁ : Module.Basis ι (FractionRing R) W), ∀ γ : ReciprocityTheory.Aut.GQ D.host.E n, LinearMap.toMatrix b₁ b₁ (ρ γ) = (LinearMap.toMatrix b₀ b₀ (ρ₀ γ)).map f) → ∃ ω : W →ₛₗ[e] PolF D T.rank S.rank, WtMap B (frameEquiv P) R e ρ ω := by
  intro D S T B hB n hF P hP hn K₀ _ R _ _ e f s hs hc W₀ _ _ ρ₀ lam hlam T₀ hT₀ W _ _ ρ hW
  subst hn
  obtain rfl : lam = B.w.lam := funext fun τ => domWeight_eq fun a => hlam τ a
  obtain ⟨ι, _, _, b₀, b₁, hmat⟩ := hW
  set O : Subring ℂ := (e.comp (algebraMap R (FractionRing R))).range with hO
  have hm : ∀ τ, B.w.p τ + B.w.q τ ≤ T.rank := fun τ => by
    have h1 := hB.sig τ
    have h2 := Formalism.BasicNotions.sig_sum _ hB.sigOK (tauE D τ)
    rw [← h1] at h2
    exact h2.le
  obtain ⟨Ψ, hΨ1, hΨ2, hΨ3⟩ := exists_psi (m := T.rank) B.w B.F.BS hB.wt hm
  have hΨinj := psi_inj hΨ2
  let c₀ : Module.Basis ι K₀ (VV K₀ B.w.lam) := b₀.map T₀
  let v : ι → VV ℂ B.w.lam := fun x => GlobalTheory.CoefModel.mapVV (e.comp f) B.w.lam (c₀ x)
  have hv : LinearIndependent ℂ v := linInd_mapVV (e.comp f) B.w.lam c₀
  let Ω : W →ₛₗ[e] VV ℂ B.w.lam := sumMap e b₁ v
  have hΩ : ∀ (w : W) (y : VV K₀ B.w.lam), (∀ x, b₁.repr w x = f (c₀.repr y x)) →
      Ω w = GlobalTheory.CoefModel.mapVV (e.comp f) B.w.lam y := by
    intro w y h
    rw [show Ω w = sumMap e b₁ v w from rfl, sumMap_apply]
    conv_rhs => rw [← c₀.sum_repr y]
    rw [map_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [LinearMap.map_smulₛₗ, h x]
    rfl
  have hΩb : ∀ y, Ω (b₁ y) = v y := fun y => by
    rw [show Ω (b₁ y) = sumMap e b₁ v (b₁ y) from rfl, sumMap_apply]
    simp [Module.Basis.repr_self, Finsupp.single_apply]
  have hOinj : Function.Injective Ω := by
    refine (injective_iff_map_eq_zero _).2 fun w hw => ?_
    have h0 := Fintype.linearIndependent_iff.1 hv (fun x => e (b₁.repr w x)) hw
    refine b₁.repr.injective (Finsupp.ext fun x => ?_)
    rw [map_zero, Finsupp.zero_apply]
    exact (map_eq_zero_iff e e.injective).1 (h0 x)
  have hrepr : ∀ a : ι → FractionRing R, ∀ x, b₁.repr (b₁.equivFun.symm a) x = a x := fun a x => by
    have := congrFun (b₁.equivFun.apply_symm_apply a) x
    rwa [Module.Basis.equivFun_apply] at this
  have hsO : (e.comp f).comp s = embLL0 D := RingHom.ext hs
  have hemb : ∀ τ, (e.comp f).comp (s.comp (labLL0 D τ)) = tauE D τ := fun τ => by
    rw [← RingHom.comp_assoc, hsO]
    exact hc.emb τ
  refine ⟨Ψ ∘ₛₗ Ω, hΨinj.comp hOinj, fun w => hΨ1 _, ?_, ?_, ?_⟩
  ·
    intro γ γ' hγγ' w
    obtain ⟨γE, hγE⟩ : ∃ γE, Bridge.IsRatMat S γ' γE := by
      obtain ⟨y, -, hy⟩ := γ'.2
      exact ⟨y, hy.symm⟩
    have hmγ := (GlobalTheory.T.frameKeepsMatrices_matches_rationalPoints D S S.rank hF P hP).2 rfl γ γ' γE hγγ' hγE
    have hT := hT₀ γ γE (Matrix.ext fun a c => by simpa using hmγ a c)
    have hact : B.act (γ' : GA D S) = fockGL T.rank B.w B.F.BS (embGL (tauE D) γE) := by
      rw [Base.act, MonoidHom.comp_apply, realGL_rat hB.frame.vac.2.inf hγE]
    have htau : (fun τ => (e.comp f).comp (s.comp (labLL0 D τ))) = tauE D := funext hemb
    have key : Ω.comp (ρ γ) = (rhoVr (tauE D) B.w.lam γE).comp Ω := by
      refine b₁.ext fun y => ?_
      rw [LinearMap.comp_apply, LinearMap.comp_apply, hΩb]
      have e1 : Ω (ρ γ (b₁ y)) = GlobalTheory.CoefModel.mapVV (e.comp f) B.w.lam (T₀ (ρ₀ γ (b₀ y))) := by
        refine hΩ _ _ fun x => ?_
        have := congrFun (congrFun (hmat γ) x) y
        rw [LinearMap.toMatrix_apply, Matrix.map_apply, LinearMap.toMatrix_apply] at this
        rw [this]
        simp [c₀]
      rw [e1, hT, GlobalTheory.ConjTwist.mapVV_rhoVr, htau]
      rfl
    have := LinearMap.congr_fun key w
    rw [LinearMap.comp_apply, LinearMap.comp_apply] at this
    change Ψ (Ω (ρ γ w)) = B.act γ' (Ψ (Ω w))
    rw [this, hact, psi_rhoVr hB.wt hm hΨ1 hΨ2]
  ·
    intro h x hx
    obtain ⟨hx1, hx2⟩ := (mem_coefLat_iff B _ _ _ h x).1 hx
    obtain ⟨G, rfl⟩ := hΨ3 x hx1
    rw [hΨ2] at hx2
    suffices ∀ φ ∈ coefLatFn (embLL0 D) (labLL0 D) O B.w.lam (B.latAt h), ∃ w, cfn B.w.lam (Ω w) = φ by
      obtain ⟨w, hw⟩ := this _ hx2
      exact ⟨w, by change Ψ (Ω w) = Ψ G; rw [cfn_injective _ hw]⟩
    intro φ hφ
    induction hφ using Submodule.span_induction with
    | mem φ hφ =>
      obtain ⟨F, -, rfl⟩ := hφ
      refine ⟨b₁.equivFun.symm fun x => f (c₀.repr (mapK s B.w.lam F) x), ?_⟩
      rw [hΩ _ (mapK s B.w.lam F) (hrepr _), mapVV_mapK, hsO, coefFn_eq_cfn]
    | zero => exact ⟨0, by rw [map_zero, map_zero]⟩
    | add φ₁ φ₂ _ _ h₁ h₂ =>
      obtain ⟨w₁, rfl⟩ := h₁
      obtain ⟨w₂, rfl⟩ := h₂
      exact ⟨w₁ + w₂, by rw [map_add, map_add]⟩
    | smul o φ _ h₁ =>
      obtain ⟨w₁, rfl⟩ := h₁
      obtain ⟨_, r, rfl⟩ := o
      refine ⟨algebraMap R (FractionRing R) r • w₁, ?_⟩
      rw [LinearMap.map_smulₛₗ, map_smul]
      rfl
  ·
    intro h w
    have hL : Submodule.IsLattice D.host.E (B.latAt h) :=
      Formalism.UG.P.csGlob_lattice _ (Module.Finite.iff_fg.2 hB.frame.sdS.1.fg) hB.frame.sdS.1.span_eq_top _
    let Lat : Submodule O (VV ℂ B.w.lam) :=
      (coefLatFn (embLL0 D) (labLL0 D) O B.w.lam (B.latAt h)).comap ((cfn B.w.lam).restrictScalars O)
    have hsmul : ∀ (c : R) {G : VV ℂ B.w.lam}, G ∈ Lat → e (algebraMap R (FractionRing R) c) • G ∈ Lat :=
      fun c G hG => Lat.smul_mem (⟨_, c, rfl⟩ : O) hG
    let Q : VV K₀ B.w.lam → Prop := fun y => ∀ r : FractionRing R, ∃ c : R, c ≠ 0 ∧
      e (algebraMap R (FractionRing R) c * r) • GlobalTheory.CoefModel.mapVV (e.comp f) B.w.lam y ∈ Lat
    have hQ0 : Q 0 := fun r => ⟨1, one_ne_zero, by rw [map_zero, smul_zero]; exact zero_mem _⟩
    have hQadd : ∀ y₁ y₂, Q y₁ → Q y₂ → Q (y₁ + y₂) := fun y₁ y₂ h₁ h₂ r => by
      obtain ⟨c₁, hc₁, h₁⟩ := h₁ r
      obtain ⟨c₂, hc₂, h₂⟩ := h₂ r
      refine ⟨c₂ * c₁, mul_ne_zero hc₂ hc₁, ?_⟩
      rw [map_add, smul_add, map_mul (algebraMap R (FractionRing R)) c₂ c₁, mul_assoc, map_mul e, ← smul_smul]
      refine add_mem (hsmul c₂ h₁) ?_
      rw [← map_mul e, ← mul_assoc, ← map_mul (algebraMap R (FractionRing R)), mul_comm c₂ c₁,
        map_mul (algebraMap R (FractionRing R)), mul_assoc, map_mul e, ← smul_smul]
      exact hsmul c₁ h₂
    have hQsmul : ∀ (k : K₀) y, Q y → Q (k • y) := fun k y hy r => by
      obtain ⟨c, hc0, hc⟩ := hy (r * f k)
      refine ⟨c, hc0, ?_⟩
      rw [LinearMap.map_smulₛₗ, smul_smul, RingHom.comp_apply, ← map_mul, mul_assoc]
      exact hc
    have hQbase : ∀ F ∈ nabAtr (labLL0 D) B.w.lam (B.latAt h), Q (mapK s B.w.lam F) := fun F hF r => by
      obtain ⟨⟨a, d⟩, had⟩ := IsLocalization.surj (nonZeroDivisors R) r
      refine ⟨d, nonZeroDivisors.ne_zero d.2, ?_⟩
      rw [mul_comm (algebraMap R (FractionRing R) _) r, had, mapVV_mapK, hsO]
      refine hsmul a ?_
      change cfn B.w.lam (GlobalTheory.CoefModel.mapVV (embLL0 D) B.w.lam F) ∈ coefLatFn _ _ _ _ _
      rw [← coefFn_eq_cfn]
      exact Submodule.subset_span ⟨F, hF, rfl⟩
    have hspanLL : ∀ G ∈ Submodule.span (↥D.LL0) (nabAtr (labLL0 D) B.w.lam (B.latAt h) : Set (VV (↥D.LL0) B.w.lam)),
        Q (mapK s B.w.lam G) := by
      intro G hG
      induction hG using Submodule.span_induction with
      | mem F hF => exact hQbase F hF
      | zero => rw [map_zero]; exact hQ0
      | add _ _ _ _ h₁ h₂ => rw [map_add]; exact hQadd _ _ h₁ h₂
      | smul k _ _ h₁ => rw [LinearMap.map_smulₛₗ]; exact hQsmul _ _ h₁
    have hlat := Formalism.L2.DIV.nabAtr_isLattice (labLL0 D) B.w.lam (B.latAt h) hL
    have hg : ∀ i, Q (mapK s B.w.lam (bVV (↥D.LL0) B.w.lam i)) := fun i =>
      hspanLL _ (by rw [hlat.span_eq_top]; trivial)
    have hgind : LinearIndependent K₀ fun i => mapK s B.w.lam (bVV (↥D.LL0) B.w.lam i) := by
      refine Fintype.linearIndependent_iff.2 fun k hk i => ?_
      have h1 := congrArg (GlobalTheory.CoefModel.mapVV (e.comp f) B.w.lam) hk
      rw [map_sum, map_zero] at h1
      simp only [LinearMap.map_smulₛₗ, mapVV_mapK] at h1
      rw [hsO] at h1
      have := Fintype.linearIndependent_iff.1 (GlobalTheory.CoefModel.linearIndependent_mapVV (embLL0 D) B.w.lam)
        (fun i => (e.comp f) (k i)) h1 i
      exact (map_eq_zero_iff (e.comp f) (e.comp f).injective).1 this
    haveI : FiniteDimensional K₀ (VV K₀ B.w.lam) := Module.Finite.of_basis (bVV K₀ B.w.lam)
    have hgspan := hgind.span_eq_top_of_card_eq_finrank' (Module.finrank_eq_card_basis (bVV K₀ B.w.lam)).symm
    have hQall : ∀ y : VV K₀ B.w.lam, Q y := by
      intro y
      have hy : y ∈ Submodule.span K₀ (Set.range fun i => mapK s B.w.lam (bVV (↥D.LL0) B.w.lam i)) := by
        rw [hgspan]; trivial
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨i, rfl⟩ := hy
        exact hg i
      | zero => exact hQ0
      | add _ _ _ _ h₁ h₂ => exact hQadd _ _ h₁ h₂
      | smul k _ _ h₁ => exact hQsmul _ _ h₁
    choose cx hcx0 hcx using fun x => hQall (c₀ x) (b₁.repr w x)
    refine ⟨∏ x, cx x, Finset.prod_ne_zero_iff.2 fun x _ => hcx0 x, ?_⟩
    refine (mem_coefLat_iff B _ _ _ h _).2 ⟨hΨ1 _, ?_⟩
    change harmFn T.rank B.w B.F.BS (Ψ (Ω _)) ∈ _
    rw [hΨ2]
    change Ω _ ∈ Lat
    rw [show Ω (algebraMap R (FractionRing R) (∏ x, cx x) • w) =
      sumMap e b₁ v (algebraMap R (FractionRing R) (∏ x, cx x) • w) from rfl, sumMap_apply]
    refine Submodule.sum_mem _ fun x _ => ?_
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
    have e1 : algebraMap R (FractionRing R) (∏ x, cx x) * b₁.repr w x =
        algebraMap R (FractionRing R) (∏ x' ∈ Finset.univ.erase x, cx x') *
          (algebraMap R (FractionRing R) (cx x) * b₁.repr w x) := by
      rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ x), map_mul, mul_assoc]
    rw [e1, map_mul e, ← smul_smul]
    exact hsmul _ (hcx x)

end GlobalTheory.MtRead.WtEmb

end
