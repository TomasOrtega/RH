import Mathlib
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SummandsContRep
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.FixedOpen

open MeasureTheory Set Filter Topology Function
open scoped InnerProductSpace

namespace GroundTheory.Automorphic

noncomputable section

set_option linter.unusedSectionVars false

namespace CuspidalSpectrum

open AutomorphicForm RightCosetSpace Reduction

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

local notation "Γ₁" => Reduction.rationalGLOne K n

variable (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]

def CuspL2 : Type _ := cuspidalL2 μ

instance : NormedAddCommGroup (CuspL2 μ) := inferInstanceAs (NormedAddCommGroup (cuspidalL2 μ))

instance : InnerProductSpace ℂ (CuspL2 μ) := inferInstanceAs (InnerProductSpace ℂ (cuspidalL2 μ))

instance : CompleteSpace (CuspL2 μ) := inferInstanceAs (CompleteSpace (cuspidalL2 μ))

def toLp : CuspL2 μ →L[ℂ] Lp ℂ 2 (quotientMeasure Γ₁ μ) := (cuspidalL2 μ).subtypeL

/- English proof (translation)
The claim follows from `(show cuspidalL2 μ from v).2`.
-/
theorem toLp_mem (v : CuspL2 μ) : toLp μ v ∈ cuspidalL2 μ := (show cuspidalL2 μ from v).2

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem norm_toLp (v : CuspL2 μ) : ‖toLp μ v‖ = ‖v‖ := rfl

/- English proof (translation)
The claim follows from `Subtype.val_injective`.
-/
theorem toLp_injective : Function.Injective (toLp μ) := Subtype.val_injective

def cuspRepT : UnitaryRep (normOneGL K n) (CuspL2 μ) := cuspRep μ

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem toLp_cuspRepT (g : normOneGL K n) (v : CuspL2 μ) :
    toLp μ (cuspRepT μ g v) = rightRegularRep Γ₁ μ g (toLp μ v) := rfl

/- English proof (translation)
Introduce `_ _` and use `rfl`.
-/
theorem toLp_mem_intertwiners : toLp μ ∈ (cuspRepT μ).intertwiners (rightRegularRep Γ₁ μ) :=
  fun _ _ => rfl

/- English proof (translation)
The claim follows from `congrArg (fun T => T v) (UnitaryRep.comp_integrated_of_mem_intertwiners (cuspRepT μ) μ (toLp_mem_intertwiners μ) f)`.
-/
theorem toLp_integrated (f : normOneGL K n →₁[μ] ℂ) (v : CuspL2 μ) :
    toLp μ ((cuspRepT μ).integrated μ f v) = (rightRegularRep Γ₁ μ).integrated μ f (toLp μ v) :=
  congrArg (fun T => T v)
    (UnitaryRep.comp_integrated_of_mem_intertwiners (cuspRepT μ) μ (toLp_mem_intertwiners μ) f)

def archURepT : UnitaryRep (archGroup K n) (CuspL2 μ) :=
  (cuspRepT μ).comapHom (archP K n) continuous_archP

def archRepT : BanachRep (archGroup K n) (CuspL2 μ) := BanachRep.ofUnitary (archURepT μ)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem archRepT_apply (a : archGroup K n) (v : CuspL2 μ) :
    archRepT μ a v = cuspRepT μ (archP K n a) v := rfl

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Establish `hle : Submodule.span ℂ (Set.range fun u : AdelicGLn.integralFiniteGL K n => (cuspRepT μ).comapHom (finOne K n) continuous_finOne u v) ≤ Submodule.span ℂ (Set.range fun k : (Reduction.maxCompact : Subgroup (AdelicGLn.AdelicGL K n)) => cuspRepT μ ⟨k, Reduction.maxCompact_le_normOne …`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨u, rfl⟩`. Conclude with `Submodule.subset_span ⟨⟨finEmb K n u, finEmb_mem_maxCompact u.2⟩, rfl⟩`. Establish `_` using `hv`.

Conclude with `UnitaryRep.exists_isOpen_forall_eq_of_finiteDimensional _ v (Submodule.finiteDimensional_of_le hle)`.
-/
theorem exists_isOpen_forall_cuspRepT_finOne_eq (v : CuspL2 μ)
    (hv : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k :
      (Reduction.maxCompact : Subgroup (AdelicGLn.AdelicGL K n)) =>
        cuspRepT μ ⟨k, Reduction.maxCompact_le_normOneGL k.2⟩ v))) :
    ∃ U : Subgroup (AdelicGLn.integralFiniteGL K n),
      IsOpen (U : Set (AdelicGLn.integralFiniteGL K n)) ∧ ∀ u ∈ U, cuspRepT μ (finOne K n u) v = v := by
  have hle : Submodule.span ℂ (Set.range fun u : AdelicGLn.integralFiniteGL K n =>
      (cuspRepT μ).comapHom (finOne K n) continuous_finOne u v) ≤
      Submodule.span ℂ (Set.range fun k : (Reduction.maxCompact : Subgroup (AdelicGLn.AdelicGL K n)) =>
        cuspRepT μ ⟨k, Reduction.maxCompact_le_normOneGL k.2⟩ v) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨u, rfl⟩
    exact Submodule.subset_span ⟨⟨finEmb K n u, finEmb_mem_maxCompact u.2⟩, rfl⟩
  have _ := hv
  exact UnitaryRep.exists_isOpen_forall_eq_of_finiteDimensional _ v
    (Submodule.finiteDimensional_of_le hle)

variable (ν : Measure (archGroup K n)) [ν.IsHaarMeasure]

/- English proof (translation)
The claim follows from `(hγ.smul ((archRepT μ).continuous_orbit w)).integrable_of_hasCompactSupport hγc.smul_right`.
-/
theorem integrable_smul_archRepT {γ : archGroup K n → ℂ} (hγ : Continuous γ)
    (hγc : HasCompactSupport γ) (w : CuspL2 μ) :
    Integrable (fun a => γ a • archRepT μ a w) ν :=
  (hγ.smul ((archRepT μ).continuous_orbit w)).integrable_of_hasCompactSupport hγc.smul_right

/- English proof (translation)
The claim follows from `((toLp μ).integral_comp_comm (integrable_smul_archRepT μ ν hγ hγc w)).symm.trans (integral_congr_ae (Eventually.of_forall fun a => (toLp μ).map_smul (γ a) _))`.
-/
theorem toLp_integrated_archRepT {γ : archGroup K n → ℂ} (hγ : Continuous γ)
    (hγc : HasCompactSupport γ) (w : CuspL2 μ) :
    toLp μ ((archRepT μ).integrated ν γ w) =
      ∫ a, γ a • rightRegularRep Γ₁ μ (archP K n a) (toLp μ w) ∂ν :=
  ((toLp μ).integral_comp_comm (integrable_smul_archRepT μ ν hγ hγc w)).symm.trans
    (integral_congr_ae (Eventually.of_forall fun a => (toLp μ).map_smul (γ a) _))

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Use `isFiniteMeasure_quotientMeasure (K := K) (n := n) μ` as an intermediate fact. Take `⟨S, hS⟩ : ∃ S, S = tsupport γ` from `⟨_, rfl⟩`. Establish `hSc : IsCompact S` using `hS ▸ hγc.isCompact`. Establish `hWc : Continuous W` using `hW.1`. Establish `hpc : Continuous (archP K n)` using `continuous_archP`.

Establish `hJ : Continuous (uncurry fun (y : normOneGL K n) (a : archGroup K n) => γ a * W (y * archP K n a))` using `(hγ.comp continuous_snd).mul (hWc.comp (continuous_fst.mul (hpc.comp continuous_snd)))`. Establish `hset : ∀ y, ∫ a, γ a * W (y * archP K n a) ∂ν = ∫ a in S, γ a * W (y * archP K n a) ∂ν`. Introduce `y`. Use `(setIntegral_eq_integral_of_forall_compl_eq_zero fun a ha => ?_).symm` and prove the remaining obligations. Establish `h0 : γ a = 0` using `image_eq_zero_of_notMem_tsupport (by rw [← hS]; exact ha)`.

Rewrite using `[h0, zero_mul]`. Take `⟨Ψ, hΨ⟩ : ∃ Ψ : normOneGL K n → ℂ, Ψ = fun y => ∫ a, γ a * W (y * archP K n a) ∂ν` from `⟨_, rfl⟩`. Establish `hΨc : Continuous Ψ`. Establish `: Ψ = fun y => ∫ a in S, γ a * W (y * archP K n a) ∂ν` using `hΨ.trans (funext hset)`. Rewrite using `[this]`.

Conclude with `continuous_parametric_integral_of_continuous hJ hSc`. Establish `hΨinv : ∀ γ₀ ∈ Γ₁, ∀ y, Ψ (γ₀ * y) = Ψ y`. Introduce `γ₀ hγ₀ y`. Rewrite using `[hΨ]`. Use `integral_congr_ae (Eventually.of_forall fun a => ?_)` and prove the remaining obligations.

Use `show γ a * W (γ₀ * y * archP K n a) = γ a * W (y * archP K n a)`. Rewrite using `[mul_assoc, hW.2.1 γ₀ hγ₀]`. Rewrite using `[← hΨ]`. Use `⟨hΨc, hΨinv, ?_⟩` and prove the remaining obligations. Take `⟨WQ, hWQ⟩ : ∃ WQ, WQ = quotFun W hW.2.1` from `⟨_, rfl⟩`.

Establish `hWQc : Continuous WQ` using `hWQ ▸ continuous_quotFun hW.2.1 hWc`. Establish `hWQb : ∀ x, ‖WQ x‖ ≤ C`. Introduce `x`. Take `⟨y, rfl⟩` from `mk_surjective Γ₁ x`. Rewrite using `[hWQ, quotFun_mk]`.

Conclude with `hWb y`. Take `⟨ΨQ, hΨQ⟩ : ∃ ΨQ, ΨQ = quotFun Ψ hΨinv` from `⟨_, rfl⟩`. Establish `hΨQ_eq : ∀ x, ΨQ x = ∫ a, γ a * WQ (rightMul Γ₁ (archP K n a) x) ∂ν`. Introduce `x`. Take `⟨y, rfl⟩` from `mk_surjective Γ₁ x`.

Rewrite using `[hΨQ, quotFun_mk, hΨ, hWQ]`. Simplify using `only [rightMul_mk, quotFun_mk]`. Establish `hγi : Integrable γ ν` using `hγ.integrable_of_hasCompactSupport hγc`. Establish `hC0 : 0 ≤ C` using `(norm_nonneg _).trans (hWb 1)`. Establish `hJQ : Continuous (uncurry fun (a : archGroup K n) (x : RightCosetSpace Γ₁) => γ a * WQ (rightMul Γ₁ (archP K n a) x))`.

Establish `hr : Continuous fun p : archGroup K n × RightCosetSpace Γ₁ => rightMul Γ₁ (archP K n p.1) p.2`. Establish `h1 : Continuous fun p : RightCosetSpace Γ₁ × normOneGL K n => rightMul Γ₁ p.2 p.1` using `continuous_rightMul_prod Γ₁`. Establish `h2 : Continuous fun p : archGroup K n × RightCosetSpace Γ₁ => (p.2, archP K n p.1)` using `continuous_snd.prodMk (hpc.comp continuous_fst)`. Establish `h3` using `h1.comp h2`. Conclude with `h3`.

Establish `h4` using `(hγ.comp continuous_fst).mul (hWQc.comp hr)`. Conclude with `h4`. Establish `hint : ∀ s : Set (RightCosetSpace Γ₁), Integrable (uncurry fun (a : archGroup K n) (x : RightCosetSpace Γ₁) => γ a * WQ (rightMul Γ₁ (archP K n a) x)) (ν.prod ((quotientMeasure Γ₁ μ).restrict s))`. Introduce `s`. Use `Integrable.mono' ((hγi.norm.mul_prod (integrable_const C))) hJQ.aestronglyMeasurable (Eventually.of_forall fun p => ?_)` and prove the remaining obligations.

Take `⟨a, x⟩` from `p`. Use `show ‖γ a * WQ (rightMul Γ₁ (archP K n a) x)‖ ≤ ‖γ a‖ * C`. Rewrite using `[norm_mul]`. Conclude with `mul_le_mul_of_nonneg_left (hWQb _) (norm_nonneg _)`. Establish `hΨQi : Integrable ΨQ (quotientMeasure Γ₁ μ)`.

Use `(hint univ).integral_prod_right` as an intermediate fact. Rewrite `this` using `[Measure.restrict_univ]`. Conclude with `this.congr (Eventually.of_forall fun x => (hΨQ_eq x).symm)`. Take `⟨V, hV⟩ : ∃ V : Lp ℂ 2 (quotientMeasure Γ₁ μ), V = ∫ a, γ a • rightRegularRep Γ₁ μ (archP K n a) (toLp μ w) ∂ν` from `⟨_, rfl⟩`. Establish `hVi : Integrable (fun a => γ a • rightRegularRep Γ₁ μ (archP K n a) (toLp μ w)) ν` using `(hγ.smul (((rightRegularRep Γ₁ μ).continuous_orbit _).comp hpc)).integrable_of_hasCompactSupport hγc.smul_right`.

Establish `hwQ : (toLp μ w : RightCosetSpace Γ₁ → ℂ) =ᵐ[quotientMeasure Γ₁ μ] WQ` using `hWQ ▸ hW.ae_eq_quotFun`. Establish `hVeq : (V : RightCosetSpace Γ₁ → ℂ) =ᵐ[quotientMeasure Γ₁ μ] ΨQ`. Use `ae_eq_of_forall_setIntegral_eq_of_sigmaFinite (fun s _ _ => ((Lp.memLp _).integrable one_le_two).integrableOn) (fun s _ _ => hΨQi.integrableOn) fun s hs hμs => ?_` and prove the remaining obligations. Rewrite using `[← L2.inner_indicatorConstLp_one hs hμs.ne, hV, ← integral_inner hVi]`. Establish `hcoef : ∀ a, ⟪indicatorConstLp 2 hs hμs.ne (1 : ℂ), γ a • rightRegularRep Γ₁ μ (archP K n a) (toLp μ w)⟫_ℂ = ∫ x in s, γ a * WQ (rightMul Γ₁ (archP K n a) x) ∂quotientMeasure Γ₁ μ`.

Introduce `a`. Rewrite using `[inner_smul_right, L2.inner_indicatorConstLp_one, ← integral_const_mul]`. Use `setIntegral_congr_ae hs ?_` and prove the remaining obligations. Establish `h1` using `coeFn_rightRegularRep Γ₁ μ (archP K n a) (toLp μ w)`. Establish `h2` using `(measurePreserving_rightMul μ (archP K n a)).quasiMeasurePreserving.ae_eq_comp hwQ`.

Use `filter_upwards [h1, h2] with x hx1 hx2`. Introduce `_`. Simplify using `only [Function.comp_apply] at hx2`. Conclude with `congrArg (γ a * ·) (hx1.trans hx2)`. Repeatedly rewrite using `[hcoef]`.

Use `(integral_integral_swap (hint s)).trans ?_` and prove the remaining obligations. Conclude with `setIntegral_congr_fun hs fun x _ => (hΨQ_eq x).symm`. Establish `hcoe` using `(toLp_integrated_archRepT μ ν hγ hγc w).trans hV.symm`. Use `filter_upwards [(quasiMeasurePreserving_mk Γ₁ μ).ae_eq_comp hVeq] with y hy`. Simplify using `only [Function.comp_apply] at hy`.

Use `(congrArg (fun f : Lp ℂ 2 (quotientMeasure Γ₁ μ) => (f : RightCosetSpace Γ₁ → ℂ) (mk Γ₁ y)) hcoe).trans ?_` and prove the remaining obligations. Use `hy.trans ?_` and prove the remaining obligations. Rewrite using `[hΨQ, quotFun_mk]`.
-/
theorem isContRep_integrated_archRepT {w : CuspL2 μ} {W : normOneGL K n → ℂ}
    (hW : IsContRep μ (toLp μ w) W) {C : ℝ} (hWb : ∀ y, ‖W y‖ ≤ C)
    {γ : archGroup K n → ℂ} (hγ : Continuous γ) (hγc : HasCompactSupport γ) :
    IsContRep μ (toLp μ ((archRepT μ).integrated ν γ w))
      (fun y => ∫ a, γ a * W (y * archP K n a) ∂ν) := by
  have := isFiniteMeasure_quotientMeasure (K := K) (n := n) μ
  obtain ⟨S, hS⟩ : ∃ S, S = tsupport γ := ⟨_, rfl⟩
  have hSc : IsCompact S := hS ▸ hγc.isCompact
  have hWc : Continuous W := hW.1
  have hpc : Continuous (archP K n) := continuous_archP

  have hJ : Continuous (uncurry fun (y : normOneGL K n) (a : archGroup K n) =>
      γ a * W (y * archP K n a)) :=
    (hγ.comp continuous_snd).mul (hWc.comp (continuous_fst.mul (hpc.comp continuous_snd)))
  have hset : ∀ y, ∫ a, γ a * W (y * archP K n a) ∂ν = ∫ a in S, γ a * W (y * archP K n a) ∂ν := by
    intro y
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun a ha => ?_).symm
    have h0 : γ a = 0 := image_eq_zero_of_notMem_tsupport (by rw [← hS]; exact ha)
    rw [h0, zero_mul]
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : normOneGL K n → ℂ, Ψ = fun y => ∫ a, γ a * W (y * archP K n a) ∂ν :=
    ⟨_, rfl⟩
  have hΨc : Continuous Ψ := by
    have : Ψ = fun y => ∫ a in S, γ a * W (y * archP K n a) ∂ν := hΨ.trans (funext hset)
    rw [this]
    exact continuous_parametric_integral_of_continuous hJ hSc
  have hΨinv : ∀ γ₀ ∈ Γ₁, ∀ y, Ψ (γ₀ * y) = Ψ y := by
    intro γ₀ hγ₀ y
    rw [hΨ]
    refine integral_congr_ae (Eventually.of_forall fun a => ?_)
    show γ a * W (γ₀ * y * archP K n a) = γ a * W (y * archP K n a)
    rw [mul_assoc, hW.2.1 γ₀ hγ₀]
  rw [← hΨ]
  refine ⟨hΨc, hΨinv, ?_⟩

  obtain ⟨WQ, hWQ⟩ : ∃ WQ, WQ = quotFun W hW.2.1 := ⟨_, rfl⟩
  have hWQc : Continuous WQ := hWQ ▸ continuous_quotFun hW.2.1 hWc
  have hWQb : ∀ x, ‖WQ x‖ ≤ C := by
    intro x
    obtain ⟨y, rfl⟩ := mk_surjective Γ₁ x
    rw [hWQ, quotFun_mk]
    exact hWb y
  obtain ⟨ΨQ, hΨQ⟩ : ∃ ΨQ, ΨQ = quotFun Ψ hΨinv := ⟨_, rfl⟩
  have hΨQ_eq : ∀ x, ΨQ x = ∫ a, γ a * WQ (rightMul Γ₁ (archP K n a) x) ∂ν := by
    intro x
    obtain ⟨y, rfl⟩ := mk_surjective Γ₁ x
    rw [hΨQ, quotFun_mk, hΨ, hWQ]
    simp only [rightMul_mk, quotFun_mk]
  have hγi : Integrable γ ν := hγ.integrable_of_hasCompactSupport hγc
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hWb 1)

  have hJQ : Continuous (uncurry fun (a : archGroup K n) (x : RightCosetSpace Γ₁) =>
      γ a * WQ (rightMul Γ₁ (archP K n a) x)) := by
    have hr : Continuous fun p : archGroup K n × RightCosetSpace Γ₁ =>
        rightMul Γ₁ (archP K n p.1) p.2 := by
      have h1 : Continuous fun p : RightCosetSpace Γ₁ × normOneGL K n => rightMul Γ₁ p.2 p.1 :=
        continuous_rightMul_prod Γ₁
      have h2 : Continuous fun p : archGroup K n × RightCosetSpace Γ₁ => (p.2, archP K n p.1) :=
        continuous_snd.prodMk (hpc.comp continuous_fst)
      have h3 := h1.comp h2
      exact h3
    have h4 := (hγ.comp continuous_fst).mul (hWQc.comp hr)
    exact h4
  have hint : ∀ s : Set (RightCosetSpace Γ₁), Integrable (uncurry fun (a : archGroup K n)
      (x : RightCosetSpace Γ₁) => γ a * WQ (rightMul Γ₁ (archP K n a) x))
        (ν.prod ((quotientMeasure Γ₁ μ).restrict s)) := by
    intro s
    refine Integrable.mono' ((hγi.norm.mul_prod (integrable_const C))) hJQ.aestronglyMeasurable
      (Eventually.of_forall fun p => ?_)
    obtain ⟨a, x⟩ := p
    show ‖γ a * WQ (rightMul Γ₁ (archP K n a) x)‖ ≤ ‖γ a‖ * C
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hWQb _) (norm_nonneg _)
  have hΨQi : Integrable ΨQ (quotientMeasure Γ₁ μ) := by
    have := (hint univ).integral_prod_right
    rw [Measure.restrict_univ] at this
    exact this.congr (Eventually.of_forall fun x => (hΨQ_eq x).symm)

  obtain ⟨V, hV⟩ : ∃ V : Lp ℂ 2 (quotientMeasure Γ₁ μ),
      V = ∫ a, γ a • rightRegularRep Γ₁ μ (archP K n a) (toLp μ w) ∂ν :=
    ⟨_, rfl⟩
  have hVi : Integrable (fun a => γ a • rightRegularRep Γ₁ μ (archP K n a)
      (toLp μ w)) ν :=
    (hγ.smul (((rightRegularRep Γ₁ μ).continuous_orbit _).comp hpc)).integrable_of_hasCompactSupport
      hγc.smul_right
  have hwQ : (toLp μ w : RightCosetSpace Γ₁ → ℂ) =ᵐ[quotientMeasure Γ₁ μ] WQ := hWQ ▸ hW.ae_eq_quotFun
  have hVeq : (V : RightCosetSpace Γ₁ → ℂ) =ᵐ[quotientMeasure Γ₁ μ] ΨQ := by
    refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
      (fun s _ _ => ((Lp.memLp _).integrable one_le_two).integrableOn)
      (fun s _ _ => hΨQi.integrableOn) fun s hs hμs => ?_
    rw [← L2.inner_indicatorConstLp_one hs hμs.ne, hV, ← integral_inner hVi]
    have hcoef : ∀ a, ⟪indicatorConstLp 2 hs hμs.ne (1 : ℂ), γ a • rightRegularRep Γ₁ μ
        (archP K n a) (toLp μ w)⟫_ℂ =
        ∫ x in s, γ a * WQ (rightMul Γ₁ (archP K n a) x) ∂quotientMeasure Γ₁ μ := by
      intro a
      rw [inner_smul_right, L2.inner_indicatorConstLp_one, ← integral_const_mul]
      refine setIntegral_congr_ae hs ?_
      have h1 := coeFn_rightRegularRep Γ₁ μ (archP K n a) (toLp μ w)
      have h2 := (measurePreserving_rightMul μ (archP K n a)).quasiMeasurePreserving.ae_eq_comp hwQ
      filter_upwards [h1, h2] with x hx1 hx2
      intro _
      simp only [Function.comp_apply] at hx2
      exact congrArg (γ a * ·) (hx1.trans hx2)
    simp_rw [hcoef]
    refine (integral_integral_swap (hint s)).trans ?_
    exact setIntegral_congr_fun hs fun x _ => (hΨQ_eq x).symm
  have hcoe := (toLp_integrated_archRepT μ ν hγ hγc w).trans hV.symm
  filter_upwards [(quasiMeasurePreserving_mk Γ₁ μ).ae_eq_comp hVeq] with y hy
  simp only [Function.comp_apply] at hy
  refine (congrArg (fun f : Lp ℂ 2 (quotientMeasure Γ₁ μ) =>
    (f : RightCosetSpace Γ₁ → ℂ) (mk Γ₁ y)) hcoe).trans ?_
  refine hy.trans ?_
  rw [hΨQ, quotFun_mk]

end CuspidalSpectrum

end

end GroundTheory.Automorphic
