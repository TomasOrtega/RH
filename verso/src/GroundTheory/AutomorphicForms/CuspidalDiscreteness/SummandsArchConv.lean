import Mathlib
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SummandsBase
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SmoothingFinite

open MeasureTheory Set Filter Topology Function
open scoped InnerProductSpace ContDiff

namespace GroundTheory.Automorphic

noncomputable section

set_option linter.unusedSectionVars false

namespace CuspidalSpectrum

open Reduction AutomorphicForm

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

section Integrated

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (σ : UnitaryRep (normOneGL K n) H)
  (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]
  (ν : Measure (ArchUnits K n)) [ν.IsHaarMeasure]
  {β : ArchMatrix K n → ℝ}

/- English proof (translation)
Rewrite using `[UnitaryRep.inner_integrated]`. Use `integral_congr_ae ((MemLp.coeFn_toLp (μ := μ) (f.continuous.memLp_of_hasCompactSupport (p := 1) f.hasCompactSupport)).mono fun g hg => ?_)` and prove the remaining obligations. Simplify using `only`. Conclude with `congrArg (· * ⟪w, σ g u⟫_ℂ) hg`.
-/
theorem inner_integrated_ccToL1_eq (f : CompactlySupportedContinuousMap (normOneGL K n) ℂ)
    (w u : H) :
    ⟪w, σ.integrated μ (UnitaryRep.ccToL1 μ f) u⟫_ℂ = ∫ g, f g * ⟪w, σ g u⟫_ℂ ∂μ := by
  rw [UnitaryRep.inner_integrated]
  refine integral_congr_ae ((MemLp.coeFn_toLp (μ := μ)
    (f.continuous.memLp_of_hasCompactSupport (p := 1) f.hasCompactSupport)).mono fun g hg => ?_)
  dsimp only
  exact congrArg (· * ⟪w, σ g u⟫_ℂ) hg

/- English proof (translation)
Use `((Complex.continuous_ofReal.comp (hβ.comp Units.continuous_val)).smul ((σ.continuous_orbit u).comp continuous_archProj)).integrable_of_hasCompactSupport ?_` and prove the remaining obligations. Use `HasCompactSupport.intro (isCompact_unitsSupport hβc hβu) fun A hA => ?_` and prove the remaining obligations. Simplify using `[image_eq_zero_of_notMem_tsupport (f := β) hA]`.
-/
theorem integrable_smul_archProj (hβ : Continuous β) (hβc : HasCompactSupport β)
    (hβu : tsupport β ⊆ range (Units.val : ArchUnits K n → ArchMatrix K n)) (u : H) :
    Integrable (fun A : ArchUnits K n => (β A : ℂ) • σ (archProj K n A) u) ν := by
  refine ((Complex.continuous_ofReal.comp (hβ.comp Units.continuous_val)).smul
    ((σ.continuous_orbit u).comp continuous_archProj)).integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.intro (isCompact_unitsSupport hβc hβu) fun A hA => ?_
  simp [image_eq_zero_of_notMem_tsupport (f := β) hA]

/- English proof (translation)
Use `ext_inner_left ℂ fun w' => ?_` and prove the remaining obligations. Use `set u := σ.integrated μ (UnitaryRep.ccToL1 μ g) w with hu`. Rewrite using `[← integral_inner (integrable_smul_archProj σ ν hβ hβc hβu u) w']`. Use `set S : Set (ArchUnits K n) := (Units.val : ArchUnits K n → ArchMatrix K n) ⁻¹' tsupport β`. Establish `hS : IsCompact S` using `isCompact_unitsSupport hβc hβu`.

Use `set Φ : ArchUnits K n → normOneGL K n → ℂ := fun A x => (β A : ℂ) * g ((archProj K n A)⁻¹ * x) * ⟪w', σ x w⟫_ℂ with hΦ`. Establish `hcont : Continuous (uncurry Φ)` using `(((Complex.continuous_ofReal.comp (hβ.comp (Units.continuous_val.comp continuous_fst)))).mul (g.continuous.comp (((continuous_archProj.comp continuous_fst).inv).mul continuous_snd))).mul (continuous_const.inner ((σ.continuous_orbit w).comp continuous_snd))`. Establish `hsupp : HasCompactSupport (uncurry Φ)`. Use `HasCompactSupport.intro (hS.prod ((hS.image continuous_archProj).mul g.hasCompactSupport)) fun p hp => ?_` and prove the remaining obligations. Take `⟨A, x⟩` from `p`.

Use `show (β A : ℂ) * g ((archProj K n A)⁻¹ * x) * ⟪w', σ x w⟫_ℂ = 0`. Distinguish the cases in `h1 : A ∈ S`. Distinguish the cases in `h2 : (archProj K n A)⁻¹ * x ∈ tsupport (g : normOneGL K n → ℂ)`. Conclude with `absurd ⟨h1, ⟨archProj K n A, ⟨A, h1, rfl⟩, _, h2, mul_inv_cancel_left _ _⟩⟩ hp`. Rewrite using `[image_eq_zero_of_notMem_tsupport h2, mul_zero, zero_mul]`.

Establish `: β A = 0` using `image_eq_zero_of_notMem_tsupport (f := β) h1`. Rewrite using `[this, Complex.ofReal_zero, zero_mul, zero_mul]`. Establish `hint : Integrable (uncurry Φ) (ν.prod μ)` using `hcont.integrable_of_hasCompactSupport hsupp`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[inner_integrated_ccToL1_eq]`.

Both sides reduce to the same expression. Use `_ = ∫ x, ∫ A, Φ A x ∂ν ∂μ := by`. Use `integral_congr_ae (Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Conclude with `(integral_mul_const _ _).symm`. Use `_ = ∫ A, ∫ x, Φ A x ∂μ ∂ν := (integral_integral_swap hint).symm`.

Use `_ = ∫ A, ⟪w', (β A : ℂ) • σ (archProj K n A) u⟫_ℂ ∂ν := by`. Use `integral_congr_ae (Eventually.of_forall fun A => ?_)` and prove the remaining obligations. Simplify using `only`. Rewrite using `[← integral_mul_left_eq_self (fun x => Φ A x) (archProj K n A), inner_smul_right, UnitaryRep.inner_map_right, hu, inner_integrated_ccToL1_eq, ← integral_const_mul]`. Use `integral_congr_ae (Eventually.of_forall fun y => ?_)` and prove the remaining obligations.

Simplify using `only [hΦ, inv_mul_cancel_left]`. Rewrite using `[UnitaryRep.inner_map_left, inv_inv, ← UnitaryRep.map_mul_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem integrated_archConv (hβ : Continuous β) (hβc : HasCompactSupport β)
    (hβu : tsupport β ⊆ range (Units.val : ArchUnits K n → ArchMatrix K n))
    (g : CompactlySupportedContinuousMap (normOneGL K n) ℂ) (w : H) :
    σ.integrated μ (UnitaryRep.ccToL1 μ (archConv ν hβ hβc hβu g)) w =
      ∫ A, (β A : ℂ) • σ (archProj K n A) (σ.integrated μ (UnitaryRep.ccToL1 μ g) w) ∂ν := by
  refine ext_inner_left ℂ fun w' => ?_
  set u := σ.integrated μ (UnitaryRep.ccToL1 μ g) w with hu
  rw [← integral_inner (integrable_smul_archProj σ ν hβ hβc hβu u) w']
  set S : Set (ArchUnits K n) := (Units.val : ArchUnits K n → ArchMatrix K n) ⁻¹' tsupport β
  have hS : IsCompact S := isCompact_unitsSupport hβc hβu
  set Φ : ArchUnits K n → normOneGL K n → ℂ :=
    fun A x => (β A : ℂ) * g ((archProj K n A)⁻¹ * x) * ⟪w', σ x w⟫_ℂ with hΦ
  have hcont : Continuous (uncurry Φ) :=
    (((Complex.continuous_ofReal.comp (hβ.comp (Units.continuous_val.comp continuous_fst)))).mul
      (g.continuous.comp (((continuous_archProj.comp continuous_fst).inv).mul continuous_snd))).mul
      (continuous_const.inner ((σ.continuous_orbit w).comp continuous_snd))
  have hsupp : HasCompactSupport (uncurry Φ) := by
    refine HasCompactSupport.intro
      (hS.prod ((hS.image continuous_archProj).mul g.hasCompactSupport)) fun p hp => ?_
    obtain ⟨A, x⟩ := p
    show (β A : ℂ) * g ((archProj K n A)⁻¹ * x) * ⟪w', σ x w⟫_ℂ = 0
    by_cases h1 : A ∈ S
    · by_cases h2 : (archProj K n A)⁻¹ * x ∈ tsupport (g : normOneGL K n → ℂ)
      · exact absurd ⟨h1, ⟨archProj K n A, ⟨A, h1, rfl⟩, _, h2, mul_inv_cancel_left _ _⟩⟩ hp
      · rw [image_eq_zero_of_notMem_tsupport h2, mul_zero, zero_mul]
    · have : β A = 0 := image_eq_zero_of_notMem_tsupport (f := β) h1
      rw [this, Complex.ofReal_zero, zero_mul, zero_mul]
  have hint : Integrable (uncurry Φ) (ν.prod μ) := hcont.integrable_of_hasCompactSupport hsupp
  calc ⟪w', σ.integrated μ (UnitaryRep.ccToL1 μ (archConv ν hβ hβc hβu g)) w⟫_ℂ
      = ∫ x, archConvFun ν β g x * ⟪w', σ x w⟫_ℂ ∂μ := by
        rw [inner_integrated_ccToL1_eq]
        rfl
    _ = ∫ x, ∫ A, Φ A x ∂ν ∂μ := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        exact (integral_mul_const _ _).symm
    _ = ∫ A, ∫ x, Φ A x ∂μ ∂ν := (integral_integral_swap hint).symm
    _ = ∫ A, ⟪w', (β A : ℂ) • σ (archProj K n A) u⟫_ℂ ∂ν := by
        refine integral_congr_ae (Eventually.of_forall fun A => ?_)
        dsimp only
        rw [← integral_mul_left_eq_self (fun x => Φ A x) (archProj K n A), inner_smul_right,
          UnitaryRep.inner_map_right, hu, inner_integrated_ccToL1_eq, ← integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        simp only [hΦ, inv_mul_cancel_left]
        rw [UnitaryRep.inner_map_left, inv_inv, ← UnitaryRep.map_mul_apply]
        ring

end Integrated

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[finAvg_apply]`. Use `compactSpace_of_isOpen U hU` as an intermediate fact. Establish `e : ∀ u : U, g ((finOne K n (u : AdelicGLn.integralFiniteGL K n))⁻¹ * x) = g x` using `fun u => by`. Rewrite using `[← map_inv]`.

Conclude with `hg _ (U.inv_mem u.2) x`. Use `show (∫ u : U, g ((finOne K n (u : AdelicGLn.integralFiniteGL K n))⁻¹ * x) ∂haarProb U) = g x`. Repeatedly rewrite using `[e]`. Simplify using the standard rewrite rules.
-/
theorem finAvg_eq_self (U : Subgroup (AdelicGLn.integralFiniteGL K n))
    (hU : IsOpen (U : Set (AdelicGLn.integralFiniteGL K n)))
    {g : CompactlySupportedContinuousMap (normOneGL K n) ℂ}
    (hg : ∀ u ∈ U, ∀ x, g (finOne K n u * x) = g x) : finAvg U hU g = g := by
  ext x
  rw [finAvg_apply]
  have := compactSpace_of_isOpen U hU
  have e : ∀ u : U, g ((finOne K n (u : AdelicGLn.integralFiniteGL K n))⁻¹ * x) = g x := fun u => by
    rw [← map_inv]
    exact hg _ (U.inv_mem u.2) x
  show (∫ u : U, g ((finOne K n (u : AdelicGLn.integralFiniteGL K n))⁻¹ * x) ∂haarProb U) = g x
  simp_rw [e]
  simp

variable (K n) in

def archGroupEquiv : archGroup K n ≃ₜ* ArchUnits K n where
  toMulEquiv := Subgroup.topEquiv
  continuous_toFun := continuous_subtype_val
  continuous_invFun := continuous_id.subtype_mk _

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem archGroupEquiv_apply (a : archGroup K n) :
    archGroupEquiv K n a = (a : ArchUnits K n) := rfl

/- English proof (translation)
The claim follows from `(archGroupEquiv K n).isHaarMeasure_map ν'`.
-/
theorem isHaarMeasure_map_val (ν' : Measure (archGroup K n)) [ν'.IsHaarMeasure] :
    (ν'.map (fun a : archGroup K n => (a : ArchUnits K n))).IsHaarMeasure :=
  (archGroupEquiv K n).isHaarMeasure_map ν'

/- English proof (translation)
The claim follows from `(MeasurableEmbedding.subtype_coe MeasurableSet.univ).integral_map f`.
-/
theorem integral_map_val {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ν' : Measure (archGroup K n)) (f : ArchUnits K n → E) :
    ∫ A, f A ∂(ν'.map (fun a : archGroup K n => (a : ArchUnits K n))) = ∫ a, f a ∂ν' :=
  (MeasurableEmbedding.subtype_coe MeasurableSet.univ).integral_map f

section Conversion

variable (K n) in
open scoped Classical in

def matExt (κ : archGroup K n → ℂ) (M : ArchMatrix K n) : ℂ :=
  if h : IsUnit M then κ ⟨h.unit, Subgroup.mem_top _⟩ else 0

/- English proof (translation)
Unfold `matExt`. Rewrite using `[dif_pos (a : ArchUnits K n).isUnit]`. Use `congr 1`. Conclude with `Subtype.ext (IsUnit.unit_of_val_units _)`.
-/
theorem matExt_val (κ : archGroup K n → ℂ) (a : archGroup K n) :
    matExt K n κ ((a : ArchUnits K n) : ArchMatrix K n) = κ a := by
  unfold matExt
  rw [dif_pos (a : ArchUnits K n).isUnit]
  congr 1
  exact Subtype.ext (IsUnit.unit_of_val_units _)

/- English proof (translation)
Unfold `matExt`. Use `split_ifs with h`. Assume the negation of the conclusion as `h0`. Conclude with `hM ⟨⟨h.unit, Subgroup.mem_top _⟩, subset_tsupport _ h0, rfl⟩`. Both sides reduce to the same expression.
-/
theorem matExt_eq_zero {κ : archGroup K n → ℂ} {M : ArchMatrix K n}
    (hM : M ∉ (fun a : archGroup K n => ((a : ArchUnits K n) : ArchMatrix K n)) '' tsupport κ) :
    matExt K n κ M = 0 := by
  unfold matExt
  split_ifs with h
  · by_contra h0
    exact hM ⟨⟨h.unit, Subgroup.mem_top _⟩, subset_tsupport _ h0, rfl⟩
  · rfl

/- English proof (translation)
Use `set h := isExpLieAlgebra K n with hh`. Use `set S : Set (ArchMatrix K n) := (fun a : archGroup K n => ((a : ArchUnits K n) : ArchMatrix K n)) '' tsupport κ with hSdef`. Establish `hS : IsCompact S` using `hκ.2.isCompact.image (Units.continuous_val.comp continuous_subtype_val)`. Use `set e := expPartialHomeomorph ℝ (ArchMatrix K n) with he`. Set `ι : ArchMatrix K n →L[ℝ] archLie K n` to `LinearMap.toContinuousLinearMap (LinearMap.codRestrict ⊤ LinearMap.id fun _ => Submodule.mem_top)`.

Use `contDiff_iff_contDiffAt.2 fun M₀ => ?_` and prove the remaining obligations. Distinguish the cases in `hM₀ : IsUnit M₀`. Use `set g : archGroup K n := ⟨hM₀.unit, Subgroup.mem_top _⟩ with hg set gi : ArchMatrix K n := ((hM₀.unit⁻¹ : ArchUnits K n) : ArchMatrix K n) with hgi`. Establish `hgix₀ : gi * M₀ = 1`. Rewrite using `[hgi]`.

Conclude with `hM₀.val_inv_mul`. Use `set V : Set (ArchMatrix K n) := {M | gi * M ∈ e.target} with hV`. Establish `hVo : IsOpen V` using `e.open_target.preimage (continuous_const.mul continuous_id)`. Establish `hM₀V : M₀ ∈ V` using `by show gi * M₀ ∈ e.target`. Rewrite using `[hgix₀]`.

Conclude with `one_mem_expPartialHomeomorph_target ℝ _`. Establish `hmul : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun M : ArchMatrix K n => gi * M` using `(ContinuousLinearMap.mul ℝ (ArchMatrix K n) gi).contDiff`. Establish `hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun M => κ (g * h.expG (ι (e.symm (gi * M))))) V` using `((h.isSmoothFun_iff).1 hκ.1 g).comp_contDiffOn (ι.contDiff.comp_contDiffOn ((contDiffOn_expPartialHomeomorph_symm ℝ _).comp hmul.contDiffOn fun M hM => hM))`. Use `(hsm.congr fun M hM => ?_).contDiffAt (hVo.mem_nhds hM₀V)` and prove the remaining obligations. Establish `hy : gi * M ∈ e.target` using `hM`.

Establish `hexpy : NormedSpace.exp (e.symm (gi * M)) = gi * M` using `e.right_inv hy`. Establish `hMeq : M = ((g : ArchUnits K n) : ArchMatrix K n) * NormedSpace.exp (e.symm (gi * M))`. Rewrite using `[hexpy, ← mul_assoc, hg]`. Use `show M = ((hM₀.unit : ArchUnits K n) : ArchMatrix K n) * gi * M`. Rewrite using `[hgi, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]`.

Establish `hMu : IsUnit M`. Rewrite using `[hMeq]`. Conclude with `(g : ArchUnits K n).isUnit.mul (h.expG (ι (e.symm (gi * M))) : ArchUnits K n).isUnit`. Unfold `matExt`. Rewrite using `[dif_pos hMu]`.

Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Simplify using `only [IsUnit.unit_spec, Subgroup.coe_mul, Units.val_mul, IsExpLieAlgebra.coe_expG]`. Conclude with `hMeq`.

Establish `hnot : M₀ ∉ S`. Introduce and unpack `⟨a, -, ha⟩`. Conclude with `hM₀ (ha ▸ (a : ArchUnits K n).isUnit)`. Use `contDiffAt_const (c := (0 : ℂ)).congr_of_eventuallyEq ?_` and prove the remaining obligations. Use `filter_upwards [hS.isClosed.isOpen_compl.mem_nhds hnot] with M hM`.

Conclude with `matExt_eq_zero hM`.
-/
theorem contDiff_matExt {κ : archGroup K n → ℂ} (hκ : (isExpLieAlgebra K n).IsTestFunction κ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (matExt K n κ) := by
  set h := isExpLieAlgebra K n with hh
  set S : Set (ArchMatrix K n) :=
    (fun a : archGroup K n => ((a : ArchUnits K n) : ArchMatrix K n)) '' tsupport κ with hSdef
  have hS : IsCompact S := hκ.2.isCompact.image (Units.continuous_val.comp continuous_subtype_val)
  set e := expPartialHomeomorph ℝ (ArchMatrix K n) with he
  let ι : ArchMatrix K n →L[ℝ] archLie K n :=
    LinearMap.toContinuousLinearMap
      (LinearMap.codRestrict ⊤ LinearMap.id fun _ => Submodule.mem_top)
  refine contDiff_iff_contDiffAt.2 fun M₀ => ?_
  by_cases hM₀ : IsUnit M₀
  · set g : archGroup K n := ⟨hM₀.unit, Subgroup.mem_top _⟩ with hg
    set gi : ArchMatrix K n := ((hM₀.unit⁻¹ : ArchUnits K n) : ArchMatrix K n) with hgi
    have hgix₀ : gi * M₀ = 1 := by
      rw [hgi]
      exact hM₀.val_inv_mul
    set V : Set (ArchMatrix K n) := {M | gi * M ∈ e.target} with hV
    have hVo : IsOpen V := e.open_target.preimage (continuous_const.mul continuous_id)
    have hM₀V : M₀ ∈ V := by
      show gi * M₀ ∈ e.target
      rw [hgix₀]
      exact one_mem_expPartialHomeomorph_target ℝ _
    have hmul : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun M : ArchMatrix K n => gi * M :=
      (ContinuousLinearMap.mul ℝ (ArchMatrix K n) gi).contDiff
    have hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun M => κ (g * h.expG (ι (e.symm (gi * M))))) V :=
      ((h.isSmoothFun_iff).1 hκ.1 g).comp_contDiffOn (ι.contDiff.comp_contDiffOn
        ((contDiffOn_expPartialHomeomorph_symm ℝ _).comp hmul.contDiffOn fun M hM => hM))
    refine (hsm.congr fun M hM => ?_).contDiffAt (hVo.mem_nhds hM₀V)
    have hy : gi * M ∈ e.target := hM
    have hexpy : NormedSpace.exp (e.symm (gi * M)) = gi * M := e.right_inv hy
    have hMeq : M = ((g : ArchUnits K n) : ArchMatrix K n) * NormedSpace.exp (e.symm (gi * M)) := by
      rw [hexpy, ← mul_assoc, hg]
      show M = ((hM₀.unit : ArchUnits K n) : ArchMatrix K n) * gi * M
      rw [hgi, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
    have hMu : IsUnit M := by
      rw [hMeq]
      exact (g : ArchUnits K n).isUnit.mul (h.expG (ι (e.symm (gi * M))) : ArchUnits K n).isUnit
    unfold matExt
    rw [dif_pos hMu]
    congr 1
    apply Subtype.ext
    apply Units.ext
    simp only [IsUnit.unit_spec, Subgroup.coe_mul, Units.val_mul, IsExpLieAlgebra.coe_expG]
    exact hMeq
  · have hnot : M₀ ∉ S := by
      rintro ⟨a, -, ha⟩
      exact hM₀ (ha ▸ (a : ArchUnits K n).isUnit)
    refine contDiffAt_const (c := (0 : ℂ)).congr_of_eventuallyEq ?_
    filter_upwards [hS.isClosed.isOpen_compl.mem_nhds hnot] with M hM
    exact matExt_eq_zero hM

/- English proof (translation)
The claim follows from `HasCompactSupport.intro (hκ.isCompact.image (Units.continuous_val.comp continuous_subtype_val)) fun _ hM => matExt_eq_zero hM`.
-/
theorem hasCompactSupport_matExt {κ : archGroup K n → ℂ} (hκ : HasCompactSupport κ) :
    HasCompactSupport (matExt K n κ) :=
  HasCompactSupport.intro (hκ.isCompact.image (Units.continuous_val.comp continuous_subtype_val))
    fun _ hM => matExt_eq_zero hM

/- English proof (translation)
Use `set S : Set (ArchMatrix K n) := (fun a : archGroup K n => ((a : ArchUnits K n) : ArchMatrix K n)) '' tsupport κ`. Establish `hS : IsCompact S` using `hκ.isCompact.image (Units.continuous_val.comp continuous_subtype_val)`. Establish `hsub : tsupport f ⊆ S`. Use `closure_minimal (fun M hM => ?_) hS.isClosed` and prove the remaining obligations. Assume the negation of the conclusion as `hMS`.

Conclude with `hM (hf M (matExt_eq_zero hMS))`. Use `hsub.trans ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨a, -, rfl⟩`. Conclude with `⟨a, rfl⟩`.
-/
theorem tsupport_subset_of_matExt {κ : archGroup K n → ℂ} (hκ : HasCompactSupport κ)
    {f : ArchMatrix K n → ℝ} (hf : ∀ M, matExt K n κ M = 0 → f M = 0) :
    tsupport f ⊆ range (Units.val : ArchUnits K n → ArchMatrix K n) := by
  set S : Set (ArchMatrix K n) :=
    (fun a : archGroup K n => ((a : ArchUnits K n) : ArchMatrix K n)) '' tsupport κ
  have hS : IsCompact S := hκ.isCompact.image (Units.continuous_val.comp continuous_subtype_val)
  have hsub : tsupport f ⊆ S := by
    refine closure_minimal (fun M hM => ?_) hS.isClosed
    by_contra hMS
    exact hM (hf M (matExt_eq_zero hMS))
  refine hsub.trans ?_
  rintro _ ⟨a, -, rfl⟩
  exact ⟨a, rfl⟩

/- English proof (translation)
Establish `hs` using `contDiff_matExt hκ`. Establish `hc` using `hasCompactSupport_matExt (K := K) (n := n) hκ.2`. Use `⟨fun M => (matExt K n κ M).re, fun M => (matExt K n κ M).im, Complex.reCLM.contDiff.comp hs, hc.comp_left Complex.zero_re, tsupport_subset_of_matExt hκ.2 fun M h0 => by simp [h0], Complex.imCLM.contDiff.comp hs, hc.comp_left Complex.zero_im, tsupport_subset_of_matExt hκ.2 fun M h …` and prove the remaining obligations. Simplify using `only`. Rewrite using `[matExt_val, Complex.re_add_im]`.
-/
theorem exists_real_parts_of_isTestFunction {κ : archGroup K n → ℂ}
    (hκ : (isExpLieAlgebra K n).IsTestFunction κ) :
    ∃ βr βi : ArchMatrix K n → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) βr ∧ HasCompactSupport βr ∧
      tsupport βr ⊆ range (Units.val : ArchUnits K n → ArchMatrix K n) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) βi ∧ HasCompactSupport βi ∧
      tsupport βi ⊆ range (Units.val : ArchUnits K n → ArchMatrix K n) ∧
      ∀ a : archGroup K n, κ a = (βr ((a : ArchUnits K n) : ArchMatrix K n) : ℂ) +
        (βi ((a : ArchUnits K n) : ArchMatrix K n) : ℂ) * Complex.I := by
  have hs := contDiff_matExt hκ
  have hc := hasCompactSupport_matExt (K := K) (n := n) hκ.2
  refine ⟨fun M => (matExt K n κ M).re, fun M => (matExt K n κ M).im,
    Complex.reCLM.contDiff.comp hs, hc.comp_left Complex.zero_re,
    tsupport_subset_of_matExt hκ.2 fun M h0 => by simp [h0],
    Complex.imCLM.contDiff.comp hs, hc.comp_left Complex.zero_im,
    tsupport_subset_of_matExt hκ.2 fun M h0 => by simp [h0], fun a => ?_⟩
  dsimp only
  rw [matExt_val, Complex.re_add_im]

end Conversion

end CuspidalSpectrum

end

end GroundTheory.Automorphic
