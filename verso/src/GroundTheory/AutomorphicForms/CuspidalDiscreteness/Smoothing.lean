import Mathlib
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.ExistsLintegralConstantTermL2SqLe

open MeasureTheory Set Filter Topology Function
open NumberField IsDedekindDomain
open scoped ENNReal Pointwise NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

set_option linter.unusedSectionVars false

namespace CuspidalSpectrum

open Reduction AutomorphicForm RightCosetSpace

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

variable (K n) in

abbrev ArchUnits : Type _ := (ArchMatrix K n)ˣ

instance : MeasurableSpace (ArchUnits K n) := borel _

instance : BorelSpace (ArchUnits K n) := ⟨rfl⟩

variable (K n) in

def archIncl : ArchUnits K n →* AdelicGLn.AdelicGL K n :=
  (infEmb K n).comp (Subgroup.topEquiv (G := ArchUnits K n)).symm.toMonoidHom

/- English proof (translation)
The claim follows from `continuous_infEmb.comp (continuous_id.subtype_mk _)`.
-/
theorem continuous_archIncl : Continuous (archIncl K n) :=
  continuous_infEmb.comp (continuous_id.subtype_mk _)

/- English proof (translation)
The claim follows from `infEmb_mul_finEmb_comm _ u`.
-/
theorem archIncl_mul_finEmb_comm (A : ArchUnits K n) (u : AdelicGLn.FiniteAdelicGL K n) :
    archIncl K n A * finEmb K n u = finEmb K n u * archIncl K n A :=
  infEmb_mul_finEmb_comm _ u

/- English proof (translation)
Rewrite using `[mem_normOneGL_iff_detModule, map_mul, map_inv]`. Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases. Establish `: Subsingleton (AdelicGLn.AdelicGL K 0)` using `⟨fun x y => Units.ext (Subsingleton.elim _ _)⟩`. Rewrite using `[Subsingleton.elim (archIncl K 0 A) 1, Subsingleton.elim (centralSection K 0 _) 1]`. Simplify using the standard rewrite rules.

Rewrite using `[detModule_centralSection hn, mul_inv_cancel]`.
-/
theorem archIncl_mul_centralSection_inv_mem (A : ArchUnits K n) :
    archIncl K n A * (centralSection K n (detModule K n (archIncl K n A)))⁻¹ ∈ normOneGL K n := by
  rw [mem_normOneGL_iff_detModule, map_mul, map_inv]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : Subsingleton (AdelicGLn.AdelicGL K 0) :=
      ⟨fun x y => Units.ext (Subsingleton.elim _ _)⟩
    rw [Subsingleton.elim (archIncl K 0 A) 1, Subsingleton.elim (centralSection K 0 _) 1]
    simp
  · rw [detModule_centralSection hn, mul_inv_cancel]

/- English proof (translation)
Rewrite using `[← map_inv, centralSection_mul_comm]`.
-/
theorem centralSection_inv_mul_comm (s : {r : ℝ // 0 < r}) (g : AdelicGLn.AdelicGL K n) :
    (centralSection K n s)⁻¹ * g = g * (centralSection K n s)⁻¹ := by
  rw [← map_inv, centralSection_mul_comm]

/- English proof (translation)
Rewrite using `[← map_inv, ← map_inv, ← map_mul, ← map_mul, mul_comm]`.
-/
theorem centralSection_inv_mul_inv_comm (s t : {r : ℝ // 0 < r}) :
    (centralSection K n s)⁻¹ * (centralSection K n t)⁻¹ =
      (centralSection K n t)⁻¹ * (centralSection K n s)⁻¹ := by
  rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, mul_comm]

variable (K n) in

def archProjFun (A : ArchUnits K n) : AdelicGLn.AdelicGL K n :=
  archIncl K n A * (centralSection K n (detModule K n (archIncl K n A)))⁻¹

/- English proof (translation)
Simplify using `[archProjFun]`.
-/
theorem archProjFun_one : archProjFun K n 1 = 1 := by
  simp [archProjFun]

/- English proof (translation)
Unfold `archProjFun`. Simplify using `only [map_mul, mul_inv_rev]`. Simplify using `only [mul_assoc]`. Rewrite using `[← mul_assoc (centralSection K n (detModule K n (archIncl K n A)))⁻¹ (archIncl K n B), centralSection_inv_mul_comm (detModule K n (archIncl K n A)) (archIncl K n B), mul_assoc (archIncl K n B), centralSection_inv_mul_inv_comm (detModule K n (archIncl K n A))]`.
-/
theorem archProjFun_mul (A B : ArchUnits K n) :
    archProjFun K n (A * B) = archProjFun K n A * archProjFun K n B := by
  unfold archProjFun
  simp only [map_mul, mul_inv_rev]
  simp only [mul_assoc]
  rw [← mul_assoc (centralSection K n (detModule K n (archIncl K n A)))⁻¹ (archIncl K n B),
    centralSection_inv_mul_comm (detModule K n (archIncl K n A)) (archIncl K n B),
    mul_assoc (archIncl K n B), centralSection_inv_mul_inv_comm (detModule K n (archIncl K n A))]

variable (K n) in

def archProj : ArchUnits K n →* normOneGL K n where
  toFun A := ⟨archProjFun K n A, archIncl_mul_centralSection_inv_mem A⟩
  map_one' := Subtype.ext archProjFun_one
  map_mul' A B := Subtype.ext (archProjFun_mul A B)

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem coe_archProj (A : ArchUnits K n) :
    (archProj K n A : AdelicGLn.AdelicGL K n) =
      archIncl K n A * (centralSection K n (detModule K n (archIncl K n A)))⁻¹ := rfl

/- English proof (translation)
Use `continuous_induced_rng.2 ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Continuous fun A : ArchUnits K n => archIncl K n A * (centralSection K n (detModule K n (archIncl K n A)))⁻¹`. Conclude with `continuous_archIncl.mul ((continuous_centralSection.comp (continuous_detModule.comp continuous_archIncl)).inv)`.
-/
theorem continuous_archProj : Continuous (archProj K n) := by
  refine continuous_induced_rng.2 ?_
  change Continuous fun A : ArchUnits K n =>
    archIncl K n A * (centralSection K n (detModule K n (archIncl K n A)))⁻¹
  exact continuous_archIncl.mul ((continuous_centralSection.comp
    (continuous_detModule.comp continuous_archIncl)).inv)

/- English proof (translation)
Use `ext1`. Rewrite using `[coe_archProj, (mem_normOneGL_iff_detModule).1 hA, map_one, inv_one, mul_one]`.
-/
theorem archProj_of_mem {A : ArchUnits K n} (hA : archIncl K n A ∈ normOneGL K n) :
    archProj K n A = ⟨archIncl K n A, hA⟩ := by
  ext1
  rw [coe_archProj, (mem_normOneGL_iff_detModule).1 hA, map_one, inv_one, mul_one]

/- English proof (translation)
Rewrite using `[coe_archProj, mul_assoc, centralSection_inv_mul_comm, ← mul_assoc, archIncl_mul_finEmb_comm, mul_assoc]`.
-/
theorem archProj_mul_finEmb_comm (A : ArchUnits K n) (u : AdelicGLn.FiniteAdelicGL K n) :
    (archProj K n A : AdelicGLn.AdelicGL K n) * finEmb K n u =
      finEmb K n u * archProj K n A := by
  rw [coe_archProj, mul_assoc, centralSection_inv_mul_comm, ← mul_assoc,
    archIncl_mul_finEmb_comm, mul_assoc]

variable (K n) in

def finOne : AdelicGLn.integralFiniteGL K n →* normOneGL K n where
  toFun u := ⟨finEmb K n u, maxCompact_le_normOneGL (finEmb_mem_maxCompact u.2)⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem coe_finOne (u : AdelicGLn.integralFiniteGL K n) :
    (finOne K n u : AdelicGLn.AdelicGL K n) = finEmb K n u := rfl

/- English proof (translation)
The claim follows from `continuous_induced_rng.2 (continuous_finEmb.comp continuous_subtype_val)`.
-/
theorem continuous_finOne : Continuous (finOne K n) :=
  continuous_induced_rng.2 (continuous_finEmb.comp continuous_subtype_val)

/- English proof (translation)
Establish `h : archProj K n A * finOne K n u = finOne K n u * archProj K n A` using `Subtype.ext (archProj_mul_finEmb_comm A u)`. Rewrite using `[inv_mul_eq_iff_eq_mul, ← mul_assoc, h, mul_inv_cancel_right]`.
-/
theorem archProj_inv_mul_finOne (A : ArchUnits K n) (u : AdelicGLn.integralFiniteGL K n) :
    (archProj K n A)⁻¹ * finOne K n u = finOne K n u * (archProj K n A)⁻¹ := by
  have h : archProj K n A * finOne K n u = finOne K n u * archProj K n A :=
    Subtype.ext (archProj_mul_finEmb_comm A u)
  rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, h, mul_inv_cancel_right]

section ArchConv

variable (ν : Measure (ArchUnits K n)) [ν.IsHaarMeasure]

def archConvFun (β : ArchMatrix K n → ℝ) (g : normOneGL K n → ℂ) (x : normOneGL K n) : ℂ :=
  ∫ A, (β A : ℂ) * g ((archProj K n A)⁻¹ * x) ∂ν

variable {β : ArchMatrix K n → ℝ}

/- English proof (translation)
The claim follows from `Units.isOpenEmbedding_val.isInducing.isCompact_preimage' hβc hβu`.
-/
theorem isCompact_unitsSupport (hβc : HasCompactSupport β)
    (hβu : tsupport β ⊆ range (Units.val : ArchUnits K n → ArchMatrix K n)) :
    IsCompact ((Units.val : ArchUnits K n → ArchMatrix K n) ⁻¹' tsupport β) :=
  Units.isOpenEmbedding_val.isInducing.isCompact_preimage' hβc hβu

/- English proof (translation)
Use `(setIntegral_eq_integral_of_forall_compl_eq_zero fun A hA => ?_).symm` and prove the remaining obligations. Rewrite using `[image_eq_zero_of_notMem_tsupport hA, Complex.ofReal_zero, zero_mul]`.
-/
theorem archConvFun_eq_setIntegral (g : normOneGL K n → ℂ) (x : normOneGL K n) :
    archConvFun ν β g x = ∫ A in (Units.val : ArchUnits K n → ArchMatrix K n) ⁻¹' tsupport β,
      (β A : ℂ) * g ((archProj K n A)⁻¹ * x) ∂ν := by
  refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun A hA => ?_).symm
  rw [image_eq_zero_of_notMem_tsupport hA, Complex.ofReal_zero, zero_mul]

/- English proof (translation)
Establish `: archConvFun ν β g = fun x => ∫ A in (Units.val : ArchUnits K n → ArchMatrix K n) ⁻¹' tsupport β, (β A : ℂ) * g ((archProj K n A)⁻¹ * x) ∂ν`. Use function extensionality and compare the values at `(archConvFun_eq_setIntegral ν g)`. Rewrite using `[this]`. Use `continuous_parametric_integral_of_continuous ?_ (isCompact_unitsSupport hβc hβu)` and prove the remaining obligations. Conclude with `((Complex.continuous_ofReal.comp (hβ.comp Units.continuous_val)).comp continuous_snd).mul (g.continuous.comp (((continuous_archProj.comp continuous_snd).inv).mul continuous_fst))`.
-/
theorem continuous_archConvFun (hβ : Continuous β) (hβc : HasCompactSupport β)
    (hβu : tsupport β ⊆ range (Units.val : ArchUnits K n → ArchMatrix K n))
    (g : CompactlySupportedContinuousMap (normOneGL K n) ℂ) :
    Continuous (archConvFun ν β g) := by
  have : archConvFun ν β g = fun x => ∫ A in (Units.val : ArchUnits K n → ArchMatrix K n) ⁻¹'
      tsupport β, (β A : ℂ) * g ((archProj K n A)⁻¹ * x) ∂ν :=
    funext (archConvFun_eq_setIntegral ν g)
  rw [this]
  refine continuous_parametric_integral_of_continuous ?_ (isCompact_unitsSupport hβc hβu)
  exact ((Complex.continuous_ofReal.comp (hβ.comp Units.continuous_val)).comp continuous_snd).mul
    (g.continuous.comp (((continuous_archProj.comp continuous_snd).inv).mul continuous_fst))

/- English proof (translation)
Use `integral_eq_zero_of_ae (Eventually.of_forall fun A => ?_)` and prove the remaining obligations. Distinguish the cases in `hA : (A : ArchMatrix K n) ∈ tsupport β`. Establish `: (archProj K n A)⁻¹ * x ∉ tsupport (g : normOneGL K n → ℂ)` using `fun h => hx ⟨archProj K n A, ⟨A, hA, rfl⟩, _, h, mul_inv_cancel_left _ _⟩`. Simplify using `[image_eq_zero_of_notMem_tsupport this]`. Simplify using `[image_eq_zero_of_notMem_tsupport hA]`.
-/
theorem archConvFun_eq_zero_of_notMem (g : CompactlySupportedContinuousMap (normOneGL K n) ℂ)
    {x : normOneGL K n} (hx : x ∉ archProj K n '' ((Units.val : ArchUnits K n → ArchMatrix K n) ⁻¹'
      tsupport β) * tsupport (g : normOneGL K n → ℂ)) : archConvFun ν β g x = 0 := by
  refine integral_eq_zero_of_ae (Eventually.of_forall fun A => ?_)
  by_cases hA : (A : ArchMatrix K n) ∈ tsupport β
  · have : (archProj K n A)⁻¹ * x ∉ tsupport (g : normOneGL K n → ℂ) := fun h =>
      hx ⟨archProj K n A, ⟨A, hA, rfl⟩, _, h, mul_inv_cancel_left _ _⟩
    simp [image_eq_zero_of_notMem_tsupport this]
  · simp [image_eq_zero_of_notMem_tsupport hA]

def archConv (hβ : Continuous β) (hβc : HasCompactSupport β)
    (hβu : tsupport β ⊆ range (Units.val : ArchUnits K n → ArchMatrix K n))
    (g : CompactlySupportedContinuousMap (normOneGL K n) ℂ) :
    CompactlySupportedContinuousMap (normOneGL K n) ℂ :=
  ⟨⟨archConvFun ν β g, continuous_archConvFun ν hβ hβc hβu g⟩,
    HasCompactSupport.intro (((isCompact_unitsSupport hβc hβu).image continuous_archProj).mul
      g.hasCompactSupport) fun _ hx => archConvFun_eq_zero_of_notMem ν g hx⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem archConv_apply (hβ : Continuous β) (hβc : HasCompactSupport β)
    (hβu : tsupport β ⊆ range (Units.val : ArchUnits K n → ArchMatrix K n))
    (g : CompactlySupportedContinuousMap (normOneGL K n) ℂ) (x : normOneGL K n) :
    archConv ν hβ hβc hβu g x = archConvFun ν β g x := rfl

/- English proof (translation)
Rewrite using `[archConvFun, ← integral_mul_left_eq_self _ C]`. Use `integral_congr_ae (Eventually.of_forall fun A => ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(β ((C * A : ArchUnits K n) : ArchMatrix K n) : ℂ) * g ((archProj K n (C * A))⁻¹ * (archProj K n C * w)) = _`. Rewrite using `[map_mul, mul_inv_rev, mul_assoc, inv_mul_cancel_left]`.
-/
theorem archConvFun_archProj_mul (C : ArchUnits K n) (g : normOneGL K n → ℂ) (w : normOneGL K n) :
    archConvFun ν β g (archProj K n C * w) =
      ∫ A, (β ((C * A : ArchUnits K n) : ArchMatrix K n) : ℂ) *
        g ((archProj K n A)⁻¹ * w) ∂ν := by
  rw [archConvFun, ← integral_mul_left_eq_self _ C]
  refine integral_congr_ae (Eventually.of_forall fun A => ?_)
  change (β ((C * A : ArchUnits K n) : ArchMatrix K n) : ℂ) *
    g ((archProj K n (C * A))⁻¹ * (archProj K n C * w)) = _
  rw [map_mul, mul_inv_rev, mul_assoc, inv_mul_cancel_left]

/- English proof (translation)
Unfold `archConvFun`. Use `integral_congr_ae (Eventually.of_forall fun A => ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(β A : ℂ) * g ((archProj K n A)⁻¹ * (finOne K n u * x)) = (β A : ℂ) * g ((archProj K n A)⁻¹ * x)`. Rewrite using `[← mul_assoc, archProj_inv_mul_finOne, mul_assoc, hg]`.
-/
theorem archConvFun_finOne_mul (g : normOneGL K n → ℂ) (u : AdelicGLn.integralFiniteGL K n)
    (hg : ∀ x, g (finOne K n u * x) = g x) (x : normOneGL K n) :
    archConvFun ν β g (finOne K n u * x) = archConvFun ν β g x := by
  unfold archConvFun
  refine integral_congr_ae (Eventually.of_forall fun A => ?_)
  change (β A : ℂ) * g ((archProj K n A)⁻¹ * (finOne K n u * x)) =
    (β A : ℂ) * g ((archProj K n A)⁻¹ * x)
  rw [← mul_assoc, archProj_inv_mul_finOne, mul_assoc, hg]

/- English proof (translation)
Use `(hβ.comp Units.continuous_val).integrable_of_hasCompactSupport ?_` and prove the remaining obligations. Conclude with `HasCompactSupport.intro (isCompact_unitsSupport hβc hβu) fun A hA => image_eq_zero_of_notMem_tsupport (f := β) hA`.
-/
theorem integrable_bump (hβ : Continuous β) (hβc : HasCompactSupport β)
    (hβu : tsupport β ⊆ range (Units.val : ArchUnits K n → ArchMatrix K n)) :
    Integrable (fun A : ArchUnits K n => β A) ν := by
  refine (hβ.comp Units.continuous_val).integrable_of_hasCompactSupport ?_
  exact HasCompactSupport.intro (isCompact_unitsSupport hβc hβu) fun A hA =>
    image_eq_zero_of_notMem_tsupport (f := β) hA

/- English proof (translation)
Establish `hint : Integrable (fun A : ArchUnits K n => β A) ν` using `integrable_bump ν hβ hβc hβu`. Establish `hi : ∀ g' : CompactlySupportedContinuousMap (normOneGL K n) ℂ, Integrable (fun A : ArchUnits K n => (β A : ℂ) * g' ((archProj K n A)⁻¹ * x)) ν`. Introduce `g'`. Take `⟨M, hM⟩` from `g'.continuous.bounded_above_of_compact_support g'.hasCompactSupport`. Conclude with `(hint.ofReal (𝕜 := ℂ)).mul_bdd (g'.continuous.comp ((continuous_archProj.inv).mul continuous_const)).aestronglyMeasurable (Eventually.of_forall fun A => hM _)`.

Rewrite using `[archConvFun, archConvFun, ← integral_sub (hi h) (hi g)]`. Combine the equalities or inequalities in the displayed calculation. Use `norm_integral_le_of_norm_le (hint.mul_const B) (Eventually.of_forall fun A => ?_)` and prove the remaining obligations. Rewrite using `[← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hβ0 _)]`. Conclude with `mul_le_mul_of_nonneg_left (hB _) (hβ0 _)`.

Use `_ = B := by rw [integral_mul_const, hβ1, one_mul]`.
-/
theorem norm_archConvFun_sub_archConvFun_le (hβ : Continuous β) (hβc : HasCompactSupport β)
    (hβu : tsupport β ⊆ range (Units.val : ArchUnits K n → ArchMatrix K n))
    (hβ0 : ∀ A, 0 ≤ β A) (hβ1 : ∫ A : ArchUnits K n, β A ∂ν = 1)
    (g h : CompactlySupportedContinuousMap (normOneGL K n) ℂ) {B : ℝ}
    (hB : ∀ y, ‖h y - g y‖ ≤ B) (x : normOneGL K n) :
    ‖archConvFun ν β h x - archConvFun ν β g x‖ ≤ B := by
  have hint : Integrable (fun A : ArchUnits K n => β A) ν := integrable_bump ν hβ hβc hβu
  have hi : ∀ g' : CompactlySupportedContinuousMap (normOneGL K n) ℂ,
      Integrable (fun A : ArchUnits K n => (β A : ℂ) * g' ((archProj K n A)⁻¹ * x)) ν := by
    intro g'
    obtain ⟨M, hM⟩ := g'.continuous.bounded_above_of_compact_support g'.hasCompactSupport
    exact (hint.ofReal (𝕜 := ℂ)).mul_bdd
      (g'.continuous.comp ((continuous_archProj.inv).mul continuous_const)).aestronglyMeasurable
      (Eventually.of_forall fun A => hM _)
  rw [archConvFun, archConvFun, ← integral_sub (hi h) (hi g)]
  calc ‖∫ A, ((β A : ℂ) * h ((archProj K n A)⁻¹ * x) - (β A : ℂ) * g ((archProj K n A)⁻¹ * x)) ∂ν‖
      ≤ ∫ A, β A * B ∂ν := by
        refine norm_integral_le_of_norm_le (hint.mul_const B) (Eventually.of_forall fun A => ?_)
        rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hβ0 _)]
        exact mul_le_mul_of_nonneg_left (hB _) (hβ0 _)
    _ = B := by rw [integral_mul_const, hβ1, one_mul]

/- English proof (translation)
Establish `hint : Integrable (fun A : ArchUnits K n => β A) ν` using `integrable_bump ν hβ hβc hβu`. Establish `hi1 : Integrable (fun A : ArchUnits K n => (β A : ℂ) * g ((archProj K n A)⁻¹ * x)) ν`. Take `⟨M, hM⟩` from `g.continuous.bounded_above_of_compact_support g.hasCompactSupport`. Conclude with `(hint.ofReal (𝕜 := ℂ)).mul_bdd (g.continuous.comp ((continuous_archProj.inv).mul continuous_const)).aestronglyMeasurable (Eventually.of_forall fun A => hM _)`. Establish `hi2 : Integrable (fun A : ArchUnits K n => (β A : ℂ) * g x) ν` using `(hint.ofReal (𝕜 := ℂ)).mul_const _`.

Establish `hgx : g x = ∫ A, (β A : ℂ) * g x ∂ν`. Rewrite using `[integral_mul_const, integral_complex_ofReal, hβ1, Complex.ofReal_one, one_mul]`. Rewrite using `[hgx, archConvFun, ← integral_sub hi1 hi2]`. Combine the equalities or inequalities in the displayed calculation. Use `norm_integral_le_of_norm_le (hint.mul_const ε) (Eventually.of_forall fun A => ?_)` and prove the remaining obligations.

Rewrite using `[← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hβ0 _)]`. Distinguish the cases in `hA : (A : ArchMatrix K n) ∈ tsupport β`. Conclude with `mul_le_mul_of_nonneg_left (hg _ (hV A hA) x) (hβ0 _)`. Rewrite using `[image_eq_zero_of_notMem_tsupport hA, zero_mul, zero_mul]`. Use `_ = ε := by rw [integral_mul_const, hβ1, one_mul]`.
-/
theorem norm_archConvFun_sub_le (hβ : Continuous β) (hβc : HasCompactSupport β)
    (hβu : tsupport β ⊆ range (Units.val : ArchUnits K n → ArchMatrix K n))
    (hβ0 : ∀ A, 0 ≤ β A) (hβ1 : ∫ A : ArchUnits K n, β A ∂ν = 1) {V : Set (normOneGL K n)}
    (hV : ∀ A : ArchUnits K n, (A : ArchMatrix K n) ∈ tsupport β → archProj K n A ∈ V)
    (g : CompactlySupportedContinuousMap (normOneGL K n) ℂ) {ε : ℝ}
    (hg : ∀ a ∈ V, ∀ x, ‖g (a⁻¹ * x) - g x‖ ≤ ε) (x : normOneGL K n) :
    ‖archConvFun ν β g x - g x‖ ≤ ε := by
  have hint : Integrable (fun A : ArchUnits K n => β A) ν := integrable_bump ν hβ hβc hβu
  have hi1 : Integrable (fun A : ArchUnits K n => (β A : ℂ) * g ((archProj K n A)⁻¹ * x)) ν := by
    obtain ⟨M, hM⟩ := g.continuous.bounded_above_of_compact_support g.hasCompactSupport
    exact (hint.ofReal (𝕜 := ℂ)).mul_bdd
      (g.continuous.comp ((continuous_archProj.inv).mul continuous_const)).aestronglyMeasurable
      (Eventually.of_forall fun A => hM _)
  have hi2 : Integrable (fun A : ArchUnits K n => (β A : ℂ) * g x) ν :=
    (hint.ofReal (𝕜 := ℂ)).mul_const _
  have hgx : g x = ∫ A, (β A : ℂ) * g x ∂ν := by
    rw [integral_mul_const, integral_complex_ofReal, hβ1, Complex.ofReal_one, one_mul]
  rw [hgx, archConvFun, ← integral_sub hi1 hi2]
  calc ‖∫ A, ((β A : ℂ) * g ((archProj K n A)⁻¹ * x) - (β A : ℂ) * g x) ∂ν‖
      ≤ ∫ A, β A * ε ∂ν := by
        refine norm_integral_le_of_norm_le (hint.mul_const ε) (Eventually.of_forall fun A => ?_)
        rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hβ0 _)]
        by_cases hA : (A : ArchMatrix K n) ∈ tsupport β
        · exact mul_le_mul_of_nonneg_left (hg _ (hV A hA) x) (hβ0 _)
        · rw [image_eq_zero_of_notMem_tsupport hA, zero_mul, zero_mul]
    _ = ε := by rw [integral_mul_const, hβ1, one_mul]

end ArchConv

end CuspidalSpectrum

end

end GroundTheory.Automorphic
