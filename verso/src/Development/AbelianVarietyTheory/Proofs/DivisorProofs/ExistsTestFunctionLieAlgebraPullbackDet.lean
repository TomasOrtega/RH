import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlRes
import Development.AbelianVarietyTheory.Definitions.Divisors.IsExpLieAlgebraComplexUnits
import Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn

noncomputable section

open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.HCA GroundTheory.Automorphic
open scoped ContDiff Topology

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

namespace GlobalTheory.GLExt

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

variable (E a) in

def toLCLM : Matrix (Fin a) (Fin a) (Cinf E) →L[ℝ] Lie E a :=
  LinearMap.toContinuousLinearMap (Matrix.ofLinearEquiv ℝ).symm.toLinearMap

variable (E a) in

def ofCLM : Lie E a →L[ℝ] Matrix (Fin a) (Fin a) (Cinf E) :=
  LinearMap.toContinuousLinearMap (Matrix.ofLinearEquiv ℝ).toLinearMap

def detL (x : Lie E a) : ℝ := LinearMap.det ((lmul x : Lie E a →L[ℝ] Lie E a) : Lie E a →ₗ[ℝ] Lie E a)

/- English proof (translation)
Set `b` to `Module.finBasis ℝ (Lie E a)`. Establish `e : (detL (E` using `E) (a := a)) = fun x => (Matrix.of fun i j => b.coord i (rmul (b j) x)).det := by`. Use function extensionality and compare the values at `x`. Rewrite using `[detL, ← LinearMap.det_toMatrix b]`. Use `congr 1`.

Use extensionality with `i j`. Rewrite using `[LinearMap.toMatrix_apply]`. Both sides reduce to the same expression. Rewrite using `[e]`. Simplify using `only [Matrix.det_apply', Matrix.of_apply]`.

Use `ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => ?_)` and prove the remaining obligations. Conclude with `(LinearMap.toContinuousLinearMap (b.coord (σ i))).contDiff.comp (ContinuousLinearMap.contDiff (rmul (b i)))`.
-/
theorem contDiff_detL : ContDiff ℝ ∞ (detL (E := E) (a := a)) := by
  let b := Module.finBasis ℝ (Lie E a)
  have e : (detL (E := E) (a := a)) = fun x => (Matrix.of fun i j => b.coord i (rmul (b j) x)).det := by
    funext x
    rw [detL, ← LinearMap.det_toMatrix b]
    congr 1
    ext i j
    rw [LinearMap.toMatrix_apply]
    rfl
  rw [e]
  simp only [Matrix.det_apply', Matrix.of_apply]
  refine ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => ?_)
  exact (LinearMap.toContinuousLinearMap (b.coord (σ i))).contDiff.comp (ContinuousLinearMap.contDiff (rmul (b i)))

/- English proof (translation)
Take `⟨u, hu⟩` from `hx`. Establish `h : ((lmul x : Lie E a →L[ℝ] Lie E a) : Lie E a →ₗ[ℝ] Lie E a) ∘ₗ ((lmul (toL (u⁻¹ : (Matrix (Fin a) (Fin a) (Cinf E))ˣ).val) : Lie E a →L[ℝ] Lie E a) : Lie E a →ₗ[ℝ] Lie E a) = LinearMap.id`. Use `LinearMap.ext fun v => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Matrix.of x * (((u⁻¹ : (Matrix (Fin a) (Fin a) (Cinf E))ˣ) : Matrix (Fin a) (Fin a) (Cinf E)) * Matrix.of v) = Matrix.of v`. Rewrite using `[← hu, Units.mul_inv_cancel_left]`.

Introduce `h0`. Establish `h1` using `congrArg LinearMap.det h`. Rewrite `h1` using `[LinearMap.det_comp, LinearMap.det_id]`. Rewrite `h0` using `[detL]`. Rewrite `h1` using `[h0, zero_mul]`.

Conclude with `zero_ne_one h1`.
-/
theorem detL_ne_zero {x : Lie E a} (hx : x ∈ invSet E a) : detL x ≠ 0 := by
  obtain ⟨u, hu⟩ := hx
  have h : ((lmul x : Lie E a →L[ℝ] Lie E a) : Lie E a →ₗ[ℝ] Lie E a) ∘ₗ
      ((lmul (toL (u⁻¹ : (Matrix (Fin a) (Fin a) (Cinf E))ˣ).val) : Lie E a →L[ℝ] Lie E a) : Lie E a →ₗ[ℝ] Lie E a) =
        LinearMap.id := by
    refine LinearMap.ext fun v => ?_
    change Matrix.of x * (((u⁻¹ : (Matrix (Fin a) (Fin a) (Cinf E))ˣ) : Matrix (Fin a) (Fin a) (Cinf E)) * Matrix.of v) =
      Matrix.of v
    rw [← hu, Units.mul_inv_cancel_left]
  intro h0
  have h1 := congrArg LinearMap.det h
  rw [LinearMap.det_comp, LinearMap.det_id] at h1
  rw [detL] at h0
  rw [h0, zero_mul] at h1
  exact zero_ne_one h1

open Classical in

def extZ (α : glG E a → ℂ) (x : Lie E a) : ℂ :=
  if h : IsUnit (Matrix.of x) then ((|detL x|⁻¹ : ℝ) : ℂ) * α ⟨h.unit, Subgroup.mem_top _⟩ else 0

/- English proof (translation)
Establish `h : IsUnit (Matrix.of (toL y.1.val))` using `y.1.isUnit`. Establish `e : (⟨h.unit, Subgroup.mem_top _⟩ : glG E a) = y` using `Subtype.ext (Units.ext h.unit_spec)`. Rewrite using `[extZ, dif_pos h, e]`.
-/
theorem extZ_val (α : glG E a → ℂ) (y : glG E a) :
    extZ α (toL y.1.val) = ((|detL (toL y.1.val)|⁻¹ : ℝ) : ℂ) * α y := by
  have h : IsUnit (Matrix.of (toL y.1.val)) := y.1.isUnit
  have e : (⟨h.unit, Subgroup.mem_top _⟩ : glG E a) = y := Subtype.ext (Units.ext h.unit_spec)
  rw [extZ, dif_pos h, e]

/- English proof (translation)
The claim follows from `(toLCLM E a).continuous.comp (Units.continuous_val.comp continuous_subtype_val)`.
-/
theorem continuous_toL_val : Continuous fun y : glG E a => toL y.1.val :=
  (toLCLM E a).continuous.comp (Units.continuous_val.comp continuous_subtype_val)

/- English proof (translation)
Introduce `x hx`. Distinguish the cases in `h : IsUnit (Matrix.of x)`. Use `⟨⟨h.unit, Subgroup.mem_top _⟩, subset_tsupport _ fun h0 => hx ?_, ?_⟩` and prove the remaining obligations. Simplify using `[extZ, h, h0]`. Use `show Matrix.of.symm (h.unit : Matrix (Fin a) (Fin a) (Cinf E)) = x`.

Rewrite using `[h.unit_spec]`. Both sides reduce to the same expression. Conclude with `absurd (by simp [extZ, h]) hx`.
-/
theorem support_extZ_subset (α : glG E a → ℂ) :
    Function.support (extZ α) ⊆ (fun y : glG E a => toL y.1.val) '' tsupport α := by
  intro x hx
  by_cases h : IsUnit (Matrix.of x)
  · refine ⟨⟨h.unit, Subgroup.mem_top _⟩, subset_tsupport _ fun h0 => hx ?_, ?_⟩
    · simp [extZ, h, h0]
    · show Matrix.of.symm (h.unit : Matrix (Fin a) (Fin a) (Cinf E)) = x
      rw [h.unit_spec]; rfl
  · exact absurd (by simp [extZ, h]) hx

/- English proof (translation)
Take `⟨u, hu⟩` from `id hx₀`. Set `g : glG E a` to `⟨u, Subgroup.mem_top _⟩`. Set `L : Lie E a → Matrix (Fin a) (Fin a) (Cinf E)` to `fun x => ((u⁻¹ : (Matrix (Fin a) (Fin a) (Cinf E))ˣ) : Matrix (Fin a) (Fin a) (Cinf E)) * ofCLM E a x`. Establish `hL1 : L x₀ = 1`. Express the relevant statement in the definitionally equal form `_ * Matrix.of x₀ = 1`.

Rewrite using `[← hu, Units.inv_mul]`. Establish `hLc : ContDiff ℝ ∞ L` using `contDiff_const.mul (ofCLM E a).contDiff`. Establish `hT : (expPartialHomeomorph ℝ (Matrix (Fin a) (Fin a) (Cinf E))).target ∈ 𝓝 (L x₀)`. Rewrite using `[hL1]`. Conclude with `(expPartialHomeomorph ℝ _).open_target.mem_nhds (one_mem_expPartialHomeomorph_target ℝ _)`.

Establish `hU : ∀ᶠ x in 𝓝 x₀, L x ∈ (expPartialHomeomorph ℝ (Matrix (Fin a) (Fin a) (Cinf E))).target` using `hLc.continuous.continuousAt.preimage_mem_nhds hT`. Establish `hI : ∀ᶠ x in 𝓝 x₀, x ∈ invSet E a` using `isOpen_invSet.mem_nhds hx₀`. Set `Y : Lie E a → glL E a` to `fun x => subspaceProj (glL E a) ((expPartialHomeomorph ℝ (Matrix (Fin a) (Fin a) (Cinf E))).symm (L x))`. Establish `hY : ContDiffAt ℝ ∞ Y x₀` using `(subspaceProj (glL E a)).contDiff.contDiffAt.comp (g := ⇑(subspaceProj (glL E a))) x₀ (((contDiffOn_expPartialHomeomorph_symm ℝ _).contDiffAt hT).comp x₀ hLc.contDiffAt)`. Establish `hF : ContDiffAt ℝ ∞ (fun x => α (g * (glH E a).expG (Y x))) x₀` using `(((glH E a).isSmoothFun_iff.1 hα g).contDiffAt).comp x₀ hY`.

Establish `hD : ContDiffAt ℝ ∞ (fun x => ((|detL x|⁻¹ : ℝ) : ℂ)) x₀` using `Complex.ofRealCLM.contDiff.contDiffAt.comp x₀ ((contDiff_detL.contDiffAt.abs (detL_ne_zero hx₀)).inv (abs_ne_zero.2 (detL_ne_zero hx₀)))`. Use `(hD.mul hF).congr_of_eventuallyEq ?_` and prove the remaining obligations. Use `filter_upwards [hU, hI] with x hx hxi`. Establish `h2 : NormedSpace.exp ((expPartialHomeomorph ℝ (Matrix (Fin a) (Fin a) (Cinf E))).symm (L x)) = L x` using `(expPartialHomeomorph ℝ _).right_inv hx`. Establish `e : (⟨hxi.unit, Subgroup.mem_top _⟩ : glG E a) = g * (glH E a).expG (Y x)`.

Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Simplify using `only [Subgroup.coe_mul, Units.val_mul, IsExpLieAlgebra.coe_expG]`. Rewrite using `[subspaceProj_of_mem Submodule.mem_top]`. Use `(?_ : _ = (u : Matrix (Fin a) (Fin a) (Cinf E)) * L x).trans (congrArg _ h2.symm)` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `Matrix.of x = (u : Matrix (Fin a) (Fin a) (Cinf E)) * (_ * Matrix.of x)`. Rewrite using `[Units.mul_inv_cancel_left]`. Rewrite using `[extZ, dif_pos (show IsUnit (Matrix.of x) from hxi), e]`.
-/
theorem contDiffAt_extZ {α : glG E a → ℂ} (hα : (glH E a).IsSmoothFun α) {x₀ : Lie E a} (hx₀ : x₀ ∈ invSet E a) :
    ContDiffAt ℝ ∞ (extZ α) x₀ := by
  obtain ⟨u, hu⟩ := id hx₀
  let g : glG E a := ⟨u, Subgroup.mem_top _⟩
  let L : Lie E a → Matrix (Fin a) (Fin a) (Cinf E) :=
    fun x => ((u⁻¹ : (Matrix (Fin a) (Fin a) (Cinf E))ˣ) : Matrix (Fin a) (Fin a) (Cinf E)) * ofCLM E a x
  have hL1 : L x₀ = 1 := by
    change _ * Matrix.of x₀ = 1
    rw [← hu, Units.inv_mul]
  have hLc : ContDiff ℝ ∞ L := contDiff_const.mul (ofCLM E a).contDiff
  have hT : (expPartialHomeomorph ℝ (Matrix (Fin a) (Fin a) (Cinf E))).target ∈ 𝓝 (L x₀) := by
    rw [hL1]
    exact (expPartialHomeomorph ℝ _).open_target.mem_nhds (one_mem_expPartialHomeomorph_target ℝ _)
  have hU : ∀ᶠ x in 𝓝 x₀, L x ∈ (expPartialHomeomorph ℝ (Matrix (Fin a) (Fin a) (Cinf E))).target :=
    hLc.continuous.continuousAt.preimage_mem_nhds hT
  have hI : ∀ᶠ x in 𝓝 x₀, x ∈ invSet E a := isOpen_invSet.mem_nhds hx₀
  let Y : Lie E a → glL E a := fun x =>
    subspaceProj (glL E a) ((expPartialHomeomorph ℝ (Matrix (Fin a) (Fin a) (Cinf E))).symm (L x))
  have hY : ContDiffAt ℝ ∞ Y x₀ :=
    (subspaceProj (glL E a)).contDiff.contDiffAt.comp (g := ⇑(subspaceProj (glL E a))) x₀
      (((contDiffOn_expPartialHomeomorph_symm ℝ _).contDiffAt hT).comp x₀ hLc.contDiffAt)
  have hF : ContDiffAt ℝ ∞ (fun x => α (g * (glH E a).expG (Y x))) x₀ :=
    (((glH E a).isSmoothFun_iff.1 hα g).contDiffAt).comp x₀ hY
  have hD : ContDiffAt ℝ ∞ (fun x => ((|detL x|⁻¹ : ℝ) : ℂ)) x₀ :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x₀
      ((contDiff_detL.contDiffAt.abs (detL_ne_zero hx₀)).inv (abs_ne_zero.2 (detL_ne_zero hx₀)))
  refine (hD.mul hF).congr_of_eventuallyEq ?_
  filter_upwards [hU, hI] with x hx hxi
  have h2 : NormedSpace.exp ((expPartialHomeomorph ℝ (Matrix (Fin a) (Fin a) (Cinf E))).symm (L x)) = L x :=
    (expPartialHomeomorph ℝ _).right_inv hx
  have e : (⟨hxi.unit, Subgroup.mem_top _⟩ : glG E a) = g * (glH E a).expG (Y x) := by
    apply Subtype.ext; apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul, IsExpLieAlgebra.coe_expG]
    rw [subspaceProj_of_mem Submodule.mem_top]
    refine (?_ : _ = (u : Matrix (Fin a) (Fin a) (Cinf E)) * L x).trans (congrArg _ h2.symm)
    change Matrix.of x = (u : Matrix (Fin a) (Fin a) (Cinf E)) * (_ * Matrix.of x)
    rw [Units.mul_inv_cancel_left]
  rw [extZ, dif_pos (show IsUnit (Matrix.of x) from hxi), e]

/- English proof (translation)
Introduce `E _ _ _ a α hα hc`. Establish `hK : IsCompact ((fun y : glG E a => toL y.1.val) '' tsupport α)` using `hc.image continuous_toL_val`. Establish `hs : tsupport (extZ α) ⊆ (fun y : glG E a => toL y.1.val) '' tsupport α` using `closure_minimal (support_extZ_subset α) hK.isClosed`. Establish `hi : tsupport (extZ α) ⊆ invSet E a` using `hs.trans (by rintro _ ⟨y, _, rfl⟩; exact val_mem_invSet y.1)`. Use `⟨extZ α, ⟨contDiff_iff_contDiffAt.2 fun x => ?_, hK.of_isClosed_subset (isClosed_tsupport _) hs, hi⟩, fun y => extZ_val α y⟩` and prove the remaining obligations.

Distinguish the cases in `hx : x ∈ tsupport (extZ α)`. Conclude with `contDiffAt_extZ hα (hi hx)`. Conclude with `(contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.1 hx)`.
-/
theorem exists_isTest_ext : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), ∀ α : glG E a → ℂ,
    (glH E a).IsSmoothFun α → HasCompactSupport α → ∃ β : Lie E a → ℂ, GlobalTheory.CuspQuot.IsTest (invSet E a) β ∧
      ∀ y : glG E a, β (toL y.1.val) = ((|LinearMap.det ((lmul (toL y.1.val) : Lie E a →L[ℝ] Lie E a) :
        Lie E a →ₗ[ℝ] Lie E a)|⁻¹ : ℝ) : ℂ) * α y := by
  intro E _ _ _ a α hα hc
  have hK : IsCompact ((fun y : glG E a => toL y.1.val) '' tsupport α) := hc.image continuous_toL_val
  have hs : tsupport (extZ α) ⊆ (fun y : glG E a => toL y.1.val) '' tsupport α :=
    closure_minimal (support_extZ_subset α) hK.isClosed
  have hi : tsupport (extZ α) ⊆ invSet E a := hs.trans (by rintro _ ⟨y, _, rfl⟩; exact val_mem_invSet y.1)
  refine ⟨extZ α, ⟨contDiff_iff_contDiffAt.2 fun x => ?_, hK.of_isClosed_subset (isClosed_tsupport _) hs, hi⟩,
    fun y => extZ_val α y⟩
  by_cases hx : x ∈ tsupport (extZ α)
  · exact contDiffAt_extZ hα (hi hx)
  · exact (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.1 hx)

end GlobalTheory.GLExt

end
