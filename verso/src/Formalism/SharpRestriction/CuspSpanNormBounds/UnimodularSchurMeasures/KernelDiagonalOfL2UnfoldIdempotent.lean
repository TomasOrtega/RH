import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RightRegularIsometricMultiplicative
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RrkDiag

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Set TopologicalSpace
open scoped InnerProductSpace ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

def ker2 (X : CData) (x y : X.I.GA) : ℂ := ∑' γ : X.I.GFset, X.φ (x⁻¹ * (γ : X.I.GA) * y)

def KernelL2RowsColumns (X : CData) : Prop := ∀ᵐ x ∂X.μ, MemLp (fun y => ker2 X x y) 2 X.μ

def KerUnfold (X : CData) : Prop :=
  ∀ T : X.L2 →L[ℂ] X.L2, X.IsOp T → ∀ f : X.L2, ∀ᵐ x ∂X.μ,
    ((T f : X.L2) : X.I.GA → ℂ) x = ∫ y, ker2 X x y * (f : X.I.GA → ℂ) y ∂X.μ

def KerIdem (X : CData) : Prop :=
  ∀ᵐ x ∂X.μ, Summable (fun γ : X.I.GFset => X.φ (x⁻¹ * (γ : X.I.GA) * x)) ∧
    X.kerD x = ((∫ y, ‖ker2 X x y‖ ^ 2 ∂X.μ : ℝ) : ℂ)

/- English proof (translation)
Use `hH` as an intermediate fact. Establish `: SecondCountableTopology X.I.Gf` using `rr_secondCountable X.I X.μf`. Establish `: SigmaFinite (X.I.muA X.μf)` using `rr_muA_sigmaFinite X.I X.μf`. Establish `: Fact ((2 : ℝ≥0∞) ≠ ∞)` using `⟨by norm_num⟩`. Establish `: SecondCountableTopology (Lp ℂ 2 ((X.I.muA X.μf).restrict X.fund))` using `inferInstance`.

Use `infer_instance`.
-/
theorem rrk_separable (X : CData) (hH : X.μf.IsHaarMeasure) : SeparableSpace X.L2 := by
  have := hH
  have : SecondCountableTopology X.I.Gf := rr_secondCountable X.I X.μf
  have : SigmaFinite (X.I.muA X.μf) := rr_muA_sigmaFinite X.I X.μf
  have : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  have : SecondCountableTopology (Lp ℂ 2 ((X.I.muA X.μf).restrict X.fund)) := inferInstance
  infer_instance

open Classical in

def rrk_kap (X : CData) (x : X.I.GA) : X.L2 :=
  if h : MemLp (fun y => star (ker2 X x y)) 2 ((X.I.muA X.μf).restrict X.fund) then h.toLp _ else 0

/- English proof (translation)
Establish `h' : MemLp (fun y => star (ker2 X x y)) 2 ((X.I.muA X.μf).restrict X.fund)` using `h.star`. Unfold `rrk_kap`. Rewrite using `[dif_pos h']`. Conclude with `h'.coeFn_toLp`.
-/
theorem rrk_kap_coe (X : CData) {x : X.I.GA} (h : MemLp (fun y => ker2 X x y) 2 ((X.I.muA X.μf).restrict X.fund)) :
    ((rrk_kap X x : X.L2) : X.I.GA → ℂ) =ᵐ[(X.I.muA X.μf).restrict X.fund] fun y => star (ker2 X x y) := by
  have h' : MemLp (fun y => star (ker2 X x y)) 2 ((X.I.muA X.μf).restrict X.fund) := h.star
  unfold rrk_kap
  rw [dif_pos h']
  exact h'.coeFn_toLp

/- English proof (translation)
Introduce `T hT hP N F`. Unfold `KernelL2RowsColumns CData.μ at h1`. Unfold `KerUnfold CData.μ at h2`. Unfold `KerIdem CData.μ at h3`. Unfold `CData.μ`.

Use `rrk_separable X hH` as an intermediate fact. Establish `hκ : ∀ f : X.L2, ∀ᵐ x ∂(X.I.muA X.μf).restrict X.fund, ((T f : X.L2) : X.I.GA → ℂ) x = ⟪rrk_kap X x, f⟫_ℂ`. Introduce `f`. Use `filter_upwards [h1, h2 T hT f] with x a1 a2`. Rewrite using `[a2, L2.inner_def]`.

Use `integral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [rrk_kap_coe X a1] with y b1`. Rewrite using `[b1, RCLike.inner_apply]`. Simplify using `[mul_comm]`. Establish `hd` using `rrk_diag ((X.I.muA X.μf).restrict X.fund) T hP F (rrk_kap X) hκ`.

Use `filter_upwards [h1, h3, hd] with x a1 a3 ad`. Use `⟨a3.1, ?_⟩` and prove the remaining obligations. Rewrite using `[a3.2, ← ad]`. Use `congr 1`. Establish `e1 : ((‖rrk_kap X x‖ ^ 2 : ℝ) : ℂ) = ⟪rrk_kap X x, rrk_kap X x⟫_ℂ`.

Rewrite using `[inner_self_eq_norm_sq_to_K]`. Use `norm_cast`. Establish `e2 : ⟪rrk_kap X x, rrk_kap X x⟫_ℂ = ((∫ y, ‖ker2 X x y‖ ^ 2 ∂(X.I.muA X.μf).restrict X.fund : ℝ) : ℂ)`. Rewrite using `[L2.inner_def, ← integral_complex_ofReal]`. Use `integral_congr_ae ?_` and prove the remaining obligations.

Use `filter_upwards [rrk_kap_coe X a1] with y b1`. Rewrite using `[b1, inner_self_eq_norm_sq_to_K, norm_star]`. Use `norm_cast`. Conclude with `(e1.trans e2).symm` after adjusting the coercions.
-/
theorem kernel_diagonal_of_L2_unfold_idempotent (X : CData) (hH : X.μf.IsHaarMeasure) (h1 : KernelL2RowsColumns X) (h2 : KerUnfold X) (h3 : KerIdem X) :
    X.KernelDiag := by
  intro T hT hP N F
  unfold KernelL2RowsColumns CData.μ at h1
  unfold KerUnfold CData.μ at h2
  unfold KerIdem CData.μ at h3
  unfold CData.μ
  have := rrk_separable X hH
  have hκ : ∀ f : X.L2, ∀ᵐ x ∂(X.I.muA X.μf).restrict X.fund, ((T f : X.L2) : X.I.GA → ℂ) x = ⟪rrk_kap X x, f⟫_ℂ := by
    intro f
    filter_upwards [h1, h2 T hT f] with x a1 a2
    rw [a2, L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [rrk_kap_coe X a1] with y b1
    rw [b1, RCLike.inner_apply]
    simp [mul_comm]
  have hd := rrk_diag ((X.I.muA X.μf).restrict X.fund) T hP F (rrk_kap X) hκ
  filter_upwards [h1, h3, hd] with x a1 a3 ad
  refine ⟨a3.1, ?_⟩
  rw [a3.2, ← ad]
  congr 1
  have e1 : ((‖rrk_kap X x‖ ^ 2 : ℝ) : ℂ) = ⟪rrk_kap X x, rrk_kap X x⟫_ℂ := by
    rw [inner_self_eq_norm_sq_to_K]; norm_cast
  have e2 : ⟪rrk_kap X x, rrk_kap X x⟫_ℂ = ((∫ y, ‖ker2 X x y‖ ^ 2 ∂(X.I.muA X.μf).restrict X.fund : ℝ) : ℂ) := by
    rw [L2.inner_def, ← integral_complex_ofReal]
    refine integral_congr_ae ?_
    filter_upwards [rrk_kap_coe X a1] with y b1
    rw [b1, inner_self_eq_norm_sq_to_K, norm_star]
    norm_cast
  exact_mod_cast (e1.trans e2).symm

end Formalism.MainNotions.LeviCoordinates

end
