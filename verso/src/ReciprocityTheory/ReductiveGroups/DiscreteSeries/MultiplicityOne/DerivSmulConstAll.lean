import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StCut1p
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.UnitaryGroupStructuralFacts

noncomputable section

open MeasureTheory Matrix

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

namespace SmulConstantLinearity

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

/- English proof (translation)
Distinguish the cases in `hd : DifferentiableAt ℝ h 0`. Conclude with `deriv_smul_const hd T`. Distinguish the cases in `hT : T = 0`. Simplify using `[hT]`. Establish `hnd : ¬ DifferentiableAt ℝ (fun t => h t • T) 0`.

Introduce `hd'`. Apply `hd` to reduce the goal to its premises. Take `⟨g, -, hg⟩` from `exists_dual_vector ℂ T (norm_ne_zero_iff.2 hT)`. Establish `hT' : g T ≠ 0`. Rewrite using `[hg]`.

Simplify using `using hT`. Establish `heq : h = fun t => (g T)⁻¹ * g (h t • T)`. Use function extensionality and compare the values at `t`. Rewrite using `[map_smul, smul_eq_mul, mul_comm, mul_assoc, mul_inv_cancel₀ hT', mul_one]`. Rewrite using `[heq]`.

Conclude with `((g.restrictScalars ℝ).differentiableAt.comp 0 hd').const_mul _`. Rewrite using `[deriv_zero_of_not_differentiableAt hd, deriv_zero_of_not_differentiableAt hnd, zero_smul]`.
-/
theorem deriv_smul_const_all {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (h : ℝ → ℂ) (T : E) :
    deriv (fun t => h t • T) 0 = deriv h 0 • T := by
  by_cases hd : DifferentiableAt ℝ h 0
  · exact deriv_smul_const hd T
  by_cases hT : T = 0
  · simp [hT]
  have hnd : ¬ DifferentiableAt ℝ (fun t => h t • T) 0 := by
    intro hd'
    apply hd
    obtain ⟨g, -, hg⟩ := exists_dual_vector ℂ T (norm_ne_zero_iff.2 hT)
    have hT' : g T ≠ 0 := by
      rw [hg]; simpa using hT
    have heq : h = fun t => (g T)⁻¹ * g (h t • T) := by
      funext t
      rw [map_smul, smul_eq_mul, mul_comm, mul_assoc, mul_inv_cancel₀ hT', mul_one]
    rw [heq]
    exact ((g.restrictScalars ℝ).differentiableAt.comp 0 hd').const_mul _
  rw [deriv_zero_of_not_differentiableAt hd, deriv_zero_of_not_differentiableAt hnd, zero_smul]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/- English proof (translation)
Use function extensionality and compare the values at `g`. Conclude with `deriv_smul_const_all _ T`.
-/
theorem ldV_smul_const (X : Mat k r) (φ : Mat k r → ℂ) (T : E) :
    LdV X (fun g => φ g • T) = fun g => LdV X φ g • T := by
  funext g
  exact deriv_smul_const_all _ T

/- English proof (translation)
Use function extensionality and compare the values at `g`. Conclude with `deriv_smul_const_all _ T`.
-/
theorem rdV_smul_const (X : Mat k r) (φ : Mat k r → ℂ) (T : E) :
    RdV X (fun g => φ g • T) = fun g => RdV X φ g • T := by
  funext g
  exact deriv_smul_const_all _ T

/- English proof (translation)
Proceed by induction on `v with`. Consider the case `nil => rfl`. Consider the case `cons X v ih => show RdV X (Rw v (fun g => φ g • T)) = fun g => RdV X (Rw v φ) g • T`. Rewrite using `[ih, rdV_smul_const]`.
-/
theorem rw_smul_const (v : List (Mat k r)) (φ : Mat k r → ℂ) (T : E) :
    Rw v (fun g => φ g • T) = fun g => Rw v φ g • T := by
  induction v with
  | nil => rfl
  | cons X v ih =>
    show RdV X (Rw v (fun g => φ g • T)) = fun g => RdV X (Rw v φ) g • T
    rw [ih, rdV_smul_const]

/- English proof (translation)
Proceed by induction on `u with`. Consider the case `nil => exact rw_smul_const v φ T`. Consider the case `cons X u ih => show LdV X (dLR u v (fun g => φ g • T)) = fun g => LdV X (dLR u v φ) g • T`. Rewrite using `[ih, ldV_smul_const]`.
-/
theorem dLR_smul_const (u v : List (Mat k r)) (φ : Mat k r → ℂ) (T : E) :
    dLR u v (fun g => φ g • T) = fun g => dLR u v φ g • T := by
  induction u with
  | nil => exact rw_smul_const v φ T
  | cons X u ih =>
    show LdV X (dLR u v (fun g => φ g • T)) = fun g => LdV X (dLR u v φ) g • T
    rw [ih, ldV_smul_const]

/- English proof (translation)
Take `⟨hCk, hb⟩` from `hf`. Use `⟨fun g₀ hg₀ => ?_, fun u v hu hv hl g hg => ?_⟩` and prove the remaining obligations. Take `⟨U, f', hU, hgU, hcd, heq⟩` from `hCk g₀ hg₀`. Use `⟨U, fun g => f' g • T, hU, hgU, hcd.smul contDiffOn_const, fun g hgU hgG => ?_⟩` and prove the remaining obligations. Use `show f g • T = f' g • T`.

Rewrite using `[heq g hgU hgG]`. Establish `h1` using `hb u v hu hv hl g hg`. Establish `hd : dLR u v (fun g => f g • T) g = dLR u v f g • T`. Rewrite using `[dLR_smul_const]`. Rewrite using `[hd, norm_smul, ← mul_assoc]`.

Conclude with `mul_le_mul_of_nonneg_right h1 (norm_nonneg T)`.
-/
theorem ccle_smul_const {A : ℝ} {m : ℕ} {f : Mat k r → ℂ} {c : ℝ} (T : E) (hf : CCle A m f c) :
    CCle A m (fun g => f g • T) (c * ‖T‖) := by
  obtain ⟨hCk, hb⟩ := hf
  refine ⟨fun g₀ hg₀ => ?_, fun u v hu hv hl g hg => ?_⟩
  · obtain ⟨U, f', hU, hgU, hcd, heq⟩ := hCk g₀ hg₀
    refine ⟨U, fun g => f' g • T, hU, hgU, hcd.smul contDiffOn_const, fun g hgU hgG => ?_⟩
    show f g • T = f' g • T
    rw [heq g hgU hgG]
  · have h1 := hb u v hu hv hl g hg
    have hd : dLR u v (fun g => f g • T) g = dLR u v f g • T := by
      rw [dLR_smul_const]
    rw [hd, norm_smul, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right h1 (norm_nonneg T)

end SmulConstantLinearity

/- English proof (translation)
Introduce `k r Wp _ _ _ A m f X₀ hf`. Take `⟨c, hc⟩` from `hf`. Conclude with `⟨c * ‖X₀‖, SmulConstantLinearity.ccle_smul_const X₀ hc⟩`.
-/
theorem stCut1p (h : UnitaryGroupStructuralFacts) : StCut1p := by
  intro k r Wp _ _ _ A m f X₀ hf
  obtain ⟨c, hc⟩ := hf
  exact ⟨c * ‖X₀‖, SmulConstantLinearity.ccle_smul_const X₀ hc⟩

end ReciprocityTheory.ChartRestriction.DS.Mult1
