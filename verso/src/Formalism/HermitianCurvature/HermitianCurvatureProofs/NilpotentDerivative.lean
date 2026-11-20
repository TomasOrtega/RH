import Formalism.HermitianCurvature.HermitianCurvatureProofs.JfSmoothBuiltOfLeaves

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
Distinguish the cases in `hφ : DifferentiableAt ℝ φ 0`. Conclude with `deriv_smul_const hφ v`. Distinguish the cases in `hv : v = 0`. Simplify using `[hv]`. Rewrite using `[deriv_zero_of_not_differentiableAt hφ, zero_smul]`.

Apply `deriv_zero_of_not_differentiableAt` to reduce the goal to its premises. Introduce `hd`. Apply `hφ` to reduce the goal to its premises. Take `⟨ℓ, -, hℓv⟩` from `exists_dual_vector ℂ v (norm_ne_zero_iff.mpr hv)`. Establish `h1 : DifferentiableAt ℝ (fun t => ℓ (φ t • v)) 0` using `(ℓ.restrictScalars ℝ).differentiableAt.comp 0 hd`.

Establish `hn : ℓ v ≠ 0`. Rewrite using `[hℓv]`. Conclude with `RCLike.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hv)`. Establish `h2 : φ = fun t => ℓ (φ t • v) * (ℓ v)⁻¹`. Use function extensionality and compare the values at `t`.

Rewrite using `[map_smul, smul_eq_mul, mul_assoc, mul_inv_cancel₀ hn, mul_one]`. Rewrite using `[h2]`. Conclude with `h1.mul_const _`.
-/
theorem nd_deriv_smul_const {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (φ : ℝ → ℂ) (v : E) :
    deriv (fun t => φ t • v) 0 = deriv φ 0 • v := by
  by_cases hφ : DifferentiableAt ℝ φ 0
  · exact deriv_smul_const hφ v
  by_cases hv : v = 0
  · simp [hv]
  rw [deriv_zero_of_not_differentiableAt hφ, zero_smul]
  apply deriv_zero_of_not_differentiableAt
  intro hd
  apply hφ
  obtain ⟨ℓ, -, hℓv⟩ := exists_dual_vector ℂ v (norm_ne_zero_iff.mpr hv)
  have h1 : DifferentiableAt ℝ (fun t => ℓ (φ t • v)) 0 :=
    (ℓ.restrictScalars ℝ).differentiableAt.comp 0 hd
  have hn : ℓ v ≠ 0 := by
    rw [hℓv]; exact RCLike.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hv)
  have h2 : φ = fun t => ℓ (φ t • v) * (ℓ v)⁻¹ := by
    funext t
    rw [map_smul, smul_eq_mul, mul_assoc, mul_inv_cancel₀ hn, mul_one]
  rw [h2]
  exact h1.mul_const _

/- English proof (translation)
Assemble the required witnesses or components as `⟨hX t, (hX t).1, fun _ ha => absurd ha (Nat.not_lt_zero _)⟩`.
-/
theorem nd_exp_mem {k r : ℕ} {X : B.Mat k r} (hX : X ∈ JfS.lieOf (Nset k r)) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) ∈ Q.Nlev k r 0 :=
  ⟨hX t, (hX t).1, fun _ ha => absurd ha (Nat.not_lt_zero _)⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨⟨hg.1, fun _ ha => absurd ha (Nat.not_lt_zero _)⟩, hg.2⟩`.
-/
theorem nd_om_mem {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {g : B.Mat k r} (hg : g ∈ JF.Om k r z z') :
    g ∈ Q.Glev k r 0 ∩ Q.OmPlus k r z z' :=
  ⟨⟨hg.1, fun _ ha => absurd ha (Nat.not_lt_zero _)⟩, hg.2⟩

/- English proof (translation)
Introduce `k r Wp Wq _ _ _ _ D m J hJ`. Take `⟨_, hL, hR, _⟩` from `hJ`. Prove the components needed by the constructor for the conclusion. Introduce `X hX`. Use `⟨deriv (fun t : ℝ => psi k r D.z' cStd (NormedSpace.exp ((t : ℂ) • X))) 0, fun g hg => ?_⟩` and prove the remaining obligations.

Use `show deriv (fun t : ℝ => J (g * NormedSpace.exp ((t : ℂ) • X))) 0 = _`. Establish `e : (fun t : ℝ => J (g * NormedSpace.exp ((t : ℂ) • X))) = fun t : ℝ => psi k r D.z' cStd (NormedSpace.exp ((t : ℂ) • X)) • J g`. Use function extensionality and compare the values at `fun t => hR g (nd_om_mem hg) _ (nd_exp_mem hX t)`. Rewrite using `[e, nd_deriv_smul_const]`. Introduce `X hX`.

Use `⟨deriv (fun t : ℝ => psi k r D.z cStd (NormedSpace.exp ((t : ℂ) • X))) 0, fun g hg => ?_⟩` and prove the remaining obligations. Use `show deriv (fun t : ℝ => J (NormedSpace.exp ((t : ℂ) • X) * g)) 0 = _`. Establish `e : (fun t : ℝ => J (NormedSpace.exp ((t : ℂ) • X) * g)) = fun t : ℝ => psi k r D.z cStd (NormedSpace.exp ((t : ℂ) • X)) • J g`. Use function extensionality and compare the values at `fun t => hL g (nd_om_mem hg) _ (nd_exp_mem hX t)`. Rewrite using `[e, nd_deriv_smul_const]`.
-/
theorem nilpotent_derivative : NDiff := by
  intro k r Wp Wq _ _ _ _ D m J hJ
  obtain ⟨_, hL, hR, _⟩ := hJ
  constructor
  · intro X hX
    refine ⟨deriv (fun t : ℝ => psi k r D.z' cStd (NormedSpace.exp ((t : ℂ) • X))) 0, fun g hg => ?_⟩
    show deriv (fun t : ℝ => J (g * NormedSpace.exp ((t : ℂ) • X))) 0 = _
    have e : (fun t : ℝ => J (g * NormedSpace.exp ((t : ℂ) • X))) =
        fun t : ℝ => psi k r D.z' cStd (NormedSpace.exp ((t : ℂ) • X)) • J g :=
      funext fun t => hR g (nd_om_mem hg) _ (nd_exp_mem hX t)
    rw [e, nd_deriv_smul_const]
  · intro X hX
    refine ⟨deriv (fun t : ℝ => psi k r D.z cStd (NormedSpace.exp ((t : ℂ) • X))) 0, fun g hg => ?_⟩
    show deriv (fun t : ℝ => J (NormedSpace.exp ((t : ℂ) • X) * g)) 0 = _
    have e : (fun t : ℝ => J (NormedSpace.exp ((t : ℂ) • X) * g)) =
        fun t : ℝ => psi k r D.z cStd (NormedSpace.exp ((t : ℂ) • X)) • J g :=
      funext fun t => hL g (nd_om_mem hg) _ (nd_exp_mem hX t)
    rw [e, nd_deriv_smul_const]

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
