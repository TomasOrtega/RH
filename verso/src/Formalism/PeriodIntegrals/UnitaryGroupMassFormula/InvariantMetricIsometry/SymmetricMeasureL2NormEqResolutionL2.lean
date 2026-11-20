import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InvariantMetricIsometry.ColChoiceFintype

noncomputable section

open Matrix

namespace PI.IsoInvMetricW

open PI.IsoInvMetric

variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] {N : ℕ} {nu : Lt → YoungDiagram}

/- English proof (translation)
Unfold `l2 ipl`. Rewrite using `[finsum_eq_sum_of_fintype]`. Use `push_cast`. Use `Finset.sum_congr rfl fun J _ => ?_` and prove the remaining obligations. Rewrite using `[Complex.star_def, Complex.conj_mul']`.
-/
theorem symmetricMeasure_l2Norm_eq_resolutionL2 (φ : LaC N nu) : ((l2 φ : ℝ) : ℂ) = ipl φ φ := by
  unfold l2 ipl
  rw [finsum_eq_sum_of_fintype]
  push_cast
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [Complex.star_def, Complex.conj_mul']

/- English proof (translation)
Simplify using `[ipl]`.
-/
theorem ipl_zero_left (ψ : LaC N nu) : ipl 0 ψ = 0 := by
  simp [ipl]

/- English proof (translation)
Simplify using `[ipl, add_mul, Finset.sum_add_distrib]`.
-/
theorem ipl_add_left (φ φ' ψ : LaC N nu) : ipl (φ + φ') ψ = ipl φ ψ + ipl φ' ψ := by
  simp [ipl, add_mul, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `[ipl, Finset.mul_sum, mul_assoc]`.
-/
theorem ipl_smul_left (c : ℂ) (φ ψ : LaC N nu) : ipl (c • φ) ψ = starRingEnd ℂ c * ipl φ ψ := by
  simp [ipl, Finset.mul_sum, mul_assoc]

/- English proof (translation)
Introduce `Lt _ _ N nu`. Use `⟨fun k hk => ⟨fun φ hφ => ⟨hS Lt N nu k φ hφ, ?_⟩, fun hle => ?_⟩, fun ip hip => ?_⟩` and prove the remaining obligations. Apply `Complex.ofReal_injective` to reduce the goal to its premises. Rewrite using `[symmetricMeasure_l2Norm_eq_resolutionL2, symmetricMeasure_l2Norm_eq_resolutionL2, hU Lt N nu k hk]`. Rewrite using `[hH Lt N nu k]`.

Apply `Complex.ofReal_injective` to reduce the goal to its premises. Rewrite using `[symmetricMeasure_l2Norm_eq_resolutionL2, hU Lt N nu k hk, ← symmetricMeasure_l2Norm_eq_resolutionL2, hN Lt N nu hle]`. Establish `hu : u0 N nu ∈ Vnu N nu` using `Submodule.subset_span ⟨_, rfl⟩`. Establish `key : ∀ φ ∈ Vnu N nu, ∀ ψ ∈ Vnu N nu, ip φ ψ = ipl φ ψ`. Introduce `φ hφ ψ hψ`.

Proceed by induction on `hφ using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨y, rfl⟩` from `hx`. Take `⟨k, hk, c, hc⟩` from `hG Lt N nu y`. Take `⟨ψ', hψ', e1⟩ : ∃ ψ', ψ' ∈ Vnu N nu ∧ ψ = VnuMap nu k ψ'` from `⟨_, hS Lt N nu _ ψ hψ, (hI Lt N nu k hk ψ).symm⟩`.

Establish `h2 : ip (VnuMap nu k (u0 N nu)) (VnuMap nu k ψ') = ipl (VnuMap nu k (u0 N nu)) (VnuMap nu k ψ')`. Rewrite using `[(hip k hk).1 _ hu _ hψ', hW Lt N nu ip hip ψ' hψ', hU Lt N nu k hk]`. Rewrite using `[hc, hH Lt N nu k, LinearMap.map_smulₛₗ₂, ipl_smul_left, e1, h2, smul_eq_mul]`. Consider the case `zero => simp [ipl_zero_left]`. Consider the case `add x y _ _ hx hy => rw [LinearMap.map_add₂, hx, hy, ipl_add_left]`.

Consider the case `smul a x _ hx => rw [LinearMap.map_smulₛₗ₂, hx, ipl_smul_left, smul_eq_mul]`. Introduce `φ hφ`. Rewrite using `[symmetricMeasure_l2Norm_eq_resolutionL2]`. Conclude with `key φ hφ φ hφ`.
-/
theorem isoInvMetric_of (hU : Unit) (hI : InvK) (hS : Stab) (hH : HvCols) (hN : Norm1)
    (hG : Gen) (hW : HW) : IsoInvMetric := by
  intro Lt _ _ N nu
  refine ⟨fun k hk => ⟨fun φ hφ => ⟨hS Lt N nu k φ hφ, ?_⟩, fun hle => ?_⟩, fun ip hip => ?_⟩
  · apply Complex.ofReal_injective
    rw [symmetricMeasure_l2Norm_eq_resolutionL2, symmetricMeasure_l2Norm_eq_resolutionL2, hU Lt N nu k hk]
  · rw [hH Lt N nu k]
    apply Complex.ofReal_injective
    rw [symmetricMeasure_l2Norm_eq_resolutionL2, hU Lt N nu k hk, ← symmetricMeasure_l2Norm_eq_resolutionL2, hN Lt N nu hle]
  · have hu : u0 N nu ∈ Vnu N nu := Submodule.subset_span ⟨_, rfl⟩
    have key : ∀ φ ∈ Vnu N nu, ∀ ψ ∈ Vnu N nu, ip φ ψ = ipl φ ψ := by
      intro φ hφ ψ hψ
      induction hφ using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨y, rfl⟩ := hx
        obtain ⟨k, hk, c, hc⟩ := hG Lt N nu y
        obtain ⟨ψ', hψ', e1⟩ : ∃ ψ', ψ' ∈ Vnu N nu ∧ ψ = VnuMap nu k ψ' :=
          ⟨_, hS Lt N nu _ ψ hψ, (hI Lt N nu k hk ψ).symm⟩
        have h2 : ip (VnuMap nu k (u0 N nu)) (VnuMap nu k ψ') =
            ipl (VnuMap nu k (u0 N nu)) (VnuMap nu k ψ') := by
          rw [(hip k hk).1 _ hu _ hψ', hW Lt N nu ip hip ψ' hψ', hU Lt N nu k hk]
        rw [hc, hH Lt N nu k, LinearMap.map_smulₛₗ₂, ipl_smul_left, e1, h2, smul_eq_mul]
      | zero => simp [ipl_zero_left]
      | add x y _ _ hx hy => rw [LinearMap.map_add₂, hx, hy, ipl_add_left]
      | smul a x _ hx => rw [LinearMap.map_smulₛₗ₂, hx, ipl_smul_left, smul_eq_mul]
    intro φ hφ
    rw [symmetricMeasure_l2Norm_eq_resolutionL2]
    exact key φ hφ φ hφ

end PI.IsoInvMetricW
