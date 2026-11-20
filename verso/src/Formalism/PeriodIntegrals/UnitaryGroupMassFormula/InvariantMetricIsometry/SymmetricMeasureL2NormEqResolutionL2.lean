import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InvariantMetricIsometry.ColChoiceFintype

noncomputable section

open Matrix

namespace PI.IsoInvMetricW

open PI.IsoInvMetric

variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] {N : ℕ} {nu : Lt → YoungDiagram}

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
theorem symmetricMeasure_l2Norm_eq_resolutionL2 (φ : LaC N nu) : ((l2 φ : ℝ) : ℂ) = ipl φ φ := by
  unfold l2 ipl
  rw [finsum_eq_sum_of_fintype]
  push_cast
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [Complex.star_def, Complex.conj_mul']

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem ipl_zero_left (ψ : LaC N nu) : ipl 0 ψ = 0 := by
  simp [ipl]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem ipl_add_left (φ φ' ψ : LaC N nu) : ipl (φ + φ') ψ = ipl φ ψ + ipl φ' ψ := by
  simp [ipl, add_mul, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem ipl_smul_left (c : ℂ) (φ ψ : LaC N nu) : ipl (c • φ) ψ = starRingEnd ℂ c * ipl φ ψ := by
  simp [ipl, Finset.mul_sum, mul_assoc]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Proceed by induction. Treat this case separately. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Treat this case separately. Treat this case separately.

Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
