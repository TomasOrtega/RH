import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.LocalDensityIntegral

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open Formalism.MainNotions.S
open ValuativeRel

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Chain the equalities or inequalities of the calculation. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Supply the required witnesses or components.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Assume the hypotheses and unpack their components. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

Supply the required witnesses or components. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem fr_max {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : Loc.LocE F E) (hl : IsNonarchimedeanLocalField F)
    (hE : ∀ x : E, x ≠ 0 → IsUnit x) (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) :
    (Ideal.span {piO L ϖ}).IsMaximal := by
  have hinj := fl_inj L
  rw [Ideal.isMaximal_iff]
  constructor
  · intro h1
    rw [Ideal.mem_span_singleton'] at h1
    obtain ⟨z, hz⟩ := h1
    have hz' : (z : E) * algebraMap F E ϖ = 1 := by
      have := congrArg Subtype.val hz
      simpa [piO] using this
    have hϖ0 : (ϖ : F) ≠ 0 := by
      intro h; apply hϖ.ne_zero; exact Subtype.ext h
    have hzF : (z : E) = algebraMap F E (ϖ : F)⁻¹ := by
      have h2 : algebraMap F E (ϖ : F) * algebraMap F E (ϖ : F)⁻¹ = 1 := by
        rw [← map_mul, mul_inv_cancel₀ hϖ0, map_one]
      calc (z : E) = (z : E) * (algebraMap F E ϖ * algebraMap F E (ϖ : F)⁻¹) := by rw [h2, mul_one]
        _ = algebraMap F E (ϖ : F)⁻¹ := by rw [← mul_assoc, hz', one_mul]
    have hmem : (ϖ : F)⁻¹ ∈ 𝒪[F] := fl_mem_int L hinj (hzF ▸ z.2)
    apply hϖ.not_isUnit
    have h3 : ϖ * ⟨_, hmem⟩ = 1 := Subtype.ext (by
      show (ϖ : F) * (ϖ : F)⁻¹ = 1
      exact mul_inv_cancel₀ hϖ0)
    exact ⟨⟨ϖ, ⟨_, hmem⟩, h3, by rw [mul_comm]; exact h3⟩, rfl⟩
  · intro J x hIJ hx hxJ
    have hnd : ¬ ∃ z ∈ L.O, (x : E) = algebraMap F E ϖ * z := by
      rintro ⟨z, hz, hxz⟩
      apply hx
      rw [Ideal.mem_span_singleton']
      exact ⟨⟨z, hz⟩, Subtype.ext (by simp [piO, hxz, mul_comm])⟩
    obtain ⟨y, hy, hxy⟩ := fl_local L hl hE hinj ϖ hϖ x x.2 hnd
    have : (1 : L.O) = x * ⟨y, hy⟩ := Subtype.ext (by simp [hxy])
    rw [this]
    exact J.mul_mem_right _ hxJ

end PI.UnitaryGroupMassFormula.CntFormula
