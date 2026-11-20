import Mathlib
import Formalism.LocalRingCardinality.DataSpaces
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeAutomorphismFiniteness.MjSmulRight
import Lemmata.GeneralBFactThirdExtra.Imports

noncomputable section

namespace PI.AutLzFinite.SlopeTestRemainingChoices

open Formalism.BasicNotions NumberField

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E}

/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem exists_smul_mem (Λ : Submodule (𝓞 E) S.V) (hΛ : Submodule.span E (Λ : Set S.V) = ⊤) (v : S.V) :
    ∃ d : 𝓞 E, d ≠ 0 ∧ d • v ∈ Λ := by
  first | exact Bl.general_b_fact_third_extra.goal1 .. | (apply Bl.general_b_fact_third_extra.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_third_extra.goal1 <;> assumption) | (apply @Bl.general_b_fact_third_extra.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_third_extra.goal1 <;> assumption) | (apply @Bl.general_b_fact_third_extra.goal1 <;> first | assumption | infer_instance)

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Fix the arbitrary inputs or assume the hypotheses.

A detailed English derivation is pending.
-/
theorem finite_of_integral_bound (t : E) (ht : t ≠ 0) (C : ℝ) :
    {a : E | IsIntegral ℤ (t * a) ∧ ∀ τ : E →+* ℂ, ‖τ a‖ ≤ C}.Finite := by
  set K : ℝ := ∑ τ : E →+* ℂ, ‖τ t‖
  apply Set.Finite.of_finite_image (f := fun a => t * a)
  · apply (Embeddings.finite_of_norm_le E ℂ (K * C)).subset
    rintro _ ⟨a, ⟨ha1, ha2⟩, rfl⟩
    refine ⟨ha1, fun τ => ?_⟩
    rw [map_mul, norm_mul]
    have h1 : ‖τ t‖ ≤ K := Finset.single_le_sum (f := fun τ : E →+* ℂ => ‖τ t‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ τ)
    have h2 := ha2 τ
    have h3 : 0 ≤ ‖τ a‖ := norm_nonneg _
    nlinarith [norm_nonneg (τ t)]
  · intro a _ b _ hab
    exact mul_left_cancel₀ ht hab

end PI.AutLzFinite.SlopeTestRemainingChoices
