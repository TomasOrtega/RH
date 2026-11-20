import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramIsHermitianL2EqDoubleSumStatement
open Filter Topology MeasureTheory GlobalTheory.HSAmp
open scoped ComplexOrder Matrix

namespace GlobalTheory.HSAmp

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem gram_posDef : ∀ (S : Type) (Y : S → Type) [∀ σ, MeasurableSpace (Y σ)] (ι : Type) [Fintype ι] [DecidableEq ι]
    (μ : ∀ σ, Measure (Y σ)) (v : ∀ σ, Y σ → ι → ℂ), IsFam μ v → (∀ c : ι → ℂ, l2 μ v c = 0 → c = 0) →
    (gram μ v).PosDef := by
  intro S Y _ ι _ _ μ v hF hinj
  obtain ⟨hH, hl⟩ := GlobalTheory.T.gram_isHermitian_l2_eq_double_sum S Y ι μ v hF
  refine Matrix.posDef_iff_dotProduct_mulVec.2 ⟨hH, fun x hx => ?_⟩
  obtain ⟨-, h0, heq⟩ := hl (fun i => (starRingEnd ℂ) (x i))
  have hform : star x ⬝ᵥ (gram μ v *ᵥ x) = ((l2 μ v (fun i => (starRingEnd ℂ) (x i)) : ℝ) : ℂ) := by
    rw [heq]
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, Complex.star_def, Complex.conj_conj]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hform]
  have hne : l2 μ v (fun i => (starRingEnd ℂ) (x i)) ≠ 0 := by
    intro h
    apply hx
    funext i
    have := congrFun (hinj _ h) i
    simpa using this
  exact_mod_cast lt_of_le_of_ne h0 (Ne.symm hne)

end GlobalTheory.HSAmp
