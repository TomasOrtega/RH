import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsConeVarInj
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsConeVarNumerator
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Replace the relevant objects with their definitions. Apply an available result and prove the equalities needed to match it to the conclusion. By extensionality, compare the relevant components.

Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending. Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Establish an intermediate fact. Simplify using the standard rewrite rules.

Use linear arithmetic over natural numbers and integers. Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending. A detailed English derivation is pending.
-/
theorem ConeVarInj.proof (hNum : ConeVarNumerator.Statement.{u}) : ConeVarInj.Statement.{u} := by
  intro F _ K _ _ ι _ P hP W hW hPW v hv
  have := hP.isPrime
  have := hW.isPrime
  rw [injective_iff_map_eq_zero]
  intro p hp
  obtain ⟨B, g, h, -, hgW, hh, hc, hφ⟩ := hNum F K ι P hP W hW hPW v hv p

  have hu : ∀ d : K →₀ ℕ, IsMultiHomog (∏ k, (X ⟨k, v k⟩ : MRing ι F) ^ d k) ⇑d := fun d => by
    unfold IsMultiHomog
    convert IsWeightedHomogeneous.prod Finset.univ (fun k => (X ⟨k, v k⟩ : MRing ι F) ^ d k)
      (fun k => d k • blockWeight ι ⟨k, v k⟩)
      (fun k _ => (isWeightedHomogeneous_X F (blockWeight ι) ⟨k, v k⟩).pow (d k)) using 1
    ext k
    simp [blockWeight, Finset.sum_apply, Pi.single_apply]
  have huW : ∀ d : K →₀ ℕ, ∏ k, (X ⟨k, v k⟩ : MRing ι F) ^ d k ∉ W := fun d => by
    rw [Ideal.IsPrime.prod_mem_iff]
    rintro ⟨k, -, hk⟩
    exact hv k (hW.isPrime.mem_of_pow_mem _ hk)
  have hN : ∑ d ∈ p.support, h d * ∏ k, (X ⟨k, v k⟩ : MRing ι F) ^ d k ∈ P := by
    have hg0 : algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P g) ≠ 0 := by
      rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
      exact fun hg => hgW (hPW hg)
    rw [hp, ZeroMemClass.coe_zero, eq_comm, div_eq_zero_iff, or_iff_left hg0,
      IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem] at hφ
    exact hφ
  refine MvPolynomial.ext _ _ fun d => ?_
  rw [coeff_zero]
  by_contra hd
  have hcomp := hP.multiHomog _ hN (B + ⇑d)
  rw [map_sum, Finset.sum_eq_single d] at hcomp
  · rw [((hh d).mul (hu d)).weightedHomogeneousComponent_same] at hcomp
    have hhd : h d ∈ P := (hP.isPrime.mem_or_mem hcomp).resolve_right fun hm => huW d (hPW hm)
    apply hd
    apply Subtype.ext
    rw [hc d, Ideal.Quotient.eq_zero_iff_mem.mpr hhd, map_zero, zero_div]
    rfl
  · intro d' _ hne
    refine ((hh d').mul (hu d')).weightedHomogeneousComponent_ne _ fun heq => hne ?_
    ext k
    have := congrFun heq k
    simp only [Pi.add_apply] at this
    omega
  · exact fun hn => absurd (mem_support_iff.mpr hd) hn

end

end GroundTheory.Heights₂.Heights.FieldNumbers
