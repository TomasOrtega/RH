import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.MeasBAll

noncomputable section

namespace MassDataIdxSteps

open MeasureTheory
open scoped ENNReal Pointwise

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.
-/
theorem redIdx : RedIdx := by
  intro K Q _ _ _ ρ hρ A hA
  have h1 : A.index = (A.map ρ).index := by
    rw [← Subgroup.index_comap_of_surjective (A.map ρ) hρ, Subgroup.comap_map_eq, sup_eq_left.mpr hA]
  rw [h1, Subgroup.index_mul_card]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Introduce a local definition for the expression. Introduce a local definition for the expression.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities.

Supply the required witnesses or components. Assume the hypotheses and unpack their components. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Assume the hypotheses and unpack their components. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact.

Chain the equalities or inequalities of the calculation. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem haarIdx : HaarIdx := by
  intro G _ _ _ _ _ μ _ K A hAK hA hne
  have hcard : Nat.card (K ⧸ A.subgroupOf K) = A.relIndex K := rfl
  have : Finite (K ⧸ A.subgroupOf K) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hne)
  let := Fintype.ofFinite (K ⧸ A.subgroupOf K)
  let r : K ⧸ A.subgroupOf K → G := fun q => ((Quotient.out q : K) : G)
  have hr : ∀ q, r q ∈ K := fun q => (Quotient.out q).2
  have hmk : ∀ q, (QuotientGroup.mk (Quotient.out q) : K ⧸ A.subgroupOf K) = q :=
    fun q => QuotientGroup.out_eq' q
  have hunion : (K : Set G) = ⋃ q, r q • (A : Set G) := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_smul_set, smul_eq_mul, SetLike.mem_coe]
    constructor
    · intro hx
      set q : K ⧸ A.subgroupOf K := QuotientGroup.mk ⟨x, hx⟩
      have hq : (Quotient.out q)⁻¹ * ⟨x, hx⟩ ∈ A.subgroupOf K := by
        rw [← QuotientGroup.eq, hmk]
      rw [Subgroup.mem_subgroupOf] at hq
      exact ⟨q, (r q)⁻¹ * x, by simpa [r] using hq, by simp⟩
    · rintro ⟨q, a, ha, rfl⟩
      exact K.mul_mem (hr q) (hAK ha)
  have hdisj : Pairwise (Function.onFun Disjoint fun q => r q • (A : Set G)) := by
    intro q q' hqq'
    rw [Function.onFun, Set.disjoint_left]
    rintro x ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
    apply hqq'
    rw [← hmk q, ← hmk q', QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simp only [smul_eq_mul] at hab
    have key : (r q)⁻¹ * r q' = a * b⁻¹ := by
      calc (r q)⁻¹ * r q' = (r q)⁻¹ * (r q' * b) * b⁻¹ := by group
        _ = (r q)⁻¹ * (r q * a) * b⁻¹ := by rw [hab]
        _ = a * b⁻¹ := by group
    have : (((Quotient.out q)⁻¹ * Quotient.out q' : K) : G) = (r q)⁻¹ * r q' := rfl
    rw [this, key]
    exact A.mul_mem ha (A.inv_mem hb)
  have hmeas : ∀ q, MeasurableSet (r q • (A : Set G)) := fun q => (hA.smul (r q)).measurableSet
  rw [hunion, measure_iUnion hdisj hmeas, tsum_fintype]
  simp only [measure_smul]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card, hcard]

end MassDataIdxSteps
