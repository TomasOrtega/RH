import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsCN
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem finite_setOf_weight_blockWeight_eq {K : Type} [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (m : K → ℕ) :
    {d : (Σ k, ι k) →₀ ℕ | Finsupp.weight (blockWeight ι) d = m}.Finite := by
  refine ((Set.Finite.pi' fun v : (Σ k, ι k) => Set.finite_le_nat (m v.1)).preimage
    DFunLike.coe_injective.injOn).subset ?_
  intro d hd
  simp only [Set.mem_ofPred_eq] at hd
  simp only [Set.mem_preimage, Set.mem_ofPred_eq]
  intro v
  rw [← hd, Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]
  by_cases hv : v ∈ d.support
  · refine le_trans ?_ (Finset.single_le_sum
      (f := fun u => (d u • blockWeight ι u) v.1) (fun _ _ => Nat.zero_le _) hv)
    simp [blockWeight]
  · simp [Finsupp.notMem_support_iff.mp hv]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Simplify to obtain the desired conclusion from the available facts. Treat this case separately.

Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.
-/
theorem mem_of_C_pow_mul_mem {O : Type u} [CommRing O] {K : Type} {ι : K → Type}
    {P : Ideal (MRing ι O)} {ϖ : O} (hP : ∀ x, C ϖ * x ∈ P → x ∈ P) :
    ∀ (n : ℕ) (y : MRing ι O), C (ϖ ^ n) * y ∈ P → y ∈ P := by
  intro n
  induction n with
  | zero => intro y hy; simpa using hy
  | succ n ih =>
    intro y hy
    apply hP
    apply ih
    rwa [pow_succ, map_mul, mul_assoc] at hy

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Consider separately whether the proposition holds or fails. Prove the first alternative. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem GradedPieceFree.proof : GradedPieceFree.Statement := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P hP m
  have hfg : (weightedHomogeneousSubmodule O (blockWeight ι) m).FG := by
    rw [weightedHomogeneousSubmodule_eq_finsupp_supported, ← Module.Finite.iff_fg]
    have := (finite_setOf_weight_blockWeight_eq ι m).to_subtype
    exact Module.Finite.of_basis (basisRestrictSupport O _)
  have hfin : Module.Finite O (gradedPieceR P m) := Module.Finite.iff_fg.mpr (hfg.map _)
  have htf : Module.IsTorsionFree O (gradedPieceR P m) := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun c x hcx => ?_
    by_cases hc : c = 0
    · exact Or.inl hc
    right
    obtain ⟨n, w, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc hϖ
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (x : MRing ι O ⧸ P)
    have h1 : ((↑w * ϖ ^ n) • (x : MRing ι O ⧸ P)) = 0 := congrArg Subtype.val hcx
    rw [← hy, ← Ideal.Quotient.mkₐ_eq_mk O, ← map_smul, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem, smul_eq_C_mul] at h1
    have h2 : C (ϖ ^ n) * y ∈ P := by
      have := P.mul_mem_left (C (↑w⁻¹ : O)) h1
      rwa [← mul_assoc, ← map_mul, ← mul_assoc, Units.inv_mul, one_mul] at this
    apply Subtype.ext
    rw [← hy, Submodule.coe_zero, Ideal.Quotient.eq_zero_iff_mem]
    exact mem_of_C_pow_mul_mem hP n y h2
  exact ⟨Module.free_of_finite_type_torsion_free', hfin⟩

end GroundTheory.Heights₂.Heights.NumbersDVR
