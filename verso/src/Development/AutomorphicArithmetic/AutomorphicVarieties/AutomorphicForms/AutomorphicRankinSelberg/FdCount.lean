import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.StripInt

open MeasureTheory Set UpperHalfPlane
open scoped MatrixGroups ENNReal

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Replace the relevant objects with their definitions. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Simplify using the standard rewrite rules. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities.

Separate the alternatives or extract the components of the hypothesis. Reduce the claim to the hypotheses of an applicable result. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem UpperTheory.V.Af.Rs.fdCount :
    UpperTheory.V.Af.Rs.FdNull → UpperTheory.V.Af.Rs.FdCount := by
  intro hN
  unfold UpperTheory.V.Af.Rs.FdNull at hN
  unfold UpperTheory.V.Af.Rs.FdCount
  haveI : Countable (Matrix (Fin 2) (Fin 2) ℤ) := inferInstanceAs (Countable (Fin 2 → Fin 2 → ℤ))
  haveI : Countable SL(2, ℤ) :=
    inferInstanceAs (Countable {A : Matrix (Fin 2) (Fin 2) ℤ // A.det = 1})
  have hnull : ∀ γ : SL(2, ℤ),
      volume ((fun z : ℍ => γ • z) ⁻¹' (ModularGroup.fd \ ModularGroup.fdo)) = 0 := by
    intro γ
    have : (fun z : ℍ => γ • z) = fun z : ℍ => ((γ : GL (Fin 2) ℝ)) • z := rfl
    rw [this, measure_preimage_smul]
    exact hN
  have hB := measure_iUnion_null hnull
  rw [ae_iff]
  refine measure_mono_null ?_ hB
  intro z hz
  by_contra hzB
  simp only [mem_iUnion, mem_preimage, not_exists] at hzB
  obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd z
  have hgo : g • z ∈ ModularGroup.fdo := by
    by_contra h
    exact hzB g ⟨hg, h⟩
  have hne : g ≠ -g := by
    intro h
    have h1 : (1 : SL(2, ℤ)) = -1 := by
      have := congrArg (fun A => A * g⁻¹) h
      simpa using this
    have := congrArg (fun A : SL(2, ℤ) => (A : Matrix (Fin 2) (Fin 2) ℤ) 0 0) h1
    simp at this
  apply hz
  rw [tsum_eq_sum (s := {g, -g}) ?_]
  · rw [Finset.sum_pair hne]
    have hg' : (-g) • z ∈ ModularGroup.fd := by simpa using hg
    rw [indicator_of_mem hg, indicator_of_mem hg', one_add_one_eq_two]
  · intro γ hγ
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hγ
    apply indicator_of_notMem
    intro hmem
    have heq : γ • z = (γ * g⁻¹) • (g • z) := by
      rw [smul_smul, inv_mul_cancel_right]
    rw [heq] at hmem
    rcases ModularGroup.eq_one_or_neg_one_of_mem_fdo_mem_fd hgo hmem with h | h
    · exact hγ.1 (mul_inv_eq_one.mp h)
    · apply hγ.2
      rw [mul_inv_eq_iff_eq_mul] at h
      rw [h]
      simp
