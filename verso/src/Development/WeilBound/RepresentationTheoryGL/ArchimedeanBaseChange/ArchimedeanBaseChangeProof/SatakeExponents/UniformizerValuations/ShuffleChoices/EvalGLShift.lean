import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FiniteDiscreteFamilies.PeakCone

noncomputable section

namespace PositivityTheory.Rg.BcB.F.F5

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem evalGL_shift {n : ℕ} (c : (Fin n → ℤ) →₀ ℂ) (y : Fin n → ℤ) (ξ : Fin n → ℂˣ) :
    evalGL (c.mapDomain (· + y)) ξ = ((∏ i, ξ i ^ y i : ℂˣ) : ℂ) * evalGL c ξ := by
  unfold evalGL
  rw [Finsupp.sum_mapDomain_index (by simp) (by intros; ring), Finsupp.mul_sum]
  refine Finsupp.sum_congr fun x _ => ?_
  simp only [Pi.add_apply, zpow_add, Finset.prod_mul_distrib, Units.val_mul]
  ring

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem evalGL_sub {n : ℕ} (c d : (Fin n → ℤ) →₀ ℂ) (p q : ℂ) (ξ : Fin n → ℂˣ) :
    evalGL (p • c - q • d) ξ = p * evalGL c ξ - q * evalGL d ξ := by
  unfold evalGL
  rw [Finsupp.sum_sub_index (by intros; ring), Finsupp.sum_smul_index (by simp), Finsupp.sum_smul_index (by simp),
    Finsupp.mul_sum, Finsupp.mul_sum]
  simp [mul_assoc]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.

Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Assume the negation of the conclusion and derive a contradiction. Reduce the claim to the hypotheses of an applicable result. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Establish an intermediate fact.

Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation.

Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Separate the alternatives or extract the components of the hypothesis. Extract witnesses or component facts from the available result. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact.

Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Separate the alternatives or extract the components of the hypothesis. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem peakCone : PeakCone := by
  classical
  intro n M α S
  induction S using Finset.induction_on with
  | empty =>
    intro _
    have hx0 : (fun i : Fin n => |M| * ((n : ℤ) - (i : ℕ))) ∈ coneGL n M := by
      intro i j hij
      have : ((i : ℕ) : ℤ) + 1 ≤ (j : ℕ) := by exact_mod_cast hij
      have := le_abs_self M
      have := abs_nonneg M
      nlinarith
    refine ⟨Finsupp.single (fun i : Fin n => |M| * ((n : ℤ) - (i : ℕ)))
      (((∏ i, α i ^ (|M| * ((n : ℤ) - (i : ℕ))) : ℂˣ)⁻¹ : ℂˣ) : ℂ), ?_, ?_, by simp⟩
    · intro z hz
      rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hz)]
      exact hx0
    · unfold evalGL
      rw [Finsupp.sum_single_index (by simp)]
      exact Units.inv_mul _
  | insert β S hβ ih =>
    intro hα
    simp only [Finset.mem_insert, not_or] at hα
    obtain ⟨c, hc, h1, h0⟩ := ih hα.2
    obtain ⟨y, hy, hne⟩ : ∃ y ∈ coneGL n 0, (∏ i, α i ^ y i : ℂˣ) ≠ ∏ i, β i ^ y i := by
      by_contra hcon
      push Not at hcon
      apply hα.1
      funext k
      have h0' := hcon (fun i : Fin n => (n : ℤ) - (i : ℕ)) (fun i j hij => by
        have : ((i : ℕ) : ℤ) + 1 ≤ (j : ℕ) := by exact_mod_cast hij
        simp only
        omega)
      have h1' := hcon ((fun i : Fin n => (n : ℤ) - (i : ℕ)) + Pi.single k 1) (fun i j hij => by
        have : ((i : ℕ) : ℤ) + 1 ≤ (j : ℕ) := by exact_mod_cast hij
        simp only [Pi.add_apply, Pi.single_apply]
        split_ifs <;> omega)
      simp only [Pi.add_apply, zpow_add, Finset.prod_mul_distrib, h0', mul_right_inj] at h1'
      have h2 : α k = β k := by simpa [Pi.single_apply, apply_ite, Finset.prod_ite_eq'] using h1'
      exact h2
    have hab : ((∏ i, α i ^ y i : ℂˣ) : ℂ) - ((∏ i, β i ^ y i : ℂˣ) : ℂ) ≠ 0 :=
      sub_ne_zero.2 fun e => hne (Units.ext e)
    refine ⟨(((∏ i, α i ^ y i : ℂˣ) : ℂ) - ((∏ i, β i ^ y i : ℂˣ) : ℂ))⁻¹ • c.mapDomain (· + y) -
      ((((∏ i, α i ^ y i : ℂˣ) : ℂ) - ((∏ i, β i ^ y i : ℂˣ) : ℂ))⁻¹ * ((∏ i, β i ^ y i : ℂˣ) : ℂ)) • c,
      ?_, ?_, ?_⟩
    · intro z hz
      rcases Finset.mem_union.1 (Finsupp.support_sub hz) with h | h
      · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support (Finsupp.support_smul h))
        intro i j hij
        have e1 := hc hu i j hij
        have e2 := hy i j hij
        simp only [Pi.add_apply]
        omega
      · exact hc (Finsupp.support_smul h)
    · rw [evalGL_sub, evalGL_shift, h1, mul_one, mul_one, ← mul_sub, inv_mul_cancel₀ hab]
    · intro γ hγ
      rw [evalGL_sub, evalGL_shift]
      rcases Finset.mem_insert.1 hγ with rfl | h
      · ring
      · simp [h0 γ h]

end PositivityTheory.Rg.BcB.F.F5

end
