import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerFlagSplitting.SubFlag

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2

noncomputable section

namespace PI.StabSplit

/- English proof (translation)
Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Simplify using the standard rewrite rules. Reduce the equality to equality of the corresponding arguments. A detailed English derivation is pending.
-/
private lemma mem_flagSpan_of_eq_zero_of_le {k r : ℕ} (z : Fin (2 * r + k + 1) → ℂ) (a : Fin (r + 1))
    (w : Fin (2 * r + k + 1) → ℂ) (hw : ∀ i : Fin (2 * r + k + 1), a.val ≤ i.val → w i = 0) :
    w ∈ flagSpan k r z a := by
  have hw' : w = ∑ i : Fin (2 * r + k + 1), w i • bvec i := by
    ext j
    simp [bvec, Pi.single_apply, Finset.sum_apply]
  rw [hw']
  refine Submodule.sum_mem _ (fun i _ => ?_)
  by_cases hi : a.val ≤ i.val
  · simp [hw i hi]
  · push_neg at hi
    have hr : i.val < r := by omega
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨⟨i.val, by omega⟩, Fin.lt_def.mpr hi⟩, ?_⟩)
    have hr' : (⟨i.val, by omega⟩ : Fin (r + 1)).val < r := hr
    simp only [fvec, dif_pos hr']
    congr 1

/- English proof (translation)
Replace the relevant objects with their definitions. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private lemma mulVec_mem_flagSpan_of_fixes_fvec {k r : ℕ} (z : Fin (2 * r + k + 1) → ℂ) (a : Fin (r + 1))
    (h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hf : ∀ b, h *ᵥ fvec k r z b = fvec k r z b) (w : Fin (2 * r + k + 1) → ℂ)
    (hw : w ∈ flagSpan k r z a) : h *ᵥ w ∈ flagSpan k r z a := by
  unfold flagSpan at *
  have hle : Submodule.span ℂ (Set.range fun b : {b : Fin (r + 1) // b < a} => fvec k r z b.1) ≤
      (Submodule.span ℂ (Set.range fun b : {b : Fin (r + 1) // b < a} => fvec k r z b.1)).comap
        (Matrix.mulVecLin h) := by
    rw [Submodule.span_le]
    rintro _ ⟨b, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap, Matrix.mulVecLin_apply]
    rw [hf]
    exact Submodule.subset_span ⟨b, rfl⟩
  exact hle hw

/- English proof (translation)
Replace the relevant objects with their definitions. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation. Simplify using the standard rewrite rules. Establish an intermediate fact.

Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Simplify using the standard rewrite rules.

Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules.

Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails.

Simplify using the standard rewrite rules. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem stabilizer_subgroup_flag : SubFlag := by
  unfold SubFlag
  intro k r z hz s hs
  obtain ⟨h, hh, m, hm, rfl⟩ := hs
  obtain ⟨hhU, hhe, hhz⟩ := hh
  obtain ⟨hmU, hmc, hmd⟩ := hm
  have hhU' : hᴴ * Hpk k r * h = Hpk k r := hhU
  have hmU' : mᴴ * Hpk k r * m = Hpk k r := hmU
  have hfix : ∀ b, h *ᵥ fvec k r z b = fvec k r z b := by
    intro b
    unfold fvec
    split_ifs with hb
    · exact (hhe ⟨b.val, hb⟩).1
    · exact hhz
  refine ⟨?_, fun a => ?_⟩
  · show (h * m)ᴴ * Hpk k r * (h * m) = Hpk k r
    rw [Matrix.conjTranspose_mul]
    calc mᴴ * hᴴ * Hpk k r * (h * m) = mᴴ * (hᴴ * Hpk k r * h) * m := by
          simp only [Matrix.mul_assoc]
      _ = Hpk k r := by rw [hhU']; exact hmU'
  · have hm1 : m *ᵥ fvec k r z a - fvec k r z a ∈ flagSpan k r z a := by
      apply mem_flagSpan_of_eq_zero_of_le
      intro i hi
      rw [Pi.sub_apply, sub_eq_zero]
      unfold fvec
      split_ifs with ha
      · simp only [Matrix.mulVec, dotProduct, bvec, Pi.single_apply, mul_ite, mul_one, mul_zero,
          Finset.sum_ite_eq', Finset.mem_univ, if_true]
        exact hmc ⟨a.val, ha⟩ i hi
      · have hri : r ≤ i.val := by omega
        simp only [Matrix.mulVec, dotProduct]
        rw [Finset.sum_eq_single i]
        · by_cases hzi : z i = 0
          · simp [hzi]
          · have hik : i.val ≤ r + k := by
              by_contra hc
              exact hzi (hz i (Or.inr (by omega)))
            rw [hmd i i hri hik hri, if_pos rfl, one_mul]
        · intro j _ hji
          by_cases hzj : z j = 0
          · simp [hzj]
          · have h1 : r ≤ j.val := by
              by_contra hc
              exact hzj (hz j (Or.inl (by omega)))
            have h2 : j.val ≤ r + k := by
              by_contra hc
              exact hzj (hz j (Or.inr (by omega)))
            rw [hmd i j h1 h2 hri, if_neg (Ne.symm hji), zero_mul]
        · intro hi'
          exact absurd (Finset.mem_univ i) hi'
    have heq : (h * m) *ᵥ fvec k r z a - fvec k r z a =
        h *ᵥ (m *ᵥ fvec k r z a - fvec k r z a) := by
      rw [← Matrix.mulVec_mulVec, Matrix.mulVec_sub, hfix]
    rw [heq]
    exact mulVec_mem_flagSpan_of_fixes_fvec z a h hfix _ hm1

end PI.StabSplit
