import Development.EtaleCohomology.EtaleSheaves.StrictLocalStalks

namespace LateralTheory.E.ULAStalkPf

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Assume the hypotheses and unpack their components. Rewrite the indicated hypotheses using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules.

Take a linear combination of the given relations to obtain the conclusion. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem fracOf : FracOf := by
  intro B C _ _ _ j hj hfr
  let _ := ((algebraMap C (FractionRing C)).comp j).toAlgebra
  have hf : ∀ x : B, algebraMap B (FractionRing C) x = algebraMap C (FractionRing C) (j x) := fun _ => rfl
  have hne : ∀ s : B, s ≠ 0 → j s ≠ 0 := fun s hs h0 => hs (hj (by rw [h0, map_zero]))
  have hB : IsDomain B := Function.Injective.isDomain j hj
  refine ⟨fun s => ?_, fun z => ?_, fun {x y} hxy => ?_⟩
  · rw [hf]
    refine IsUnit.mk0 _ ?_
    exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero (hne _ (nonZeroDivisors.ne_zero s.2)))
  · obtain ⟨⟨a, t⟩, ha⟩ := IsLocalization.surj (nonZeroDivisors C) z
    obtain ⟨s1, y1, hs1, e1⟩ := hfr a
    obtain ⟨s2, y2, hs2, e2⟩ := hfr t
    have ht : (t : C) ≠ 0 := nonZeroDivisors.ne_zero t.2
    have hy2 : y2 ≠ 0 := by
      rintro rfl
      rw [map_zero] at e2
      exact mul_ne_zero (hne _ hs2) ht e2
    refine ⟨⟨y1 * s2, ⟨s1 * y2, mem_nonZeroDivisors_of_ne_zero (mul_ne_zero hs1 hy2)⟩⟩, ?_⟩
    simp only [hf, map_mul] at ha ⊢
    have e1' := congrArg (algebraMap C (FractionRing C)) e1
    have e2' := congrArg (algebraMap C (FractionRing C)) e2
    simp only [map_mul] at e1' e2'
    linear_combination (-(z * algebraMap C (FractionRing C) (j s1))) * e2' +
      (algebraMap C (FractionRing C) (j s1) * algebraMap C (FractionRing C) (j s2)) * ha +
      algebraMap C (FractionRing C) (j s2) * e1'
  · refine ⟨1, ?_⟩
    simp only [OneMemClass.coe_one, one_mul]
    exact hj (IsFractionRing.injective C (FractionRing C) hxy)

end LateralTheory.E.ULAStalkPf
