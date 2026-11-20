import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.PartShortOf

noncomputable section

namespace PIW.AdelClassFin

open NumberField

/- English proof (translation)
Introduce `E _ _`. Use `⟨(NumberField.discr E).natAbs, Int.natAbs_pos.2 (NumberField.discr_ne_zero E), fun y hy => ?_⟩` and prove the remaining obligations. Establish `hmem : y ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 E) E)`. Rewrite using `[Submodule.mem_traceDual]`. Introduce `a ha`.

Take `⟨a', rfl⟩` from `Submodule.mem_one.1 ha`. Rewrite using `[Algebra.traceForm_apply, mul_comm]`. Conclude with `hy a'`. Establish `hint` using `isIntegral_discr_mul_of_mem_traceDual (A := ℤ) (K := ℚ) (1 : Submodule (𝓞 E) E) (b := integralBasis E) (fun i => by rw [integralBasis_apply]; exact RingOfIntegers.isIntegral_coe _) (Submodule.mem_one.2 ⟨1, map_one _⟩) hmem`. Rewrite `hint` using `[← NumberField.coe_discr]`.

Establish `hx : IsIntegral ℤ (((NumberField.discr E : ℤ) : E) * y)`. Use `hint using 1` and compare the differences between its conclusion and the goal. Rewrite using `[Algebra.smul_def, mul_one, map_intCast]`. Take `⟨z, hz⟩` from `(IsIntegralClosure.isIntegral_iff (A := 𝓞 E)).1 hx`. Take `⟨n, hn⟩ : ∃ n : ℕ, n = (NumberField.discr E).natAbs` from `⟨_, rfl⟩`.

Rewrite using `[← hn]`. Break down `Int.natAbs_eq (NumberField.discr E) with h | h` into its components or cases. Rewrite `h` using `[← hn]`. Use `⟨z, ?_⟩` and prove the remaining obligations. Rewrite using `[hz, h, Int.cast_natCast]`.

Rewrite `h` using `[← hn]`. Use `⟨-z, ?_⟩` and prove the remaining obligations. Rewrite using `[map_neg, hz, h, Int.cast_neg, Int.cast_natCast, neg_mul, neg_neg]`.
-/
theorem successive_vector_codifferent : SvCodiff := by
  intro E _ _
  refine ⟨(NumberField.discr E).natAbs, Int.natAbs_pos.2 (NumberField.discr_ne_zero E), fun y hy => ?_⟩
  have hmem : y ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 E) E) := by
    rw [Submodule.mem_traceDual]
    intro a ha
    obtain ⟨a', rfl⟩ := Submodule.mem_one.1 ha
    rw [Algebra.traceForm_apply, mul_comm]
    exact hy a'
  have hint := isIntegral_discr_mul_of_mem_traceDual (A := ℤ) (K := ℚ)
    (1 : Submodule (𝓞 E) E) (b := integralBasis E)
    (fun i => by rw [integralBasis_apply]; exact RingOfIntegers.isIntegral_coe _)
    (Submodule.mem_one.2 ⟨1, map_one _⟩) hmem
  rw [← NumberField.coe_discr] at hint
  have hx : IsIntegral ℤ (((NumberField.discr E : ℤ) : E) * y) := by
    convert hint using 1
    rw [Algebra.smul_def, mul_one, map_intCast]
  obtain ⟨z, hz⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 E)).1 hx
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = (NumberField.discr E).natAbs := ⟨_, rfl⟩
  rw [← hn]
  rcases Int.natAbs_eq (NumberField.discr E) with h | h
  · rw [← hn] at h
    refine ⟨z, ?_⟩
    rw [hz, h, Int.cast_natCast]
  · rw [← hn] at h
    refine ⟨-z, ?_⟩
    rw [map_neg, hz, h, Int.cast_neg, Int.cast_natCast, neg_mul, neg_neg]

end PIW.AdelClassFin

end
