import Development.AbelianVarietyTheory.Definitions.Divisors.MaxWeightGL1EqOne

namespace GlobalTheory.ConjugateIntersectionMembership

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Simplify to obtain the desired conclusion from the available facts. Simplify using the standard rewrite rules.
-/
theorem mem_inter_conj_iff {H : Type} [Group H] {T L : Subgroup H} {x g : H} :
    g ∈ GlobalTheory.LKLoc.locPart T L x ↔ g ∈ T ∧ x⁻¹ * g * x ∈ L := by
  rw [GlobalTheory.LKLoc.locPart, Subgroup.mem_inf, Subgroup.mem_map]
  refine and_congr_right fun _ => ⟨?_, fun h => ⟨x⁻¹ * g * x, h, ?_⟩⟩
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · simp [MulAut.conj_apply, mul_assoc]

end GlobalTheory.ConjugateIntersectionMembership
