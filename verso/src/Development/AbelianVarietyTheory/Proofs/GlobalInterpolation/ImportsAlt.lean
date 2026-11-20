import Mathlib

namespace GlobalTheory.LocalRingBasicFacts

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Simplify using the standard rewrite rules.
-/
theorem main : ∀ {O : Type} [inst : CommRing O] [inst_1 : IsLocalRing O] {a : ℕ}, Ideal.span (Set.range MvPowerSeries.X) ≤ IsLocalRing.maximalIdeal (MvPowerSeries (Fin a) O) := by
  intro O _ _ a
  rw [Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  rw [SetLike.mem_coe, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro h
  have := h.map (MvPowerSeries.constantCoeff (R := O) (σ := Fin a))
  simp at this

end GlobalTheory.LocalRingBasicFacts
