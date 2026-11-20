import Mathlib

namespace GlobalTheory.LocalRingBasicFacts

/- English proof (translation)
Introduce `O _ _ a`. Rewrite using `[Ideal.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Rewrite using `[SetLike.mem_coe, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`. Introduce `h`.

Use `h.map (MvPowerSeries.constantCoeff (R := O) (σ := Fin a))` as an intermediate fact. Simplify using `at this`.
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
