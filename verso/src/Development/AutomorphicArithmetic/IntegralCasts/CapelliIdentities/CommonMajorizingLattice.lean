import Mathlib

/- English proof (translation)
Introduce `K _ _ t`. Take `⟨d, hd, h⟩` from `exists_integral_multiples ℤ ℚ t`. Conclude with `⟨d, hd, fun a ha => by simpa [zsmul_eq_mul] using h a ha⟩`.
-/
theorem UpperTheory.Reformulated.B.CommonMajorizingLattice.majLattice_common.{u_1} :
    ∀ {K : Type u_1} [inst : Field K] [NumberField K] (t : Finset K),
    ∃ (d : ℤ), d ≠ (0 : ℤ) ∧ ∀ a ∈ t, IsIntegral ℤ ((↑d : K) * a) := by
  intro K _ _ t
  obtain ⟨d, hd, h⟩ := exists_integral_multiples ℤ ℚ t
  exact ⟨d, hd, fun a ha => by simpa [zsmul_eq_mul] using h a ha⟩
