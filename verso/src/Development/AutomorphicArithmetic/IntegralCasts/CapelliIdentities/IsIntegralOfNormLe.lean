import Mathlib

namespace UpperTheory.Reformulated.B.S4

/- English proof (translation)
Establish `hi : IsIntegral ℚ_[l] z` using `Algebra.IsIntegral.isIntegral z`. Establish `hm : (minpoly ℚ_[l] z).Monic` using `minpoly.monic hi`. Establish `hv : spectralValue (minpoly ℚ_[l] z) ≤ 1` using `hz`. Establish `hc : ∀ n, ‖(minpoly ℚ_[l] z).coeff n‖ ≤ 1` using `(spectralValue_le_one_iff hm).1 hv`. Establish `hl : minpoly ℚ_[l] z ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l])`.

Rewrite using `[Polynomial.lifts_iff_coeff_lifts]`. Introduce `n`. Conclude with `⟨⟨_, hc n⟩, rfl⟩`. Take `⟨q, hq, -, hqm⟩` from `Polynomial.lifts_and_natDegree_eq_and_monic hl hm`. Use `⟨q, hqm, ?_⟩` and prove the remaining obligations.

Establish `h0 : Polynomial.aeval z (q.map (algebraMap ℤ_[l] ℚ_[l])) = 0`. Rewrite using `[hq]`. Conclude with `minpoly.aeval _ _`. Rewrite `h0` using `[Polynomial.aeval_map_algebraMap]`. Conclude with `h0`.
-/
theorem isIntegral_of_norm_le {l : ℕ} [Fact l.Prime] {z : PadicAlgCl l} (hz : ‖z‖ ≤ 1) : IsIntegral ℤ_[l] z := by
  have hi : IsIntegral ℚ_[l] z := Algebra.IsIntegral.isIntegral z
  have hm : (minpoly ℚ_[l] z).Monic := minpoly.monic hi
  have hv : spectralValue (minpoly ℚ_[l] z) ≤ 1 := hz
  have hc : ∀ n, ‖(minpoly ℚ_[l] z).coeff n‖ ≤ 1 := (spectralValue_le_one_iff hm).1 hv
  have hl : minpoly ℚ_[l] z ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l]) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    exact ⟨⟨_, hc n⟩, rfl⟩
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl hm
  refine ⟨q, hqm, ?_⟩
  have h0 : Polynomial.aeval z (q.map (algebraMap ℤ_[l] ℚ_[l])) = 0 := by
    rw [hq]
    exact minpoly.aeval _ _
  rw [Polynomial.aeval_map_algebraMap] at h0
  exact h0

end UpperTheory.Reformulated.B.S4
