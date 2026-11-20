import Mathlib

/- English proof (translation)
Introduce `l _ x hx`. Establish `hint : IsIntegral ℚ_[l] x` using `(Algebra.IsAlgebraic.isAlgebraic x).isIntegral`. Establish `hm : (minpoly ℚ_[l] x).Monic` using `minpoly.monic hint`. Establish `hs : spectralValue (minpoly ℚ_[l] x) ≤ 1` using `hx`. Establish `hc : ∀ n : ℕ, ‖(minpoly ℚ_[l] x).coeff n‖ ≤ 1` using `(spectralValue_le_one_iff hm).1 hs`.

Establish `hl : minpoly ℚ_[l] x ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l])`. Rewrite using `[Polynomial.lifts_iff_coeff_lifts]`. Introduce `n`. Conclude with `⟨⟨_, hc n⟩, rfl⟩`. Take `⟨q, hq, -, hqm⟩` from `Polynomial.lifts_and_natDegree_eq_and_monic hl hm`.

Use `⟨q, hqm, ?_⟩` and prove the remaining obligations. Rewrite using `[← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap ℚ_[l], hq]`. Conclude with `minpoly.aeval _ _`.
-/
theorem UpperTheory.padicAlgCl_isIntegral_of_norm_le_one :
    ∀ {l : ℕ} [Fact l.Prime] (x : PadicAlgCl l), ‖x‖ ≤ 1 → IsIntegral ℤ_[l] x := by
  intro l _ x hx
  have hint : IsIntegral ℚ_[l] x := (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  have hm : (minpoly ℚ_[l] x).Monic := minpoly.monic hint
  have hs : spectralValue (minpoly ℚ_[l] x) ≤ 1 := hx
  have hc : ∀ n : ℕ, ‖(minpoly ℚ_[l] x).coeff n‖ ≤ 1 := (spectralValue_le_one_iff hm).1 hs
  have hl : minpoly ℚ_[l] x ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l]) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    exact ⟨⟨_, hc n⟩, rfl⟩
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl hm
  refine ⟨q, hqm, ?_⟩
  rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap ℚ_[l], hq]
  exact minpoly.aeval _ _
