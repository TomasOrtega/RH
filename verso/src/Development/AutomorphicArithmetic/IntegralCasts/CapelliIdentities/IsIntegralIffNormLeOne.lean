import Mathlib

open Polynomial

/- English proof (translation)
Introduce `l _ x`. Establish `hx : IsIntegral ℚ_[l] x` using `Algebra.IsIntegral.isIntegral x`. Establish `hm : (minpoly ℚ_[l] x).Monic` using `minpoly.monic hx`. Establish `key : ‖x‖ ≤ (1 : ℝ) ↔ ∀ n, ‖(minpoly ℚ_[l] x).coeff n‖ ≤ 1` using `spectralValue_le_one_iff hm`. Rewrite using `[key]`.

Prove the components needed by the constructor for the conclusion. Introduce `h n`. Rewrite using `[minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, coeff_map]`. Conclude with `((minpoly ℤ_[l] x).coeff n).2`. Introduce `h`.

Establish `hl : minpoly ℚ_[l] x ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l])`. Rewrite using `[lifts_iff_coeff_lifts]`. Introduce `n`. Conclude with `⟨⟨_, h n⟩, rfl⟩`. Take `⟨q, hq, -, hqm⟩` from `lifts_and_degree_eq_and_monic hl hm`.

Use `⟨q, hqm, ?_⟩` and prove the remaining obligations. Rewrite using `[← aeval_def, ← aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]`.
-/
theorem UpperTheory.padicAlgCl_isIntegral_iff_norm_le_one :
    ∀ {l : ℕ} [Fact (Nat.Prime l)] (x : PadicAlgCl l), IsIntegral ℤ_[l] x ↔ ‖x‖ ≤ (1 : ℝ) := by
  intro l _ x
  have hx : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  have hm : (minpoly ℚ_[l] x).Monic := minpoly.monic hx
  have key : ‖x‖ ≤ (1 : ℝ) ↔ ∀ n, ‖(minpoly ℚ_[l] x).coeff n‖ ≤ 1 :=
    spectralValue_le_one_iff hm
  rw [key]
  constructor
  · intro h n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, coeff_map]
    exact ((minpoly ℤ_[l] x).coeff n).2
  · intro h
    have hl : minpoly ℚ_[l] x ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l]) := by
      rw [lifts_iff_coeff_lifts]
      intro n
      exact ⟨⟨_, h n⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := lifts_and_degree_eq_and_monic hl hm
    refine ⟨q, hqm, ?_⟩
    rw [← aeval_def, ← aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]
