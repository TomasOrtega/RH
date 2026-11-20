import Mathlib
import Formalism.PeriodIntegrals.Residue
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ResidueLatticeCount.HeckeLower

open NumberField

namespace PI.Residue

/- English proof (translation)
Take `⟨C, hC1, hC⟩` from `hC`. Use `⟨C, hC1, fun E _ _ hm => ?_⟩` and prove the remaining obligations. Establish `hd : 4 / 9 * (3 * Real.pi / 4) ^ Module.finrank ℚ E ≤ ((|discr E| : ℤ) : ℝ)`. Use `NumberField.abs_discr_ge (K := E) (by omega)` as an intermediate fact. Conclude with `this` after adjusting the coercions.

Take `⟨s, hs, hle⟩` from `hC (Module.finrank ℚ E) _ hm hd`. Take `⟨hsum, hz⟩` from `hA1 E s hs`. Use `(hB E s hs hsum).trans (le_trans ?_ hle)` and prove the remaining obligations. Establish `hd0 : (0 : ℝ) ≤ ((|discr E| : ℤ) : ℝ)` using `by exact_mod_cast abs_nonneg _`. Establish `hz0 : 0 ≤ zetaR s` using `tsum_nonneg fun n => by positivity`.

Use `gcongr`. Conclude with `hz.trans (pow_le_pow_left₀ hz0 (hA2 s hs) _)`.
-/
theorem residueBound_of (hA1 : ZetaLePow) (hA2 : ZetaRLe) (hB : HeckeLower) (hC : Optimise) :
    PI.ResidueBound := by
  obtain ⟨C, hC1, hC⟩ := hC
  refine ⟨C, hC1, fun E _ _ hm => ?_⟩
  have hd : 4 / 9 * (3 * Real.pi / 4) ^ Module.finrank ℚ E ≤ ((|discr E| : ℤ) : ℝ) := by
    have := NumberField.abs_discr_ge (K := E) (by omega)
    exact_mod_cast this
  obtain ⟨s, hs, hle⟩ := hC (Module.finrank ℚ E) _ hm hd
  obtain ⟨hsum, hz⟩ := hA1 E s hs
  refine (hB E s hs hsum).trans (le_trans ?_ hle)
  have hd0 : (0 : ℝ) ≤ ((|discr E| : ℤ) : ℝ) := by exact_mod_cast abs_nonneg _
  have hz0 : 0 ≤ zetaR s := tsum_nonneg fun n => by positivity
  gcongr
  exact hz.trans (pow_le_pow_left₀ hz0 (hA2 s hs) _)

end PI.Residue
