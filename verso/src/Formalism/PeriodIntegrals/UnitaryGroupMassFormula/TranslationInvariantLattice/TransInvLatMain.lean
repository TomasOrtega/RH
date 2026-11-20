import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TranslationInvariantLattice.TransInvLatOfPhase
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AreaLat

open Classical Complex

namespace PI.TransInvLatW

/- English proof (translation)
Introduce `w₁ w₂ hD x ω m _hm hx hω`. Take `⟨hA, hint⟩` from `area_lattice_formula w₁ w₂ hD`. Take `⟨n, hn⟩` from `hint _ hx ω hω`. Use `set D := ((starRingEnd ℂ) w₁ * w₂).im with hDdef`. Use `set a := (m : ℂ) * (x / 2) with ha`.

Establish `hca : (m : ℂ) * ((starRingEnd ℂ) x / 2) = (starRingEnd ℂ) a`. Rewrite using `[ha, map_mul, map_div₀, Complex.conj_natCast, Complex.conj_ofNat]`. Establish `hkey : x * (starRingEnd ℂ) (2 * (m : ℂ) * ω) - 2 * (m : ℂ) * ω * (starRingEnd ℂ) x = 4 * (a * (starRingEnd ℂ) ω - ω * (starRingEnd ℂ) a)`. Rewrite using `[map_mul, map_mul, Complex.conj_natCast, Complex.conj_ofNat]`. Take the linear combination `(-4 * (starRingEnd ℂ) ω) * ha - (4 * ω) * hca`.

Establish `him : a * (starRingEnd ℂ) ω - ω * (starRingEnd ℂ) a = -2 * (((starRingEnd ℂ) a * ω).im : ℂ) * I`. Apply the tactic sequence `apply Complex.ext <;> simp <;> ring`. Rewrite using `[hkey, him, hn, hA]`. Establish `hD' : (D : ℂ) ≠ 0` using `by exact_mod_cast hD`. Break down `abs_cases D with ⟨h, _⟩ | ⟨h, _⟩` into its components or cases.

Rewrite using `[h]`. Establish `: (Real.pi : ℂ) * (4 * (-2 * (((n : ℝ) * D : ℝ) : ℂ) * I)) / (2 * (D : ℂ)) = ((-2 * n : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * I)` using `by push_cast; field_simp; ring`. Rewrite using `[this, Complex.exp_int_mul_two_pi_mul_I]`. Rewrite using `[h]`. Establish `hD'' : ((-D : ℝ) : ℂ) ≠ 0` using `by push_cast; exact neg_ne_zero.mpr hD'`.

Establish `: (Real.pi : ℂ) * (4 * (-2 * (((n : ℝ) * D : ℝ) : ℂ) * I)) / (2 * ((-D : ℝ) : ℂ)) = ((2 * n : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * I)`. Move the coercions through the operations in `at hD'' ⊢`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, Complex.exp_int_mul_two_pi_mul_I]`.
-/
theorem phaseOne : PhaseOne := by
  intro w₁ w₂ hD x ω m _hm hx hω
  obtain ⟨hA, hint⟩ := area_lattice_formula w₁ w₂ hD
  obtain ⟨n, hn⟩ := hint _ hx ω hω
  set D := ((starRingEnd ℂ) w₁ * w₂).im with hDdef
  set a := (m : ℂ) * (x / 2) with ha
  have hca : (m : ℂ) * ((starRingEnd ℂ) x / 2) = (starRingEnd ℂ) a := by
    rw [ha, map_mul, map_div₀, Complex.conj_natCast, Complex.conj_ofNat]
  have hkey : x * (starRingEnd ℂ) (2 * (m : ℂ) * ω) - 2 * (m : ℂ) * ω * (starRingEnd ℂ) x =
      4 * (a * (starRingEnd ℂ) ω - ω * (starRingEnd ℂ) a) := by
    rw [map_mul, map_mul, Complex.conj_natCast, Complex.conj_ofNat]
    linear_combination (-4 * (starRingEnd ℂ) ω) * ha - (4 * ω) * hca
  have him : a * (starRingEnd ℂ) ω - ω * (starRingEnd ℂ) a =
      -2 * (((starRingEnd ℂ) a * ω).im : ℂ) * I := by
    apply Complex.ext <;> simp <;> ring
  rw [hkey, him, hn, hA]
  have hD' : (D : ℂ) ≠ 0 := by exact_mod_cast hD
  rcases abs_cases D with ⟨h, _⟩ | ⟨h, _⟩
  · rw [h]
    have : (Real.pi : ℂ) * (4 * (-2 * (((n : ℝ) * D : ℝ) : ℂ) * I)) / (2 * (D : ℂ)) =
        ((-2 * n : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * I) := by
      push_cast; field_simp; ring
    rw [this, Complex.exp_int_mul_two_pi_mul_I]
  · rw [h]
    have hD'' : ((-D : ℝ) : ℂ) ≠ 0 := by push_cast; exact neg_ne_zero.mpr hD'
    have : (Real.pi : ℂ) * (4 * (-2 * (((n : ℝ) * D : ℝ) : ℂ) * I)) / (2 * ((-D : ℝ) : ℂ)) =
        ((2 * n : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * I) := by
      push_cast at hD'' ⊢; field_simp; ring
    rw [this, Complex.exp_int_mul_two_pi_mul_I]

/- English proof (translation)
The claim follows from `transInvLat_of_phase phaseOne`.
-/
theorem transInvLat_main : PI.TransInvLat := transInvLat_of_phase phaseOne

end PI.TransInvLatW
