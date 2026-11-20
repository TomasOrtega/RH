import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LSatLemmas

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

/- English proof (translation)
Introduce `R _ _ r n ν c f hc hcf`. Rewrite `hcf`, the goal using `[lsat_mem_dualWeyl]`. Take `⟨hwh, hcol⟩` from `hcf`. Use `⟨fun {d} hd => hwh ?_, fun l j hlj => ?_⟩` and prove the remaining obligations. Rewrite using `[coeff_smul, smul_eq_mul]`.

Conclude with `mul_ne_zero hc hd`. Establish `h` using `hcol l j hlj`. Rewrite `h` using `[smul_eq_C_mul, map_mul, map_mul, algHom_C, algHom_C]`. Conclude with `mul_left_cancel₀ (by simpa using hc) h`.
-/
theorem dualWeylModuleSaturated : DualWeylSat := by
  intro R _ _ r n ν c f hc hcf
  rw [lsat_mem_dualWeyl] at hcf ⊢
  obtain ⟨hwh, hcol⟩ := hcf
  refine ⟨fun {d} hd => hwh ?_, fun l j hlj => ?_⟩
  · rw [coeff_smul, smul_eq_mul]
    exact mul_ne_zero hc hd
  · have h := hcol l j hlj
    rw [smul_eq_C_mul, map_mul, map_mul, algHom_C, algHom_C] at h
    exact mul_left_cancel₀ (by simpa using hc) h

end Formalism.GradedWeylDivisibility
