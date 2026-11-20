import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexOfGammaLe
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

namespace GlobalTheory

/- English proof (translation)
Introduce `d hd hev`. Take `⟨k, rfl⟩` from `Int.eq_ofNat_of_zero_le (by omega : (0 : ℤ) ≤ d)`. Establish `hk : 3 ≤ k` using `by omega`. Establish `hk2 : Even k` using `by simpa [Int.even_coe_nat] using hev`. Set `f : ModularForm 𝒮ℒ (k : ℤ)` to `ModularForm.E hk`.

Use `⟨f, isMF_coe_top f, ?_⟩` and prove the remaining obligations. Establish `h0 : valueAtInfty (f : ℍ → ℂ) = 1`. Rewrite using `[← qExpansion_coeff_zero one_pos (ModularFormClass.analyticAt_cuspFunction_zero f one_pos one_mem_strictPeriods_SL) (SlashInvariantFormClass.periodic_comp_ofComplex f one_mem_strictPeriods_SL)]`. Conclude with `EisensteinSeries.E_qExpansion_coeff_zero hk hk2`. Establish `h` using `exp_decay_sub_atImInfty one_pos (SlashInvariantFormClass.periodic_comp_ofComplex f one_mem_strictPeriods_SL) (ModularFormClass.holo f) (ModularFormClass.bdd_at_infty f)`.

Rewrite `h` using `[h0]`. Simplify using `using h`.
-/
theorem levelOne_form_one_add_expDecay :
    ∀ d : ℤ, 4 ≤ d → Even d → ∃ e : ℍ → ℂ, IsMF ⊤ d e ∧
      (fun τ : ℍ => e τ - 1) =O[atImInfty] fun τ : ℍ => Real.exp (-2 * Real.pi * τ.im) := by
  intro d hd hev
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : (0 : ℤ) ≤ d)
  have hk : 3 ≤ k := by omega
  have hk2 : Even k := by simpa [Int.even_coe_nat] using hev
  let f : ModularForm 𝒮ℒ (k : ℤ) := ModularForm.E hk
  refine ⟨f, isMF_coe_top f, ?_⟩
  have h0 : valueAtInfty (f : ℍ → ℂ) = 1 := by
    rw [← qExpansion_coeff_zero one_pos
      (ModularFormClass.analyticAt_cuspFunction_zero f one_pos one_mem_strictPeriods_SL)
      (SlashInvariantFormClass.periodic_comp_ofComplex f one_mem_strictPeriods_SL)]
    exact EisensteinSeries.E_qExpansion_coeff_zero hk hk2
  have h := exp_decay_sub_atImInfty one_pos
    (SlashInvariantFormClass.periodic_comp_ofComplex f one_mem_strictPeriods_SL)
    (ModularFormClass.holo f) (ModularFormClass.bdd_at_infty f)
  rw [h0] at h
  simpa using h

end GlobalTheory
