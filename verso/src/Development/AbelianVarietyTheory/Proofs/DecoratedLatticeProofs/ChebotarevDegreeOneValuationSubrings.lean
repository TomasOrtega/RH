import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModChebOm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevDegreeOne

noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory

/- English proof (translation)
Introduce `E Ω _ _ _ _ _ S hS H hn ho _ σ`. Take `⟨v, hv, hd, -, B, hB, -, φ, hφ, hφσ⟩` from `GlobalTheory.Published.cheb_holds E Ω H ho hn σ hS.toFinset`. Use `⟨B, v, φ, ?_, by simpa using hv, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x`. Rewrite using `[ValuationSubring.mem_nonunits_iff]`.

Conclude with `hB x`. Use `((GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified E).1 v).2 hd` as an intermediate fact. Rewrite `this` using `[Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Then use the resulting hypothesis. Use `⟨hφ.1, fun x hx => ?_⟩` and prove the remaining obligations. Rewrite using `[ValuationSubring.mem_nonunits_iff]`.

Conclude with `hφ.2 x ((B.valuation_le_one_iff x).2 hx)`. Use `hn.conj_mem _ hφσ σ⁻¹` as an intermediate fact. Simplify `this` using `[mul_assoc]`.
-/
theorem chebOmSt_holds : ReciprocityTheory.ChartRestriction.L1.ChebOmSt := by
  intro E Ω _ _ _ _ _ S hS H hn ho _ σ
  obtain ⟨v, hv, hd, -, B, hB, -, φ, hφ, hφσ⟩ := GlobalTheory.Published.cheb_holds E Ω H ho hn σ hS.toFinset
  refine ⟨B, v, φ, ?_, by simpa using hv, ?_, ?_, ?_⟩
  · intro x
    rw [ValuationSubring.mem_nonunits_iff]
    exact hB x
  · have := ((GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified E).1 v).2 hd
    rwa [Ideal.absNorm_apply, Submodule.cardQuot_apply] at this
  · refine ⟨hφ.1, fun x hx => ?_⟩
    rw [ValuationSubring.mem_nonunits_iff]
    exact hφ.2 x ((B.valuation_le_one_iff x).2 hx)
  · have := hn.conj_mem _ hφσ σ⁻¹
    simpa [mul_assoc] using this

end GlobalTheory
