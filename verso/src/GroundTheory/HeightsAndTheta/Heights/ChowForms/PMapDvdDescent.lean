import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowForms.StatementsNormForm
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

/- English proof (translation)
Introduce `K Ω _ _ _ σ f g ⟨G, hG⟩`. Take `⟨π, hπ⟩` from `LinearMap.exists_leftInverse_of_injective (Algebra.linearMap K Ω) (LinearMap.ker_eq_bot.mpr (algebraMap K Ω).injective)`. Establish `hπa : ∀ a : K, π (algebraMap K Ω a) = a` using `fun a => by`. Simplify using `using LinearMap.congr_fun hπ a`. Establish `hπm : ∀ (a : K) (y : Ω), π (algebraMap K Ω a * y) = a * π y` using `fun a y => by`.

Rewrite using `[← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]`. Set `Φ : MvPolynomial σ K` to `∑ s ∈ G.support, monomial s (π (coeff s G))`. Establish `hΦ : ∀ s, coeff s Φ = π (coeff s G)` using `fun s => by`. Simplify using `only [Φ, coeff_sum, coeff_monomial]`. Rewrite using `[Finset.sum_ite_eq']`.

Use `split_ifs with h`. Both sides reduce to the same expression. Rewrite using `[notMem_support_iff.mp h, map_zero]`. Use `⟨Φ, ?_⟩` and prove the remaining obligations. Use extensionality with `s`.

Establish `h1` using `congrArg (fun P => π (coeff s P)) hG`. Simplify using `only [coeff_map, hπa, coeff_mul, map_sum, hπm] at h1`. Rewrite using `[h1, coeff_mul]`. Conclude with `Finset.sum_congr rfl fun x _ => by rw [hΦ]`.
-/
theorem MapDvdDescent.proof : MapDvdDescent.Statement := by
  classical
  intro K Ω _ _ _ σ f g ⟨G, hG⟩
  obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap K Ω)
    (LinearMap.ker_eq_bot.mpr (algebraMap K Ω).injective)
  have hπa : ∀ a : K, π (algebraMap K Ω a) = a := fun a => by
    simpa using LinearMap.congr_fun hπ a
  have hπm : ∀ (a : K) (y : Ω), π (algebraMap K Ω a * y) = a * π y := fun a y => by
    rw [← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]

  let Φ : MvPolynomial σ K := ∑ s ∈ G.support, monomial s (π (coeff s G))
  have hΦ : ∀ s, coeff s Φ = π (coeff s G) := fun s => by
    simp only [Φ, coeff_sum, coeff_monomial]
    rw [Finset.sum_ite_eq']
    split_ifs with h
    · rfl
    · rw [notMem_support_iff.mp h, map_zero]
  refine ⟨Φ, ?_⟩
  ext s
  have h1 := congrArg (fun P => π (coeff s P)) hG
  simp only [coeff_map, hπa, coeff_mul, map_sum, hπm] at h1
  rw [h1, coeff_mul]
  exact Finset.sum_congr rfl fun x _ => by rw [hΦ]

end GroundTheory.Heights₂.Heights
