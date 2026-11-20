import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.StepFormula
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.CasimirBounds.Expand
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.CasimirBounds.CountCross

open Matrix

namespace PositivityTheory.Rg.Cz

/- English proof (translation)
Introduce `n Q _ _ C _ col b S hT hS f hf`. Rewrite using `[cas_expand']`. Establish `key : (star f ⬝ᵥ ((((n * S.card : ℕ) : ℂ) • (1 : Module.End ℂ (TV n ℂ Q)) + ∑ p ∈ S, ∑ q ∈ S.erase p, pm (Equiv.swap p q) : Module.End ℂ (TV n ℂ Q)) f)).re = ((n * S.card : ℕ) : ℝ) * (star f ⬝ᵥ f).re + ∑ p ∈ S, ∑ q ∈ S.erase p, (star f ⬝ᵥ pm (Equiv.swap p q) f).re`. Simplify using `only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, LinearMap.sum_apply, dotProduct_add, dotProduct_smul, dotProduct_sum, Complex.add_re, Complex.re_sum, smul_eq_mul]`. Simplify using the standard rewrite rules.

Rewrite using `[key]`. Use `cas_count hT hS (fun p q => (star f ⬝ᵥ pm (Equiv.swap p q) f).re) _ ?_ ?_ ?_` and prove the remaining obligations. Introduce `p q`. Simplify using `only [Equiv.swap_comm]`. Introduce `p q hpq hne`.

Simplify using `[hf p q hpq hne]`. Introduce `p _ c hc`. Establish `h1` using `re_swapSum_le' f (S.filter fun q => col q = c) p (by simp only [Finset.mem_filter, not_and]; exact fun _ h => hc h.symm) (by`. Introduce `q hq q' hq' hne`. Simplify using `only [Finset.mem_filter] at hq hq'`.

Conclude with `hf q q' (hq.2.trans hq'.2.symm) hne)`. Simplify `h1` using `only [Complex.re_sum]`.
-/
theorem casBound_holds : CasBound := by
  intro n Q _ _ C _ col b S hT hS f hf
  rw [cas_expand']
  have key : (star f ⬝ᵥ ((((n * S.card : ℕ) : ℂ) • (1 : Module.End ℂ (TV n ℂ Q)) +
      ∑ p ∈ S, ∑ q ∈ S.erase p, pm (Equiv.swap p q) : Module.End ℂ (TV n ℂ Q)) f)).re =
      ((n * S.card : ℕ) : ℝ) * (star f ⬝ᵥ f).re +
        ∑ p ∈ S, ∑ q ∈ S.erase p, (star f ⬝ᵥ pm (Equiv.swap p q) f).re := by
    simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, LinearMap.sum_apply,
      dotProduct_add, dotProduct_smul, dotProduct_sum, Complex.add_re, Complex.re_sum, smul_eq_mul]
    simp
  rw [key]
  refine cas_count hT hS (fun p q => (star f ⬝ᵥ pm (Equiv.swap p q) f).re) _ ?_ ?_ ?_
  · intro p q
    simp only [Equiv.swap_comm]
  · intro p q hpq hne
    simp [hf p q hpq hne]
  · intro p _ c hc
    have h1 := re_swapSum_le' f (S.filter fun q => col q = c) p
      (by simp only [Finset.mem_filter, not_and]; exact fun _ h => hc h.symm)
      (by
        intro q hq q' hq' hne
        simp only [Finset.mem_filter] at hq hq'
        exact hf q q' (hq.2.trans hq'.2.symm) hne)
    simpa only [Complex.re_sum] using h1

end PositivityTheory.Rg.Cz
