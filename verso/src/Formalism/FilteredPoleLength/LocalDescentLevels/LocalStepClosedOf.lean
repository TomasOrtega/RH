import Formalism.FilteredPoleLength.ReducedBasisBounds.GradedFreeLengthFiltered
import Formalism.FilteredPoleLength.LocalDescentLevels.LevelsChainOfAddOneLe
import Formalism.FilteredPoleLength.LocalDescentLevels.LevelsLengthSum

open Module

namespace Formalism.LatticeBaseChangeAlt

/- English proof (translation)
Introduce `ι _ ep f ν v νs c' T R I hep hT hc' hv hν O K K₁ V W`. Introduce `_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`. Introduce `ϖ hϖ M Θ N₁ Z Zm N' e be n th c AA AA' N₁' ρ a a' hM hΘ h1 h2 h3 h4 h5 h6 ha ha' h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 hcase`. Introduce `Rr Aq _ _ _ _ _ _ _ _ xq nq Fq rq hF0 hFn hFd hFi hFl hsum hres hequiv`. Introduce `A0 _ _ n1 F1 ι1 _ _ deg δ t σ u hG0 hGn hGd hker hsurj hdeg hlead hind hspan hcard hI V'`.

Take `⟨eqv⟩` from `hequiv`. Use `set mmz : ι → ℕ := fun z => (max 0 ⌈(ep z : ℝ) * ((T : ℝ) * ν z - (e : ℝ))⌉).toNat with hmmz`. Establish `hL` using `levelsLengthSum O ι Rr Aq xq mmz nq Fq rq R hF0 hFn hFd hFi hFl hsum`. Establish `hA : Module.length O (↥AA' ⧸ AA.comap AA'.subtype) ≤ ((R * ∑ z, mmz z * f z : ℕ) : ℕ∞)`. Rewrite using `[eqv.length_eq, hL]`.

Use `le_of_eq ?_` and prove the remaining obligations. Simplify using `only [hres]`. Use `push_cast`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun z _ => ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree. Establish `hN : Module.length O (↥AA ⧸ N₁'.comap AA.subtype) ≤ ((R * I : ℕ) : ℕ∞)`. Rewrite using `[hspan, hLT O (↥AA) A0 n1 F1 ι1 deg δ t σ u hG0 hGn hGd hker hsurj hdeg hlead hind, hcard, hI]`. Use `push_cast`. Conclude with `le_rfl`.

Conclude with `localLevelsExt ι ep f ν v νs c' T R I hep hT hc' hv hν O K K₁ V W ϖ hϖ M Θ N₁ Z Zm N' e be n th c AA AA' N₁' ρ a a' hM hΘ h1 h2 h3 h4 h5 h6 ha ha' h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 hcase hA hN V'`.
-/
theorem localStepClosed_of (hLT : LeadingTermLength) : LocalStepClosed := by
  intro ι _ ep f ν v νs c' T R I hep hT hc' hv hν O K K₁ V W
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  intro ϖ hϖ M Θ N₁ Z Zm N' e be n th c AA AA' N₁' ρ a a' hM hΘ h1 h2 h3 h4 h5 h6 ha ha' h7 h8 h9
    h10 h11 h12 h13 h14 h15 h16 h17 hcase
  intro Rr Aq _ _ _ _ _ _ _ _ xq nq Fq rq hF0 hFn hFd hFi hFl hsum hres hequiv
  intro A0 _ _ n1 F1 ι1 _ _ deg δ t σ u hG0 hGn hGd hker hsurj hdeg hlead hind hspan hcard hI V'
  obtain ⟨eqv⟩ := hequiv
  set mmz : ι → ℕ := fun z => (max 0 ⌈(ep z : ℝ) * ((T : ℝ) * ν z - (e : ℝ))⌉).toNat with hmmz
  have hL := levelsLengthSum O ι Rr Aq xq mmz nq Fq rq R hF0 hFn hFd hFi hFl hsum
  have hA : Module.length O (↥AA' ⧸ AA.comap AA'.subtype) ≤
      ((R * ∑ z, mmz z * f z : ℕ) : ℕ∞) := by
    rw [eqv.length_eq, hL]
    refine le_of_eq ?_
    simp only [hres]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    ring
  have hN : Module.length O (↥AA ⧸ N₁'.comap AA.subtype) ≤ ((R * I : ℕ) : ℕ∞) := by
    rw [hspan, hLT O (↥AA) A0 n1 F1 ι1 deg δ t σ u hG0 hGn hGd hker hsurj hdeg hlead hind, hcard, hI]
    push_cast
    exact le_rfl
  exact localLevelsExt ι ep f ν v νs c' T R I hep hT hc' hv hν O K K₁ V W ϖ hϖ M Θ N₁ Z Zm N' e be
    n th c AA AA' N₁' ρ a a' hM hΘ h1 h2 h3 h4 h5 h6 ha ha' h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
    hcase hA hN V'

end Formalism.LatticeBaseChangeAlt
