import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff

open Matrix NumberField IsDedekindDomain GlobalTheory.WeilM
open scoped ComplexConjugate

namespace GlobalTheory.CompanionTheory.ThetaReal

/- English proof (translation)
Use `⟨?_, fun h => ?_⟩` and prove the remaining obligations. Unfold `thetaSum`. Rewrite using `[← RCLike.star_def, tsum_star]`. Both sides reduce to the same expression. Proceed by induction on `h using Submodule.span_induction with`.

Consider the case `mem x hx`. Take `⟨f, g, hg, rfl⟩` from `hx`. Use `Submodule.subset_span ⟨SchwartzMap.postcompCLM (𝕜 := ℝ) (Complex.conjCLE : ℂ →L[ℝ] ℂ) f, star g, ⟨hg.1.comp star, hg.2.comp_left (g := star) (star_zero ℂ)⟩, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `x`. Simplify using `[pureA]`.

Consider the case `zero => rw [star_zero]`. Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => rw [star_add]`. Conclude with `add_mem hx hy`. Consider the case `smul a x _ hx => rw [star_smul]`.

Conclude with `Submodule.smul_mem _ _ hx`.
-/
theorem thetaSum_star_and_schA_star (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ) :
    thetaSum F (star Φ) = conj (thetaSum F Φ) ∧ (Φ ∈ schA F κ → star Φ ∈ schA F κ) := by
  refine ⟨?_, fun h => ?_⟩
  · unfold thetaSum
    rw [← RCLike.star_def, tsum_star]
    rfl
  · classical
    induction h using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, g, hg, rfl⟩ := hx
      refine Submodule.subset_span ⟨SchwartzMap.postcompCLM (𝕜 := ℝ) (Complex.conjCLE : ℂ →L[ℝ] ℂ) f, star g,
        ⟨hg.1.comp star, hg.2.comp_left (g := star) (star_zero ℂ)⟩, ?_⟩
      funext x
      simp [pureA]
    | zero => rw [star_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [star_add]; exact add_mem hx hy
    | smul a x _ hx => rw [star_smul]; exact Submodule.smul_mem _ _ hx

end GlobalTheory.CompanionTheory.ThetaReal
