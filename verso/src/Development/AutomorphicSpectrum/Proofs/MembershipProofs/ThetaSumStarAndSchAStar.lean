import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff

open Matrix NumberField IsDedekindDomain GlobalTheory.WeilM
open scoped ComplexConjugate

namespace GlobalTheory.CompanionTheory.ThetaReal

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Proceed by induction.

Treat this case separately. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.

Treat this case separately. Treat this case separately. Treat this case separately. A detailed English derivation is pending.
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
