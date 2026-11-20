import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff

namespace AdelicReflection
section

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.AdelicReflect

def conjNeg {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : SchwartzMap E ℂ) : SchwartzMap E ℂ :=
  let g : SchwartzMap E ℂ := SchwartzMap.compCLMOfContinuousLinearEquiv ℝ (ContinuousLinearEquiv.neg ℝ) f
  { toFun := fun y => starRingEnd ℂ (g y)
    smooth' := Complex.conjCLE.contDiff.comp g.smooth'
    decay' := by
      intro k n
      obtain ⟨C, hC⟩ := g.decay' k n
      refine ⟨C, fun x => ?_⟩
      have e : (fun y => starRingEnd ℂ (g y)) = Complex.conjLIE ∘ g := rfl
      rw [e, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left]
      exact hC x }

/- English proof (translation)
Take `⟨hlc, hcs⟩` from `hg`. Use `⟨(hlc.comp_continuous continuous_neg).comp (starRingEnd ℂ), ?_⟩` and prove the remaining obligations. Conclude with `(hcs.comp_homeomorph (Homeomorph.neg X)).comp_left (g := starRingEnd ℂ) (map_zero _)`.
-/
theorem conjNeg_mem_SB {X : Type} [TopologicalSpace X] [AddGroup X] [IsTopologicalAddGroup X] {g : X → ℂ}
    (hg : g ∈ GlobalTheory.WeilM.SB X) : (fun y => starRingEnd ℂ (g (-y))) ∈ GlobalTheory.WeilM.SB X := by
  obtain ⟨hlc, hcs⟩ := hg
  refine ⟨(hlc.comp_continuous continuous_neg).comp (starRingEnd ℂ), ?_⟩
  exact (hcs.comp_homeomorph (Homeomorph.neg X)).comp_left (g := starRingEnd ℂ) (map_zero _)

/- English proof (translation)
Simplify using `only [GlobalTheory.WeilM.pureA, map_mul]`. Use `congr 3`. Use function extensionality and compare the values at `i`. Rewrite using `[Pi.neg_apply, Pi.neg_apply, ← map_neg]`. Both sides reduce to the same expression.
-/
theorem conj_pureA_neg (F : Type) [Field F] [NumberField F] {κ : Type}
    (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (x : κ → AdeleRing (𝓞 F) F) :
    starRingEnd ℂ (GlobalTheory.WeilM.pureA F f g (-x)) =
      GlobalTheory.WeilM.pureA F (fun y => starRingEnd ℂ (f (-y))) (fun y => starRingEnd ℂ (g (-y))) x := by
  simp only [GlobalTheory.WeilM.pureA, map_mul]
  congr 3
  funext i
  rw [Pi.neg_apply, Pi.neg_apply, ← map_neg]
  rfl

/- English proof (translation)
Introduce `F _ _ κ _ φ hφ`. Unfold `GlobalTheory.WeilM.schA at hφ ⊢`. Proceed by induction on `hφ using Submodule.span_induction with`. Consider the case `mem Φ hΦ`. Take `⟨f, g, hg, rfl⟩` from `hΦ`.

Use `Submodule.subset_span ⟨conjNeg f, fun y => starRingEnd ℂ (g (-y)), conjNeg_mem_SB hg, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `x`. Rewrite using `[conj_pureA_neg]`. Use `congr 1`. Consider the case `zero`.

Use `Submodule.zero_mem _ using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `x`. Simplify using the standard rewrite rules. Consider the case `add a b _ _ ha hb`. Use `Submodule.add_mem _ ha hb using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `x`. Simplify using the standard rewrite rules. Consider the case `smul c a _ ha`. Use `Submodule.smul_mem _ (starRingEnd ℂ c) ha using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `x`.

Simplify using the standard rewrite rules.
-/
theorem schA_conj_neg : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ],
    ∀ φ ∈ GlobalTheory.WeilM.schA F κ, (fun x => starRingEnd ℂ (φ (-x))) ∈ GlobalTheory.WeilM.schA F κ := by
  intro F _ _ κ _ φ hφ
  unfold GlobalTheory.WeilM.schA at hφ ⊢
  induction hφ using Submodule.span_induction with
  | mem Φ hΦ =>
    obtain ⟨f, g, hg, rfl⟩ := hΦ
    refine Submodule.subset_span ⟨conjNeg f, fun y => starRingEnd ℂ (g (-y)), conjNeg_mem_SB hg, ?_⟩
    funext x
    rw [conj_pureA_neg]
    congr 1
  | zero =>
    convert Submodule.zero_mem _ using 1
    funext x
    simp
  | add a b _ _ ha hb =>
    convert Submodule.add_mem _ ha hb using 1
    funext x
    simp
  | smul c a _ ha =>
    convert Submodule.smul_mem _ (starRingEnd ℂ c) ha using 1
    funext x
    simp

end GlobalTheory.CompanionTheory.AdelicReflect

end

end

end AdelicReflection
section

open NumberField IsDedekindDomain

/- English proof (translation)
Introduce `F _ _ κ _ φ hφ`. Conclude with `AdelicReflection.GlobalTheory.CompanionTheory.AdelicReflect.schA_conj_neg F κ φ hφ`.
-/
theorem _root_.GlobalTheory.Adopt.adelicSchwartzSpace_closed_under_conj_reflection : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ],
    ∀ φ ∈ GlobalTheory.WeilM.schA F κ, (fun x => starRingEnd ℂ (φ (-x))) ∈ GlobalTheory.WeilM.schA F κ := by
  intro F _ _ κ _ φ hφ
  exact AdelicReflection.GlobalTheory.CompanionTheory.AdelicReflect.schA_conj_neg F κ φ hφ

end
