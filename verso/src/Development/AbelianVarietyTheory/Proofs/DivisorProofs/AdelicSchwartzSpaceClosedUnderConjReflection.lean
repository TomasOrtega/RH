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
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem conjNeg_mem_SB {X : Type} [TopologicalSpace X] [AddGroup X] [IsTopologicalAddGroup X] {g : X → ℂ}
    (hg : g ∈ GlobalTheory.WeilM.SB X) : (fun y => starRingEnd ℂ (g (-y))) ∈ GlobalTheory.WeilM.SB X := by
  obtain ⟨hlc, hcs⟩ := hg
  refine ⟨(hlc.comp_continuous continuous_neg).comp (starRingEnd ℂ), ?_⟩
  exact (hcs.comp_homeomorph (Homeomorph.neg X)).comp_left (g := starRingEnd ℂ) (map_zero _)

/- English proof (translation)
Simplify using the standard rewrite rules. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
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
Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Proceed by induction. Treat this case separately. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Treat this case separately.

Apply an available result and prove the equalities needed to match it to the conclusion. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Treat this case separately. Apply an available result and prove the equalities needed to match it to the conclusion.

Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Treat this case separately. Apply an available result and prove the equalities needed to match it to the conclusion. Apply function extensionality and compare values at an arbitrary argument.

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
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem _root_.GlobalTheory.Adopt.adelicSchwartzSpace_closed_under_conj_reflection : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ],
    ∀ φ ∈ GlobalTheory.WeilM.schA F κ, (fun x => starRingEnd ℂ (φ (-x))) ∈ GlobalTheory.WeilM.schA F κ := by
  intro F _ _ κ _ φ hφ
  exact AdelicReflection.GlobalTheory.CompanionTheory.AdelicReflect.schA_conj_neg F κ φ hφ

end
