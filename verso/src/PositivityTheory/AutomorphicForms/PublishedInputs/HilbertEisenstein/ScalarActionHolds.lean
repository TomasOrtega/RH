import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.SSmooth

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published

namespace UpperTheory.HilbertEisensteinWeightOne

/- English proof (translation)
Introduce `_ _ _ F _ _ _ ω c k φ a ha`. Establish `e2 : ∀ g, (a • φ).1 g = a * φ.1 g` using `fun _ => rfl`. Use `⟨fun h => ?_, fun c₀ b h => ?_⟩` and prove the remaining obligations. Take `⟨⟨hl, hlev, hk, hz, hg⟩, hlevel, hcent, hwt, hlow⟩` from `h`. Use `⟨⟨fun γ g => ?_, ?_, ?_, ?_, fun g => ?_⟩, fun w => Submodule.smul_mem _ a (hlevel w), fun z g => ?_, fun v => ?_, fun v => ?_⟩` and prove the remaining obligations.

Rewrite using `[e2, e2, hl]`. Establish `e : {x | UpperTheory.V.TR.finRep F 2 x (a • φ) = a • φ} = {x | UpperTheory.V.TR.finRep F 2 x φ = φ}`. Use extensionality with `x`. Simplify using `only [Set.mem_ofPred_eq, map_smul]`. Conclude with `smul_right_inj ha`.

Rewrite using `[e]`. Conclude with `hlev`. Use `Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range fun x => UpperTheory.V.TR.cptRep F 2 x φ)) (Submodule.span_le.2 ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨x, rfl⟩`. Use `show UpperTheory.V.TR.cptRep F 2 x (a • φ) ∈ _`.

Rewrite using `[map_smul]`. Conclude with `Submodule.smul_mem _ a (Submodule.subset_span ⟨x, rfl⟩)`. Use `Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ ((fun z : Module.End ℂ (UpperTheory.V.TR.Sm F 2) => z φ) '' UpperTheory.V.TR.Zalg F 2)) (Submodule.span_le.2 ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨z, hz', rfl⟩`. Use `show z (a • φ) ∈ _`.

Rewrite using `[map_smul]`. Conclude with `Submodule.smul_mem _ a (Submodule.subset_span ⟨z, hz', rfl⟩)`. Take `⟨C, N, hC⟩` from `hg g`. Use `⟨‖a‖ * C, N, fun y => ?_⟩` and prove the remaining obligations. Rewrite using `[e2, norm_mul, mul_assoc]`.

Conclude with `mul_le_mul_of_nonneg_left (hC y) (norm_nonneg a)`. Rewrite using `[e2, e2, hcent]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [map_smul]`. Rewrite using `[← smul_sub, hwt v]`.

Conclude with `smul_comm _ _ _`. Simplify using `only [map_smul]`. Rewrite using `[← smul_sub, hlow v, ← smul_add]`. Conclude with `smul_comm _ _ _`. Introduce `x y hy yf`.

Establish `e : ∀ z : Af F, coefAt (fun 𝔪 => a * b 𝔪) z = a * coefAt b z`. Introduce `z`. Unfold `coefAt`. Apply the tactic sequence `split_ifs <;> simp`. Use `(h x y hy yf).mul_left a using 1` and compare the differences between its conclusion and the goal.

Both sides reduce to the same expression. Use function extensionality and compare the values at `ξ`. Rewrite using `[e, mul_assoc]`. Rewrite using `[e2]`. Simplify using `only`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem scalar_action_holds : SPois → SInt → SSmooth → SSmul := by
  intro _ _ _ F _ _ _ ω c k φ a ha
  have e2 : ∀ g, (a • φ).1 g = a * φ.1 g := fun _ => rfl
  refine ⟨fun h => ?_, fun c₀ b h => ?_⟩
  · obtain ⟨⟨hl, hlev, hk, hz, hg⟩, hlevel, hcent, hwt, hlow⟩ := h
    refine ⟨⟨fun γ g => ?_, ?_, ?_, ?_, fun g => ?_⟩, fun w => Submodule.smul_mem _ a (hlevel w),
      fun z g => ?_, fun v => ?_, fun v => ?_⟩
    · rw [e2, e2, hl]
    · have e : {x | UpperTheory.V.TR.finRep F 2 x (a • φ) = a • φ} = {x | UpperTheory.V.TR.finRep F 2 x φ = φ} := by
        ext x
        simp only [Set.mem_ofPred_eq, map_smul]
        exact smul_right_inj ha
      rw [e]
      exact hlev
    · refine Submodule.finiteDimensional_of_le
        (S₂ := Submodule.span ℂ (Set.range fun x => UpperTheory.V.TR.cptRep F 2 x φ)) (Submodule.span_le.2 ?_)
      rintro _ ⟨x, rfl⟩
      show UpperTheory.V.TR.cptRep F 2 x (a • φ) ∈ _
      rw [map_smul]
      exact Submodule.smul_mem _ a (Submodule.subset_span ⟨x, rfl⟩)
    · refine Submodule.finiteDimensional_of_le
        (S₂ := Submodule.span ℂ ((fun z : Module.End ℂ (UpperTheory.V.TR.Sm F 2) => z φ) '' UpperTheory.V.TR.Zalg F 2))
        (Submodule.span_le.2 ?_)
      rintro _ ⟨z, hz', rfl⟩
      show z (a • φ) ∈ _
      rw [map_smul]
      exact Submodule.smul_mem _ a (Submodule.subset_span ⟨z, hz', rfl⟩)
    · obtain ⟨C, N, hC⟩ := hg g
      refine ⟨‖a‖ * C, N, fun y => ?_⟩
      rw [e2, norm_mul, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hC y) (norm_nonneg a)
    · rw [e2, e2, hcent]
      ring
    · simp only [map_smul]
      rw [← smul_sub, hwt v]
      exact smul_comm _ _ _
    · simp only [map_smul]
      rw [← smul_sub, hlow v, ← smul_add]
      exact smul_comm _ _ _
  · intro x y hy yf
    have e : ∀ z : Af F, coefAt (fun 𝔪 => a * b 𝔪) z = a * coefAt b z := by
      intro z
      unfold coefAt
      split_ifs <;> simp
    convert (h x y hy yf).mul_left a using 1
    · rfl
    · funext ξ
      rw [e, mul_assoc]
    · rw [e2]
      simp only
      ring

end UpperTheory.HilbertEisensteinWeightOne
