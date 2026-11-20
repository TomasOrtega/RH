import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.TracePow

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL ValuativeRel Matrix MeasureTheory UpperTheory.ConvolutionTheory.Loc MulAction UpperTheory.Gal.LocD

/- English proof (translation)
Introduce `hE T J _ _ _ _ _ ρ s A hA hμs`. Take `⟨μ, l0, hl0, hl0eq, hgen⟩` from `hE T J ρ`. Establish `hμ : ∀ t, μ (s t) = μ t` using `hμs μ hgen`. Set `W : Submodule ℂ (Module.Dual ℂ J)` to `{ carrier := {l | ∀ t y, l (ρ t y) = (μ t : ℂ) * l y} add_mem' := by`. Introduce `a b ha hb`.

Simplify using `only [Set.mem_setOf_eq] at *`. Introduce `t y`. Simplify using `only [LinearMap.add_apply, ha t y, hb t y]`. Expand and normalize the polynomial expressions, which then agree. Use the proof step `zero_mem' := by`.

Simplify using `only [Set.mem_setOf_eq]`. Introduce `t y`. Simplify using the standard rewrite rules. Use the proof step `smul_mem' := by`. Introduce `c l hl`.

Simplify using `only [Set.mem_setOf_eq] at *`. Introduce `t y`. Simplify using `only [LinearMap.smul_apply, smul_eq_mul, hl t y]`. Use `ring }`. Establish `hAW : ∀ l ∈ W, LinearMap.dualMap A l ∈ W`.

Introduce `l hl t y`. Use `show l (A (ρ t y)) = (μ t : ℂ) * l (A y)`. Rewrite using `[hA, hl, hμ]`. Set `A' : W →ₗ[ℂ] W` to `(LinearMap.dualMap A).restrict hAW`. Use `haveI : Nontrivial W := ⟨⟨⟨l0, hl0eq⟩, 0, fun h => hl0 (congrArg Subtype.val h)⟩⟩`.

Take `⟨c, hc⟩` from `Module.End.exists_eigenvalue A'`. Take `⟨v, hv⟩` from `hc.exists_hasEigenvector`. Use `⟨μ, (v : Module.Dual ℂ J), c, fun h => hv.2 (Subtype.ext h), hμ, v.2, fun y => ?_⟩` and prove the remaining obligations. Use `congrArg (fun w : W => (w : Module.Dual ℂ J) y) hv.apply_eq_smul` as an intermediate fact. Simplify `this` using `[A']`.
-/
theorem UpperTheory.Gal.LocD.eig :
    EigZero → Eig := by
  intro hE T J _ _ _ _ _ ρ s A hA hμs
  obtain ⟨μ, l0, hl0, hl0eq, hgen⟩ := hE T J ρ
  have hμ : ∀ t, μ (s t) = μ t := hμs μ hgen
  let W : Submodule ℂ (Module.Dual ℂ J) :=
    { carrier := {l | ∀ t y, l (ρ t y) = (μ t : ℂ) * l y}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at *
        intro t y
        simp only [LinearMap.add_apply, ha t y, hb t y]
        ring
      zero_mem' := by
        simp only [Set.mem_setOf_eq]
        intro t y
        simp
      smul_mem' := by
        intro c l hl
        simp only [Set.mem_setOf_eq] at *
        intro t y
        simp only [LinearMap.smul_apply, smul_eq_mul, hl t y]
        ring }
  have hAW : ∀ l ∈ W, LinearMap.dualMap A l ∈ W := by
    intro l hl t y
    show l (A (ρ t y)) = (μ t : ℂ) * l (A y)
    rw [hA, hl, hμ]
  let A' : W →ₗ[ℂ] W := (LinearMap.dualMap A).restrict hAW
  haveI : Nontrivial W := ⟨⟨⟨l0, hl0eq⟩, 0, fun h => hl0 (congrArg Subtype.val h)⟩⟩
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue A'
  obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
  refine ⟨μ, (v : Module.Dual ℂ J), c, fun h => hv.2 (Subtype.ext h), hμ, v.2, fun y => ?_⟩
  have := congrArg (fun w : W => (w : Module.Dual ℂ J) y) hv.apply_eq_smul
  simpa [A'] using this
