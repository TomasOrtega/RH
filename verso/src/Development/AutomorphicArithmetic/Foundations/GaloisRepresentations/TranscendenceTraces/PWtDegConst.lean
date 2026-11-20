import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

/- English proof (translation)
Introduce `_ Z S p _ _ w hw`. Take `⟨ψ, hψ, hsum⟩` from `hw (Sq.self p) (fun _ => 1) (IsLocallyConstant.const 1)`. Establish `hψ' : IsLocallyConstant (fun s : S => ψ s)` using `hψ`. Distinguish the cases in `hS : Nonempty S`. Take `⟨s₀⟩` from `hS`.

Use `⟨ψ s₀, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `Ω _ _ x`. Establish `h : ψ (pt x) = ∑ᶠ (z : gp Ω ⟶ Z) (_ : z ∈ fib p x), w Ω (z ≫ 𝟙 Z) * 1` using `hsum Ω x`. Simplify using `only [Category.comp_id, mul_one] at h`. Use `show (∑ᶠ (z : gp Ω ⟶ Z) (_ : z ∈ fib p x), w Ω z) = ψ s₀`.

Establish `hc : ψ (pt x) = ψ s₀` using `hψ'.apply_eq_of_preconnectedSpace (pt x) s₀`. Rewrite using `[← hc]`. Conclude with `h.symm`. Use `⟨0, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `Ω _ _ x`.

Conclude with `(hS ⟨pt x⟩).elim`.
-/
theorem UpperTheory.Gal.TranscendenceTraces.wtDegConst_of :
    PtEx → WtDegConst := by
  intro _ Z S p _ _ w hw
  obtain ⟨ψ, hψ, hsum⟩ := hw (Sq.self p) (fun _ => 1) (IsLocallyConstant.const 1)
  have hψ' : IsLocallyConstant (fun s : S => ψ s) := hψ
  by_cases hS : Nonempty S
  · obtain ⟨s₀⟩ := hS
    refine ⟨ψ s₀, ?_⟩
    funext Ω _ _ x
    have h : ψ (pt x) = ∑ᶠ (z : gp Ω ⟶ Z) (_ : z ∈ fib p x), w Ω (z ≫ 𝟙 Z) * 1 := hsum Ω x
    simp only [Category.comp_id, mul_one] at h
    show (∑ᶠ (z : gp Ω ⟶ Z) (_ : z ∈ fib p x), w Ω z) = ψ s₀
    have hc : ψ (pt x) = ψ s₀ := hψ'.apply_eq_of_preconnectedSpace (pt x) s₀
    rw [← hc]
    exact h.symm
  · refine ⟨0, ?_⟩
    funext Ω _ _ x
    exact (hS ⟨pt x⟩).elim
