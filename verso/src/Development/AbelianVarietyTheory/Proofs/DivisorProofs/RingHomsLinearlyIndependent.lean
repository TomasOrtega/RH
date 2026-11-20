import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SandwichMaps
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory

/- English proof (translation)
Introduce `C _ O _ _ Λ _ hinj S c hsum`. Set `φ : (Λ →+* O) → (Λ →* C)` to `fun σ => ((algebraMap O C).comp σ).toMonoidHom`. Establish `hφ : Function.Injective φ`. Introduce `σ τ h`. Use extensionality with `a`.

Apply `hinj` to reduce the goal to its premises. Use `congrArg (fun f : Λ →* C => f a) h` as an intermediate fact. Simplify `this` using `[φ]`. Establish `hli` using `(linearIndependent_monoidHom Λ C).comp φ hφ`. Rewrite `hli` using `[linearIndependent_iff']`.

Introduce `σ hσ`. Apply `hli S c _ σ hσ` to reduce the goal to its premises. Use function extensionality and compare the values at `a`. Simplify `hsum a` using `[φ, Finset.sum_apply]`.
-/
theorem ringHom_independent_via_algebraMap :
    ∀ (C : Type) [Field C] (O : Type) [CommRing O] [Algebra O C] (Λ : Type) [CommRing Λ],
      Function.Injective (algebraMap O C) → ∀ (S : Finset (Λ →+* O)) (c : (Λ →+* O) → C),
        (∀ a : Λ, ∑ σ ∈ S, c σ * algebraMap O C (σ a) = 0) → ∀ σ ∈ S, c σ = 0 := by
  intro C _ O _ _ Λ _ hinj S c hsum
  classical
  let φ : (Λ →+* O) → (Λ →* C) := fun σ => ((algebraMap O C).comp σ).toMonoidHom
  have hφ : Function.Injective φ := by
    intro σ τ h
    ext a
    apply hinj
    have := congrArg (fun f : Λ →* C => f a) h
    simpa [φ] using this
  have hli := (linearIndependent_monoidHom Λ C).comp φ hφ
  rw [linearIndependent_iff'] at hli
  intro σ hσ
  apply hli S c _ σ hσ
  funext a
  simpa [φ, Finset.sum_apply] using hsum a

end GlobalTheory
