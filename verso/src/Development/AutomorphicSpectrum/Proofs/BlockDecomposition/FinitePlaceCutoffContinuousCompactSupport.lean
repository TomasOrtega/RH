import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThPr
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GroundTheory.Global PositivityTheory.Rg.Base1 GlobalTheory.CompanionTheory.BasePsi
open scoped ENNReal NNReal Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.BasePsi.Test

/- English proof (translation)
Introduce `F _ _ S g a hg v`. Establish `hu : (a : AF F).2 v * ((a⁻¹ : (AF F)ˣ) : AF F).2 v = 1`. Establish `h : ((a : AF F) * ((a⁻¹ : (AF F)ˣ) : AF F)).2 v = (1 : AF F).2 v` using `by rw [a.mul_inv]`. Conclude with `h`. Establish `ha : (a : AF F).2 v ≠ 0` using `left_ne_zero_of_mul_eq_one hu`.

Set `e : (Unit → Fv F v) ≃ₜ Fv F v` to `(Homeomorph.funUnique Unit (Fv F v)).trans (Homeomorph.mulLeft₀ ((a : AF F).2 v) ha)`. Establish `he : ∀ y, e y = (a : AF F).2 v * y ()` using `fun y => rfl`. Establish `hO : IsClopen (v.adicCompletionIntegers F : Set (Fv F v))` using `Valued.isClopen_integer _`. Establish `hOc : IsCompact (v.adicCompletionIntegers F : Set (Fv F v))` using `PI.AdicCompletionValuation.isCompact_adicCompletionIntegers F v`. Establish `key : ∀ h : Fv F v → ℝ, Continuous h → HasCompactSupport h → Continuous (h ∘ e) ∧ HasCompactSupport (h ∘ e)` using `fun h h1 h2 => ⟨h1.comp e.continuous, h2.comp_isClosedEmbedding e.isClosedEmbedding⟩`.

Distinguish the cases in `hv : v ∈ S`. Establish `hfun : psiA S g a v = g v ∘ e`. Use function extensionality and compare the values at `y`. Simplify using `[psiA, hv, he]`. Rewrite using `[hfun]`.

Conclude with `key _ (hg v hv).1 (hg v hv).2`. Establish `hfun : psiA S g a v = (Set.indicator (v.adicCompletionIntegers F : Set (Fv F v)) (fun _ => (1 : ℝ))) ∘ e`. Use function extensionality and compare the values at `y`. Simplify using `[psiA, hv, he, Set.indicator_apply]`. Rewrite using `[hfun]`.

Use `key _ (hO.continuous_indicator continuous_const) ?_` and prove the remaining obligations. Conclude with `HasCompactSupport.intro hOc fun x hx => Set.indicator_of_notMem hx _`.
-/
theorem psiA_isTest : ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (g : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ) (a : (AF F)ˣ), (∀ v ∈ S, Continuous (g v) ∧ HasCompactSupport (g v)) →
    ∀ v : HeightOneSpectrum (𝓞 F), Continuous (psiA S g a v) ∧ HasCompactSupport (psiA S g a v) := by
  intro F _ _ S g a hg v
  have hu : (a : AF F).2 v * ((a⁻¹ : (AF F)ˣ) : AF F).2 v = 1 := by
    have h : ((a : AF F) * ((a⁻¹ : (AF F)ˣ) : AF F)).2 v = (1 : AF F).2 v := by rw [a.mul_inv]
    exact h
  have ha : (a : AF F).2 v ≠ 0 := left_ne_zero_of_mul_eq_one hu
  let e : (Unit → Fv F v) ≃ₜ Fv F v :=
    (Homeomorph.funUnique Unit (Fv F v)).trans (Homeomorph.mulLeft₀ ((a : AF F).2 v) ha)
  have he : ∀ y, e y = (a : AF F).2 v * y () := fun y => rfl
  have hO : IsClopen (v.adicCompletionIntegers F : Set (Fv F v)) := Valued.isClopen_integer _
  have hOc : IsCompact (v.adicCompletionIntegers F : Set (Fv F v)) :=
    PI.AdicCompletionValuation.isCompact_adicCompletionIntegers F v
  have key : ∀ h : Fv F v → ℝ, Continuous h → HasCompactSupport h →
      Continuous (h ∘ e) ∧ HasCompactSupport (h ∘ e) := fun h h1 h2 =>
    ⟨h1.comp e.continuous, h2.comp_isClosedEmbedding e.isClosedEmbedding⟩
  by_cases hv : v ∈ S
  · have hfun : psiA S g a v = g v ∘ e := by
      funext y
      simp [psiA, hv, he]
    rw [hfun]
    exact key _ (hg v hv).1 (hg v hv).2
  · have hfun : psiA S g a v =
        (Set.indicator (v.adicCompletionIntegers F : Set (Fv F v)) (fun _ => (1 : ℝ))) ∘ e := by
      funext y
      simp [psiA, hv, he, Set.indicator_apply]
    rw [hfun]
    refine key _ (hO.continuous_indicator continuous_const) ?_
    exact HasCompactSupport.intro hOc fun x hx => Set.indicator_of_notMem hx _

end GlobalTheory.CompanionTheory.BasePsi.Test

end
