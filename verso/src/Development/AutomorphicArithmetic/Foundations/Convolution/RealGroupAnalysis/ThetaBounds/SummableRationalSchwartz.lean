import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.UnfoldedThetaIntegralConvergesSimilitudeOne
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.WtBound
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.EmbPiInjective

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

/- English proof (translation)
Take `⟨-, K, hK, hB⟩` from `wtBound F φ`. Take `⟨N, hN⟩` from `wtSum F`. Take `⟨B, hB⟩` from `hB N`. Take `⟨C, hC⟩` from `hN K hK 1 one_pos`. Establish `hab : (1 : ℝ) ≤ ab (1 : (A F)ˣ)`.

Simplify using `[ab]`. Establish `hs` using `(hC 1 hab).1`. Use `Summable.of_norm_bounded (g := fun ξ => B * wt K N (sc (1 : (A F)ˣ) ξ)) (hs.mul_left B) ?_` and prove the remaining obligations. Introduce `ξ`. Use `hB () (Set.mem_univ _) (fun i => rt (ξ i))` as an intermediate fact.

Establish `hsc : sc (1 : (A F)ˣ) ξ = fun i => rt (ξ i)`. Use function extensionality and compare the values at `i`. Conclude with `one_mul _`. Rewrite using `[hsc]`. Conclude with `this`.
-/
private theorem summable_rational_schwartz (F : Type) [Field F] [NumberField F] (φ : S4 F) :
    Summable (fun ξ : Fin 4 → F => φ.1 fun i => rt (ξ i)) := by
  obtain ⟨-, K, hK, hB⟩ := wtBound F φ
  obtain ⟨N, hN⟩ := wtSum F
  obtain ⟨B, hB⟩ := hB N
  obtain ⟨C, hC⟩ := hN K hK 1 one_pos
  have hab : (1 : ℝ) ≤ ab (1 : (A F)ˣ) := by
    simp [ab]
  have hs := (hC 1 hab).1
  refine Summable.of_norm_bounded (g := fun ξ => B * wt K N (sc (1 : (A F)ˣ) ξ)) (hs.mul_left B) ?_
  intro ξ
  have := hB () (Set.mem_univ _) (fun i => rt (ξ i))
  have hsc : sc (1 : (A F)ˣ) ξ = fun i => rt (ξ i) := by
    funext i
    exact one_mul _
  rw [hsc]
  exact this

/- English proof (translation)
Introduce `F _ _`. Use `⟨fun φ φ' => ?_, fun c φ => ?_⟩` and prove the remaining obligations. Establish `h : ∀ ξ : Fin 4 → F, (φ + φ').1 (fun i => rt (ξ i)) = φ.1 (fun i => rt (ξ i)) + φ'.1 (fun i => rt (ξ i))` using `fun ξ => rfl`. Simplify using `only [Th, h]`. Conclude with `(summable_rational_schwartz F φ).tsum_add (summable_rational_schwartz F φ')`.

Establish `h : ∀ ξ : Fin 4 → F, (c • φ).1 (fun i => rt (ξ i)) = c * φ.1 (fun i => rt (ξ i))` using `fun ξ => rfl`. Simplify using `only [Th, h]`. Conclude with `tsum_mul_left`.
-/
theorem UpperTheory.ConvolutionTheory.R2.Ff.thLin :
    ∀ (F : Type) [Field F] [NumberField F], ThLin F := by
  intro F _ _
  refine ⟨fun φ φ' => ?_, fun c φ => ?_⟩
  · have h : ∀ ξ : Fin 4 → F, (φ + φ').1 (fun i => rt (ξ i)) =
        φ.1 (fun i => rt (ξ i)) + φ'.1 (fun i => rt (ξ i)) := fun ξ => rfl
    simp only [Th, h]
    exact (summable_rational_schwartz F φ).tsum_add (summable_rational_schwartz F φ')
  · have h : ∀ ξ : Fin 4 → F, (c • φ).1 (fun i => rt (ξ i)) =
        c * φ.1 (fun i => rt (ξ i)) := fun ξ => rfl
    simp only [Th, h]
    exact tsum_mul_left
