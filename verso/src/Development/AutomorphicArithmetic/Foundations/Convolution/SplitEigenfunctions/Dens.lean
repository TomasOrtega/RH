import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbitMeasurability.DetCentralSection
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbitMeasurability.ExistsForm0
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbitMeasurability.Imports
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbitMeasurability.FormBd

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical
open UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Cp

/- English proof (translation)
Introduce `M u hu hne`. Take `⟨F, hF, he, hc⟩` from `Cp.ext u hu`. Establish `h1 : (1 : (A ℚ)ˣ) ∈ UU` using `⟨rfl, fun v => by`. Express the relevant statement in the definitionally equal form `Valued.v (1 : v.adicCompletion ℚ) = 1`. Conclude with `map_one _⟩`.

Establish `hF0 : F ≠ 0` using `fun h => hne (funext fun g => by rw [← he g 1 h1, h]; rfl)`. Take `⟨π, hπ, f, hf, hint⟩` from `pairL Measure.haar F hF hF0 hc`. Take `⟨hb, ht⟩` from `formBd π hπ f hf`. Use `⟨π, hπ, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hcon`.

Use `push Not at hcon`. Take `⟨B, hB⟩` from `hb.bdd`. Take `⟨B', hB'⟩` from `hF.bdd`. Use `hint (fibre M Measure.haar (fun x => f.1 x * F x) ⟨hb.cont.mul hF.cont, fun γ g => by rw [hb.left, hF.left], ⟨B * B', fun x => by rw [norm_mul]; exact mul_le_mul (hB x) (hB' x) (norm_nonneg _) ((norm_nonneg _).trans (hB x))⟩, fun s x => by rw [hb.cen, hF.cen]⟩ fun t htU => ?_)` and prove the remaining obligations. Take `⟨f', hf', e⟩` from `ht t htU`.

Simplify `hcon f' hf'` using `only [e, he _ t htU]`.
-/
theorem UpperTheory.ConvolutionTheory.RankTwoDescent.dens :
    Dens := by
  intro M u hu hne
  obtain ⟨F, hF, he, hc⟩ := Cp.ext u hu
  have h1 : (1 : (A ℚ)ˣ) ∈ UU := ⟨rfl, fun v => by
    change Valued.v (1 : v.adicCompletion ℚ) = 1
    exact map_one _⟩
  have hF0 : F ≠ 0 := fun h => hne (funext fun g => by rw [← he g 1 h1, h]; rfl)
  obtain ⟨π, hπ, f, hf, hint⟩ := pairL Measure.haar F hF hF0 hc
  obtain ⟨hb, ht⟩ := formBd π hπ f hf
  refine ⟨π, hπ, ?_⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨B, hB⟩ := hb.bdd
  obtain ⟨B', hB'⟩ := hF.bdd
  refine hint (fibre M Measure.haar (fun x => f.1 x * F x) ⟨hb.cont.mul hF.cont, fun γ g => by rw [hb.left, hF.left],
    ⟨B * B', fun x => by rw [norm_mul]; exact mul_le_mul (hB x) (hB' x) (norm_nonneg _) ((norm_nonneg _).trans (hB x))⟩,
    fun s x => by rw [hb.cen, hF.cen]⟩ fun t htU => ?_)
  obtain ⟨f', hf', e⟩ := ht t htU
  simpa only [e, he _ t htU] using hcon f' hf'
