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
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Assume the negation of the conclusion and derive a contradiction. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
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
