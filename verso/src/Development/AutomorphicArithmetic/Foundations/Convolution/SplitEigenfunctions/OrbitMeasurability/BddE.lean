import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbitMeasurability.PerCont
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.UnitsCpt
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.ContinuousAdelicGL2OfContinuousEntries
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.AbLower

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical Pointwise

/- English proof (translation)
Introduce `E _ _ _ P φ hφ C hC`. Take `⟨c, C₀, hc, hC₀, hred⟩` from `UpperTheory.ConvolutionTheory.RankTwoDescent.redE E`. Establish `hC' : IsCompact ((gl (F` using `E) '' C₀) * C) := (hC₀.image continuous_gl).mul hC`. Take `⟨hL, -, hd⟩` from `UpperTheory.ConvolutionTheory.RankTwoDescent.decE E P φ hφ`. Take `⟨B, hB⟩` from `hd _ hC' c hc 0`.

Use `⟨B, fun h k hk => ?_⟩` and prove the remaining obligations. Take `⟨γ, u, b, k₀, hk₀, hg, hb⟩` from `hred h`. Establish `e1 : φ.1 (gl h * k) = φ.1 (gl (nU u * mD b) * (gl k₀ * k))`. Rewrite using `[← mul_assoc, ← gl_mul, ← hg, gl_mul, gl_ratS, mul_assoc, hL.2]`. Establish `h1` using `hB u b (gl k₀ * k) (Set.mul_mem_mul ⟨k₀, hk₀, rfl⟩ hk) hb`.

Rewrite using `[e1]`. Simplify using `using h1`.
-/
theorem UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.bddE :
    UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.BddE := by
  intro E _ _ _ P φ hφ C hC
  obtain ⟨c, C₀, hc, hC₀, hred⟩ := UpperTheory.ConvolutionTheory.RankTwoDescent.redE E
  have hC' : IsCompact ((gl (F := E) '' C₀) * C) := (hC₀.image continuous_gl).mul hC
  obtain ⟨hL, -, hd⟩ := UpperTheory.ConvolutionTheory.RankTwoDescent.decE E P φ hφ
  obtain ⟨B, hB⟩ := hd _ hC' c hc 0
  refine ⟨B, fun h k hk => ?_⟩
  obtain ⟨γ, u, b, k₀, hk₀, hg, hb⟩ := hred h
  have e1 : φ.1 (gl h * k) = φ.1 (gl (nU u * mD b) * (gl k₀ * k)) := by
    rw [← mul_assoc, ← gl_mul, ← hg, gl_mul, gl_ratS, mul_assoc, hL.2]
  have h1 := hB u b (gl k₀ * k) (Set.mul_mem_mul ⟨k₀, hk₀, rfl⟩ hk) hb
  rw [e1]
  simpa using h1
