import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.ContinuousEntry
import GroundTheory.GlobalFields.TateThesis.AdeleScaling

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

/- English proof (translation)
Introduce `F _ _ k v`. Establish `hinv : (Reduction.finAt v (gl k))⁻¹ = Reduction.finAt v (gl k⁻¹)`. Establish `e : ∀ g : GL (Fin 2) (A F), Reduction.finAt v g = Matrix.GeneralLinearGroup.map (Reduction.finEval v) g`. Introduce `g`. Use extensionality with `i j`.

Both sides reduce to the same expression. Rewrite using `[e, e, ← map_inv, ← map_inv]`. Establish `hent : ∀ (g : G1 F) i j, (Reduction.finAt v (gl g)) i j = (g i j).2 v` using `fun _ _ _ => rfl`. Rewrite using `[GLnLocal.mem_integralGL_iff, hinv]`. Simplify using `only [hent, GroundTheory.Global.mem_valuationInteger_iff]`.

Use `⟨fun h => ⟨h, ?_⟩, fun h => h.1⟩` and prove the remaining obligations. Introduce `i j`. Establish `e : (k⁻¹ : G1 F).1 = !![k.1 1 1, -k.1 0 1; -k.1 1 0, k.1 0 0]`. Rewrite using `[Matrix.SpecialLinearGroup.coe_inv, adjugate_fin_two]`. Establish `hn : ∀ a b, (-(k.1 a b)).2 v ∈ v.adicCompletionIntegers F` using `fun a b => neg_mem (h a b)`.

Use `show ((k⁻¹ : G1 F).1 i j).2 v ∈ _`. Rewrite using `[e]`. Apply the tactic sequence `fin_cases i <;> fin_cases j`. Conclude with `h 1 1`. Conclude with `hn 0 1`.

Conclude with `hn 1 0`. Conclude with `h 0 0`.
-/
theorem UpperTheory.ConvolutionTheory.R2.M.kkFin :
    ∀ (F : Type) [Field F] [NumberField F], ∀ (k : G1 F) (v : HeightOneSpectrum (𝓞 F)), IntAt v k ↔ Reduction.finAt v (gl k) ∈ GLnLocal.integralGL (v.adicCompletion F) 2 := by
  intro F _ _ k v
  have hinv : (Reduction.finAt v (gl k))⁻¹ = Reduction.finAt v (gl k⁻¹) := by
    have e : ∀ g : GL (Fin 2) (A F), Reduction.finAt v g = Matrix.GeneralLinearGroup.map (Reduction.finEval v) g := by
      intro g; ext i j; rfl
    rw [e, e, ← map_inv, ← map_inv]
  have hent : ∀ (g : G1 F) i j, (Reduction.finAt v (gl g)) i j = (g i j).2 v := fun _ _ _ => rfl
  rw [GLnLocal.mem_integralGL_iff, hinv]
  simp only [hent, GroundTheory.Global.mem_valuationInteger_iff]
  refine ⟨fun h => ⟨h, ?_⟩, fun h => h.1⟩
  intro i j
  have e : (k⁻¹ : G1 F).1 = !![k.1 1 1, -k.1 0 1; -k.1 1 0, k.1 0 0] := by
    rw [Matrix.SpecialLinearGroup.coe_inv, adjugate_fin_two]
  have hn : ∀ a b, (-(k.1 a b)).2 v ∈ v.adicCompletionIntegers F := fun a b =>
    neg_mem (h a b)
  show ((k⁻¹ : G1 F).1 i j).2 v ∈ _
  rw [e]
  fin_cases i <;> fin_cases j
  · exact h 1 1
  · exact hn 0 1
  · exact hn 1 0
  · exact h 0 0
