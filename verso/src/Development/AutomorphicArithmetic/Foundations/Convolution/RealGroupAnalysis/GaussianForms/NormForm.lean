import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.NApply
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.EqAmOfBarEq

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

/- English proof (translation)
Introduce `F E _ _ _ _ _ D a`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨s, t, h⟩`. Establish `hm : D.mkE s t * D.bar (D.mkE s t) = am E (a : A F)` using `by rw [D.mkE_mul_bar, h]`. Establish `hu : IsUnit (D.mkE s t * D.bar (D.mkE s t))`.

Rewrite using `[hm]`. Conclude with `a.isUnit.map (am (F := F) E)`. Take `⟨z, hz⟩` from `isUnit_of_mul_isUnit_left hu`. Use `⟨z, Units.ext ?_⟩` and prove the remaining obligations. Rewrite using `[D.coe_ideleNorm, hz, D.co_mkE, h]`.

Simplify using the standard rewrite rules. Introduce and unpack `⟨z, rfl⟩`. Conclude with `⟨D.co z 0, D.co z 1, D.coe_ideleNorm z⟩`.
-/
theorem UpperTheory.ConvolutionTheory.R2.C.normForm :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (D : Dat F E) (a : (A F)ˣ), (∃ s t : A F, (a : A F) = s ^ 2 - rt D.δ * t ^ 2) ↔ ∃ z : (A E)ˣ, ideleNorm F E z = a := by
  intro F E _ _ _ _ _ D a
  constructor
  · rintro ⟨s, t, h⟩
    have hm : D.mkE s t * D.bar (D.mkE s t) = am E (a : A F) := by rw [D.mkE_mul_bar, h]
    have hu : IsUnit (D.mkE s t * D.bar (D.mkE s t)) := by
      rw [hm]
      exact a.isUnit.map (am (F := F) E)
    obtain ⟨z, hz⟩ := isUnit_of_mul_isUnit_left hu
    refine ⟨z, Units.ext ?_⟩
    rw [D.coe_ideleNorm, hz, D.co_mkE, h]
    simp
  · rintro ⟨z, rfl⟩
    exact ⟨D.co z 0, D.co z 1, D.coe_ideleNorm z⟩
