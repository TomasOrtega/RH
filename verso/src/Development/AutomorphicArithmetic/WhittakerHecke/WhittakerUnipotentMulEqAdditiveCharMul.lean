import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.ThInf
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.EqAmOfBarEq
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.NormWfLe
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExistsRowSec

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.TA
open UpperTheory.ConvolutionTheory.R2.G (FS2 nE)
open scoped Classical

/- English proof (translation)
Introduce `E _ _ D f hf v h`. Establish `hadd : ∀ u w : Fin 2 → A ℚ, nE D (u + w) = nE D u * nE D w` using `fun u w => by`. Simplify using `only [nE, Pi.add_apply, D.mkE_add, Pp.n_add]`. Set `G : (Fin 2 → A ℚ) → ℂ` to `fun u => f (nE D u * h) * ψ (u 1)`. Establish `hper : ∀ ξ ∈ GroundTheory.Automorphic.FourierWhittaker.vecLattice ℚ (Fin 2), ∀ x, G (ξ + x) = G x`.

Introduce `ξ hξ x`. Take `⟨η, rfl⟩` from `GroundTheory.Automorphic.FourierWhittaker.mem_vecLattice.1 hξ`. Establish `e1 : D.mkE (rt (η 0) + x 0) (rt (η 1) + x 1) = rt (algebraMap ℚ E (η 0) + algebraMap ℚ E (η 1) * D.θ) + D.mkE (x 0) (x 1)`. Rewrite using `[D.mkE_add, D.mkE_rt]`. Express the relevant statement in the definitionally equal form `f (gl (nU (D.mkE (rt (η 0) + x 0) (rt (η 1) + x 1))) * h) * ψ (rt (η 1) + x 1) = f (gl (nU (D.mkE (x 0) (x 1))) * h) * ψ (x 1)`.

Rewrite using `[e1, hf.per, Pp.ψ_add, Pp.ψ_rt, one_mul]`. Establish `key : ∫ u in FS2 ℚ, G (u + v) ∂(adeleMeasurePi ℚ) = ∫ u in FS2 ℚ, G u ∂(adeleMeasurePi ℚ)` using `GroundTheory.Automorphic.FourierWhittaker.setIntegral_comp_add v hper`. Establish `pt : ∀ u : Fin 2 → A ℚ, f (nE D u * (nE D v * h)) * ψ (u 1) = ψ (-(v 1)) * G (u + v)`. Introduce `u`. Establish `e2 : ψ (u 1) = ψ (-(v 1)) * ψ ((u + v) 1)`.

Rewrite using `[← Pp.ψ_add]`. Use `congr 1`. Simplify using `only [Pi.add_apply]`. Expand and normalize the polynomial expressions, which then agree. Express the relevant statement in the definitionally equal form `_ = ψ (-(v 1)) * (f (nE D (u + v) * h) * ψ ((u + v) 1))`.

Rewrite using `[hadd, mul_assoc, e2]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [Wo, pt]`. Rewrite using `[integral_const_mul]`. Conclude with `congrArg _ key`.
-/
theorem UpperTheory.whittaker_unipotent_mul_eq_additiveChar_mul :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (f : GL (Fin 2) (A E) → ℂ), Pp.Lf f → ∀ (v : Fin 2 → A ℚ) (h : GL (Fin 2) (A E)),
        Wo D f (nE D v * h) = ψ (-(v 1)) * Wo D f h := by
  intro E _ _ D f hf v h
  have hadd : ∀ u w : Fin 2 → A ℚ, nE D (u + w) = nE D u * nE D w := fun u w => by
    simp only [nE, Pi.add_apply, D.mkE_add, Pp.n_add]
  let G : (Fin 2 → A ℚ) → ℂ := fun u => f (nE D u * h) * ψ (u 1)
  have hper : ∀ ξ ∈ GroundTheory.Automorphic.FourierWhittaker.vecLattice ℚ (Fin 2), ∀ x, G (ξ + x) = G x := by
    intro ξ hξ x
    obtain ⟨η, rfl⟩ := GroundTheory.Automorphic.FourierWhittaker.mem_vecLattice.1 hξ
    have e1 : D.mkE (rt (η 0) + x 0) (rt (η 1) + x 1) =
        rt (algebraMap ℚ E (η 0) + algebraMap ℚ E (η 1) * D.θ) + D.mkE (x 0) (x 1) := by
      rw [D.mkE_add, D.mkE_rt]
    change f (gl (nU (D.mkE (rt (η 0) + x 0) (rt (η 1) + x 1))) * h) * ψ (rt (η 1) + x 1) =
      f (gl (nU (D.mkE (x 0) (x 1))) * h) * ψ (x 1)
    rw [e1, hf.per, Pp.ψ_add, Pp.ψ_rt, one_mul]
  have key : ∫ u in FS2 ℚ, G (u + v) ∂(adeleMeasurePi ℚ) = ∫ u in FS2 ℚ, G u ∂(adeleMeasurePi ℚ) :=
    GroundTheory.Automorphic.FourierWhittaker.setIntegral_comp_add v hper
  have pt : ∀ u : Fin 2 → A ℚ, f (nE D u * (nE D v * h)) * ψ (u 1) = ψ (-(v 1)) * G (u + v) := by
    intro u
    have e2 : ψ (u 1) = ψ (-(v 1)) * ψ ((u + v) 1) := by
      rw [← Pp.ψ_add]
      congr 1
      simp only [Pi.add_apply]
      ring
    change _ = ψ (-(v 1)) * (f (nE D (u + v) * h) * ψ ((u + v) 1))
    rw [hadd, mul_assoc, e2]
    ring
  simp only [Wo, pt]
  rw [integral_const_mul]
  exact congrArg _ key
