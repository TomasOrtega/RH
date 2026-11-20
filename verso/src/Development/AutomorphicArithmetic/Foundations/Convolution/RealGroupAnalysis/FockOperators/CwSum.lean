import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.XApply
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaReindexing.ActMat

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

/- English proof (translation)
Simplify using `only [cw, map_sum, map_mul, Finset.sum_apply, Pi.mul_apply, Complex.ofReal_sum, Complex.ofReal_mul]`.
-/
private theorem cw_sum {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (w : InfinitePlace F)
    (a b : Fin 4 → A F) : cw w (∑ j, a j * b j) = ∑ j, cw w (a j) * cw w (b j) := by
  simp only [cw, map_sum, map_mul, Finset.sum_apply, Pi.mul_apply, Complex.ofReal_sum, Complex.ofReal_mul]

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ _ D W O h w i φ`. Take `⟨ρ, hρ, -, -⟩` from `UpperTheory.ConvolutionTheory.R2.D.actMat F E D`. Establish `key : W.L h (O.x w i φ) = ∑ j, cw w ((ρ h⁻¹).val i j) • O.x w j (W.L h φ)`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `v`.

Establish `hs : ((∑ j, cw w ((ρ h⁻¹).val i j) • O.x w j (W.L h φ) : S4 F)).1 v = ∑ j, cw w ((ρ h⁻¹).val i j) * (O.x w j (W.L h φ)).1 v`. Rewrite using `[Submodule.coe_sum, Finset.sum_apply]`. Both sides reduce to the same expression. Rewrite using `[hs, W.L_apply, O.x_apply]`. Simplify using `only [O.x_apply, W.L_apply]`.

Establish `hi : D.act h⁻¹ v i = ∑ j, (ρ h⁻¹).val i j * v j`. Rewrite using `[hρ]`. Both sides reduce to the same expression. Rewrite using `[hi, cw_sum, Finset.sum_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[key]`. Use `Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨w, j, Or.inl rfl⟩)` and prove the remaining obligations.
-/
theorem UpperTheory.ConvolutionTheory.R2.Fo.lX :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D) (O : Ops F) (h : GL (Fin 2) (A E)) w i φ, W.L h (O.x w i φ) ∈ Submodule.span ℂ {χ : S4 F | ∃ w' j, χ = O.x w' j (W.L h φ) ∨ χ = O.d w' j (W.L h φ)} := by
  intro F E _ _ _ _ _ _ _ D W O h w i φ
  obtain ⟨ρ, hρ, -, -⟩ := UpperTheory.ConvolutionTheory.R2.D.actMat F E D
  have key : W.L h (O.x w i φ) = ∑ j, cw w ((ρ h⁻¹).val i j) • O.x w j (W.L h φ) := by
    apply Subtype.ext
    funext v
    have hs : ((∑ j, cw w ((ρ h⁻¹).val i j) • O.x w j (W.L h φ) : S4 F)).1 v
        = ∑ j, cw w ((ρ h⁻¹).val i j) * (O.x w j (W.L h φ)).1 v := by
      rw [Submodule.coe_sum, Finset.sum_apply]
      rfl
    rw [hs, W.L_apply, O.x_apply]
    simp only [O.x_apply, W.L_apply]
    have hi : D.act h⁻¹ v i = ∑ j, (ρ h⁻¹).val i j * v j := by
      rw [hρ]; rfl
    rw [hi, cw_sum, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [key]
  refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨w, j, Or.inl rfl⟩)
