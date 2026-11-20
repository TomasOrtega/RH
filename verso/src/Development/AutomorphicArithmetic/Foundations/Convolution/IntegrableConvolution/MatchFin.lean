import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.ClosedProperAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.MatchSplit
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.RegOkPi
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.PushTens
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.GlueBasic

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Global.SemiLocal PositivityTheory.Rg.Tf.Geo

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ m v D n _ _ _ _ μE μF hE hF`. Establish `hreg : UpperTheory.ConvolutionTheory.L1.RegOk (v.adicCompletion F) n` using `UpperTheory.ConvolutionTheory.L1.regOkPi.1 _ n`. Take `⟨c, hc, hμ, hφ⟩` from `UpperTheory.ConvolutionTheory.L1.matchSplit (v.adicCompletion F) (CompletionsOver E v) (incFin E v) (galFin σ v) m D n μE μF hE hF hreg`. Use `⟨c, hc, hμ, fun φ h1 h2 => (hφ φ h1 h2).2.2, fun φ h => ?_⟩` and prove the remaining obligations. Take `⟨hcomp, hglue, -, hgc, hcc, -⟩` from `UpperTheory.ConvolutionTheory.L1.glueBasic (v.adicCompletion F) (CompletionsOver E v) (incFin E v) (galFin σ v) m D n`.

Set `e : (Fin (m + 1) → GL (Fin n) (v.adicCompletion F)) ≃ₜ GL (Fin n) (CompletionsOver E v)` to `{ toFun := D.glue n invFun := fun x i => D.comp n i x left_inv := fun g => funext fun i => hcomp g i right_inv := hglue continuous_toFun := hgc continuous_invFun := continuous_pi hcc }`. Establish `hΨc : Continuous fun g : Fin (m + 1) → GL (Fin n) (v.adicCompletion F) => ∏ i, φ i (g i)` using `continuous_finset_prod _ fun i _ => (h i).1.comp (continuous_apply i)`. Establish `hΨs : HasCompactSupport fun g : Fin (m + 1) → GL (Fin n) (v.adicCompletion F) => ∏ i, φ i (g i)`. Use `HasCompactSupport.intro' (K := Set.pi Set.univ fun i => tsupport (φ i)) (isCompact_univ_pi fun i => (h i).2) (isClosed_set_pi fun i _ => isClosed_tsupport _) ?_` and prove the remaining obligations. Introduce `g hg`.

Choose the witnesses or unpack the hypotheses as in `⟨i, -, hi⟩ : ∃ i, i ∈ Set.univ ∧ g i ∉ tsupport (φ i) := by`. Simplify `hg` using `[Set.mem_pi]`. Conclude with `Finset.prod_eq_zero (Finset.mem_univ i) (image_eq_zero_of_notMem_tsupport hi)`. Establish `htens : D.tens n φ = (fun g : Fin (m + 1) → GL (Fin n) (v.adicCompletion F) => ∏ i, φ i (g i)) ∘ e.symm`. Both sides reduce to the same expression.

Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[htens]`. Conclude with `hΨc.comp e.symm.continuous`. Rewrite using `[htens]`. Conclude with `hΨs.comp_isClosedEmbedding e.symm.isClosedEmbedding`.

Establish `hpush` using `UpperTheory.ConvolutionTheory.L1.pushTens (GL (Fin n) (v.adicCompletion F)) μF m φ (fun i => (h i).1) (fun i => (h i).2)`. Rewrite using `[← hpush]`. Unfold `UpperTheory.ConvolutionTheory.L1.Split.transfer`. Use `congr 1`. Use function extensionality and compare the values at `g`.

Simplify using `only [UpperTheory.ConvolutionTheory.L1.Split.tens, hcomp]`.
-/
theorem UpperTheory.ConvolutionTheory.L1.matchFin :
    UpperTheory.ConvolutionTheory.L1.MatchFin := by
  intro F E _ _ _ _ _ σ m v D n _ _ _ _ μE μF hE hF
  have hreg : UpperTheory.ConvolutionTheory.L1.RegOk (v.adicCompletion F) n := UpperTheory.ConvolutionTheory.L1.regOkPi.1 _ n
  obtain ⟨c, hc, hμ, hφ⟩ := UpperTheory.ConvolutionTheory.L1.matchSplit (v.adicCompletion F) (CompletionsOver E v)
    (incFin E v) (galFin σ v) m D n μE μF hE hF hreg
  refine ⟨c, hc, hμ, fun φ h1 h2 => (hφ φ h1 h2).2.2, fun φ h => ?_⟩
  obtain ⟨hcomp, hglue, -, hgc, hcc, -⟩ :=
    UpperTheory.ConvolutionTheory.L1.glueBasic (v.adicCompletion F) (CompletionsOver E v) (incFin E v) (galFin σ v) m D n
  let e : (Fin (m + 1) → GL (Fin n) (v.adicCompletion F)) ≃ₜ GL (Fin n) (CompletionsOver E v) :=
    { toFun := D.glue n
      invFun := fun x i => D.comp n i x
      left_inv := fun g => funext fun i => hcomp g i
      right_inv := hglue
      continuous_toFun := hgc
      continuous_invFun := continuous_pi hcc }
  have hΨc : Continuous fun g : Fin (m + 1) → GL (Fin n) (v.adicCompletion F) => ∏ i, φ i (g i) :=
    continuous_finset_prod _ fun i _ => (h i).1.comp (continuous_apply i)
  have hΨs : HasCompactSupport fun g : Fin (m + 1) → GL (Fin n) (v.adicCompletion F) => ∏ i, φ i (g i) := by
    refine HasCompactSupport.intro' (K := Set.pi Set.univ fun i => tsupport (φ i))
      (isCompact_univ_pi fun i => (h i).2) (isClosed_set_pi fun i _ => isClosed_tsupport _) ?_
    intro g hg
    obtain ⟨i, -, hi⟩ : ∃ i, i ∈ Set.univ ∧ g i ∉ tsupport (φ i) := by
      simpa [Set.mem_pi] using hg
    exact Finset.prod_eq_zero (Finset.mem_univ i) (image_eq_zero_of_notMem_tsupport hi)
  have htens : D.tens n φ = (fun g : Fin (m + 1) → GL (Fin n) (v.adicCompletion F) => ∏ i, φ i (g i)) ∘ e.symm :=
    rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [htens]
    exact hΨc.comp e.symm.continuous
  · rw [htens]
    exact hΨs.comp_isClosedEmbedding e.symm.isClosedEmbedding
  · have hpush := UpperTheory.ConvolutionTheory.L1.pushTens (GL (Fin n) (v.adicCompletion F)) μF m φ
      (fun i => (h i).1) (fun i => (h i).2)
    rw [← hpush]
    unfold UpperTheory.ConvolutionTheory.L1.Split.transfer
    congr 1
    funext g
    simp only [UpperTheory.ConvolutionTheory.L1.Split.tens, hcomp]
