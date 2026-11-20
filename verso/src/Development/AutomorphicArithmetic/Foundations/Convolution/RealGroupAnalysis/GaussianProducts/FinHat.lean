import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExistsRowSec
import GroundTheory.HeightsAndTheta.Theta.Weil.PartialFourierAdelicPi

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

namespace UpperTheory.ConvolutionTheory.R2.G.FiniteFourierHat

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Take `⟨hl, hc⟩` from `hg`. Establish `hcont : Continuous fun s : FiniteAdeleRing (𝓞 F) F => Function.update v 1 s` using `continuous_const.update 1 continuous_id`. Use `⟨hl.comp_continuous hcont, ?_⟩` and prove the remaining obligations. Use `HasCompactSupport.intro (hc.isCompact.image (continuous_apply 1)) fun s hs => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `h`.

Conclude with `hs ⟨Function.update v 1 s, subset_tsupport _ h, by simp⟩`.
-/
private theorem slice_mem {g : (Fin 4 → FiniteAdeleRing (𝓞 F) F) → ℂ}
    (hg : g ∈ finiteSchwartzBruhatPi F (ι := Fin 4)) (v : Fin 4 → FiniteAdeleRing (𝓞 F) F) :
    (fun s => g (Function.update v 1 s)) ∈ finiteSchwartzBruhat F := by
  obtain ⟨hl, hc⟩ := hg
  have hcont : Continuous fun s : FiniteAdeleRing (𝓞 F) F => Function.update v 1 s :=
    continuous_const.update 1 continuous_id
  refine ⟨hl.comp_continuous hcont, ?_⟩
  refine HasCompactSupport.intro (hc.isCompact.image (continuous_apply 1)) fun s hs => ?_
  by_contra h
  exact hs ⟨Function.update v 1 s, subset_tsupport _ h, by simp⟩

private noncomputable def T (g : (Fin 4 → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (v : Fin 4 → FiniteAdeleRing (𝓞 F) F) : ℂ :=
  finiteFourier F (fun s => g (Function.update v 1 s)) (-(v 1))

/- English proof (translation)
Use function extensionality and compare the values at `v`. Establish `hs : ∀ s, finiteTensor h (Function.update v 1 s) * (finiteAdelicChar F (s * -(v 1)) : ℂ) = (h 0 (v 0) * h 2 (v 2) * h 3 (v 3)) * (h 1 s * (finiteAdelicChar F (s * -(v 1)) : ℂ))`. Introduce `s`. Simplify using `[finiteTensor, Fin.prod_univ_four, Function.update_apply]`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only [T, finiteFourier]`. Repeatedly rewrite using `[hs]`. Rewrite using `[integral_const_mul]`. Simplify using `[finiteTensor, Fin.prod_univ_four, finiteFourier]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem T_tensor (h : Fin 4 → FiniteAdeleRing (𝓞 F) F → ℂ) :
    T (finiteTensor h) =
      finiteTensor ![h 0, fun x => finiteFourier F (h 1) (-x), h 2, h 3] := by
  funext v
  have hs : ∀ s, finiteTensor h (Function.update v 1 s) * (finiteAdelicChar F (s * -(v 1)) : ℂ) =
      (h 0 (v 0) * h 2 (v 2) * h 3 (v 3)) * (h 1 s * (finiteAdelicChar F (s * -(v 1)) : ℂ)) := by
    intro s
    simp [finiteTensor, Fin.prod_univ_four, Function.update_apply]
    ring
  simp only [T, finiteFourier]
  simp_rw [hs]
  rw [integral_const_mul]
  simp [finiteTensor, Fin.prod_univ_four, finiteFourier]
  ring

/- English proof (translation)
Assemble the required witnesses or components as `⟨hf.1.comp_continuous continuous_neg, hf.2.comp_homeomorph (Homeomorph.neg _)⟩`.
-/
private theorem neg_mem {f : FiniteAdeleRing (𝓞 F) F → ℂ} (hf : f ∈ finiteSchwartzBruhat F) :
    (fun x => f (-x)) ∈ finiteSchwartzBruhat F :=
  ⟨hf.1.comp_continuous continuous_neg, hf.2.comp_homeomorph (Homeomorph.neg _)⟩

/- English proof (translation)
Establish `hsub` using `(finiteSchwartzBruhatPi_eq_span (K := F) (ι := Fin 4)).ge`. Rewrite `hg` using `[finiteSchwartzBruhatPi_eq_span]`. Proceed by induction on `hg using Submodule.span_induction with`. Consider the case `mem f hf`. Take `⟨⟨J, a⟩, rfl⟩` from `hf`.

Rewrite using `[T_tensor]`. Use `finiteTensor_mem fun i => ?_` and prove the remaining obligations. Use `fin_cases i`. Conclude with `cosetIndicator_mem_finiteSchwartzBruhat J _`. Conclude with `neg_mem (finiteFourier_mem_finiteSchwartzBruhat (cosetIndicator_mem_finiteSchwartzBruhat J _))`.

Conclude with `cosetIndicator_mem_finiteSchwartzBruhat J _`. Conclude with `cosetIndicator_mem_finiteSchwartzBruhat J _`. Consider the case `zero`. Establish `: T (0 : (Fin 4 → FiniteAdeleRing (𝓞 F) F) → ℂ) = 0`. Use function extensionality and compare the values at `v`.

Simplify using `[T, finiteFourier]`. Rewrite using `[this]`. Conclude with `zero_mem _`. Consider the case `add f₁ f₂ h₁ h₂ ih₁ ih₂`. Establish `: T (f₁ + f₂) = T f₁ + T f₂`.

Use function extensionality and compare the values at `v`. Conclude with `congrFun (finiteFourier_add (integrable_of_mem_finiteSchwartzBruhat (slice_mem (hsub h₁) v)) (integrable_of_mem_finiteSchwartzBruhat (slice_mem (hsub h₂) v))) _`. Rewrite using `[this]`. Conclude with `add_mem ih₁ ih₂`. Consider the case `smul c f _ ih`.

Establish `: T (c • f) = c • T f`. Use function extensionality and compare the values at `v`. Simplify using `only [T, finiteFourier, Pi.smul_apply, smul_eq_mul, mul_assoc]`. Conclude with `integral_const_mul _ _`. Rewrite using `[this]`.

Conclude with `Submodule.smul_mem _ c ih`.
-/
private theorem T_mem {g : (Fin 4 → FiniteAdeleRing (𝓞 F) F) → ℂ}
    (hg : g ∈ finiteSchwartzBruhatPi F (ι := Fin 4)) :
    T g ∈ finiteSchwartzBruhatPi F (ι := Fin 4) := by
  have hsub := (finiteSchwartzBruhatPi_eq_span (K := F) (ι := Fin 4)).ge
  rw [finiteSchwartzBruhatPi_eq_span] at hg
  induction hg using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨⟨J, a⟩, rfl⟩ := hf
    rw [T_tensor]
    refine finiteTensor_mem fun i => ?_
    fin_cases i
    · exact cosetIndicator_mem_finiteSchwartzBruhat J _
    · exact neg_mem (finiteFourier_mem_finiteSchwartzBruhat
        (cosetIndicator_mem_finiteSchwartzBruhat J _))
    · exact cosetIndicator_mem_finiteSchwartzBruhat J _
    · exact cosetIndicator_mem_finiteSchwartzBruhat J _
  | zero =>
    have : T (0 : (Fin 4 → FiniteAdeleRing (𝓞 F) F) → ℂ) = 0 := by
      funext v
      simp [T, finiteFourier]
    rw [this]
    exact zero_mem _
  | add f₁ f₂ h₁ h₂ ih₁ ih₂ =>
    have : T (f₁ + f₂) = T f₁ + T f₂ := by
      funext v
      exact congrFun (finiteFourier_add
        (integrable_of_mem_finiteSchwartzBruhat (slice_mem (hsub h₁) v))
        (integrable_of_mem_finiteSchwartzBruhat (slice_mem (hsub h₂) v))) _
    rw [this]
    exact add_mem ih₁ ih₂
  | smul c f _ ih =>
    have : T (c • f) = c • T f := by
      funext v
      simp only [T, finiteFourier, Pi.smul_apply, smul_eq_mul, mul_assoc]
      exact integral_const_mul _ _
    rw [this]
    exact Submodule.smul_mem _ c ih

end UpperTheory.ConvolutionTheory.R2.G.FiniteFourierHat

/- English proof (translation)
Introduce `F _ _ g hg`. Use `⟨fun v => integrable_of_mem_finiteSchwartzBruhat (FiniteFourierHat.slice_mem hg v), ?_⟩` and prove the remaining obligations. Establish `he : (fun v => ∫ s, g (Function.update v 1 s) * ((finiteAdelicChar F (-(s * v 1)) : Circle) : ℂ) ∂(finiteAdeleMeasure F)) = FiniteFourierHat.T g`. Use function extensionality and compare the values at `v`. Simplify using `only [FiniteFourierHat.T, finiteFourier, mul_neg]`.

Rewrite using `[he]`. Conclude with `FiniteFourierHat.T_mem hg`.
-/
theorem UpperTheory.ConvolutionTheory.R2.G.finHat :
    ∀ (F : Type) [Field F] [NumberField F], ∀ g ∈ finiteSchwartzBruhatPi F (ι := Fin 4), (∀ v, Integrable (fun s => g (Function.update v 1 s)) (finiteAdeleMeasure F)) ∧
    (fun v => ∫ s, g (Function.update v 1 s) * ((finiteAdelicChar F (-(s * v 1)) : Circle) : ℂ) ∂(finiteAdeleMeasure F)) ∈ finiteSchwartzBruhatPi F (ι := Fin 4) := by
  intro F _ _ g hg
  refine ⟨fun v => integrable_of_mem_finiteSchwartzBruhat (FiniteFourierHat.slice_mem hg v), ?_⟩
  have he : (fun v => ∫ s, g (Function.update v 1 s) * ((finiteAdelicChar F (-(s * v 1)) : Circle) : ℂ) ∂(finiteAdeleMeasure F)) = FiniteFourierHat.T g := by
    funext v
    simp only [FiniteFourierHat.T, finiteFourier, mul_neg]
  rw [he]
  exact FiniteFourierHat.T_mem hg
