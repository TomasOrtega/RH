import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.ThInf

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.TA
open UpperTheory.ConvolutionTheory.R2.G (FS2 nE)
open scoped Classical

/- English proof (translation)
Introduce `x`. Establish `hu : Nonempty (InfinitePlace ℚ)` using `inferInstance`. Take `⟨w⟩` from `hu`. Establish `huniq : ∀ v : InfinitePlace ℚ, v = w` using `fun v => Subsingleton.elim v w`. Establish `hreal : InfinitePlace.IsReal w` using `IsTotallyReal.isReal w`.

Establish `h : adelicChar ℚ (TR.sInf ℚ fun _ => x) = Real.fourierChar (-x)`. Establish `e : TR.sInf ℚ (fun _ => x) = infiniteAdeleInl (TR.infEq ℚ fun _ => x)` using `rfl`. Rewrite using `[e, adelicChar_infiniteAdeleInl, Fintype.prod_eq_single w (fun v hv => absurd (huniq v) hv)]`. Rewrite using `[infiniteAdelicChar_apply_of_isReal hreal]`. Establish `e2 : InfinitePlace.Completion.extensionEmbeddingOfIsReal hreal (TR.infEq ℚ (fun _ => x) w) = x` using `(InfinitePlace.Completion.ringEquivRealOfIsReal hreal).apply_symm_apply x`.

Rewrite using `[e2]`. Establish `h2 : adelicChar ℚ (-(TR.sInf ℚ fun _ => x)) = Real.fourierChar x`. Rewrite using `[AddChar.map_neg_eq_inv, h, AddChar.map_neg_eq_inv, inv_inv]`. Establish `h3 : ψ (-(TR.sInf ℚ fun _ => x)) = ((adelicChar ℚ (-(TR.sInf ℚ fun _ => x)) : Circle) : ℂ)` using `rfl`. Rewrite using `[h3, h2, Real.fourierChar_apply]`.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.standardAddChar_neg_archimedean_rat :
    ∀ x : ℝ, ψ (-(TR.sInf ℚ fun _ => x)) = Complex.exp (2 * Real.pi * Complex.I * x) := by
  intro x
  have hu : Nonempty (InfinitePlace ℚ) := inferInstance
  obtain ⟨w⟩ := hu
  have huniq : ∀ v : InfinitePlace ℚ, v = w := fun v => Subsingleton.elim v w
  have hreal : InfinitePlace.IsReal w := IsTotallyReal.isReal w
  have h : adelicChar ℚ (TR.sInf ℚ fun _ => x) = Real.fourierChar (-x) := by
    have e : TR.sInf ℚ (fun _ => x) = infiniteAdeleInl (TR.infEq ℚ fun _ => x) := rfl
    rw [e, adelicChar_infiniteAdeleInl, Fintype.prod_eq_single w (fun v hv => absurd (huniq v) hv)]
    rw [infiniteAdelicChar_apply_of_isReal hreal]
    have e2 : InfinitePlace.Completion.extensionEmbeddingOfIsReal hreal (TR.infEq ℚ (fun _ => x) w) = x :=
      (InfinitePlace.Completion.ringEquivRealOfIsReal hreal).apply_symm_apply x
    rw [e2]
  have h2 : adelicChar ℚ (-(TR.sInf ℚ fun _ => x)) = Real.fourierChar x := by
    rw [AddChar.map_neg_eq_inv, h, AddChar.map_neg_eq_inv, inv_inv]
  have h3 : ψ (-(TR.sInf ℚ fun _ => x)) = ((adelicChar ℚ (-(TR.sInf ℚ fun _ => x)) : Circle) : ℂ) := rfl
  rw [h3, h2, Real.fourierChar_apply]
  congr 1
  push_cast
  ring
