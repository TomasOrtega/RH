import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.DatDatum
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LocEmb
import GroundTheory.GlobalFields.LocalFieldAtPlace

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C

/- English proof (translation)
Introduce `E _ _ n w`. Use `⟨fun g => ?_, ?_⟩` and prove the remaining obligations. Take `⟨-, h1, h2, -⟩` from `UpperTheory.ConvolutionTheory.Tf.locEmb E n w`. Establish `key : ∀ v, Matrix.GeneralLinearGroup.map (GlobalTheory.CuspRep.pLoc E v) (GlobalTheory.CuspRep.locGL E n w g) = Matrix.GeneralLinearGroup.map (GlobalTheory.CuspRep.pLoc E v) (AdelicGLn.localEmbedding w g)` using `fun v => by`. Distinguish the cases in `h : v = w`.

Substitute `h` using the available equality. Rewrite using `[GlobalTheory.CuspRep.pLoc_locGL]`. Conclude with `(h1 g).symm`. Rewrite using `[GlobalTheory.CuspRep.pLoc_locGL_of_ne h]`. Conclude with `(h2 v h g).symm`.

Use `Units.ext (Matrix.ext fun i j => ?_)` and prove the remaining obligations. Use `DFunLike.ext _ _ fun v => ?_` and prove the remaining obligations. Conclude with `congrArg (fun x : GL (Fin n) (v.adicCompletion E) => x.val i j) (key v)`. Establish `h : ∀ O : Subring (w.adicCompletion E), O = (ValuativeRel.valuation (w.adicCompletion E)).integer → Formalism.UG.GLint (Fin n) O = GLnLocal.integralGL (w.adicCompletion E) n`. Introduce and unpack `_ rfl`.

Both sides reduce to the same expression. Conclude with `h _ (Subring.ext fun x => (GroundTheory.Global.mem_valuationInteger_iff w x).symm)`.
-/
theorem UpperTheory.locGL_eq_localEmbedding_and_KGL_eq_integralGL :
    ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (w : HeightOneSpectrum (𝓞 E)),
          (∀ g, GlobalTheory.CuspRep.locGL E n w g = AdelicGLn.localEmbedding w g) ∧
          GlobalTheory.LFun.KGL w n = GLnLocal.integralGL (w.adicCompletion E) n := by
  intro E _ _ n w
  refine ⟨fun g => ?_, ?_⟩
  · obtain ⟨-, h1, h2, -⟩ := UpperTheory.ConvolutionTheory.Tf.locEmb E n w
    have key : ∀ v, Matrix.GeneralLinearGroup.map (GlobalTheory.CuspRep.pLoc E v) (GlobalTheory.CuspRep.locGL E n w g) =
        Matrix.GeneralLinearGroup.map (GlobalTheory.CuspRep.pLoc E v) (AdelicGLn.localEmbedding w g) := fun v => by
      by_cases h : v = w
      · subst h
        rw [GlobalTheory.CuspRep.pLoc_locGL]
        exact (h1 g).symm
      · rw [GlobalTheory.CuspRep.pLoc_locGL_of_ne h]
        exact (h2 v h g).symm
    refine Units.ext (Matrix.ext fun i j => ?_)
    refine DFunLike.ext _ _ fun v => ?_
    exact congrArg (fun x : GL (Fin n) (v.adicCompletion E) => x.val i j) (key v)
  · have h : ∀ O : Subring (w.adicCompletion E), O = (ValuativeRel.valuation (w.adicCompletion E)).integer →
        Formalism.UG.GLint (Fin n) O = GLnLocal.integralGL (w.adicCompletion E) n := by
      rintro _ rfl
      rfl
    exact h _ (Subring.ext fun x => (GroundTheory.Global.mem_valuationInteger_iff w x).symm)
