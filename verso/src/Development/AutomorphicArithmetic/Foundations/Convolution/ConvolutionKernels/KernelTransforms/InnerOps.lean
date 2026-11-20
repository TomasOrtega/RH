import Development.AutomorphicArithmetic.Foundations.Convolution.TensFun
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.HopBasic
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.CommPrj

open MeasureTheory NumberField IsDedekindDomain MvPolynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

/- English proof (translation)
Introduce `K _ _ n μ _`. Establish `hI : ∀ V : Submodule ℂ (LL μ), IsClosed (V : Set (LL μ)) → (rightRegularRep (rationalGLOne K n) μ).IsInvariant V → ∀ g, Commute (prj V) (rightRegularRep (rationalGLOne K n) μ g)`. Introduce `V hc hi g`. Establish `hi' : (rightRegularRep (rationalGLOne K n) μ).IsInvariant V.topologicalClosure`. Rewrite using `[hc.submodule_topologicalClosure_eq]`.

Conclude with `hi`. Conclude with `((UnitaryRep.isInvariant_iff_commute_starProjection V.topologicalClosure).mp hi' g).symm`. Establish `hF : ∀ V : Submodule ℂ (LL μ), IsClosed (V : Set (LL μ)) → (rightRegularRep (rationalGLOne K n) μ).IsInvariant V → ∀ h, Commute (prj V) (rhoF μ h)` using `fun V hc hi h => hI V hc hi _`. Use `⟨?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `ν _ β V hc hi`.

Establish `hT : prj V ∈ ((rightRegularRep (rationalGLOne K n) μ).compHom (archP K n) continuous_archP).intertwiners ((rightRegularRep (rationalGLOne K n) μ).compHom (archP K n) continuous_archP)` using `fun g v => congrArg (fun S : LL μ →L[ℂ] LL μ => S v) (hI V hc hi (archP K n g)).eq`. Conclude with `(UnitaryRep.comp_integrated_of_mem_intertwiners _ ν hT (UnitaryRep.ccToL1 ν β)).symm`. Introduce `m _ e V hc hi`. Establish `hT : prj V ∈ ((rightRegularRep (rationalGLOne K n) μ).compHom (MultiplicityOne.finProj K n) MultiplicityOne.continuous_finProj).intertwiners ((rightRegularRep (rationalGLOne K n) μ).compHom (MultiplicityOne.finProj K n) MultiplicityOne.continuous_finProj)` using `fun g v => congrArg (fun S : LL μ →L[ℂ] LL μ => S v) (hI V hc hi (MultiplicityOne.finProj K n g)).eq`. Conclude with `(UnitaryRep.comp_integrated_of_mem_intertwiners _ m hT (UnitaryRep.ccToL1 m e)).symm`.

Introduce `f V hc hi`. Establish `hT : prj V ∈ (rightRegularRep (rationalGLOne K n) μ).intertwiners (rightRegularRep (rationalGLOne K n) μ)` using `UnitaryRep.mem_intertwiners_self_iff.mpr (hI V hc hi)`. Conclude with `(UnitaryRep.comp_integrated_of_mem_intertwiners _ μ hT (UnitaryRep.ccToL1 μ f)).symm`. Introduce `h V hc hi`. Conclude with `(hF V hc hi h).eq.symm`.

Introduce `U V hc hi`. Conclude with `((UpperTheory.ConvolutionTheory.Tf.commPrj K n μ U).2.2.2.2.2.2.2.2 (prj V) fun u _ => hF V hc hi u).eq.symm`. Introduce `w J x ho hk V hc hi`. Conclude with `((UpperTheory.ConvolutionTheory.Tf.hopBasic K n μ w J x ho hk).2.2.2.2.1 (prj V) fun g => hF V hc hi _).eq.symm`.
-/
theorem UpperTheory.ConvolutionTheory.Tf.innerOps :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure],
      (∀ (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (β : TI K n), (∀ V : Submodule ℂ (LL μ), IsClosed (V : Set (LL μ)) → (rightRegularRep (rationalGLOne K n) μ).IsInvariant V → Oinf μ ν β ∘L prj V = prj V ∘L Oinf μ ν β)) ∧
      (∀ (m : Measure (AdelicGLn.FiniteAdelicGL K n)) [m.IsHaarMeasure] (e : TF K n), (∀ V : Submodule ℂ (LL μ), IsClosed (V : Set (LL μ)) → (rightRegularRep (rationalGLOne K n) μ).IsInvariant V → Ofin μ m e ∘L prj V = prj V ∘L Ofin μ m e)) ∧
      (∀ f : TG K n, (∀ V : Submodule ℂ (LL μ), IsClosed (V : Set (LL μ)) → (rightRegularRep (rationalGLOne K n) μ).IsInvariant V → RR μ f ∘L prj V = prj V ∘L RR μ f)) ∧
      (∀ h, (∀ V : Submodule ℂ (LL μ), IsClosed (V : Set (LL μ)) → (rightRegularRep (rationalGLOne K n) μ).IsInvariant V → rhoF μ h ∘L prj V = prj V ∘L rhoF μ h)) ∧ (∀ U, (∀ V : Submodule ℂ (LL μ), IsClosed (V : Set (LL μ)) → (rightRegularRep (rationalGLOne K n) μ).IsInvariant V → prj (fixF μ U) ∘L prj V = prj V ∘L prj (fixF μ U))) ∧
      ∀ (w : Pl K) (J : Subgroup (GL (Fin n) (w.adicCompletion K))) (x : GL (Fin n) (w.adicCompletion K)), IsOpen (J : Set (GL (Fin n) (w.adicCompletion K))) → IsCompact (J : Set (GL (Fin n) (w.adicCompletion K))) →
        (∀ V : Submodule ℂ (LL μ), IsClosed (V : Set (LL μ)) → (rightRegularRep (rationalGLOne K n) μ).IsInvariant V → Hop μ w J x ∘L prj V = prj V ∘L Hop μ w J x) := by
  intro K _ _ n μ _
  have hI : ∀ V : Submodule ℂ (LL μ), IsClosed (V : Set (LL μ)) →
      (rightRegularRep (rationalGLOne K n) μ).IsInvariant V →
      ∀ g, Commute (prj V) (rightRegularRep (rationalGLOne K n) μ g) := by
    intro V hc hi g
    have hi' : (rightRegularRep (rationalGLOne K n) μ).IsInvariant V.topologicalClosure := by
      rw [hc.submodule_topologicalClosure_eq]; exact hi
    exact ((UnitaryRep.isInvariant_iff_commute_starProjection V.topologicalClosure).mp hi' g).symm
  have hF : ∀ V : Submodule ℂ (LL μ), IsClosed (V : Set (LL μ)) →
      (rightRegularRep (rationalGLOne K n) μ).IsInvariant V → ∀ h, Commute (prj V) (rhoF μ h) :=
    fun V hc hi h => hI V hc hi _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ν _ β V hc hi
    have hT : prj V ∈ ((rightRegularRep (rationalGLOne K n) μ).compHom (archP K n) continuous_archP).intertwiners
        ((rightRegularRep (rationalGLOne K n) μ).compHom (archP K n) continuous_archP) :=
      fun g v => congrArg (fun S : LL μ →L[ℂ] LL μ => S v) (hI V hc hi (archP K n g)).eq
    exact (UnitaryRep.comp_integrated_of_mem_intertwiners _ ν hT (UnitaryRep.ccToL1 ν β)).symm
  · intro m _ e V hc hi
    have hT : prj V ∈ ((rightRegularRep (rationalGLOne K n) μ).compHom (MultiplicityOne.finProj K n)
          MultiplicityOne.continuous_finProj).intertwiners
        ((rightRegularRep (rationalGLOne K n) μ).compHom (MultiplicityOne.finProj K n)
          MultiplicityOne.continuous_finProj) :=
      fun g v => congrArg (fun S : LL μ →L[ℂ] LL μ => S v) (hI V hc hi (MultiplicityOne.finProj K n g)).eq
    exact (UnitaryRep.comp_integrated_of_mem_intertwiners _ m hT (UnitaryRep.ccToL1 m e)).symm
  · intro f V hc hi
    have hT : prj V ∈ (rightRegularRep (rationalGLOne K n) μ).intertwiners
        (rightRegularRep (rationalGLOne K n) μ) :=
      UnitaryRep.mem_intertwiners_self_iff.mpr (hI V hc hi)
    exact (UnitaryRep.comp_integrated_of_mem_intertwiners _ μ hT (UnitaryRep.ccToL1 μ f)).symm
  · intro h V hc hi
    exact (hF V hc hi h).eq.symm
  · intro U V hc hi
    exact ((UpperTheory.ConvolutionTheory.Tf.commPrj K n μ U).2.2.2.2.2.2.2.2 (prj V) fun u _ => hF V hc hi u).eq.symm
  · intro w J x ho hk V hc hi
    exact ((UpperTheory.ConvolutionTheory.Tf.hopBasic K n μ w J x ho hk).2.2.2.2.1 (prj V)
      fun g => hF V hc hi _).eq.symm
