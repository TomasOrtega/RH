import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.OfinProd
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.OpBasics
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.FixLev
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.RrTens
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.CompatEx
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.PrjFix

open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM UpperTheory.ConvolutionTheory.C

/- English proof (translation)
Establish `h : f ∈ V.topologicalClosure` using `V.le_topologicalClosure hf`. Conclude with `(Submodule.starProjection_eq_self_iff).2 h`.
-/
private theorem prj_self {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (V : Submodule ℂ H) {f : H} (hf : f ∈ V) : prj V f = f := by
  have h : f ∈ V.topologicalClosure := V.le_topologicalClosure hf
  exact (Submodule.starProjection_eq_self_iff).2 h

/- English proof (translation)
Use `show (AdelicGLn.finiteRestrictedEquiv K n (AdelicGLn.prodEquiv K n (finEmb K n y)).2) v = _`. Rewrite using `[prodEquiv_finEmb]`.
-/
private theorem comp_eq {K : Type} [Field K] [NumberField K] {n : ℕ} (v : Pl K)
    (y : AdelicGLn.FiniteAdelicGL K n) :
    finAt v (finEmb K n y) = AdelicGLn.finiteRestrictedEquiv K n y v := by
  show (AdelicGLn.finiteRestrictedEquiv K n (AdelicGLn.prodEquiv K n (finEmb K n y)).2) v = _
  rw [prodEquiv_finEmb]

open scoped Classical in

/- English proof (translation)
Use extensionality with `h`. Simplify using `only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]`. Prove the components needed by the constructor for the conclusion. Introduce `hh`. Establish `hh' : ∀ v, finAt v (finEmb K n h) ∈ (if v ∈ P then U v ⊓ GLnLocal.integralGL (v.adicCompletion K) n else GLnLocal.integralGL (v.adicCompletion K) n)` using `hh`.

Use `⟨(AdelicGLn.mem_integralFiniteGL_iff_forall K n).2 fun v => ?_, fun v hv => ?_⟩` and prove the remaining obligations. Rewrite using `[← comp_eq]`. Use `hh' v` as an intermediate fact. Use `split_ifs at this`. Conclude with `this.2`.

Conclude with `this`. Use `hh' v` as an intermediate fact. Rewrite `this` using `[if_pos hv]`. Conclude with `this.1`. Introduce and unpack `⟨h1, h2⟩`.

Establish `h1'` using `(AdelicGLn.mem_integralFiniteGL_iff_forall K n).1 h1`. Use `show ∀ v, finAt v (finEmb K n h) ∈ (if v ∈ P then U v ⊓ GLnLocal.integralGL (v.adicCompletion K) n else GLnLocal.integralGL (v.adicCompletion K) n)`. Introduce `v`. Establish `h3` using `h1' v`. Rewrite `h3` using `[← comp_eq]`.

Use `split_ifs with hv`. Conclude with `⟨h2 v hv, h3⟩`. Conclude with `h3`.
-/
private theorem levOn_inter {K : Type} [Field K] [NumberField K] {n : ℕ} (P : Finset (Pl K))
    (U : ∀ v : Pl K, Subgroup (Gw n v)) :
    (levOn P (fun v => U v ⊓ GLnLocal.integralGL (v.adicCompletion K) n) :
        Set (AdelicGLn.FiniteAdelicGL K n)) =
      (AdelicGLn.integralFiniteGL K n : Set (AdelicGLn.FiniteAdelicGL K n)) ∩
        ⋂ v ∈ P, (fun h : AdelicGLn.FiniteAdelicGL K n => finAt v (finEmb K n h)) ⁻¹' (U v : Set (Gw n v)) := by
  ext h
  simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
  constructor
  · intro hh
    have hh' : ∀ v, finAt v (finEmb K n h) ∈ (if v ∈ P then U v ⊓ GLnLocal.integralGL (v.adicCompletion K) n
        else GLnLocal.integralGL (v.adicCompletion K) n) := hh
    refine ⟨(AdelicGLn.mem_integralFiniteGL_iff_forall K n).2 fun v => ?_, fun v hv => ?_⟩
    · rw [← comp_eq]
      have := hh' v
      split_ifs at this
      · exact this.2
      · exact this
    · have := hh' v
      rw [if_pos hv] at this
      exact this.1
  · rintro ⟨h1, h2⟩
    have h1' := (AdelicGLn.mem_integralFiniteGL_iff_forall K n).1 h1
    show ∀ v, finAt v (finEmb K n h) ∈ (if v ∈ P then U v ⊓ GLnLocal.integralGL (v.adicCompletion K) n
        else GLnLocal.integralGL (v.adicCompletion K) n)
    intro v
    have h3 := h1' v
    rw [← comp_eq] at h3
    split_ifs with hv
    · exact ⟨h2 v hv, h3⟩
    · exact h3

/- English proof (translation)
Introduce `f hf`. Simplify using `only [fixL, fixF, Submodule.mem_iInf] at hf ⊢`. Conclude with `fun u hu => hf u (Subgroup.map_mono h hu)`.
-/
private theorem fixL_anti {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL K n))
    [μ.IsHaarMeasure] (v : Pl K) {J J' : Subgroup (Gw n v)} (h : J' ≤ J) : fixL μ v J ≤ fixL μ v J' := by
  intro f hf
  simp only [fixL, fixF, Submodule.mem_iInf] at hf ⊢
  exact fun u hu => hf u (Subgroup.map_mono h hu)

/- English proof (translation)
Use `haveI := ContinuousLinearMap.finite_dimensional_eigenspace hT c hc`. Use `Submodule.finiteDimensional_of_le (S₂ := Module.End.eigenspace (T ∘L prj W).toLinearMap c) ?_` and prove the remaining obligations. Introduce `f hf`. Take `⟨h1, h2⟩` from `h f hf`. Rewrite using `[Module.End.mem_eigenspace_iff]`.

Use `show T (prj W f) = c • f`. Rewrite using `[prj_self W h1, h2]`.
-/
private theorem fin_of_compact {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (W E : Submodule ℂ H) (T : H →L[ℂ] H) {c : ℂ} (hc : c ≠ 0) (hT : IsCompactOperator (T ∘L prj W))
    (h : ∀ f ∈ E, f ∈ W ∧ T f = c • f) : FiniteDimensional ℂ E := by
  haveI := ContinuousLinearMap.finite_dimensional_eigenspace hT c hc
  refine Submodule.finiteDimensional_of_le (S₂ := Module.End.eigenspace (T ∘L prj W).toLinearMap c) ?_
  intro f hf
  obtain ⟨h1, h2⟩ := h f hf
  rw [Module.End.mem_eigenspace_iff]
  show T (prj W f) = c • f
  rw [prj_self W h1, h2]

set_option maxHeartbeats 2000000 in
/- English proof (translation)
Introduce `K _ _ n hn μ _ ν _ a x hx P U hU`. Take `⟨m, _, hC⟩` from `(UpperTheory.ConvolutionTheory.Tf.compatEx K n hn).2.1 μ ν`. Set `U' : ∀ v : Pl K, Subgroup (Gw n v)` to `fun v => U v ⊓ GLnLocal.integralGL (v.adicCompletion K) n`. Establish `hcomp : ∀ v : Pl K, Continuous fun h : AdelicGLn.FiniteAdelicGL K n => finAt v (finEmb K n h)` using `fun v => (continuous_finAt v).comp continuous_finEmb`. Establish `hO : IsOpen (levOn P U' : Set (AdelicGLn.FiniteAdelicGL K n))`.

Rewrite using `[levOn_inter]`. Conclude with `(AdelicGLn.isOpen_integralFiniteGL K n).inter (P.finite_toSet.isOpen_biInter fun v hv => (hU v hv).2.preimage (hcomp v))`. Establish `hK : IsCompact (levOn P U' : Set (AdelicGLn.FiniteAdelicGL K n))`. Rewrite using `[levOn_inter]`. Use `(AdelicGLn.isCompact_integralFiniteGL K n).inter_right (isClosed_biInter fun v hv => ?_)` and prove the remaining obligations.

Conclude with `(Subgroup.isClosed_of_isOpen (U v) (hU v hv).2).preimage (hcomp v)`. Take `⟨e, -, he⟩` from `UpperTheory.ConvolutionTheory.Tf.prjFix K n μ m (levOn P U') hO hK`. Establish `hfix` using `UpperTheory.ConvolutionTheory.C.fixLev K n μ P U'`. Establish `hB` using `(UpperTheory.ConvolutionTheory.C.opBasics K n μ (tens a e)).2.2`. Establish `hx' : (x : ℂ) ≠ 0` using `by exact_mod_cast hx`.

Use `fin_of_compact (cuspidalL2 μ) _ (RR μ (tens a e)) hx' hB fun f hf => ?_` and prove the remaining obligations. Rewrite `hf` using `[Submodule.mem_inf, Submodule.mem_inf]`. Take `⟨⟨he1, hs⟩, hl⟩` from `hf`. Take `⟨hc, he2⟩` from `Submodule.mem_inf.1 he1`. Establish `hfF : f ∈ fixF μ (levOn P U')`.

Rewrite using `[hfix, Submodule.mem_inf]`. Use `⟨hs, ?_⟩` and prove the remaining obligations. Simplify using `only [Submodule.mem_iInf] at hl ⊢`. Conclude with `fun v hv => fixL_anti μ v inf_le_left (hl v hv)`. Establish `h1 : Ofin μ m e f = f` using `by rw [he]; exact prj_self _ hfF`.

Establish `h2 : Oinf μ ν a f = (x : ℂ) • f` using `Module.End.mem_eigenspace_iff.1 he2`. Use `⟨hc, ?_⟩` and prove the remaining obligations. Rewrite using `[UpperTheory.ConvolutionTheory.Tf.rrTens K n hn μ ν m hC a e, ContinuousLinearMap.comp_apply, h1, h2]`.
-/
theorem UpperTheory.ConvolutionTheory.C.eigAdm :
    UpperTheory.ConvolutionTheory.C.EigAdm := by
  intro K _ _ n hn μ _ ν _ a x hx P U hU
  obtain ⟨m, _, hC⟩ := (UpperTheory.ConvolutionTheory.Tf.compatEx K n hn).2.1 μ ν
  let U' : ∀ v : Pl K, Subgroup (Gw n v) := fun v => U v ⊓ GLnLocal.integralGL (v.adicCompletion K) n
  have hcomp : ∀ v : Pl K, Continuous fun h : AdelicGLn.FiniteAdelicGL K n => finAt v (finEmb K n h) :=
    fun v => (continuous_finAt v).comp continuous_finEmb
  have hO : IsOpen (levOn P U' : Set (AdelicGLn.FiniteAdelicGL K n)) := by
    rw [levOn_inter]
    exact (AdelicGLn.isOpen_integralFiniteGL K n).inter
      (P.finite_toSet.isOpen_biInter fun v hv => (hU v hv).2.preimage (hcomp v))
  have hK : IsCompact (levOn P U' : Set (AdelicGLn.FiniteAdelicGL K n)) := by
    rw [levOn_inter]
    refine (AdelicGLn.isCompact_integralFiniteGL K n).inter_right
      (isClosed_biInter fun v hv => ?_)
    exact (Subgroup.isClosed_of_isOpen (U v) (hU v hv).2).preimage (hcomp v)
  obtain ⟨e, -, he⟩ := UpperTheory.ConvolutionTheory.Tf.prjFix K n μ m (levOn P U') hO hK
  have hfix := UpperTheory.ConvolutionTheory.C.fixLev K n μ P U'
  have hB := (UpperTheory.ConvolutionTheory.C.opBasics K n μ (tens a e)).2.2
  have hx' : (x : ℂ) ≠ 0 := by exact_mod_cast hx
  refine fin_of_compact (cuspidalL2 μ) _ (RR μ (tens a e)) hx' hB fun f hf => ?_
  rw [Submodule.mem_inf, Submodule.mem_inf] at hf
  obtain ⟨⟨he1, hs⟩, hl⟩ := hf
  obtain ⟨hc, he2⟩ := Submodule.mem_inf.1 he1
  have hfF : f ∈ fixF μ (levOn P U') := by
    rw [hfix, Submodule.mem_inf]
    refine ⟨hs, ?_⟩
    simp only [Submodule.mem_iInf] at hl ⊢
    exact fun v hv => fixL_anti μ v inf_le_left (hl v hv)
  have h1 : Ofin μ m e f = f := by rw [he]; exact prj_self _ hfF
  have h2 : Oinf μ ν a f = (x : ℂ) • f := Module.End.mem_eigenspace_iff.1 he2
  refine ⟨hc, ?_⟩
  rw [UpperTheory.ConvolutionTheory.Tf.rrTens K n hn μ ν m hC a e, ContinuousLinearMap.comp_apply, h1, h2]
