import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.OfinProd
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.FixLev
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.FinTens
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.RrTens
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.CompatEx
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.AvgTens

open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM UpperTheory.ConvolutionTheory.C
open scoped Classical

/- English proof (translation)
Introduce `K _ _ n hn μ _ ν _`. Take `⟨m, _, hC⟩` from `(UpperTheory.ConvolutionTheory.Tf.compatEx K n hn).2.1 μ ν`. Use `⟨m.real (AdelicGLn.integralFiniteGL K n : Set (AdelicGLn.FiniteAdelicGL K n)), ?_, ?_⟩` and prove the remaining obligations. Establish `ho` using `AdelicGLn.isOpen_integralFiniteGL K n`. Establish `hc` using `AdelicGLn.isCompact_integralFiniteGL K n`.

Conclude with `ENNReal.toReal_pos (ho.measure_pos m ⟨1, one_mem _⟩).ne' hc.measure_lt_top.ne`. Introduce `a r w _ _ mw f T g hw hm ht hoff hT hg`. Take `⟨e, he, -, hO⟩` from `UpperTheory.ConvolutionTheory.Tf.finTens K n μ m r w hw f ht hoff`. Establish `hge : g = tens a e`. Take `⟨h1, h2⟩` from `UpperTheory.ConvolutionTheory.Tf.avgTens K n hn a e (fun g => a (infPart K n g) * e (finPart K n g)) (fun _ => rfl)`.

Establish `hΦ : tensF (onInf a) f = fun g => a (infPart K n g) * e (finPart K n g)`. Use function extensionality and compare the values at `g`. Simplify using `only [tensF, onInf]`. Rewrite using `[h2 g, he (finPart K n g)]`. Use `congr 1`.

Use `DFunLike.ext _ _ fun x => ?_` and prove the remaining obligations. Rewrite using `[hg x, hΦ, h1 x]`. Establish `hUS : ∀ h, h ∈ levOn (Finset.univ.image w) (fun _ => (⊥ : Subgroup _)) ↔ h ∈ AdelicGLn.integralFiniteGL K n ∧ ∀ i, finAt (w i) (finEmb K n h) = 1`. Introduce `h`. Rewrite using `[AdelicGLn.mem_integralFiniteGL_iff_forall]`.

Express the relevant statement in the definitionally equal form `(∀ v, finAt v (finEmb K n h) ∈ if v ∈ Finset.univ.image w then (⊥ : Subgroup _) else GLnLocal.integralGL (v.adicCompletion K) n) ↔ _`. Prove the components needed by the constructor for the conclusion. Introduce `H`. Use `⟨fun v => ?_, fun i => ?_⟩` and prove the remaining obligations. Use `H v split_ifs at this with hv` as an intermediate fact.

Rewrite `this` using `[Subgroup.mem_bot]`. Express the relevant statement in the definitionally equal form `finAt v (finEmb K n h) ∈ _`. Rewrite using `[this]`. Conclude with `one_mem _`. Conclude with `this`.

Use `H (w i)` as an intermediate fact. Rewrite `this` using `[if_pos (by simp)]`. Conclude with `Subgroup.mem_bot.1 this`. Introduce and unpack `⟨H1, H2⟩ v split_ifs with hv`. Take `⟨i, -, rfl⟩` from `Finset.mem_image.1 hv`.

Conclude with `Subgroup.mem_bot.2 (H2 i)`. Conclude with `H1 v`. Establish `hfix : fixF μ (levOn (Finset.univ.image w) (fun _ => (⊥ : Subgroup _))) = sphOff μ (Finset.univ.image w)`. Rewrite using `[UpperTheory.ConvolutionTheory.C.fixLev K n μ (Finset.univ.image w) (fun _ => ⊥)]`. Establish `htop : ∀ v : Pl K, fixL μ v (⊥ : Subgroup (Gw n v)) = ⊤`.

Introduce `v`. Simplify using `[fixL, fixF, rhoF, Subgroup.map_bot]`. Both sides reduce to the same expression. Simplify using `[htop]`. Establish `hOf` using `hO mw (fun i => (hm i).1) (fun i => (hm i).2) T hT _ hUS`.

Rewrite `hOf` using `[hfix]`. Rewrite using `[hge, UpperTheory.ConvolutionTheory.Tf.rrTens K n hn μ ν m hC a e, hOf, ContinuousLinearMap.comp_smul]`.
-/
theorem UpperTheory.exists_pos_const_prod_localHeckeOperators :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), 0 < n → ∀ (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (ν : Measure (archGroup K n)) [ν.IsHaarMeasure],
      ∃ κ : ℝ, 0 < κ ∧ ∀ (a : TI K n) (r : ℕ) (w : Fin r → Pl K) [∀ i, MeasurableSpace (Gw n (w i))] [∀ i, BorelSpace (Gw n (w i))]
        (mw : ∀ i, Measure (Gw n (w i))) (f : ∀ v : Pl K, Gw n v → ℂ) (T : Fin r → LL μ →L[ℂ] LL μ) (g : TG K n),
        Function.Injective w → (∀ i, (mw i).IsHaarMeasure ∧ mw i (GLnLocal.integralGL ((w i).adicCompletion K) n) = 1) →
        (∀ i, Test (f (w i))) →
        (∀ v, v ∉ Set.range w → f v = (GLnLocal.integralGL (v.adicCompletion K) n : Set (Gw n v)).indicator 1) →
        (∀ i, IsOloc μ (w i) (mw i) (f (w i)) (T i)) → (∀ x, g x = PositivityTheory.Rg.Tf.Geo.avg (tensF (onInf a) f) x) →
        RR μ g = (κ : ℂ) • (Oinf μ ν a ∘L (List.ofFn T).prod ∘L prj (sphOff μ (Finset.univ.image w))) := by
  intro K _ _ n hn μ _ ν _
  obtain ⟨m, _, hC⟩ := (UpperTheory.ConvolutionTheory.Tf.compatEx K n hn).2.1 μ ν
  refine ⟨m.real (AdelicGLn.integralFiniteGL K n : Set (AdelicGLn.FiniteAdelicGL K n)), ?_, ?_⟩
  · have ho := AdelicGLn.isOpen_integralFiniteGL K n
    have hc := AdelicGLn.isCompact_integralFiniteGL K n
    exact ENNReal.toReal_pos (ho.measure_pos m ⟨1, one_mem _⟩).ne' hc.measure_lt_top.ne
  intro a r w _ _ mw f T g hw hm ht hoff hT hg
  obtain ⟨e, he, -, hO⟩ := UpperTheory.ConvolutionTheory.Tf.finTens K n μ m r w hw f ht hoff
  have hge : g = tens a e := by
    obtain ⟨h1, h2⟩ := UpperTheory.ConvolutionTheory.Tf.avgTens K n hn a e (fun g => a (infPart K n g) * e (finPart K n g)) (fun _ => rfl)
    have hΦ : tensF (onInf a) f = fun g => a (infPart K n g) * e (finPart K n g) := by
      funext g
      simp only [tensF, onInf]
      rw [h2 g, he (finPart K n g)]
      congr 1
    refine DFunLike.ext _ _ fun x => ?_
    rw [hg x, hΦ, h1 x]
  have hUS : ∀ h, h ∈ levOn (Finset.univ.image w) (fun _ => (⊥ : Subgroup _)) ↔
      h ∈ AdelicGLn.integralFiniteGL K n ∧ ∀ i, finAt (w i) (finEmb K n h) = 1 := by
    intro h
    rw [AdelicGLn.mem_integralFiniteGL_iff_forall]
    change (∀ v, finAt v (finEmb K n h) ∈ if v ∈ Finset.univ.image w then (⊥ : Subgroup _)
      else GLnLocal.integralGL (v.adicCompletion K) n) ↔ _
    constructor
    · intro H
      refine ⟨fun v => ?_, fun i => ?_⟩
      · have := H v
        split_ifs at this with hv
        · rw [Subgroup.mem_bot] at this
          change finAt v (finEmb K n h) ∈ _
          rw [this]
          exact one_mem _
        · exact this
      · have := H (w i)
        rw [if_pos (by simp)] at this
        exact Subgroup.mem_bot.1 this
    · rintro ⟨H1, H2⟩ v
      split_ifs with hv
      · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hv
        exact Subgroup.mem_bot.2 (H2 i)
      · exact H1 v
  have hfix : fixF μ (levOn (Finset.univ.image w) (fun _ => (⊥ : Subgroup _))) = sphOff μ (Finset.univ.image w) := by
    rw [UpperTheory.ConvolutionTheory.C.fixLev K n μ (Finset.univ.image w) (fun _ => ⊥)]
    have htop : ∀ v : Pl K, fixL μ v (⊥ : Subgroup (Gw n v)) = ⊤ := by
      intro v
      simp [fixL, fixF, rhoF, Subgroup.map_bot]
      rfl
    simp [htop]
  have hOf := hO mw (fun i => (hm i).1) (fun i => (hm i).2) T hT _ hUS
  rw [hfix] at hOf
  rw [hge, UpperTheory.ConvolutionTheory.Tf.rrTens K n hn μ ν m hC a e, hOf, ContinuousLinearMap.comp_smul]
