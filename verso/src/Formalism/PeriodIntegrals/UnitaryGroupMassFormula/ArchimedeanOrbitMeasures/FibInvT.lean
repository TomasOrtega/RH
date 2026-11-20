import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.FibInv

noncomputable section

namespace PI.AprimeInfW

open scoped TensorProduct
open MeasureTheory NumberField Topology Set Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.TypedSets
  Formalism.L2.SG.Sub Matrix

/- English proof (translation)
Use `haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X`. Establish `hm : Measurable (fun y : TupI X => g • y)` using `measurable_smul_tupI X g`. Establish `hinv : ∀ b : HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS), (fun y : TupI X => g • y) ⁻¹' ((gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) ⁻¹' {(b : Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS)) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E))} ∩ IndI X) = (gramR (Ainf X …`. Introduce `b`. Use extensionality with `y`.

Simplify using `only [mem_preimage, mem_inter_iff, mem_singleton_iff, gramR_smulI, indI_smul_iff]`. Establish `hmeasA : ∀ b : HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS), MeasurableSet ((gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) ⁻¹' {(b : Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS)) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E))} ∩ IndI X)` using `fun b => (isClosed_singleton.preimage (continuous_gramRP (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J)).measurableSet.inter (isOpen_IndI X).measurableSet`. Establish `hU' : (fun y : TupI X => g • y) ⁻¹' IndI X = IndI X`. Use extensionality with `y`. Conclude with `indI_smul_iff X g y`.

Use `⟨fun b => ?_, fun φ hφ => ?_, fun φ hc hs hU => ?_⟩` and prove the remaining obligations. Rewrite using `[Measure.map_apply hm (hmeasA b).compl, preimage_compl, hinv b]`. Conclude with `hfib.1 b`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[setLIntegral_map (isOpen_IndI X).measurableSet hφ hm, hU']`.

Use `_ = ∫⁻ b, ∫⁻ v, φ (g • v) ∂(fibInf b) ∂νinf := hfib.2.1 _ (hφ.comp hm)`. Use `_ = ∫⁻ b, ∫⁻ v, φ v ∂((fibInf b).map (fun y => g • y)) ∂νinf := by`. Use `congr 1`. Use function extensionality and compare the values at `b`. Rewrite using `[lintegral_map hφ hm]`.

Establish `hc' : Continuous (fun v => φ (g • v))` using `hc.comp (continuous_smul_tupI X g)`. Establish `hs' : HasCompactSupport (fun v => φ (g • v))` using `hs.comp_homeomorph (smulH X g)`. Establish `hU2 : tsupport (fun v => φ (g • v)) ⊆ IndI X`. Rewrite using `[show (fun v => φ (g • v)) = φ ∘ smulH X g from rfl, tsupport_comp_eq_preimage]`. Introduce `y hy`.

Conclude with `(indI_smul_iff X g y).1 (hU hy)`. Take `⟨hI, hC⟩` from `hfib.2.2 _ hc' hs' hU2`. Use `⟨fun b hb => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[integrable_map_measure hc.aestronglyMeasurable hm.aemeasurable]`. Conclude with `hI b hb`.

Establish `e : (fun b => ∫ v, φ v ∂((fibInf b).map (fun y => g • y))) = fun b => ∫ v, φ (g • v) ∂(fibInf b)`. Use function extensionality and compare the values at `b`. Rewrite using `[integral_map hm.aemeasurable hc.aestronglyMeasurable]`. Rewrite using `[e]`. Conclude with `hC`.
-/
theorem fibTrans {D : D7} (X : HidaSetting D) (μinf : Measure (TupI X)) (νinf : Measure (HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS)))
    (fibInf : HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS) → Measure (TupI X))
    (hfib : IsFibreFamily μinf (gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) Subtype.val (IndI X) νinf Set.univ fibInf)
    (g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (hS : μinf.map (fun y => g • y) = μinf) :
    IsFibreFamily μinf (gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) Subtype.val (IndI X) νinf Set.univ
      (fun b => (fibInf b).map (fun y => g • y)) := by
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  have hm : Measurable (fun y : TupI X => g • y) := measurable_smul_tupI X g
  have hinv : ∀ b : HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS), (fun y : TupI X => g • y) ⁻¹' ((gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) ⁻¹' {(b : Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS)) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E))} ∩ IndI X) =
      (gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) ⁻¹' {(b : Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS)) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E))} ∩ IndI X := by
    intro b; ext y
    simp only [mem_preimage, mem_inter_iff, mem_singleton_iff, gramR_smulI, indI_smul_iff]
  have hmeasA : ∀ b : HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS), MeasurableSet ((gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) ⁻¹' {(b : Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS)) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E))} ∩ IndI X) := fun b =>
    (isClosed_singleton.preimage (continuous_gramRP (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J)).measurableSet.inter
      (isOpen_IndI X).measurableSet
  have hU' : (fun y : TupI X => g • y) ⁻¹' IndI X = IndI X := by
    ext y; exact indI_smul_iff X g y
  refine ⟨fun b => ?_, fun φ hφ => ?_, fun φ hc hs hU => ?_⟩
  · rw [Measure.map_apply hm (hmeasA b).compl, preimage_compl, hinv b]
    exact hfib.1 b
  · calc ∫⁻ v in IndI X, φ v ∂μinf = ∫⁻ v in IndI X, φ v ∂(μinf.map (fun y => g • y)) := by rw [hS]
      _ = ∫⁻ v in IndI X, φ (g • v) ∂μinf := by
          rw [setLIntegral_map (isOpen_IndI X).measurableSet hφ hm, hU']
      _ = ∫⁻ b, ∫⁻ v, φ (g • v) ∂(fibInf b) ∂νinf := hfib.2.1 _ (hφ.comp hm)
      _ = ∫⁻ b, ∫⁻ v, φ v ∂((fibInf b).map (fun y => g • y)) ∂νinf := by
          congr 1; funext b; rw [lintegral_map hφ hm]
  · have hc' : Continuous (fun v => φ (g • v)) := hc.comp (continuous_smul_tupI X g)
    have hs' : HasCompactSupport (fun v => φ (g • v)) := hs.comp_homeomorph (smulH X g)
    have hU2 : tsupport (fun v => φ (g • v)) ⊆ IndI X := by
      rw [show (fun v => φ (g • v)) = φ ∘ smulH X g from rfl, tsupport_comp_eq_preimage]
      intro y hy
      exact (indI_smul_iff X g y).1 (hU hy)
    obtain ⟨hI, hC⟩ := hfib.2.2 _ hc' hs' hU2
    refine ⟨fun b hb => ?_, ?_⟩
    · rw [integrable_map_measure hc.aestronglyMeasurable hm.aemeasurable]
      exact hI b hb
    · have e : (fun b => ∫ v, φ v ∂((fibInf b).map (fun y => g • y))) =
          fun b => ∫ v, φ (g • v) ∂(fibInf b) := by
        funext b; rw [integral_map hm.aemeasurable hc.aestronglyMeasurable]
      rw [e]
      exact hC

/- English proof (translation)
Use `haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X`. Use `haveI := hμ.1`. Use `haveI := hν.1`. Use `haveI : BorelSpace (HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS)) := ⟨rfl⟩`. Use `haveI : LocallyCompactSpace (Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS)) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) := inferInstanceAs (LocallyCompactSpace (Fin (D.R.rS + 1 + D.R.rS) → Fin (D.R.rS + 1 + D.R.rS) → Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E))`.

Use `haveI : LocallyCompactSpace (HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS)) := (isClosed_HermRP (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS)).isClosedEmbedding_subtypeVal.locallyCompactSpace`. Conclude with `FU.fib_eq h1 h2 (continuous_gramHI X) (fun _ => rfl) Subtype.val_injective (isOpen_IndI X)`.
-/
theorem fibEqI {D : D7} (X : HidaSetting D) (ψ : AddChar (AF X.B.I.F) ℂ) (μinf : Measure (TupI X))
    (νinf : Measure (HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS))) (fib1 fib2 : HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS) → Measure (TupI X))
    (hμ : SdW X.B.I.F X.B.I.E X.B.I.cm.sig X.B.I.n X.B.I.J (Ainf X.B.I.F) (psiInf X.B.I.F ψ) (D.R.rS + 1 + D.R.rS) μinf)
    (hν : SdHerm X.B.I.F X.B.I.E X.B.I.cm.sig (Ainf X.B.I.F) (psiInf X.B.I.F ψ) (D.R.rS + 1 + D.R.rS) νinf)
    (h1 : IsFibreFamily μinf (gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) Subtype.val (IndI X) νinf Set.univ fib1)
    (h2 : IsFibreFamily μinf (gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) Subtype.val (IndI X) νinf Set.univ fib2) : fib1 = fib2 := by
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  haveI := hμ.1
  haveI := hν.1
  haveI : BorelSpace (HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS)) := ⟨rfl⟩
  haveI : LocallyCompactSpace (Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS)) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin (D.R.rS + 1 + D.R.rS) → Fin (D.R.rS + 1 + D.R.rS) →
      Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E))
  haveI : LocallyCompactSpace (HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS)) :=
    (isClosed_HermRP (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS)).isClosedEmbedding_subtypeVal.locallyCompactSpace
  exact FU.fib_eq h1 h2 (continuous_gramHI X) (fun _ => rfl) Subtype.val_injective (isOpen_IndI X)

/- English proof (translation)
Introduce `D X u' ψ hT μinf νinf fibInf hP g`. Establish `hfib` using `hP.2.2.2.2.2.2`. Establish `h` using `fibEqI X ψ μinf νinf _ _ hP.2.2.2.2.1 hP.2.2.2.2.2.1 (fibTrans X μinf νinf fibInf hfib g (hS X u' ψ hT μinf νinf fibInf hP g)) hfib`. Conclude with `congrFun h (TI X u' hT)`.
-/
theorem invFib_of (hS : SdInvG) : InvFib := by
  intro D X u' ψ hT μinf νinf fibInf hP g
  have hfib := hP.2.2.2.2.2.2
  have h := fibEqI X ψ μinf νinf _ _ hP.2.2.2.2.1 hP.2.2.2.2.2.1
    (fibTrans X μinf νinf fibInf hfib g (hS X u' ψ hT μinf νinf fibInf hP g)) hfib
  exact congrFun h (TI X u' hT)

end PI.AprimeInfW
