import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchurMultMultiplicitySpacesOfRapidDecayStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FubiniRightConvolutionBoundedContinuousStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RightConvEqSmulOfInnerTranslatesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MultTApplyRapidDec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TopStepVectorProperty
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteVolumeAdelicUnitaryQuotient
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealMeasureUniformInTupleOfThetaLiftScalar
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EvalTEquiv
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GinfCSecondCountable
import Formalism.LocalToGlobal.IndefiniteReal.EqZeroOfVec
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ValAct

/- English proof (translation)
Introduce `hP D θ hθ V S M J χ t ht w m hm α c hα hc`. Take `rfl` from `Formalism.IndefR.Eqv.eq_thetaC D hθ`. Take `⟨i1, i2, i3, i4, i5⟩` from `Formalism.IndefR.Eqv.ga_facts D V`. Take `⟨-, -, -, -, -, j6, j7, j8⟩` from `GlobalTheory.RealMeasOne.ginfC_facts V`. Use `haveI := hm`.

Use `haveI := Formalism.IndefR.Eqv.gQ_countable D V`. Establish `hT : PiTensorProduct.lift.symm t ∈ Mult (Formalism.IndefR.Eqv.thetaC D) M J χ` using `(mem_multT _ M J χ t).1 ht`. Establish `hTv : ∀ (v : M.Vec) g, (PiTensorProduct.lift.symm t) v g = t (PiTensorProduct.tprod ℂ v) g` using `fun v g => rfl`. Establish `hEq` using `Formalism.IndefR.AutomorphicEvaluation.eqCont_of_mem hT`. Take `⟨haut, hcusp, -⟩` from `GlobalTheory.ChainOnto.MultRapid.multT_apply_rapidDec hP D V S M _ hθ J χ t ht (PiTensorProduct.tprod ℂ w)`.

Take `⟨B, hB⟩` from `GlobalTheory.CuspDecay.bounded_of_cuspForm hP hθ haut hcusp`. Establish `hφc : Continuous (t (PiTensorProduct.tprod ℂ w))` using `GlobalTheory.BaseChain.multT_apply_continuous _ M J χ t ht _`. Establish `htr : ∀ (h : GinfC V) y, t (PiTensorProduct.tprod ℂ w) (y * h) = t (PiTensorProduct.tprod ℂ (Formalism.L2.SG.EvalTEquiv.transl M h w)) y` using `fun h y => by`. Use `Formalism.L2.SG.EvalTEquiv.equiv_ginf hθ hEq h.2 w y` as an intermediate fact. Rewrite `this` using `[hTv, hTv]`. Then use the resulting hypothesis.

Set `μ : Measure (GA D V)` to `Measure.haar`. Take `⟨𝓕, -, h𝓕⟩` from `Formalism.IndefR.Eqv.fundDomExists_holds D V`. Establish `hfd` using `h𝓕 μ`. Establish `hfin : μ 𝓕 < ⊤` using `GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol V μ 𝓕 inferInstance hfd`. Take `⟨κ, hκ⟩` from `GlobalTheory.T.schurMult_multiplicitySpaces_of_rapidDecay hP D _ hθ V S M J χ μ 𝓕 inferInstance hfd hθ inferInstance hfd _ hT _ hT`.

Establish `hS : ∀ v v' : M.Vec, ∫ g in 𝓕, star (t (PiTensorProduct.tprod ℂ v) g) * t (PiTensorProduct.tprod ℂ v') g ∂μ = κ * ∏ τ, ⟪(v τ : M.H τ), (v' τ : M.H τ)⟫_ℂ` using `fun v v' => by`. Use `(hκ v v').2` as an intermediate fact. Simplify using `only [hTv] at this`. Conclude with `this`. Establish `hcoef : ∀ (b : ∀ τ, M.H τ) (h : GinfC V), coefR (Formalism.IndefR.Eqv.thetaC D) M b (fun τ => w τ) h = ∏ τ, ⟪b τ, (Formalism.L2.SG.EvalTEquiv.transl M h w τ : M.H τ)⟫_ℂ` using `fun b h => by`.

Simplify using `only [coefR, Formalism.L2.SG.EvalTEquiv.transl_apply]`. Use `GlobalTheory.T.rightConv_eq_smul_of_inner_translates_eq (GQ V) μ 𝓕 hfd hfin m α hα _ hφc B hB (GlobalTheory.BaseChain.multT_apply_left _ M J χ t ht _) c fun h' => ?_` and prove the remaining obligations. Establish `hψc : Continuous fun x => star (t (PiTensorProduct.tprod ℂ w) (x * (h' : GA D V)))` using `(hφc.comp (continuous_id.mul continuous_const)).star`. Rewrite using `[(GlobalTheory.T.integral_fundamentalDomain_convolution_comm_of_bounded μ 𝓕 hfin m α hα _ _ hψc hφc B B (fun g => by rw [norm_star]; exact hB _) hB).2.2]`. Establish `e1 : ∀ h : GinfC V, ∫ x in 𝓕, star (t (PiTensorProduct.tprod ℂ w) (x * (h' : GA D V))) * t (PiTensorProduct.tprod ℂ w) (x * (h : GA D V)) ∂μ = κ * ∏ τ, ⟪(Formalism.L2.SG.EvalTEquiv.transl M h' w τ : M.H τ), (Formalism.L2.SG.EvalTEquiv.transl M h w τ : M.H τ)⟫_ℂ`.

Introduce `h`. Simplify using `only [htr]`. Conclude with `hS _ _`. Repeatedly rewrite using `[e1]`. Establish `e2 : ∫ x in 𝓕, star (t (PiTensorProduct.tprod ℂ w) (x * (h' : GA D V))) * t (PiTensorProduct.tprod ℂ w) x ∂μ = κ * ∏ τ, ⟪(Formalism.L2.SG.EvalTEquiv.transl M h' w τ : M.H τ), (w τ : M.H τ)⟫_ℂ`.

Simplify using `only [htr]`. Conclude with `hS _ _`. Rewrite using `[e2]`. Establish `e3` using `hc (fun τ => (Formalism.L2.SG.EvalTEquiv.transl M h' w τ : M.H τ))`. Simplify using `only [hcoef] at e3`.

Repeatedly rewrite using `[mul_left_comm _ κ]`. Rewrite using `[integral_const_mul, e3]`.
-/
theorem integral_mul_multT_eq : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ), ∀ t ∈ MultT θ M J χ, ∀ (w : M.Vec) (m : Measure (GinfC V)), m.IsHaarMeasure → ∀ (α : GinfC V → ℂ) (c : ℂ), Integrable α m → (∀ b : ∀ τ, M.H τ, ∫ h, α h * coefR θ M b (fun τ => w τ) h ∂m = c * ∏ τ, ⟪b τ, (w τ : M.H τ)⟫_ℂ) → ∀ x, ∫ h, α h * t (PiTensorProduct.tprod ℂ w) (x * h) ∂m = c * t (PiTensorProduct.tprod ℂ w) x := by
  intro hP D θ hθ V S M J χ t ht w m hm α c hα hc
  obtain rfl := Formalism.IndefR.Eqv.eq_thetaC D hθ
  obtain ⟨i1, i2, i3, i4, i5⟩ := Formalism.IndefR.Eqv.ga_facts D V
  obtain ⟨-, -, -, -, -, j6, j7, j8⟩ := GlobalTheory.RealMeasOne.ginfC_facts V
  haveI := hm
  haveI := Formalism.IndefR.Eqv.gQ_countable D V
  have hT : PiTensorProduct.lift.symm t ∈ Mult (Formalism.IndefR.Eqv.thetaC D) M J χ := (mem_multT _ M J χ t).1 ht
  have hTv : ∀ (v : M.Vec) g, (PiTensorProduct.lift.symm t) v g = t (PiTensorProduct.tprod ℂ v) g := fun v g => rfl
  have hEq := Formalism.IndefR.AutomorphicEvaluation.eqCont_of_mem hT
  obtain ⟨haut, hcusp, -⟩ := GlobalTheory.ChainOnto.MultRapid.multT_apply_rapidDec hP D V S M _ hθ J χ t ht (PiTensorProduct.tprod ℂ w)
  obtain ⟨B, hB⟩ := GlobalTheory.CuspDecay.bounded_of_cuspForm hP hθ haut hcusp
  have hφc : Continuous (t (PiTensorProduct.tprod ℂ w)) := GlobalTheory.BaseChain.multT_apply_continuous _ M J χ t ht _
  have htr : ∀ (h : GinfC V) y, t (PiTensorProduct.tprod ℂ w) (y * h) =
      t (PiTensorProduct.tprod ℂ (Formalism.L2.SG.EvalTEquiv.transl M h w)) y := fun h y => by
    have := Formalism.L2.SG.EvalTEquiv.equiv_ginf hθ hEq h.2 w y
    rwa [hTv, hTv] at this
  let μ : Measure (GA D V) := Measure.haar
  obtain ⟨𝓕, -, h𝓕⟩ := Formalism.IndefR.Eqv.fundDomExists_holds D V
  have hfd := h𝓕 μ
  have hfin : μ 𝓕 < ⊤ := GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol V μ 𝓕 inferInstance hfd
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.schurMult_multiplicitySpaces_of_rapidDecay hP D _ hθ V S M J χ μ 𝓕 inferInstance hfd hθ inferInstance hfd _ hT _ hT
  have hS : ∀ v v' : M.Vec, ∫ g in 𝓕, star (t (PiTensorProduct.tprod ℂ v) g) * t (PiTensorProduct.tprod ℂ v') g ∂μ =
      κ * ∏ τ, ⟪(v τ : M.H τ), (v' τ : M.H τ)⟫_ℂ := fun v v' => by
    have := (hκ v v').2
    simp only [hTv] at this
    exact this
  have hcoef : ∀ (b : ∀ τ, M.H τ) (h : GinfC V), coefR (Formalism.IndefR.Eqv.thetaC D) M b (fun τ => w τ) h =
      ∏ τ, ⟪b τ, (Formalism.L2.SG.EvalTEquiv.transl M h w τ : M.H τ)⟫_ℂ := fun b h => by
    simp only [coefR, Formalism.L2.SG.EvalTEquiv.transl_apply]
  refine GlobalTheory.T.rightConv_eq_smul_of_inner_translates_eq (GQ V) μ 𝓕 hfd hfin m α hα _ hφc B hB
    (GlobalTheory.BaseChain.multT_apply_left _ M J χ t ht _) c fun h' => ?_
  have hψc : Continuous fun x => star (t (PiTensorProduct.tprod ℂ w) (x * (h' : GA D V))) :=
    (hφc.comp (continuous_id.mul continuous_const)).star
  rw [(GlobalTheory.T.integral_fundamentalDomain_convolution_comm_of_bounded μ 𝓕 hfin m α hα _ _ hψc hφc B B (fun g => by rw [norm_star]; exact hB _) hB).2.2]
  have e1 : ∀ h : GinfC V, ∫ x in 𝓕, star (t (PiTensorProduct.tprod ℂ w) (x * (h' : GA D V))) *
      t (PiTensorProduct.tprod ℂ w) (x * (h : GA D V)) ∂μ =
      κ * ∏ τ, ⟪(Formalism.L2.SG.EvalTEquiv.transl M h' w τ : M.H τ), (Formalism.L2.SG.EvalTEquiv.transl M h w τ : M.H τ)⟫_ℂ := by
    intro h
    simp only [htr]
    exact hS _ _
  simp_rw [e1]
  have e2 : ∫ x in 𝓕, star (t (PiTensorProduct.tprod ℂ w) (x * (h' : GA D V))) * t (PiTensorProduct.tprod ℂ w) x ∂μ =
      κ * ∏ τ, ⟪(Formalism.L2.SG.EvalTEquiv.transl M h' w τ : M.H τ), (w τ : M.H τ)⟫_ℂ := by
    simp only [htr]
    exact hS _ _
  rw [e2]
  have e3 := hc (fun τ => (Formalism.L2.SG.EvalTEquiv.transl M h' w τ : M.H τ))
  simp only [hcoef] at e3
  simp_rw [mul_left_comm _ κ]
  rw [integral_const_mul, e3]

end GlobalTheory.ValAct

end
