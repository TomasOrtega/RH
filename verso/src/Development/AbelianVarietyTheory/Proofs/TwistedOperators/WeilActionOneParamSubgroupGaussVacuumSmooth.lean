import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairInfApply
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryArchimedeanLineOperatorsOneParameterStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OneParameterOperatorUniqueStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OneParameterWeilOperatorDerivativeStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousArchimedeanWeilOperatorLineTripleStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsComplexStructureGaussVacuumFockEquationsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaTriplePolynomialFockStableMulTraceLinearStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TracePairingArchimedeanVarsNondegenerateRightStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilOneParamMovesFockVacuumSmoothlyStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical

namespace GlobalTheory.GaussLine

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ a a' B G X om om' hT γ hγ T hTa f₀ hf₀`. Take `⟨h1, h0⟩` from `GlobalTheory.T.unitaryArchimedeanLine_operators_oneParameter B G X om om' hT γ hγ T hTa`. Establish `hU` using `GlobalTheory.T.one_parameter_operator_unique B G X om om' hT γ hγ T hTa Measure.addHaar inferInstance`. Take `⟨A, hAc, hAadd, hA0, hAint⟩` from `GlobalTheory.T.one_parameter_weil_operator_derivative B G X om om' hT γ hγ T hTa`. Establish `hC` using `GlobalTheory.T.continuous_archimedeanWeilOperator_line_triple B G X om om' hT γ hγ T hTa`.

Take `⟨J₀, hJ, hvac⟩` from `GlobalTheory.T.exists_complexStructure_gaussVacuum_fockEquations B G X om om' hT f₀ hf₀`. Use `haveI : BorelSpace (Fin a × Fin (a + a') → mixedEmbedding.mixedSpace F) := Pi.borelSpace`. Take `⟨hsm, n, qs, qs', cs, c, hd⟩` from `GlobalTheory.T.weilOneParam_moves_fockVacuum_smoothly (V := Fin a × Fin (a + a') → mixedEmbedding.mixedSpace F) Measure.addHaar (GlobalTheory.GaussLine.pairInf F (Fin a × Fin (a + a'))) (GlobalTheory.T.tracePairingArchimedeanVars_nondegenerate_right F _) T h1 h0 hU A hAc hAadd hA …`. Use `⟨hsm, ?_⟩` and prove the remaining obligations. Establish `hf₀P : f₀ ∈ G.M.Pol B.ψ B.emb` using `Submodule.mem_sInf.2 fun N hN => hN.1 f₀ hf₀`.

Establish `hmul` using `GlobalTheory.T.thetaTriple_polynomialFock_stable_mul_trace_linear B G X om om' hT`. Use `choose m hmP hmE using hmul`. Use `⟨(∑ i, cs i • m (qs i) (m (qs' i) f₀ hf₀P) (hmP _ _ _)) + c • f₀, add_mem (sum_mem fun i _ => Submodule.smul_mem _ _ (hmP _ _ _)) (Submodule.smul_mem _ _ hf₀P), fun x => ?_⟩` and prove the remaining obligations. Use `hd x using 1` and compare the differences between its conclusion and the goal. Simplify using `only [SchwartzMap.add_apply, SchwartzMap.sum_apply, SchwartzMap.smul_apply, smul_eq_mul, hmE]`.

Use `congr 1`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem smooth_vacuum_line : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {a a' : ℕ} (B : Base F E) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' → ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ G.W, ∀ T : ℝ → SInf F (Fin a × Fin (a + a')) →ₗ[ℂ] SInf F (Fin a × Fin (a + a')),
    (∀ (t : ℝ) (f : SInf F (Fin a × Fin (a + a'))), Acts (evI F) (om (1, γ (Multiplicative.ofAdd t))) f (T t f)) → ∀ f₀, G.M.IsGauss B.ψ B.emb f₀ →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × (Fin a × Fin (a + a') → mixedEmbedding.mixedSpace F) => T p.1 f₀ p.2) ∧ ∃ f' ∈ G.M.Pol B.ψ B.emb, ∀ x, HasDerivAt (fun t => T t f₀ x) (f' x) 0 := by
  intro F E _ _ _ _ _ σ a a' B G X om om' hT γ hγ T hTa f₀ hf₀
  obtain ⟨h1, h0⟩ := GlobalTheory.T.unitaryArchimedeanLine_operators_oneParameter B G X om om' hT γ hγ T hTa
  have hU := GlobalTheory.T.one_parameter_operator_unique B G X om om' hT γ hγ T hTa Measure.addHaar inferInstance
  obtain ⟨A, hAc, hAadd, hA0, hAint⟩ := GlobalTheory.T.one_parameter_weil_operator_derivative B G X om om' hT γ hγ T hTa
  have hC := GlobalTheory.T.continuous_archimedeanWeilOperator_line_triple B G X om om' hT γ hγ T hTa
  obtain ⟨J₀, hJ, hvac⟩ := GlobalTheory.T.exists_complexStructure_gaussVacuum_fockEquations B G X om om' hT f₀ hf₀
  haveI : BorelSpace (Fin a × Fin (a + a') → mixedEmbedding.mixedSpace F) := Pi.borelSpace
  obtain ⟨hsm, n, qs, qs', cs, c, hd⟩ := GlobalTheory.T.weilOneParam_moves_fockVacuum_smoothly (V := Fin a × Fin (a + a') → mixedEmbedding.mixedSpace F) Measure.addHaar (GlobalTheory.GaussLine.pairInf F (Fin a × Fin (a + a')))
    (GlobalTheory.T.tracePairingArchimedeanVars_nondegenerate_right F _) T h1 h0 hU A hAc hAadd hA0 hAint hC J₀ hJ f₀ hvac
  refine ⟨hsm, ?_⟩
  have hf₀P : f₀ ∈ G.M.Pol B.ψ B.emb := Submodule.mem_sInf.2 fun N hN => hN.1 f₀ hf₀
  have hmul := GlobalTheory.T.thetaTriple_polynomialFock_stable_mul_trace_linear B G X om om' hT
  choose m hmP hmE using hmul
  refine ⟨(∑ i, cs i • m (qs i) (m (qs' i) f₀ hf₀P) (hmP _ _ _)) + c • f₀,
    add_mem (sum_mem fun i _ => Submodule.smul_mem _ _ (hmP _ _ _)) (Submodule.smul_mem _ _ hf₀P), fun x => ?_⟩
  convert hd x using 1
  simp only [SchwartzMap.add_apply, SchwartzMap.sum_apply, SchwartzMap.smul_apply, smul_eq_mul, hmE]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

end GlobalTheory.GaussLine
