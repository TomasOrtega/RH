import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultiplicityValuesContinuousBoundedHeckeConjStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SphericalOperatorEigenvaluesDeterminedByParamsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSatakeParametersBoundedEigenfunctionStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BcParamEqOfSatUEq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ChainParSucc
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.EisRegularAtOfEisPoleLE
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Introduce `hCRD D c hc j hj s hs u B hB`. Take `⟨hu0, hpar⟩` from `hB`. Establish `hex : ∃ v, PiLocalization₂.val u v ≠ 0`. Assume the negation of the conclusion as `h`. Use `push_neg at h`.

Apply `hu0` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `v`. Conclude with `h v`.

Take `⟨v, hv⟩` from `hex`. Use `set f : GA D s.V → ℂ := fun g => conj (PiLocalization₂.val u v g) with hfdef`. Establish `h3 : GlobalTheory.LFun.IsParamFunV s.V c.S f B` using `hpar v hv`. Take `⟨h4a, _⟩` from `GlobalTheory.T.multiplicity_values_continuous_bounded_hecke_conj hCRD D c hc j hj s hs`. Take `⟨hcont, ⟨C, hC⟩, hinv, hlev, _⟩` from `h4a u v`.

Establish `hsph : SphOff (s.J : Set (GA D s.V)) 1 c.S` using `hs.sph`. Establish `hfmem : f ∈ GlobalTheory.FinZeta.bddAut s.V`. Use `⟨(Complex.continuous_conj).comp hcont, fun γ hγ g => ?_, C, fun g => ?_⟩` and prove the remaining obligations. Simplify using `only [hfdef, hinv γ hγ g]`. Simplify `hC g` using `[hfdef]`.

Establish `hf0 : f ≠ 0`. Introduce `h0`. Apply `hv` to reduce the goal to its premises. Use function extensionality and compare the values at `g`. Use `congrFun h0 g` as an intermediate fact.

Simplify `this` using `[hfdef]`. Establish `hlev' : ∀ k ∈ (s.J : Set (GA D s.V)), ∀ g, f (g * k) = (1 : GA D s.V → ℂ) k * f g`. Introduce `k hk g`. Simplify using `only [hfdef, hlev k hk g, Pi.one_apply, one_mul]`. Take `⟨a, ha⟩` from `GlobalTheory.T.sphericalOperator_eigenvalues_determined_by_params D s.V (s.J : Set (GA D s.V)) 1 c.S hsph B`.

Take `⟨B', hB', hbd⟩` from `GlobalTheory.T.exists_satake_parameters_bounded_eigenfunction D s.V _ _ c.S hsph f hfmem hf0 hlev' a (fun P d R hR => ha f h3 P d R hR)`. Introduce `w hw`. Rewrite using `[GlobalTheory.LFun.IsParamVecOff.unique h3 hB' hw]`. Conclude with `hbd w hw`.
-/
theorem GlobalTheory.EvenOnto.parBound_of_rapidDecay : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, ParBound D := by
  intro hCRD D c hc j hj s hs u B hB
  obtain ⟨hu0, hpar⟩ := hB
  have hex : ∃ v, PiLocalization₂.val u v ≠ 0 := by
    by_contra h
    push_neg at h
    apply hu0
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    exact h v
  obtain ⟨v, hv⟩ := hex
  set f : GA D s.V → ℂ := fun g => conj (PiLocalization₂.val u v g) with hfdef
  have h3 : GlobalTheory.LFun.IsParamFunV s.V c.S f B := hpar v hv
  obtain ⟨h4a, _⟩ := GlobalTheory.T.multiplicity_values_continuous_bounded_hecke_conj hCRD D c hc j hj s hs
  obtain ⟨hcont, ⟨C, hC⟩, hinv, hlev, _⟩ := h4a u v
  have hsph : SphOff (s.J : Set (GA D s.V)) 1 c.S := hs.sph
  have hfmem : f ∈ GlobalTheory.FinZeta.bddAut s.V := by
    refine ⟨(Complex.continuous_conj).comp hcont, fun γ hγ g => ?_, C, fun g => ?_⟩
    · simp only [hfdef, hinv γ hγ g]
    · simpa [hfdef] using hC g
  have hf0 : f ≠ 0 := by
    intro h0
    apply hv
    funext g
    have := congrFun h0 g
    simpa [hfdef] using this
  have hlev' : ∀ k ∈ (s.J : Set (GA D s.V)), ∀ g, f (g * k) = (1 : GA D s.V → ℂ) k * f g := by
    intro k hk g
    simp only [hfdef, hlev k hk g, Pi.one_apply, one_mul]
  obtain ⟨a, ha⟩ := GlobalTheory.T.sphericalOperator_eigenvalues_determined_by_params D s.V (s.J : Set (GA D s.V)) 1 c.S hsph B
  obtain ⟨B', hB', hbd⟩ := GlobalTheory.T.exists_satake_parameters_bounded_eigenfunction D s.V _ _ c.S hsph f hfmem hf0 hlev' a (fun P d R hR => ha f h3 P d R hR)
  intro w hw
  rw [GlobalTheory.LFun.IsParamVecOff.unique h3 hB' hw]
  exact hbd w hw
