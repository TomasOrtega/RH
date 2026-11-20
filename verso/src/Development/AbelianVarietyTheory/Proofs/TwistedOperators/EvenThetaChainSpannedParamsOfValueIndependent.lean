import Mathlib
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
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LinearIndependentOfIsParamFunV
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspMultiplicitySpaceSpanSphericalEigenPartsEqToStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenRankChainEigenPartHasParametersStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspMultiplicityMemSphericalEigenPartOfValueParaStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.EvenOnto

/- English proof (translation)
Introduce `D c hc j hj s hs ι x B hpar hB`. Rewrite using `[linearIndependent_iff']`. Introduce `t a hsum i₀ hi₀`. Take `⟨hne0, _⟩` from `hpar i₀`. Choose the witnesses or unpack the hypotheses as in `⟨v, hv⟩ : ∃ v, PiLocalization₂.val (x i₀) v ≠ 0 := by`.

Assume the negation of the conclusion as `h`. Use `push_neg at h`. Apply `hne0` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Apply `LinearMap.ext` to reduce the goal to its premises.

Introduce `w`. Simplify `h w` using `[PiLocalization₂.val]`. Set `p : ι → Prop` to `fun i => PiLocalization₂.val (x i) v ≠ 0`. Set `f : {i // p i} → (GA D s.V → ℂ)` to `fun i g => conj (PiLocalization₂.val (x i.1) v g)`. Establish `hli : LinearIndependent ℂ f`.

Use `GlobalTheory.ChainOnto.linearIndependent_of_isParamFunV D s.V c.S {i // p i} f (fun i => B i.1) ?_ ?_ ?_` and prove the remaining obligations. Introduce `i h0`. Apply `i.2` to reduce the goal to its premises. Use function extensionality and compare the values at `g`. Use `congrFun h0 g` as an intermediate fact.

Simplify `this` using `[f]`. Introduce `i`. Conclude with `(hpar i.1).2 v i.2`. Introduce `i i' hii'`. Conclude with `hB i.1 i'.1 (fun h => hii' (Subtype.ext h))`.

Rewrite `hli` using `[linearIndependent_iff']`. Establish `hsum' : ∀ g, ∑ i ∈ t, a i * PiLocalization₂.val (x i) v g = 0`. Introduce `g`. Use `congrArg (fun y : s.CC c => PiLocalization₂.val y v g) hsum` as an intermediate fact. Simplify `this` using `[PiLocalization₂.val, Finset.sum_apply]`.

Establish `key` using `hli (t.subtype p) (fun i => conj (a i.1)) ?_ ⟨i₀, hv⟩ (by simp [Finset.mem_subtype, hi₀])`. Simplify using `using key`. Use function extensionality and compare the values at `g`. Rewrite using `[Finset.sum_apply]`. Simplify using `only [Pi.smul_apply, smul_eq_mul, f, Pi.zero_apply]`.

Rewrite using `[Finset.sum_subtype_eq_sum_filter (f := fun i => conj (a i) * conj (PiLocalization₂.val (x i) v g)) (p := p)]`. Rewrite using `[Finset.sum_filter_of_ne]`. Rewrite using `[← map_zero (starRingEnd ℂ), ← hsum' g, map_sum]`. Simplify using `[map_mul]`. Introduce `i _ hne h0`.

Apply `hne` to reduce the goal to its premises. Simplify using `[h0]`.
-/
theorem parIndep_even : ∀ D : D7, ParIndep D := by
  intro D c hc j hj s hs ι x B hpar hB
  classical
  rw [linearIndependent_iff']
  intro t a hsum i₀ hi₀
  obtain ⟨hne0, _⟩ := hpar i₀
  obtain ⟨v, hv⟩ : ∃ v, PiLocalization₂.val (x i₀) v ≠ 0 := by
    by_contra h
    push_neg at h
    apply hne0
    apply Subtype.ext
    apply LinearMap.ext
    intro w
    simpa [PiLocalization₂.val] using h w
  let p : ι → Prop := fun i => PiLocalization₂.val (x i) v ≠ 0
  let f : {i // p i} → (GA D s.V → ℂ) := fun i g => conj (PiLocalization₂.val (x i.1) v g)
  have hli : LinearIndependent ℂ f := by
    refine GlobalTheory.ChainOnto.linearIndependent_of_isParamFunV D s.V c.S {i // p i} f (fun i => B i.1) ?_ ?_ ?_
    · intro i h0
      apply i.2
      funext g
      have := congrFun h0 g
      simpa [f] using this
    · intro i
      exact (hpar i.1).2 v i.2
    · intro i i' hii'
      exact hB i.1 i'.1 (fun h => hii' (Subtype.ext h))
  rw [linearIndependent_iff'] at hli
  have hsum' : ∀ g, ∑ i ∈ t, a i * PiLocalization₂.val (x i) v g = 0 := by
    intro g
    have := congrArg (fun y : s.CC c => PiLocalization₂.val y v g) hsum
    simpa [PiLocalization₂.val, Finset.sum_apply] using this
  have key := hli (t.subtype p) (fun i => conj (a i.1)) ?_ ⟨i₀, hv⟩ (by simp [Finset.mem_subtype, hi₀])
  · simpa using key
  · funext g
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, f, Pi.zero_apply]
    rw [Finset.sum_subtype_eq_sum_filter (f := fun i => conj (a i) * conj (PiLocalization₂.val (x i) v g)) (p := p)]
    rw [Finset.sum_filter_of_ne]
    · rw [← map_zero (starRingEnd ℂ), ← hsum' g, map_sum]
      simp [map_mul]
    · intro i _ hne h0
      apply hne
      simp [h0]

/- English proof (translation)
Introduce `hC D hF hM`. Use `⟨?_, ?_, parIndep_even D⟩` and prove the remaining obligations. Introduce `c hc j hj s hs`. Establish `hspan` using `GlobalTheory.T.cuspMultiplicitySpace_span_sphericalEigenParts_eq_top hC D hF c hc j hj s hs`. Establish `hpar` using `GlobalTheory.T.evenRankChain_eigenPart_has_parameters hC D c hc j hj s hs`.

Rewrite using `[eq_top_iff, ← hspan]`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `u ⟨e, he⟩`. Distinguish the cases in `h0 : u = 0`. Rewrite using `[h0]`.

Conclude with `Submodule.zero_mem _`. Conclude with `Submodule.subset_span ((hpar u e he).1 h0)`. Introduce `c hc j hj s hs x w B hv hf`. Take `⟨e, he⟩` from `GlobalTheory.T.cuspMultiplicity_mem_sphericalEigenPart_of_value_params hC D hM c hc j hj s hs x w B hv hf`. Conclude with `(GlobalTheory.T.evenRankChain_eigenPart_has_parameters hC D c hc j hj s hs x e he).2 w B hv hf`.
-/
theorem eig_parOfVal_indep : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, FinDim D → MetEx D → EigSpan D ∧ ParOfVal D ∧ ParIndep D := by
  intro hC D hF hM
  refine ⟨?_, ?_, parIndep_even D⟩
  · intro c hc j hj s hs
    have hspan := GlobalTheory.T.cuspMultiplicitySpace_span_sphericalEigenParts_eq_top hC D hF c hc j hj s hs
    have hpar := GlobalTheory.T.evenRankChain_eigenPart_has_parameters hC D c hc j hj s hs
    rw [eq_top_iff, ← hspan]
    refine Submodule.span_le.2 ?_
    rintro u ⟨e, he⟩
    by_cases h0 : u = 0
    · rw [h0]; exact Submodule.zero_mem _
    · exact Submodule.subset_span ((hpar u e he).1 h0)
  · intro c hc j hj s hs x w B hv hf
    obtain ⟨e, he⟩ := GlobalTheory.T.cuspMultiplicity_mem_sphericalEigenPart_of_value_params hC D hM c hc j hj s hs x w B hv hf
    exact (GlobalTheory.T.evenRankChain_eigenPart_has_parameters hC D c hc j hj s hs x e he).2 w B hv hf

end GlobalTheory.EvenOnto
