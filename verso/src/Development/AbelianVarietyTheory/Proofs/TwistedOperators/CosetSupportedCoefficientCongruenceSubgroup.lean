import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsCoreLat
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilMatrixCoeffEqZeroOfDistinctEigencharactersStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CosetCharConditionIntegralUnitCongruentDepthStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemCongruenceSubgroupOfStabilisesAndCongruentStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate TensorProduct
open Matrix

noncomputable section

namespace GlobalTheory.CosSupport

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem isHalf_actO_one {D : D7} (S T : HSp D) (c : AE D) (h : GA D T) (y : WO S T) (hy : IsHalf c y) :
    IsHalf c (actO S T 1 h y) := by
  intro i j
  simp only [actO, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  conv_rhs => rw [← hy k l]
  ring

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Replace the relevant objects with their definitions.

Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem cosSupp : CosSupp := by
  classical
  intro D hq T L μ0 hL sc G W M hM i hi x₀ hx₀ Φ hΦ m X hm g hg hne
  obtain ⟨e, he, -⟩ := W.cosVec_is
  have hw := W.om_is (.core i) (by show Node.InRange D.R.m (.core (i + 1)); simp [Node.InRange]; omega)
  have hth : IsThetaFunO W.ψ _ _ Φ := hΦ.1.1
  have hchar : ∀ y : WO (G.pS (.core i)) (G.pT (.core i)), IsHalf (cA D e) y →
      (∀ u ∈ depLat G (.core i), W.ψ (symplO _ _ u y) = 1) →
      (∀ u ∈ depLat G (.core i), W.ψ (symplO _ _ u (actO _ _ 1 g⁻¹ y)) = 1) →
      W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) (e • x₀.map (incA D)) y) =
        W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) (e • x₀.map (incA D)) (actO _ _ 1 g⁻¹ y)) := by
    intro y h1 h2 h3
    by_contra hne'
    exact hne (GlobalTheory.T.weilMatrixCoeff_eq_zero_of_distinct_eigencharacters D W.ψ _ _ _ _ (W.om (.core i)) hw m X hm Φ hth g y _ _ (hΦ.2 e he y h1 h2)
      (hΦ.2 e he _ (isHalf_actO_one _ _ _ _ y h1) h3) hne')
  have hloc := GlobalTheory.T.cosetCharCondition_integral_unit_congruent_depth D hq T L μ0 hL sc G W M hM i hi x₀ hx₀ e he g hchar
  refine GlobalTheory.T.mem_congruenceSubgroup_of_stabilises_and_congruent D (G.V (.core i)) (G.Λ (.core i)) (G.sp.P_is i (by omega)).sd G.pl.W0 e he G.modul ?_ g ?_ hloc
  · intro PP hPP
    have hprime : PP.asIdeal.IsPrime := PP.isPrime
    obtain ⟨v, hv, hle⟩ := hprime.prod_le.1 hPP
    have hle' : (G.pl.w v).asIdeal ≤ PP.asIdeal := hprime.le_of_pow_le hle
    have heq : G.pl.w v = PP := HeightOneSpectrum.ext ((G.pl.w v).isMaximal.eq_of_le hprime.ne_top hle')
    unfold Places.W0
    exact Finset.mem_image.2 ⟨v, hv, heq⟩
  · intro v hv
    apply hg v
    intro hvS
    exact hv _ (by unfold Places.W0; exact Finset.mem_image.2 ⟨v, hvS, rfl⟩) (G.pl.under_w hvS)

end GlobalTheory.CosSupport

end
