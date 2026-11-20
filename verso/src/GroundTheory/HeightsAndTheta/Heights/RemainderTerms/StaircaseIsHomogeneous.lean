import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsFlag
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.IsFlagIntegralOne
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.FlagIntegralRealEqMulDdConst
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCoinvAtTop
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCoinvPolynomialReduction
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCoinvMonomialReduction
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCoinvStepReduction
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCoinvIdealComponent
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCoinvIdealRepresentation
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PHomogeneousComponentMul
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCoinvStaircaseComponent
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCoinvStaircaseDegree
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

/- English proof (translation)
The claim follows from `CoinvAtTop.proof (CoinvPolynomialReduction.proof (CoinvMonomialReduction.proof CoinvStepReduction.proof)) (CoinvIdealComponent.proof CoinvIdealRepresentation.proof HomogeneousComponentMul.proof) (CoinvStaircaseComponent.proof CoinvStaircaseDegree.proof)`.
-/
theorem CoinvAtTop.closed : CoinvAtTop.Statement :=
  CoinvAtTop.proof
    (CoinvPolynomialReduction.proof (CoinvMonomialReduction.proof CoinvStepReduction.proof))
    (CoinvIdealComponent.proof CoinvIdealRepresentation.proof HomogeneousComponentMul.proof)
    (CoinvStaircaseComponent.proof CoinvStaircaseDegree.proof)

namespace FlagProportional

/- English proof (translation)
Use `isHomogeneous_monomial _ ?_` and prove the remaining obligations. Rewrite using `[Finsupp.degree_eq_sum]`. Use `show ∑ v, (Coinv.staircase f (j + k)) v = Coinv.coinvTop f (j + k)`. Rewrite using `[← Coinv.sum_staircase_exponents]`. Simplify using `[Coinv.staircase]`.
-/
theorem staircase_isHomogeneous (f j k : ℕ) :
    (monomial (Coinv.staircase f (j + k)) (1 : ℝ)).IsHomogeneous (IndefiniteRowSideFullHecke.RestTerms.dimFl f j k) := by
  refine isHomogeneous_monomial _ ?_
  rw [Finsupp.degree_eq_sum]
  show ∑ v, (Coinv.staircase f (j + k)) v = Coinv.coinvTop f (j + k)
  rw [← Coinv.sum_staircase_exponents]
  simp [Coinv.staircase]

/- English proof (translation)
Use `set D := IndefiniteRowSideFullHecke.RestTerms.dimFl f j k`. Use `set s : IndefiniteRowSideFullHecke.RestTerms.Roots f j k := monomial (Coinv.staircase f (j + k)) 1`. Take `⟨Q, hQ, hEq⟩` from `CoinvIdealComponent.proof CoinvIdealRepresentation.proof HomogeneousComponentMul.proof ℝ f (j + k) _ hc D`. Establish `hJ : (G - C c * s).IsHomogeneous D` using `hG.sub ((staircase_isHomogeneous f j k).C_mul c)`. Establish `hcomp : homogeneousComponent D (G - C c * s) = G - C c * s`.

Rewrite using `[homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).mpr hJ), if_pos rfl]`. Establish `e1` using `hcomp.symm.trans hEq`. Establish `e2 : G - C c * s = homogeneousComponent D (∑ m ∈ Finset.Icc 1 (j + k), ∑ b : Fin f, Coinv.bps ℝ f (j + k) m b * Q m b)`. Rewrite using `[← e1, hcomp]`. Establish `hzero : L (G - C c * s) = 0`.

Rewrite using `[e2, map_sum, map_sum]`. Use `Finset.sum_eq_zero fun m hm => ?_` and prove the remaining obligations. Rewrite using `[map_sum, map_sum]`. Use `Finset.sum_eq_zero fun b _ => ?_` and prove the remaining obligations. Establish `hm1 : 1 ≤ m` using `(Finset.mem_Icc.mp hm).1`.

Establish `hp : (Coinv.bps ℝ f (j + k) m b).IsHomogeneous m` using `IsHomogeneous.sum _ _ _ fun i _ => isHomogeneous_X_pow _ _`. Rewrite using `[homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).mpr (hp.mul (hQ m b)))]`. Use `split_ifs with h`. Conclude with `hL m b (Q m b) hm1 (by omega) (hQ m b)`. Conclude with `map_zero L`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem eval_top (f j k : ℕ) (L : IndefiniteRowSideFullHecke.RestTerms.Roots f j k →ₗ[ℝ] ℝ)
    (hL : ∀ (m : ℕ) (τ : Fin f) (G : IndefiniteRowSideFullHecke.RestTerms.Roots f j k), 1 ≤ m →
      m ≤ IndefiniteRowSideFullHecke.RestTerms.dimFl f j k → G.IsHomogeneous (IndefiniteRowSideFullHecke.RestTerms.dimFl f j k - m) →
        L (IndefiniteRowSideFullHecke.RestTerms.psumAt f j k m τ * G) = 0)
    (G : IndefiniteRowSideFullHecke.RestTerms.Roots f j k) (hG : G.IsHomogeneous (IndefiniteRowSideFullHecke.RestTerms.dimFl f j k)) (c : ℝ)
    (hc : G - C c * monomial (Coinv.staircase f (j + k)) 1 ∈ Coinv.psumIdeal ℝ f (j + k)) :
    L G = c * L (monomial (Coinv.staircase f (j + k)) 1) := by
  classical
  set D := IndefiniteRowSideFullHecke.RestTerms.dimFl f j k
  set s : IndefiniteRowSideFullHecke.RestTerms.Roots f j k := monomial (Coinv.staircase f (j + k)) 1
  obtain ⟨Q, hQ, hEq⟩ := CoinvIdealComponent.proof CoinvIdealRepresentation.proof
    HomogeneousComponentMul.proof ℝ f (j + k) _ hc D
  have hJ : (G - C c * s).IsHomogeneous D := hG.sub ((staircase_isHomogeneous f j k).C_mul c)
  have hcomp : homogeneousComponent D (G - C c * s) = G - C c * s := by
    rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).mpr hJ), if_pos rfl]
  have e1 := hcomp.symm.trans hEq
  have e2 : G - C c * s = homogeneousComponent D
      (∑ m ∈ Finset.Icc 1 (j + k), ∑ b : Fin f, Coinv.bps ℝ f (j + k) m b * Q m b) := by
    rw [← e1, hcomp]
  have hzero : L (G - C c * s) = 0 := by
    rw [e2, map_sum, map_sum]
    refine Finset.sum_eq_zero fun m hm => ?_
    rw [map_sum, map_sum]
    refine Finset.sum_eq_zero fun b _ => ?_
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    have hp : (Coinv.bps ℝ f (j + k) m b).IsHomogeneous m :=
      IsHomogeneous.sum _ _ _ fun i _ => isHomogeneous_X_pow _ _
    rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).mpr (hp.mul (hQ m b)))]
    split_ifs with h
    · exact hL m b (Q m b) hm1 (by omega) (hQ m b)
    · exact map_zero L
  calc L G = L (G - C c * s) + L (C c * s) := by rw [← map_add, sub_add_cancel]
    _ = c * L s := by rw [hzero, zero_add, C_mul', map_smul, smul_eq_mul]

end FlagProportional

open FlagProportional in

/- English proof (translation)
Introduce `f j k _ _ _ I hI`. Use `set s : IndefiniteRowSideFullHecke.RestTerms.Roots f j k := monomial (Coinv.staircase f (j + k)) 1`. Establish `hdd : ∀ G : IndefiniteRowSideFullHecke.RestTerms.Roots f j k, G.IsHomogeneous (IndefiniteRowSideFullHecke.RestTerms.dimFl f j k) → ∃ c : ℝ, I G = c * I s ∧ IndefiniteRowSideFullHecke.RestTerms.ddConst f j k G = c * IndefiniteRowSideFullHecke.RestTerms.ddConst f j k s`. Introduce `G hG`. Take `⟨c, hc⟩` from `CoinvAtTop.closed ℝ f (j + k) G hG`.

Conclude with `⟨c, eval_top f j k I hI.kills G hG c hc, eval_top f j k (IndefiniteRowSideFullHecke.RestTerms.ddConst f j k) (fun m τ G hm _ _ => FlagEq.ddConst_psumAt_mul f j k m τ G hm) G hG c hc⟩`. Establish `hs0 : IndefiniteRowSideFullHecke.RestTerms.ddConst f j k s ≠ 0`. Take `⟨c, -, h⟩` from `hdd (monomial (FlagEq.rho f (j + k)) 1) (isHomogeneous_monomial _ (by rw [FlagEq.rho_degree]; rfl))`. Rewrite `h` using `[FlagEq.ddConst_monomial_rho]`. Introduce `h0`.

Rewrite `h` using `[h0, mul_zero]`. Conclude with `one_ne_zero h`. Establish `hIs : I s ≠ 0`. Take `⟨G0, hG0, hne⟩` from `hI.ne_zero`. Take `⟨c, h, -⟩` from `hdd G0 hG0`.

Introduce `h0`. Rewrite `h` using `[h0, mul_zero]`. Conclude with `hne h`. Use `⟨I s / IndefiniteRowSideFullHecke.RestTerms.ddConst f j k s, div_ne_zero hIs hs0, fun G hG => ?_⟩` and prove the remaining obligations. Take `⟨c, h1, h2⟩` from `hdd G hG`.

Rewrite using `[h1, h2]`. Clear the denominators using the available nonvanishing facts.
-/
theorem FlagIntegralProportional.intersectionNumber_baseChange : IndefiniteRowSideFullHecke.RestTerms.FlagIntegralProportional.Statement := by
  intro f j k _ _ _ I hI
  set s : IndefiniteRowSideFullHecke.RestTerms.Roots f j k := monomial (Coinv.staircase f (j + k)) 1
  have hdd : ∀ G : IndefiniteRowSideFullHecke.RestTerms.Roots f j k, G.IsHomogeneous (IndefiniteRowSideFullHecke.RestTerms.dimFl f j k) →
      ∃ c : ℝ, I G = c * I s ∧ IndefiniteRowSideFullHecke.RestTerms.ddConst f j k G = c * IndefiniteRowSideFullHecke.RestTerms.ddConst f j k s := by
    intro G hG
    obtain ⟨c, hc⟩ := CoinvAtTop.closed ℝ f (j + k) G hG
    exact ⟨c, eval_top f j k I hI.kills G hG c hc,
      eval_top f j k (IndefiniteRowSideFullHecke.RestTerms.ddConst f j k)
        (fun m τ G hm _ _ => FlagEq.ddConst_psumAt_mul f j k m τ G hm) G hG c hc⟩
  have hs0 : IndefiniteRowSideFullHecke.RestTerms.ddConst f j k s ≠ 0 := by
    obtain ⟨c, -, h⟩ := hdd (monomial (FlagEq.rho f (j + k)) 1)
      (isHomogeneous_monomial _ (by rw [FlagEq.rho_degree]; rfl))
    rw [FlagEq.ddConst_monomial_rho] at h
    intro h0
    rw [h0, mul_zero] at h
    exact one_ne_zero h
  have hIs : I s ≠ 0 := by
    obtain ⟨G0, hG0, hne⟩ := hI.ne_zero
    obtain ⟨c, h, -⟩ := hdd G0 hG0
    intro h0
    rw [h0, mul_zero] at h
    exact hne h
  refine ⟨I s / IndefiniteRowSideFullHecke.RestTerms.ddConst f j k s, div_ne_zero hIs hs0, fun G hG => ?_⟩
  obtain ⟨c, h1, h2⟩ := hdd G hG
  rw [h1, h2]
  field_simp

end

end GroundTheory.Heights₂.Heights.RestTerms
