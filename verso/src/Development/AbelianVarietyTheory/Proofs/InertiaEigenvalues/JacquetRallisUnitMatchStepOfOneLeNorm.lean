import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FullToGlIsSelfAdjoint
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisBorderedMatrixNormalFormInvariantsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryActionHermitianInvariantsTransitiveStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisOrbitalIntegralsInvariantLocallyConStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyJacquetRallisHaarMeasuresForallSizeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMulStarEqOfNormOneUnramifiedQuadraticStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGlConjugateLastBasisNormalFormOfNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisHankelDetNeZeroOfLiftStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlOrbitalIntegralUnitLiftLastBasisReduceStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryOrbitNormalFormUnitInvariantStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryOrbitalIntegralLiftLastBasisReduceStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HermitianBlockHasInvariantsOfLiftMatchStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HermitianBlockHasInvariantsOfLiftWithLastBasisStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitIndicatorsMatchAtOfOneLtNormFirstMomentStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BorderedInvariantsAndHankelDetMapRingHomStatement

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.Step

/- English proof (translation)
Simplify using `[mom, sec, dotProduct, Fin.sum_univ_succ]`.
-/
theorem mom_sec_zero {k : Type} [CommRing k] {r : ℕ} (a : Inv (r + 1) k) : mom (sec a) 0 = a.2.1 0 := by
  simp [mom, sec, dotProduct, Fin.sum_univ_succ]

/- English proof (translation)
Introduce `r hUM F E _ _ _ _ _ M a hΔ h1`. Rewrite `h1` using `[mom_sec_zero]`. Break down `h1.lt_or_eq with hlt | heq` into its components or cases. Conclude with `GlobalTheory.T.unitIndicators_matchAt_of_one_lt_norm_firstMoment F E r M a hlt`. Use `set μ := a.2.1 0 with hμdef`.

Establish `hμ1 : ‖μ‖ = 1` using `heq.symm`. Establish `hμ0 : μ ≠ 0` using `by intro h; rw [h, norm_zero] at hμ1; exact zero_ne_one hμ1`. Take `⟨g, Z, hgZ⟩` from `GlobalTheory.T.exists_glConjugate_lastBasisNormalForm_of_ne_zero F r a hμ0`. Establish `hinvF` using `GlobalTheory.T.jacquetRallis_borderedMatrix_normalForm_invariants F (r + 1)`. Establish `hinvL : inv (GlobalTheory.JR.Step.lift Z μ a.2.2) = a`.

Rewrite using `[← hgZ, hinvF.1, hinvF.2.1]`. Establish `hΔL : Delta (inv (GlobalTheory.JR.Step.lift Z μ a.2.2)) ≠ 0` using `by rw [hinvL]; exact hΔ`. Establish `hΔZ : Delta (inv Z) ≠ 0` using `GlobalTheory.T.jacquetRallisHankelDet_ne_zero_of_lift F r Z μ a.2.2 hΔL`. Take `⟨M'⟩` from `GlobalTheory.T.nonempty_jacquetRallisHaarMeasures_forall_size F E r`. Establish `hL7` using `GlobalTheory.T.jacquetRallisOrbitalIntegrals_invariant_locallyConstant F E (r + 1) M`.

Establish `hL7'` using `GlobalTheory.T.jacquetRallisOrbitalIntegrals_invariant_locallyConstant F E r M'`. Establish `hG : orbG M (unitG (r + 1) F) (sec a) = (if ‖a.2.2‖ ≤ 1 then 1 else 0) * orbG M' (unitG r F) (sec (inv Z))`. Rewrite using `[← hL7.1 _ g, hgZ, GlobalTheory.T.glOrbitalIntegral_unit_liftLastBasis_reduce F E r M M' Z μ a.2.2 hμ1 hΔL]`. Take `⟨h, hh, -⟩` from `(GlobalTheory.T.jacquetRallis_borderedMatrix_normalForm_invariants F r).2.2.2.2 Z (sec (inv Z)) hΔZ ((GlobalTheory.T.jacquetRallis_borderedMatrix_normalForm_invariants F r).2.1 (inv Z))`. Rewrite using `[← hh.1, hL7'.1]`.

Establish `hIH` using `hUM F E M' (inv Z) hΔZ`. Establish `hΔmap : ∀ (X : Hn (r + 1) F E), HasInv X a → Delta (inv X.toGl) ≠ 0`. Introduce `X hX`. Rewrite using `[hX, (GlobalTheory.T.borderedInvariants_and_hankelDet_map_ringHom F E (algebraMap F E) (r + 1)).2]`. Conclude with `(map_ne_zero _).mpr hΔ`.

Use `⟨fun X hX => ?_, fun hno => ?_⟩` and prove the remaining obligations. Take `⟨u, X', ν, hν, huX⟩` from `GlobalTheory.T.unitary_orbit_normal_form_unit_invariant F E r X a hX hμ1`. Establish `hν1 : ‖ν‖ = 1`. Establish `h2 : ‖ν‖ * ‖ν‖ = 1`. Use `congrArg norm hν` as an intermediate fact.

Rewrite `this` using `[norm_mul, Unram.norm_star (F := F), norm_algebraMap']`. Rewrite using `[this, hμ1]`. Use polynomial arithmetic with `[norm_nonneg ν]`. Establish `hXL : HasInv (GlobalTheory.JR.Step.liftH X' ν a.2.2) a`. Rewrite using `[← huX]`.

Conclude with `(GlobalTheory.T.unitary_action_hermitian_invariants_transitive F E (r + 1)).2.1 u X a hX`. Establish `hU : orbU M (unitU (r + 1) F E) X = (if ‖a.2.2‖ ≤ 1 then 1 else 0) * orbU M' (unitU r F E) X'`. Rewrite using `[← hL7.2.1 _ u, huX]`. Conclude with `GlobalTheory.T.unitaryOrbitalIntegral_liftLastBasis_reduce F E r M M' X' ν a.2.2 hν1 (hΔmap _ hXL)`. Establish `hX' : HasInv X' (inv Z)` using `GlobalTheory.T.hermitianBlock_hasInvariants_of_lift_match F E r Z X' μ a.2.2 ν hν hμ0 hΔL (by rw [hinvL]; exact hXL)`.

Rewrite using `[hG, hU, hIH.1 X' hX']`. Take `⟨ν, hν⟩` from `GlobalTheory.T.exists_mul_star_eq_of_norm_one_unramifiedQuadratic F E μ hμ1`. Establish `hno' : ¬ ∃ X' : Hn r F E, HasInv X' (inv Z)`. Introduce and unpack `⟨X', hX'⟩`. Conclude with `hno ⟨_, hinvL ▸ GlobalTheory.T.hermitianBlock_hasInvariants_of_liftWithLastBasis F E r Z X' μ a.2.2 ν hν hμ0 hΔL hΔZ hX'⟩`.

Rewrite using `[hG, hIH.2 hno', mul_zero]`.
-/
theorem unitMatchAt_of_one_le_norm : ∀ r : ℕ, UnitMatch r → ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (M : Meas (r + 1) F E) (a : Inv (r + 1) F), Delta a ≠ 0 → 1 ≤ ‖mom (sec a) 0‖ → MatchAt M (unitG (r + 1) F) (unitU (r + 1) F E) a := by
  intro r hUM F E _ _ _ _ _ M a hΔ h1
  rw [mom_sec_zero] at h1
  rcases h1.lt_or_eq with hlt | heq
  · exact GlobalTheory.T.unitIndicators_matchAt_of_one_lt_norm_firstMoment F E r M a hlt
  set μ := a.2.1 0 with hμdef
  have hμ1 : ‖μ‖ = 1 := heq.symm
  have hμ0 : μ ≠ 0 := by intro h; rw [h, norm_zero] at hμ1; exact zero_ne_one hμ1
  obtain ⟨g, Z, hgZ⟩ := GlobalTheory.T.exists_glConjugate_lastBasisNormalForm_of_ne_zero F r a hμ0
  have hinvF := GlobalTheory.T.jacquetRallis_borderedMatrix_normalForm_invariants F (r + 1)
  have hinvL : inv (GlobalTheory.JR.Step.lift Z μ a.2.2) = a := by
    rw [← hgZ, hinvF.1, hinvF.2.1]
  have hΔL : Delta (inv (GlobalTheory.JR.Step.lift Z μ a.2.2)) ≠ 0 := by rw [hinvL]; exact hΔ
  have hΔZ : Delta (inv Z) ≠ 0 := GlobalTheory.T.jacquetRallisHankelDet_ne_zero_of_lift F r Z μ a.2.2 hΔL
  obtain ⟨M'⟩ := GlobalTheory.T.nonempty_jacquetRallisHaarMeasures_forall_size F E r
  have hL7 := GlobalTheory.T.jacquetRallisOrbitalIntegrals_invariant_locallyConstant F E (r + 1) M
  have hL7' := GlobalTheory.T.jacquetRallisOrbitalIntegrals_invariant_locallyConstant F E r M'
  have hG : orbG M (unitG (r + 1) F) (sec a) = (if ‖a.2.2‖ ≤ 1 then 1 else 0) * orbG M' (unitG r F) (sec (inv Z)) := by
    rw [← hL7.1 _ g, hgZ, GlobalTheory.T.glOrbitalIntegral_unit_liftLastBasis_reduce F E r M M' Z μ a.2.2 hμ1 hΔL]
    obtain ⟨h, hh, -⟩ := (GlobalTheory.T.jacquetRallis_borderedMatrix_normalForm_invariants F r).2.2.2.2 Z (sec (inv Z)) hΔZ ((GlobalTheory.T.jacquetRallis_borderedMatrix_normalForm_invariants F r).2.1 (inv Z))
    rw [← hh.1, hL7'.1]
  have hIH := hUM F E M' (inv Z) hΔZ
  have hΔmap : ∀ (X : Hn (r + 1) F E), HasInv X a → Delta (inv X.toGl) ≠ 0 := by
    intro X hX
    rw [hX, (GlobalTheory.T.borderedInvariants_and_hankelDet_map_ringHom F E (algebraMap F E) (r + 1)).2]
    exact (map_ne_zero _).mpr hΔ
  refine ⟨fun X hX => ?_, fun hno => ?_⟩
  · obtain ⟨u, X', ν, hν, huX⟩ := GlobalTheory.T.unitary_orbit_normal_form_unit_invariant F E r X a hX hμ1
    have hν1 : ‖ν‖ = 1 := by
      have h2 : ‖ν‖ * ‖ν‖ = 1 := by
        have := congrArg norm hν
        rw [norm_mul, Unram.norm_star (F := F), norm_algebraMap'] at this
        rw [this, hμ1]
      nlinarith [norm_nonneg ν]
    have hXL : HasInv (GlobalTheory.JR.Step.liftH X' ν a.2.2) a := by
      rw [← huX]; exact (GlobalTheory.T.unitary_action_hermitian_invariants_transitive F E (r + 1)).2.1 u X a hX
    have hU : orbU M (unitU (r + 1) F E) X = (if ‖a.2.2‖ ≤ 1 then 1 else 0) * orbU M' (unitU r F E) X' := by
      rw [← hL7.2.1 _ u, huX]
      exact GlobalTheory.T.unitaryOrbitalIntegral_liftLastBasis_reduce F E r M M' X' ν a.2.2 hν1 (hΔmap _ hXL)
    have hX' : HasInv X' (inv Z) :=
      GlobalTheory.T.hermitianBlock_hasInvariants_of_lift_match F E r Z X' μ a.2.2 ν hν hμ0 hΔL (by rw [hinvL]; exact hXL)
    rw [hG, hU, hIH.1 X' hX']
  · obtain ⟨ν, hν⟩ := GlobalTheory.T.exists_mul_star_eq_of_norm_one_unramifiedQuadratic F E μ hμ1
    have hno' : ¬ ∃ X' : Hn r F E, HasInv X' (inv Z) := by
      rintro ⟨X', hX'⟩
      exact hno ⟨_, hinvL ▸ GlobalTheory.T.hermitianBlock_hasInvariants_of_liftWithLastBasis F E r Z X' μ a.2.2 ν hν hμ0 hΔL hΔZ hX'⟩
    rw [hG, hIH.2 hno', mul_zero]

end GlobalTheory.JR.Step
