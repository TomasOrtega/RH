import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsRealFormsOnPoints
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsComplexFormsOnPoints
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsIndependentModBaseChange
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the hypotheses and the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Simplify to obtain the desired conclusion from the available facts. Rewrite the indicated hypotheses using the stated equalities. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem RealFormsOnPoints.proof (hN : ComplexFormsOnPoints.Statement)
    (hB : IndependentModBaseChange.Statement) : RealFormsOnPoints.Statement := by
  intro K _ ι _ Ω _ y d e r g hP hg hli c hc
  obtain ⟨_, ⟨hprime, -, hrel⟩, -, -⟩ := hP

  have hZ : LinearIndependent ℤ (fun i => Ideal.Quotient.mk (mCoordIdeal y) (g i)) := by
    rw [Fintype.linearIndependent_iff] at hli ⊢
    intro n hn
    apply hli n
    have hmem : ∑ i, n i • g i ∈ mCoordIdeal y := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sum]
      simpa only [map_zsmul] using hn
    have h0 : mConeMap y (∑ i, n i • g i) = 0 := hmem
    have hsum : mConeMap y (∑ i, n i • g i) =
        MvPolynomial.C (∑ i, n i • aeval y (g i)) * ∏ k, MvPolynomial.X k ^ e k := by
      rw [map_sum, map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_zsmul, ProjLine.mConeMap_eq_of_isMultiHomog y (hg i), map_zsmul, smul_mul_assoc]
    rw [hsum] at h0
    have hX : (∏ k, MvPolynomial.X k ^ e k : MvPolynomial K Ω) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (X_ne_zero k)
    exact (MvPolynomial.C_eq_zero).mp ((mul_eq_zero.mp h0).resolve_right hX)

  have hC := hB _ (mCoordIdeal y) r g hZ
  set I := (mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℂ)) with hI

  have hF : (∑ i, (c i : ℂ) • MvPolynomial.map (Int.castRingHom ℂ) (g i)) ∈ I := by
    refine hN K ι _ hprime hrel _ fun z hz => ?_
    rw [map_sum]
    simpa only [smul_eval] using hc z hz
  rw [Fintype.linearIndependent_iff] at hC
  funext i
  have h := hC (fun i => (c i : ℂ)) (by
    rw [← Ideal.Quotient.eq_zero_iff_mem] at hF
    rw [← hF, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Ideal.Quotient.mkₐ_eq_mk ℂ, map_smul]) i
  exact_mod_cast h

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
