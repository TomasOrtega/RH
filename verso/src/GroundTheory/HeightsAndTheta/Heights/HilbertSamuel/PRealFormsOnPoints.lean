import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsRealFormsOnPoints
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsComplexFormsOnPoints
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsIndependentModBaseChange
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

/- English proof (translation)
Introduce `K _ ι _ Ω _ y d e r g hP hg hli c hc`. Take `⟨_, ⟨hprime, -, hrel⟩, -, -⟩` from `hP`. Establish `hZ : LinearIndependent ℤ (fun i => Ideal.Quotient.mk (mCoordIdeal y) (g i))`. Rewrite `hli`, the goal using `[Fintype.linearIndependent_iff]`. Introduce `n hn`.

Apply `hli n` to reduce the goal to its premises. Establish `hmem : ∑ i, n i • g i ∈ mCoordIdeal y`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_sum]`. Simplify `hn` using `only [map_zsmul]`. Establish `h0 : mConeMap y (∑ i, n i • g i) = 0` using `hmem`.

Establish `hsum : mConeMap y (∑ i, n i • g i) = MvPolynomial.C (∑ i, n i • aeval y (g i)) * ∏ k, MvPolynomial.X k ^ e k`. Rewrite using `[map_sum, map_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_zsmul, ProjLine.mConeMap_eq_of_isMultiHomog y (hg i), map_zsmul, smul_mul_assoc]`. Rewrite `h0` using `[hsum]`.

Establish `hX : (∏ k, MvPolynomial.X k ^ e k : MvPolynomial K Ω) ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (X_ne_zero k)`. Conclude with `(MvPolynomial.C_eq_zero).mp ((mul_eq_zero.mp h0).resolve_right hX)`. Establish `hC` using `hB _ (mCoordIdeal y) r g hZ`. Use `set I := (mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℂ)) with hI`. Establish `hF : (∑ i, (c i : ℂ) • MvPolynomial.map (Int.castRingHom ℂ) (g i)) ∈ I`.

Use `hN K ι _ hprime hrel _ fun z hz => ?_` and prove the remaining obligations. Rewrite using `[map_sum]`. Simplify `hc z hz` using `only [smul_eval]`. Rewrite `hC` using `[Fintype.linearIndependent_iff]`. Use function extensionality and compare the values at `i`.

Establish `h` using `hC (fun i => (c i : ℂ)) (by`. Rewrite `hF` using `[← Ideal.Quotient.eq_zero_iff_mem]`. Rewrite using `[← hF, map_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← Ideal.Quotient.mkₐ_eq_mk ℂ, map_smul]) i`.

Conclude with `h` after adjusting the coercions.
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
