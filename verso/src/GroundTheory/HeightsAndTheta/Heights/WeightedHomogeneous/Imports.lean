import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Statements
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.StatementsFibreCompDimZ
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.GeoNum
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.CycDim
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ReciprocityTheory.ChartRestriction.G

/- English proof (translation)
Introduce `ι _ _ n P D hdim a p hp`. Rewrite using `[hF ι n P D hdim a p, NumbersDVR.cycEval, finsum_mem_def]`. Use `finsum_congr fun W ↦ ?_` and prove the remaining obligations. Distinguish the cases in `hW : W ∈ Geo.divSupp (ι := blockIdx n) P.ideal (C (p : ℤ))`. Rewrite using `[Set.indicator_of_mem hW]`.

Establish `hW' : W ∈ (P.ideal ⊔ Ideal.span {C (p : ℤ)}).minimalPrimes ∧ NumbersDVR.IsRelevant W` using `hW`. Establish `hWp : W.IsPrime` using `hW.1.1.1`. Establish `hpW : (C (p : ℤ) : MvPolynomial (Coord n) ℤ) ∈ W` using `hW.1.1.2 (Ideal.mem_sup_right (Ideal.subset_span rfl))`. Establish `hC : Geo.IsMultiHomog (ι` using `blockIdx n) (C (p : ℤ) : MvPolynomial (Coord n) ℤ) 0 := by`. Introduce `m hm k`.

Establish `h0` using `MvPolynomial.mem_support_iff.mp hm`. Rewrite `h0` using `[coeff_C]`. Use `split_ifs at h0 with h`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Conclude with `absurd rfl h0`. Establish `hMP : Geo.IsMultiProjPrime (ι` using `blockIdx n) W := ⟨hWp, ReciprocityTheory.ChartRestriction.G.AI.I1.cyc_isMultiHomogIdeal_of_mem_minimalPrimes P.isMultiProjPrime.2.1 hC hW.1, hW.2⟩`. Establish `hdimW : ringKrullDim (Geo.MRing (blockIdx n) ⧸ W) = ((D + Fintype.card ι : ℕ) : WithBot ℕ∞)`. Use `hZ (Coord n) P.ideal P.isPrime P.isHorizontal (D + Fintype.card ι) p hp.out ?_ W hW.1` and prove the remaining obligations. Rewrite using `[show D + Fintype.card ι + 1 = D + 1 + Fintype.card ι by omega]`.

Conclude with `hdim`. Establish `hm : Geo.multAt (ι` using `blockIdx n) (P.ideal ⊔ Ideal.span {C (p : ℤ)}) W = (NumbersDVR.multAt (P.ideal ⊔ Ideal.span {C (p : ℤ)}) W).toNat := by`. Rewrite using `[Geo.multAt, dif_pos hWp]`. Both sides reduce to the same expression. Rewrite using `[NumbersDVR.divCycle, dif_pos hW', hm, Bridge.intNum_map_eq_geoNum p D W hMP hpW hdimW a]`.

Establish `hW' : ¬(W ∈ (P.ideal ⊔ Ideal.span {C (p : ℤ)}).minimalPrimes ∧ NumbersDVR.IsRelevant W)` using `hW`. Rewrite using `[Set.indicator_of_notMem hW, NumbersDVR.divCycle, dif_neg hW', zero_mul]`.
-/
theorem GeometricArithmeticNumbers.proof (hF : WeightedDegree.Statement) (hZ : FibreCompDimZ.Statement) :
    GeometricArithmeticNumbers.Statement := by
  intro ι _ _ n P D hdim a p hp
  rw [hF ι n P D hdim a p, NumbersDVR.cycEval, finsum_mem_def]
  refine finsum_congr fun W ↦ ?_
  by_cases hW : W ∈ Geo.divSupp (ι := blockIdx n) P.ideal (C (p : ℤ))
  · rw [Set.indicator_of_mem hW]
    have hW' : W ∈ (P.ideal ⊔ Ideal.span {C (p : ℤ)}).minimalPrimes ∧ NumbersDVR.IsRelevant W := hW
    have hWp : W.IsPrime := hW.1.1.1
    have hpW : (C (p : ℤ) : MvPolynomial (Coord n) ℤ) ∈ W :=
      hW.1.1.2 (Ideal.mem_sup_right (Ideal.subset_span rfl))
    have hC : Geo.IsMultiHomog (ι := blockIdx n) (C (p : ℤ) : MvPolynomial (Coord n) ℤ) 0 := by
      intro m hm k
      have h0 := MvPolynomial.mem_support_iff.mp hm
      rw [coeff_C] at h0
      split_ifs at h0 with h
      · subst h
        simp
      · exact absurd rfl h0
    have hMP : Geo.IsMultiProjPrime (ι := blockIdx n) W :=
      ⟨hWp, ReciprocityTheory.ChartRestriction.G.AI.I1.cyc_isMultiHomogIdeal_of_mem_minimalPrimes
        P.isMultiProjPrime.2.1 hC hW.1, hW.2⟩
    have hdimW : ringKrullDim (Geo.MRing (blockIdx n) ⧸ W) =
        ((D + Fintype.card ι : ℕ) : WithBot ℕ∞) := by
      refine hZ (Coord n) P.ideal P.isPrime P.isHorizontal (D + Fintype.card ι) p hp.out ?_ W hW.1
      rw [show D + Fintype.card ι + 1 = D + 1 + Fintype.card ι by omega]
      exact hdim
    have hm : Geo.multAt (ι := blockIdx n) (P.ideal ⊔ Ideal.span {C (p : ℤ)}) W =
        (NumbersDVR.multAt (P.ideal ⊔ Ideal.span {C (p : ℤ)}) W).toNat := by
      rw [Geo.multAt, dif_pos hWp]
      rfl
    rw [NumbersDVR.divCycle, dif_pos hW', hm,
      Bridge.intNum_map_eq_geoNum p D W hMP hpW hdimW a]
  · have hW' : ¬(W ∈ (P.ideal ⊔ Ideal.span {C (p : ℤ)}).minimalPrimes ∧ NumbersDVR.IsRelevant W) := hW
    rw [Set.indicator_of_notMem hW, NumbersDVR.divCycle, dif_neg hW', zero_mul]

end GroundTheory.Heights₂.Heights
