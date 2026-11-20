import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.IsSemipositiveRelTrivLine
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter

noncomputable section

/- English proof (translation)
Use `charZero_of_inj_zero fun n hn => ?_` and prove the remaining obligations. Establish `hmem : (MvPolynomial.C (n : ℤ) : MRing ι) ∈ mCoordIdeal y` using `by show mConeMap y (MvPolynomial.C (n : ℤ)) = 0`. Rewrite using `[mConeMap, MvPolynomial.aeval_C, eq_intCast, Int.cast_natCast, ← map_natCast (MvPolynomial.C : Ω →+* MvPolynomial K Ω), hn, map_zero]`. Establish `h' : (n : ℤ) ∈ (mCoordIdeal y).comap (MvPolynomial.C : ℤ →+* MRing ι)` using `hmem`. Rewrite `h'` using `[h]`.

Conclude with `(Submodule.mem_bot _).mp h'` after adjusting the coercions.
-/
theorem charZero_of_isHorizontal {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    (y : (Σ k, ι k) → Ω) (h : IsHorizontal (mCoordIdeal y)) : CharZero Ω := by
  refine charZero_of_inj_zero fun n hn => ?_
  have hmem : (MvPolynomial.C (n : ℤ) : MRing ι) ∈ mCoordIdeal y := by
    show mConeMap y (MvPolynomial.C (n : ℤ)) = 0
    rw [mConeMap, MvPolynomial.aeval_C, eq_intCast, Int.cast_natCast, ← map_natCast (MvPolynomial.C : Ω →+* MvPolynomial K Ω), hn,
      map_zero]
  have h' : (n : ℤ) ∈ (mCoordIdeal y).comap (MvPolynomial.C : ℤ →+* MRing ι) := hmem
  rw [h] at h'
  exact_mod_cast (Submodule.mem_bot _).mp h'

/- English proof (translation)
Introduce `K _ ι _ Ω _ y D A P0 II hD hII har hb hP0 hs hnef hc`. Distinguish the cases in `hbig : 0 < genDeg (mCoordIdeal y) D A.a`. Establish `: CharZero Ω` using `charZero_of_isHorizontal y har.2.2.1`. Conclude with `hB K ι Ω y D A P0 II hD hII har hb ⟨hP0, hs, hc, hnef, hbig⟩`. Conclude with `hZ K ι Ω y D A P0 II hD hII har hb hP0 hs hnef hc (not_lt.mp hbig)`.
-/
theorem ArithmeticVolumeBig.proof (hB : G6.StatementB) (hZ : ArithmeticVolumeDegreeZero.Statement) : ArithmeticVolumeBig.Statement := by
  intro K _ ι _ Ω _ y D A P0 II hD hII har hb hP0 hs hnef hc
  by_cases hbig : 0 < genDeg (mCoordIdeal y) D A.a
  · have : CharZero Ω := charZero_of_isHorizontal y har.2.2.1
    exact hB K ι Ω y D A P0 II hD hII har hb ⟨hP0, hs, hc, hnef, hbig⟩
  · exact hZ K ι Ω y D A P0 II hD hII har hb hP0 hs hnef hc (not_lt.mp hbig)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
