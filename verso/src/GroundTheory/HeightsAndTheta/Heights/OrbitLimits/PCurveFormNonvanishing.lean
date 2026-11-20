import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsCurveFormNonvanishing
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.PCoordCurveDegree
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBigIffGenDeg
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

namespace CurveFormNonvanishing

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

/- English proof (translation)
Use `conv_lhs => rw [g.as_sum]`. Use `conv_rhs => rw [g.as_sum]`. Rewrite using `[eval₂_sum, eval₂_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun m hm ↦ ?_` and prove the remaining obligations. Rewrite using `[eval₂_monomial, eval₂_monomial, Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _), Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _)]`.

Establish `h1 : ∏ p, (w p / w ⟨p.1, c p.1⟩) ^ m p = (∏ p, w p ^ m p) / ∏ k, w ⟨k, c k⟩ ^ d k`. Simplify using `only [div_pow, Finset.prod_div_distrib]`. Use `congr 1`. Rewrite using `[Fintype.prod_sigma]`. Use `Finset.prod_congr rfl fun k _ ↦ ?_` and prove the remaining obligations.

Rewrite using `[← hg m hm k]`. Conclude with `Finset.prod_pow_eq_pow_sum Finset.univ (fun i ↦ m ⟨k, i⟩) (w ⟨k, c k⟩)`. Establish `h3 : ∏ k, w ⟨k, c k⟩ ^ d k ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hw k)`. Rewrite using `[h1]`. Clear the denominators using the available nonvanishing facts.
-/
theorem eval₂_multiHomog {L : Type*} [Field L] (f : ℤ →+* L) {g : MRing ι} {d : K → ℕ}
    (hg : IsMultiHomog g d) (c : ∀ k, ι k) (w : (Σ k, ι k) → L) (hw : ∀ k, w ⟨k, c k⟩ ≠ 0) :
    eval₂ f w g = (∏ k, w ⟨k, c k⟩ ^ d k) * eval₂ f (fun p ↦ w p / w ⟨p.1, c p.1⟩) g := by
  conv_lhs => rw [g.as_sum]
  conv_rhs => rw [g.as_sum]
  rw [eval₂_sum, eval₂_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  rw [eval₂_monomial, eval₂_monomial, Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _),
    Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _)]
  have h1 : ∏ p, (w p / w ⟨p.1, c p.1⟩) ^ m p = (∏ p, w p ^ m p) / ∏ k, w ⟨k, c k⟩ ^ d k := by
    simp only [div_pow, Finset.prod_div_distrib]
    congr 1
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ ↦ ?_
    rw [← hg m hm k]
    exact Finset.prod_pow_eq_pow_sum Finset.univ (fun i ↦ m ⟨k, i⟩) (w ⟨k, c k⟩)
  have h3 : ∏ k, w ⟨k, c k⟩ ^ d k ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hw k)
  rw [h1]
  field_simp

end CurveFormNonvanishing

/- English proof (translation)
Introduce `K _ ι _ Ω _ y d g hP hg hgy z hz`. Use `HilbertSamuel.BigIffGenDeg.charZero_of_isArithVar hP` as an intermediate fact. Use `choose c hc using HilbertSamuel.BigIffGenDeg.coord_ne_zero_of_isArithVar hP`. Take `⟨φ, hφ, hzc⟩` from `IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree.exists_ptOf hP hc hz`. Establish `hF : eval₂ (Int.castRingHom _) (IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree.ratioF y c) g ≠ 0`.

Introduce `h0`. Establish `h` using `congrArg (algebraMap (blockFnField y) Ω) h0`. Rewrite `h` using `[map_zero, eval₂_comp_left]`. Establish `hy` using `CurveFormNonvanishing.eval₂_multiHomog (Int.castRingHom Ω) hg c y hc`. Establish `e : eval₂ ((algebraMap (blockFnField y) Ω).comp (Int.castRingHom _)) (algebraMap _ Ω ∘ IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree.ratioF y c) g = eval₂ (Int.castRingHom Ω) (fun p ↦ y p / y ⟨p.1, c p.1⟩) g`.

Use `congr 1`. Rewrite `h` using `[e]`. Rewrite `hy` using `[h, mul_zero]`. Conclude with `hgy (by rw [aeval_def, algebraMap_int_eq, hy])`. Establish `hpt : eval₂ (Int.castRingHom ℂ) (IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree.ptOf y c φ) g ≠ 0`.

Establish `h` using `(map_ne_zero_iff (φ : blockFnField y →+* ℂ) φ.toRingHom.injective).mpr hF`. Rewrite `h` using `[eval₂_comp_left]`. Use `h using 2` and compare the differences between its conclusion and the goal. Conclude with `RingHom.ext_int _ _`. Both sides reduce to the same expression.

Rewrite using `[eval_map, CurveFormNonvanishing.eval₂_multiHomog (Int.castRingHom ℂ) hg c z hzc]`. Use `mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hzc k)) ?_` and prove the remaining obligations. Establish `e : (fun p ↦ z p / z ⟨p.1, c p.1⟩) = IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree.ptOf y c φ`. Rewrite using `[hφ]`. Use function extensionality and compare the values at `p`.

Rewrite using `[div_eq_inv_mul]`. Rewrite using `[e]`. Conclude with `hpt`.
-/
theorem CurveFormNonvanishing.proof : CurveFormNonvanishing.Statement := by
  intro K _ ι _ Ω _ y d g hP hg hgy z hz
  have := HilbertSamuel.BigIffGenDeg.charZero_of_isArithVar hP
  choose c hc using HilbertSamuel.BigIffGenDeg.coord_ne_zero_of_isArithVar hP
  obtain ⟨φ, hφ, hzc⟩ := IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree.exists_ptOf hP hc hz

  have hF : eval₂ (Int.castRingHom _) (IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree.ratioF y c) g ≠ 0 := by
    intro h0
    have h := congrArg (algebraMap (blockFnField y) Ω) h0
    rw [map_zero, eval₂_comp_left] at h
    have hy := CurveFormNonvanishing.eval₂_multiHomog (Int.castRingHom Ω) hg c y hc
    have e : eval₂ ((algebraMap (blockFnField y) Ω).comp (Int.castRingHom _))
        (algebraMap _ Ω ∘ IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree.ratioF y c) g =
        eval₂ (Int.castRingHom Ω) (fun p ↦ y p / y ⟨p.1, c p.1⟩) g := by
      congr 1
    rw [e] at h
    rw [h, mul_zero] at hy
    exact hgy (by rw [aeval_def, algebraMap_int_eq, hy])

  have hpt : eval₂ (Int.castRingHom ℂ) (IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree.ptOf y c φ) g ≠ 0 := by
    have h := (map_ne_zero_iff (φ : blockFnField y →+* ℂ) φ.toRingHom.injective).mpr hF
    rw [eval₂_comp_left] at h
    convert h using 2
    · exact RingHom.ext_int _ _
    · rfl
  rw [eval_map, CurveFormNonvanishing.eval₂_multiHomog (Int.castRingHom ℂ) hg c z hzc]
  refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hzc k)) ?_
  have e : (fun p ↦ z p / z ⟨p.1, c p.1⟩) = IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree.ptOf y c φ := by
    rw [hφ]
    funext p
    rw [div_eq_inv_mul]
  rw [e]
  exact hpt

end

end GroundTheory.Heights₂.Heights.Targets
