import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.CurveVerticalPointChart
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsCurveRingFinite
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsCurveClosedPointChart
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLiftBirationalAmple
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.PCurveDivVertical
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo CurveVerticalPointChart

noncomputable section

/- English proof (translation)
Introduce `K _ ι _ Ω _ y s d hy hs hsP W hW c hc`. Establish `hWp : W.IsPrime` using `hW.1.1.1`. Establish `hPW : mCoordIdeal y ≤ W` using `le_sup_left.trans hW.1.1.2`. Establish `hyc : ∀ k, y ⟨k, c k⟩ ≠ 0` using `fun k => ne_zero_of_X_notMem fun h => hc k (hPW h)`. Establish `hv` using `IndefiniteRowSideFullHecke.HeightsSet.CurveDivVertical.full K ι (mCoordIdeal y) s d hy hs hsP W hW`.

Rewrite `hv` using `[IsHorizontal, ← Ne, Submodule.ne_bot_iff]`. Take `⟨n, hn, hn0⟩` from `hv`. Establish `hmax` using `chartPrimeB_isMaximal y (hF K ι Ω y hy) hPW hWp hc hyc hn0 (Ideal.mem_comap.mp hn)`. Rewrite using `[curvePtIdeal_eq y hPW hWp hc hyc]`. Establish `hmp : (chartPrimeB y c W hyc).IsPrime` using `hmax.isPrime`.

Establish `hrat : ∀ p : Σ k, ι k, y p / y ⟨p.1, c p.1⟩ ∈ locSub y _ hmp`. Take `⟨c', hyc', h'⟩` from `hCP K ι Ω y hy _ hmax`. Establish `hinv : ∀ k, y ⟨k, c' k⟩ / y ⟨k, c k⟩ ∈ locSub y _ hmp`. Introduce `k`. Take `⟨a, b, hb, hab⟩` from `h' ⟨k, c k⟩`.

Establish `hab0 : (b : Ω) * (y ⟨k, c k⟩ / y ⟨k, c' k⟩) = a` using `hab`. Establish `hab' : (a : Ω) * y ⟨k, c' k⟩ = b * y ⟨k, c k⟩`. Rewrite using `[← hab0]`. Clear denominators, using `[hyc' k]` for the nonvanishing conditions. Use `mem_locSub.mpr ⟨b, a, ?_, ?_⟩` and prove the remaining obligations.

Introduce `ha`. Take `⟨e, g, hg, hgW, he⟩` from `mem_chartPrimeB.mp ha`. Take `⟨f, w, hw, hbw⟩` from `exists_rep y hyc (mem_chart y hyc b)`. Apply `hb` to reduce the goal to its premises. Use `mem_chartPrimeB.mpr ⟨f, w, hw, ?_, hbw⟩` and prove the remaining obligations.

Establish `h1 : X ⟨k, c k⟩ * (HilbertSamuel.SmallSectionsNonzero.chartMono c e * w) ∈ W`. Use `mem_of_aeval_eq y hPW (Inter.AvoidRing.isMultiHomog_mul (Inter.AvoidRing.isMultiHomog_mul hg (Inter.AvoidRing.isMultiHomog_X k (c' k))) (HilbertSamuel.SmallSectionsNonzero.isMultiHomog_chartMono c f)) (Inter.AvoidRing.isMultiHomog_mul (Inter.AvoidRing.isMultiHomog_X k (c k)) (Int …` and prove the remaining obligations. Simplify using `only [map_mul, aeval_X, HilbertSamuel.SmallSectionsNonzero.aeval_chartMono]`. Take the linear combination `(-(y ⟨k, c' k⟩ * ∏ k, y ⟨k, c k⟩ ^ f k)) * he + (y ⟨k, c k⟩ * ∏ k, y ⟨k, c k⟩ ^ e k) * hbw + ((∏ k, y ⟨k, c k⟩ ^ e k) * ∏ k, y ⟨k, c k⟩ ^ f k) * hab'`. Conclude with `mem_of_chartMono_mul hWp hc ((hWp.mem_or_mem h1).resolve_left (hc k))`.

Rewrite using `[← hab0]`. Clear denominators, using `[hyc' k, hyc k]` for the nonvanishing conditions. Introduce `p`. Take `⟨a, b, hb, hab⟩` from `h' p`. Establish `hu : y p / y ⟨p.1, c' p.1⟩ ∈ locSub y _ hmp` using `mem_locSub.mpr ⟨a, b, hb, hab⟩`.

Establish `hprod` using `mul_mem hu (hinv p.1)`. Establish `he : y p / y ⟨p.1, c' p.1⟩ * (y ⟨p.1, c' p.1⟩ / y ⟨p.1, c p.1⟩) = y p / y ⟨p.1, c p.1⟩`. Clear denominators, using `[hyc' p.1, hyc p.1]` for the nonvanishing conditions. Rewrite `hprod` using `[he]`. Then use the resulting hypothesis. Establish `hY : ∀ e : K → ℕ, ∏ k, y ⟨k, c k⟩ ^ e k ≠ 0` using `fun e => Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hyc k)`.

Use `⟨hmax, fun p => mem_locSub.mp (hrat p), fun e g hg => ⟨fun hgW => ?_, ?_⟩⟩` and prove the remaining obligations. Establish `hr : aeval y g * ∏ k, y ⟨k, c k⟩ ^ (-(e k : ℤ)) ∈ chartRingZ y c` using `(HilbertSamuel.LiftBirationalAmple.mem_chartLat_one y).mp (HilbertSamuel.LiftBirationalAmple.chartLat_form hg) c hyc`. Establish `hinv : ∏ k, y ⟨k, c k⟩ ^ (-(e k : ℤ)) = (∏ k, y ⟨k, c k⟩ ^ e k)⁻¹`. Rewrite using `[← Finset.prod_inv_distrib]`. Conclude with `Finset.prod_congr rfl fun k _ => by rw [zpow_neg, zpow_natCast]`.

Rewrite `hr` using `[hinv]`. Take `⟨a, b, hb, hab⟩` from `mem_locSub.mp (chart_le_locSub y _ hmp c hrat hr)`. Establish `hab' : (b : Ω) * aeval y g = a * ∏ k, y ⟨k, c k⟩ ^ e k`. Rewrite using `[← hab]`. Clear denominators, using `[hY e]` for the nonvanishing conditions.

Use `⟨a, b, ?_, hb, hab'⟩` and prove the remaining obligations. Take `⟨f, w, hw, hbw⟩` from `exists_rep y hyc (mem_chart y hyc b)`. Use `mem_chartPrimeB.mpr ⟨f + e, w * g, Inter.AvoidRing.isMultiHomog_mul hw hg, W.mul_mem_left _ hgW, ?_⟩` and prove the remaining obligations. Rewrite using `[prod_pow_add, map_mul]`. Take the linear combination `(-(∏ k, y ⟨k, c k⟩ ^ f k)) * hab' + (aeval y g) * hbw`.

Introduce and unpack `⟨a, b, ha, hb, hab⟩`. Take `⟨f, v, hv, hvW, hav⟩` from `mem_chartPrimeB.mp ha`. Take `⟨f', w, hw, hbw⟩` from `exists_rep y hyc (mem_chart y hyc b)`. Establish `hwW : w ∉ W` using `fun h => hb (mem_chartPrimeB.mpr ⟨f', w, hw, h, hbw⟩)`. Establish `h1 : HilbertSamuel.SmallSectionsNonzero.chartMono c f * (w * g) ∈ W`.

Use `mem_of_aeval_eq y hPW (Inter.AvoidRing.isMultiHomog_mul (Inter.AvoidRing.isMultiHomog_mul (HilbertSamuel.SmallSectionsNonzero.isMultiHomog_chartMono c e) (HilbertSamuel.SmallSectionsNonzero.isMultiHomog_chartMono c f')) hv) (Inter.AvoidRing.isMultiHomog_mul (HilbertSamuel.SmallSe …` and prove the remaining obligations. Simplify using `only [map_mul, HilbertSamuel.SmallSectionsNonzero.aeval_chartMono]`. Take the linear combination `(-((∏ k, y ⟨k, c k⟩ ^ e k) * ∏ k, y ⟨k, c k⟩ ^ f' k)) * hav + ((∏ k, y ⟨k, c k⟩ ^ f k) * aeval y g) * hbw - ((∏ k, y ⟨k, c k⟩ ^ f k) * ∏ k, y ⟨k, c k⟩ ^ f' k) * hab`. Conclude with `(hWp.mem_or_mem (mem_of_chartMono_mul hWp hc h1)).resolve_left hwW`.
-/
theorem CurveVertPointChart.proof (hF : CurveRingFinite.Statement) (hCP : CurveClosedPointChart.Statement) :
    CurveVertPointChart.Statement := by
  classical
  intro K _ ι _ Ω _ y s d hy hs hsP W hW c hc
  have hWp : W.IsPrime := hW.1.1.1
  have hPW : mCoordIdeal y ≤ W := le_sup_left.trans hW.1.1.2
  have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => ne_zero_of_X_notMem fun h => hc k (hPW h)

  have hv := IndefiniteRowSideFullHecke.HeightsSet.CurveDivVertical.full K ι (mCoordIdeal y) s d hy hs hsP W hW
  rw [IsHorizontal, ← Ne, Submodule.ne_bot_iff] at hv
  obtain ⟨n, hn, hn0⟩ := hv
  have hmax := chartPrimeB_isMaximal y (hF K ι Ω y hy) hPW hWp hc hyc hn0 (Ideal.mem_comap.mp hn)
  rw [curvePtIdeal_eq y hPW hWp hc hyc]
  have hmp : (chartPrimeB y c W hyc).IsPrime := hmax.isPrime

  have hrat : ∀ p : Σ k, ι k, y p / y ⟨p.1, c p.1⟩ ∈ locSub y _ hmp := by
    obtain ⟨c', hyc', h'⟩ := hCP K ι Ω y hy _ hmax
    have hinv : ∀ k, y ⟨k, c' k⟩ / y ⟨k, c k⟩ ∈ locSub y _ hmp := by
      intro k
      obtain ⟨a, b, hb, hab⟩ := h' ⟨k, c k⟩
      have hab0 : (b : Ω) * (y ⟨k, c k⟩ / y ⟨k, c' k⟩) = a := hab
      have hab' : (a : Ω) * y ⟨k, c' k⟩ = b * y ⟨k, c k⟩ := by
        rw [← hab0]
        field_simp [hyc' k]
      refine mem_locSub.mpr ⟨b, a, ?_, ?_⟩
      · intro ha
        obtain ⟨e, g, hg, hgW, he⟩ := mem_chartPrimeB.mp ha
        obtain ⟨f, w, hw, hbw⟩ := exists_rep y hyc (mem_chart y hyc b)
        apply hb
        refine mem_chartPrimeB.mpr ⟨f, w, hw, ?_, hbw⟩
        have h1 : X ⟨k, c k⟩ * (HilbertSamuel.SmallSectionsNonzero.chartMono c e * w) ∈ W := by
          refine mem_of_aeval_eq y hPW
            (Inter.AvoidRing.isMultiHomog_mul (Inter.AvoidRing.isMultiHomog_mul hg
              (Inter.AvoidRing.isMultiHomog_X k (c' k)))
              (HilbertSamuel.SmallSectionsNonzero.isMultiHomog_chartMono c f))
            (Inter.AvoidRing.isMultiHomog_mul (Inter.AvoidRing.isMultiHomog_X k (c k))
              (Inter.AvoidRing.isMultiHomog_mul
                (HilbertSamuel.SmallSectionsNonzero.isMultiHomog_chartMono c e) hw))
            (by abel) ?_ (W.mul_mem_right _ (W.mul_mem_right _ hgW))
          simp only [map_mul, aeval_X, HilbertSamuel.SmallSectionsNonzero.aeval_chartMono]
          linear_combination (-(y ⟨k, c' k⟩ * ∏ k, y ⟨k, c k⟩ ^ f k)) * he +
            (y ⟨k, c k⟩ * ∏ k, y ⟨k, c k⟩ ^ e k) * hbw +
            ((∏ k, y ⟨k, c k⟩ ^ e k) * ∏ k, y ⟨k, c k⟩ ^ f k) * hab'
        exact mem_of_chartMono_mul hWp hc ((hWp.mem_or_mem h1).resolve_left (hc k))
      · rw [← hab0]
        field_simp [hyc' k, hyc k]
    intro p
    obtain ⟨a, b, hb, hab⟩ := h' p
    have hu : y p / y ⟨p.1, c' p.1⟩ ∈ locSub y _ hmp := mem_locSub.mpr ⟨a, b, hb, hab⟩
    have hprod := mul_mem hu (hinv p.1)
    have he : y p / y ⟨p.1, c' p.1⟩ * (y ⟨p.1, c' p.1⟩ / y ⟨p.1, c p.1⟩) = y p / y ⟨p.1, c p.1⟩ := by
      field_simp [hyc' p.1, hyc p.1]
    rwa [he] at hprod
  have hY : ∀ e : K → ℕ, ∏ k, y ⟨k, c k⟩ ^ e k ≠ 0 := fun e =>
    Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hyc k)
  refine ⟨hmax, fun p => mem_locSub.mp (hrat p), fun e g hg => ⟨fun hgW => ?_, ?_⟩⟩
  · have hr : aeval y g * ∏ k, y ⟨k, c k⟩ ^ (-(e k : ℤ)) ∈ chartRingZ y c :=
      (HilbertSamuel.LiftBirationalAmple.mem_chartLat_one y).mp
        (HilbertSamuel.LiftBirationalAmple.chartLat_form hg) c hyc
    have hinv : ∏ k, y ⟨k, c k⟩ ^ (-(e k : ℤ)) = (∏ k, y ⟨k, c k⟩ ^ e k)⁻¹ := by
      rw [← Finset.prod_inv_distrib]
      exact Finset.prod_congr rfl fun k _ => by rw [zpow_neg, zpow_natCast]
    rw [hinv] at hr
    obtain ⟨a, b, hb, hab⟩ := mem_locSub.mp (chart_le_locSub y _ hmp c hrat hr)
    have hab' : (b : Ω) * aeval y g = a * ∏ k, y ⟨k, c k⟩ ^ e k := by
      rw [← hab]
      field_simp [hY e]
    refine ⟨a, b, ?_, hb, hab'⟩
    obtain ⟨f, w, hw, hbw⟩ := exists_rep y hyc (mem_chart y hyc b)
    refine mem_chartPrimeB.mpr ⟨f + e, w * g, Inter.AvoidRing.isMultiHomog_mul hw hg, W.mul_mem_left _ hgW, ?_⟩
    rw [prod_pow_add, map_mul]
    linear_combination (-(∏ k, y ⟨k, c k⟩ ^ f k)) * hab' + (aeval y g) * hbw
  · rintro ⟨a, b, ha, hb, hab⟩
    obtain ⟨f, v, hv, hvW, hav⟩ := mem_chartPrimeB.mp ha
    obtain ⟨f', w, hw, hbw⟩ := exists_rep y hyc (mem_chart y hyc b)
    have hwW : w ∉ W := fun h => hb (mem_chartPrimeB.mpr ⟨f', w, hw, h, hbw⟩)
    have h1 : HilbertSamuel.SmallSectionsNonzero.chartMono c f * (w * g) ∈ W := by
      refine mem_of_aeval_eq y hPW
        (Inter.AvoidRing.isMultiHomog_mul (Inter.AvoidRing.isMultiHomog_mul
          (HilbertSamuel.SmallSectionsNonzero.isMultiHomog_chartMono c e)
          (HilbertSamuel.SmallSectionsNonzero.isMultiHomog_chartMono c f')) hv)
        (Inter.AvoidRing.isMultiHomog_mul (HilbertSamuel.SmallSectionsNonzero.isMultiHomog_chartMono c f)
          (Inter.AvoidRing.isMultiHomog_mul hw hg))
        (by abel) ?_ (W.mul_mem_left _ hvW)
      simp only [map_mul, HilbertSamuel.SmallSectionsNonzero.aeval_chartMono]
      linear_combination (-((∏ k, y ⟨k, c k⟩ ^ e k) * ∏ k, y ⟨k, c k⟩ ^ f' k)) * hav +
        ((∏ k, y ⟨k, c k⟩ ^ f k) * aeval y g) * hbw -
        ((∏ k, y ⟨k, c k⟩ ^ f k) * ∏ k, y ⟨k, c k⟩ ^ f' k) * hab
    exact (hWp.mem_or_mem (mem_of_chartMono_mul hWp hc h1)).resolve_left hwW

end

end GroundTheory.Heights₂.Heights.Targets
