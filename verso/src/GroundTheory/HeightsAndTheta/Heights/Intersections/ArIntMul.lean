import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.NotIsHorizontalOfDimOne
import GroundTheory.HeightsAndTheta.Heights.Intersections.PConsequences
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

/- English proof (translation)
Take `⟨a, -, hsa, hsP⟩` from `id hs`. Take `⟨b, -, htb, htP⟩` from `id ht`. Use `show ptsIntegral P (pot L) _ = ptsIntegral P (pot L) _ + ptsIntegral P (pot L) _`. Unfold `ptsIntegral`. Use `split_ifs with hΨ`.

Establish `hΨg : IsGoodProj P hΨ.choose` using `hΨ.choose_spec`. Unfold `ptsIntegralAt`. Rewrite using `[← integral_add (hInt K ι P n _ L A s hP hΨg hL hA hs) (hInt K ι P n _ L B t hP hΨg hL hB ht)]`. Use `integral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [ae_eval_ne_zero hP hΨg ⟨a, hsa⟩ hsP, ae_eval_ne_zero hP hΨg ⟨b, htb⟩ htP] with y hys hyt`.

Rewrite using `[← finsum_mem_add_distrib' ((fibreFinite K ι P n _ hP hΨg y).subset Set.inter_subset_left) ((fibreFinite K ι P n _ hP hΨg y).subset Set.inter_subset_left)]`. Use `finsum_mem_congr rfl fun w _ ↦ ?_` and prove the remaining obligations. Unfold `sheetDensity`. Use `split_ifs with hγ`. Establish `hsh` using `hγ.choose_spec.2.self_of_nhds set z := hγ.choose y`.

Establish `hz : z ∈ mcPts P` using `hsh.2.1`. Establish `hs0` using `norm_pos_iff.mpr (hys z hz hsh.2.2)`. Establish `ht0` using `norm_pos_iff.mpr (hyt z hz hsh.2.2)`. Establish `hA0` using `A.pos z hz.1`. Establish `hB0` using `B.pos z hz.1`.

Rewrite using `[← add_mul]`. Use `congr 1`. Use `show Real.log (‖eval z (map (Int.castRingHom ℂ) (s * t))‖ / (A.h z * B.h z)) = Real.log (‖eval z (map (Int.castRingHom ℂ) s)‖ / A.h z) + Real.log (‖eval z (map (Int.castRingHom ℂ) t)‖ / B.h z)`. Rewrite using `[map_mul, map_mul, norm_mul, mul_div_mul_comm]`. Conclude with `Real.log_mul (div_pos hs0 hA0).ne' (div_pos ht0 hB0).ne'`.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem arInt_mul (hInt : PtsIntegrableStatement) {P : Ideal (MRing ι)} {n : ℕ}
    (hP : IsArithVar P (n + 1)) {L : Fin n → HermLine ι} (hL : ∀ j, IsSmoothHerm (L j))
    {A B : HermLine ι} (hA : IsSmoothHerm A) (hB : IsSmoothHerm B) {s t : MRing ι}
    (hs : IsSectionOn P A s) (ht : IsSectionOn P B t) :
    arInt P (s * t) (A.tensor B) L = arInt P s A L + arInt P t B L := by
  obtain ⟨a, -, hsa, hsP⟩ := id hs
  obtain ⟨b, -, htb, htP⟩ := id ht
  show ptsIntegral P (pot L) _ = ptsIntegral P (pot L) _ + ptsIntegral P (pot L) _
  unfold ptsIntegral
  split_ifs with hΨ
  · have hΨg : IsGoodProj P hΨ.choose := hΨ.choose_spec
    unfold ptsIntegralAt
    rw [← integral_add (hInt K ι P n _ L A s hP hΨg hL hA hs) (hInt K ι P n _ L B t hP hΨg hL hB ht)]
    refine integral_congr_ae ?_
    filter_upwards [ae_eval_ne_zero hP hΨg ⟨a, hsa⟩ hsP, ae_eval_ne_zero hP hΨg ⟨b, htb⟩ htP]
      with y hys hyt
    rw [← finsum_mem_add_distrib' ((fibreFinite K ι P n _ hP hΨg y).subset Set.inter_subset_left)
      ((fibreFinite K ι P n _ hP hΨg y).subset Set.inter_subset_left)]
    refine finsum_mem_congr rfl fun w _ ↦ ?_
    unfold sheetDensity
    split_ifs with hγ
    · have hsh := hγ.choose_spec.2.self_of_nhds
      set z := hγ.choose y
      have hz : z ∈ mcPts P := hsh.2.1
      have hs0 := norm_pos_iff.mpr (hys z hz hsh.2.2)
      have ht0 := norm_pos_iff.mpr (hyt z hz hsh.2.2)
      have hA0 := A.pos z hz.1
      have hB0 := B.pos z hz.1
      rw [← add_mul]
      congr 1
      show Real.log (‖eval z (map (Int.castRingHom ℂ) (s * t))‖ / (A.h z * B.h z)) =
        Real.log (‖eval z (map (Int.castRingHom ℂ) s)‖ / A.h z) +
          Real.log (‖eval z (map (Int.castRingHom ℂ) t)‖ / B.h z)
      rw [map_mul, map_mul, norm_mul, mul_div_mul_comm]
      exact Real.log_mul (div_pos hs0 hA0).ne' (div_pos ht0 hB0).ne'
    · simp
  · simp

/- English proof (translation)
Introduce `K _ ι _ I P n L A B s t hP hL hA hB hs ht`. Take `⟨-, -, -, hsP⟩` from `id hs`. Take `⟨-, -, -, htP⟩` from `id ht`. Rewrite using `[recR_eq, recR_eq, recR_eq, cycR_mul I hP.2.1.1 L hsP htP, arInt_mul hInt hP hL hA hB hs ht]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem RMul.proof (hInt : PtsIntegrableStatement) : RMulStatement := by
  intro K _ ι _ I P n L A B s t hP hL hA hB hs ht
  obtain ⟨-, -, -, hsP⟩ := id hs
  obtain ⟨-, -, -, htP⟩ := id ht
  rw [recR_eq, recR_eq, recR_eq, cycR_mul I hP.2.1.1 L hsP htP, arInt_mul hInt hP hL hA hB hs ht]
  ring

end GroundTheory.Heights₂.Heights.Inter
