import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDerived
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSupp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterFib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedF
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.Intersections.ConservationDegreeFormOfExistence
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

omit [∀ k, Fintype (ι k)] in

/- English proof (translation)
Unfold `ptsIntegral ptsIntegralAt`. Use `split_ifs with hΨ`. Use `congr 1`. Use function extensionality and compare the values at `y`. Use `finsum_congr fun w ↦ finsum_congr fun _ ↦ ?_` and prove the remaining obligations.

Unfold `sheetDensity`. Use `split_ifs with hγ`. Use `congr 1`. Conclude with `hg _ hγ.choose_spec.2.self_of_nhds.2.1`. Both sides reduce to the same expression.

Both sides reduce to the same expression.
-/
theorem ptsIntegral_congr_pts (P : Ideal (MRing ι)) {e : ℕ} (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ)
    {g g' : ((Σ k, ι k) → ℂ) → ℝ} (hg : ∀ z ∈ mcPts P, g z = g' z) :
    ptsIntegral P φ g = ptsIntegral P φ g' := by
  unfold ptsIntegral ptsIntegralAt
  split_ifs with hΨ
  · congr 1
    funext y
    refine finsum_congr fun w ↦ finsum_congr fun _ ↦ ?_
    unfold sheetDensity
    split_ifs with hγ
    · congr 1
      exact hg _ hγ.choose_spec.2.self_of_nhds.2.1
    · rfl
  · rfl

/- English proof (translation)
Unfold `cycR vertR`. Rewrite using `[finsum_mem_eq_finite_toFinset_sum _ (divSupp_finite P s), finsum_mem_eq_finite_toFinset_sum _ (divSupp_finite P s), ← Finset.sum_sub_distrib, Finset.sum_filter]`. Use `Finset.sum_congr rfl fun W _ ↦ ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> ring`.
-/
theorem cycR_sub_vertR (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (P : Ideal (MRing ι))
    {n : ℕ} (L : Fin n → HermLine ι) (s : MRing ι) [DecidablePred (IsHorizontal (ι := ι))] :
    cycR I P L s - vertR P L s = ∑ W ∈ (divSupp_finite P s).toFinset.filter IsHorizontal,
      (multAt (P ⊔ Ideal.span {s}) W : ℝ) * I W n L := by
  unfold cycR vertR
  rw [finsum_mem_eq_finite_toFinset_sum _ (divSupp_finite P s),
    finsum_mem_eq_finite_toFinset_sum _ (divSupp_finite P s), ← Finset.sum_sub_distrib, Finset.sum_filter]
  refine Finset.sum_congr rfl fun W _ ↦ ?_
  split_ifs <;> ring

/- English proof (translation)
Use `show A.a k + (β k : ℤ) = α k`. Rewrite using `[← h k]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem tensor_sqMetric_a {A : HermLine ι} {α β : K → ℕ} (h : ∀ k, (α k : ℤ) - β k = A.a k) (k : K) :
    (A.tensor (HermLine.sqMetric β)).a k = α k := by
  show A.a k + (β k : ℤ) = α k
  rw [← h k]
  ring

/- English proof (translation)
The claim follows from `metricChange`.
-/
theorem ArithmeticIntersectionSecond.proof : ArithmeticIntersectionSecond.Statement := metricChange

/- English proof (translation)
The claim follows from `Conservation.statement_holds`.
-/
theorem Conservation.proof : Conservation.Statement := Conservation.statement_holds

/- English proof (translation)
Introduce `K _ ι _ I hI P n L A f g hP hL hA ⟨α, β, hf, hg, hfP, hgP, hαβ⟩ hhor hmult hnorm`. Take `⟨-, hAdd, hR⟩` from `hI`. Establish `hB : IsSmoothHerm (HermLine.sqMetric (ι` using `ι) β) := isSmoothHerm_sqMetric β`. Establish `hRf` using `hR P n L _ f α hP hL (isSmoothHerm_tensor hA hB) (tensor_sqMetric_a hαβ) hf hfP`. Establish `hRg` using `hR P n L _ g β hP hL hB (fun k ↦ rfl) hg hgP`.

Establish `hsum` using `hAdd P n L A _ hP hL hA hB`. Establish `hint : arInt P f (A.tensor (HermLine.sqMetric β)) L = arInt P g (HermLine.sqMetric β) L`. Unfold `arInt`. Use `ptsIntegral_congr_pts P _ fun z hz ↦ ?_` and prove the remaining obligations. Establish `hApos` using `A.pos z hz.1`.

Use `show Real.log (‖eval z (map (Int.castRingHom ℂ) f)‖ / (A.h z * (HermLine.sqMetric β).h z)) = Real.log (‖eval z (map (Int.castRingHom ℂ) g)‖ / (HermLine.sqMetric β).h z)`. Rewrite using `[hnorm z hz, mul_comm (A.h z), mul_div_mul_right _ _ hApos.ne']`. Establish `hS : (divSupp_finite P f).toFinset.filter IsHorizontal = (divSupp_finite P g).toFinset.filter IsHorizontal`. Use extensionality with `W`. Simplify using `only [Finset.mem_filter, Set.Finite.mem_toFinset]`.

Conclude with `⟨fun h ↦ ⟨(hhor W h.2).1 h.1, h.2⟩, fun h ↦ ⟨(hhor W h.2).2 h.1, h.2⟩⟩`. Establish `hcyc : cycR I P L f - vertR P L f = cycR I P L g - vertR P L g`. Rewrite using `[cycR_sub_vertR, cycR_sub_vertR, hS]`. Use `Finset.sum_congr rfl fun W hW ↦ ?_` and prove the remaining obligations. Rewrite `hW` using `[Finset.mem_filter, Set.Finite.mem_toFinset]`.

Rewrite using `[hmult W hW.2 ((hhor W hW.2).2 hW.1)]`. Rewrite `hRf`, `hRg` using `[recR_eq]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem InductiveIntersectionFormula.proof : InductiveIntersectionFormula.Statement := by
  classical
  intro K _ ι _ I hI P n L A f g hP hL hA ⟨α, β, hf, hg, hfP, hgP, hαβ⟩ hhor hmult hnorm
  obtain ⟨-, hAdd, hR⟩ := hI
  have hB : IsSmoothHerm (HermLine.sqMetric (ι := ι) β) := isSmoothHerm_sqMetric β
  have hRf := hR P n L _ f α hP hL (isSmoothHerm_tensor hA hB) (tensor_sqMetric_a hαβ) hf hfP
  have hRg := hR P n L _ g β hP hL hB (fun k ↦ rfl) hg hgP
  have hsum := hAdd P n L A _ hP hL hA hB
  have hint : arInt P f (A.tensor (HermLine.sqMetric β)) L = arInt P g (HermLine.sqMetric β) L := by
    unfold arInt
    refine ptsIntegral_congr_pts P _ fun z hz ↦ ?_
    have hApos := A.pos z hz.1
    show Real.log (‖eval z (map (Int.castRingHom ℂ) f)‖ / (A.h z * (HermLine.sqMetric β).h z)) =
      Real.log (‖eval z (map (Int.castRingHom ℂ) g)‖ / (HermLine.sqMetric β).h z)
    rw [hnorm z hz, mul_comm (A.h z), mul_div_mul_right _ _ hApos.ne']
  have hS : (divSupp_finite P f).toFinset.filter IsHorizontal =
      (divSupp_finite P g).toFinset.filter IsHorizontal := by
    ext W
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset]
    exact ⟨fun h ↦ ⟨(hhor W h.2).1 h.1, h.2⟩, fun h ↦ ⟨(hhor W h.2).2 h.1, h.2⟩⟩
  have hcyc : cycR I P L f - vertR P L f = cycR I P L g - vertR P L g := by
    rw [cycR_sub_vertR, cycR_sub_vertR, hS]
    refine Finset.sum_congr rfl fun W hW ↦ ?_
    rw [Finset.mem_filter, Set.Finite.mem_toFinset] at hW
    rw [hmult W hW.2 ((hhor W hW.2).2 hW.1)]
  rw [recR_eq] at hRf hRg
  linarith

/- English proof (translation)
Introduce `K _ ι _ I hI P A s hP hA ⟨a, ha, hs, hsP⟩`. Establish `hR` using `hI.2.2 P 0 Fin.elim0 A s a hP (fun j ↦ j.elim0) hA ha hs hsP`. Establish `hsnoc : (Fin.snoc (Fin.elim0 : Fin 0 → HermLine ι) A : Fin (0 + 1) → HermLine ι) = ![A]`. Use function extensionality and compare the values at `j`. Use `fin_cases j`.

Both sides reduce to the same expression. Rewrite `hR` using `[hsnoc]`. Rewrite using `[hR, recR_eq]`. Use `congr 1`. Unfold `cycR vertR`.

Use `finsum_mem_congr rfl fun W hW ↦ ?_` and prove the remaining obligations. Establish `hnh : ¬ IsHorizontal W` using `fun hh ↦ h₀ K ι W ((divSuppArith K ι P 0 A s W hP ⟨a, ha, hs, hsP⟩ hW).1 hh)`. Rewrite using `[if_neg hnh, if_neg hnh]`.
-/
theorem ArithmeticIntersectionFifth.proof (h₀ : ArithVarZeroStatement) : ArithmeticIntersectionFifth.Statement := by
  intro K _ ι _ I hI P A s hP hA ⟨a, ha, hs, hsP⟩
  have hR := hI.2.2 P 0 Fin.elim0 A s a hP (fun j ↦ j.elim0) hA ha hs hsP
  have hsnoc : (Fin.snoc (Fin.elim0 : Fin 0 → HermLine ι) A : Fin (0 + 1) → HermLine ι) = ![A] := by
    funext j
    fin_cases j
    rfl
  rw [hsnoc] at hR
  rw [hR, recR_eq]
  congr 1
  unfold cycR vertR
  refine finsum_mem_congr rfl fun W hW ↦ ?_
  have hnh : ¬ IsHorizontal W := fun hh ↦
    h₀ K ι W ((divSuppArith K ι P 0 A s W hP ⟨a, ha, hs, hsP⟩ hW).1 hh)
  rw [if_neg hnh, if_neg hnh]

/- English proof (translation)
Establish `hJ : IsMultiHomogIdeal (Ideal.span {h} : Ideal (MRing ι))` using `⟨{h}, fun f hf ↦ by rw [Set.mem_singleton_iff.mp hf]; exact hh, rfl⟩`. Establish `hJP : ¬ (Ideal.span {h} : Ideal (MRing ι)) ≤ P`. Rewrite using `[Ideal.span_singleton_le_iff_mem]` and apply the resulting hypothesis. Establish `hnull` using `projB_null Ψ hP hΨ hJ hJP`. Use `ae_iff.mpr (measure_mono_null (fun y hy ↦ ?_) hnull)` and prove the remaining obligations.

Simplify using `only [Set.mem_ofPred_eq, not_forall, not_not] at hy`. Take `⟨z, hz, hzy, hz0⟩` from `hy`. Use `⟨z, hz, ⟨hz.1, fun q hq ↦ ?_⟩, hzy⟩` and prove the remaining obligations. Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton'.mp hq`. Simplify using `[hz0]`.
-/
theorem ae_eval_ne_zero {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)} {e : ℕ} {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)}
    (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) {h : MRing ι} (hh : ∃ a, IsMultiHomog h a)
    (hhP : h ∉ P) :
    ∀ᵐ y : Fin e → ℂ, ∀ z ∈ mcPts P, Ψ (segre z) = Fin.cons 1 y →
      eval z (map (Int.castRingHom ℂ) h) ≠ 0 := by
  have hJ : IsMultiHomogIdeal (Ideal.span {h} : Ideal (MRing ι)) :=
    ⟨{h}, fun f hf ↦ by rw [Set.mem_singleton_iff.mp hf]; exact hh, rfl⟩
  have hJP : ¬ (Ideal.span {h} : Ideal (MRing ι)) ≤ P := by
    rwa [Ideal.span_singleton_le_iff_mem]
  have hnull := projB_null Ψ hP hΨ hJ hJP
  refine ae_iff.mpr (measure_mono_null (fun y hy ↦ ?_) hnull)
  simp only [Set.mem_ofPred_eq, not_forall, not_not] at hy
  obtain ⟨z, hz, hzy, hz0⟩ := hy
  refine ⟨z, hz, ⟨hz.1, fun q hq ↦ ?_⟩, hzy⟩
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hq
  simp [hz0]

/- English proof (translation)
Introduce `K _ ι _ I hI P n L A f g hP hL hA ⟨α, β, hf, hg, hfP, hgP, hαβ⟩`. Take `⟨-, hAdd, hR⟩` from `hI`. Establish `hB : IsSmoothHerm (HermLine.sqMetric (ι` using `ι) β) := isSmoothHerm_sqMetric β`. Establish `hAB` using `isSmoothHerm_tensor hA hB`. Establish `hRf` using `hR P n L _ f α hP hL hAB (tensor_sqMetric_a hαβ) hf hfP`.

Establish `hRg` using `hR P n L _ g β hP hL hB (fun k ↦ rfl) hg hgP`. Establish `hsum` using `hAdd P n L A _ hP hL hA hB`. Establish `hint : arInt P f (A.tensor (HermLine.sqMetric β)) L - arInt P g (HermLine.sqMetric β) L = ptsIntegral P (pot L) (logNormRat A f g)` using `by show ptsIntegral P (pot L) _ - ptsIntegral P (pot L) _ = _`. Unfold `ptsIntegral`. Use `split_ifs with hΨ`.

Establish `hΨg : IsGoodProj P hΨ.choose` using `hΨ.choose_spec`. Unfold `ptsIntegralAt`. Rewrite using `[← integral_sub (hInt K ι P n _ L _ f hP hΨg hL hAB ⟨α, tensor_sqMetric_a hαβ, hf, hfP⟩) (hInt K ι P n _ L _ g hP hΨg hL hB ⟨β, fun k ↦ rfl, hg, hgP⟩)]`. Use `integral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [ae_eval_ne_zero hP hΨg ⟨α, hf⟩ hfP, ae_eval_ne_zero hP hΨg ⟨β, hg⟩ hgP] with y hyf hyg`.

Rewrite using `[← finsum_mem_sub_distrib _ _ (fibreFinite K ι P n _ hP hΨg y)]`. Use `finsum_mem_congr rfl fun w _ ↦ ?_` and prove the remaining obligations. Unfold `sheetDensity`. Use `split_ifs with hγ`. Establish `hs` using `hγ.choose_spec.2.self_of_nhds set z := hγ.choose y`.

Establish `hz : z ∈ mcPts P` using `hs.2.1`. Establish `hf0` using `norm_pos_iff.mpr (hyf z hz hs.2.2)`. Establish `hg0` using `norm_pos_iff.mpr (hyg z hz hs.2.2)`. Establish `hA0` using `A.pos z hz.1`. Establish `hB0` using `(HermLine.sqMetric (ι := ι) β).pos z hz.1`.

Rewrite using `[← sub_mul]`. Use `congr 1`. Use `show Real.log (‖eval z (map (Int.castRingHom ℂ) f)‖ / (A.h z * (HermLine.sqMetric β).h z)) - Real.log (‖eval z (map (Int.castRingHom ℂ) g)‖ / (HermLine.sqMetric β).h z) = Real.log (‖eval z (map (Int.castRingHom ℂ) f)‖ / ‖eval z (map (Int.castRingHom ℂ) g)‖ / A.h z)`. Rewrite using `[Real.log_div hf0.ne' (mul_pos hA0 hB0).ne', Real.log_mul hA0.ne' hB0.ne', Real.log_div hg0.ne' hB0.ne', Real.log_div (div_pos hf0 hg0).ne' hA0.ne', Real.log_div hf0.ne' hg0.ne']`. Expand and normalize the polynomial expressions, which then agree.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Unfold `recRRat`. Rewrite `hRf`, `hRg` using `[recR_eq]`. Use `show I P (n + 1) (Fin.snoc L A) = cycR I P L f - cycR I P L g - ptsIntegral P (pot L) (logNormRat A f g)`.

Rewrite using `[← hint]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem RatR.proof (hInt : PtsIntegrableStatement) : RatR.Statement := by
  intro K _ ι _ I hI P n L A f g hP hL hA ⟨α, β, hf, hg, hfP, hgP, hαβ⟩
  obtain ⟨-, hAdd, hR⟩ := hI
  have hB : IsSmoothHerm (HermLine.sqMetric (ι := ι) β) := isSmoothHerm_sqMetric β
  have hAB := isSmoothHerm_tensor hA hB
  have hRf := hR P n L _ f α hP hL hAB (tensor_sqMetric_a hαβ) hf hfP
  have hRg := hR P n L _ g β hP hL hB (fun k ↦ rfl) hg hgP
  have hsum := hAdd P n L A _ hP hL hA hB
  have hint : arInt P f (A.tensor (HermLine.sqMetric β)) L - arInt P g (HermLine.sqMetric β) L =
      ptsIntegral P (pot L) (logNormRat A f g) := by
    show ptsIntegral P (pot L) _ - ptsIntegral P (pot L) _ = _
    unfold ptsIntegral
    split_ifs with hΨ
    · have hΨg : IsGoodProj P hΨ.choose := hΨ.choose_spec
      unfold ptsIntegralAt
      rw [← integral_sub (hInt K ι P n _ L _ f hP hΨg hL hAB ⟨α, tensor_sqMetric_a hαβ, hf, hfP⟩)
        (hInt K ι P n _ L _ g hP hΨg hL hB ⟨β, fun k ↦ rfl, hg, hgP⟩)]
      refine integral_congr_ae ?_
      filter_upwards [ae_eval_ne_zero hP hΨg ⟨α, hf⟩ hfP, ae_eval_ne_zero hP hΨg ⟨β, hg⟩ hgP]
        with y hyf hyg
      rw [← finsum_mem_sub_distrib _ _ (fibreFinite K ι P n _ hP hΨg y)]
      refine finsum_mem_congr rfl fun w _ ↦ ?_
      unfold sheetDensity
      split_ifs with hγ
      · have hs := hγ.choose_spec.2.self_of_nhds
        set z := hγ.choose y
        have hz : z ∈ mcPts P := hs.2.1
        have hf0 := norm_pos_iff.mpr (hyf z hz hs.2.2)
        have hg0 := norm_pos_iff.mpr (hyg z hz hs.2.2)
        have hA0 := A.pos z hz.1
        have hB0 := (HermLine.sqMetric (ι := ι) β).pos z hz.1
        rw [← sub_mul]
        congr 1
        show Real.log (‖eval z (map (Int.castRingHom ℂ) f)‖ / (A.h z * (HermLine.sqMetric β).h z)) -
          Real.log (‖eval z (map (Int.castRingHom ℂ) g)‖ / (HermLine.sqMetric β).h z) =
          Real.log (‖eval z (map (Int.castRingHom ℂ) f)‖ / ‖eval z (map (Int.castRingHom ℂ) g)‖ / A.h z)
        rw [Real.log_div hf0.ne' (mul_pos hA0 hB0).ne', Real.log_mul hA0.ne' hB0.ne',
          Real.log_div hg0.ne' hB0.ne', Real.log_div (div_pos hf0 hg0).ne' hA0.ne',
          Real.log_div hf0.ne' hg0.ne']
        ring
      · simp
    · simp
  unfold recRRat
  rw [recR_eq] at hRf hRg
  show I P (n + 1) (Fin.snoc L A) = cycR I P L f - cycR I P L g - ptsIntegral P (pot L) (logNormRat A f g)
  rw [← hint]
  linarith

end GroundTheory.Heights₂.Heights.Inter
