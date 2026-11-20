import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterFib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedF
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsFieldIntersectionNoBlockFam
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsFurtherBis
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2
  ReciprocityTheory.ChartRestriction.G.AI.I4

namespace ArithmeticIntersectionIntegral

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]

/- English proof (translation)
Establish `hJ : IsMultiHomogIdeal (Ideal.span {h} : Ideal (MRing ι))` using `⟨{h}, fun f hf => by rw [Set.mem_singleton_iff.mp hf]; exact hh, rfl⟩`. Establish `hJP : ¬ (Ideal.span {h} : Ideal (MRing ι)) ≤ P`. Rewrite using `[Ideal.span_singleton_le_iff_mem]` and apply the resulting hypothesis. Establish `hnull` using `projB_null Ψ hP hΨ hJ hJP`. Use `ae_iff.mpr (measure_mono_null (fun y hy => ?_) hnull)` and prove the remaining obligations.

Simplify using `only [Set.mem_ofPred_eq, not_forall, not_not] at hy`. Take `⟨z, hz, hzy, hz0⟩` from `hy`. Use `⟨z, hz, ⟨hz.1, fun q hq => ?_⟩, hzy⟩` and prove the remaining obligations. Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton'.mp hq`. Simplify using `[hz0]`.
-/
theorem ae_eval_ne_zero {P : Ideal (MRing ι)} {e : ℕ} {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)}
    (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) {h : MRing ι} (hh : ∃ a, IsMultiHomog h a)
    (hhP : h ∉ P) :
    ∀ᵐ y : Fin e → ℂ, ∀ z ∈ mcPts P, Ψ (segre z) = Fin.cons 1 y →
      eval z (map (Int.castRingHom ℂ) h) ≠ 0 := by
  have hJ : IsMultiHomogIdeal (Ideal.span {h} : Ideal (MRing ι)) :=
    ⟨{h}, fun f hf => by rw [Set.mem_singleton_iff.mp hf]; exact hh, rfl⟩
  have hJP : ¬ (Ideal.span {h} : Ideal (MRing ι)) ≤ P := by
    rwa [Ideal.span_singleton_le_iff_mem]
  have hnull := projB_null Ψ hP hΨ hJ hJP
  refine ae_iff.mpr (measure_mono_null (fun y hy => ?_) hnull)
  simp only [Set.mem_ofPred_eq, not_forall, not_not] at hy
  obtain ⟨z, hz, hzy, hz0⟩ := hy
  refine ⟨z, hz, ⟨hz.1, fun q hq => ?_⟩, hzy⟩
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hq
  simp [hz0]

/- English proof (translation)
Establish `hAB` using `isSmoothHerm_tensor hA hB`. Take `⟨α, -, hfα, hfP⟩` from `id hf`. Take `⟨β, -, hgβ, hgP⟩` from `id hg`. Unfold `ptsIntegral`. Use `split_ifs with hΨ`.

Establish `hΨg : IsGoodProj P hΨ.choose` using `hΨ.choose_spec`. Unfold `ptsIntegralAt`. Rewrite using `[← integral_sub (hInt K ι P n _ L _ f hP hΨg hL hAB hf) (hInt K ι P n _ L _ g hP hΨg hL hB hg)]`. Use `integral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [ae_eval_ne_zero hP hΨg ⟨α, hfα⟩ hfP, ae_eval_ne_zero hP hΨg ⟨β, hgβ⟩ hgP] with y hyf hyg`.

Rewrite using `[← finsum_mem_sub_distrib _ _ (fibreFinite K ι P n _ hP hΨg y)]`. Use `finsum_mem_congr rfl fun w _ => ?_` and prove the remaining obligations. Unfold `sheetDensity`. Use `split_ifs with hγ`. Establish `hs` using `hγ.choose_spec.2.self_of_nhds set z := hγ.choose y`.

Establish `hz : z ∈ mcPts P` using `hs.2.1`. Establish `hf0` using `norm_pos_iff.mpr (hyf z hz hs.2.2)`. Establish `hg0` using `norm_pos_iff.mpr (hyg z hz hs.2.2)`. Establish `hA0` using `A.pos z hz.1`. Establish `hB0` using `B.pos z hz.1`.

Rewrite using `[← sub_mul]`. Use `congr 1`. Use `show Real.log (‖eval z (map (Int.castRingHom ℂ) f)‖ / ‖eval z (map (Int.castRingHom ℂ) g)‖ / A.h z) = Real.log (‖eval z (map (Int.castRingHom ℂ) f)‖ / (A.h z * B.h z)) - Real.log (‖eval z (map (Int.castRingHom ℂ) g)‖ / B.h z)`. Rewrite using `[Real.log_div hf0.ne' (mul_pos hA0 hB0).ne', Real.log_mul hA0.ne' hB0.ne', Real.log_div hg0.ne' hB0.ne', Real.log_div (div_pos hf0 hg0).ne' hA0.ne', Real.log_div hf0.ne' hg0.ne']`. Expand and normalize the polynomial expressions, which then agree.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem ptsIntegral_logNormRat (hInt : PtsIntegrableStatement) {P : Ideal (MRing ι)} {n : ℕ}
    {L : Fin n → HermLine ι} {A B : HermLine ι} {f g : MRing ι} (hP : IsArithVar P (n + 1))
    (hL : ∀ j, IsSmoothHerm (L j)) (hA : IsSmoothHerm A) (hB : IsSmoothHerm B)
    (hf : IsSectionOn P (A.tensor B) f) (hg : IsSectionOn P B g) :
    ptsIntegral P (pot L) (logNormRat A f g) =
      ptsIntegral P (pot L) (logNorm (A.tensor B) f) - ptsIntegral P (pot L) (logNorm B g) := by
  have hAB := isSmoothHerm_tensor hA hB
  obtain ⟨α, -, hfα, hfP⟩ := id hf
  obtain ⟨β, -, hgβ, hgP⟩ := id hg
  unfold ptsIntegral
  split_ifs with hΨ
  · have hΨg : IsGoodProj P hΨ.choose := hΨ.choose_spec
    unfold ptsIntegralAt
    rw [← integral_sub (hInt K ι P n _ L _ f hP hΨg hL hAB hf) (hInt K ι P n _ L _ g hP hΨg hL hB hg)]
    refine integral_congr_ae ?_
    filter_upwards [ae_eval_ne_zero hP hΨg ⟨α, hfα⟩ hfP, ae_eval_ne_zero hP hΨg ⟨β, hgβ⟩ hgP]
      with y hyf hyg
    rw [← finsum_mem_sub_distrib _ _ (fibreFinite K ι P n _ hP hΨg y)]
    refine finsum_mem_congr rfl fun w _ => ?_
    unfold sheetDensity
    split_ifs with hγ
    · have hs := hγ.choose_spec.2.self_of_nhds
      set z := hγ.choose y
      have hz : z ∈ mcPts P := hs.2.1
      have hf0 := norm_pos_iff.mpr (hyf z hz hs.2.2)
      have hg0 := norm_pos_iff.mpr (hyg z hz hs.2.2)
      have hA0 := A.pos z hz.1
      have hB0 := B.pos z hz.1
      rw [← sub_mul]
      congr 1
      show Real.log (‖eval z (map (Int.castRingHom ℂ) f)‖ / ‖eval z (map (Int.castRingHom ℂ) g)‖ / A.h z) =
        Real.log (‖eval z (map (Int.castRingHom ℂ) f)‖ / (A.h z * B.h z)) -
          Real.log (‖eval z (map (Int.castRingHom ℂ) g)‖ / B.h z)
      rw [Real.log_div hf0.ne' (mul_pos hA0 hB0).ne', Real.log_mul hA0.ne' hB0.ne',
        Real.log_div hg0.ne' hB0.ne', Real.log_div (div_pos hf0 hg0).ne' hA0.ne',
        Real.log_div hf0.ne' hg0.ne']
      ring
    · simp
  · simp

/- English proof (translation)
Establish `e : A'.h = A.h ∘ fun z' p => z' (v p)` using `funext h.2`. Unfold `IsSmoothHerm`. Rewrite using `[e]`. Use `hA.comp (contDiff_pi.2 fun p => contDiff_apply ℝ ℂ (v p)).contDiffOn ?_` and prove the remaining obligations. Introduce `z' hz'`.

Simplify using `only [Set.mem_ofPred_eq] at hz' ⊢`. Introduce `k`. Take `⟨i', hi'⟩` from `hz' (κ k)`. Take `⟨p, hp⟩` from `hv.2.2.2 ⟨κ k, i'⟩ ⟨k, rfl⟩`. Establish `h2 : p.1 = k` using `hv.1 (by rw [← hv.2.2.1 p, hp])`.

Take `⟨pk, pi⟩` from `p`. Simplify using `only at h2`. Substitute `h2` using the available equality. Conclude with `⟨pi, by rw [hp]; exact hi'⟩`.
-/
theorem isSmoothHerm_pull {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {A : HermLine ι} {A' : HermLine ι'} (hA : IsSmoothHerm A) (h : IsPullHerm κ v A A') :
    IsSmoothHerm A' := by
  have e : A'.h = A.h ∘ fun z' p => z' (v p) := funext h.2
  unfold IsSmoothHerm
  rw [e]
  refine hA.comp (contDiff_pi.2 fun p => contDiff_apply ℝ ℂ (v p)).contDiffOn ?_
  intro z' hz'
  simp only [Set.mem_ofPred_eq] at hz' ⊢
  intro k
  obtain ⟨i', hi'⟩ := hz' (κ k)
  obtain ⟨p, hp⟩ := hv.2.2.2 ⟨κ k, i'⟩ ⟨k, rfl⟩
  have h2 : p.1 = k := hv.1 (by rw [← hv.2.2.1 p, hp])
  obtain ⟨pk, pi⟩ := p
  simp only at h2
  subst h2
  exact ⟨pi, by rw [hp]; exact hi'⟩

omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)] in

/- English proof (translation)
Use function extensionality and compare the values at `k'`. Simplify using `only [pullDeg, Pi.add_apply]`. Unfold `Function.extend`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem pullDeg_add (κ : K → K') (a b : K → ℤ) : pullDeg κ (a + b) = pullDeg κ a + pullDeg κ b := by
  funext k'
  simp only [pullDeg, Pi.add_apply]
  unfold Function.extend
  split_ifs <;> simp

omit [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)] in

/- English proof (translation)
Use `⟨?_, fun z' => ?_⟩` and prove the remaining obligations. Use `show A'.a + B'.a = pullDeg κ (A.a + B.a)`. Rewrite using `[pullDeg_add, hA.1, hB.1]`. Use `show A'.h z' * B'.h z' = A.h _ * B.h _`. Rewrite using `[hA.2, hB.2]`.
-/
theorem isPullHerm_tensor {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} {A B : HermLine ι}
    {A' B' : HermLine ι'} (hA : IsPullHerm κ v A A') (hB : IsPullHerm κ v B B') :
    IsPullHerm κ v (A.tensor B) (A'.tensor B') := by
  refine ⟨?_, fun z' => ?_⟩
  · show A'.a + B'.a = pullDeg κ (A.a + B.a)
    rw [pullDeg_add, hA.1, hB.1]
  · show A'.h z' * B'.h z' = A.h _ * B.h _
    rw [hA.2, hB.2]

omit [Fintype K] [∀ k, Fintype (ι k)] in
open Classical in

/- English proof (translation)
Rewrite using `[Fintype.sum_sigma, Finset.sum_eq_single k']`. Simplify using the standard rewrite rules. Introduce `b _ hb`. Simplify using `[hb]`. Simplify using the standard rewrite rules.
-/
theorem sum_block (F : (Σ k', ι' k') → ℕ) (k' : K') :
    ∑ i, F ⟨k', i⟩ = ∑ q, if q.1 = k' then F q else 0 := by
  classical
  rw [Fintype.sum_sigma, Finset.sum_eq_single k']
  · simp
  · intro b _ hb
    simp [hb]
  · simp

/- English proof (translation)
Introduce `m' hm' k'`. Rewrite `hm'` using `[support_rename_of_injective hv.2.1, Finset.mem_image]`. Take `⟨m, hm, rfl⟩` from `hm'`. Rewrite using `[sum_block]`. Establish `h1 : (∑ q, if q.1 = k' then Finsupp.mapDomain v m q else 0) = ∑ p, if κ p.1 = k' then m p else 0`.

Use `Finsupp.sum_mapDomain_index_inj (h := fun (q : Σ k', ι' k') (n : ℕ) => if q.1 = k' then n else 0) (s := m) hv.2.1` as an intermediate fact. Rewrite `this` using `[Finsupp.sum_fintype _ _ (by simp), Finsupp.sum_fintype _ _ (by simp)]`. Simplify `this` using `[hv.2.2.1]`. Establish `h2 : (∑ p : Σ k, ι k, if κ p.1 = k' then m p else 0) = ∑ k, if κ k = k' then α k else 0`. Rewrite using `[Fintype.sum_sigma]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Use `split_ifs with hk`. Conclude with `hs m hm k`. Simplify using the standard rewrite rules. Use `h1.trans h2` and compare the differences between its conclusion and the goal.

Distinguish the cases in `h : ∃ k, κ k = k'`. Take `⟨k, rfl⟩` from `h`. Rewrite using `[hv.1.extend_apply, Finset.sum_eq_single k]`. Simplify using the standard rewrite rules. Introduce `b _ hb`.

Simplify using `[hv.1.ne hb]`. Simplify using the standard rewrite rules. Rewrite using `[Function.extend_apply' _ _ _ h]`. Use `(Finset.sum_eq_zero fun k _ => ?_).symm` and prove the remaining obligations. Rewrite using `[if_neg fun hk => h ⟨k, hk⟩]`.
-/
theorem isMultiHomog_rename {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {s : MRing ι} {α : K → ℕ} (hs : IsMultiHomog s α) :
    IsMultiHomog (rename v s) (Function.extend κ α 0) := by
  classical
  intro m' hm' k'
  rw [support_rename_of_injective hv.2.1, Finset.mem_image] at hm'
  obtain ⟨m, hm, rfl⟩ := hm'
  rw [sum_block]
  have h1 : (∑ q, if q.1 = k' then Finsupp.mapDomain v m q else 0) =
      ∑ p, if κ p.1 = k' then m p else 0 := by
    have := Finsupp.sum_mapDomain_index_inj (h := fun (q : Σ k', ι' k') (n : ℕ) => if q.1 = k' then n else 0)
      (s := m) hv.2.1
    rw [Finsupp.sum_fintype _ _ (by simp), Finsupp.sum_fintype _ _ (by simp)] at this
    simpa [hv.2.2.1] using this
  have h2 : (∑ p : Σ k, ι k, if κ p.1 = k' then m p else 0) = ∑ k, if κ k = k' then α k else 0 := by
    rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs with hk
    · exact hs m hm k
    · simp
  convert h1.trans h2
  by_cases h : ∃ k, κ k = k'
  · obtain ⟨k, rfl⟩ := h
    rw [hv.1.extend_apply, Finset.sum_eq_single k]
    · simp
    · intro b _ hb
      simp [hv.1.ne hb]
    · simp
  · rw [Function.extend_apply' _ _ _ h]
    refine (Finset.sum_eq_zero fun k _ => ?_).symm
    rw [if_neg fun hk => h ⟨k, hk⟩]

end ArithmeticIntersectionIntegral

open ArithmeticIntersectionIntegral in

/- English proof (translation)
Introduce `K _ ι _ K' _ ι' _ κ v P' n G J L L' A A' f g hv hP' hP hJ hL hLL' hA hAA' hfg`. Take `⟨α, β, hf, hg, hfP, hgP, hαβ⟩` from `hfg`. Establish `hB : IsSmoothHerm (HermLine.sqMetric (ι` using `ι) β) := isSmoothHerm_sqMetric β`. Establish `hBB'` using `IndefiniteRowSideFullHecke.Inter.isPullHerm_pullHerm hv (HermLine.sqMetric (ι := ι) β)`. Establish `hB'` using `isSmoothHerm_pull hv hB hBB'`.

Establish `hA'` using `isSmoothHerm_pull hv hA hAA'`. Establish `hL' : ∀ j, IsSmoothHerm (L' j)` using `fun j => isSmoothHerm_pull hv (hL j) (hLL' j)`. Establish `hfs : IsSectionOn (imageZ v P') (A.tensor (HermLine.sqMetric β)) f`. Use `⟨α, fun k => ?_, hf, hfP⟩` and prove the remaining obligations. Use `show A.a k + (β k : ℤ) = α k`.

Rewrite using `[← hαβ k]`. Expand and normalize the polynomial expressions, which then agree. Establish `hgs : IsSectionOn (imageZ v P') (HermLine.sqMetric (ι` using `ι) β) g := ⟨β, fun k => rfl, hg, hgP⟩`. Establish `hfs' : IsSectionOn P' (A'.tensor (IndefiniteRowSideFullHecke.Inter.pullHerm hv (HermLine.sqMetric β))) (rename v f)`. Use `⟨Function.extend κ α 0, fun k' => ?_, isMultiHomog_rename hv hf, fun h => hfP (Ideal.mem_comap.mpr h)⟩` and prove the remaining obligations.

Use `show A'.a k' + pullDeg κ (fun k => (β k : ℤ)) k' = _`. Rewrite using `[hAA'.1, pullDeg, pullDeg]`. Distinguish the cases in `h : ∃ k, κ k = k'`. Take `⟨k, rfl⟩` from `h`. Rewrite using `[hv.1.extend_apply, hv.1.extend_apply, hv.1.extend_apply, ← hαβ k]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Function.extend_apply' _ _ _ h, Function.extend_apply' _ _ _ h, Function.extend_apply' _ _ _ h]`. Simplify using the standard rewrite rules. Establish `hgs' : IsSectionOn P' (IndefiniteRowSideFullHecke.Inter.pullHerm hv (HermLine.sqMetric (ι` using `ι) β)) (rename v g) := by`. Use `⟨Function.extend κ β 0, fun k' => ?_, isMultiHomog_rename hv hg, fun h => hgP (Ideal.mem_comap.mpr h)⟩` and prove the remaining obligations.

Use `show pullDeg κ (fun k => (β k : ℤ)) k' = _`. Rewrite using `[pullDeg]`. Distinguish the cases in `h : ∃ k, κ k = k'`. Take `⟨k, rfl⟩` from `h`. Rewrite using `[hv.1.extend_apply, hv.1.extend_apply]`.

Rewrite using `[Function.extend_apply' _ _ _ h, Function.extend_apply' _ _ _ h]`. Simplify using the standard rewrite rules. Rewrite using `[ptsIntegral_logNormRat hInt hP' hL' hA' hB' hfs' hgs', ptsIntegral_logNormRat hInt hP hL hA hB hfs hgs, hSec K ι K' ι' κ v P' n G J L L' _ _ f hv hP' hP hJ hL hLL' (isSmoothHerm_tensor hA hB) (isPullHerm_tensor hAA' hBB') hfs, hSec K ι K' ι' κ v P' n G J L L' _ _ g hv hP' hP hJ …`.
-/
theorem ArithmeticIntersectionIntegral.proof (hInt : PtsIntegrableStatement) (hSec : IntersectionWithSection.Statement) : ArithmeticIntersectionIntegral.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' n G J L L' A A' f g hv hP' hP hJ hL hLL' hA hAA' hfg
  obtain ⟨α, β, hf, hg, hfP, hgP, hαβ⟩ := hfg
  have hB : IsSmoothHerm (HermLine.sqMetric (ι := ι) β) := isSmoothHerm_sqMetric β
  have hBB' := IndefiniteRowSideFullHecke.Inter.isPullHerm_pullHerm hv (HermLine.sqMetric (ι := ι) β)
  have hB' := isSmoothHerm_pull hv hB hBB'
  have hA' := isSmoothHerm_pull hv hA hAA'
  have hL' : ∀ j, IsSmoothHerm (L' j) := fun j => isSmoothHerm_pull hv (hL j) (hLL' j)
  have hfs : IsSectionOn (imageZ v P') (A.tensor (HermLine.sqMetric β)) f := by
    refine ⟨α, fun k => ?_, hf, hfP⟩
    show A.a k + (β k : ℤ) = α k
    rw [← hαβ k]
    ring
  have hgs : IsSectionOn (imageZ v P') (HermLine.sqMetric (ι := ι) β) g := ⟨β, fun k => rfl, hg, hgP⟩
  have hfs' : IsSectionOn P' (A'.tensor (IndefiniteRowSideFullHecke.Inter.pullHerm hv (HermLine.sqMetric β))) (rename v f) := by
    refine ⟨Function.extend κ α 0, fun k' => ?_, isMultiHomog_rename hv hf,
      fun h => hfP (Ideal.mem_comap.mpr h)⟩
    show A'.a k' + pullDeg κ (fun k => (β k : ℤ)) k' = _
    rw [hAA'.1, pullDeg, pullDeg]
    by_cases h : ∃ k, κ k = k'
    · obtain ⟨k, rfl⟩ := h
      rw [hv.1.extend_apply, hv.1.extend_apply, hv.1.extend_apply, ← hαβ k]
      ring
    · rw [Function.extend_apply' _ _ _ h, Function.extend_apply' _ _ _ h, Function.extend_apply' _ _ _ h]
      simp
  have hgs' : IsSectionOn P' (IndefiniteRowSideFullHecke.Inter.pullHerm hv (HermLine.sqMetric (ι := ι) β)) (rename v g) := by
    refine ⟨Function.extend κ β 0, fun k' => ?_, isMultiHomog_rename hv hg,
      fun h => hgP (Ideal.mem_comap.mpr h)⟩
    show pullDeg κ (fun k => (β k : ℤ)) k' = _
    rw [pullDeg]
    by_cases h : ∃ k, κ k = k'
    · obtain ⟨k, rfl⟩ := h
      rw [hv.1.extend_apply, hv.1.extend_apply]
    · rw [Function.extend_apply' _ _ _ h, Function.extend_apply' _ _ _ h]
      simp
  rw [ptsIntegral_logNormRat hInt hP' hL' hA' hB' hfs' hgs', ptsIntegral_logNormRat hInt hP hL hA hB hfs hgs,
    hSec K ι K' ι' κ v P' n G J L L' _ _ f hv hP' hP hJ hL hLL' (isSmoothHerm_tensor hA hB)
      (isPullHerm_tensor hAA' hBB') hfs,
    hSec K ι K' ι' κ v P' n G J L L' _ _ g hv hP' hP hJ hL hLL' hB hBB' hgs, mul_sub]

end GroundTheory.Heights₂.Heights.Inter
