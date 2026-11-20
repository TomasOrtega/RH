import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StVarIntChartChange
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StChartChangeSheetNull
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StChartChangeLocal
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLinearNoetherNormalization
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPosPartSplit
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PIntegralIndependent
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets

noncomputable section

namespace ChartChange

variable {n d : ℕ}

/- English proof (translation)
Use `(isClosed_eq ?_ continuous_const).measurableSet` and prove the remaining obligations. Unfold `linEval`. Use `fun_prop`.
-/
theorem measurableSet_linEval_eq_zero (u : Fin n → ℂ) : MeasurableSet {x | linEval u x = 0} := by
  refine (isClosed_eq ?_ continuous_const).measurableSet
  unfold linEval
  fun_prop

/- English proof (translation)
The claim follows from `(SheetSumMeasurable.isClosed_zeroSet J).measurableSet.diff (measurableSet_linEval_eq_zero u)`.
-/
theorem measurableSet_zeroSet_diff (J : Ideal (MvPolynomial (Fin n) ℂ)) (u : Fin n → ℂ) :
    MeasurableSet (zeroSet J \ {x | linEval u x = 0}) :=
  (SheetSumMeasurable.isClosed_zeroSet J).measurableSet.diff (measurableSet_linEval_eq_zero u)

/- English proof (translation)
Establish `hm : Measurable (U.piecewise Ψ fun _ => 0)` using `hΨ.measurable_piecewise continuousOn_const hU.measurableSet`. Establish `: Ψ ⁻¹' E ∩ S = (U.piecewise Ψ fun _ => 0) ⁻¹' E ∩ S`. Use extensionality with `x`. Simplify using `only [Set.mem_inter_iff, Set.mem_preimage]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨h1, h2⟩`. Conclude with `⟨by rwa [Set.piecewise_eq_of_mem _ _ _ (hSU h2)], h2⟩`. Introduce and unpack `⟨h1, h2⟩`. Conclude with `⟨by rwa [Set.piecewise_eq_of_mem _ _ _ (hSU h2)] at h1, h2⟩`. Rewrite using `[this]`.

Conclude with `(hm hE).inter hS`.
-/
theorem measurableSet_preimage_inter {Ψ : (Fin n → ℂ) → Fin n → ℂ} {U S E : Set (Fin n → ℂ)}
    (hU : IsOpen U) (hΨ : ContinuousOn Ψ U) (hSU : S ⊆ U) (hS : MeasurableSet S)
    (hE : MeasurableSet E) : MeasurableSet (Ψ ⁻¹' E ∩ S) := by
  classical
  have hm : Measurable (U.piecewise Ψ fun _ => 0) :=
    hΨ.measurable_piecewise continuousOn_const hU.measurableSet
  have : Ψ ⁻¹' E ∩ S = (U.piecewise Ψ fun _ => 0) ⁻¹' E ∩ S := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by rwa [Set.piecewise_eq_of_mem _ _ _ (hSU h2)], h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by rwa [Set.piecewise_eq_of_mem _ _ _ (hSU h2)] at h1, h2⟩
  rw [this]
  exact (hm hE).inter hS

/- English proof (translation)
Use `filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with y hy`. Use `PosPartSplit.proof n d K B w ψ F y hB hF fun x hx hs => hc x hx.1 hs ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hn`. Conclude with `hy ⟨x, ⟨hx.1, hs, hn⟩, hx.2⟩`.
-/
theorem ae_split {K : Ideal (MvPolynomial (Fin n) ℂ)} {B : Matrix (Fin d) (Fin n) ℂ}
    (w : (Fin n → ℂ) → ℝ) (ψ : Fin d → (Fin n → ℂ) → ℝ) (F : ℕ → Set (Fin n → ℂ))
    (P : (Fin n → ℂ) → Prop) (hB : IsFiniteProjection K B) (hF : Pairwise (Function.onFun Disjoint F))
    (h0 : volume ((fun x => B *ᵥ x) '' {x | x ∈ zeroSet K ∧ (∃ s, IsSheetAt K B x s) ∧ ¬ P x}) = 0)
    (hc : ∀ x ∈ zeroSet K, (∃ s, IsSheetAt K B x s) → P x → ∃ k, x ∈ F k) :
    ∀ᵐ y, ENNReal.ofReal (chartPosDens K B w ψ y) =
      ∑' k, ENNReal.ofReal (chartPosDens K B ((F k).indicator w) ψ y) := by
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with y hy
  refine PosPartSplit.proof n d K B w ψ F y hB hF fun x hx hs => hc x hx.1 hs ?_
  by_contra hn
  exact hy ⟨x, ⟨hx.1, hs, hn⟩, hx.2⟩

/- English proof (translation)
Rewrite using `[lintegral_congr_ae h, lintegral_tsum fun k => (IntegralIndep.measurable_chartPosDens hB (hw.indicator (hFm k)) ψ).ennreal_ofReal.aemeasurable]`.
-/
theorem lintegral_split {K : Ideal (MvPolynomial (Fin n) ℂ)} {B : Matrix (Fin d) (Fin n) ℂ}
    {w : (Fin n → ℂ) → ℝ} (ψ : Fin d → (Fin n → ℂ) → ℝ) {F : ℕ → Set (Fin n → ℂ)}
    (hB : IsFiniteProjection K B) (hw : Measurable w) (hFm : ∀ k, MeasurableSet (F k))
    (h : ∀ᵐ y, ENNReal.ofReal (chartPosDens K B w ψ y) =
      ∑' k, ENNReal.ofReal (chartPosDens K B ((F k).indicator w) ψ y)) :
    ∫⁻ y, ENNReal.ofReal (chartPosDens K B w ψ y) =
      ∑' k, ∫⁻ y, ENNReal.ofReal (chartPosDens K B ((F k).indicator w) ψ y) := by
  rw [lintegral_congr_ae h, lintegral_tsum fun k =>
    (IntegralIndep.measurable_chartPosDens hB (hw.indicator (hFm k)) ψ).ennreal_ofReal.aemeasurable]

/- English proof (translation)
Use `set Z := zeroSet J \ {x | linEval u x = 0} with hZ`. Use `set Z' := zeroSet J' \ {x | linEval u' x = 0} with hZ'`. Establish `key : ∀ x : Fin n → ℂ, ∃ W : Set (Fin n → ℂ), IsOpen W ∧ (x ∈ zeroSet J' → linEval u' x ≠ 0 → (∃ s', IsSheetAt J' A' x s') → (∃ s, IsSheetAt J A (Φ x) s) → x ∈ W) ∧ ∀ E : Set (Fin n → ℂ), MeasurableSet E → E ⊆ W → ∫⁻ y, ENNReal.ofReal (chartPosDens J' A' (E.indicator f') φ' y) = …`. Introduce `x`. Distinguish the cases in `hx : x ∈ zeroSet J' ∧ linEval u' x ≠ 0 ∧ (∃ s', IsSheetAt J' A' x s') ∧ ∃ s, IsSheetAt J A (Φ x) s`.

Take `⟨W, hW, hxW, hWE⟩` from `hL n d J J' A A' u u' U U' Φ Ψ f f' φ φ' c g x hU hU' hZU hZU' hΦ hΨ hΦm hΨm hΨΦ hΦΨ hf hf' hff hφ hφ' hg hg0 hφφ hx.1 hx.2.1 hx.2.2.1 hx.2.2.2`. Conclude with `⟨W, hW, fun _ _ _ _ => hxW, hWE⟩`. Use `⟨∅, isOpen_empty, fun h1 h2 h3 h4 => absurd ⟨h1, h2, h3, h4⟩ hx, fun E _ hE => ?_⟩` and prove the remaining obligations. Rewrite using `[Set.subset_empty_iff.1 hE, Set.image_empty, Set.indicator_empty]`. Simplify using `[chartPosDens, sheetSum]`.

Use `choose W hWo hxW hWE using key`. Take `⟨T, hTc, hTU⟩` from `TopologicalSpace.isOpen_iUnion_countable W hWo`. Take `⟨e, he⟩` from `(hTc.insert 0).exists_eq_range (Set.insert_nonempty 0 T)`. Use `set E' : ℕ → Set (Fin n → ℂ) := fun k => Z' ∩ disjointed (fun k => W (e k)) k with hE'`. Use `set E : ℕ → Set (Fin n → ℂ) := fun k => Φ '' E' k with hE`.

Establish `hE'm : ∀ k, MeasurableSet (E' k)` using `fun k => (measurableSet_zeroSet_diff J' u').inter (MeasurableSet.disjointed (fun k => (hWo (e k)).measurableSet) k)`. Establish `hE'W : ∀ k, E' k ⊆ W (e k)` using `fun k x hx => disjointed_subset (fun k => W (e k)) k hx.2`. Establish `hE'd : Pairwise (Function.onFun Disjoint E')` using `fun i j hij => ((disjoint_disjointed (fun k => W (e k))) hij).mono Set.inter_subset_right Set.inter_subset_right`. Establish `hEeq : ∀ k, E k = Ψ ⁻¹' E' k ∩ Z`. Introduce `k`.

Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x', hx', rfl⟩`. Conclude with `⟨by rw [Set.mem_preimage, hΨΦ x' hx'.1]; exact hx', hΦm hx'.1⟩`. Introduce and unpack `⟨h1, h2⟩`.

Conclude with `⟨Ψ x, h1, hΦΨ x h2⟩`. Establish `hEm : ∀ k, MeasurableSet (E k)` using `fun k => by`. Rewrite using `[hEeq k]`. Conclude with `measurableSet_preimage_inter hU hΨ.continuousOn hZU (measurableSet_zeroSet_diff J u) (hE'm k)`. Establish `hEd : Pairwise (Function.onFun Disjoint E)`.

Introduce `i j hij`. Rewrite using `[Function.onFun, Set.disjoint_left]`. Introduce and unpack `_ ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩`. Establish `: b = a` using `by rw [← hΨΦ b hb.1, hab, hΨΦ a ha.1]`. Conclude with `Set.disjoint_left.1 (hE'd hij) ha (this ▸ hb)`.

Establish `hcov' : ∀ x ∈ zeroSet J', (∃ s', IsSheetAt J' A' x s') → (linEval u' x ≠ 0 ∧ ∃ s, IsSheetAt J A (Φ x) s) → ∃ k, x ∈ E' k`. Introduce and unpack `x hxZ h1 ⟨h2, h3⟩`. Establish `: x ∈ ⋃ i ∈ T, W i` using `hTU ▸ Set.mem_iUnion.2 ⟨x, hxW x hxZ h2 h1 h3⟩`. Take `⟨i, hiT, hxi⟩` from `Set.mem_iUnion₂.1 this`. Take `⟨m, rfl⟩ : i ∈ Set.range e` from `he ▸ Set.mem_insert_of_mem 0 hiT`.

Establish `: x ∈ ⋃ k, disjointed (fun k => W (e k)) k`. Rewrite using `[iUnion_disjointed]`. Conclude with `Set.mem_iUnion.2 ⟨m, hxi⟩`. Take `⟨k, hk⟩` from `Set.mem_iUnion.1 this`. Conclude with `⟨k, ⟨hxZ, h2⟩, hk⟩`.

Establish `hcov : ∀ x ∈ zeroSet J, (∃ s, IsSheetAt J A x s) → (linEval u x ≠ 0 ∧ ∃ s', IsSheetAt J' A' (Ψ x) s') → ∃ k, x ∈ E k`. Introduce and unpack `x hxZ h1 ⟨h2, h3⟩`. Establish `hx : x ∈ Z` using `⟨hxZ, h2⟩`. Establish `hΨx` using `hΨm hx`. Take `⟨k, hk⟩` from `hcov' (Ψ x) hΨx.1 h3 ⟨hΨx.2, by rw [hΦΨ x hx]; exact h1⟩`.

Conclude with `⟨k, Ψ x, hk, hΦΨ x hx⟩`. Establish `hN` using `hNull n d J J' A A' u u' U U' Φ Ψ hJ hd hJ' hd' hu hu' hA hA' hU hU' hZU hZU' hΦ hΨ hΦm hΨm hΨΦ hΦΨ`. Establish `hN'` using `hNull n d J' J A' A u' u U' U Ψ Φ hJ' hd' hJ hd hu' hu hA' hA hU' hU hZU' hZU hΨ hΦ hΨm hΦm hΦΨ hΨΦ`. Rewrite using `[lintegral_split φ' hA' hf' hE'm (ae_split f' φ' E' _ hA' hE'd hN' hcov'), lintegral_split φ hA hf hEm (ae_split f φ E _ hA hEd hN hcov)]`. Conclude with `tsum_congr fun k => hWE (e k) (E' k) (hE'm k) (hE'W k)`.
-/
theorem posPart_eq (hNull : ChartChangeSheetNull.Statement) (hL : ChartChangeLocal.Statement)
    {J J' : Ideal (MvPolynomial (Fin n) ℂ)} {A A' : Matrix (Fin d) (Fin n) ℂ}
    {u u' : Fin n → ℂ} {U U' : Set (Fin n → ℂ)} {Φ Ψ : (Fin n → ℂ) → Fin n → ℂ}
    {f f' : (Fin n → ℂ) → ℝ} {φ φ' : Fin d → (Fin n → ℂ) → ℝ} {c : Fin d → ℝ}
    {g : Fin d → (Fin n → ℂ) → ℂ}
    (hJ : J.IsPrime) (hd : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d)
    (hJ' : J'.IsPrime) (hd' : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J') = d)
    (hu : linForm u ∉ J) (hu' : linForm u' ∉ J') (hA : IsFiniteProjection J A)
    (hA' : IsFiniteProjection J' A') (hU : IsOpen U) (hU' : IsOpen U')
    (hZU : zeroSet J \ {x | linEval u x = 0} ⊆ U) (hZU' : zeroSet J' \ {x | linEval u' x = 0} ⊆ U')
    (hΦ : DifferentiableOn ℂ Φ U') (hΨ : DifferentiableOn ℂ Ψ U)
    (hΦm : Set.MapsTo Φ (zeroSet J' \ {x | linEval u' x = 0}) (zeroSet J \ {x | linEval u x = 0}))
    (hΨm : Set.MapsTo Ψ (zeroSet J \ {x | linEval u x = 0}) (zeroSet J' \ {x | linEval u' x = 0}))
    (hΨΦ : ∀ x ∈ zeroSet J' \ {x | linEval u' x = 0}, Ψ (Φ x) = x)
    (hΦΨ : ∀ x ∈ zeroSet J \ {x | linEval u x = 0}, Φ (Ψ x) = x)
    (hf : Measurable f) (hf' : Measurable f')
    (hff : ∀ x ∈ zeroSet J' \ {x | linEval u' x = 0}, f' x = f (Φ x))
    (hφ : ∀ k, SmoothNear (zeroSet J) (φ k)) (hφ' : ∀ k, SmoothNear (zeroSet J') (φ' k))
    (hg : ∀ k, DifferentiableOn ℂ (g k) U') (hg0 : ∀ k, ∀ x ∈ U', g k x ≠ 0)
    (hφφ : ∀ k, ∀ x ∈ U', φ' k x = φ k (Φ x) + c k * Real.log ‖g k x‖) :
    ∫⁻ y, ENNReal.ofReal (chartPosDens J' A' f' φ' y) =
      ∫⁻ y, ENNReal.ofReal (chartPosDens J A f φ y) := by
  set Z := zeroSet J \ {x | linEval u x = 0} with hZ
  set Z' := zeroSet J' \ {x | linEval u' x = 0} with hZ'

  have key : ∀ x : Fin n → ℂ, ∃ W : Set (Fin n → ℂ), IsOpen W ∧
      (x ∈ zeroSet J' → linEval u' x ≠ 0 → (∃ s', IsSheetAt J' A' x s') →
        (∃ s, IsSheetAt J A (Φ x) s) → x ∈ W) ∧
      ∀ E : Set (Fin n → ℂ), MeasurableSet E → E ⊆ W →
        ∫⁻ y, ENNReal.ofReal (chartPosDens J' A' (E.indicator f') φ' y) =
          ∫⁻ y, ENNReal.ofReal (chartPosDens J A ((Φ '' E).indicator f) φ y) := by
    intro x
    by_cases hx : x ∈ zeroSet J' ∧ linEval u' x ≠ 0 ∧ (∃ s', IsSheetAt J' A' x s') ∧
        ∃ s, IsSheetAt J A (Φ x) s
    · obtain ⟨W, hW, hxW, hWE⟩ := hL n d J J' A A' u u' U U' Φ Ψ f f' φ φ' c g x hU hU' hZU hZU'
        hΦ hΨ hΦm hΨm hΨΦ hΦΨ hf hf' hff hφ hφ' hg hg0 hφφ hx.1 hx.2.1 hx.2.2.1 hx.2.2.2
      exact ⟨W, hW, fun _ _ _ _ => hxW, hWE⟩
    · refine ⟨∅, isOpen_empty, fun h1 h2 h3 h4 => absurd ⟨h1, h2, h3, h4⟩ hx, fun E _ hE => ?_⟩
      rw [Set.subset_empty_iff.1 hE, Set.image_empty, Set.indicator_empty]
      simp [chartPosDens, sheetSum]
  choose W hWo hxW hWE using key
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable W hWo
  obtain ⟨e, he⟩ := (hTc.insert 0).exists_eq_range (Set.insert_nonempty 0 T)
  set E' : ℕ → Set (Fin n → ℂ) := fun k => Z' ∩ disjointed (fun k => W (e k)) k with hE'
  set E : ℕ → Set (Fin n → ℂ) := fun k => Φ '' E' k with hE
  have hE'm : ∀ k, MeasurableSet (E' k) := fun k =>
    (measurableSet_zeroSet_diff J' u').inter
      (MeasurableSet.disjointed (fun k => (hWo (e k)).measurableSet) k)
  have hE'W : ∀ k, E' k ⊆ W (e k) := fun k x hx => disjointed_subset (fun k => W (e k)) k hx.2
  have hE'd : Pairwise (Function.onFun Disjoint E') := fun i j hij =>
    ((disjoint_disjointed (fun k => W (e k))) hij).mono Set.inter_subset_right
      Set.inter_subset_right

  have hEeq : ∀ k, E k = Ψ ⁻¹' E' k ∩ Z := by
    intro k
    ext x
    constructor
    · rintro ⟨x', hx', rfl⟩
      exact ⟨by rw [Set.mem_preimage, hΨΦ x' hx'.1]; exact hx', hΦm hx'.1⟩
    · rintro ⟨h1, h2⟩
      exact ⟨Ψ x, h1, hΦΨ x h2⟩
  have hEm : ∀ k, MeasurableSet (E k) := fun k => by
    rw [hEeq k]
    exact measurableSet_preimage_inter hU hΨ.continuousOn hZU (measurableSet_zeroSet_diff J u)
      (hE'm k)
  have hEd : Pairwise (Function.onFun Disjoint E) := by
    intro i j hij
    rw [Function.onFun, Set.disjoint_left]
    rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
    have : b = a := by rw [← hΨΦ b hb.1, hab, hΨΦ a ha.1]
    exact Set.disjoint_left.1 (hE'd hij) ha (this ▸ hb)

  have hcov' : ∀ x ∈ zeroSet J', (∃ s', IsSheetAt J' A' x s') →
      (linEval u' x ≠ 0 ∧ ∃ s, IsSheetAt J A (Φ x) s) → ∃ k, x ∈ E' k := by
    rintro x hxZ h1 ⟨h2, h3⟩
    have : x ∈ ⋃ i ∈ T, W i := hTU ▸ Set.mem_iUnion.2 ⟨x, hxW x hxZ h2 h1 h3⟩
    obtain ⟨i, hiT, hxi⟩ := Set.mem_iUnion₂.1 this
    obtain ⟨m, rfl⟩ : i ∈ Set.range e := he ▸ Set.mem_insert_of_mem 0 hiT
    have : x ∈ ⋃ k, disjointed (fun k => W (e k)) k := by
      rw [iUnion_disjointed]
      exact Set.mem_iUnion.2 ⟨m, hxi⟩
    obtain ⟨k, hk⟩ := Set.mem_iUnion.1 this
    exact ⟨k, ⟨hxZ, h2⟩, hk⟩
  have hcov : ∀ x ∈ zeroSet J, (∃ s, IsSheetAt J A x s) →
      (linEval u x ≠ 0 ∧ ∃ s', IsSheetAt J' A' (Ψ x) s') → ∃ k, x ∈ E k := by
    rintro x hxZ h1 ⟨h2, h3⟩
    have hx : x ∈ Z := ⟨hxZ, h2⟩
    have hΨx := hΨm hx
    obtain ⟨k, hk⟩ := hcov' (Ψ x) hΨx.1 h3 ⟨hΨx.2, by rw [hΦΨ x hx]; exact h1⟩
    exact ⟨k, Ψ x, hk, hΦΨ x hx⟩

  have hN := hNull n d J J' A A' u u' U U' Φ Ψ hJ hd hJ' hd' hu hu' hA hA' hU hU' hZU hZU' hΦ hΨ
    hΦm hΨm hΨΦ hΦΨ
  have hN' := hNull n d J' J A' A u' u U' U Ψ Φ hJ' hd' hJ hd hu' hu hA' hA hU' hU hZU' hZU hΨ hΦ
    hΨm hΦm hΦΨ hΨΦ
  rw [lintegral_split φ' hA' hf' hE'm (ae_split f' φ' E' _ hA' hE'd hN' hcov'),
    lintegral_split φ hA hf hEm (ae_split f φ E _ hA hEd hN hcov)]
  exact tsum_congr fun k => hWE (e k) (E' k) (hE'm k) (hE'W k)

end ChartChange

open ChartChange in

/- English proof (translation)
Introduce `n d J J' u u' U U' Φ Ψ f f' φ φ' c g hJ hd hJ' hd' hu hu' hU hU' hZU hZU' hΦ hΨ hΦm hΨm hΨΦ hΦΨ hf hf' hff hφ hφ' hg hg0 hφφ hint`. Establish `hex : ∃ A : Matrix (Fin d) (Fin n) ℂ, IsFiniteProjection J A` using `hN n d J hd`. Establish `hex' : ∃ A : Matrix (Fin d) (Fin n) ℂ, IsFiniteProjection J' A` using `hN n d J' hd'`. Establish `hA` using `hex.choose_spec`. Establish `hA'` using `hex'.choose_spec`.

Simplify using `only [varInt, dif_pos hex, dif_pos hex']`. Establish `hpos` using `posPart_eq hNull hL hJ hd hJ' hd' hu hu' hA hA' hU hU' hZU hZU' hΦ hΨ hΦm hΨm hΨΦ hΦΨ hf hf' hff hφ hφ' hg hg0 hφφ`. Establish `hneg` using `posPart_eq hNull hL hJ hd hJ' hd' hu hu' hA hA' hU hU' hZU hZU' hΦ hΨ hΦm hΨm hΨΦ hΦΨ hf.neg hf'.neg (fun x hx => by simp only [Pi.neg_apply, hff x hx]) hφ hφ' hg hg0 hφφ`. Take `⟨h1, h2⟩` from `IntegralIndep.chartInt_eq_posParts hA hf φ`. Take `⟨h1', h2'⟩` from `IntegralIndep.chartInt_eq_posParts hA' hf' φ'`.

Establish `hI` using `hint _ hA`. Establish `hI' : Integrable (chartAbsDens J' hex'.choose f' φ')` using `h1'.2 (by rw [hpos, hneg]; exact h1.1 hI)`. Rewrite using `[h2 hI, h2' hI', hpos, hneg]`.
-/
theorem VarIntChartChange.proof (hN : ComplexSets.LinearNoetherNormalization.Statement)
    (hNull : ChartChangeSheetNull.Statement) (hL : ChartChangeLocal.Statement) :
    VarIntChartChange.Statement := by
  intro n d J J' u u' U U' Φ Ψ f f' φ φ' c g hJ hd hJ' hd' hu hu' hU hU' hZU hZU' hΦ hΨ hΦm hΨm
    hΨΦ hΦΨ hf hf' hff hφ hφ' hg hg0 hφφ hint
  have hex : ∃ A : Matrix (Fin d) (Fin n) ℂ, IsFiniteProjection J A := hN n d J hd
  have hex' : ∃ A : Matrix (Fin d) (Fin n) ℂ, IsFiniteProjection J' A := hN n d J' hd'
  have hA := hex.choose_spec
  have hA' := hex'.choose_spec
  simp only [varInt, dif_pos hex, dif_pos hex']
  have hpos := posPart_eq hNull hL hJ hd hJ' hd' hu hu' hA hA' hU hU' hZU hZU' hΦ hΨ hΦm hΨm hΨΦ
    hΦΨ hf hf' hff hφ hφ' hg hg0 hφφ
  have hneg := posPart_eq hNull hL hJ hd hJ' hd' hu hu' hA hA' hU hU' hZU hZU' hΦ hΨ hΦm hΨm hΨΦ
    hΦΨ hf.neg hf'.neg (fun x hx => by simp only [Pi.neg_apply, hff x hx]) hφ hφ' hg hg0 hφφ
  obtain ⟨h1, h2⟩ := IntegralIndep.chartInt_eq_posParts hA hf φ
  obtain ⟨h1', h2'⟩ := IntegralIndep.chartInt_eq_posParts hA' hf' φ'
  have hI := hint _ hA
  have hI' : Integrable (chartAbsDens J' hex'.choose f' φ') := h1'.2 (by rw [hpos, hneg]; exact h1.1 hI)
  rw [h2 hI, h2' hI', hpos, hneg]

end

end GroundTheory.Heights₂.Heights
