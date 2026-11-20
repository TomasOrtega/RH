import Mathlib
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LintegralImageEqLintegralNormSqDetMul
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPosPartLocal
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetSumMeasurable
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets

noncomputable section

namespace PosPartLocal

variable {n d : ℕ}

/- English proof (translation)
Unfold `chartPosDens sheetSum`. Distinguish the cases in `hy : y ∈ U ∩ s ⁻¹' E`. Rewrite using `[Set.indicator_of_mem hy]`. Establish `hfib : s y ∈ fibre J A y` using `⟨(hsec y hy.1).2, (hsec y hy.1).1⟩`. Establish `hsh : IsSheetAt J A (s y) s` using `⟨U, hU, by rw [(hsec y hy.1).1]; exact hy.1, hsd, by rw [(hsec y hy.1).1], hsec, W, hW.mem_nhds (hEW hy.2), fun x' hx' _ => (hWs x' hx').2.symm⟩`.

Rewrite using `[finsum_eq_single _ (s y) ?_, finsum_eq_if, if_pos hfib, dif_pos ⟨s, hsh⟩]`. Establish `h` using `SheetSumMeasurable.term_eq (fun a b => max (a * b) 0) (E.indicator f) φ hsh ⟨s, hsh⟩`. Rewrite `h` using `[(hsec y hy.1).1]`. Simplify using `only`. Rewrite using `[h, Set.indicator_of_mem (show s y ∈ E from hy.2)]`.

Introduce `x hne`. Rewrite using `[finsum_eq_if]`. Use `split_ifs with hx h`. Establish `hxE : x ∉ E` using `fun hxE => hne (by`. Establish `h'` using `(hWs x ⟨hx.1, hEW hxE⟩).2`.

Rewrite `h'` using `[hx.2]`. Conclude with `h'.symm)`. Simplify using `only`. Rewrite using `[Set.indicator_of_notMem hxE, zero_mul, max_self]`. Both sides reduce to the same expression.

Both sides reduce to the same expression. Rewrite using `[Set.indicator_of_notMem hy]`. Use `finsum_mem_eq_zero_of_forall_eq_zero fun x hx => ?_` and prove the remaining obligations. Use `split_ifs with h`. Establish `hxE : x ∉ E` using `fun hxE => hy (by`.

Take `⟨h1, h2⟩` from `hWs x ⟨hx.1, hEW hxE⟩`. Rewrite `h1`, `h2` using `[hx.2]`. Conclude with `⟨h1, by rw [Set.mem_preimage, h2]; exact hxE⟩)`. Simplify using `only`. Rewrite using `[Set.indicator_of_notMem hxE, zero_mul, max_self]`.

Both sides reduce to the same expression.
-/
theorem chartPosDens_eq {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    {s : (Fin d → ℂ) → Fin n → ℂ} {U : Set (Fin d → ℂ)} {W E : Set (Fin n → ℂ)}
    (hU : IsOpen U) (hsd : DifferentiableOn ℂ s U)
    (hsec : ∀ y ∈ U, A *ᵥ s y = y ∧ s y ∈ zeroSet J)
    (hW : IsOpen W) (hWs : ∀ x' ∈ zeroSet J ∩ W, A *ᵥ x' ∈ U ∧ s (A *ᵥ x') = x')
    (hEW : E ⊆ W) (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) (y : Fin d → ℂ) :
    chartPosDens J A (E.indicator f) φ y = (U ∩ s ⁻¹' E).indicator
      (fun y => max (f (s y) * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) y) 0) y := by
  classical
  unfold chartPosDens sheetSum
  by_cases hy : y ∈ U ∩ s ⁻¹' E
  · rw [Set.indicator_of_mem hy]
    have hfib : s y ∈ fibre J A y := ⟨(hsec y hy.1).2, (hsec y hy.1).1⟩
    have hsh : IsSheetAt J A (s y) s :=
      ⟨U, hU, by rw [(hsec y hy.1).1]; exact hy.1, hsd, by rw [(hsec y hy.1).1], hsec, W,
        hW.mem_nhds (hEW hy.2), fun x' hx' _ => (hWs x' hx').2.symm⟩
    rw [finsum_eq_single _ (s y) ?_, finsum_eq_if, if_pos hfib, dif_pos ⟨s, hsh⟩]
    · have h := SheetSumMeasurable.term_eq (fun a b => max (a * b) 0) (E.indicator f) φ hsh ⟨s, hsh⟩
      rw [(hsec y hy.1).1] at h
      dsimp only
      rw [h, Set.indicator_of_mem (show s y ∈ E from hy.2)]
    · intro x hne
      rw [finsum_eq_if]
      split_ifs with hx h
      · have hxE : x ∉ E := fun hxE => hne (by
          have h' := (hWs x ⟨hx.1, hEW hxE⟩).2
          rw [hx.2] at h'
          exact h'.symm)
        dsimp only
        rw [Set.indicator_of_notMem hxE, zero_mul, max_self]
      · rfl
      · rfl
  · rw [Set.indicator_of_notMem hy]
    refine finsum_mem_eq_zero_of_forall_eq_zero fun x hx => ?_
    split_ifs with h
    · have hxE : x ∉ E := fun hxE => hy (by
        obtain ⟨h1, h2⟩ := hWs x ⟨hx.1, hEW hxE⟩
        rw [hx.2] at h1 h2
        exact ⟨h1, by rw [Set.mem_preimage, h2]; exact hxE⟩)
      dsimp only
      rw [Set.indicator_of_notMem hxE, zero_mul, max_self]
    · rfl

end PosPartLocal

/- English proof (translation)
Introduce and unpack `n d J A A' f φ x - hφ ⟨s, U, hU, hxU, hsd, -, hsec, V, hV, hVs⟩ ⟨s', U', hU', hxU', hsd', -, hsec', V', hV', hVs'⟩`. Establish `hAc : Continuous fun z : Fin n → ℂ => A *ᵥ z` using `by fun_prop`. Establish `hAc' : Continuous fun z : Fin n → ℂ => A' *ᵥ z` using `by fun_prop`. Use `set W := (interior V ∩ (fun z => A *ᵥ z) ⁻¹' U) ∩ (interior V' ∩ (fun z => A' *ᵥ z) ⁻¹' U') with hWdef`. Establish `hW : IsOpen W` using `(isOpen_interior.inter (hU.preimage hAc)).inter (isOpen_interior.inter (hU'.preimage hAc'))`.

Establish `hWs : ∀ x' ∈ zeroSet J ∩ W, A *ᵥ x' ∈ U ∧ s (A *ᵥ x') = x'` using `by rintro x' ⟨hZ, ⟨hV1, hU1⟩, -⟩; exact ⟨hU1, (hVs x' ⟨hZ, interior_subset hV1⟩ hU1).symm⟩`. Establish `hWs' : ∀ x' ∈ zeroSet J ∩ W, A' *ᵥ x' ∈ U' ∧ s' (A' *ᵥ x') = x'` using `by rintro x' ⟨hZ, -, ⟨hV1, hU1⟩⟩; exact ⟨hU1, (hVs' x' ⟨hZ, interior_subset hV1⟩ hU1).symm⟩`. Use `⟨W, hW, ⟨⟨mem_interior_iff_mem_nhds.2 hV, hxU⟩, ⟨mem_interior_iff_mem_nhds.2 hV', hxU'⟩⟩, fun E _ hEW => ?_⟩` and prove the remaining obligations. Repeatedly rewrite using `[PosPartLocal.chartPosDens_eq hU hsd hsec hW hWs hEW, PosPartLocal.chartPosDens_eq hU' hsd' hsec' hW hWs' hEW]`. Use `set O' := U' ∩ s' ⁻¹' W with hO'def`.

Use `set τ : (Fin d → ℂ) → Fin d → ℂ := fun z => A *ᵥ s' z with hτdef`. Establish `hO' : IsOpen O'` using `hsd'.continuousOn.isOpen_inter_preimage hU' hW`. Establish `hτU : ∀ z ∈ O', τ z ∈ U ∧ s (τ z) = s' z` using `fun z hz => hWs _ ⟨(hsec' z hz.1).2, hz.2⟩`. Establish `hτd : DifferentiableOn ℂ τ O'`. Establish `hs'O : DifferentiableOn ℂ s' O'` using `hsd'.mono Set.inter_subset_left`.

Conclude with `((Matrix.mulVecLin A).toContinuousLinearMap.differentiable.comp_differentiableOn hs'O)`. Establish `hτan : AnalyticOnNhd ℂ τ O'` using `IndefiniteRowSideFullHecke.ComplexSets.analyticOnNhd_of_differentiableOn hO' hτd`. Establish `hτinj : Set.InjOn τ O'` using `fun z₁ h₁ z₂ h₂ h => by`. Establish `h'` using `congrArg s h`. Rewrite `h'` using `[(hτU z₁ h₁).2, (hτU z₂ h₂).2]`.

Rewrite using `[← (hsec' z₁ h₁.1).1, ← (hsec' z₂ h₂.1).1, h']`. Establish `hsan : AnalyticOnNhd ℂ s U` using `IndefiniteRowSideFullHecke.ComplexSets.analyticOnNhd_of_differentiableOn hU hsd`. Combine the equalities or inequalities in the displayed calculation. Use `(setLIntegral_eq_of_support_subset fun y hy => ?_).symm` and prove the remaining obligations. Establish `hyE : y ∈ U ∩ s ⁻¹' E`.

Assume the negation of the conclusion as `h`. Conclude with `hy (by simp [Set.indicator_of_notMem h])`. Establish `hZ : s y ∈ zeroSet J ∩ W` using `⟨(hsec y hyE.1).2, hEW hyE.2⟩`. Use `⟨A' *ᵥ s y, ⟨(hWs' _ hZ).1, ?_⟩, ?_⟩` and prove the remaining obligations. Use `show s' (A' *ᵥ s y) ∈ W`.

Rewrite using `[(hWs' _ hZ).2]`. Conclude with `hZ.2`. Use `show A *ᵥ s' (A' *ᵥ s y) = y`. Rewrite using `[(hWs' _ hZ).2, (hsec y hyE.1).1]`. Use `_ = ∫⁻ z in O', ENNReal.ofReal (Complex.normSq (ReciprocityTheory.AnForm.A.jacC τ z).det) * ENNReal.ofReal ((U ∩ s ⁻¹' E).indicator (fun y => max (f (s y) * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) y) 0) (τ z)) := ReciprocityTheory.AnForm.A.lintegral_image_eq_lintegral_ …`.

Use `_ = ∫⁻ z in O', ENNReal.ofReal ((U' ∩ s' ⁻¹' E).indicator (fun y => max (f (s' y) * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s') y) 0) z) := by`. Use `setLIntegral_congr_fun hO'.measurableSet fun z hz => ?_` and prove the remaining obligations. Distinguish the cases in `hzE : s' z ∈ E`. Establish `hm : τ z ∈ U ∩ s ⁻¹' E` using `⟨(hτU z hz).1, by rw [Set.mem_preimage, (hτU z hz).2]; exact hzE⟩`. Rewrite using `[Set.indicator_of_mem hm, Set.indicator_of_mem (show z ∈ U' ∩ s' ⁻¹' E from ⟨hz.1, hzE⟩)]`.

Establish `h1 : ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s') z = ReciprocityTheory.AnForm.maDens (fun k => (φ k ∘ s) ∘ τ) z` using `IndefiniteRowSideFullHecke.ComplexSets.maDens_congr_of_eventuallyEq fun k => by filter_upwards [hO'.mem_nhds hz] with w hw show φ k (s' w) = φ k (s (τ w))`. Rewrite using `[(hτU w hw).2]`. Establish `h2 : ReciprocityTheory.AnForm.maDens (fun k => (φ k ∘ s) ∘ τ) z = ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) (τ z) * Complex.normSq (ReciprocityTheory.AnForm.A.jacC τ z).det`. Use `ReciprocityTheory.AnForm.A.maDens_comp (fun k => φ k ∘ s) τ z (hτan z hz) fun k => ?_` and prove the remaining obligations. Take `⟨Ok, hOk, hZOk, hφk⟩` from `hφ k`.

Establish `hsZ : s (τ z) ∈ Ok` using `hZOk (by rw [(hτU z hz).2]; exact (hsec' z hz.1).2)`. Establish `hφa : ContDiffAt ℝ 2 (φ k) (s (τ z))` using `(hφk.contDiffAt (hOk.mem_nhds hsZ)).of_le (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))`. Establish `hsa : ContDiffAt ℝ 2 s (τ z)` using `((hsan (τ z) (hτU z hz).1).contDiffAt).restrict_scalars ℝ`. Conclude with `hφa.comp (τ z) hsa`. Rewrite using `[h1, h2, (hτU z hz).2, ← ENNReal.ofReal_mul (Complex.normSq_nonneg _), mul_comm, max_mul_of_nonneg _ _ (Complex.normSq_nonneg _), zero_mul, mul_assoc]`.

Rewrite using `[Set.indicator_of_notMem (fun hm => hzE (by`. Use `hm.2` as an intermediate fact. Rewrite `this` using `[Set.mem_preimage, (hτU z hz).2]`. Conclude with `this)),`. Use the proof step `Set.indicator_of_notMem (show z ∉ U' ∩ s' ⁻¹' E from fun hm => hzE hm.2)]`.

Simplify using the standard rewrite rules. Use `_ = _ := by`. Use `setLIntegral_eq_of_support_subset fun z hz => ?_` and prove the remaining obligations. Establish `hzE : z ∈ U' ∩ s' ⁻¹' E`. Assume the negation of the conclusion as `h`.

Conclude with `hz (by simp [Set.indicator_of_notMem h])`. Conclude with `⟨hzE.1, hEW hzE.2⟩`.
-/
theorem PosPartLocal.proof : PosPartLocal.Statement := by
  rintro n d J A A' f φ x - hφ ⟨s, U, hU, hxU, hsd, -, hsec, V, hV, hVs⟩
    ⟨s', U', hU', hxU', hsd', -, hsec', V', hV', hVs'⟩
  have hAc : Continuous fun z : Fin n → ℂ => A *ᵥ z := by fun_prop
  have hAc' : Continuous fun z : Fin n → ℂ => A' *ᵥ z := by fun_prop
  set W := (interior V ∩ (fun z => A *ᵥ z) ⁻¹' U) ∩ (interior V' ∩ (fun z => A' *ᵥ z) ⁻¹' U')
    with hWdef
  have hW : IsOpen W :=
    (isOpen_interior.inter (hU.preimage hAc)).inter (isOpen_interior.inter (hU'.preimage hAc'))
  have hWs : ∀ x' ∈ zeroSet J ∩ W, A *ᵥ x' ∈ U ∧ s (A *ᵥ x') = x' :=
    by rintro x' ⟨hZ, ⟨hV1, hU1⟩, -⟩; exact ⟨hU1, (hVs x' ⟨hZ, interior_subset hV1⟩ hU1).symm⟩
  have hWs' : ∀ x' ∈ zeroSet J ∩ W, A' *ᵥ x' ∈ U' ∧ s' (A' *ᵥ x') = x' :=
    by rintro x' ⟨hZ, -, ⟨hV1, hU1⟩⟩; exact ⟨hU1, (hVs' x' ⟨hZ, interior_subset hV1⟩ hU1).symm⟩
  refine ⟨W, hW, ⟨⟨mem_interior_iff_mem_nhds.2 hV, hxU⟩, ⟨mem_interior_iff_mem_nhds.2 hV', hxU'⟩⟩,
    fun E _ hEW => ?_⟩
  simp_rw [PosPartLocal.chartPosDens_eq hU hsd hsec hW hWs hEW,
    PosPartLocal.chartPosDens_eq hU' hsd' hsec' hW hWs' hEW]

  set O' := U' ∩ s' ⁻¹' W with hO'def
  set τ : (Fin d → ℂ) → Fin d → ℂ := fun z => A *ᵥ s' z with hτdef
  have hO' : IsOpen O' := hsd'.continuousOn.isOpen_inter_preimage hU' hW
  have hτU : ∀ z ∈ O', τ z ∈ U ∧ s (τ z) = s' z := fun z hz => hWs _ ⟨(hsec' z hz.1).2, hz.2⟩
  have hτd : DifferentiableOn ℂ τ O' := by
    have hs'O : DifferentiableOn ℂ s' O' := hsd'.mono Set.inter_subset_left
    exact ((Matrix.mulVecLin A).toContinuousLinearMap.differentiable.comp_differentiableOn hs'O)
  have hτan : AnalyticOnNhd ℂ τ O' := IndefiniteRowSideFullHecke.ComplexSets.analyticOnNhd_of_differentiableOn hO' hτd
  have hτinj : Set.InjOn τ O' := fun z₁ h₁ z₂ h₂ h => by
    have h' := congrArg s h
    rw [(hτU z₁ h₁).2, (hτU z₂ h₂).2] at h'
    rw [← (hsec' z₁ h₁.1).1, ← (hsec' z₂ h₂.1).1, h']
  have hsan : AnalyticOnNhd ℂ s U := IndefiniteRowSideFullHecke.ComplexSets.analyticOnNhd_of_differentiableOn hU hsd
  calc _ = ∫⁻ y in τ '' O', ENNReal.ofReal ((U ∩ s ⁻¹' E).indicator
          (fun y => max (f (s y) * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) y) 0) y) := by
        refine (setLIntegral_eq_of_support_subset fun y hy => ?_).symm
        have hyE : y ∈ U ∩ s ⁻¹' E := by
          by_contra h
          exact hy (by simp [Set.indicator_of_notMem h])
        have hZ : s y ∈ zeroSet J ∩ W := ⟨(hsec y hyE.1).2, hEW hyE.2⟩
        refine ⟨A' *ᵥ s y, ⟨(hWs' _ hZ).1, ?_⟩, ?_⟩
        · show s' (A' *ᵥ s y) ∈ W
          rw [(hWs' _ hZ).2]
          exact hZ.2
        · show A *ᵥ s' (A' *ᵥ s y) = y
          rw [(hWs' _ hZ).2, (hsec y hyE.1).1]
    _ = ∫⁻ z in O', ENNReal.ofReal (Complex.normSq (ReciprocityTheory.AnForm.A.jacC τ z).det) *
          ENNReal.ofReal ((U ∩ s ⁻¹' E).indicator
            (fun y => max (f (s y) * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) y) 0) (τ z)) :=
        ReciprocityTheory.AnForm.A.lintegral_image_eq_lintegral_normSq_det_mul τ O' hO' hτan hτinj _
    _ = ∫⁻ z in O', ENNReal.ofReal ((U' ∩ s' ⁻¹' E).indicator
          (fun y => max (f (s' y) * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s') y) 0) z) := by
        refine setLIntegral_congr_fun hO'.measurableSet fun z hz => ?_
        by_cases hzE : s' z ∈ E
        · have hm : τ z ∈ U ∩ s ⁻¹' E :=
            ⟨(hτU z hz).1, by rw [Set.mem_preimage, (hτU z hz).2]; exact hzE⟩
          rw [Set.indicator_of_mem hm, Set.indicator_of_mem (show z ∈ U' ∩ s' ⁻¹' E from ⟨hz.1, hzE⟩)]
          have h1 : ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s') z =
              ReciprocityTheory.AnForm.maDens (fun k => (φ k ∘ s) ∘ τ) z :=
            IndefiniteRowSideFullHecke.ComplexSets.maDens_congr_of_eventuallyEq fun k => by
              filter_upwards [hO'.mem_nhds hz] with w hw
              show φ k (s' w) = φ k (s (τ w))
              rw [(hτU w hw).2]
          have h2 : ReciprocityTheory.AnForm.maDens (fun k => (φ k ∘ s) ∘ τ) z =
              ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) (τ z) *
                Complex.normSq (ReciprocityTheory.AnForm.A.jacC τ z).det := by
            refine ReciprocityTheory.AnForm.A.maDens_comp (fun k => φ k ∘ s) τ z (hτan z hz) fun k => ?_
            obtain ⟨Ok, hOk, hZOk, hφk⟩ := hφ k
            have hsZ : s (τ z) ∈ Ok := hZOk (by rw [(hτU z hz).2]; exact (hsec' z hz.1).2)
            have hφa : ContDiffAt ℝ 2 (φ k) (s (τ z)) :=
              (hφk.contDiffAt (hOk.mem_nhds hsZ)).of_le (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))
            have hsa : ContDiffAt ℝ 2 s (τ z) :=
              ((hsan (τ z) (hτU z hz).1).contDiffAt).restrict_scalars ℝ
            exact hφa.comp (τ z) hsa
          rw [h1, h2, (hτU z hz).2, ← ENNReal.ofReal_mul (Complex.normSq_nonneg _), mul_comm,
            max_mul_of_nonneg _ _ (Complex.normSq_nonneg _), zero_mul, mul_assoc]
        · rw [Set.indicator_of_notMem (fun hm => hzE (by
              have := hm.2
              rw [Set.mem_preimage, (hτU z hz).2] at this
              exact this)),
            Set.indicator_of_notMem (show z ∉ U' ∩ s' ⁻¹' E from fun hm => hzE hm.2)]
          simp
    _ = _ := by
        refine setLIntegral_eq_of_support_subset fun z hz => ?_
        have hzE : z ∈ U' ∩ s' ⁻¹' E := by
          by_contra h
          exact hz (by simp [Set.indicator_of_notMem h])
        exact ⟨hzE.1, hEW hzE.2⟩

end

end GroundTheory.Heights₂.Heights
