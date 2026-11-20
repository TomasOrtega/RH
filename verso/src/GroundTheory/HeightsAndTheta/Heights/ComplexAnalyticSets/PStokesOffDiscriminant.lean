import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StokesOffDiscriminantWindow
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets StokesOffDiscriminant
open scoped ContDiff Manifold

noncomputable section

/- English proof (translation)
Introduce `n d J A P _ _ _ _ hsheet F G φ hF hG hφ hFc ⟨U, hUo, hPU, hFU⟩`. Use `set K := closure {x | x ∈ zeroSet J ∧ F x ≠ 0} with hKdef`. Establish `hKZ : K ⊆ zeroSet J` using `closure_minimal (fun x hx => hx.1) (SheetSumMeasurable.isClosed_zeroSet J)`. Establish `hKU : K ⊆ Uᶜ` using `closure_minimal (fun x hx hxU => hx.2 (hFU x ⟨hxU, hx.1⟩)) hUo.isClosed_compl`. Establish `hKc : IsCompact K` using `hFc.of_isClosed_subset isClosed_closure (closure_mono fun x hx => hx.2)`.

Establish `hwin : ∀ x : K, ∃ (s : (Fin (d + 1) → ℂ) → Fin n → ℂ) (V : Set (Fin (d + 1) → ℂ)) (W : Set (Fin n → ℂ)), IsOpen V ∧ IsOpen W ∧ (x : Fin n → ℂ) ∈ W ∧ DifferentiableOn ℂ s V ∧ (∀ y ∈ V, A *ᵥ s y = y ∧ s y ∈ zeroSet J) ∧ ∀ x' ∈ zeroSet J ∩ W, A *ᵥ x' ∈ V ∧ IsSheetAt J A x' s`. Introduce and unpack `⟨x, hx⟩`. Take `⟨s, hs⟩` from `hsheet x (hKZ hx) fun h => hKU hx (hPU h)`. Conclude with `⟨s, window_of_sheet hs⟩`. Use `choose s V W hVo hWo hxW hsd hsec hWs using hwin`.

Take `⟨t, ht⟩` from `hKc.elim_finite_subcover W hWo fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, hxW _⟩`. Take `⟨ρ, hρ⟩` from `SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, Fin n → ℂ) isClosed_closure (fun i : t => W i.1) (fun i => hWo i.1) fun x hx => by`. Take `⟨i, hi, hxi⟩` from `Set.mem_iUnion₂.1 (ht hx)`. Conclude with `Set.mem_iUnion.2 ⟨⟨i, hi⟩, hxi⟩`. Establish `hρs : ∀ i, ContDiff ℝ ∞ (ρ i)` using `fun i => contMDiff_iff_contDiff.1 (ρ i).contMDiff`.

Use `set f : t → (Fin n → ℂ) → ℝ := fun i x => ρ i x * F x with hfdef`. Establish `hsum : ∀ x ∈ zeroSet J, F x = ∑ i, f i x`. Introduce `x hxZ`. Distinguish the cases in `hK : x ∈ K`. Establish `h1` using `ρ.sum_eq_one hK`.

Rewrite `h1` using `[finsum_eq_sum_of_fintype]`. Simplify using `only [hfdef, ← Finset.sum_mul, h1, one_mul]`. Establish `hF0 : F x = 0` using `by_contra fun h => hK (subset_closure ⟨hxZ, h⟩)`. Simplify using `[hfdef, hF0]`. Establish `hfs : ∀ i, SmoothNear (zeroSet J) (f i)`.

Take `⟨O, hO, hZO, hFO⟩` from `hF`. Conclude with `fun i => ⟨O, hO, hZO, (hρs i).contDiffOn.mul hFO⟩`. Establish `hfW : ∀ i, tsupport (f i) ⊆ W i.1` using `fun i => tsupport_mul_subset_left.trans (hρ i)`. Establish `hpiece` using `fun i : t => window_stokes (hVo i.1) (hsd i.1) (hsec i.1) (hWs i.1) (f i) G φ (hfs i) hG hφ hFc.mul_left (hfW i)`. Establish `hL : ∀ y, chartDens J A F (vecCons G φ) y = ∑ i, chartDens J A (f i) (vecCons G φ) y`.

Introduce `y`. Unfold `chartDens`. Use `sheetSum_finset_sum Finset.univ _ (fun i x s' => f i x * ReciprocityTheory.AnForm.maDens (fun k => vecCons G φ k ∘ s') y) ?_ fun i _ => finite_support_sheetTerm_window (sheetTerm_weight_window (hsec i.1) (hWs i.1) (f i) (hfW i) _ y)` and prove the remaining obligations. Introduce `x hx s' _`. Rewrite using `[hsum x hx.1, Finset.sum_mul]`.

Establish `hR : ∀ y, chartDens J A G (vecCons F φ) y = ∑ i, chartDens J A G (vecCons (f i) φ) y`. Introduce `y`. Unfold `chartDens`. Use `sheetSum_finset_sum Finset.univ _ (fun i x s' => G x * ReciprocityTheory.AnForm.maDens (fun k => vecCons (f i) φ k ∘ s') y) ?_ fun i _ => finite_support_sheetTerm_window (sheetTerm_cons_window (hVo i.1) (hsd i.1) (hsec i.1) (hWs i.1) (f i) G (hfW i) φ y)` and prove the remaining obligations. Introduce and unpack `x ⟨-, rfl⟩ s' hs'`.

Rewrite using `[maDens_sheet_finset_sum Finset.univ F f φ hs' hsum fun i _ => hfs i, Finset.mul_sum]`. Unfold `chartInt`. Simplify using `only [hL, hR]`. Rewrite using `[integral_finsetSum _ fun i _ => (hpiece i).2.1, integral_finsetSum _ fun i _ => (hpiece i).2.2]`. Conclude with `Finset.sum_congr rfl fun i _ => (hpiece i).1`.
-/
theorem StokesOffDiscriminant.proof : StokesOffDiscriminant.Statement := by
  intro n d J A P _ _ _ _ hsheet F G φ hF hG hφ hFc ⟨U, hUo, hPU, hFU⟩
  set K := closure {x | x ∈ zeroSet J ∧ F x ≠ 0} with hKdef
  have hKZ : K ⊆ zeroSet J :=
    closure_minimal (fun x hx => hx.1) (SheetSumMeasurable.isClosed_zeroSet J)
  have hKU : K ⊆ Uᶜ :=
    closure_minimal (fun x hx hxU => hx.2 (hFU x ⟨hxU, hx.1⟩)) hUo.isClosed_compl
  have hKc : IsCompact K := hFc.of_isClosed_subset isClosed_closure (closure_mono fun x hx => hx.2)
  have hwin : ∀ x : K, ∃ (s : (Fin (d + 1) → ℂ) → Fin n → ℂ) (V : Set (Fin (d + 1) → ℂ))
      (W : Set (Fin n → ℂ)), IsOpen V ∧ IsOpen W ∧ (x : Fin n → ℂ) ∈ W ∧ DifferentiableOn ℂ s V ∧
        (∀ y ∈ V, A *ᵥ s y = y ∧ s y ∈ zeroSet J) ∧
        ∀ x' ∈ zeroSet J ∩ W, A *ᵥ x' ∈ V ∧ IsSheetAt J A x' s := by
    rintro ⟨x, hx⟩
    obtain ⟨s, hs⟩ := hsheet x (hKZ hx) fun h => hKU hx (hPU h)
    exact ⟨s, window_of_sheet hs⟩
  choose s V W hVo hWo hxW hsd hsec hWs using hwin
  obtain ⟨t, ht⟩ := hKc.elim_finite_subcover W hWo fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, hxW _⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, Fin n → ℂ) isClosed_closure
    (fun i : t => W i.1) (fun i => hWo i.1) fun x hx => by
      obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.1 (ht hx)
      exact Set.mem_iUnion.2 ⟨⟨i, hi⟩, hxi⟩
  have hρs : ∀ i, ContDiff ℝ ∞ (ρ i) := fun i => contMDiff_iff_contDiff.1 (ρ i).contMDiff
  set f : t → (Fin n → ℂ) → ℝ := fun i x => ρ i x * F x with hfdef
  have hsum : ∀ x ∈ zeroSet J, F x = ∑ i, f i x := by
    intro x hxZ
    by_cases hK : x ∈ K
    · have h1 := ρ.sum_eq_one hK
      rw [finsum_eq_sum_of_fintype] at h1
      simp only [hfdef, ← Finset.sum_mul, h1, one_mul]
    · have hF0 : F x = 0 := by_contra fun h => hK (subset_closure ⟨hxZ, h⟩)
      simp [hfdef, hF0]
  have hfs : ∀ i, SmoothNear (zeroSet J) (f i) := by
    obtain ⟨O, hO, hZO, hFO⟩ := hF
    exact fun i => ⟨O, hO, hZO, (hρs i).contDiffOn.mul hFO⟩
  have hfW : ∀ i, tsupport (f i) ⊆ W i.1 := fun i => tsupport_mul_subset_left.trans (hρ i)
  have hpiece := fun i : t => window_stokes (hVo i.1) (hsd i.1) (hsec i.1) (hWs i.1) (f i) G φ
    (hfs i) hG hφ hFc.mul_left (hfW i)
  have hL : ∀ y, chartDens J A F (vecCons G φ) y = ∑ i, chartDens J A (f i) (vecCons G φ) y := by
    intro y
    unfold chartDens
    refine sheetSum_finset_sum Finset.univ _
      (fun i x s' => f i x * ReciprocityTheory.AnForm.maDens (fun k => vecCons G φ k ∘ s') y) ?_
      fun i _ => finite_support_sheetTerm_window
        (sheetTerm_weight_window (hsec i.1) (hWs i.1) (f i) (hfW i) _ y)
    intro x hx s' _
    rw [hsum x hx.1, Finset.sum_mul]
  have hR : ∀ y, chartDens J A G (vecCons F φ) y = ∑ i, chartDens J A G (vecCons (f i) φ) y := by
    intro y
    unfold chartDens
    refine sheetSum_finset_sum Finset.univ _
      (fun i x s' => G x * ReciprocityTheory.AnForm.maDens (fun k => vecCons (f i) φ k ∘ s') y) ?_
      fun i _ => finite_support_sheetTerm_window
        (sheetTerm_cons_window (hVo i.1) (hsd i.1) (hsec i.1) (hWs i.1) (f i) G (hfW i) φ y)
    rintro x ⟨-, rfl⟩ s' hs'
    rw [maDens_sheet_finset_sum Finset.univ F f φ hs' hsum fun i _ => hfs i, Finset.mul_sum]
  unfold chartInt
  simp only [hL, hR]
  rw [integral_finsetSum _ fun i _ => (hpiece i).2.1, integral_finsetSum _ fun i _ => (hpiece i).2.2]
  exact Finset.sum_congr rfl fun i _ => (hpiece i).1

end

end GroundTheory.Heights₂.Heights
