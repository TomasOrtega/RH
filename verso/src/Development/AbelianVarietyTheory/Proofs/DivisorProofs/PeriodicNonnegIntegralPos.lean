import Mathlib
open MeasureTheory Set
open scoped ContDiff

namespace GlobalTheory

/- English proof (translation)
Introduce `ι _ f hf hnn hper ⟨x, hx⟩`. Take `⟨y, hy⟩ : ∃ y : ι → ℝ, y = fun i => Int.fract (x i)` from `⟨_, rfl⟩`. Establish `hxy : x = y + fun i => ((⌊x i⌋ : ℤ) : ℝ)`. Use function extensionality and compare the values at `i`. Substitute `hy` using the available equality.

Conclude with `(Int.fract_add_floor (x i)).symm`. Establish `hyne : f y ≠ 0`. Use `hper y (fun i => ⌊x i⌋)` as an intermediate fact. Rewrite `this` using `[← hxy]`. Rewrite using `[← this]`.

Conclude with `hx`. Use `set V : Set (ι → ℝ) := pi univ (fun _ => Ioo (0:ℝ) 1) with hV`. Establish `hVopen : IsOpen V` using `isOpen_set_pi finite_univ (fun _ _ => isOpen_Ioo)`. Establish `hyV : y ∈ closure V`. Rewrite using `[hV, closure_pi_set]`.

Introduce `i _`. Rewrite using `[closure_Ioo (zero_ne_one)]`. Substitute `hy` using the available equality. Conclude with `⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩`. Establish `hWopen : IsOpen (Function.support f)` using `isOpen_ne_fun hf continuous_const`.

Establish `hne : (Function.support f ∩ V).Nonempty` using `mem_closure_iff.mp hyV _ hWopen hyne`. Establish `hpos : 0 < volume (Function.support f ∩ V)` using `(hWopen.inter hVopen).measure_pos volume hne`. Establish `hVsub : V ⊆ Icc (0 : ι → ℝ) 1`. Rewrite using `[← pi_univ_Icc]`. Conclude with `pi_mono (fun _ _ => Ioo_subset_Icc_self)`.

Rewrite using `[setIntegral_pos_iff_support_of_nonneg_ae]`. Conclude with `lt_of_lt_of_le hpos (measure_mono (inter_subset_inter_right _ hVsub))`. Conclude with `Filter.Eventually.of_forall (fun z => hnn z)`. Conclude with `hf.continuousOn.integrableOn_compact isCompact_Icc`.
-/
theorem integral_unitCube_pos_of_periodic :
    ∀ (ι : Type) [Fintype ι] (f : (ι → ℝ) → ℝ), Continuous f → (∀ x, 0 ≤ f x) →
      (∀ (x : ι → ℝ) (n : ι → ℤ), f (x + fun i => (n i : ℝ)) = f x) → (∃ x, f x ≠ 0) →
      0 < ∫ x in Icc (0 : ι → ℝ) 1, f x := by
  intro ι _ f hf hnn hper ⟨x, hx⟩
  obtain ⟨y, hy⟩ : ∃ y : ι → ℝ, y = fun i => Int.fract (x i) := ⟨_, rfl⟩
  have hxy : x = y + fun i => ((⌊x i⌋ : ℤ) : ℝ) := by
    funext i; subst hy; exact (Int.fract_add_floor (x i)).symm
  have hyne : f y ≠ 0 := by
    have := hper y (fun i => ⌊x i⌋)
    rw [← hxy] at this; rw [← this]; exact hx
  set V : Set (ι → ℝ) := pi univ (fun _ => Ioo (0:ℝ) 1) with hV
  have hVopen : IsOpen V := isOpen_set_pi finite_univ (fun _ _ => isOpen_Ioo)
  have hyV : y ∈ closure V := by
    rw [hV, closure_pi_set]
    intro i _
    rw [closure_Ioo (zero_ne_one)]
    subst hy
    exact ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
  have hWopen : IsOpen (Function.support f) := isOpen_ne_fun hf continuous_const
  have hne : (Function.support f ∩ V).Nonempty :=
    mem_closure_iff.mp hyV _ hWopen hyne
  have hpos : 0 < volume (Function.support f ∩ V) := (hWopen.inter hVopen).measure_pos volume hne
  have hVsub : V ⊆ Icc (0 : ι → ℝ) 1 := by
    rw [← pi_univ_Icc]
    exact pi_mono (fun _ _ => Ioo_subset_Icc_self)
  rw [setIntegral_pos_iff_support_of_nonneg_ae]
  · exact lt_of_lt_of_le hpos (measure_mono (inter_subset_inter_right _ hVsub))
  · exact Filter.Eventually.of_forall (fun z => hnn z)
  · exact hf.continuousOn.integrableOn_compact isCompact_Icc

end GlobalTheory
