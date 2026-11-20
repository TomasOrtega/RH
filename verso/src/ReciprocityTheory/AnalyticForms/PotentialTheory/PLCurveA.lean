import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialPullbackStatement
import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
import ReciprocityTheory.AnalyticForms.PotentialTheory.LogInt
import ReciprocityTheory.AnalyticForms.PotentialTheory.AtlasIndep
import ReciprocityTheory.AnalyticForms.PotentialTheory.Partition
import ReciprocityTheory.AnalyticForms.PotentialTheory.PotentialContDiffAt
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LintegralImageEqLintegralNormSqDetMul
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LeviOneEqLaplacianThm

namespace ReciprocityTheory.AnForm.M

open MeasureTheory FinHolAtlas Filter Topology
open scoped ContDiff

noncomputable section

namespace PLC

variable {e : ℕ} {X : Type} [TopologicalSpace X]

/- English proof (translation)
Conclude with `st_smooth_continuous A hf`.
-/
theorem continuous_of_smooth (A : FinHolAtlas e X) {f : X → ℝ} (hf : A.Smooth f) :
    Continuous f := by
  exact st_smooth_continuous A hf

/- English proof (translation)
The claim follows from `st_smooth_mul A hf hg`.
-/
theorem smooth_mul (A : FinHolAtlas e X) {f g : X → ℝ} (hf : A.Smooth f) (hg : A.Smooth g) :
    A.Smooth (fun x => f x * g x) := st_smooth_mul A hf hg

/- English proof (translation)
The claim follows from `st_smooth_sum A S hf`.
-/
theorem smooth_sum (A : FinHolAtlas e X) {ι : Type*} (S : Finset ι) {f : ι → X → ℝ}
    (hf : ∀ i, A.Smooth (f i)) : A.Smooth (fun x => ∑ i ∈ S, f i x) := st_smooth_sum A S hf

/- English proof (translation)
Take `⟨B, hB, hall, -⟩` from `atlasOfCompat A (Fin.cons ψ A.chart : Fin (A.n + 1) → OpenPartialHomeomorph X (Fin e → ℂ)) (fun i => by`. Use `Fin.cases ?_ (fun j => ?_) i` and prove the remaining obligations. Simplify using `using hψ`. Simplify using `using pa_compat_chart A j)`. Use the proof step `(fun x => by`.

Take `⟨j, hj⟩` from `A.cover x`. Conclude with `⟨j.succ, by simpa using hj⟩)`. Take `⟨j, hj⟩` from `hall 0`. Conclude with `⟨B, hB, j, by simpa using hj⟩`.
-/
theorem exists_atlas_with (A : FinHolAtlas e X) (ψ : OpenPartialHomeomorph X (Fin e → ℂ))
    (hψ : IsCompatChart A ψ) : ∃ B : FinHolAtlas e X, A.Compatible B ∧ ∃ j, B.chart j = ψ := by
  obtain ⟨B, hB, hall, -⟩ := atlasOfCompat A
    (Fin.cons ψ A.chart : Fin (A.n + 1) → OpenPartialHomeomorph X (Fin e → ℂ))
    (fun i => by
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hψ
      · simpa using pa_compat_chart A j)
    (fun x => by
      obtain ⟨j, hj⟩ := A.cover x
      exact ⟨j.succ, by simpa using hj⟩)
  obtain ⟨j, hj⟩ := hall 0
  exact ⟨B, hB, j, by simpa using hj⟩

/- English proof (translation)
Establish `hKc : IsCompact K` using `hK.isCompact`. Establish `hK'c : IsCompact (ψ '' K)` using `hKc.image_of_continuousOn (ψ.continuousOn.mono hKψ)`. Establish `hK'U : ψ '' K ⊆ ψ.target`. Introduce and unpack `_ ⟨z, hz, rfl⟩`. Conclude with `ψ.map_source (hKψ hz)`.

Establish `hb : ∀ x ∈ ψ.target, ∃ f : (Fin e → ℂ) → ℝ, tsupport f ⊆ ψ.target ∧ HasCompactSupport f ∧ ContDiff ℝ ∞ f ∧ Set.range f ⊆ Set.Icc 0 1 ∧ f x = 1` using `fun x hx => exists_contDiff_tsupport_subset (n := ⊤) (ψ.open_target.mem_nhds hx)`. Use `choose! F hFs hFc hFd hFr hF1 using hb`. Take `⟨t, ht⟩` from `hK'c.elim_finite_subcover (fun i : ψ '' K => {y | 1 / 2 < F i y}) (fun i => isOpen_lt continuous_const (hFd i (hK'U i.2)).continuous) (fun y hy => Set.mem_iUnion.mpr ⟨⟨y, hy⟩, by show (1 : ℝ) / 2 < F y y`. Rewrite using `[hF1 y (hK'U hy)]`. Use the proof step `norm_num⟩)`.

Establish `hgd : ContDiff ℝ ∞ (fun y => ∑ i ∈ t, F i y)` using `contDiffOn_univ.mp (ContDiffOn.sum (fun i _ => (hFd i (hK'U i.2)).contDiffOn))`. Establish `hgK : ∀ y ∈ ψ '' K, 1 / 2 ≤ ∑ i ∈ t, F i y`. Introduce `y hy`. Take `⟨i, hi, hyi⟩` from `Set.mem_iUnion₂.mp (ht hy)`. Conclude with `le_trans (le_of_lt hyi) (Finset.single_le_sum (f := fun j : ψ '' K => F j y) (fun j _ => (hFr j (hK'U j.2) (Set.mem_range_self y)).1) hi)`.

Establish `hTc : IsCompact (⋃ i ∈ t, tsupport (F i))` using `t.isCompact_biUnion (fun i _ => hFc i (hK'U i.2))`. Establish `hTU : (⋃ i ∈ t, tsupport (F i)) ⊆ ψ.target` using `Set.iUnion₂_subset (fun i _ => hFs i (hK'U i.2))`. Establish `hrd : ContDiff ℝ ∞ (fun y => Real.smoothTransition (2 * ∑ i ∈ t, F i y))` using `Real.smoothTransition.contDiff.comp (contDiff_const.mul hgd)`. Establish `hrT : ∀ y, Real.smoothTransition (2 * ∑ i ∈ t, F i y) ≠ 0 → y ∈ ⋃ i ∈ t, tsupport (F i)`. Introduce `y hy`.

Assume the negation of the conclusion as `hyT`. Apply `hy` to reduce the goal to its premises. Apply `Real.smoothTransition.zero_of_nonpos` to reduce the goal to its premises. Establish `h0 : ∑ i ∈ t, F i y = 0` using `Finset.sum_eq_zero (fun i hi => by`. Assume the negation of the conclusion as `hne`.

Conclude with `hyT (Set.mem_iUnion₂.mpr ⟨i, hi, subset_tsupport _ hne⟩))`. Rewrite using `[h0]`. Evaluate the numerical expressions. Establish `hLc : IsCompact (ψ.symm '' ⋃ i ∈ t, tsupport (F i))` using `hTc.image_of_continuousOn (ψ.continuousOn_symm.mono hTU)`. Establish `hLs : ψ.symm '' (⋃ i ∈ t, tsupport (F i)) ⊆ ψ.source`.

Introduce and unpack `_ ⟨y, hy, rfl⟩`. Conclude with `ψ.map_target (hTU hy)`. Establish `hsupp : Function.support (fun x => if x ∈ ψ.source then Real.smoothTransition (2 * ∑ i ∈ t, F i (ψ x)) else 0) ⊆ ψ.symm '' ⋃ i ∈ t, tsupport (F i)`. Introduce `x hx`. Distinguish the cases in `hxs : x ∈ ψ.source`.

Establish `hr : Real.smoothTransition (2 * ∑ i ∈ t, F i (ψ x)) ≠ 0` using `by simpa [hxs] using hx`. Conclude with `⟨ψ x, hrT _ hr, ψ.left_inv hxs⟩`. Conclude with `absurd (show (if x ∈ ψ.source then Real.smoothTransition (2 * ∑ i ∈ t, F i (ψ x)) else 0) = 0 by simp [hxs]) hx`. Use `⟨fun x => if x ∈ ψ.source then Real.smoothTransition (2 * ∑ i ∈ t, F i (ψ x)) else 0, ?_, (closure_minimal hsupp hLc.isClosed).trans hLs, ?_⟩` and prove the remaining obligations. Introduce `j`.

Use `contDiffOn_of_locally_contDiffOn (fun y hy => ?_)` and prove the remaining obligations. Establish `hyt : y ∈ (A.chart j).target` using `hy.1`. Distinguish the cases in `hp : (A.chart j).symm y ∈ ψ.source`. Establish `hopen : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' ψ.source)` using `(A.chart j).isOpen_inter_preimage_symm ψ.open_source`. Use `⟨(A.chart j).target ∩ (A.chart j).symm ⁻¹' ψ.source, hopen, ⟨hyt, hp⟩, ?_⟩` and prove the remaining obligations.

Establish `han : ContDiffOn ℝ ∞ (ψ ∘ (A.chart j).symm) ((A.chart j).target ∩ (A.chart j).symm ⁻¹' ψ.source)` using `((hψ j).1.contDiffOn hopen.uniqueDiffOn).restrict_scalars ℝ`. Use `((hrd.comp_contDiffOn han).mono Set.inter_subset_right).congr (fun w hw => ?_)` and prove the remaining obligations. Establish `hws : (A.chart j).symm w ∈ ψ.source` using `hw.2.2`. Simplify using `only [Function.comp_apply, if_pos hws]`. Use `⟨(A.chart j).target ∩ (A.chart j).symm ⁻¹' (ψ.symm '' ⋃ i ∈ t, tsupport (F i))ᶜ, (A.chart j).isOpen_inter_preimage_symm hLc.isClosed.isOpen_compl, ⟨hyt, fun hL => hp (hLs hL)⟩, ?_⟩` and prove the remaining obligations.

Use `(contDiffOn_const (c := (0 : ℝ))).congr (fun w hw => ?_)` and prove the remaining obligations. Establish `hwL : (A.chart j).symm w ∉ ψ.symm '' ⋃ i ∈ t, tsupport (F i)` using `hw.2.2`. Use `show (fun x => if x ∈ ψ.source then Real.smoothTransition (2 * ∑ i ∈ t, F i (ψ x)) else 0) ((A.chart j).symm w) = 0`. Assume the negation of the conclusion as `hne`. Conclude with `hwL (hsupp hne)`.

Introduce `z hz`. Simplify using `only [if_pos (hKψ hz)]`. Conclude with `Real.smoothTransition.one_of_one_le (by linarith [hgK (ψ z) ⟨z, hz, rfl⟩])`.
-/
theorem exists_cutoff [CompactSpace X] [T2Space X] (A : FinHolAtlas e X)
    (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (hψ : IsCompatChart A ψ) (K : Set X)
    (hK : IsClosed K) (hKψ : K ⊆ ψ.source) :
    ∃ ρ : X → ℝ, A.Smooth ρ ∧ tsupport ρ ⊆ ψ.source ∧ ∀ z ∈ K, ρ z = 1 := by
  classical

  have hKc : IsCompact K := hK.isCompact
  have hK'c : IsCompact (ψ '' K) := hKc.image_of_continuousOn (ψ.continuousOn.mono hKψ)
  have hK'U : ψ '' K ⊆ ψ.target := by
    rintro _ ⟨z, hz, rfl⟩
    exact ψ.map_source (hKψ hz)
  have hb : ∀ x ∈ ψ.target, ∃ f : (Fin e → ℂ) → ℝ, tsupport f ⊆ ψ.target ∧ HasCompactSupport f ∧
      ContDiff ℝ ∞ f ∧ Set.range f ⊆ Set.Icc 0 1 ∧ f x = 1 :=
    fun x hx => exists_contDiff_tsupport_subset (n := ⊤) (ψ.open_target.mem_nhds hx)
  choose! F hFs hFc hFd hFr hF1 using hb
  obtain ⟨t, ht⟩ := hK'c.elim_finite_subcover (fun i : ψ '' K => {y | 1 / 2 < F i y})
    (fun i => isOpen_lt continuous_const (hFd i (hK'U i.2)).continuous)
    (fun y hy => Set.mem_iUnion.mpr ⟨⟨y, hy⟩, by
      show (1 : ℝ) / 2 < F y y
      rw [hF1 y (hK'U hy)]
      norm_num⟩)

  have hgd : ContDiff ℝ ∞ (fun y => ∑ i ∈ t, F i y) :=
    contDiffOn_univ.mp (ContDiffOn.sum (fun i _ => (hFd i (hK'U i.2)).contDiffOn))
  have hgK : ∀ y ∈ ψ '' K, 1 / 2 ≤ ∑ i ∈ t, F i y := by
    intro y hy
    obtain ⟨i, hi, hyi⟩ := Set.mem_iUnion₂.mp (ht hy)
    exact le_trans (le_of_lt hyi) (Finset.single_le_sum (f := fun j : ψ '' K => F j y)
      (fun j _ => (hFr j (hK'U j.2) (Set.mem_range_self y)).1) hi)
  have hTc : IsCompact (⋃ i ∈ t, tsupport (F i)) := t.isCompact_biUnion (fun i _ => hFc i (hK'U i.2))
  have hTU : (⋃ i ∈ t, tsupport (F i)) ⊆ ψ.target := Set.iUnion₂_subset (fun i _ => hFs i (hK'U i.2))
  have hrd : ContDiff ℝ ∞ (fun y => Real.smoothTransition (2 * ∑ i ∈ t, F i y)) :=
    Real.smoothTransition.contDiff.comp (contDiff_const.mul hgd)
  have hrT : ∀ y, Real.smoothTransition (2 * ∑ i ∈ t, F i y) ≠ 0 → y ∈ ⋃ i ∈ t, tsupport (F i) := by
    intro y hy
    by_contra hyT
    apply hy
    apply Real.smoothTransition.zero_of_nonpos
    have h0 : ∑ i ∈ t, F i y = 0 := Finset.sum_eq_zero (fun i hi => by
      by_contra hne
      exact hyT (Set.mem_iUnion₂.mpr ⟨i, hi, subset_tsupport _ hne⟩))
    rw [h0]
    norm_num

  have hLc : IsCompact (ψ.symm '' ⋃ i ∈ t, tsupport (F i)) :=
    hTc.image_of_continuousOn (ψ.continuousOn_symm.mono hTU)
  have hLs : ψ.symm '' (⋃ i ∈ t, tsupport (F i)) ⊆ ψ.source := by
    rintro _ ⟨y, hy, rfl⟩
    exact ψ.map_target (hTU hy)
  have hsupp : Function.support (fun x => if x ∈ ψ.source then
      Real.smoothTransition (2 * ∑ i ∈ t, F i (ψ x)) else 0) ⊆ ψ.symm '' ⋃ i ∈ t, tsupport (F i) := by
    intro x hx
    by_cases hxs : x ∈ ψ.source
    · have hr : Real.smoothTransition (2 * ∑ i ∈ t, F i (ψ x)) ≠ 0 := by simpa [hxs] using hx
      exact ⟨ψ x, hrT _ hr, ψ.left_inv hxs⟩
    · exact absurd (show (if x ∈ ψ.source then
        Real.smoothTransition (2 * ∑ i ∈ t, F i (ψ x)) else 0) = 0 by simp [hxs]) hx
  refine ⟨fun x => if x ∈ ψ.source then Real.smoothTransition (2 * ∑ i ∈ t, F i (ψ x)) else 0,
    ?_, (closure_minimal hsupp hLc.isClosed).trans hLs, ?_⟩
  · intro j
    refine contDiffOn_of_locally_contDiffOn (fun y hy => ?_)
    have hyt : y ∈ (A.chart j).target := hy.1
    by_cases hp : (A.chart j).symm y ∈ ψ.source
    · have hopen : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' ψ.source) :=
        (A.chart j).isOpen_inter_preimage_symm ψ.open_source
      refine ⟨(A.chart j).target ∩ (A.chart j).symm ⁻¹' ψ.source, hopen, ⟨hyt, hp⟩, ?_⟩
      have han : ContDiffOn ℝ ∞ (ψ ∘ (A.chart j).symm)
          ((A.chart j).target ∩ (A.chart j).symm ⁻¹' ψ.source) :=
        ((hψ j).1.contDiffOn hopen.uniqueDiffOn).restrict_scalars ℝ
      refine ((hrd.comp_contDiffOn han).mono Set.inter_subset_right).congr (fun w hw => ?_)
      have hws : (A.chart j).symm w ∈ ψ.source := hw.2.2
      simp only [Function.comp_apply, if_pos hws]
    · refine ⟨(A.chart j).target ∩ (A.chart j).symm ⁻¹' (ψ.symm '' ⋃ i ∈ t, tsupport (F i))ᶜ,
        (A.chart j).isOpen_inter_preimage_symm hLc.isClosed.isOpen_compl,
        ⟨hyt, fun hL => hp (hLs hL)⟩, ?_⟩
      refine (contDiffOn_const (c := (0 : ℝ))).congr (fun w hw => ?_)
      have hwL : (A.chart j).symm w ∉ ψ.symm '' ⋃ i ∈ t, tsupport (F i) := hw.2.2
      show (fun x => if x ∈ ψ.source then
        Real.smoothTransition (2 * ∑ i ∈ t, F i (ψ x)) else 0) ((A.chart j).symm w) = 0
      by_contra hne
      exact hwL (hsupp hne)
  · intro z hz
    simp only [if_pos (hKψ hz)]
    exact Real.smoothTransition.one_of_one_le (by linarith [hgK (ψ z) ⟨z, hz, rfl⟩])

/- English proof (translation)
Establish `hU : (Finset.univ : Finset (Finset (Fin 1))) = {∅, {0}}` using `by decide`. Unfold `ReciprocityTheory.AnForm.maDens ReciprocityTheory.AnForm.mdisc`. Rewrite using `[hU, Finset.sum_pair (by decide)]`. Simplify using `[Matrix.det_fin_one]`.
-/
theorem maDens_one (φ : Fin 1 → (Fin 1 → ℂ) → ℝ) (z : Fin 1 → ℂ) :
    ReciprocityTheory.AnForm.maDens φ z = 2 / Real.pi * (ReciprocityTheory.AnForm.hessC (φ 0) z 0 0).re := by
  have hU : (Finset.univ : Finset (Finset (Fin 1))) = {∅, {0}} := by decide
  unfold ReciprocityTheory.AnForm.maDens ReciprocityTheory.AnForm.mdisc
  rw [hU, Finset.sum_pair (by decide)]
  simp [Matrix.det_fin_one]

/- English proof (translation)
Establish `hH : ∀ k, ReciprocityTheory.AnForm.hessC (φ k) z = ReciprocityTheory.AnForm.hessC (ψ k) z`. Introduce `k`. Establish `hF : fderiv ℝ (fderiv ℝ (φ k)) z = fderiv ℝ (fderiv ℝ (ψ k)) z` using `(h k).fderiv.fderiv_eq`. Unfold `ReciprocityTheory.AnForm.hessC`. Rewrite using `[hF]`.

Unfold `ReciprocityTheory.AnForm.maDens`. Simplify using `only [hH]`.
-/
theorem maDens_congr {D : ℕ} (φ ψ : Fin D → (Fin D → ℂ) → ℝ) (z : Fin D → ℂ)
    (h : ∀ k, φ k =ᶠ[𝓝 z] ψ k) : ReciprocityTheory.AnForm.maDens φ z = ReciprocityTheory.AnForm.maDens ψ z := by
  have hH : ∀ k, ReciprocityTheory.AnForm.hessC (φ k) z = ReciprocityTheory.AnForm.hessC (ψ k) z := by
    intro k
    have hF : fderiv ℝ (fderiv ℝ (φ k)) z = fderiv ℝ (fderiv ℝ (ψ k)) z := (h k).fderiv.fderiv_eq
    unfold ReciprocityTheory.AnForm.hessC
    rw [hF]
  unfold ReciprocityTheory.AnForm.maDens
  simp only [hH]

/- English proof (translation)
Rewrite using `[maDens_one]`. Simplify using `only [Matrix.cons_val_zero]`. Establish `hH : ReciprocityTheory.AnForm.hessC f z = ReciprocityTheory.AnForm.hessC (0 : (Fin 1 → ℂ) → ℝ) z`. Establish `hF : fderiv ℝ (fderiv ℝ f) z = fderiv ℝ (fderiv ℝ (0 : (Fin 1 → ℂ) → ℝ)) z` using `h.fderiv.fderiv_eq`. Unfold `ReciprocityTheory.AnForm.hessC`.

Rewrite using `[hF]`. Rewrite using `[hH]`. Simplify using `[ReciprocityTheory.AnForm.hessC]`.
-/
theorem maDens_one_eq_zero (f : (Fin 1 → ℂ) → ℝ) (z : Fin 1 → ℂ) (h : f =ᶠ[𝓝 z] 0) :
    ReciprocityTheory.AnForm.maDens ![f] z = 0 := by
  rw [maDens_one]
  simp only [Matrix.cons_val_zero]
  have hH : ReciprocityTheory.AnForm.hessC f z = ReciprocityTheory.AnForm.hessC (0 : (Fin 1 → ℂ) → ℝ) z := by
    have hF : fderiv ℝ (fderiv ℝ f) z = fderiv ℝ (fderiv ℝ (0 : (Fin 1 → ℂ) → ℝ)) z :=
      h.fderiv.fderiv_eq
    unfold ReciprocityTheory.AnForm.hessC
    rw [hF]
  rw [hH]
  simp [ReciprocityTheory.AnForm.hessC]

/- English proof (translation)
Apply `maDens_one_eq_zero` to reduce the goal to its premises. Establish `ho : IsOpen (ψ.target ∩ ψ.symm ⁻¹' (tsupport v)ᶜ)` using `ψ.isOpen_inter_preimage_symm (isClosed_tsupport v).isOpen_compl`. Use `filter_upwards [ho.mem_nhds ⟨hy, hv⟩] with w hw`. Use `show v (ψ.symm w) = 0`. Conclude with `image_eq_zero_of_notMem_tsupport hw.2`.
-/
theorem maDens_comp_symm_eq_zero (ψ : OpenPartialHomeomorph X (Fin 1 → ℂ)) (v : X → ℝ)
    {y : Fin 1 → ℂ} (hy : y ∈ ψ.target) (hv : ψ.symm y ∉ tsupport v) :
    ReciprocityTheory.AnForm.maDens ![v ∘ ψ.symm] y = 0 := by
  apply maDens_one_eq_zero
  have ho : IsOpen (ψ.target ∩ ψ.symm ⁻¹' (tsupport v)ᶜ) :=
    ψ.isOpen_inter_preimage_symm (isClosed_tsupport v).isOpen_compl
  filter_upwards [ho.mem_nhds ⟨hy, hv⟩] with w hw
  show v (ψ.symm w) = 0
  exact image_eq_zero_of_notMem_tsupport hw.2

/- English proof (translation)
Unfold `locDens`. Use `congr 1`. Use function extensionality and compare the values at `i y'`. Use `fin_cases i`. Both sides reduce to the same expression.
-/
theorem locDens_ofFun (A : FinHolAtlas 1 X) (v : X → ℝ) (j : Fin A.n) (y : Fin 1 → ℂ) :
    locDens A ![LocPot.ofFun v] j y = ReciprocityTheory.AnForm.maDens ![v ∘ (A.chart j).symm] y := by
  unfold locDens
  congr 1
  funext i y'
  fin_cases i
  rfl

/- English proof (translation)
Simplify using `only [locDens, h]`.
-/
theorem locDens_congr_phi (A : FinHolAtlas e X) (Φ Ψ : Fin e → LocPot X)
    (h : ∀ i a b, (Φ i).φ a b = (Ψ i).φ a b) (j : Fin A.n) (y : Fin e → ℂ) :
    locDens A Φ j y = locDens A Ψ j y := by
  simp only [locDens, h]

/- English proof (translation)
Unfold `mInt`. Use `split_ifs with hP`. Unfold `integralWith`. Use `Finset.sum_congr rfl (fun j _ => ?_)` and prove the remaining obligations. Use `MeasureTheory.integral_congr_ae ?_` and prove the remaining obligations.

Use `filter_upwards [h j] with y hy`. Rewrite using `[mul_assoc, hy, ← mul_assoc]`. Both sides reduce to the same expression.
-/
theorem mInt_congr (A : FinHolAtlas e X) (Φ Ψ : Fin e → LocPot X) (g g' : X → ℝ)
    (h : ∀ j, ∀ᵐ y ∂(volume.restrict (A.chart j).target),
      g ((A.chart j).symm y) * locDens A Φ j y = g' ((A.chart j).symm y) * locDens A Ψ j y) :
    mInt A Φ g = mInt A Ψ g' := by
  unfold mInt
  split_ifs with hP
  · unfold integralWith
    refine Finset.sum_congr rfl (fun j _ => ?_)
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [h j] with y hy
    rw [mul_assoc, hy, ← mul_assoc]
  · rfl

/- English proof (translation)
The claim follows from `mInt_congr A Φ Ψ g g (fun j => Filter.Eventually.of_forall (fun y => by rw [locDens_congr_phi A Φ Ψ h j y]))`.
-/
theorem mInt_congr_phi (A : FinHolAtlas e X) (Φ Ψ : Fin e → LocPot X)
    (h : ∀ i a b, (Φ i).φ a b = (Ψ i).φ a b) (g : X → ℝ) : mInt A Φ g = mInt A Ψ g :=
  mInt_congr A Φ Ψ g g (fun j => Filter.Eventually.of_forall (fun y => by
    rw [locDens_congr_phi A Φ Ψ h j y]))

/- English proof (translation)
Unfold `mInt`. Use `split_ifs with hP`. Simplify using `[integralWith]`. Both sides reduce to the same expression.
-/
theorem mInt_zero (A : FinHolAtlas e X) (Φ : Fin e → LocPot X) : mInt A Φ (fun _ => 0) = 0 := by
  unfold mInt
  split_ifs with hP
  · simp [integralWith]
  · rfl

/- English proof (translation)
Use `mInt_congr A _ _ g g' (fun j => ?_)` and prove the remaining obligations. Use `filter_upwards [MeasureTheory.ae_restrict_mem (A.chart j).open_target.measurableSet] with y hy`. Distinguish the cases in `hs : (A.chart j).symm y ∈ tsupport v`. Rewrite using `[h _ hs]`. Rewrite using `[locDens_ofFun, maDens_comp_symm_eq_zero _ v hy hs]`.

Simplify using the standard rewrite rules.
-/
theorem mInt_ofFun_congr (A : FinHolAtlas 1 X) (v : X → ℝ) (g g' : X → ℝ)
    (h : ∀ z ∈ tsupport v, g z = g' z) :
    mInt A ![LocPot.ofFun v] g = mInt A ![LocPot.ofFun v] g' := by
  refine mInt_congr A _ _ g g' (fun j => ?_)
  filter_upwards [MeasureTheory.ae_restrict_mem (A.chart j).open_target.measurableSet] with y hy
  by_cases hs : (A.chart j).symm y ∈ tsupport v
  · rw [h _ hs]
  · rw [locDens_ofFun, maDens_comp_symm_eq_zero _ v hy hs]
    simp

/- English proof (translation)
Introduce `j K hK hc`. Use `(MeasureTheory.Integrable.sub (hf j K hK hc) (hg j K hK hc)).congr (Filter.Eventually.of_forall (fun y => ?_))` and prove the remaining obligations. Simplify using `only [Pi.sub_apply, sub_mul]`.
-/
theorem mIntegrable_sub (A : FinHolAtlas e X) (Φ : Fin e → LocPot X) {f g : X → ℝ}
    (hf : MIntegrable A Φ f) (hg : MIntegrable A Φ g) : MIntegrable A Φ (fun x => f x - g x) := by
  intro j K hK hc
  refine (MeasureTheory.Integrable.sub (hf j K hK hc) (hg j K hK hc)).congr
    (Filter.Eventually.of_forall (fun y => ?_))
  simp only [Pi.sub_apply, sub_mul]

def plDefect (A : FinHolAtlas 1 X) (L : LocPot X) (s : X → X → ℂ) {r : ℕ} (m : Fin r → ℕ)
    (p : Fin r → X) (f : X → ℝ) : ℝ :=
  mInt A ![LocPot.ofFun f] (logNormSec L s) - (∑ k, (m k : ℝ) * f (p k) - mInt A ![L] f)

end PLC

end

end ReciprocityTheory.AnForm.M
