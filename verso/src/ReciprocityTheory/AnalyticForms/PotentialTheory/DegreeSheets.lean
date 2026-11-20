import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialPullbackStatement
import ReciprocityTheory.AnalyticForms.PotentialTheory.Pullback
import ReciprocityTheory.AnalyticForms.PotentialTheory.AnalyticSubsetChartLocal
import ReciprocityTheory.AnalyticForms.PotentialTheory.IntegrableOnTargetOfTsupport
import ReciprocityTheory.AnalyticForms.PotentialTheory.Partition
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential

namespace ReciprocityTheory.AnForm.M

open FinHolAtlas Topology

noncomputable section

variable {e : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/- English proof (translation)
Unfold `FinHolAtlas.IsAnalyticSubset at hS`. Rewrite using `[← isOpen_compl_iff, isOpen_iff_mem_nhds]`. Introduce `x hx`. Take `⟨W, hW, hxW, r, f, hf, hSW⟩` from `hS x`. Establish `hne : ∃ i, f i x ≠ 0`.

Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Apply `hx` to reduce the goal to its premises. Establish `hxSW : x ∈ S ∩ W`. Rewrite using `[hSW]`.

Conclude with `⟨hxW, hcon⟩`. Conclude with `hxSW.1`. Take `⟨i, hi⟩` from `hne`. Establish `hca : ContinuousAt (f i) x`. Take `⟨j, hxj⟩` from `A.cover x`.

Establish `h : ∀ k, AnalyticOnNhd ℂ ((f i) ∘ (A.chart k).symm) ((A.chart k).target ∩ (A.chart k).symm ⁻¹' W)` using `hf i`. Establish `hmem : (A.chart j) x ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' W`. Use `⟨(A.chart j).map_source hxj, ?_⟩` and prove the remaining obligations. Use `show (A.chart j).symm ((A.chart j) x) ∈ W`. Rewrite using `[(A.chart j).left_inv hxj]`.

Conclude with `hxW`. Establish `h1 : ContinuousAt ((f i ∘ (A.chart j).symm) ∘ (A.chart j)) x` using `((h j _ hmem).continuousAt).comp ((A.chart j).continuousAt hxj)`. Use `h1.congr ?_` and prove the remaining obligations. Use `filter_upwards [(A.chart j).open_source.mem_nhds hxj] with y hy`. Simplify using `only [Function.comp_apply, (A.chart j).left_inv hy]`.

Use `filter_upwards [hW.mem_nhds hxW, hca.eventually_ne hi] with y hyW hyi hyS`. Establish `hy : y ∈ S ∩ W` using `⟨hyS, hyW⟩`. Rewrite `hy` using `[hSW]`. Conclude with `hyi (hy.2 i)`.
-/
theorem isClosed_of_isAnalyticSubset' (A : FinHolAtlas e X) {S : Set X}
    (hS : A.IsAnalyticSubset S) : IsClosed S := by
  unfold FinHolAtlas.IsAnalyticSubset at hS
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨W, hW, hxW, r, f, hf, hSW⟩ := hS x
  have hne : ∃ i, f i x ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hx
    have hxSW : x ∈ S ∩ W := by
      rw [hSW]
      exact ⟨hxW, hcon⟩
    exact hxSW.1
  obtain ⟨i, hi⟩ := hne
  have hca : ContinuousAt (f i) x := by
    obtain ⟨j, hxj⟩ := A.cover x
    have h : ∀ k, AnalyticOnNhd ℂ ((f i) ∘ (A.chart k).symm)
        ((A.chart k).target ∩ (A.chart k).symm ⁻¹' W) := hf i
    have hmem : (A.chart j) x ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' W := by
      refine ⟨(A.chart j).map_source hxj, ?_⟩
      show (A.chart j).symm ((A.chart j) x) ∈ W
      rw [(A.chart j).left_inv hxj]
      exact hxW
    have h1 : ContinuousAt ((f i ∘ (A.chart j).symm) ∘ (A.chart j)) x :=
      ((h j _ hmem).continuousAt).comp ((A.chart j).continuousAt hxj)
    refine h1.congr ?_
    filter_upwards [(A.chart j).open_source.mem_nhds hxj] with y hy
    simp only [Function.comp_apply, (A.chart j).left_inv hy]
  filter_upwards [hW.mem_nhds hxW, hca.eventually_ne hi] with y hyW hyi hyS
  have hy : y ∈ S ∩ W := ⟨hyS, hyW⟩
  rw [hSW] at hy
  exact hyi (hy.2 i)

/- English proof (translation)
Take `⟨j, hyj⟩` from `B.cover y`. Take `⟨k, hk⟩` from `A.cover (h y)`. Establish `hb : (B.chart j) y ∈ (B.chart j).target ∩ (B.chart j).symm ⁻¹' (h ⁻¹' (A.chart k).source)`. Use `⟨(B.chart j).map_source hyj, ?_⟩` and prove the remaining obligations. Use `show h ((B.chart j).symm ((B.chart j) y)) ∈ (A.chart k).source`.

Rewrite using `[(B.chart j).left_inv hyj]`. Conclude with `hk`. Establish `han` using `hh.2 j k ((B.chart j) y) hb`. Establish `hdet` using `hd.2.2.2.2.2 j k ((B.chart j) y) ((B.chart j).map_source hyj) (by rw [(B.chart j).left_inv hyj]; exact hy) (by rw [(B.chart j).left_inv hyj]; exact hk)`. Use `set L := (LinearMap.equivOfDetNeZero _ hdet).toContinuousLinearEquiv with hL`.

Establish `hstrict : HasStrictFDerivAt ((A.chart k) ∘ h ∘ (B.chart j).symm) (L : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) ((B.chart j) y)` using `han.hasStrictFDerivAt.congr_fderiv (by ext v; rfl)`. Use `set Φ := hstrict.toOpenPartialHomeomorph ((A.chart k) ∘ h ∘ (B.chart j).symm) with hΦ`. Establish `hcoe : (Φ : (Fin e → ℂ) → (Fin e → ℂ)) = (A.chart k) ∘ h ∘ (B.chart j).symm` using `hstrict.toOpenPartialHomeomorph_coe`. Establish `hsrc : (B.chart j) y ∈ Φ.source` using `hstrict.mem_toOpenPartialHomeomorph_source`. Establish `hU : IsOpen (h ⁻¹' (A.chart k).source)` using `(A.chart k).open_source.preimage hh.1`.

Use `⟨(((B.chart j).trans Φ).trans (A.chart k).symm).restrOpen _ hU, ?_, ?_, j, ?_⟩` and prove the remaining obligations. Rewrite using `[OpenPartialHomeomorph.restrOpen_source, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.trans_source]`. Use `⟨⟨⟨hyj, hsrc⟩, ?_⟩, hk⟩` and prove the remaining obligations. Use `show Φ ((B.chart j) y) ∈ (A.chart k).target`. Rewrite using `[hcoe]`.

Use `show (A.chart k) (h ((B.chart j).symm ((B.chart j) y))) ∈ (A.chart k).target`. Rewrite using `[(B.chart j).left_inv hyj]`. Conclude with `(A.chart k).map_source hk`. Introduce `y' hy'`. Rewrite `hy'` using `[OpenPartialHomeomorph.restrOpen_source, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.trans_source]`.

Take `⟨⟨⟨hy1, -⟩, -⟩, hy4⟩` from `hy'`. Use `show h y' = (A.chart k).symm (Φ ((B.chart j) y'))`. Rewrite using `[hcoe]`. Use `show h y' = (A.chart k).symm ((A.chart k) (h ((B.chart j).symm ((B.chart j) y'))))`. Rewrite using `[(B.chart j).left_inv hy1, (A.chart k).left_inv hy4]`.

Introduce `y' hy'`. Rewrite `hy'` using `[OpenPartialHomeomorph.restrOpen_source, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.trans_source]`. Conclude with `hy'.1.1.1`.
-/
theorem exists_localHomeomorph_of_isDegreeOff {A : FinHolAtlas e X} {B : FinHolAtlas e Y}
    {h : Y → X} (hh : HoloMap B A h) {d : ℕ} {S : Set X} (hd : IsDegreeOff A B h d S) (y : Y)
    (hy : h y ∉ S) :
    ∃ E : OpenPartialHomeomorph Y X, y ∈ E.source ∧ Set.EqOn h E E.source ∧
      ∃ j : Fin B.n, E.source ⊆ (B.chart j).source := by
  obtain ⟨j, hyj⟩ := B.cover y
  obtain ⟨k, hk⟩ := A.cover (h y)
  have hb : (B.chart j) y ∈ (B.chart j).target ∩ (B.chart j).symm ⁻¹' (h ⁻¹' (A.chart k).source) := by
    refine ⟨(B.chart j).map_source hyj, ?_⟩
    show h ((B.chart j).symm ((B.chart j) y)) ∈ (A.chart k).source
    rw [(B.chart j).left_inv hyj]
    exact hk
  have han := hh.2 j k ((B.chart j) y) hb
  have hdet := hd.2.2.2.2.2 j k ((B.chart j) y) ((B.chart j).map_source hyj)
    (by rw [(B.chart j).left_inv hyj]; exact hy) (by rw [(B.chart j).left_inv hyj]; exact hk)
  set L := (LinearMap.equivOfDetNeZero _ hdet).toContinuousLinearEquiv with hL
  have hstrict : HasStrictFDerivAt ((A.chart k) ∘ h ∘ (B.chart j).symm)
      (L : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) ((B.chart j) y) :=
    han.hasStrictFDerivAt.congr_fderiv (by ext v; rfl)
  set Φ := hstrict.toOpenPartialHomeomorph ((A.chart k) ∘ h ∘ (B.chart j).symm) with hΦ
  have hcoe : (Φ : (Fin e → ℂ) → (Fin e → ℂ)) = (A.chart k) ∘ h ∘ (B.chart j).symm :=
    hstrict.toOpenPartialHomeomorph_coe
  have hsrc : (B.chart j) y ∈ Φ.source := hstrict.mem_toOpenPartialHomeomorph_source
  have hU : IsOpen (h ⁻¹' (A.chart k).source) := (A.chart k).open_source.preimage hh.1
  refine ⟨(((B.chart j).trans Φ).trans (A.chart k).symm).restrOpen _ hU, ?_, ?_, j, ?_⟩
  · rw [OpenPartialHomeomorph.restrOpen_source, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.trans_source]
    refine ⟨⟨⟨hyj, hsrc⟩, ?_⟩, hk⟩
    show Φ ((B.chart j) y) ∈ (A.chart k).target
    rw [hcoe]
    show (A.chart k) (h ((B.chart j).symm ((B.chart j) y))) ∈ (A.chart k).target
    rw [(B.chart j).left_inv hyj]
    exact (A.chart k).map_source hk
  · intro y' hy'
    rw [OpenPartialHomeomorph.restrOpen_source, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.trans_source] at hy'
    obtain ⟨⟨⟨hy1, -⟩, -⟩, hy4⟩ := hy'
    show h y' = (A.chart k).symm (Φ ((B.chart j) y'))
    rw [hcoe]
    show h y' = (A.chart k).symm ((A.chart k) (h ((B.chart j).symm ((B.chart j) y'))))
    rw [(B.chart j).left_inv hy1, (A.chart k).left_inv hy4]
  · intro y' hy'
    rw [OpenPartialHomeomorph.restrOpen_source, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.trans_source] at hy'
    exact hy'.1.1.1

/- English proof (translation)
Establish `hSc : IsClosed S` using `isClosed_of_isAnalyticSubset' A hd.1`. Establish `hloc : ∀ y : (h ⁻¹' {x} : Set Y), ∃ E : OpenPartialHomeomorph Y X, y.1 ∈ E.source ∧ Set.EqOn h E E.source ∧ ∃ j : Fin B.n, E.source ⊆ (B.chart j).source` using `fun y => exists_localHomeomorph_of_isDegreeOff hh hd y.1 (by rw [show h y.1 = x from y.2]; exact hx)`. Use `choose E hEy hEeq jE hjE using hloc`. Establish `hFc : IsCompact (h ⁻¹' {x})` using `(isClosed_singleton.preimage hh.1).isCompact`. Establish `hFfin : (h ⁻¹' {x}).Finite`.

Take `⟨t, ht⟩` from `hFc.elim_finite_subcover (fun y => (E y).source) (fun y => (E y).open_source) (fun y hy => Set.mem_iUnion.2 ⟨⟨y, hy⟩, hEy ⟨y, hy⟩⟩)`. Use `(t.finite_toSet.image Subtype.val).subset ?_` and prove the remaining obligations. Introduce `z hz`. Take `⟨w, hwt, hzw⟩` from `Set.mem_iUnion₂.1 (ht hz)`. Establish `hzx : h z = x` using `hz`.

Establish `hwx : h w.1 = x` using `w.2`. Establish `h1 : E w w.1 = E w z`. Rewrite using `[← hEeq w hzw, ← hEeq w (hEy w), hzx, hwx]`. Conclude with `⟨w, hwt, (E w).injOn (hEy w) hzw h1⟩`. Establish `: Finite (h ⁻¹' {x})` using `hFfin.to_subtype`.

Establish `hcard : Nat.card (h ⁻¹' {x}) = d`. Rewrite using `[Nat.card_coe_set_eq]`. Conclude with `hd.2.2.2.2.1 x hx`. Set `en : Fin d ≃ (h ⁻¹' {x} : Set Y)` to `((Finite.equivFin _).trans (finCongr hcard)).symm`. Take `⟨U0, hU0, hU0d⟩` from `hFfin.t2_separation`.

Set `U : Fin d → Set Y` to `fun i => U0 (en i).1 ∩ (E (en i)).source`. Establish `hUo : ∀ i, IsOpen (U i)` using `fun i => (hU0 _).2.inter (E _).open_source`. Establish `hyU : ∀ i, (en i).1 ∈ U i` using `fun i => ⟨(hU0 _).1, hEy _⟩`. Establish `hUd : Pairwise (Function.onFun Disjoint U)`. Introduce `i i' hii'`.

Establish `hne : (en i).1 ≠ (en i').1` using `fun h' => hii' (en.injective (Subtype.ext h'))`. Conclude with `(hU0d (en i).2 (en i').2 hne).mono Set.inter_subset_left Set.inter_subset_left`. Establish `hhU : ∀ i, h '' U i = E (en i) '' U i` using `fun i => ((hEeq (en i)).mono Set.inter_subset_right).image_eq`. Establish `hhUo : ∀ i, IsOpen (h '' U i)` using `fun i => by`. Rewrite using `[hhU]`.

Conclude with `(E _).isOpen_image_of_subset_source (hUo i) Set.inter_subset_right`. Establish `hKc : IsCompact (⋃ i, U i)ᶜ` using `(isOpen_iUnion hUo).isClosed_compl.isCompact`. Establish `hK : IsClosed (h '' (⋃ i, U i)ᶜ)` using `(hKc.image hh.1).isClosed`. Establish `hxK : x ∉ h '' (⋃ i, U i)ᶜ`. Introduce and unpack `⟨z, hzK, hzx⟩`.

Apply `hzK` to reduce the goal to its premises. Establish `hz : z ∈ h ⁻¹' {x}` using `hzx`. Use `Set.mem_iUnion.2 ⟨en.symm ⟨z, hz⟩, ?_⟩` and prove the remaining obligations. Use `hyU (en.symm ⟨z, hz⟩)` as an intermediate fact. Simplify using `using this`.

Take `⟨k, hk⟩` from `A.cover x`. Set `V : Set X` to `(⋂ i, h '' U i) ∩ (A.chart k).source ∩ (h '' (⋃ i, U i)ᶜ)ᶜ ∩ Sᶜ`. Establish `hVo : IsOpen V` using `(((isOpen_iInter_of_finite hhUo).inter (A.chart k).open_source).inter hK.isOpen_compl).inter hSc.isOpen_compl`. Establish `hVU : ∀ i, V ⊆ h '' U i` using `fun i z hz => Set.mem_iInter.1 hz.1.1.1 i`. Use `⟨V, hVo, ⟨⟨⟨Set.mem_iInter.2 fun i => ⟨(en i).1, hyU i, (en i).2⟩, hk⟩, hxK⟩, hx⟩, Set.disjoint_left.2 fun z hz hzS => hz.2 hzS, k, fun z hz => hz.1.1.2, ?_⟩` and prove the remaining obligations.

Use `⟨fun i => U i ∩ h ⁻¹' V, fun i => (hUo i).inter (hVo.preimage hh.1), ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `i i' hii'`. Conclude with `(hUd hii').mono Set.inter_subset_left Set.inter_subset_left`. Use extensionality with `z`. Prove the components needed by the constructor for the conclusion.

Introduce `hz`. Establish `hzU : z ∈ ⋃ i, U i`. Assume the negation of the conclusion as `hc`. Conclude with `hz.1.2 ⟨z, hc, rfl⟩`. Take `⟨i, hi⟩` from `Set.mem_iUnion.1 hzU`.

Conclude with `Set.mem_iUnion.2 ⟨i, hi, hz⟩`. Introduce `hz`. Take `⟨i, hi⟩` from `Set.mem_iUnion.1 hz`. Conclude with `hi.2`. Introduce `i`.

Use `⟨⟨fun z hz => hz.2, ?_, ?_⟩, jE (en i), fun z hz => hjE _ hz.1.2⟩` and prove the remaining obligations. Introduce `a ha b hb hab`. Apply `(E (en i)).injOn ha.1.2 hb.1.2` to reduce the goal to its premises. Rewrite using `[← hEeq (en i) ha.1.2, ← hEeq (en i) hb.1.2]`. Conclude with `hab`.

Introduce `v hv`. Take `⟨u, hu, rfl⟩` from `hVU i hv`. Conclude with `⟨u, ⟨hu, hv⟩, rfl⟩`.
-/
theorem degree_local_sheets' [CompactSpace Y] [T2Space Y] [T2Space X]
    {A : FinHolAtlas e X} {B : FinHolAtlas e Y} {h : Y → X} (hh : HoloMap B A h) {d : ℕ}
    {S : Set X} (hd : IsDegreeOff A B h d S) (x : X) (hx : x ∉ S) :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ Disjoint V S ∧ ∃ k : Fin A.n, V ⊆ (A.chart k).source ∧
      ∃ W : Fin d → Set Y, (∀ i, IsOpen (W i)) ∧ Pairwise (Function.onFun Disjoint W) ∧
        h ⁻¹' V = ⋃ i, W i ∧ ∀ i, Set.BijOn h (W i) V ∧
          ∃ j : Fin B.n, W i ⊆ (B.chart j).source := by
  classical
  have hSc : IsClosed S := isClosed_of_isAnalyticSubset' A hd.1
  have hloc : ∀ y : (h ⁻¹' {x} : Set Y), ∃ E : OpenPartialHomeomorph Y X, y.1 ∈ E.source ∧
      Set.EqOn h E E.source ∧ ∃ j : Fin B.n, E.source ⊆ (B.chart j).source := fun y =>
    exists_localHomeomorph_of_isDegreeOff hh hd y.1
      (by rw [show h y.1 = x from y.2]; exact hx)
  choose E hEy hEeq jE hjE using hloc
  have hFc : IsCompact (h ⁻¹' {x}) := (isClosed_singleton.preimage hh.1).isCompact
  have hFfin : (h ⁻¹' {x}).Finite := by
    obtain ⟨t, ht⟩ := hFc.elim_finite_subcover (fun y => (E y).source)
      (fun y => (E y).open_source) (fun y hy => Set.mem_iUnion.2 ⟨⟨y, hy⟩, hEy ⟨y, hy⟩⟩)
    refine (t.finite_toSet.image Subtype.val).subset ?_
    intro z hz
    obtain ⟨w, hwt, hzw⟩ := Set.mem_iUnion₂.1 (ht hz)
    have hzx : h z = x := hz
    have hwx : h w.1 = x := w.2
    have h1 : E w w.1 = E w z := by
      rw [← hEeq w hzw, ← hEeq w (hEy w), hzx, hwx]
    exact ⟨w, hwt, (E w).injOn (hEy w) hzw h1⟩
  have : Finite (h ⁻¹' {x}) := hFfin.to_subtype
  have hcard : Nat.card (h ⁻¹' {x}) = d := by
    rw [Nat.card_coe_set_eq]; exact hd.2.2.2.2.1 x hx
  let en : Fin d ≃ (h ⁻¹' {x} : Set Y) := ((Finite.equivFin _).trans (finCongr hcard)).symm
  obtain ⟨U0, hU0, hU0d⟩ := hFfin.t2_separation
  let U : Fin d → Set Y := fun i => U0 (en i).1 ∩ (E (en i)).source
  have hUo : ∀ i, IsOpen (U i) := fun i => (hU0 _).2.inter (E _).open_source
  have hyU : ∀ i, (en i).1 ∈ U i := fun i => ⟨(hU0 _).1, hEy _⟩
  have hUd : Pairwise (Function.onFun Disjoint U) := by
    intro i i' hii'
    have hne : (en i).1 ≠ (en i').1 := fun h' => hii' (en.injective (Subtype.ext h'))
    exact (hU0d (en i).2 (en i').2 hne).mono Set.inter_subset_left Set.inter_subset_left
  have hhU : ∀ i, h '' U i = E (en i) '' U i := fun i =>
    ((hEeq (en i)).mono Set.inter_subset_right).image_eq
  have hhUo : ∀ i, IsOpen (h '' U i) := fun i => by
    rw [hhU]; exact (E _).isOpen_image_of_subset_source (hUo i) Set.inter_subset_right
  have hKc : IsCompact (⋃ i, U i)ᶜ := (isOpen_iUnion hUo).isClosed_compl.isCompact
  have hK : IsClosed (h '' (⋃ i, U i)ᶜ) := (hKc.image hh.1).isClosed
  have hxK : x ∉ h '' (⋃ i, U i)ᶜ := by
    rintro ⟨z, hzK, hzx⟩
    apply hzK
    have hz : z ∈ h ⁻¹' {x} := hzx
    refine Set.mem_iUnion.2 ⟨en.symm ⟨z, hz⟩, ?_⟩
    have := hyU (en.symm ⟨z, hz⟩)
    simpa using this
  obtain ⟨k, hk⟩ := A.cover x
  let V : Set X := (⋂ i, h '' U i) ∩ (A.chart k).source ∩ (h '' (⋃ i, U i)ᶜ)ᶜ ∩ Sᶜ
  have hVo : IsOpen V :=
    (((isOpen_iInter_of_finite hhUo).inter (A.chart k).open_source).inter
      hK.isOpen_compl).inter hSc.isOpen_compl
  have hVU : ∀ i, V ⊆ h '' U i := fun i z hz => Set.mem_iInter.1 hz.1.1.1 i
  refine ⟨V, hVo, ⟨⟨⟨Set.mem_iInter.2 fun i => ⟨(en i).1, hyU i, (en i).2⟩, hk⟩, hxK⟩, hx⟩,
    Set.disjoint_left.2 fun z hz hzS => hz.2 hzS, k, fun z hz => hz.1.1.2, ?_⟩
  refine ⟨fun i => U i ∩ h ⁻¹' V, fun i => (hUo i).inter (hVo.preimage hh.1), ?_, ?_, ?_⟩
  · intro i i' hii'
    exact (hUd hii').mono Set.inter_subset_left Set.inter_subset_left
  · ext z
    constructor
    · intro hz
      have hzU : z ∈ ⋃ i, U i := by
        by_contra hc
        exact hz.1.2 ⟨z, hc, rfl⟩
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hzU
      exact Set.mem_iUnion.2 ⟨i, hi, hz⟩
    · intro hz
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hz
      exact hi.2
  · intro i
    refine ⟨⟨fun z hz => hz.2, ?_, ?_⟩, jE (en i), fun z hz => hjE _ hz.1.2⟩
    · intro a ha b hb hab
      apply (E (en i)).injOn ha.1.2 hb.1.2
      rw [← hEeq (en i) ha.1.2, ← hEeq (en i) hb.1.2]
      exact hab
    · intro v hv
      obtain ⟨u, hu, rfl⟩ := hVU i hv
      exact ⟨u, ⟨hu, hv⟩, rfl⟩

end

end ReciprocityTheory.AnForm.M
