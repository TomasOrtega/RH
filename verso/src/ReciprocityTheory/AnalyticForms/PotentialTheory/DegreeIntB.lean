import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeIntA

namespace ReciprocityTheory.AnForm.M

open MeasureTheory FinHolAtlas Filter Topology

noncomputable section

variable {e : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/- English proof (translation)
Establish `hU : ∀ k, SecondCountableTopology ((A.chart k).source)` using `fun k => (A.chart k).toHomeomorphSourceTarget.secondCountableTopology`. Establish `hcov : ⋃ k, (A.chart k).source = Set.univ` using `Set.eq_univ_of_forall fun x => Set.mem_iUnion.mpr (A.cover x)`. Conclude with `TopologicalSpace.secondCountableTopology_of_countable_cover (fun k => (A.chart k).open_source) hcov`.
-/
theorem dI_secondCountable (A : FinHolAtlas e X) : SecondCountableTopology X := by
  have hU : ∀ k, SecondCountableTopology ((A.chart k).source) := fun k =>
    (A.chart k).toHomeomorphSourceTarget.secondCountableTopology
  have hcov : ⋃ k, (A.chart k).source = Set.univ :=
    Set.eq_univ_of_forall fun x => Set.mem_iUnion.mpr (A.cover x)
  exact TopologicalSpace.secondCountableTopology_of_countable_cover
    (fun k => (A.chart k).open_source) hcov

/- English proof (translation)
Establish `hO : ∃ O : Set X, IsOpen O ∧ x ∈ O ∧ Disjoint O S`. Take `⟨W, hWo, hxW, r, f, hf, hSW⟩` from `hd.1 x`. Establish `hex : ∃ i, f i x ≠ 0`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`.

Establish `hm : x ∈ {y ∈ W | ∀ i, f i y = 0}` using `⟨hxW, hc⟩`. Rewrite `hm` using `[← hSW]`. Conclude with `hx hm.1`. Take `⟨i, hi⟩` from `hex`. Take `⟨j, hj⟩` from `A.cover x`.

Establish `hcont : ContinuousAt (f i) x`. Establish `h1 : AnalyticAt ℂ (f i ∘ (A.chart j).symm) (A.chart j x)` using `hf i j (A.chart j x) ⟨(A.chart j).map_source hj, by`. Simplify using `only [Set.mem_preimage, (A.chart j).left_inv hj]`. Conclude with `hxW⟩`. Establish `h2 : ContinuousAt ((f i ∘ (A.chart j).symm) ∘ A.chart j) x` using `h1.continuousAt.comp ((A.chart j).continuousAt hj)`.

Use `h2.congr ?_` and prove the remaining obligations. Use `filter_upwards [(A.chart j).eventually_left_inverse hj] with w hw`. Simplify using `only [Function.comp_apply, hw]`. Establish `hne : f i ⁻¹' {0}ᶜ ∈ 𝓝 x` using `hcont.preimage_mem_nhds (isClosed_singleton.isOpen_compl.mem_nhds hi)`. Take `⟨t, ht, hto, hxt⟩` from `mem_nhds_iff.mp hne`.

Use `⟨t ∩ W, hto.inter hWo, ⟨hxt, hxW⟩, Set.disjoint_left.mpr ?_⟩` and prove the remaining obligations. Introduce and unpack `w ⟨hwt, hwW⟩ hwS`. Establish `hw2 : w ∈ S ∩ W` using `⟨hwS, hwW⟩`. Rewrite `hw2` using `[hSW]`. Conclude with `ht hwt (hw2.2 i)`.

Establish `loc : ∀ y : Y, ∃ U : Set Y, IsOpen U ∧ y ∈ U ∧ (h y ∉ S → ∃ j, U ⊆ (B.chart j).source ∧ Set.InjOn h U ∧ ∀ U' ⊆ U, IsOpen U' → IsOpen (h '' U'))`. Introduce `y`. Distinguish the cases in `hyS : h y ∈ S`. Conclude with `⟨Set.univ, isOpen_univ, Set.mem_univ _, fun h' => absurd hyS h'⟩`. Take `⟨j, hj⟩` from `B.cover y`.

Take `⟨k, hk⟩` from `A.cover (h y)`. Establish `hzt : B.chart j y ∈ (B.chart j).target` using `(B.chart j).map_source hj`. Establish `hzy : (B.chart j).symm (B.chart j y) = y` using `(B.chart j).left_inv hj`. Use `set φ : (Fin e → ℂ) → (Fin e → ℂ) := A.chart k ∘ h ∘ (B.chart j).symm with hφ`. Establish `han : AnalyticAt ℂ φ (B.chart j y)` using `hh.2 j k (B.chart j y) ⟨hzt, by simp only [Set.mem_preimage, hzy]; exact hk⟩`.

Establish `hdet` using `hd.2.2.2.2.2 j k (B.chart j y) hzt (by rw [hzy]; exact hyS) (by rw [hzy]; exact hk)`. Set `L` to `(LinearMap.equivOfDetNeZero (fderiv ℂ φ (B.chart j y) : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) hdet).toContinuousLinearEquiv`. Establish `hL : HasStrictFDerivAt φ (L : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) (B.chart j y)`. Establish `hLe : (L : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) = fderiv ℂ φ (B.chart j y)` using `ContinuousLinearMap.ext fun v => rfl`. Rewrite using `[hLe]`.

Conclude with `han.hasStrictFDerivAt`. Set `P` to `hL.toOpenPartialHomeomorph φ`. Establish `hPc : (P : (Fin e → ℂ) → (Fin e → ℂ)) = φ` using `hL.toOpenPartialHomeomorph_coe`. Establish `hPs : B.chart j y ∈ P.source` using `hL.mem_toOpenPartialHomeomorph_source`. Set `U` to `(B.chart j).source ∩ (B.chart j) ⁻¹' P.source ∩ h ⁻¹' (A.chart k).source`.

Establish `hUo : IsOpen U` using `((B.chart j).isOpen_inter_preimage P.open_source).inter (hh.1.isOpen_preimage _ (A.chart k).open_source)`. Establish `key : ∀ y' ∈ U, (A.chart k).symm (P (B.chart j y')) = h y'`. Introduce `y' hy'`. Establish `e1` using `(B.chart j).left_inv hy'.1.1`. Establish `e2` using `(A.chart k).left_inv (show h y' ∈ (A.chart k).source from hy'.2)`.

Rewrite using `[hPc, hφ]`. Simplify using `only [Function.comp_apply, e1, e2]`. Establish `hinj : Set.InjOn h U`. Introduce `y1 h1 y2 h2 he`. Establish `hP : P (B.chart j y1) = P (B.chart j y2)`.

Rewrite using `[hPc, hφ]`. Simplify using `only [Function.comp_apply, (B.chart j).left_inv h1.1.1, (B.chart j).left_inv h2.1.1, he]`. Conclude with `(B.chart j).injOn h1.1.1 h2.1.1 (P.injOn h1.1.2 h2.1.2 hP)`. Establish `hopen : ∀ U' ⊆ U, IsOpen U' → IsOpen (h '' U')`. Introduce `U' hU' hU'o`.

Establish `e : h '' U' = (A.chart k).symm '' (P '' ((B.chart j) '' U'))`. Rewrite using `[Set.image_image, Set.image_image]`. Conclude with `Set.image_congr fun y' hy' => (key y' (hU' hy')).symm`. Rewrite using `[e]`. Establish `o1 : IsOpen ((B.chart j) '' U')` using `(B.chart j).isOpen_image_of_subset_source hU'o (fun y' hy' => (hU' hy').1.1)`.

Establish `s1 : (B.chart j) '' U' ⊆ P.source`. Introduce and unpack `_ ⟨y', hy', rfl⟩`. Conclude with `(hU' hy').1.2`. Establish `o2 : IsOpen (P '' ((B.chart j) '' U'))` using `P.isOpen_image_of_subset_source o1 s1`. Establish `s2 : P '' ((B.chart j) '' U') ⊆ (A.chart k).symm.source`.

Introduce and unpack `_ ⟨_, ⟨y', hy', rfl⟩, rfl⟩`. Rewrite using `[OpenPartialHomeomorph.symm_source, hPc, hφ]`. Simplify using `only [Function.comp_apply, (B.chart j).left_inv (hU' hy').1.1]`. Conclude with `(A.chart k).map_source (hU' hy').2`. Conclude with `(A.chart k).symm.isOpen_image_of_subset_source o2 s2`.

Conclude with `⟨U, hUo, ⟨⟨hj, hPs⟩, hk⟩, fun _ => ⟨j, fun y' hy' => hy'.1.1, hinj, hopen⟩⟩`. Use `choose U hUo hyU hUp using loc`. Use `set F := h ⁻¹' {x} with hFdef`. Establish `hFS : ∀ y ∈ F, h y ∉ S` using `fun y hy => by rw [show h y = x from hy]; exact hx`. Establish `hFc : IsCompact F` using `(isClosed_singleton.preimage hh.1).isCompact`.

Take `⟨t, htF, hFt⟩` from `hFc.elim_nhds_subcover U (fun y _ => (hUo y).mem_nhds (hyU y))`. Establish `hFfin : F.Finite`. Use `t.finite_toSet.subset ?_` and prove the remaining obligations. Introduce `z hz`. Take `⟨y, hy, hzy⟩` from `Set.mem_iUnion₂.mp (hFt hz)`.

Take `⟨_, _, hinj, _⟩` from `hUp y (hFS y (htF y hy))`. Establish `hzy' : z = y` using `hinj hzy (hyU y) (by rw [show h z = x from hz, show h y = x from htF y hy])`. Rewrite using `[hzy']`. Conclude with `hy`. Establish `hcard : hFfin.toFinset.card = d`.

Rewrite using `[← Set.ncard_eq_toFinset_card F hFfin]`. Conclude with `hd.2.2.2.2.1 x hx`. Substitute `hcard` using the available equality. Set `σ : Fin hFfin.toFinset.card → Y` to `fun i => (hFfin.toFinset.equivFin.symm i : Y)`. Establish `hσF : ∀ i, σ i ∈ F` using `fun i => hFfin.mem_toFinset.mp (hFfin.toFinset.equivFin.symm i).2`.

Establish `hσinj : Function.Injective σ` using `fun a b hab => hFfin.toFinset.equivFin.symm.injective (Subtype.ext hab)`. Establish `hσsurj : ∀ y ∈ F, ∃ i, σ i = y` using `fun y hy => ⟨hFfin.toFinset.equivFin ⟨y, hFfin.mem_toFinset.mpr hy⟩, by simp [σ]⟩`. Take `⟨Sep, hSep, hSepD⟩` from `hFfin.t2_separation`. Set `G : Fin hFfin.toFinset.card → Set Y` to `fun i => U (σ i) ∩ Sep (σ i)`. Establish `hGo : ∀ i, IsOpen (G i)` using `fun i => (hUo _).inter (hSep _).2`.

Establish `hGm : ∀ i, σ i ∈ G i` using `fun i => ⟨hyU _, (hSep _).1⟩`. Establish `hGd : ∀ a b, a ≠ b → Disjoint (G a) (G b)`. Introduce `a b hab`. Establish `hab'` using `hSepD (hσF a) (hσF b) (hσinj.ne hab)`. Conclude with `Disjoint.mono Set.inter_subset_right Set.inter_subset_right hab'`.

Establish `hGp : ∀ i, ∃ j, G i ⊆ (B.chart j).source ∧ Set.InjOn h (G i) ∧ IsOpen (h '' G i)`. Introduce `i`. Take `⟨j, hj, hinj, hop⟩` from `hUp (σ i) (hFS _ (hσF i))`. Conclude with `⟨j, Set.inter_subset_left.trans hj, hinj.mono Set.inter_subset_left, hop _ Set.inter_subset_left (hGo i)⟩`. Use `choose jj hjj hGinj hGop using hGp`.

Take `⟨k, hk⟩` from `A.cover x`. Take `⟨O, hOo, hxO, hOS⟩` from `hO`. Set `K` to `(⋃ i, G i)ᶜ`. Establish `hKc : IsCompact K` using `(isOpen_iUnion hGo).isClosed_compl.isCompact`. Establish `hhK : IsClosed (h '' K)` using `(hKc.image hh.1).isClosed`.

Establish `hxK : x ∉ h '' K`. Introduce and unpack `⟨y, hyK, hyx⟩`. Take `⟨i, rfl⟩` from `hσsurj y hyx`. Conclude with `hyK (Set.mem_iUnion.mpr ⟨i, hGm i⟩)`. Set `V` to `(A.chart k).source ∩ O ∩ (h '' K)ᶜ ∩ ⋂ i, h '' G i`.

Establish `hVo : IsOpen V` using `(((A.chart k).open_source.inter hOo).inter hhK.isOpen_compl).inter (isOpen_iInter_of_finite hGop)`. Establish `hxV : x ∈ V` using `⟨⟨⟨hk, hxO⟩, hxK⟩, Set.mem_iInter.mpr fun i => ⟨σ i, hGm i, hσF i⟩⟩`. Use `⟨V, hVo, hxV, Set.disjoint_left.mpr fun v hv hvS => Set.disjoint_left.mp hOS hv.1.1.2 hvS, k, fun v hv => hv.1.1.1, fun i => G i ∩ h ⁻¹' V, jj, fun i => (hGo i).inter (hh.1.isOpen_preimage _ hVo), fun a b hab => Disjoint.mono Set.inter_subset_left Set.inter_subset_left (hGd a b h …` and prove the remaining obligations. Use extensionality with `y`. Simplify using `only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff]`.

Prove the components needed by the constructor for the conclusion. Introduce `hy`. Establish `hyG : y ∈ ⋃ i, G i`. Assume the negation of the conclusion as `hc`. Conclude with `hy.1.2 ⟨y, hc, rfl⟩`.

Take `⟨i, hi⟩` from `Set.mem_iUnion.mp hyG`. Conclude with `⟨i, hi, hy⟩`. Introduce and unpack `⟨i, _, hy⟩`. Conclude with `hy`. Take `⟨y, hyG, rfl⟩` from `Set.mem_iInter.mp hv.2 i`.

Conclude with `⟨y, ⟨hyG, hv⟩, rfl⟩`.
-/
theorem dI_sheets [CompactSpace Y] [T2Space Y] [T2Space X]
    {A : FinHolAtlas e X} {B : FinHolAtlas e Y} {h : Y → X} (hh : HoloMap B A h) {d : ℕ}
    {S : Set X} (hd : IsDegreeOff A B h d S) (x : X) (hx : x ∉ S) :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ Disjoint V S ∧ ∃ k : Fin A.n, V ⊆ (A.chart k).source ∧
      ∃ W : Fin d → Set Y, ∃ j : Fin d → Fin B.n, (∀ i, IsOpen (W i)) ∧
        Pairwise (Function.onFun Disjoint W) ∧ h ⁻¹' V = ⋃ i, W i ∧
        ∀ i, Set.BijOn h (W i) V ∧ W i ⊆ (B.chart (j i)).source := by
  have hO : ∃ O : Set X, IsOpen O ∧ x ∈ O ∧ Disjoint O S := by
    obtain ⟨W, hWo, hxW, r, f, hf, hSW⟩ := hd.1 x
    have hex : ∃ i, f i x ≠ 0 := by
      by_contra hc
      push_neg at hc
      have hm : x ∈ {y ∈ W | ∀ i, f i y = 0} := ⟨hxW, hc⟩
      rw [← hSW] at hm
      exact hx hm.1
    obtain ⟨i, hi⟩ := hex
    obtain ⟨j, hj⟩ := A.cover x
    have hcont : ContinuousAt (f i) x := by
      have h1 : AnalyticAt ℂ (f i ∘ (A.chart j).symm) (A.chart j x) :=
        hf i j (A.chart j x) ⟨(A.chart j).map_source hj, by
          simp only [Set.mem_preimage, (A.chart j).left_inv hj]; exact hxW⟩
      have h2 : ContinuousAt ((f i ∘ (A.chart j).symm) ∘ A.chart j) x :=
        h1.continuousAt.comp ((A.chart j).continuousAt hj)
      refine h2.congr ?_
      filter_upwards [(A.chart j).eventually_left_inverse hj] with w hw
      simp only [Function.comp_apply, hw]
    have hne : f i ⁻¹' {0}ᶜ ∈ 𝓝 x :=
      hcont.preimage_mem_nhds (isClosed_singleton.isOpen_compl.mem_nhds hi)
    obtain ⟨t, ht, hto, hxt⟩ := mem_nhds_iff.mp hne
    refine ⟨t ∩ W, hto.inter hWo, ⟨hxt, hxW⟩, Set.disjoint_left.mpr ?_⟩
    rintro w ⟨hwt, hwW⟩ hwS
    have hw2 : w ∈ S ∩ W := ⟨hwS, hwW⟩
    rw [hSW] at hw2
    exact ht hwt (hw2.2 i)
  have loc : ∀ y : Y, ∃ U : Set Y, IsOpen U ∧ y ∈ U ∧ (h y ∉ S →
      ∃ j, U ⊆ (B.chart j).source ∧ Set.InjOn h U ∧
        ∀ U' ⊆ U, IsOpen U' → IsOpen (h '' U')) := by
    intro y
    by_cases hyS : h y ∈ S
    · exact ⟨Set.univ, isOpen_univ, Set.mem_univ _, fun h' => absurd hyS h'⟩
    obtain ⟨j, hj⟩ := B.cover y
    obtain ⟨k, hk⟩ := A.cover (h y)
    have hzt : B.chart j y ∈ (B.chart j).target := (B.chart j).map_source hj
    have hzy : (B.chart j).symm (B.chart j y) = y := (B.chart j).left_inv hj
    set φ : (Fin e → ℂ) → (Fin e → ℂ) := A.chart k ∘ h ∘ (B.chart j).symm with hφ
    have han : AnalyticAt ℂ φ (B.chart j y) :=
      hh.2 j k (B.chart j y) ⟨hzt, by simp only [Set.mem_preimage, hzy]; exact hk⟩
    have hdet := hd.2.2.2.2.2 j k (B.chart j y) hzt (by rw [hzy]; exact hyS) (by rw [hzy]; exact hk)
    let L := (LinearMap.equivOfDetNeZero
      (fderiv ℂ φ (B.chart j y) : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) hdet).toContinuousLinearEquiv
    have hL : HasStrictFDerivAt φ (L : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) (B.chart j y) := by
      have hLe : (L : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) = fderiv ℂ φ (B.chart j y) :=
        ContinuousLinearMap.ext fun v => rfl
      rw [hLe]
      exact han.hasStrictFDerivAt
    let P := hL.toOpenPartialHomeomorph φ
    have hPc : (P : (Fin e → ℂ) → (Fin e → ℂ)) = φ := hL.toOpenPartialHomeomorph_coe
    have hPs : B.chart j y ∈ P.source := hL.mem_toOpenPartialHomeomorph_source
    let U := (B.chart j).source ∩ (B.chart j) ⁻¹' P.source ∩ h ⁻¹' (A.chart k).source
    have hUo : IsOpen U := ((B.chart j).isOpen_inter_preimage P.open_source).inter
      (hh.1.isOpen_preimage _ (A.chart k).open_source)
    have key : ∀ y' ∈ U, (A.chart k).symm (P (B.chart j y')) = h y' := by
      intro y' hy'
      have e1 := (B.chart j).left_inv hy'.1.1
      have e2 := (A.chart k).left_inv (show h y' ∈ (A.chart k).source from hy'.2)
      rw [hPc, hφ]
      simp only [Function.comp_apply, e1, e2]
    have hinj : Set.InjOn h U := by
      intro y1 h1 y2 h2 he
      have hP : P (B.chart j y1) = P (B.chart j y2) := by
        rw [hPc, hφ]
        simp only [Function.comp_apply, (B.chart j).left_inv h1.1.1, (B.chart j).left_inv h2.1.1, he]
      exact (B.chart j).injOn h1.1.1 h2.1.1 (P.injOn h1.1.2 h2.1.2 hP)
    have hopen : ∀ U' ⊆ U, IsOpen U' → IsOpen (h '' U') := by
      intro U' hU' hU'o
      have e : h '' U' = (A.chart k).symm '' (P '' ((B.chart j) '' U')) := by
        rw [Set.image_image, Set.image_image]
        exact Set.image_congr fun y' hy' => (key y' (hU' hy')).symm
      rw [e]
      have o1 : IsOpen ((B.chart j) '' U') :=
        (B.chart j).isOpen_image_of_subset_source hU'o (fun y' hy' => (hU' hy').1.1)
      have s1 : (B.chart j) '' U' ⊆ P.source := by
        rintro _ ⟨y', hy', rfl⟩
        exact (hU' hy').1.2
      have o2 : IsOpen (P '' ((B.chart j) '' U')) := P.isOpen_image_of_subset_source o1 s1
      have s2 : P '' ((B.chart j) '' U') ⊆ (A.chart k).symm.source := by
        rintro _ ⟨_, ⟨y', hy', rfl⟩, rfl⟩
        rw [OpenPartialHomeomorph.symm_source, hPc, hφ]
        simp only [Function.comp_apply, (B.chart j).left_inv (hU' hy').1.1]
        exact (A.chart k).map_source (hU' hy').2
      exact (A.chart k).symm.isOpen_image_of_subset_source o2 s2
    exact ⟨U, hUo, ⟨⟨hj, hPs⟩, hk⟩, fun _ => ⟨j, fun y' hy' => hy'.1.1, hinj, hopen⟩⟩
  choose U hUo hyU hUp using loc
  set F := h ⁻¹' {x} with hFdef
  have hFS : ∀ y ∈ F, h y ∉ S := fun y hy => by rw [show h y = x from hy]; exact hx
  have hFc : IsCompact F := (isClosed_singleton.preimage hh.1).isCompact
  obtain ⟨t, htF, hFt⟩ := hFc.elim_nhds_subcover U (fun y _ => (hUo y).mem_nhds (hyU y))
  have hFfin : F.Finite := by
    refine t.finite_toSet.subset ?_
    intro z hz
    obtain ⟨y, hy, hzy⟩ := Set.mem_iUnion₂.mp (hFt hz)
    obtain ⟨_, _, hinj, _⟩ := hUp y (hFS y (htF y hy))
    have hzy' : z = y := hinj hzy (hyU y)
      (by rw [show h z = x from hz, show h y = x from htF y hy])
    rw [hzy']
    exact hy
  have hcard : hFfin.toFinset.card = d := by
    rw [← Set.ncard_eq_toFinset_card F hFfin]
    exact hd.2.2.2.2.1 x hx
  subst hcard
  classical
  let σ : Fin hFfin.toFinset.card → Y := fun i => (hFfin.toFinset.equivFin.symm i : Y)
  have hσF : ∀ i, σ i ∈ F := fun i => hFfin.mem_toFinset.mp (hFfin.toFinset.equivFin.symm i).2
  have hσinj : Function.Injective σ := fun a b hab =>
    hFfin.toFinset.equivFin.symm.injective (Subtype.ext hab)
  have hσsurj : ∀ y ∈ F, ∃ i, σ i = y := fun y hy =>
    ⟨hFfin.toFinset.equivFin ⟨y, hFfin.mem_toFinset.mpr hy⟩, by simp [σ]⟩
  obtain ⟨Sep, hSep, hSepD⟩ := hFfin.t2_separation
  let G : Fin hFfin.toFinset.card → Set Y := fun i => U (σ i) ∩ Sep (σ i)
  have hGo : ∀ i, IsOpen (G i) := fun i => (hUo _).inter (hSep _).2
  have hGm : ∀ i, σ i ∈ G i := fun i => ⟨hyU _, (hSep _).1⟩
  have hGd : ∀ a b, a ≠ b → Disjoint (G a) (G b) := by
    intro a b hab
    have hab' := hSepD (hσF a) (hσF b) (hσinj.ne hab)
    exact Disjoint.mono Set.inter_subset_right Set.inter_subset_right hab'
  have hGp : ∀ i, ∃ j, G i ⊆ (B.chart j).source ∧ Set.InjOn h (G i) ∧ IsOpen (h '' G i) := by
    intro i
    obtain ⟨j, hj, hinj, hop⟩ := hUp (σ i) (hFS _ (hσF i))
    exact ⟨j, Set.inter_subset_left.trans hj, hinj.mono Set.inter_subset_left,
      hop _ Set.inter_subset_left (hGo i)⟩
  choose jj hjj hGinj hGop using hGp
  obtain ⟨k, hk⟩ := A.cover x
  obtain ⟨O, hOo, hxO, hOS⟩ := hO
  let K := (⋃ i, G i)ᶜ
  have hKc : IsCompact K := (isOpen_iUnion hGo).isClosed_compl.isCompact
  have hhK : IsClosed (h '' K) := (hKc.image hh.1).isClosed
  have hxK : x ∉ h '' K := by
    rintro ⟨y, hyK, hyx⟩
    obtain ⟨i, rfl⟩ := hσsurj y hyx
    exact hyK (Set.mem_iUnion.mpr ⟨i, hGm i⟩)
  let V := (A.chart k).source ∩ O ∩ (h '' K)ᶜ ∩ ⋂ i, h '' G i
  have hVo : IsOpen V := (((A.chart k).open_source.inter hOo).inter hhK.isOpen_compl).inter
    (isOpen_iInter_of_finite hGop)
  have hxV : x ∈ V := ⟨⟨⟨hk, hxO⟩, hxK⟩, Set.mem_iInter.mpr fun i => ⟨σ i, hGm i, hσF i⟩⟩
  refine ⟨V, hVo, hxV, Set.disjoint_left.mpr fun v hv hvS => Set.disjoint_left.mp hOS hv.1.1.2 hvS,
    k, fun v hv => hv.1.1.1, fun i => G i ∩ h ⁻¹' V, jj,
    fun i => (hGo i).inter (hh.1.isOpen_preimage _ hVo),
    fun a b hab => Disjoint.mono Set.inter_subset_left Set.inter_subset_left (hGd a b hab), ?_,
    fun i => ⟨⟨fun y hy => hy.2, (hGinj i).mono Set.inter_subset_left, fun v hv => ?_⟩,
      Set.inter_subset_left.trans (hjj i)⟩⟩
  · ext y
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro hy
      have hyG : y ∈ ⋃ i, G i := by
        by_contra hc
        exact hy.1.2 ⟨y, hc, rfl⟩
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hyG
      exact ⟨i, hi, hy⟩
    · rintro ⟨i, _, hy⟩
      exact hy
  · obtain ⟨y, hyG, rfl⟩ := Set.mem_iInter.mp hv.2 i
    exact ⟨y, ⟨hyG, hv⟩, rfl⟩

/- English proof (translation)
Distinguish the cases in `hx : ∃ m ∈ Finset.range N, x ∈ E m`. Take `⟨m0, hm0, hxm0⟩` from `hx`. Rewrite using `[Finset.sum_eq_single m0]`. Simplify using `only [Set.indicator_of_mem hxm0, le_refl]`. Introduce `m _ hm`.

Establish `hxm : x ∉ E m` using `fun h' => Set.disjoint_left.mp (hd hm) h' hxm0`. Simplify using `[Set.indicator_apply, hxm]`. Introduce `h'`. Conclude with `absurd hm0 h'`. Use `push_neg at hx`.

Use `le_trans (le_of_eq (Finset.sum_eq_zero fun m hm => ?_)) (abs_nonneg _)` and prove the remaining obligations. Simplify using `[Set.indicator_apply, hx m hm]`.
-/
theorem dI_sum_ind_le (E : ℕ → Set X) (hd : Pairwise (Function.onFun Disjoint E)) (g : X → ℝ)
    (x : X) (N : ℕ) : ∑ m ∈ Finset.range N, |(E m).indicator g x| ≤ |g x| := by
  classical
  by_cases hx : ∃ m ∈ Finset.range N, x ∈ E m
  · obtain ⟨m0, hm0, hxm0⟩ := hx
    rw [Finset.sum_eq_single m0]
    · simp only [Set.indicator_of_mem hxm0, le_refl]
    · intro m _ hm
      have hxm : x ∉ E m := fun h' => Set.disjoint_left.mp (hd hm) h' hxm0
      simp [Set.indicator_apply, hxm]
    · intro h'
      exact absurd hm0 h'
  · push_neg at hx
    refine le_trans (le_of_eq (Finset.sum_eq_zero fun m hm => ?_)) (abs_nonneg _)
    simp [Set.indicator_apply, hx m hm]

end

end ReciprocityTheory.AnForm.M
