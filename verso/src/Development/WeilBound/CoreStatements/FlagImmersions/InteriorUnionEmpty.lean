import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogResolutionCompatiblePullback
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsMultiHomogIdealMap
import ReciprocityTheory.AnalyticForms.PotentialTheory.Degree

noncomputable section

namespace RootFieldNumerics.Ref.Comp

open ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.PB Topology Filter

/- English proof (translation)
Introduce `x`. Take `⟨W, hW, hx, r, f, hf, hSW⟩` from `hS x`. Take `⟨W', hW', hx', r', f', hf', hTW⟩` from `hT x`. Use `⟨W ∩ W', hW.inter hW', ⟨hx, hx'⟩, r * r', fun i y => f (finProdFinEquiv.symm i).1 y * f' (finProdFinEquiv.symm i).2 y, fun i j t ht => ?_, ?_⟩` and prove the remaining obligations. Conclude with `(hf _ j t ⟨ht.1, ht.2.1⟩).mul (hf' _ j t ⟨ht.1, ht.2.2⟩)`.

Use extensionality with `y`. Establish `h1` using `Set.ext_iff.1 hSW y`. Establish `h2` using `Set.ext_iff.1 hTW y`. Simplify using `only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_union] at h1 h2 ⊢`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨h | h, hy⟩`. Conclude with `⟨hy, fun i => by rw [(h1.1 ⟨h, hy.1⟩).2, zero_mul]⟩`. Conclude with `⟨hy, fun i => by rw [(h2.1 ⟨h, hy.2⟩).2, mul_zero]⟩`. Introduce and unpack `⟨hy, h⟩`. Use `⟨?_, hy⟩` and prove the remaining obligations.

Assume the negation of the conclusion as `hn`. Use `push Not at hn`. Establish `a1 : ∃ i, f i y ≠ 0`. Assume the negation of the conclusion as `h3`. Use `push Not at h3`.

Conclude with `hn.1 (h1.2 ⟨hy.1, h3⟩).1`. Establish `a2 : ∃ i, f' i y ≠ 0`. Assume the negation of the conclusion as `h3`. Use `push Not at h3`. Conclude with `hn.2 (h2.2 ⟨hy.2, h3⟩).1`.

Take `⟨i, hi⟩` from `a1`. Take `⟨i', hi'⟩` from `a2`. Use `h (finProdFinEquiv (i, i'))` as an intermediate fact. Simplify using `only [Equiv.symm_apply_apply] at this`. Conclude with `mul_ne_zero hi hi' this`.
-/
theorem analytic_union {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X} {S T : Set X}
    (hS : A.IsAnalyticSubset S) (hT : A.IsAnalyticSubset T) : A.IsAnalyticSubset (S ∪ T) := by
  intro x
  obtain ⟨W, hW, hx, r, f, hf, hSW⟩ := hS x
  obtain ⟨W', hW', hx', r', f', hf', hTW⟩ := hT x
  refine ⟨W ∩ W', hW.inter hW', ⟨hx, hx'⟩, r * r', fun i y => f (finProdFinEquiv.symm i).1 y *
    f' (finProdFinEquiv.symm i).2 y, fun i j t ht => ?_, ?_⟩
  · exact (hf _ j t ⟨ht.1, ht.2.1⟩).mul (hf' _ j t ⟨ht.1, ht.2.2⟩)
  · ext y
    have h1 := Set.ext_iff.1 hSW y
    have h2 := Set.ext_iff.1 hTW y
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_union] at h1 h2 ⊢
    constructor
    · rintro ⟨h | h, hy⟩
      · exact ⟨hy, fun i => by rw [(h1.1 ⟨h, hy.1⟩).2, zero_mul]⟩
      · exact ⟨hy, fun i => by rw [(h2.1 ⟨h, hy.2⟩).2, mul_zero]⟩
    · rintro ⟨hy, h⟩
      refine ⟨?_, hy⟩
      by_contra hn
      push Not at hn
      have a1 : ∃ i, f i y ≠ 0 := by
        by_contra h3
        push Not at h3
        exact hn.1 (h1.2 ⟨hy.1, h3⟩).1
      have a2 : ∃ i, f' i y ≠ 0 := by
        by_contra h3
        push Not at h3
        exact hn.2 (h2.2 ⟨hy.2, h3⟩).1
      obtain ⟨i, hi⟩ := a1
      obtain ⟨i', hi'⟩ := a2
      have := h (finProdFinEquiv (i, i'))
      simp only [Equiv.symm_apply_apply] at this
      exact mul_ne_zero hi hi' this

/- English proof (translation)
Rewrite using `[interior_union_isClosed_of_interior_empty hS h2, h1]`.
-/
theorem interior_union_empty {X : Type} [TopologicalSpace X] {S T : Set X} (hS : IsClosed S) (h1 : interior S = ∅)
    (h2 : interior T = ∅) : interior (S ∪ T) = ∅ := by
  rw [interior_union_isClosed_of_interior_empty hS h2, h1]

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Establish `hd : Dense (h ⁻¹' N)ᶜ` using `interior_eq_empty_iff_dense_compl.1 hNi`. Take `⟨z, hzN, hzO⟩` from `hd.exists_mem_open isOpen_interior (Set.nonempty_iff_ne_empty.2 hne)`. Establish `hC : IsClosed (h '' (interior (h ⁻¹' T))ᶜ)` using `(isOpen_interior.isClosed_compl.isCompact.image hh).isClosed`. Establish `hO : IsOpen ((h '' (interior (h ⁻¹' T))ᶜ)ᶜ ∩ Nᶜ)` using `hC.isOpen_compl.inter hN.isOpen_compl`.

Establish `hsub : (h '' (interior (h ⁻¹' T))ᶜ)ᶜ ∩ Nᶜ ⊆ T`. Introduce and unpack `x ⟨h1, h2⟩`. Take `⟨c, hc⟩` from `Set.ncard_eq_one.1 (hfib x h2)`. Establish `hcx : h c = x`. Establish `: c ∈ h ⁻¹' {x}` using `by rw [hc]; rfl`.

Conclude with `this`. Establish `: c ∈ interior (h ⁻¹' T)`. Assume the negation of the conclusion as `hn`. Conclude with `h1 ⟨c, hn, hcx⟩`. Establish `h3 : c ∈ h ⁻¹' T` using `interior_subset this`.

Rewrite using `[← hcx]`. Conclude with `h3`. Establish `hmem : h z ∈ (h '' (interior (h ⁻¹' T))ᶜ)ᶜ ∩ Nᶜ`. Use `⟨?_, hzN⟩` and prove the remaining obligations. Introduce and unpack `⟨w, hw, hwz⟩`.

Take `⟨c, hc⟩` from `Set.ncard_eq_one.1 (hfib (h z) hzN)`. Establish `e1 : w ∈ h ⁻¹' {h z}` using `hwz`. Establish `e2 : z ∈ h ⁻¹' {h z}` using `rfl`. Rewrite `e1`, `e2` using `[hc]`. Conclude with `hw ((e1.trans e2.symm) ▸ hzO)`.

Use `interior_maximal hsub hO hmem` as an intermediate fact. Rewrite `this` using `[hT]`. Conclude with `this`.
-/
theorem interior_preimage {Y Z : Type} [TopologicalSpace Y] [TopologicalSpace Z] [T2Space Y] [CompactSpace Z]
    {h : Z → Y} (hh : Continuous h) {N T : Set Y} (hN : IsClosed N) (hNi : interior (h ⁻¹' N) = ∅)
    (hfib : ∀ x ∉ N, (h ⁻¹' {x}).ncard = 1) (hT : interior T = ∅) : interior (h ⁻¹' T) = ∅ := by
  by_contra hne
  have hd : Dense (h ⁻¹' N)ᶜ := interior_eq_empty_iff_dense_compl.1 hNi
  obtain ⟨z, hzN, hzO⟩ := hd.exists_mem_open isOpen_interior (Set.nonempty_iff_ne_empty.2 hne)
  have hC : IsClosed (h '' (interior (h ⁻¹' T))ᶜ) :=
    (isOpen_interior.isClosed_compl.isCompact.image hh).isClosed
  have hO : IsOpen ((h '' (interior (h ⁻¹' T))ᶜ)ᶜ ∩ Nᶜ) := hC.isOpen_compl.inter hN.isOpen_compl
  have hsub : (h '' (interior (h ⁻¹' T))ᶜ)ᶜ ∩ Nᶜ ⊆ T := by
    rintro x ⟨h1, h2⟩
    obtain ⟨c, hc⟩ := Set.ncard_eq_one.1 (hfib x h2)
    have hcx : h c = x := by
      have : c ∈ h ⁻¹' {x} := by rw [hc]; rfl
      exact this
    have : c ∈ interior (h ⁻¹' T) := by
      by_contra hn
      exact h1 ⟨c, hn, hcx⟩
    have h3 : c ∈ h ⁻¹' T := interior_subset this
    rw [← hcx]
    exact h3
  have hmem : h z ∈ (h '' (interior (h ⁻¹' T))ᶜ)ᶜ ∩ Nᶜ := by
    refine ⟨?_, hzN⟩
    rintro ⟨w, hw, hwz⟩
    obtain ⟨c, hc⟩ := Set.ncard_eq_one.1 (hfib (h z) hzN)
    have e1 : w ∈ h ⁻¹' {h z} := hwz
    have e2 : z ∈ h ⁻¹' {h z} := rfl
    rw [hc] at e1 e2
    exact hw ((e1.trans e2.symm) ▸ hzO)
  have := interior_maximal hsub hO hmem
  rw [hT] at this
  exact this

/- English proof (translation)
Take `⟨a1, a2, a3, a4, a5, a6⟩` from `hdπ`. Take `⟨b1, b2, b3, b4, b5, b6⟩` from `hdh`. Establish `hcomp` using `CovMap.holoMap_comp hh hπ`. Establish `hbrc : IsClosed br` using `isClosed_of_isAnalyticSubset A a1`. Establish `hSi' : interior S = ∅`.

Assume the negation of the conclusion as `hne`. Establish `hdn : Dense brᶜ` using `interior_eq_empty_iff_dense_compl.1 a2`. Take `⟨x, hx, hxO⟩` from `hdn.exists_mem_open isOpen_interior (Set.nonempty_iff_ne_empty.2 hne)`. Establish `hpos : 0 < (π ⁻¹' {x}).ncard` using `by rw [a5 x hx]; exact hd`. Take `⟨y, hy⟩` from `Set.nonempty_of_ncard_ne_zero hpos.ne'`.

Establish `hy' : π y = x` using `hy`. Establish `: y ∈ interior (π ⁻¹' S)` using `preimage_interior_subset_interior_preimage hπ.1 (by show π y ∈ interior S`. Rewrite using `[hy']`. Conclude with `hxO)`. Rewrite `this` using `[hSi]`.

Conclude with `this`. Establish `hU` using `analytic_union a1 hS`. Use `⟨hU, interior_union_empty hbrc a2 hSi', CovMap.Deg.isAnalyticSubset_preimage hcomp hU, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Set.preimage_comp]`. Use `interior_preimage hh.1 (isClosed_of_isAnalyticSubset B b1) b4 b5 ?_` and prove the remaining obligations.

Rewrite using `[Set.preimage_union]`. Conclude with `interior_union_empty (hbrc.preimage hπ.1) a4 hSi`. Introduce `x hx`. Establish `hx1 : x ∉ br` using `fun h => hx (Or.inl h)`. Establish `hx2 : x ∉ S` using `fun h => hx (Or.inr h)`.

Establish `hN : ∀ y, π y = x → y ∉ N` using `fun y hy hn => hx2 (hy ▸ hNS hn)`. Rewrite using `[← a5 x hx1]`. Establish `himg : h '' ((π ∘ h) ⁻¹' {x}) = π ⁻¹' {x}`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨z, hz, rfl⟩`. Conclude with `hz`. Introduce `hy`. Take `⟨c, hc⟩` from `Set.ncard_eq_one.1 (b5 y (hN y hy))`. Establish `hcx : h c = y`.

Establish `: c ∈ h ⁻¹' {y}` using `by rw [hc]; rfl`. Conclude with `this`. Use `⟨c, ?_, hcx⟩` and prove the remaining obligations. Use `show π (h c) = x`. Rewrite using `[hcx]`.

Conclude with `hy`. Rewrite using `[← himg]`. Use `(Set.ncard_image_of_injOn ?_).symm` and prove the remaining obligations. Introduce `z hz w _ hzw`. Take `⟨c, hc⟩` from `Set.ncard_eq_one.1 (b5 (h z) (hN _ hz))`.

Establish `e1 : w ∈ h ⁻¹' {h z}` using `hzw.symm`. Establish `e2 : z ∈ h ⁻¹' {h z}` using `rfl`. Rewrite `e1`, `e2` using `[hc]`. Conclude with `e2.trans e1.symm`. Introduce `j k y hy hnot hk`.

Establish `hnot1 : (C.chart j).symm y ∉ h ⁻¹' N` using `fun hn => hnot (Or.inr (hNS hn))`. Establish `hnot2 : h ((C.chart j).symm y) ∉ π ⁻¹' br` using `fun hn => hnot (Or.inl hn)`. Take `⟨l, hl⟩` from `B.cover (h ((C.chart j).symm y))`. Take `⟨Q, hQdef⟩ : ∃ Q : (Fin e → ℂ) → Fin e → ℂ, Q = B.chart l ∘ h ∘ (C.chart j).symm` from `⟨_, rfl⟩`. Take `⟨P, hPdef⟩ : ∃ P : (Fin e → ℂ) → Fin e → ℂ, P = A.chart k ∘ π ∘ (B.chart l).symm` from `⟨_, rfl⟩`.

Establish `hQa : AnalyticAt ℂ Q y`. Rewrite using `[hQdef]`. Conclude with `hh.2 j l y ⟨hy, hl⟩`. Establish `hu : (B.chart l).symm (Q y) = h ((C.chart j).symm y)`. Rewrite using `[hQdef]`.

Conclude with `(B.chart l).left_inv hl`. Establish `hQt : Q y ∈ (B.chart l).target`. Rewrite using `[hQdef]`. Conclude with `(B.chart l).map_source hl`. Establish `hk' : π ((B.chart l).symm (Q y)) ∈ (A.chart k).source`.

Rewrite using `[hu]`. Conclude with `hk`. Establish `hPa : AnalyticAt ℂ P (Q y)`. Rewrite using `[hPdef]`. Conclude with `hπ.2 l k _ ⟨hQt, hk'⟩`.

Establish `hc : ContinuousAt (h ∘ (C.chart j).symm) y` using `hh.1.continuousAt.comp ((C.chart j).continuousAt_symm hy)`. Establish `heq : (A.chart k ∘ (π ∘ h) ∘ (C.chart j).symm) =ᶠ[nhds y] P ∘ Q` using `by filter_upwards [hc ((B.chart l).open_source.mem_nhds hl)] with t ht`. Establish `ht' : h ((C.chart j).symm t) ∈ (B.chart l).source` using `ht`. Rewrite using `[hPdef, hQdef]`. Simplify using `only [Function.comp, (B.chart l).left_inv ht']`.

Establish `hcomp' : fderiv ℂ (P ∘ Q) y = (fderiv ℂ P (Q y)).comp (fderiv ℂ Q y)` using `fderiv_comp y hPa.differentiableAt hQa.differentiableAt`. Rewrite using `[heq.fderiv_eq, hcomp']`. Express the relevant statement in the definitionally equal form `LinearMap.det ((fderiv ℂ P (Q y) : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ∘ₗ (fderiv ℂ Q y : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))) ≠ 0`. Rewrite using `[LinearMap.det_comp]`. Use `mul_ne_zero ?_ ?_` and prove the remaining obligations.

Rewrite using `[hPdef]`. Conclude with `a6 l k _ hQt (by rw [hu]; exact hnot2) hk'`. Rewrite using `[hQdef]`. Conclude with `b6 j l y hy hnot1 hl`.
-/
theorem degree_comp {e d : ℕ} {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    [TopologicalSpace Z] [CompactSpace Z] {A : FinHolAtlas e X} {B : FinHolAtlas e Y} {C : FinHolAtlas e Z}
    {π : Y → X} {h : Z → Y} {br S : Set X} {N : Set Y} (hπ : HoloMap B A π) (hh : HoloMap C B h) (hd : 0 < d)
    (hdπ : IsDegreeOff A B π d br) (hdh : IsDegreeOff B C h 1 N) (hS : A.IsAnalyticSubset S)
    (hSi : interior (π ⁻¹' S) = ∅) (hNS : N ⊆ π ⁻¹' S) : IsDegreeOff A C (π ∘ h) d (br ∪ S) := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hdπ
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := hdh
  have hcomp := CovMap.holoMap_comp hh hπ
  have hbrc : IsClosed br := isClosed_of_isAnalyticSubset A a1
  have hSi' : interior S = ∅ := by
    by_contra hne
    have hdn : Dense brᶜ := interior_eq_empty_iff_dense_compl.1 a2
    obtain ⟨x, hx, hxO⟩ := hdn.exists_mem_open isOpen_interior (Set.nonempty_iff_ne_empty.2 hne)
    have hpos : 0 < (π ⁻¹' {x}).ncard := by rw [a5 x hx]; exact hd
    obtain ⟨y, hy⟩ := Set.nonempty_of_ncard_ne_zero hpos.ne'
    have hy' : π y = x := hy
    have : y ∈ interior (π ⁻¹' S) := preimage_interior_subset_interior_preimage hπ.1 (by
      show π y ∈ interior S
      rw [hy']; exact hxO)
    rw [hSi] at this
    exact this
  have hU := analytic_union a1 hS
  refine ⟨hU, interior_union_empty hbrc a2 hSi', CovMap.Deg.isAnalyticSubset_preimage hcomp hU, ?_, ?_, ?_⟩
  · rw [Set.preimage_comp]
    refine interior_preimage hh.1 (isClosed_of_isAnalyticSubset B b1) b4 b5 ?_
    rw [Set.preimage_union]
    exact interior_union_empty (hbrc.preimage hπ.1) a4 hSi
  · intro x hx
    have hx1 : x ∉ br := fun h => hx (Or.inl h)
    have hx2 : x ∉ S := fun h => hx (Or.inr h)
    have hN : ∀ y, π y = x → y ∉ N := fun y hy hn => hx2 (hy ▸ hNS hn)
    rw [← a5 x hx1]
    have himg : h '' ((π ∘ h) ⁻¹' {x}) = π ⁻¹' {x} := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact hz
      · intro hy
        obtain ⟨c, hc⟩ := Set.ncard_eq_one.1 (b5 y (hN y hy))
        have hcx : h c = y := by
          have : c ∈ h ⁻¹' {y} := by rw [hc]; rfl
          exact this
        refine ⟨c, ?_, hcx⟩
        show π (h c) = x
        rw [hcx]; exact hy
    rw [← himg]
    refine (Set.ncard_image_of_injOn ?_).symm
    intro z hz w _ hzw
    obtain ⟨c, hc⟩ := Set.ncard_eq_one.1 (b5 (h z) (hN _ hz))
    have e1 : w ∈ h ⁻¹' {h z} := hzw.symm
    have e2 : z ∈ h ⁻¹' {h z} := rfl
    rw [hc] at e1 e2
    exact e2.trans e1.symm
  · intro j k y hy hnot hk
    have hnot1 : (C.chart j).symm y ∉ h ⁻¹' N := fun hn => hnot (Or.inr (hNS hn))
    have hnot2 : h ((C.chart j).symm y) ∉ π ⁻¹' br := fun hn => hnot (Or.inl hn)
    obtain ⟨l, hl⟩ := B.cover (h ((C.chart j).symm y))
    obtain ⟨Q, hQdef⟩ : ∃ Q : (Fin e → ℂ) → Fin e → ℂ, Q = B.chart l ∘ h ∘ (C.chart j).symm :=
      ⟨_, rfl⟩
    obtain ⟨P, hPdef⟩ : ∃ P : (Fin e → ℂ) → Fin e → ℂ, P = A.chart k ∘ π ∘ (B.chart l).symm :=
      ⟨_, rfl⟩
    have hQa : AnalyticAt ℂ Q y := by
      rw [hQdef]
      exact hh.2 j l y ⟨hy, hl⟩
    have hu : (B.chart l).symm (Q y) = h ((C.chart j).symm y) := by
      rw [hQdef]
      exact (B.chart l).left_inv hl
    have hQt : Q y ∈ (B.chart l).target := by
      rw [hQdef]
      exact (B.chart l).map_source hl
    have hk' : π ((B.chart l).symm (Q y)) ∈ (A.chart k).source := by
      rw [hu]
      exact hk
    have hPa : AnalyticAt ℂ P (Q y) := by
      rw [hPdef]
      exact hπ.2 l k _ ⟨hQt, hk'⟩
    have hc : ContinuousAt (h ∘ (C.chart j).symm) y :=
      hh.1.continuousAt.comp ((C.chart j).continuousAt_symm hy)
    have heq : (A.chart k ∘ (π ∘ h) ∘ (C.chart j).symm) =ᶠ[nhds y] P ∘ Q := by
      filter_upwards [hc ((B.chart l).open_source.mem_nhds hl)] with t ht
      have ht' : h ((C.chart j).symm t) ∈ (B.chart l).source := ht
      rw [hPdef, hQdef]
      simp only [Function.comp, (B.chart l).left_inv ht']
    have hcomp' : fderiv ℂ (P ∘ Q) y = (fderiv ℂ P (Q y)).comp (fderiv ℂ Q y) :=
      fderiv_comp y hPa.differentiableAt hQa.differentiableAt
    rw [heq.fderiv_eq, hcomp']
    change LinearMap.det ((fderiv ℂ P (Q y) : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ∘ₗ
      (fderiv ℂ Q y : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))) ≠ 0
    rw [LinearMap.det_comp]
    refine mul_ne_zero ?_ ?_
    · rw [hPdef]
      exact a6 l k _ hQt (by rw [hu]; exact hnot2) hk'
    · rw [hQdef]
      exact b6 j l y hy hnot1 hl

end RootFieldNumerics.Ref.Comp
