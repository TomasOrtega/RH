import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Development.AutomorphicSpectrum.Statements.GeometryStatements.NineGeoU
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.BlockFrame

/- English proof (translation)
Introduce `X Ω _ ξ P Wv _ _ _ _ i A B Va Vb N j hj b s p hinj hrange hdisj hAV hBV hfr hhead hs`. Establish `hzero : ∀ {x : P}, x ∈ Va → x ∈ Vb → x = 0` using `fun h1 h2 => Submodule.disjoint_def.1 hdisj _ h1 h2`. Establish `hmemfr : ∀ k, i (b k) ∈ A p ⊔ B p` using `fun k => by`. Establish `h : b k ∈ (Lat.comap (fun q => A q ⊔ B q) i) p`. Rewrite using `[hfr.2]`.

Conclude with `Submodule.subset_span ⟨k, rfl⟩`. Conclude with `h`. Establish `hbhead : ∀ k, i (b (headIdx hj k)) ∈ Va` using `fun k => by`. Establish `h : b (headIdx hj k) ∈ Va.comap i`. Rewrite using `[← hhead]`.

Conclude with `Submodule.subset_span ⟨k, rfl⟩`. Conclude with `h`. Establish `hH : ∀ k, i (b (headIdx hj k)) ∈ A p` using `fun k => by`. Take `⟨a, ha, e, he, hae⟩` from `Submodule.mem_sup.1 (hmemfr (headIdx hj k))`. Establish `he0 : e = 0` using `hzero (by`.

Establish `h : e = i (b (headIdx hj k)) - a` using `by rw [← hae]; abel`. Rewrite using `[h]`. Conclude with `Va.sub_mem (hbhead k) (hAV a ha)) (hBV e he)`. Rewrite using `[← hae, he0, add_zero]`. Conclude with `ha`.

Establish `hT : ∀ k, i (b (tailIdx hj k)) - s k ∈ A p ∧ s k ∈ B p` using `fun k => by`. Take `⟨a, ha, e, he, hae⟩` from `Submodule.mem_sup.1 (hmemfr (tailIdx hj k))`. Establish `hes : e - s k = 0` using `hzero (by`. Establish `h : e - s k = (i (b (tailIdx hj k)) - s k) - a` using `by rw [← hae]; abel`. Rewrite using `[h]`.

Conclude with `Va.sub_mem (hs k).2 (hAV a ha)) (Vb.sub_mem (hBV e he) (hs k).1)`. Establish `hes' : e = s k` using `sub_eq_zero.1 hes`. Use `⟨?_, hes' ▸ he⟩` and prove the remaining obligations. Establish `h : i (b (tailIdx hj k)) - s k = a` using `by rw [← hae, hes']; abel`. Rewrite using `[h]`.

Conclude with `ha`. Establish `hcase : ∀ k : Fin N, (∃ a, k = headIdx hj a) ∨ ∃ a, k = tailIdx hj a` using `fun k => by`. Distinguish the cases in `h : (k : ℕ) < j`. Conclude with `Or.inl ⟨⟨k, h⟩, by ext; rfl⟩`. Conclude with `Or.inr ⟨⟨k - j, by have := k.2; omega⟩, by ext; simp [tailIdx]; omega⟩`.

Establish `hspan : ∀ x ∈ Submodule.span (regAt ξ p) (Set.range b), ∃ t ∈ Submodule.span (regAt ξ p) (Set.range s), i x - t ∈ Va`. Introduce `x hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨k, rfl⟩` from `hx`.

Break down `hcase k with ⟨a, rfl⟩ | ⟨a, rfl⟩` into its components or cases. Conclude with `⟨0, zero_mem _, by simpa using hbhead a⟩`. Conclude with `⟨s a, Submodule.subset_span ⟨a, rfl⟩, (hs a).2⟩`. Consider the case `zero => exact ⟨0, zero_mem _, by simp⟩`. Consider the case `add x y _ _ hx hy`.

Take `⟨t, ht, hxt⟩` from `hx`. Take `⟨t', ht', hyt⟩` from `hy`. Use `⟨t + t', add_mem ht ht', ?_⟩` and prove the remaining obligations. Establish `h : i (x + y) - (t + t') = (i x - t) + (i y - t')` using `by rw [map_add]; abel`. Rewrite using `[h]`.

Conclude with `Va.add_mem hxt hyt`. Consider the case `smul r x _ hx`. Take `⟨t, ht, hxt⟩` from `hx`. Use `⟨r • t, Submodule.smul_mem _ r ht, ?_⟩` and prove the remaining obligations. Establish `h : i (r • x) - r • t = (r : Ω) • (i x - t)`.

Rewrite using `[smul_sub]`. Use `show i ((r : Ω) • x) - (r : Ω) • t = _`. Rewrite using `[map_smul]`. Rewrite using `[h]`. Conclude with `Va.smul_mem _ hxt`.

Establish `hle : Submodule.span (regAt ξ p) (Set.range s) ≤ B p` using `Submodule.span_le.2 (by`. Introduce and unpack `_ ⟨k, rfl⟩`. Conclude with `(hT k).2)`. Establish `hgen : B p = Submodule.span (regAt ξ p) (Set.range s)`. Use `le_antisymm (fun e he => ?_) hle` and prove the remaining obligations.

Establish `hr : e ∈ LinearMap.range i`. Rewrite using `[hrange]`. Conclude with `Submodule.mem_sup_right (hBV e he)`. Take `⟨x, rfl⟩` from `hr`. Establish `hxc : x ∈ (Lat.comap (fun q => A q ⊔ B q) i) p` using `by show i x ∈ A p ⊔ B p`.

Conclude with `Submodule.mem_sup_right he`. Rewrite `hxc` using `[hfr.2]`. Take `⟨t, ht, hxt⟩` from `hspan x hxc`. Establish `h0 : i x - t = 0` using `hzero hxt (Vb.sub_mem (hBV _ he) (hBV _ (hle ht)))`. Rewrite using `[sub_eq_zero.1 h0]`.

Conclude with `ht`. Establish `htinj : Function.Injective (tailIdx hj)` using `fun a c h => by`. Establish `h'` using `congrArg Fin.val h`. Simplify using `only [tailIdx] at h'`. Use `ext`.

Use linear arithmetic over natural numbers and integers. Establish `hli : LinearIndependent Ω s`. Use `Fintype.linearIndependent_iff.2 fun g hg => ?_` and prove the remaining obligations. Establish `hx1 : (∑ k, g k • b (tailIdx hj k)) ∈ Va.comap i`. Establish `h : i (∑ k, g k • b (tailIdx hj k)) = ∑ k, g k • (i (b (tailIdx hj k)) - s k)`.

Simplify using `only [map_sum, map_smul, smul_sub, Finset.sum_sub_distrib, hg, sub_zero]`. Use `show i _ ∈ Va`. Rewrite using `[h]`. Conclude with `Va.sum_mem fun k _ => Va.smul_mem _ (hs k).2`. Establish `hdis : Disjoint (Set.range (headIdx hj)) (Set.range (tailIdx hj))`.

Use `Set.disjoint_left.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨a, rfl⟩ ⟨c, h⟩`. Establish `h'` using `congrArg Fin.val h`. Simplify using `only [headIdx, tailIdx, Fin.val_castLE] at h'`. Use `a.2` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Establish `hd` using `hfr.1.disjoint_span_image hdis`. Establish `hx2 : (∑ k, g k • b (tailIdx hj k)) ∈ Submodule.span Ω (b '' Set.range (tailIdx hj))` using `Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ⟨k, rfl⟩, rfl⟩)`. Establish `hx3 : (∑ k, g k • b (tailIdx hj k)) ∈ Submodule.span Ω (b '' Set.range (headIdx hj))`. Rewrite using `[← Set.range_comp, hhead]`.

Conclude with `hx1`. Establish `hx0` using `Submodule.disjoint_def.1 hd _ hx3 hx2`. Conclude with `Fintype.linearIndependent_iff.1 (hfr.1.comp _ htinj) g hx0`. Conclude with `⟨⟨hli, hgen⟩, fun k => (hT k).1, hH⟩`.
-/
theorem frame_of_sum_frame : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (P Wv : Type) [AddCommGroup P] [Module Ω P] [AddCommGroup Wv] [Module Ω Wv] (i : Wv →ₗ[Ω] P) (A B : Lat ξ P) (Va Vb : Submodule Ω P) (N j : ℕ) (hj : j ≤ N) (b : Fin N → Wv) (s : Fin (N - j) → P) (p : Cpt ξ), Function.Injective i → LinearMap.range i = Va ⊔ Vb → Disjoint Va Vb → (∀ x ∈ A p, x ∈ Va) → (∀ x ∈ B p, x ∈ Vb) → (Lat.comap (fun q => A q ⊔ B q) i).IsFrameAt b p → Submodule.span Ω (Set.range (b ∘ headIdx hj)) = Va.comap i → (∀ k, s k ∈ Vb ∧ i (b (tailIdx hj k)) - s k ∈ Va) → B.IsFrameAt s p ∧ (∀ k, i (b (tailIdx hj k)) - s k ∈ A p) ∧ ∀ k, i (b (headIdx hj k)) ∈ A p := by
  intro X Ω _ ξ P Wv _ _ _ _ i A B Va Vb N j hj b s p hinj hrange hdisj hAV hBV hfr hhead hs
  have hzero : ∀ {x : P}, x ∈ Va → x ∈ Vb → x = 0 := fun h1 h2 => Submodule.disjoint_def.1 hdisj _ h1 h2
  have hmemfr : ∀ k, i (b k) ∈ A p ⊔ B p := fun k => by
    have h : b k ∈ (Lat.comap (fun q => A q ⊔ B q) i) p := by
      rw [hfr.2]
      exact Submodule.subset_span ⟨k, rfl⟩
    exact h
  have hbhead : ∀ k, i (b (headIdx hj k)) ∈ Va := fun k => by
    have h : b (headIdx hj k) ∈ Va.comap i := by
      rw [← hhead]
      exact Submodule.subset_span ⟨k, rfl⟩
    exact h
  have hH : ∀ k, i (b (headIdx hj k)) ∈ A p := fun k => by
    obtain ⟨a, ha, e, he, hae⟩ := Submodule.mem_sup.1 (hmemfr (headIdx hj k))
    have he0 : e = 0 := hzero (by
      have h : e = i (b (headIdx hj k)) - a := by rw [← hae]; abel
      rw [h]
      exact Va.sub_mem (hbhead k) (hAV a ha)) (hBV e he)
    rw [← hae, he0, add_zero]
    exact ha
  have hT : ∀ k, i (b (tailIdx hj k)) - s k ∈ A p ∧ s k ∈ B p := fun k => by
    obtain ⟨a, ha, e, he, hae⟩ := Submodule.mem_sup.1 (hmemfr (tailIdx hj k))
    have hes : e - s k = 0 := hzero (by
      have h : e - s k = (i (b (tailIdx hj k)) - s k) - a := by rw [← hae]; abel
      rw [h]
      exact Va.sub_mem (hs k).2 (hAV a ha)) (Vb.sub_mem (hBV e he) (hs k).1)
    have hes' : e = s k := sub_eq_zero.1 hes
    refine ⟨?_, hes' ▸ he⟩
    have h : i (b (tailIdx hj k)) - s k = a := by rw [← hae, hes']; abel
    rw [h]
    exact ha
  have hcase : ∀ k : Fin N, (∃ a, k = headIdx hj a) ∨ ∃ a, k = tailIdx hj a := fun k => by
    by_cases h : (k : ℕ) < j
    · exact Or.inl ⟨⟨k, h⟩, by ext; rfl⟩
    · exact Or.inr ⟨⟨k - j, by have := k.2; omega⟩, by ext; simp [tailIdx]; omega⟩
  have hspan : ∀ x ∈ Submodule.span (regAt ξ p) (Set.range b),
      ∃ t ∈ Submodule.span (regAt ξ p) (Set.range s), i x - t ∈ Va := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      rcases hcase k with ⟨a, rfl⟩ | ⟨a, rfl⟩
      · exact ⟨0, zero_mem _, by simpa using hbhead a⟩
      · exact ⟨s a, Submodule.subset_span ⟨a, rfl⟩, (hs a).2⟩
    | zero => exact ⟨0, zero_mem _, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨t, ht, hxt⟩ := hx
      obtain ⟨t', ht', hyt⟩ := hy
      refine ⟨t + t', add_mem ht ht', ?_⟩
      have h : i (x + y) - (t + t') = (i x - t) + (i y - t') := by rw [map_add]; abel
      rw [h]
      exact Va.add_mem hxt hyt
    | smul r x _ hx =>
      obtain ⟨t, ht, hxt⟩ := hx
      refine ⟨r • t, Submodule.smul_mem _ r ht, ?_⟩
      have h : i (r • x) - r • t = (r : Ω) • (i x - t) := by
        rw [smul_sub]
        show i ((r : Ω) • x) - (r : Ω) • t = _
        rw [map_smul]
      rw [h]
      exact Va.smul_mem _ hxt
  have hle : Submodule.span (regAt ξ p) (Set.range s) ≤ B p := Submodule.span_le.2 (by
    rintro _ ⟨k, rfl⟩
    exact (hT k).2)
  have hgen : B p = Submodule.span (regAt ξ p) (Set.range s) := by
    refine le_antisymm (fun e he => ?_) hle
    have hr : e ∈ LinearMap.range i := by
      rw [hrange]
      exact Submodule.mem_sup_right (hBV e he)
    obtain ⟨x, rfl⟩ := hr
    have hxc : x ∈ (Lat.comap (fun q => A q ⊔ B q) i) p := by
      show i x ∈ A p ⊔ B p
      exact Submodule.mem_sup_right he
    rw [hfr.2] at hxc
    obtain ⟨t, ht, hxt⟩ := hspan x hxc
    have h0 : i x - t = 0 := hzero hxt (Vb.sub_mem (hBV _ he) (hBV _ (hle ht)))
    rw [sub_eq_zero.1 h0]
    exact ht
  have htinj : Function.Injective (tailIdx hj) := fun a c h => by
    have h' := congrArg Fin.val h
    simp only [tailIdx] at h'
    ext
    omega
  have hli : LinearIndependent Ω s := by
    refine Fintype.linearIndependent_iff.2 fun g hg => ?_
    have hx1 : (∑ k, g k • b (tailIdx hj k)) ∈ Va.comap i := by
      have h : i (∑ k, g k • b (tailIdx hj k)) = ∑ k, g k • (i (b (tailIdx hj k)) - s k) := by
        simp only [map_sum, map_smul, smul_sub, Finset.sum_sub_distrib, hg, sub_zero]
      show i _ ∈ Va
      rw [h]
      exact Va.sum_mem fun k _ => Va.smul_mem _ (hs k).2
    have hdis : Disjoint (Set.range (headIdx hj)) (Set.range (tailIdx hj)) := by
      refine Set.disjoint_left.2 ?_
      rintro _ ⟨a, rfl⟩ ⟨c, h⟩
      have h' := congrArg Fin.val h
      simp only [headIdx, tailIdx, Fin.val_castLE] at h'
      have := a.2
      omega
    have hd := hfr.1.disjoint_span_image hdis
    have hx2 : (∑ k, g k • b (tailIdx hj k)) ∈ Submodule.span Ω (b '' Set.range (tailIdx hj)) :=
      Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _
        (Submodule.subset_span ⟨_, ⟨k, rfl⟩, rfl⟩)
    have hx3 : (∑ k, g k • b (tailIdx hj k)) ∈ Submodule.span Ω (b '' Set.range (headIdx hj)) := by
      rw [← Set.range_comp, hhead]
      exact hx1
    have hx0 := Submodule.disjoint_def.1 hd _ hx3 hx2
    exact Fintype.linearIndependent_iff.1 (hfr.1.comp _ htinj) g hx0
  exact ⟨⟨hli, hgen⟩, fun k => (hT k).1, hH⟩

end GlobalTheory.CompanionTheory.Ar.BlockFrame
