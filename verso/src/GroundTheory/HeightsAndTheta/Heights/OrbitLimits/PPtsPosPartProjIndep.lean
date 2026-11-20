import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterFib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StPtsSheetOnlyNull
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StPtsPosPartLocal
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StPtsPosDensMeasurable
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm IsArithVar IsGoodProj mcPts segre fibre IsSheet sheetDensity
  pot fibreFinite)

/- English proof (translation)
Unfold `ptsPosDens`. Simplify using `only [finsum_mem_eq_finite_toFinset_sum _ hfin]`. Establish `hT0 : ∀ (g' : ((Σ k, ι k) → ℂ) → ℝ) w, 0 ≤ max (sheetDensity P Ψ φ g' y w) 0` using `fun _ _ => le_max_right _ _`. Establish `hpt : ∀ w ∈ hfin.toFinset, ENNReal.ofReal (max (sheetDensity P Ψ φ g y w) 0) = ∑' k, ENNReal.ofReal (max (sheetDensity P Ψ φ ((E k).indicator g) y w) 0)`. Introduce `w hw`.

Establish `hw' : w ∈ fibre P Ψ y` using `hfin.mem_toFinset.mp hw`. Distinguish the cases in `hs : ∃ γ, IsSheet P Ψ y w γ`. Establish `hz : hs.choose y ∈ mcPts P` using `hs.choose_spec.2.self_of_nhds.2.1`. Take `⟨k₀, hk₀⟩` from `hcov w hw' hs _ hz hs.choose_spec.1`. Rewrite using `[tsum_eq_single k₀]`.

Simplify using `only [sheetDensity, dif_pos hs, Set.indicator_of_mem hk₀]`. Introduce `k hk`. Establish `hxk : hs.choose y ∉ E k` using `fun hxk => Set.disjoint_left.mp (hE hk) hxk hk₀`. Simplify using `[sheetDensity, dif_pos hs, Set.indicator_of_notMem hxk]`. Simplify using `[sheetDensity, dif_neg hs]`.

Rewrite using `[ENNReal.ofReal_sum_of_nonneg (fun w _ => hT0 g w), Finset.sum_congr rfl hpt, ← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]`. Conclude with `tsum_congr fun k => (ENNReal.ofReal_sum_of_nonneg (fun w _ => hT0 _ w)).symm`.
-/
theorem ptsPosDens_split {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {e : ℕ}
    {P : Ideal (MRing ι)} {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)}
    (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) (g : ((Σ k, ι k) → ℂ) → ℝ) (E : ℕ → Set ((Σ k, ι k) → ℂ))
    (y : Fin e → ℂ) (hfin : (fibre P Ψ y).Finite) (hE : Pairwise (Function.onFun Disjoint E))
    (hcov : ∀ w ∈ fibre P Ψ y, (∃ γ, IsSheet P Ψ y w γ) → ∀ z ∈ mcPts P, segre z = w → ∃ k, z ∈ E k) :
    ENNReal.ofReal (ptsPosDens P Ψ φ g y) =
      ∑' k, ENNReal.ofReal (ptsPosDens P Ψ φ ((E k).indicator g) y) := by
  classical
  unfold ptsPosDens
  simp only [finsum_mem_eq_finite_toFinset_sum _ hfin]
  have hT0 : ∀ (g' : ((Σ k, ι k) → ℂ) → ℝ) w, 0 ≤ max (sheetDensity P Ψ φ g' y w) 0 :=
    fun _ _ => le_max_right _ _
  have hpt : ∀ w ∈ hfin.toFinset, ENNReal.ofReal (max (sheetDensity P Ψ φ g y w) 0) =
      ∑' k, ENNReal.ofReal (max (sheetDensity P Ψ φ ((E k).indicator g) y w) 0) := by
    intro w hw
    have hw' : w ∈ fibre P Ψ y := hfin.mem_toFinset.mp hw
    by_cases hs : ∃ γ, IsSheet P Ψ y w γ
    · have hz : hs.choose y ∈ mcPts P := hs.choose_spec.2.self_of_nhds.2.1
      obtain ⟨k₀, hk₀⟩ := hcov w hw' hs _ hz hs.choose_spec.1
      rw [tsum_eq_single k₀]
      · simp only [sheetDensity, dif_pos hs, Set.indicator_of_mem hk₀]
      · intro k hk
        have hxk : hs.choose y ∉ E k := fun hxk => Set.disjoint_left.mp (hE hk) hxk hk₀
        simp [sheetDensity, dif_pos hs, Set.indicator_of_notMem hxk]
    · simp [sheetDensity, dif_neg hs]
  rw [ENNReal.ofReal_sum_of_nonneg (fun w _ => hT0 g w), Finset.sum_congr rfl hpt,
    ← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  exact tsum_congr fun k => (ENNReal.ofReal_sum_of_nonneg (fun w _ => hT0 _ w)).symm

/- English proof (translation)
Introduce `K _ ι _ P e Ψ Ψ' L g hP hΨ hΨ' hLs hg hg0`. Use `set Inv : Set ((Σ k, ι k) → ℂ) → Prop := fun S => ∀ (c : K → ℂ) (z' : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → ((fun p => c p.1 * z' p) ∈ S ↔ z' ∈ S) with hInv`. Use `set Q : ((Σ k, ι k) → ℂ) → Prop := fun z => z ∈ mcPts P ∧ IsSimpleSheetPt P Ψ ((Ψ (segre z) 0)⁻¹ • segre z) ∧ IsSimpleSheetPt P Ψ' ((Ψ' (segre z) 0)⁻¹ • segre z) with hQ`. Establish `key : ∀ z, ∃ W : Set ((Σ k, ι k) → ℂ), IsOpen W ∧ Inv W ∧ (Q z → z ∈ W) ∧ ∀ E, MeasurableSet E → Inv E → E ⊆ W → ∫⁻ y, ENNReal.ofReal (ptsPosDens P Ψ (pot L) (E.indicator g) y) = ∫⁻ y, ENNReal.ofReal (ptsPosDens P Ψ' (pot L) (E.indicator g) y)`. Introduce `z`.

Distinguish the cases in `hz : Q z`. Take `⟨W, hW, hzW, hWi, hWE⟩` from `hL K ι P e Ψ Ψ' L g z hP hΨ hΨ' hLs hg hg0 hz.1 hz.2.1 hz.2.2`. Conclude with `⟨W, hW, hWi, fun _ => hzW, hWE⟩`. Use `⟨∅, isOpen_empty, fun _ _ _ => Iff.rfl, fun h => absurd h hz, fun E _ _ hE => ?_⟩` and prove the remaining obligations. Rewrite using `[Set.subset_empty_iff.1 hE, Set.indicator_empty]`.

Simplify using `[ptsPosDens, sheetDensity]`. Use `choose W hWo hWi hzW hWE using key`. Take `⟨T, hTc, hTU⟩` from `TopologicalSpace.isOpen_iUnion_countable W hWo`. Take `⟨f, hf⟩` from `(hTc.insert 0).exists_eq_range (Set.insert_nonempty 0 T)`. Use `set E : ℕ → Set ((Σ k, ι k) → ℂ) := disjointed (fun k => W (f k)) with hE`.

Establish `hEm : ∀ k, MeasurableSet (E k)` using `MeasurableSet.disjointed fun k => (hWo (f k)).measurableSet`. Establish `hEW : ∀ k, E k ⊆ W (f k)` using `disjointed_subset _`. Establish `hEd : Pairwise (Function.onFun Disjoint E)` using `disjoint_disjointed _`. Establish `hEi : ∀ k, Inv (E k)`. Introduce `k c z' hc`.

Simplify using `only [hE, disjointed_eq_inter_compl, Set.mem_inter_iff, Set.mem_iInter, Set.mem_compl_iff, hWi _ c z' hc]`. Establish `hgE : ∀ k (c : K → ℂ) (z' : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → (E k).indicator g (fun p => c p.1 * z' p) = (E k).indicator g z'`. Introduce `k c z' hc`. Simplify using `only [Set.indicator_apply, hEi k c z' hc, hg0 c z' hc]`. Establish `hcov : ∀ z, Q z → ∃ k, z ∈ E k`.

Introduce `z hq`. Establish `: z ∈ ⋃ i ∈ T, W i` using `hTU ▸ Set.mem_iUnion.2 ⟨z, hzW z hq⟩`. Take `⟨i, hiT, hzi⟩` from `Set.mem_iUnion₂.1 this`. Take `⟨m, rfl⟩ : i ∈ Set.range f` from `hf ▸ Set.mem_insert_of_mem 0 hiT`. Establish `: z ∈ ⋃ k, E k`.

Rewrite using `[hE, iUnion_disjointed]`. Conclude with `Set.mem_iUnion.2 ⟨m, hzi⟩`. Conclude with `Set.mem_iUnion.1 this`. Establish `hae : ∀ B B' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ), IsGoodProj P B → IsGoodProj P B' → (∀ z ∈ mcPts P, IsSimpleSheetPt P B ((B (segre z) 0)⁻¹ • segre z) → IsSimpleSheetPt P B' ((B' (segre z) 0)⁻¹ • segre z) → ∃ k, z ∈ E k) → ∀ᵐ y, ENNReal.ofReal (ptsPosDens P B (pot L) …`. Introduce `B B' hB hB' hc`.

Establish `hnull` using `measure_union_null (hS K ι P e B hP hB) (hO K ι P e B B' hP hB hB')`. Use `filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with y hy`. Use `ptsPosDens_split _ _ E y (fibreFinite K ι P e B hP hB y) hEd fun w hw hs z hz hzw => ?_` and prove the remaining obligations. Establish `hw1 : B w 0 = 1`. Take `⟨_, _, _, h⟩` from `hw`.

Rewrite using `[h]`. Both sides reduce to the same expression. Establish `hs1 : IsSimpleSheetPt P B w`. Assume the negation of the conclusion as `hn`. Conclude with `hy (Or.inl ⟨w, hw, hs, hn⟩)`.

Establish `hs2 : IsSimpleSheetPt P B' ((B' w 0)⁻¹ • w)`. Assume the negation of the conclusion as `hn`. Conclude with `hy (Or.inr ⟨w, hw, hs1, hn⟩)`. Substitute `hzw` using the available equality. Use `hc z hz ?_ hs2` and prove the remaining obligations.

Rewrite using `[hw1, inv_one, one_smul]` and apply the resulting hypothesis. Establish `hint : ∀ B : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ), IsGoodProj P B → (∀ᵐ y, ENNReal.ofReal (ptsPosDens P B (pot L) g y) = ∑' k, ENNReal.ofReal (ptsPosDens P B (pot L) ((E k).indicator g) y)) → ∫⁻ y, ENNReal.ofReal (ptsPosDens P B (pot L) g y) = ∑' k, ∫⁻ y, ENNReal.ofReal …`. Introduce `B hB h2`. Rewrite using `[lintegral_congr_ae h2, lintegral_tsum fun k => (hM K ι P e B L _ hP hB hLs (hg.indicator (hEm k)) (hgE k)).ennreal_ofReal]`. Rewrite using `[hint Ψ hΨ (hae Ψ Ψ' hΨ hΨ' fun z hz h1 h2 => hcov z ⟨hz, h1, h2⟩), hint Ψ' hΨ' (hae Ψ' Ψ hΨ' hΨ fun z hz h1 h2 => hcov z ⟨hz, h2, h1⟩)]`.

Conclude with `tsum_congr fun k => hWE (f k) (E k) (hEm k) (hEi k) (hEW k)`.
-/
theorem PtsPosPartProjIndep.proof (hS : PtsSheetSimpleNull.Statement) (hO : PtsSheetOnlyNull.Statement)
    (hL : PtsPosPartLocal.Statement) (hM : PtsPosDensMeasurable.Statement) :
    PtsPosPartProjIndep.Statement := by
  intro K _ ι _ P e Ψ Ψ' L g hP hΨ hΨ' hLs hg hg0
  classical

  set Inv : Set ((Σ k, ι k) → ℂ) → Prop := fun S => ∀ (c : K → ℂ) (z' : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) →
    ((fun p => c p.1 * z' p) ∈ S ↔ z' ∈ S) with hInv

  set Q : ((Σ k, ι k) → ℂ) → Prop := fun z => z ∈ mcPts P ∧
    IsSimpleSheetPt P Ψ ((Ψ (segre z) 0)⁻¹ • segre z) ∧
    IsSimpleSheetPt P Ψ' ((Ψ' (segre z) 0)⁻¹ • segre z) with hQ
  have key : ∀ z, ∃ W : Set ((Σ k, ι k) → ℂ), IsOpen W ∧ Inv W ∧ (Q z → z ∈ W) ∧
      ∀ E, MeasurableSet E → Inv E → E ⊆ W →
        ∫⁻ y, ENNReal.ofReal (ptsPosDens P Ψ (pot L) (E.indicator g) y) =
          ∫⁻ y, ENNReal.ofReal (ptsPosDens P Ψ' (pot L) (E.indicator g) y) := by
    intro z
    by_cases hz : Q z
    · obtain ⟨W, hW, hzW, hWi, hWE⟩ := hL K ι P e Ψ Ψ' L g z hP hΨ hΨ' hLs hg hg0 hz.1 hz.2.1 hz.2.2
      exact ⟨W, hW, hWi, fun _ => hzW, hWE⟩
    · refine ⟨∅, isOpen_empty, fun _ _ _ => Iff.rfl, fun h => absurd h hz, fun E _ _ hE => ?_⟩
      rw [Set.subset_empty_iff.1 hE, Set.indicator_empty]
      simp [ptsPosDens, sheetDensity]
  choose W hWo hWi hzW hWE using key
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable W hWo
  obtain ⟨f, hf⟩ := (hTc.insert 0).exists_eq_range (Set.insert_nonempty 0 T)
  set E : ℕ → Set ((Σ k, ι k) → ℂ) := disjointed (fun k => W (f k)) with hE
  have hEm : ∀ k, MeasurableSet (E k) := MeasurableSet.disjointed fun k => (hWo (f k)).measurableSet
  have hEW : ∀ k, E k ⊆ W (f k) := disjointed_subset _
  have hEd : Pairwise (Function.onFun Disjoint E) := disjoint_disjointed _
  have hEi : ∀ k, Inv (E k) := by
    intro k c z' hc
    simp only [hE, disjointed_eq_inter_compl, Set.mem_inter_iff, Set.mem_iInter, Set.mem_compl_iff,
      hWi _ c z' hc]
  have hgE : ∀ k (c : K → ℂ) (z' : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) →
      (E k).indicator g (fun p => c p.1 * z' p) = (E k).indicator g z' := by
    intro k c z' hc
    simp only [Set.indicator_apply, hEi k c z' hc, hg0 c z' hc]
  have hcov : ∀ z, Q z → ∃ k, z ∈ E k := by
    intro z hq
    have : z ∈ ⋃ i ∈ T, W i := hTU ▸ Set.mem_iUnion.2 ⟨z, hzW z hq⟩
    obtain ⟨i, hiT, hzi⟩ := Set.mem_iUnion₂.1 this
    obtain ⟨m, rfl⟩ : i ∈ Set.range f := hf ▸ Set.mem_insert_of_mem 0 hiT
    have : z ∈ ⋃ k, E k := by
      rw [hE, iUnion_disjointed]
      exact Set.mem_iUnion.2 ⟨m, hzi⟩
    exact Set.mem_iUnion.1 this

  have hae : ∀ B B' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ), IsGoodProj P B → IsGoodProj P B' →
      (∀ z ∈ mcPts P, IsSimpleSheetPt P B ((B (segre z) 0)⁻¹ • segre z) →
        IsSimpleSheetPt P B' ((B' (segre z) 0)⁻¹ • segre z) → ∃ k, z ∈ E k) →
      ∀ᵐ y, ENNReal.ofReal (ptsPosDens P B (pot L) g y) =
        ∑' k, ENNReal.ofReal (ptsPosDens P B (pot L) ((E k).indicator g) y) := by
    intro B B' hB hB' hc
    have hnull := measure_union_null (hS K ι P e B hP hB) (hO K ι P e B B' hP hB hB')
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with y hy
    refine ptsPosDens_split _ _ E y (fibreFinite K ι P e B hP hB y) hEd fun w hw hs z hz hzw => ?_
    have hw1 : B w 0 = 1 := by
      obtain ⟨_, _, _, h⟩ := hw
      rw [h]
      rfl
    have hs1 : IsSimpleSheetPt P B w := by
      by_contra hn
      exact hy (Or.inl ⟨w, hw, hs, hn⟩)
    have hs2 : IsSimpleSheetPt P B' ((B' w 0)⁻¹ • w) := by
      by_contra hn
      exact hy (Or.inr ⟨w, hw, hs1, hn⟩)
    subst hzw
    refine hc z hz ?_ hs2
    rwa [hw1, inv_one, one_smul]
  have hint : ∀ B : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ), IsGoodProj P B →
      (∀ᵐ y, ENNReal.ofReal (ptsPosDens P B (pot L) g y) =
        ∑' k, ENNReal.ofReal (ptsPosDens P B (pot L) ((E k).indicator g) y)) →
      ∫⁻ y, ENNReal.ofReal (ptsPosDens P B (pot L) g y) =
        ∑' k, ∫⁻ y, ENNReal.ofReal (ptsPosDens P B (pot L) ((E k).indicator g) y) := by
    intro B hB h2
    rw [lintegral_congr_ae h2, lintegral_tsum fun k =>
      (hM K ι P e B L _ hP hB hLs (hg.indicator (hEm k)) (hgE k)).ennreal_ofReal]
  rw [hint Ψ hΨ (hae Ψ Ψ' hΨ hΨ' fun z hz h1 h2 => hcov z ⟨hz, h1, h2⟩),
    hint Ψ' hΨ' (hae Ψ' Ψ hΨ' hΨ fun z hz h1 h2 => hcov z ⟨hz, h2, h1⟩)]
  exact tsum_congr fun k => hWE (f k) (E k) (hEm k) (hEi k) (hEW k)

end GroundTheory.Heights₂.Heights
