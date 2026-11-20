import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StUnbranchedFibreSections
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

/- English proof (translation)
Introduce `σ _ X w B d A D δ N hP y₀ hy₀ hδ₀`. Take `⟨_, _, hD, _, _, hprop, _, hδan, _, hcard, hchart, _⟩` from `hP`. Establish `hF0 : {x | x ∈ X ∩ B ∧ A x = y₀}.encard = N` using `hcard y₀ hy₀ hδ₀`. Establish `hfin : {x | x ∈ X ∩ B ∧ A x = y₀}.Finite` using `Set.finite_of_encard_eq_coe hF0`. Establish `ht : hfin.toFinset.card = N`.

Establish `h` using `hfin.encard_eq_coe_toFinset_card`. Rewrite `h` using `[hF0]`. Conclude with `h.symm` after adjusting the coercions. Set `e : Fin N ≃ hfin.toFinset` to `(Finset.equivFinOfCardEq ht).symm`. Establish `he : ∀ i, (e i : σ → ℂ) ∈ X ∩ B ∧ A (e i) = y₀` using `fun i => hfin.mem_toFinset.mp (e i).2`.

Establish `hc : ∀ i : Fin N, ∃ (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ)) (g : (Fin d → ℂ) → σ → ℂ), IsOpen O ∧ IsOpen V ∧ (e i : σ → ℂ) ∈ V ∧ AnalyticOnNhd ℂ g O ∧ (∀ y ∈ O, A (g y) = y) ∧ X ∩ B ∩ V = g '' O` using `fun i => hchart _ (he i).1 (by rw [(he i).2]; exact hδ₀)`. Use `choose O V g hO hV hxV hg hAg hXV using hc`. Establish `hy₀O : ∀ i, y₀ ∈ O i`. Introduce `i`. Establish `hm : (e i : σ → ℂ) ∈ X ∩ B ∩ V i` using `⟨(he i).1, hxV i⟩`.

Rewrite `hm` using `[hXV i]`. Take `⟨y', hy', hgy'⟩` from `hm`. Establish `h` using `hAg i y' hy'`. Rewrite `h` using `[hgy', (he i).2]`. Rewrite using `[h]`.

Conclude with `hy'`. Take `⟨ρ, hρ, hρD⟩` from `Metric.isOpen_iff.mp hD y₀ hy₀`. Establish `hKD : Metric.closedBall y₀ (ρ / 2) ⊆ D` using `(Metric.closedBall_subset_ball (by linarith)).trans hρD`. Use `set C := {x | x ∈ X ∩ B ∧ A x ∈ Metric.closedBall y₀ (ρ / 2)} with hCdef`. Establish `hC : IsCompact C` using `hprop _ hKD (isCompact_closedBall _ _)`.

Establish `hC' : IsCompact (C \ ⋃ i, V i)` using `hC.diff (isOpen_iUnion hV)`. Establish `hE : IsClosed (A '' (C \ ⋃ i, V i))` using `(hC'.image A.continuous).isClosed`. Establish `hy₀E : y₀ ∉ A '' (C \ ⋃ i, V i)`. Introduce and unpack `⟨x, ⟨⟨hxXB, _⟩, hxV'⟩, hAx⟩`. Establish `hxF : x ∈ hfin.toFinset` using `hfin.mem_toFinset.mpr ⟨hxXB, hAx⟩`.

Apply `hxV'` to reduce the goal to its premises. Use `Set.mem_iUnion.mpr ⟨e.symm ⟨x, hxF⟩, ?_⟩` and prove the remaining obligations. Simplify using `using hxV (e.symm ⟨x, hxF⟩)`. Establish `hnhds : Metric.ball y₀ (ρ / 2) ∩ (A '' (C \ ⋃ i, V i))ᶜ ∩ (⋂ i, O i) ∩ {y | δ y ≠ 0} ∈ 𝓝 y₀`. Use `Filter.inter_mem (Filter.inter_mem (Filter.inter_mem (Metric.ball_mem_nhds _ (by linarith)) (hE.isOpen_compl.mem_nhds hy₀E)) ?_) ?_` and prove the remaining obligations.

Conclude with `Filter.iInter_mem.mpr fun i => (hO i).mem_nhds (hy₀O i)`. Conclude with `(hδan y₀ hy₀).continuousAt.eventually_ne hδ₀`. Take `⟨r, hr, hrsub⟩` from `Metric.mem_nhds_iff.mp hnhds`. Establish `hrD : Metric.ball y₀ r ⊆ D` using `fun y hy => hρD (Metric.ball_subset_ball (by linarith) (hrsub hy).1.1.1)`. Use `⟨r, g, hr, hrD, fun y hy => (hrsub hy).2, fun i y hy => hg i y (Set.mem_iInter.mp (hrsub hy).1.2 i), ?_⟩` and prove the remaining obligations.

Introduce `y hy`. Take `⟨⟨⟨hyb, hyE⟩, hyO⟩, hyδ⟩` from `hrsub hy`. Establish `hyO' : ∀ i, y ∈ O i` using `Set.mem_iInter.mp hyO`. Establish `hrange : {x | x ∈ X ∩ B ∧ A x = y} = Set.range (fun i => g i y)`. Use extensionality with `x`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hxXB, hAx⟩`. Establish `hxC : x ∈ C` using `⟨hxXB, by rw [hAx]; exact Metric.ball_subset_closedBall hyb⟩`. Establish `hxU : x ∈ ⋃ i, V i`. Assume the negation of the conclusion as `hn`.

Conclude with `hyE ⟨x, ⟨hxC, hn⟩, hAx⟩`. Take `⟨i, hi⟩` from `Set.mem_iUnion.mp hxU`. Establish `hm : x ∈ X ∩ B ∩ V i` using `⟨hxXB, hi⟩`. Rewrite `hm` using `[hXV i]`. Take `⟨y', hy', rfl⟩` from `hm`.

Establish `h` using `hAg i y' hy'`. Rewrite `h` using `[hAx]`. Conclude with `⟨i, by rw [h]⟩`. Introduce and unpack `⟨i, rfl⟩`. Establish `hm : g i y ∈ g i '' O i` using `⟨y, hyO' i, rfl⟩`.

Rewrite `hm` using `[← hXV i]`. Conclude with `⟨hm.1, hAg i y (hyO' i)⟩`. Use `⟨?_, hrange⟩` and prove the remaining obligations. Establish `hN : (Set.range (fun i => g i y)).encard = N`. Rewrite using `[← hrange]`.

Conclude with `hcard y (hrD hy) hyδ`. Establish `himg : Set.range (fun i => g i y) = ↑(Finset.univ.image (fun i => g i y))`. Simplify using the standard rewrite rules. Rewrite `hN` using `[himg, Set.encard_coe_eq_coe_finsetCard]`. Establish `hcardeq : (Finset.univ.image (fun i => g i y)).card = (Finset.univ : Finset (Fin N)).card`.

Rewrite using `[Finset.card_univ, Fintype.card_fin]`. Conclude with `hN` after adjusting the coercions. Establish `hinj` using `Finset.card_image_iff.mp hcardeq`. Introduce `i j hij`. Conclude with `hinj (Finset.mem_coe.mpr (Finset.mem_univ i)) (Finset.mem_coe.mpr (Finset.mem_univ j)) hij`.
-/
theorem UnbranchedFibreSections.proof : UnbranchedFibreSections.Statement := by
  intro σ _ X w B d A D δ N hP y₀ hy₀ hδ₀
  obtain ⟨_, _, hD, _, _, hprop, _, hδan, _, hcard, hchart, _⟩ := hP
  have hF0 : {x | x ∈ X ∩ B ∧ A x = y₀}.encard = N := hcard y₀ hy₀ hδ₀
  have hfin : {x | x ∈ X ∩ B ∧ A x = y₀}.Finite := Set.finite_of_encard_eq_coe hF0
  have ht : hfin.toFinset.card = N := by
    have h := hfin.encard_eq_coe_toFinset_card
    rw [hF0] at h
    exact_mod_cast h.symm
  let e : Fin N ≃ hfin.toFinset := (Finset.equivFinOfCardEq ht).symm
  have he : ∀ i, (e i : σ → ℂ) ∈ X ∩ B ∧ A (e i) = y₀ := fun i => hfin.mem_toFinset.mp (e i).2
  have hc : ∀ i : Fin N, ∃ (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ)) (g : (Fin d → ℂ) → σ → ℂ),
      IsOpen O ∧ IsOpen V ∧ (e i : σ → ℂ) ∈ V ∧ AnalyticOnNhd ℂ g O ∧ (∀ y ∈ O, A (g y) = y) ∧
        X ∩ B ∩ V = g '' O := fun i => hchart _ (he i).1 (by rw [(he i).2]; exact hδ₀)
  choose O V g hO hV hxV hg hAg hXV using hc
  have hy₀O : ∀ i, y₀ ∈ O i := by
    intro i
    have hm : (e i : σ → ℂ) ∈ X ∩ B ∩ V i := ⟨(he i).1, hxV i⟩
    rw [hXV i] at hm
    obtain ⟨y', hy', hgy'⟩ := hm
    have h := hAg i y' hy'
    rw [hgy', (he i).2] at h
    rw [h]
    exact hy'
  obtain ⟨ρ, hρ, hρD⟩ := Metric.isOpen_iff.mp hD y₀ hy₀
  have hKD : Metric.closedBall y₀ (ρ / 2) ⊆ D :=
    (Metric.closedBall_subset_ball (by linarith)).trans hρD
  set C := {x | x ∈ X ∩ B ∧ A x ∈ Metric.closedBall y₀ (ρ / 2)} with hCdef
  have hC : IsCompact C := hprop _ hKD (isCompact_closedBall _ _)
  have hC' : IsCompact (C \ ⋃ i, V i) := hC.diff (isOpen_iUnion hV)
  have hE : IsClosed (A '' (C \ ⋃ i, V i)) := (hC'.image A.continuous).isClosed
  have hy₀E : y₀ ∉ A '' (C \ ⋃ i, V i) := by
    rintro ⟨x, ⟨⟨hxXB, _⟩, hxV'⟩, hAx⟩
    have hxF : x ∈ hfin.toFinset := hfin.mem_toFinset.mpr ⟨hxXB, hAx⟩
    apply hxV'
    refine Set.mem_iUnion.mpr ⟨e.symm ⟨x, hxF⟩, ?_⟩
    simpa using hxV (e.symm ⟨x, hxF⟩)
  have hnhds : Metric.ball y₀ (ρ / 2) ∩ (A '' (C \ ⋃ i, V i))ᶜ ∩ (⋂ i, O i) ∩ {y | δ y ≠ 0} ∈ 𝓝 y₀ := by
    refine Filter.inter_mem (Filter.inter_mem (Filter.inter_mem
      (Metric.ball_mem_nhds _ (by linarith)) (hE.isOpen_compl.mem_nhds hy₀E)) ?_) ?_
    · exact Filter.iInter_mem.mpr fun i => (hO i).mem_nhds (hy₀O i)
    · exact (hδan y₀ hy₀).continuousAt.eventually_ne hδ₀
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp hnhds
  have hrD : Metric.ball y₀ r ⊆ D := fun y hy =>
    hρD (Metric.ball_subset_ball (by linarith) (hrsub hy).1.1.1)
  refine ⟨r, g, hr, hrD, fun y hy => (hrsub hy).2,
    fun i y hy => hg i y (Set.mem_iInter.mp (hrsub hy).1.2 i), ?_⟩
  intro y hy
  obtain ⟨⟨⟨hyb, hyE⟩, hyO⟩, hyδ⟩ := hrsub hy
  have hyO' : ∀ i, y ∈ O i := Set.mem_iInter.mp hyO
  have hrange : {x | x ∈ X ∩ B ∧ A x = y} = Set.range (fun i => g i y) := by
    ext x
    constructor
    · rintro ⟨hxXB, hAx⟩
      have hxC : x ∈ C := ⟨hxXB, by rw [hAx]; exact Metric.ball_subset_closedBall hyb⟩
      have hxU : x ∈ ⋃ i, V i := by
        by_contra hn
        exact hyE ⟨x, ⟨hxC, hn⟩, hAx⟩
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxU
      have hm : x ∈ X ∩ B ∩ V i := ⟨hxXB, hi⟩
      rw [hXV i] at hm
      obtain ⟨y', hy', rfl⟩ := hm
      have h := hAg i y' hy'
      rw [hAx] at h
      exact ⟨i, by rw [h]⟩
    · rintro ⟨i, rfl⟩
      have hm : g i y ∈ g i '' O i := ⟨y, hyO' i, rfl⟩
      rw [← hXV i] at hm
      exact ⟨hm.1, hAg i y (hyO' i)⟩
  refine ⟨?_, hrange⟩
  classical
  have hN : (Set.range (fun i => g i y)).encard = N := by
    rw [← hrange]
    exact hcard y (hrD hy) hyδ
  have himg : Set.range (fun i => g i y) = ↑(Finset.univ.image (fun i => g i y)) := by
    simp
  rw [himg, Set.encard_coe_eq_coe_finsetCard] at hN
  have hcardeq : (Finset.univ.image (fun i => g i y)).card = (Finset.univ : Finset (Fin N)).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact_mod_cast hN
  have hinj := Finset.card_image_iff.mp hcardeq
  intro i j hij
  exact hinj (Finset.mem_coe.mpr (Finset.mem_univ i)) (Finset.mem_coe.mpr (Finset.mem_univ j)) hij

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
