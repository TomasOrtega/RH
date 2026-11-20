import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ProdFnMemSB
open GlobalTheory.SplitWeil GlobalTheory.LocFlat.CFac

open Filter Topology

noncomputable section
namespace GlobalTheory.LocFlat.CFac.Span

/- English proof (translation)
Rewrite using `[IsLocallyConstant.iff_eventually_eq]`. Introduce `x`. Distinguish the cases in `hx : x ∈ W`. Use `filter_upwards [hW.isOpen.mem_nhds hx] with y hy`. Simplify using `[Set.indicator_of_mem hy, Set.indicator_of_mem hx]`.

Use `filter_upwards [hW.isClosed.isOpen_compl.mem_nhds hx] with y hy`. Simplify using `[Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]`.
-/
theorem isLocallyConstant_indicator_one {Z : Type} [TopologicalSpace Z] {W : Set Z} (hW : IsClopen W) :
    IsLocallyConstant (W.indicator (1 : Z → ℂ)) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  by_cases hx : x ∈ W
  · filter_upwards [hW.isOpen.mem_nhds hx] with y hy
    simp [Set.indicator_of_mem hy, Set.indicator_of_mem hx]
  · filter_upwards [hW.isClosed.isOpen_compl.mem_nhds hx] with y hy
    simp [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]

/- English proof (translation)
Assemble the required witnesses or components as `⟨isLocallyConstant_indicator_one hW, HasCompactSupport.intro' hc hW.isClosed fun x hx => Set.indicator_of_notMem hx _⟩`.
-/
theorem indicator_one_mem_SB {Z : Type} [TopologicalSpace Z] {W : Set Z} (hc : IsCompact W)
    (hW : IsClopen W) : W.indicator (1 : Z → ℂ) ∈ SB Z :=
  ⟨isLocallyConstant_indicator_one hW, HasCompactSupport.intro' hc hW.isClosed fun x hx => Set.indicator_of_notMem hx _⟩

def S (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] : Submodule ℂ (X × Y → ℂ) :=
  Submodule.span ℂ (Set.range fun q : SB X × SB Y => prodFn q.1.1 q.2.1)

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

def IsBox (r : Set X × Set Y) : Prop := IsCompact r.1 ∧ IsClopen r.1 ∧ IsCompact r.2 ∧ IsClopen r.2

/- English proof (translation)
Assemble the required witnesses or components as `⟨hr.1.inter_right hs.2.1.isClosed, hr.2.1.inter hs.2.1, hr.2.2.1.inter_right hs.2.2.2.isClosed, hr.2.2.2.inter hs.2.2.2⟩`.
-/
theorem IsBox.inter {r s : Set X × Set Y} (hr : IsBox r) (hs : IsBox s) :
    IsBox (r.1 ∩ s.1, r.2 ∩ s.2) :=
  ⟨hr.1.inter_right hs.2.1.isClosed, hr.2.1.inter hs.2.1, hr.2.2.1.inter_right hs.2.2.2.isClosed,
    hr.2.2.2.inter hs.2.2.2⟩

/- English proof (translation)
Establish `: (r.1 ×ˢ r.2).indicator (1 : X × Y → ℂ) = prodFn (r.1.indicator 1) (r.2.indicator 1)`. Use extensionality with `⟨x, y⟩`. Apply the tactic sequence `by_cases hx : x ∈ r.1 <;> by_cases hy : y ∈ r.2 <;> simp [prodFn, Set.indicator, hx, hy]`. Rewrite using `[this]`. Conclude with `Submodule.subset_span ⟨(⟨_, indicator_one_mem_SB hr.1 hr.2.1⟩, ⟨_, indicator_one_mem_SB hr.2.2.1 hr.2.2.2⟩), rfl⟩`.
-/
theorem box_mem {r : Set X × Set Y} (hr : IsBox r) :
    (r.1 ×ˢ r.2).indicator (1 : X × Y → ℂ) ∈ S X Y := by
  have : (r.1 ×ˢ r.2).indicator (1 : X × Y → ℂ) = prodFn (r.1.indicator 1) (r.2.indicator 1) := by
    ext ⟨x, y⟩
    by_cases hx : x ∈ r.1 <;> by_cases hy : y ∈ r.2 <;> simp [prodFn, Set.indicator, hx, hy]
  rw [this]
  exact Submodule.subset_span ⟨(⟨_, indicator_one_mem_SB hr.1 hr.2.1⟩,
    ⟨_, indicator_one_mem_SB hr.2.2.1 hr.2.2.2⟩), rfl⟩

def U (L : List (Set X × Set Y)) : Set (X × Y) := ⋃ r ∈ L, r.1 ×ˢ r.2

/- English proof (translation)
Simplify using `[U]`.
-/
theorem U_cons (r : Set X × Set Y) (L : List (Set X × Set Y)) : U (r :: L) = r.1 ×ˢ r.2 ∪ U L := by
  simp [U]

/- English proof (translation)
Use extensionality with `p`. Simplify using `only [U, Set.mem_inter_iff, Set.mem_iUnion, List.mem_map, Set.mem_prod]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨h1, h2⟩, s, hs, h3, h4⟩`. Conclude with `⟨_, ⟨s, hs, rfl⟩, ⟨h1, h3⟩, ⟨h2, h4⟩⟩`.

Introduce and unpack `⟨_, ⟨s, hs, rfl⟩, ⟨h1, h3⟩, ⟨h2, h4⟩⟩`. Conclude with `⟨⟨h1, h2⟩, s, hs, h3, h4⟩`.
-/
theorem inter_U (r : Set X × Set Y) (L : List (Set X × Set Y)) :
    r.1 ×ˢ r.2 ∩ U L = U (L.map fun s => (r.1 ∩ s.1, r.2 ∩ s.2)) := by
  ext p
  simp only [U, Set.mem_inter_iff, Set.mem_iUnion, List.mem_map, Set.mem_prod]
  constructor
  · rintro ⟨⟨h1, h2⟩, s, hs, h3, h4⟩
    exact ⟨_, ⟨s, hs, rfl⟩, ⟨h1, h3⟩, ⟨h2, h4⟩⟩
  · rintro ⟨_, ⟨s, hs, rfl⟩, ⟨h1, h3⟩, ⟨h2, h4⟩⟩
    exact ⟨⟨h1, h2⟩, s, hs, h3, h4⟩

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `L hL _`. Rewrite using `[List.length_eq_zero_iff.1 (Nat.le_zero.1 hL)]`.

Simplify using `[U]`. Conclude with `Submodule.zero_mem _`. Consider the case `succ n ih`. Introduce `L hL hB`. Consider the cases of `L with`.

Consider the case `nil => simp [U]`. Conclude with `Submodule.zero_mem _`. Consider the case `cons r L`. Establish `key` using `Set.indicator_union_add_inter (f := (1 : X × Y → ℂ)) (r.1 ×ˢ r.2) (U L)`. Establish `hL' : L.length ≤ n` using `by simp at hL; omega`.

Rewrite using `[U_cons, eq_sub_of_add_eq key, inter_U]`. Use `Submodule.sub_mem _ (Submodule.add_mem _ (box_mem (hB r (by simp))) (ih L hL' fun s hs => hB s (by simp [hs]))) (ih _ (by simpa using hL') ?_)` and prove the remaining obligations. Introduce `s hs`. Take `⟨t, ht, rfl⟩` from `List.mem_map.1 hs`. Conclude with `(hB r (by simp)).inter (hB t (by simp [ht]))`.
-/
theorem U_mem : ∀ (n : ℕ) (L : List (Set X × Set Y)), L.length ≤ n → (∀ r ∈ L, IsBox r) →
    (U L).indicator (1 : X × Y → ℂ) ∈ S X Y := by
  intro n
  induction n with
  | zero =>
    intro L hL _
    rw [List.length_eq_zero_iff.1 (Nat.le_zero.1 hL)]
    simp [U]
    exact Submodule.zero_mem _
  | succ n ih =>
    intro L hL hB
    cases L with
    | nil => simp [U]; exact Submodule.zero_mem _
    | cons r L =>
      have key := Set.indicator_union_add_inter (f := (1 : X × Y → ℂ)) (r.1 ×ˢ r.2) (U L)
      have hL' : L.length ≤ n := by simp at hL; omega
      rw [U_cons, eq_sub_of_add_eq key, inter_U]
      refine Submodule.sub_mem _ (Submodule.add_mem _ (box_mem (hB r (by simp)))
        (ih L hL' fun s hs => hB s (by simp [hs]))) (ih _ (by simpa using hL') ?_)
      intro s hs
      obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hs
      exact (hB r (by simp)).inter (hB t (by simp [ht]))

/- English proof (translation)
Introduce `L`. Proceed by induction on `L with`. Consider the case `nil => intro _`. Simplify using `[U]`. Conclude with `Submodule.zero_mem _`.

Consider the case `cons r L ih`. Introduce `hL`. Take `⟨hB, c, hc⟩` from `hL r (by simp)`. Establish `key` using `Set.indicator_union_add_inter (f := F) (r.1 ×ˢ r.2) (U L)`. Establish `hA : (r.1 ×ˢ r.2).indicator F = c • (r.1 ×ˢ r.2).indicator (1 : X × Y → ℂ)`.

Use extensionality with `p`. Simplify using `only [Pi.smul_apply]`. Distinguish the cases in `hp : p ∈ r.1 ×ˢ r.2`. Rewrite using `[Set.indicator_of_mem hp, Set.indicator_of_mem hp]`. Simplify using `[hc p hp]`.

Rewrite using `[Set.indicator_of_notMem hp, Set.indicator_of_notMem hp]`. Simplify using the standard rewrite rules. Establish `hI : (r.1 ×ˢ r.2 ∩ U L).indicator F = c • (r.1 ×ˢ r.2 ∩ U L).indicator (1 : X × Y → ℂ)`. Use extensionality with `p`. Simplify using `only [Pi.smul_apply]`.

Distinguish the cases in `hp : p ∈ r.1 ×ˢ r.2 ∩ U L`. Rewrite using `[Set.indicator_of_mem hp, Set.indicator_of_mem hp]`. Simplify using `[hc p hp.1]`. Rewrite using `[Set.indicator_of_notMem hp, Set.indicator_of_notMem hp]`. Simplify using the standard rewrite rules.

Rewrite using `[U_cons, eq_sub_of_add_eq key, hA, hI, inter_U]`. Use `Submodule.sub_mem _ (Submodule.add_mem _ (Submodule.smul_mem _ c (box_mem hB)) (ih fun s hs => hL s (by simp [hs]))) (Submodule.smul_mem _ c (U_mem _ _ le_rfl ?_))` and prove the remaining obligations. Introduce `s hs`. Take `⟨t, ht, rfl⟩` from `List.mem_map.1 hs`. Conclude with `hB.inter (hL t (by simp [ht])).1`.
-/
theorem F_mem (F : X × Y → ℂ) : ∀ L : List (Set X × Set Y),
    (∀ r ∈ L, IsBox r ∧ ∃ c : ℂ, ∀ p ∈ r.1 ×ˢ r.2, F p = c) → (U L).indicator F ∈ S X Y := by
  intro L
  induction L with
  | nil => intro _; simp [U]; exact Submodule.zero_mem _
  | cons r L ih =>
    intro hL
    obtain ⟨hB, c, hc⟩ := hL r (by simp)
    have key := Set.indicator_union_add_inter (f := F) (r.1 ×ˢ r.2) (U L)
    have hA : (r.1 ×ˢ r.2).indicator F = c • (r.1 ×ˢ r.2).indicator (1 : X × Y → ℂ) := by
      ext p
      simp only [Pi.smul_apply]
      by_cases hp : p ∈ r.1 ×ˢ r.2
      · rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp]; simp [hc p hp]
      · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hp]; simp
    have hI : (r.1 ×ˢ r.2 ∩ U L).indicator F = c • (r.1 ×ˢ r.2 ∩ U L).indicator (1 : X × Y → ℂ) := by
      ext p
      simp only [Pi.smul_apply]
      by_cases hp : p ∈ r.1 ×ˢ r.2 ∩ U L
      · rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp]; simp [hc p hp.1]
      · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hp]; simp
    rw [U_cons, eq_sub_of_add_eq key, hA, hI, inter_U]
    refine Submodule.sub_mem _ (Submodule.add_mem _ (Submodule.smul_mem _ c (box_mem hB))
      (ih fun s hs => hL s (by simp [hs]))) (Submodule.smul_mem _ c (U_mem _ _ le_rfl ?_))
    intro s hs
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hs
    exact hB.inter (hL t (by simp [ht])).1

/- English proof (translation)
Take `⟨K, hK, hxK, hKO⟩` from `exists_compact_subset hO hx`. Take `⟨V, hV, hxV, hVK⟩` from `(loc_compact_Haus_tot_disc_of_zero_dim (H := X)).isOpen_iff.1 isOpen_interior x hxK`. Conclude with `⟨V, hK.of_isClosed_subset hV.isClosed (hVK.trans interior_subset), hV, hxV, (hVK.trans interior_subset).trans hKO⟩`.
-/
theorem exists_compact_clopen [LocallyCompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]
    {x : X} {O : Set X} (hO : IsOpen O) (hx : x ∈ O) :
    ∃ V, IsCompact V ∧ IsClopen V ∧ x ∈ V ∧ V ⊆ O := by
  obtain ⟨K, hK, hxK, hKO⟩ := exists_compact_subset hO hx
  obtain ⟨V, hV, hxV, hVK⟩ := (loc_compact_Haus_tot_disc_of_zero_dim (H := X)).isOpen_iff.1
    isOpen_interior x hxK
  exact ⟨V, hK.of_isClosed_subset hV.isClosed (hVK.trans interior_subset), hV, hxV,
    (hVK.trans interior_subset).trans hKO⟩

/- English proof (translation)
Establish `hbox : ∀ p : X × Y, ∃ r : Set X × Set Y, IsBox r ∧ p ∈ r.1 ×ˢ r.2 ∧ ∀ q ∈ r.1 ×ˢ r.2, F q = F p`. Introduce `p`. Establish `hO : IsOpen {q | F q = F p}` using `hF.1.isOpen_fiber _`. Take `⟨u, v, hu, hv, hpu, hpv, huv⟩` from `isOpen_prod_iff.1 hO p.1 p.2 rfl`. Take `⟨U₁, hU1, hU2, hU3, hU4⟩` from `exists_compact_clopen hu hpu`.

Take `⟨V₁, hV1, hV2, hV3, hV4⟩` from `exists_compact_clopen hv hpv`. Conclude with `⟨(U₁, V₁), ⟨hU1, hU2, hV1, hV2⟩, ⟨hU3, hV3⟩, fun q hq => huv (Set.prod_mono hU4 hV4 hq)⟩`. Use `choose R hRb hRp hRc using hbox`. Take `⟨t, -, ht⟩` from `hF.2.isCompact.elim_nhds_subcover (fun p => (R p).1 ×ˢ (R p).2) fun p _ => ((hRb p).2.1.isOpen.prod (hRb p).2.2.2.isOpen).mem_nhds (hRp p)`. Establish `hsub : tsupport F ⊆ U (t.toList.map R)`.

Introduce `q hq`. Use `ht hq` as an intermediate fact. Simplify using `only [Set.mem_iUnion] at this`. Take `⟨p, hp, hq'⟩` from `this`. Simplify using `only [U, Set.mem_iUnion]`.

Conclude with `⟨R p, List.mem_map.2 ⟨p, Finset.mem_toList.2 hp, rfl⟩, hq'⟩`. Establish `heq : (U (t.toList.map R)).indicator F = F` using `Set.indicator_eq_self.2 ((subset_tsupport F).trans hsub)`. Rewrite using `[← heq]`. Use `F_mem F _ ?_` and prove the remaining obligations. Introduce `r hr`.

Take `⟨p, -, rfl⟩` from `List.mem_map.1 hr`. Conclude with `⟨hRb p, F p, hRc p⟩`.
-/
theorem mem_S [T2Space X] [LocallyCompactSpace X] [TotallyDisconnectedSpace X]
    [T2Space Y] [LocallyCompactSpace Y] [TotallyDisconnectedSpace Y]
    (F : X × Y → ℂ) (hF : F ∈ SB (X × Y)) : F ∈ S X Y := by
  have hbox : ∀ p : X × Y, ∃ r : Set X × Set Y, IsBox r ∧ p ∈ r.1 ×ˢ r.2 ∧
      ∀ q ∈ r.1 ×ˢ r.2, F q = F p := by
    intro p
    have hO : IsOpen {q | F q = F p} := hF.1.isOpen_fiber _
    obtain ⟨u, v, hu, hv, hpu, hpv, huv⟩ := isOpen_prod_iff.1 hO p.1 p.2 rfl
    obtain ⟨U₁, hU1, hU2, hU3, hU4⟩ := exists_compact_clopen hu hpu
    obtain ⟨V₁, hV1, hV2, hV3, hV4⟩ := exists_compact_clopen hv hpv
    exact ⟨(U₁, V₁), ⟨hU1, hU2, hV1, hV2⟩, ⟨hU3, hV3⟩, fun q hq => huv (Set.prod_mono hU4 hV4 hq)⟩
  choose R hRb hRp hRc using hbox
  obtain ⟨t, -, ht⟩ := hF.2.isCompact.elim_nhds_subcover (fun p => (R p).1 ×ˢ (R p).2)
    fun p _ => ((hRb p).2.1.isOpen.prod (hRb p).2.2.2.isOpen).mem_nhds (hRp p)
  have hsub : tsupport F ⊆ U (t.toList.map R) := by
    intro q hq
    have := ht hq
    simp only [Set.mem_iUnion] at this
    obtain ⟨p, hp, hq'⟩ := this
    simp only [U, Set.mem_iUnion]
    exact ⟨R p, List.mem_map.2 ⟨p, Finset.mem_toList.2 hp, rfl⟩, hq'⟩
  have heq : (U (t.toList.map R)).indicator F = F :=
    Set.indicator_eq_self.2 ((subset_tsupport F).trans hsub)
  rw [← heq]
  refine F_mem F _ ?_
  intro r hr
  obtain ⟨p, -, rfl⟩ := List.mem_map.1 hr
  exact ⟨hRb p, F p, hRc p⟩

/- English proof (translation)
Introduce `X Y _ _ _ _ _ _ _ _`. Establish `hmap : (Submodule.span ℂ (Set.range fun q : SB X × SB Y => prodSB q.1 q.2)).map (SB (X × Y)).subtype = S X Y`. Rewrite using `[Submodule.map_span, ← Set.range_comp]`. Both sides reduce to the same expression. Rewrite using `[eq_top_iff]`.

Introduce and unpack `F -`. Establish `h` using `mem_S F.1 F.2`. Rewrite `h` using `[← hmap]`. Take `⟨G, hG, hGF⟩` from `Submodule.mem_map.1 h`. Establish `: G = F` using `Subtype.ext hGF`.

Rewrite using `[← this]` and apply the resulting hypothesis.
-/
theorem span_prodSB_eq_top : ∀ (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] [T2Space X]
    [LocallyCompactSpace X] [TotallyDisconnectedSpace X] [T2Space Y] [LocallyCompactSpace Y]
    [TotallyDisconnectedSpace Y],
    Submodule.span ℂ (Set.range fun q : SB X × SB Y => prodSB q.1 q.2) = ⊤ := by
  intro X Y _ _ _ _ _ _ _ _
  have hmap : (Submodule.span ℂ (Set.range fun q : SB X × SB Y => prodSB q.1 q.2)).map
      (SB (X × Y)).subtype = S X Y := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  rw [eq_top_iff]
  rintro F -
  have h := mem_S F.1 F.2
  rw [← hmap] at h
  obtain ⟨G, hG, hGF⟩ := Submodule.mem_map.1 h
  have : G = F := Subtype.ext hGF
  rwa [← this]

end GlobalTheory.LocFlat.CFac.Span
