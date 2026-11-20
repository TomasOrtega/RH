import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFlatLift
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.TotalDifferentialCupProduct
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CechVanishingAlongFiltration

open GlobalTheory GlobalTheory.DI

namespace GlobalTheory.DI

/- English proof (translation)
Establish `hU : ({x ∈ u | x ≤ j}) ∪ ({x ∈ u | j ≤ x}) = u`. Use extensionality with `x`. Simplify using `only [Finset.mem_union, Finset.mem_filter]`. Prove the components needed by the constructor for the conclusion. Apply the tactic sequence `rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h`.

Introduce `hx`. Break down `le_total x j with h | h` into its components or cases. Conclude with `Or.inl ⟨hx, h⟩`. Conclude with `Or.inr ⟨hx, h⟩`. Establish `hI : ({x ∈ u | x ≤ j}) ∩ ({x ∈ u | j ≤ x}) = {j}`.

Use extensionality with `x`. Simplify using `only [Finset.mem_inter, Finset.mem_filter, Finset.mem_singleton]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨_, h1⟩, ⟨_, h2⟩⟩`. Conclude with `le_antisymm h1 h2`.

Introduce and unpack `rfl`. Conclude with `⟨⟨hj, le_refl _⟩, ⟨hj, le_refl _⟩⟩`. Establish `h` using `Finset.card_union_add_card_inter ({x ∈ u | x ≤ j}) ({x ∈ u | j ≤ x})`. Rewrite `h` using `[hU, hI, Finset.card_singleton]`. Use linear arithmetic over natural numbers and integers.
-/
private theorem card_filter_le_add_card_filter_ge {ι : Type} [LinearOrder ι] (u : Finset ι) (j : ι)
    (hj : j ∈ u) : ({x ∈ u | x ≤ j}).card + ({x ∈ u | j ≤ x}).card = u.card + 1 := by
  have hU : ({x ∈ u | x ≤ j}) ∪ ({x ∈ u | j ≤ x}) = u := by
    ext x
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · intro hx
      rcases le_total x j with h | h
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr ⟨hx, h⟩
  have hI : ({x ∈ u | x ≤ j}) ∩ ({x ∈ u | j ≤ x}) = {j} := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨_, h1⟩, ⟨_, h2⟩⟩
      exact le_antisymm h1 h2
    · rintro rfl
      exact ⟨⟨hj, le_refl _⟩, ⟨hj, le_refl _⟩⟩
  have h := Finset.card_union_add_card_inter ({x ∈ u | x ≤ j}) ({x ∈ u | j ≤ x})
  rw [hU, hI, Finset.card_singleton] at h
  omega

/- English proof (translation)
Introduce `ι _ E _ d N T Φ hdd hN hT hd hΦ0 hΦD hΦT hC a b hH`. Set `Ψ : (Finset ι → E) →+ (Finset ι → E)` to `AddMonoidHom.mk' (fun c => cup Φ c) (by`. Introduce `c c'`. Use function extensionality and compare the values at `u`. Simplify using `only [cup, Pi.add_apply, map_add, Finset.sum_add_distrib])`.

Establish `hΨ : ∀ c, Ψ c = cup Φ c` using `fun c => rfl`. Set `γ : Finset ι → E → E` to `fun s x => if h : s.Nonempty then Φ x {s.max' h} else 0`. Use `cechZero_of_hypZero_filtered d N T Ψ γ hdd hN hT hd ?_ ?_ ?_ ?_ a b hH` and prove the remaining obligations. Introduce `m c hc`. Rewrite using `[hΨ, hΨ]`.

Conclude with `Dtot_cup d Φ c hΦ0 hc.1 (fun s => hΦD _)`. Introduce `m c hc`. Rewrite using `[hΨ]`. Use `⟨?_, fun q u hq => ?_, fun u hu => ?_⟩` and prove the remaining obligations. Simplify using `[cup]`.

Simplify using `only [cup]`. Use `sum_mem fun j hj => ?_` and prove the remaining obligations. Establish `hsz` using `card_filter_le_add_card_filter_ge u j hj`. Establish `hLne : ({x ∈ u | x ≤ j}).Nonempty` using `⟨j, Finset.mem_filter.mpr ⟨hj, le_refl _⟩⟩`. Establish `hune : u.Nonempty` using `⟨j, hj⟩`.

Distinguish the cases in `hLm : ({x ∈ u | x ≤ j}).card ≤ m`. Establish `hx : c ({x ∈ u | x ≤ j}) ∈ N (m - ({x ∈ u | x ≤ j}).card) u` using `hN _ _ u hLne (Finset.filter_subset _ _) (hc.2.1 _ _ (by omega))`. Conclude with `(hΦT _ u _ _ hune (Finset.filter_subset _ _) hx).1 q (by omega)`. Rewrite using `[hc.2.2 _ (by omega), map_zero, Pi.zero_apply]`. Conclude with `zero_mem _`.

Simplify using `only [cup]`. Use `Finset.sum_eq_zero fun j hj => ?_` and prove the remaining obligations. Establish `hsz` using `card_filter_le_add_card_filter_ge u j hj`. Establish `hLne : ({x ∈ u | x ≤ j}).Nonempty` using `⟨j, Finset.mem_filter.mpr ⟨hj, le_refl _⟩⟩`. Establish `hune : u.Nonempty` using `⟨j, hj⟩`.

Distinguish the cases in `hLm : ({x ∈ u | x ≤ j}).card ≤ m`. Establish `hx : c ({x ∈ u | x ≤ j}) ∈ N (m - ({x ∈ u | x ≤ j}).card) u` using `hN _ _ u hLne (Finset.filter_subset _ _) (hc.2.1 _ _ (by omega))`. Conclude with `(hΦT _ u _ _ hune (Finset.filter_subset _ _) hx).2 (by omega)`. Rewrite using `[hc.2.2 _ (by omega), map_zero, Pi.zero_apply]`. Introduce `s hs`.

Establish `hγs : γ s = fun x => Φ x {s.max' hs}`. Use function extensionality and compare the values at `x`. Simplify using `only [γ, dif_pos hs]`. Rewrite using `[hγs]`. Conclude with `hC s (s.max' hs) (s.max'_mem hs)`.

Introduce `m c u hc hu hlow`. Rewrite using `[hΨ]`. Simplify using `only [cup]`. Rewrite using `[Finset.sum_eq_single_of_mem (u.max' hu) (u.max'_mem hu)]`. Establish `hL : ({x ∈ u | x ≤ u.max' hu}) = u`.

Use extensionality with `x`. Simplify using `only [Finset.mem_filter]`. Prove the components needed by the constructor for the conclusion. Conclude with `fun h => h.1`. Introduce `hx`.

Conclude with `⟨hx, u.le_max' x hx⟩`. Establish `hR : ({x ∈ u | u.max' hu ≤ x}) = {u.max' hu}`. Use extensionality with `x`. Simplify using `only [Finset.mem_filter, Finset.mem_singleton]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨hx, hle⟩`. Conclude with `le_antisymm (u.le_max' x hx) hle`. Introduce and unpack `rfl`. Conclude with `⟨u.max'_mem hu, le_refl _⟩`. Rewrite using `[hL, hR]`.

Simplify using `only [γ, dif_pos hu]`. Introduce `j hj hne`. Establish `hlt : ({x ∈ u | x ≤ j}).card < u.card`. Apply `Finset.card_lt_card` to reduce the goal to its premises. Use `⟨Finset.filter_subset _ _, fun hsub => ?_⟩` and prove the remaining obligations.

Establish `hm` using `hsub (u.max'_mem hu)`. Simplify using `only [Finset.mem_filter] at hm`. Conclude with `hne (le_antisymm (u.le_max' j hj) hm.2)`. Rewrite using `[hlow _ hlt, map_zero, Pi.zero_apply]`.
-/
theorem cechZero_of_hypZero_of_closed_map : ∀ {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E] (d : E →+ E) (N T : ℕ → Finset ι → AddSubgroup E) (Φ : E →+ (Finset ι → E)), (∀ x, d (d x) = 0) → (∀ q s t, s.Nonempty → s ⊆ t → N q s ≤ N q t) → (∀ q s t, s.Nonempty → s ⊆ t → T q s ≤ T q t) → (∀ q s x, x ∈ T q s → d x ∈ T (q + 1) s) → (∀ x, Φ x ∅ = 0) → (∀ x, Dtot d (Φ x) = 0) → (∀ a u t x, u.Nonempty → t ⊆ u → x ∈ N a u → (∀ q, q + t.card = a + 1 → Φ x t ∈ T q u) ∧ (a + 1 < t.card → Φ x t = 0)) → (∀ s, ∀ j ∈ s, CartierAt d (fun x => Φ x {j}) (fun a => N a s) (fun a => T a s)) → ∀ a b, HypZero d T (a + b) → CechZero (N a) b := by
  intro ι _ E _ d N T Φ hdd hN hT hd hΦ0 hΦD hΦT hC a b hH
  let Ψ : (Finset ι → E) →+ (Finset ι → E) := AddMonoidHom.mk' (fun c => cup Φ c) (by
    intro c c'
    funext u
    simp only [cup, Pi.add_apply, map_add, Finset.sum_add_distrib])
  have hΨ : ∀ c, Ψ c = cup Φ c := fun c => rfl
  let γ : Finset ι → E → E := fun s x => if h : s.Nonempty then Φ x {s.max' h} else 0
  refine cechZero_of_hypZero_filtered d N T Ψ γ hdd hN hT hd ?_ ?_ ?_ ?_ a b hH
  · intro m c hc
    rw [hΨ, hΨ]
    exact Dtot_cup d Φ c hΦ0 hc.1 (fun s => hΦD _)
  · intro m c hc
    rw [hΨ]
    refine ⟨?_, fun q u hq => ?_, fun u hu => ?_⟩
    · simp [cup]
    · simp only [cup]
      refine sum_mem fun j hj => ?_
      have hsz := card_filter_le_add_card_filter_ge u j hj
      have hLne : ({x ∈ u | x ≤ j}).Nonempty := ⟨j, Finset.mem_filter.mpr ⟨hj, le_refl _⟩⟩
      have hune : u.Nonempty := ⟨j, hj⟩
      by_cases hLm : ({x ∈ u | x ≤ j}).card ≤ m
      · have hx : c ({x ∈ u | x ≤ j}) ∈ N (m - ({x ∈ u | x ≤ j}).card) u :=
          hN _ _ u hLne (Finset.filter_subset _ _) (hc.2.1 _ _ (by omega))
        exact (hΦT _ u _ _ hune (Finset.filter_subset _ _) hx).1 q (by omega)
      · rw [hc.2.2 _ (by omega), map_zero, Pi.zero_apply]
        exact zero_mem _
    · simp only [cup]
      refine Finset.sum_eq_zero fun j hj => ?_
      have hsz := card_filter_le_add_card_filter_ge u j hj
      have hLne : ({x ∈ u | x ≤ j}).Nonempty := ⟨j, Finset.mem_filter.mpr ⟨hj, le_refl _⟩⟩
      have hune : u.Nonempty := ⟨j, hj⟩
      by_cases hLm : ({x ∈ u | x ≤ j}).card ≤ m
      · have hx : c ({x ∈ u | x ≤ j}) ∈ N (m - ({x ∈ u | x ≤ j}).card) u :=
          hN _ _ u hLne (Finset.filter_subset _ _) (hc.2.1 _ _ (by omega))
        exact (hΦT _ u _ _ hune (Finset.filter_subset _ _) hx).2 (by omega)
      · rw [hc.2.2 _ (by omega), map_zero, Pi.zero_apply]
  · intro s hs
    have hγs : γ s = fun x => Φ x {s.max' hs} := by
      funext x
      simp only [γ, dif_pos hs]
    rw [hγs]
    exact hC s (s.max' hs) (s.max'_mem hs)
  · intro m c u hc hu hlow
    rw [hΨ]
    simp only [cup]
    rw [Finset.sum_eq_single_of_mem (u.max' hu) (u.max'_mem hu)]
    · have hL : ({x ∈ u | x ≤ u.max' hu}) = u := by
        ext x
        simp only [Finset.mem_filter]
        constructor
        · exact fun h => h.1
        · intro hx
          exact ⟨hx, u.le_max' x hx⟩
      have hR : ({x ∈ u | u.max' hu ≤ x}) = {u.max' hu} := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨hx, hle⟩
          exact le_antisymm (u.le_max' x hx) hle
        · rintro rfl
          exact ⟨u.max'_mem hu, le_refl _⟩
      rw [hL, hR]
      simp only [γ, dif_pos hu]
    · intro j hj hne
      have hlt : ({x ∈ u | x ≤ j}).card < u.card := by
        apply Finset.card_lt_card
        refine ⟨Finset.filter_subset _ _, fun hsub => ?_⟩
        have hm := hsub (u.max'_mem hu)
        simp only [Finset.mem_filter] at hm
        exact hne (le_antisymm (u.le_max' j hj) hm.2)
      rw [hlow _ hlt, map_zero, Pi.zero_apply]

end GlobalTheory.DI
