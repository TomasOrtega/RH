import Mathlib
open Filter Topology

namespace GlobalTheory

/- English proof (translation)
Introduce `C V Γ _ _ _ _ ν _h1 _h2 h3 F _`. Use `set S : Set Γ := ν '' {u | u ∈ F ∧ u ≠ 0} with hS`. Establish `hg : ∀ s ∈ S, ∃ u, (u ∈ F ∧ u ≠ 0) ∧ ν u = s` using `fun s hs => hs`. Use `choose! g hgF hgν using hg`. It suffices to establish `hcard : ∃ e : Fin (Module.finrank C F) → Γ, Function.Injective e ∧ ∀ i, e i ∈ S by`.

Take `⟨e, he, heS⟩` from `hcard`. Use `⟨fun i => g (e i), fun i => hgF _ (heS i), ?_⟩` and prove the remaining obligations. Introduce `i j hij`. Simplify using `only at hij`. Rewrite `hij` using `[hgν _ (heS i), hgν _ (heS j)]`.

Conclude with `he hij`. Distinguish the cases in `hfin : S.Finite`. Establish `key : ∀ n : ℕ, ∀ u, u ∈ F → u ≠ 0 → (hfin.toFinset.filter (fun s => ν u < s)).card = n → u ∈ Submodule.span C (g '' S)`. Introduce `n`. Proceed by induction on `n using Nat.strong_induction_on with`.

Consider the case `_ n ih`. Introduce `u huF hu0 hn`. Establish `huS : ν u ∈ S` using `⟨u, ⟨huF, hu0⟩, rfl⟩`. Take `⟨hgF', hg0⟩` from `hgF _ huS`. Take `⟨c, hc⟩` from `h3 u (g (ν u)) hu0 hg0 (hgν _ huS).symm`.

Establish `hgmem : g (ν u) ∈ Submodule.span C (g '' S)` using `Submodule.subset_span ⟨ν u, huS, rfl⟩`. Establish `hdec : u = (u - c • g (ν u)) + c • g (ν u)` using `(sub_add_cancel _ _).symm`. Rewrite using `[hdec]`. Use `Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ hgmem)` and prove the remaining obligations. Break down `hc with hc | hc` into its components or cases.

Rewrite using `[hc]`. Conclude with `Submodule.zero_mem _`. Distinguish the cases in `hw0 : u - c • g (ν u) = 0`. Rewrite using `[hw0]`. Conclude with `Submodule.zero_mem _`.

Establish `hwF : u - c • g (ν u) ∈ F` using `F.sub_mem huF (F.smul_mem c hgF')`. Use `ih _ ?_ _ hwF hw0 rfl` and prove the remaining obligations. Rewrite using `[← hn]`. Apply `Finset.card_lt_card` to reduce the goal to its premises. Rewrite using `[Finset.ssubset_iff_of_subset]`.

Use `⟨ν (u - c • g (ν u)), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.mem_filter, Set.Finite.mem_toFinset]`. Conclude with `⟨⟨_, ⟨hwF, hw0⟩, rfl⟩, hc⟩`. Rewrite using `[Finset.mem_filter]`. Conclude with `fun h => lt_irrefl _ h.2`.

Introduce `s hs`. Rewrite `hs`, the goal using `[Finset.mem_filter]`. Conclude with `⟨hs.1, lt_trans hc hs.2⟩`. Establish `hle : F ≤ Submodule.span C (g '' S)`. Introduce `u huF`.

Distinguish the cases in `hu0 : u = 0`. Rewrite using `[hu0]`. Conclude with `Submodule.zero_mem _`. Conclude with `key _ u huF hu0 rfl`. Establish `himg : g '' S = ((hfin.toFinset.image g : Finset V) : Set V)`.

Use extensionality with `x`. Simplify using the standard rewrite rules. Establish `hdim : Module.finrank C F ≤ hfin.toFinset.card`. Rewrite `hle` using `[himg]`. Combine the equalities or inequalities in the displayed calculation.

Set `emb : Fin (Module.finrank C F) ↪ hfin.toFinset` to `(Fin.castLEEmb hdim).trans hfin.toFinset.equivFin.symm.toEmbedding`. Use `⟨fun i => (emb i : Γ), ?_, ?_⟩` and prove the remaining obligations. Introduce `i j hij`. Conclude with `emb.injective (Subtype.ext hij)`. Introduce `i`.

Conclude with `(Set.Finite.mem_toFinset hfin).1 (emb i).2`. Set `emb : ℕ ↪ S` to `Set.Infinite.natEmbedding S hfin`. Use `⟨fun i => (emb i : Γ), ?_, fun i => (emb i).2⟩` and prove the remaining obligations. Introduce `i j hij`. Conclude with `Fin.ext (emb.injective (Subtype.ext hij))`.
-/
theorem finrank_le_card_values : ∀ (C V Γ : Type) [Field C] [AddCommGroup V] [Module C V] [LinearOrder Γ] (ν : V → Γ), (∀ (c : C) (u : V), c ≠ 0 → ν (c • u) = ν u) → (∀ u v : V, u ≠ 0 → v ≠ 0 → ν u < ν v → u + v ≠ 0 ∧ ν (u + v) = ν u) → (∀ u v : V, u ≠ 0 → v ≠ 0 → ν u = ν v → ∃ c : C, u - c • v = 0 ∨ ν u < ν (u - c • v)) → ∀ (F : Submodule C V) [Module.Finite C F], ∃ f : Fin (Module.finrank C F) → V, (∀ i, f i ∈ F ∧ f i ≠ 0) ∧ Function.Injective (fun i => ν (f i)) := by
  intro C V Γ _ _ _ _ ν _h1 _h2 h3 F _
  classical
  set S : Set Γ := ν '' {u | u ∈ F ∧ u ≠ 0} with hS
  have hg : ∀ s ∈ S, ∃ u, (u ∈ F ∧ u ≠ 0) ∧ ν u = s := fun s hs => hs
  choose! g hgF hgν using hg
  suffices hcard : ∃ e : Fin (Module.finrank C F) → Γ, Function.Injective e ∧ ∀ i, e i ∈ S by
    obtain ⟨e, he, heS⟩ := hcard
    refine ⟨fun i => g (e i), fun i => hgF _ (heS i), ?_⟩
    intro i j hij
    simp only at hij
    rw [hgν _ (heS i), hgν _ (heS j)] at hij
    exact he hij
  by_cases hfin : S.Finite
  · have key : ∀ n : ℕ, ∀ u, u ∈ F → u ≠ 0 →
        (hfin.toFinset.filter (fun s => ν u < s)).card = n →
        u ∈ Submodule.span C (g '' S) := by
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ih =>
      intro u huF hu0 hn
      have huS : ν u ∈ S := ⟨u, ⟨huF, hu0⟩, rfl⟩
      obtain ⟨hgF', hg0⟩ := hgF _ huS
      obtain ⟨c, hc⟩ := h3 u (g (ν u)) hu0 hg0 (hgν _ huS).symm
      have hgmem : g (ν u) ∈ Submodule.span C (g '' S) := Submodule.subset_span ⟨ν u, huS, rfl⟩
      have hdec : u = (u - c • g (ν u)) + c • g (ν u) := (sub_add_cancel _ _).symm
      rw [hdec]
      refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ hgmem)
      rcases hc with hc | hc
      · rw [hc]; exact Submodule.zero_mem _
      · by_cases hw0 : u - c • g (ν u) = 0
        · rw [hw0]; exact Submodule.zero_mem _
        · have hwF : u - c • g (ν u) ∈ F := F.sub_mem huF (F.smul_mem c hgF')
          refine ih _ ?_ _ hwF hw0 rfl
          rw [← hn]
          apply Finset.card_lt_card
          rw [Finset.ssubset_iff_of_subset]
          · refine ⟨ν (u - c • g (ν u)), ?_, ?_⟩
            · rw [Finset.mem_filter, Set.Finite.mem_toFinset]
              exact ⟨⟨_, ⟨hwF, hw0⟩, rfl⟩, hc⟩
            · rw [Finset.mem_filter]
              exact fun h => lt_irrefl _ h.2
          · intro s hs
            rw [Finset.mem_filter] at hs ⊢
            exact ⟨hs.1, lt_trans hc hs.2⟩
    have hle : F ≤ Submodule.span C (g '' S) := by
      intro u huF
      by_cases hu0 : u = 0
      · rw [hu0]; exact Submodule.zero_mem _
      · exact key _ u huF hu0 rfl
    have himg : g '' S = ((hfin.toFinset.image g : Finset V) : Set V) := by
      ext x; simp
    have hdim : Module.finrank C F ≤ hfin.toFinset.card := by
      rw [himg] at hle
      calc Module.finrank C F ≤ Module.finrank C (Submodule.span C ((hfin.toFinset.image g : Finset V) : Set V)) :=
            Submodule.finrank_mono hle
        _ ≤ (hfin.toFinset.image g).card := finrank_span_finset_le_card _
        _ ≤ hfin.toFinset.card := Finset.card_image_le
    let emb : Fin (Module.finrank C F) ↪ hfin.toFinset :=
      (Fin.castLEEmb hdim).trans hfin.toFinset.equivFin.symm.toEmbedding
    refine ⟨fun i => (emb i : Γ), ?_, ?_⟩
    · intro i j hij
      exact emb.injective (Subtype.ext hij)
    · intro i
      exact (Set.Finite.mem_toFinset hfin).1 (emb i).2
  · let emb : ℕ ↪ S := Set.Infinite.natEmbedding S hfin
    refine ⟨fun i => (emb i : Γ), ?_, fun i => (emb i).2⟩
    intro i j hij
    exact Fin.ext (emb.injective (Subtype.ext hij))

end GlobalTheory
