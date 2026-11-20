import Mathlib
open Polynomial Matrix

/- English proof (translation)
Introduce `K G V _ _ _ _ _ ρ N hN hirr W hW`. Establish `hmul : ∀ (a b : G) (v : V), ρ a (ρ b v) = ρ (a * b) v`. Introduce `a b v`. Rewrite using `[map_mul]`. Both sides reduce to the same expression.

Take `⟨W', ⟨hW's, hW'd⟩, hmax⟩` from `exists_maximal_of_wellFoundedGT (fun U : Submodule K V => (∀ g ∈ N, ∀ v ∈ U, ρ g v ∈ U) ∧ Disjoint W U) ⟨⊥, by intro g _ v hv; rw [Submodule.mem_bot] at hv ⊢; rw [hv, map_zero], disjoint_bot_right⟩`. Use `⟨W', hW's, hW'd, ?_⟩` and prove the remaining obligations. Rewrite using `[codisjoint_iff]`. Distinguish the cases in `htriv : (⊤ : Submodule K V) = ⊥`. Conclude with `top_le_iff.mp (htriv ▸ bot_le)`.

Take `⟨S, ⟨hSs, hS0⟩, hmin⟩` from `exists_minimal_of_wellFoundedLT (fun U : Submodule K V => (∀ g ∈ N, ∀ v ∈ U, ρ g v ∈ U) ∧ U ≠ ⊥) ⟨⊤, fun _ _ _ _ => Submodule.mem_top, htriv⟩`. Establish `hsup : ∀ n ∈ N, ∀ v ∈ W ⊔ W', ρ n v ∈ W ⊔ W'`. Introduce `n hn v hv`. Take `⟨a, ha, b, hb, rfl⟩` from `Submodule.mem_sup.mp hv`. Rewrite using `[map_add]`.

Conclude with `Submodule.add_mem_sup (hW n hn a ha) (hW's n hn b hb)`. Establish `key : ∀ g : G, ∀ s ∈ S, ρ g s ∈ W ⊔ W'`. Introduce `g`. Distinguish the cases in `hA : S ⊓ (W ⊔ W').comap (ρ g) = ⊥`. Establish `hle : W' ⊔ S.map (ρ g) ≤ W'`.

Use `hmax ⟨?_, ?_⟩ le_sup_left` and prove the remaining obligations. Introduce `n hn v hv`. Take `⟨a, ha, b, hb, rfl⟩` from `Submodule.mem_sup.mp hv`. Take `⟨s, hs, rfl⟩` from `Submodule.mem_map.mp hb`. Rewrite using `[map_add]`.

Use `Submodule.add_mem_sup (hW's n hn a ha) ?_` and prove the remaining obligations. Use `Submodule.mem_map.mpr ⟨ρ (g⁻¹ * n * g) s, hSs _ (hN.conj_mem' n hn g) s hs, ?_⟩` and prove the remaining obligations. Rewrite using `[hmul, hmul]`. Use `congr 2`. Use `group`.

Rewrite using `[Submodule.disjoint_def]`. Introduce `v hvW hv`. Take `⟨a, ha, b, hb, rfl⟩` from `Submodule.mem_sup.mp hv`. Take `⟨s, hs, rfl⟩` from `Submodule.mem_map.mp hb`. Establish `h1 : ρ g s ∈ W ⊔ W'`.

Use `(W ⊔ W').sub_mem (Submodule.mem_sup_left hvW) (Submodule.mem_sup_right ha)` as an intermediate fact. Simplify using `using this`. Establish `h2 : s ∈ S ⊓ (W ⊔ W').comap (ρ g)` using `⟨hs, h1⟩`. Rewrite `h2` using `[hA, Submodule.mem_bot]`. Substitute `h2` using the available equality.

Rewrite `hvW`, the goal using `[map_zero, add_zero]`. Conclude with `Submodule.disjoint_def.mp hW'd a hvW ha`. Introduce `s hs`. Conclude with `Submodule.mem_sup_right (hle (Submodule.mem_sup_right (Submodule.mem_map_of_mem hs)))`. Establish `hle : S ≤ S ⊓ (W ⊔ W').comap (ρ g)`.

Use `hmin ⟨?_, hA⟩ inf_le_left` and prove the remaining obligations. Introduce `n hn v hv`. Use `⟨hSs n hn v hv.1, ?_⟩` and prove the remaining obligations. Establish `h1 : ρ g v ∈ W ⊔ W'` using `hv.2`. Establish `h2` using `hsup _ (hN.conj_mem n hn g) _ h1`.

Use `show ρ g (ρ n v) ∈ W ⊔ W'`. Rewrite `h2`, the goal using `[hmul]`. Establish `: g * n * g⁻¹ * g = g * n` using `by group`. Rewrite `h2` using `[this]`. Then use the resulting hypothesis. Introduce `s hs`.

Conclude with `(hle hs).2`. Establish `hU` using `hirr (⨅ g : G, (W ⊔ W').comap (ρ g)) (by`. Introduce `g v hv`. Simplify using `only [Submodule.mem_iInf, Submodule.mem_comap] at hv ⊢`. Introduce `h`.

Rewrite using `[hmul]`. Conclude with `hv _)`. Break down `hU with hU | hU` into its components or cases. It suffices to derive a contradiction. Apply `hS0` to reduce the goal to its premises.

Rewrite using `[eq_bot_iff, ← hU]`. Introduce `s hs`. Simplify using `only [Submodule.mem_iInf, Submodule.mem_comap]`. Conclude with `fun g => key g s hs`. Rewrite using `[eq_top_iff]`.

Introduce `v _`. Establish `hv : v ∈ (⨅ g : G, (W ⊔ W').comap (ρ g))` using `hU ▸ Submodule.mem_top`. Simplify using `only [Submodule.mem_iInf, Submodule.mem_comap] at hv`. Simplify using `using hv 1`.
-/
theorem UpperTheory.V.Pr.T.cliffordSS :
    ∀ {K G V : Type} [Field K] [Group G] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
      (ρ : Representation K G V) (N : Subgroup G) [N.Normal],
      (∀ W : Submodule K V, (∀ g, ∀ v ∈ W, ρ g v ∈ W) → W = ⊥ ∨ W = ⊤) →
      ∀ W : Submodule K V, (∀ g ∈ N, ∀ v ∈ W, ρ g v ∈ W) →
        ∃ W' : Submodule K V, (∀ g ∈ N, ∀ v ∈ W', ρ g v ∈ W') ∧ IsCompl W W' := by
  intro K G V _ _ _ _ _ ρ N hN hirr W hW
  have hmul : ∀ (a b : G) (v : V), ρ a (ρ b v) = ρ (a * b) v := by
    intro a b v; rw [map_mul]; rfl
  obtain ⟨W', ⟨hW's, hW'd⟩, hmax⟩ := exists_maximal_of_wellFoundedGT
    (fun U : Submodule K V => (∀ g ∈ N, ∀ v ∈ U, ρ g v ∈ U) ∧ Disjoint W U)
    ⟨⊥, by intro g _ v hv; rw [Submodule.mem_bot] at hv ⊢; rw [hv, map_zero], disjoint_bot_right⟩
  refine ⟨W', hW's, hW'd, ?_⟩
  rw [codisjoint_iff]
  by_cases htriv : (⊤ : Submodule K V) = ⊥
  · exact top_le_iff.mp (htriv ▸ bot_le)
  obtain ⟨S, ⟨hSs, hS0⟩, hmin⟩ := exists_minimal_of_wellFoundedLT
    (fun U : Submodule K V => (∀ g ∈ N, ∀ v ∈ U, ρ g v ∈ U) ∧ U ≠ ⊥)
    ⟨⊤, fun _ _ _ _ => Submodule.mem_top, htriv⟩
  have hsup : ∀ n ∈ N, ∀ v ∈ W ⊔ W', ρ n v ∈ W ⊔ W' := by
    intro n hn v hv
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
    rw [map_add]
    exact Submodule.add_mem_sup (hW n hn a ha) (hW's n hn b hb)
  have key : ∀ g : G, ∀ s ∈ S, ρ g s ∈ W ⊔ W' := by
    intro g
    by_cases hA : S ⊓ (W ⊔ W').comap (ρ g) = ⊥
    · have hle : W' ⊔ S.map (ρ g) ≤ W' := by
        refine hmax ⟨?_, ?_⟩ le_sup_left
        · intro n hn v hv
          obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
          obtain ⟨s, hs, rfl⟩ := Submodule.mem_map.mp hb
          rw [map_add]
          refine Submodule.add_mem_sup (hW's n hn a ha) ?_
          refine Submodule.mem_map.mpr ⟨ρ (g⁻¹ * n * g) s, hSs _ (hN.conj_mem' n hn g) s hs, ?_⟩
          rw [hmul, hmul]; congr 2; group
        · rw [Submodule.disjoint_def]
          intro v hvW hv
          obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
          obtain ⟨s, hs, rfl⟩ := Submodule.mem_map.mp hb
          have h1 : ρ g s ∈ W ⊔ W' := by
            have := (W ⊔ W').sub_mem (Submodule.mem_sup_left hvW) (Submodule.mem_sup_right ha)
            simpa using this
          have h2 : s ∈ S ⊓ (W ⊔ W').comap (ρ g) := ⟨hs, h1⟩
          rw [hA, Submodule.mem_bot] at h2
          subst h2
          rw [map_zero, add_zero] at hvW ⊢
          exact Submodule.disjoint_def.mp hW'd a hvW ha
      intro s hs
      exact Submodule.mem_sup_right (hle (Submodule.mem_sup_right (Submodule.mem_map_of_mem hs)))
    · have hle : S ≤ S ⊓ (W ⊔ W').comap (ρ g) := by
        refine hmin ⟨?_, hA⟩ inf_le_left
        intro n hn v hv
        refine ⟨hSs n hn v hv.1, ?_⟩
        have h1 : ρ g v ∈ W ⊔ W' := hv.2
        have h2 := hsup _ (hN.conj_mem n hn g) _ h1
        show ρ g (ρ n v) ∈ W ⊔ W'
        rw [hmul] at h2 ⊢
        have : g * n * g⁻¹ * g = g * n := by group
        rwa [this] at h2
      intro s hs
      exact (hle hs).2
  have hU := hirr (⨅ g : G, (W ⊔ W').comap (ρ g)) (by
    intro g v hv
    simp only [Submodule.mem_iInf, Submodule.mem_comap] at hv ⊢
    intro h
    rw [hmul]; exact hv _)
  rcases hU with hU | hU
  · exfalso
    apply hS0
    rw [eq_bot_iff, ← hU]
    intro s hs
    simp only [Submodule.mem_iInf, Submodule.mem_comap]
    exact fun g => key g s hs
  · rw [eq_top_iff]
    intro v _
    have hv : v ∈ (⨅ g : G, (W ⊔ W').comap (ρ g)) := hU ▸ Submodule.mem_top
    simp only [Submodule.mem_iInf, Submodule.mem_comap] at hv
    simpa using hv 1
