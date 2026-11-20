import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemRiemannRochSpaceIffRegularAtEverywhere

open Matrix Classical PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.GLFirstBasisOrbit

namespace GlobalTheory.CompanionTheory.GapOpCount

/- English proof (translation)
Introduce `k _ _ n j M hM hdim`. Set `E` to `dotProductEquiv k (Fin (n + 1))`. Establish `hE : ∀ a x : Fin (n + 1) → k, E a x = a ⬝ᵥ x` using `fun a x => by`. Simplify using `[E, dotProductEquiv]`. Set `W : Submodule k (Fin (n + 1) → k)` to `M ⊔ Submodule.span k {e0 k n}`.

Set `T : Submodule k (Fin (n + 1) → k)` to `W.dualAnnihilator.comap E.toLinearMap`. Establish `hT : ∀ a, a ∈ T ↔ a ⬝ᵥ e0 k n = 0 ∧ ∀ x ∈ M, a ⬝ᵥ x = 0`. Introduce `a`. Simplify using `only [T, W, Submodule.mem_comap, Submodule.mem_dualAnnihilator, LinearEquiv.coe_coe, hE]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Conclude with `⟨h _ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)), fun x hx => h x (Submodule.mem_sup_left hx)⟩`. Introduce and unpack `⟨h0, h1⟩ w hw`. Take `⟨x, hx, y, hy, rfl⟩` from `Submodule.mem_sup.1 hw`. Take `⟨c, rfl⟩` from `Submodule.mem_span_singleton.1 hy`.

Rewrite using `[dotProduct_add, dotProduct_smul, h0, h1 x hx, smul_zero, add_zero]`. Establish `hfr : Module.finrank k T = j`. Establish `hmap : T.map E.toLinearMap = W.dualAnnihilator` using `Submodule.map_comap_eq_of_surjective E.surjective _`. Establish `h1 : Module.finrank k T = Module.finrank k W.dualAnnihilator`. Rewrite using `[← hmap]`.

Conclude with `(LinearEquiv.finrank_map_eq E T).symm`. Establish `h2` using `Subspace.finrank_add_finrank_dualAnnihilator_eq W`. Establish `h3 : Module.finrank k W = Module.finrank k M + 1` using `Submodule.finrank_sup_span_singleton hM`. Establish `h4 : Module.finrank k (Fin (n + 1) → k) = n + 1` using `by simp`. Use linear arithmetic over natural numbers and integers.

Take `⟨f, hf0, hfM⟩` from `Submodule.exists_le_ker_of_notMem hM`. Take `⟨b, rfl⟩` from `E.surjective f`. Establish `hb0 : b ⬝ᵥ e0 k n ≠ 0` using `by rwa [← hE]`. Establish `hbM : ∀ x ∈ M, b ⬝ᵥ x = 0` using `fun x hx => by`. Rewrite using `[← hE]`.

Conclude with `hfM hx`. Set `a0 : Fin (n + 1) → k` to `(b ⬝ᵥ e0 k n)⁻¹ • b`. Establish `ha0 : a0 ⬝ᵥ e0 k n = 1`. Simplify using `only [a0, smul_dotProduct, smul_eq_mul]`. Conclude with `inv_mul_cancel₀ hb0`.

Establish `ha0M : ∀ x ∈ M, a0 ⬝ᵥ x = 0` using `fun x hx => by`. Simplify using `only [a0, smul_dotProduct, hbM x hx, smul_zero]`. Establish `hcard : (Finset.univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ e0 k n = 1 ∧ ∀ x ∈ M, a ⬝ᵥ x = 0)).card = (Finset.univ : Finset T).card`. Use `Finset.card_bij' (fun a ha => ⟨a - a0, ?_⟩) (fun t _ => t.1 + a0) ?_ ?_ ?_ ?_` and prove the remaining obligations. Take `⟨-, h1, h2⟩` from `Finset.mem_filter.1 ha`.

Use `(hT _).2 ⟨?_, fun x hx => ?_⟩` and prove the remaining obligations. Rewrite using `[sub_dotProduct, h1, ha0, sub_self]`. Rewrite using `[sub_dotProduct, h2 x hx, ha0M x hx, sub_self]`. Introduce `a ha`. Conclude with `Finset.mem_univ _`.

Introduce `t _`. Take `⟨h1, h2⟩` from `(hT t.1).1 t.2`. Use `Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_, fun x hx => ?_⟩` and prove the remaining obligations. Rewrite using `[add_dotProduct, h1, ha0, zero_add]`. Rewrite using `[add_dotProduct, h2 x hx, ha0M x hx, add_zero]`.

Introduce `a ha`. Simplify using the standard rewrite rules. Introduce `t _ ext1`. Simplify using the standard rewrite rules. Rewrite using `[hcard, Finset.card_univ, Module.card_eq_pow_finrank (K := k) (V := T), hfr]`.
-/
theorem card_forms_vanishing_missing_line : ∀ (k : Type) [Field k] [Fintype k] (n j : ℕ) (M : Submodule k (Fin (n + 1) → k)), e0 k n ∉ M →
    Module.finrank k M + (j + 1) = n + 1 →
    (Finset.univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ e0 k n = 1 ∧ ∀ x ∈ M, a ⬝ᵥ x = 0)).card = Fintype.card k ^ j := by
  intro k _ _ n j M hM hdim
  let E := dotProductEquiv k (Fin (n + 1))
  have hE : ∀ a x : Fin (n + 1) → k, E a x = a ⬝ᵥ x := fun a x => by
    simp [E, dotProductEquiv]
  let W : Submodule k (Fin (n + 1) → k) := M ⊔ Submodule.span k {e0 k n}
  let T : Submodule k (Fin (n + 1) → k) := W.dualAnnihilator.comap E.toLinearMap
  have hT : ∀ a, a ∈ T ↔ a ⬝ᵥ e0 k n = 0 ∧ ∀ x ∈ M, a ⬝ᵥ x = 0 := by
    intro a
    simp only [T, W, Submodule.mem_comap, Submodule.mem_dualAnnihilator, LinearEquiv.coe_coe, hE]
    constructor
    · intro h
      exact ⟨h _ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)),
        fun x hx => h x (Submodule.mem_sup_left hx)⟩
    · rintro ⟨h0, h1⟩ w hw
      obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hw
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
      rw [dotProduct_add, dotProduct_smul, h0, h1 x hx, smul_zero, add_zero]
  have hfr : Module.finrank k T = j := by
    have hmap : T.map E.toLinearMap = W.dualAnnihilator :=
      Submodule.map_comap_eq_of_surjective E.surjective _
    have h1 : Module.finrank k T = Module.finrank k W.dualAnnihilator := by
      rw [← hmap]
      exact (LinearEquiv.finrank_map_eq E T).symm
    have h2 := Subspace.finrank_add_finrank_dualAnnihilator_eq W
    have h3 : Module.finrank k W = Module.finrank k M + 1 := Submodule.finrank_sup_span_singleton hM
    have h4 : Module.finrank k (Fin (n + 1) → k) = n + 1 := by simp
    omega
  obtain ⟨f, hf0, hfM⟩ := Submodule.exists_le_ker_of_notMem hM
  obtain ⟨b, rfl⟩ := E.surjective f
  have hb0 : b ⬝ᵥ e0 k n ≠ 0 := by rwa [← hE]
  have hbM : ∀ x ∈ M, b ⬝ᵥ x = 0 := fun x hx => by
    rw [← hE]
    exact hfM hx
  let a0 : Fin (n + 1) → k := (b ⬝ᵥ e0 k n)⁻¹ • b
  have ha0 : a0 ⬝ᵥ e0 k n = 1 := by
    simp only [a0, smul_dotProduct, smul_eq_mul]
    exact inv_mul_cancel₀ hb0
  have ha0M : ∀ x ∈ M, a0 ⬝ᵥ x = 0 := fun x hx => by
    simp only [a0, smul_dotProduct, hbM x hx, smul_zero]
  have hcard : (Finset.univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ e0 k n = 1 ∧ ∀ x ∈ M, a ⬝ᵥ x = 0)).card
      = (Finset.univ : Finset T).card := by
    refine Finset.card_bij' (fun a ha => ⟨a - a0, ?_⟩) (fun t _ => t.1 + a0) ?_ ?_ ?_ ?_
    · obtain ⟨-, h1, h2⟩ := Finset.mem_filter.1 ha
      refine (hT _).2 ⟨?_, fun x hx => ?_⟩
      · rw [sub_dotProduct, h1, ha0, sub_self]
      · rw [sub_dotProduct, h2 x hx, ha0M x hx, sub_self]
    · intro a ha
      exact Finset.mem_univ _
    · intro t _
      obtain ⟨h1, h2⟩ := (hT t.1).1 t.2
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_, fun x hx => ?_⟩
      · rw [add_dotProduct, h1, ha0, zero_add]
      · rw [add_dotProduct, h2 x hx, ha0M x hx, add_zero]
    · intro a ha
      simp
    · intro t _
      ext1
      simp
  rw [hcard, Finset.card_univ, Module.card_eq_pow_finrank (K := k) (V := T), hfr]

end GlobalTheory.CompanionTheory.GapOpCount
