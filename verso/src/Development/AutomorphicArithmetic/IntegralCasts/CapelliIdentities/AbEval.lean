import Mathlib

/- English proof (translation)
Introduce `k X inst _ r`. Proceed by induction on `r with`. Consider the case `zero`. Introduce `H hfin hr`. Establish `hH : H = ⊥` using `Submodule.finrank_eq_zero.mp (Nat.le_zero.mp hr)`.

Use `⟨fun _ => default, fun φ hφ _ => ?_⟩` and prove the remaining obligations. Rewrite `hφ` using `[hH]`. Conclude with `(Submodule.mem_bot k).mp hφ`. Consider the case `succ n ih`. Introduce `H hfin hr`.

Distinguish the cases in `h : ∀ φ ∈ H, φ = 0`. Conclude with `⟨fun _ => default, fun φ hφ _ => h φ hφ⟩`. Establish `h' : ∃ ψ ∈ H, ∃ x, ψ x ≠ 0`. Assume the negation of the conclusion as `hc`. Apply `h` to reduce the goal to its premises.

Introduce `φ hφ`. Use function extensionality and compare the values at `x`. Assume the negation of the conclusion as `hx`. Conclude with `hc ⟨φ, hφ, x, hx⟩`. Take `⟨ψ, hψ, x, hx⟩` from `h'`.

Set `K : Submodule k (X → k)` to `H ⊓ LinearMap.ker (LinearMap.proj (R := k) (φ := fun _ : X => k) x)`. Establish `hle : K ≤ H` using `inf_le_left`. Establish `hlt : K < H`. Use `lt_of_le_of_ne hle ?_` and prove the remaining obligations. Introduce `he`.

Establish `hK : ψ ∈ K` using `he ▸ hψ`. Conclude with `hx hK.2`. Establish `hKfin : Module.Finite k ↥K` using `Submodule.finiteDimensional_of_le hle`. Establish `hrank : Module.finrank k ↥K < Module.finrank k ↥H` using `Submodule.finrank_lt_finrank_of_lt hlt`. Take `⟨t, ht⟩` from `ih K hKfin (by omega)`.

Use `⟨Fin.cons x t, fun φ hφ h0 => ?_⟩` and prove the remaining obligations. Conclude with `ht φ ⟨hφ, h0 0⟩ (fun a => h0 a.succ)`.
-/
theorem UpperTheory.Reformulated.B.Ra1.ab_eval :
    ∀ {k X : Type} [inst : Field k] [Inhabited X] (r : ℕ)
    (H : Submodule k (X → k)),
    Module.Finite k ↥H →
      Module.finrank k ↥H ≤ r → ∃ (t : Fin r → X), ∀ φ ∈ H, (∀ (a : Fin r), φ (t a) = (0 : k)) → φ = (0 : X → k) := by
  intro k X inst _ r
  induction r with
  | zero =>
    intro H hfin hr
    have hH : H = ⊥ := Submodule.finrank_eq_zero.mp (Nat.le_zero.mp hr)
    refine ⟨fun _ => default, fun φ hφ _ => ?_⟩
    rw [hH] at hφ
    exact (Submodule.mem_bot k).mp hφ
  | succ n ih =>
    intro H hfin hr
    by_cases h : ∀ φ ∈ H, φ = 0
    · exact ⟨fun _ => default, fun φ hφ _ => h φ hφ⟩
    · have h' : ∃ ψ ∈ H, ∃ x, ψ x ≠ 0 := by
        by_contra hc
        apply h
        intro φ hφ
        funext x
        by_contra hx
        exact hc ⟨φ, hφ, x, hx⟩
      obtain ⟨ψ, hψ, x, hx⟩ := h'
      let K : Submodule k (X → k) :=
        H ⊓ LinearMap.ker (LinearMap.proj (R := k) (φ := fun _ : X => k) x)
      have hle : K ≤ H := inf_le_left
      have hlt : K < H := by
        refine lt_of_le_of_ne hle ?_
        intro he
        have hK : ψ ∈ K := he ▸ hψ
        exact hx hK.2
      have hKfin : Module.Finite k ↥K := Submodule.finiteDimensional_of_le hle
      have hrank : Module.finrank k ↥K < Module.finrank k ↥H :=
        Submodule.finrank_lt_finrank_of_lt hlt
      obtain ⟨t, ht⟩ := ih K hKfin (by omega)
      refine ⟨Fin.cons x t, fun φ hφ h0 => ?_⟩
      exact ht φ ⟨hφ, h0 0⟩ (fun a => h0 a.succ)
