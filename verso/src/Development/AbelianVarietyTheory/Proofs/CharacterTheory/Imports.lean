import Mathlib

namespace GlobalTheory.UnimodularLatticeLemma

/- English proof (translation)
Set `S : Set (Submodule L V)` to `{W | W ≠ ⊥ ∧ ∀ b, ∀ x ∈ W, f b x ∈ W}`. Establish `hS : (⊤ : Submodule L V) ∈ S` using `⟨top_ne_bot, fun _ _ _ => Submodule.mem_top⟩`. Take `⟨W, hW, hmin⟩` from `(wellFounded_lt (α := Submodule L V)).has_min S ⟨⊤, hS⟩`. Establish `key : ∀ b, ∃ μ : L, ∀ x ∈ W, f b x = μ • x`. Introduce `b`.

Establish `hWb : ∀ x ∈ W, f b x ∈ W` using `hW.2 b`. Use `haveI : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW.1`. Take `⟨μ, hμ⟩` from `Module.End.exists_eigenvalue ((f b).restrict hWb)`. Take `⟨w, hw⟩` from `hμ.exists_hasEigenvector`. Establish `hw1 : (f b).restrict hWb w = μ • w` using `hw.apply_eq_smul`.

Establish `hw0 : w ≠ 0` using `hw.2`. Set `W' : Submodule L V` to `W ⊓ LinearMap.ker (f b - μ • 1)`. Establish `hmem : ∀ x, x ∈ W' ↔ x ∈ W ∧ f b x = μ • x`. Introduce `x`. Simplify using `only [W', Submodule.mem_inf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero]`.

Establish `hW'S : W' ∈ S`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `h`. Apply `hw0` to reduce the goal to its premises. Establish `: (w : V) ∈ W'`.

Rewrite using `[hmem]`. Use `⟨w.2, ?_⟩` and prove the remaining obligations. Use `congrArg Subtype.val hw1` as an intermediate fact. Simplify using `using this`. Rewrite `this` using `[h, Submodule.mem_bot]`.

Conclude with `Subtype.ext this`. Introduce `c x hx`. Rewrite `hx`, the goal using `[hmem]`. Use `⟨hW.2 c x hx.1, ?_⟩` and prove the remaining obligations. Establish `h1 : f b (f c x) = (f b * f c) x` using `rfl`.

Rewrite using `[h1, hc b c, Module.End.mul_apply, hx.2, map_smul]`. Establish `hle : W' ≤ W` using `inf_le_left`. Establish `heq : W' = W`. Assume the negation of the conclusion as `hne`. Conclude with `hmin W' hW'S (lt_of_le_of_ne hle hne)`.

Use `⟨μ, fun x hx => ?_⟩` and prove the remaining obligations. Establish `: x ∈ W'` using `heq ▸ hx`. Conclude with `((hmem x).1 this).2`. Take `⟨v, hvW, hv0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hW.1`. Use `⟨v, hv0, fun b => ?_⟩` and prove the remaining obligations.

Take `⟨μ, hμ⟩` from `key b`. Conclude with `⟨μ, hμ v hvW⟩`.
-/
theorem main {L : Type} [Field L] [IsAlgClosed L] {ι V : Type} [AddCommGroup V] [Module L V]
    [FiniteDimensional L V] [Nontrivial V] (f : ι → Module.End L V)
    (hc : ∀ (a b : ι), f a * f b = f b * f a) :
    ∃ (v : V), v ≠ (0 : V) ∧ ∀ (b : ι), ∃ (μ : L), (f b : V → V) v = μ • v := by
  classical
  let S : Set (Submodule L V) := {W | W ≠ ⊥ ∧ ∀ b, ∀ x ∈ W, f b x ∈ W}
  have hS : (⊤ : Submodule L V) ∈ S := ⟨top_ne_bot, fun _ _ _ => Submodule.mem_top⟩
  obtain ⟨W, hW, hmin⟩ := (wellFounded_lt (α := Submodule L V)).has_min S ⟨⊤, hS⟩
  have key : ∀ b, ∃ μ : L, ∀ x ∈ W, f b x = μ • x := by
    intro b
    have hWb : ∀ x ∈ W, f b x ∈ W := hW.2 b
    haveI : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW.1
    obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue ((f b).restrict hWb)
    obtain ⟨w, hw⟩ := hμ.exists_hasEigenvector
    have hw1 : (f b).restrict hWb w = μ • w := hw.apply_eq_smul
    have hw0 : w ≠ 0 := hw.2
    let W' : Submodule L V := W ⊓ LinearMap.ker (f b - μ • 1)
    have hmem : ∀ x, x ∈ W' ↔ x ∈ W ∧ f b x = μ • x := by
      intro x
      simp only [W', Submodule.mem_inf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero]
    have hW'S : W' ∈ S := by
      refine ⟨?_, ?_⟩
      · intro h
        apply hw0
        have : (w : V) ∈ W' := by
          rw [hmem]
          refine ⟨w.2, ?_⟩
          have := congrArg Subtype.val hw1
          simpa using this
        rw [h, Submodule.mem_bot] at this
        exact Subtype.ext this
      · intro c x hx
        rw [hmem] at hx ⊢
        refine ⟨hW.2 c x hx.1, ?_⟩
        have h1 : f b (f c x) = (f b * f c) x := rfl
        rw [h1, hc b c, Module.End.mul_apply, hx.2, map_smul]
    have hle : W' ≤ W := inf_le_left
    have heq : W' = W := by
      by_contra hne
      exact hmin W' hW'S (lt_of_le_of_ne hle hne)
    refine ⟨μ, fun x hx => ?_⟩
    have : x ∈ W' := heq ▸ hx
    exact ((hmem x).1 this).2
  obtain ⟨v, hvW, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW.1
  refine ⟨v, hv0, fun b => ?_⟩
  obtain ⟨μ, hμ⟩ := key b
  exact ⟨μ, hμ v hvW⟩

end GlobalTheory.UnimodularLatticeLemma
