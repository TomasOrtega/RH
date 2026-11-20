import Mathlib

namespace GlobalTheory

/- English proof (translation)
Establish `key : ∀ (W : Submodule L V), (∀ g, ∀ x ∈ W, ρ g x ∈ W) → W ≠ ⊥ → W = ⊤`. Introduce `W hW hne`. Set `S : Subrepresentation ρ` to `⟨W, fun g x hx => hW g x hx⟩`. Break down `hρ.eq_bot_or_eq_top S with h | h` into its components or cases. Conclude with `absurd (congrArg Subrepresentation.toSubmodule h) hne`.

Conclude with `congrArg Subrepresentation.toSubmodule h`. Use `⟨fun e he hee hc => ?_, fun lam v hv hl g => ?_⟩` and prove the remaining obligations. Establish `h : LinearMap.range e = ⊤`. Use `key _ ?_ ?_` and prove the remaining obligations. Introduce and unpack `g _ ⟨u, rfl⟩`.

Conclude with `⟨ρ g u, (congrArg (fun f : Module.End L V => f u) (hc g)).symm⟩`. Introduce `h`. Conclude with `he (LinearMap.range_eq_bot.mp h)`. Use extensionality with `w`. Take `⟨u, rfl⟩` from `LinearMap.range_eq_top.mp h w`.

Conclude with `congrArg (fun f : Module.End L V => f u) hee`. Establish `h : Submodule.span L {v} = ⊤`. Use `key _ ?_ ?_` and prove the remaining obligations. Introduce `g x hx`. Take `⟨c, rfl⟩` from `Submodule.mem_span_singleton.mp hx`.

Rewrite using `[map_smul, hl]`. Conclude with `Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v))`. Simplify using `using hv`. Establish `hfin : Module.finrank L V = 1`. Rewrite using `[← finrank_top, ← h]`.

Conclude with `finrank_span_singleton hv`. Establish `hg : ρ g = (lam g : L) • LinearMap.id`. Use extensionality with `x`. Establish `hx : x ∈ Submodule.span L {v}` using `h ▸ Submodule.mem_top`. Take `⟨c, rfl⟩` from `Submodule.mem_span_singleton.mp hx`.

Simplify using `[hl, smul_comm c]`. Simplify using `[Representation.character, hg, hfin]`.
-/
theorem irreducible_idempotent_eq_one_and_character_eq_weight
    (L : Type) [Field L] (G : Type) [Group G] (V : Type) [AddCommGroup V] [Module L V]
    [FiniteDimensional L V] (ρ : Representation L G V) (hρ : ρ.IsIrreducible) :
    (∀ e : Module.End L V, e ≠ 0 → e * e = e → (∀ g, ρ g * e = e * ρ g) → e = 1) ∧
    (∀ (lam : G →* Lˣ) (v : V), v ≠ 0 → (∀ g, ρ g v = (lam g : L) • v) →
      ∀ g, ρ.character g = (lam g : L)) := by
  have key : ∀ (W : Submodule L V), (∀ g, ∀ x ∈ W, ρ g x ∈ W) → W ≠ ⊥ → W = ⊤ := by
    intro W hW hne
    let S : Subrepresentation ρ := ⟨W, fun g x hx => hW g x hx⟩
    rcases hρ.eq_bot_or_eq_top S with h | h
    · exact absurd (congrArg Subrepresentation.toSubmodule h) hne
    · exact congrArg Subrepresentation.toSubmodule h
  refine ⟨fun e he hee hc => ?_, fun lam v hv hl g => ?_⟩
  · have h : LinearMap.range e = ⊤ := by
      refine key _ ?_ ?_
      · rintro g _ ⟨u, rfl⟩
        exact ⟨ρ g u, (congrArg (fun f : Module.End L V => f u) (hc g)).symm⟩
      · intro h
        exact he (LinearMap.range_eq_bot.mp h)
    ext w
    obtain ⟨u, rfl⟩ := LinearMap.range_eq_top.mp h w
    exact congrArg (fun f : Module.End L V => f u) hee
  · have h : Submodule.span L {v} = ⊤ := by
      refine key _ ?_ ?_
      · intro g x hx
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
        rw [map_smul, hl]
        exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v))
      · simpa using hv
    have hfin : Module.finrank L V = 1 := by
      rw [← finrank_top, ← h]
      exact finrank_span_singleton hv
    have hg : ρ g = (lam g : L) • LinearMap.id := by
      ext x
      have hx : x ∈ Submodule.span L {v} := h ▸ Submodule.mem_top
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
      simp [hl, smul_comm c]
    simp [Representation.character, hg, hfin]

end GlobalTheory
