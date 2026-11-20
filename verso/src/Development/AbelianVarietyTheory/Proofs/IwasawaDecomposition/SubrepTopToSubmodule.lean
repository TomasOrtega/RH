import Mathlib

namespace GlobalTheory.SubrepTopBot

open Representation

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem subrep_bot_toSubmodule {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) : (⊥ : Subrepresentation ρ).toSubmodule = ⊥ := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem subrep_top_toSubmodule {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) : (⊤ : Subrepresentation ρ).toSubmodule = ⊤ := rfl

/- English proof (translation)
Introduce `G _ V _ _ ρ`. Establish `hbot` using `subrep_bot_toSubmodule ρ`. Establish `htop` using `subrep_top_toSubmodule ρ`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `hne : (⊥ : Subrepresentation ρ) ≠ ⊤` using `bot_ne_top`. Rewrite using `[← Submodule.nontrivial_iff ℂ]`. Use `⟨⟨⊥, ⊤, fun e => hne ?_⟩⟩` and prove the remaining obligations. Apply `Subrepresentation.toSubmodule_injective` to reduce the goal to its premises.

Rewrite using `[hbot, htop]`. Conclude with `e`. Introduce `U hU`. Set `S : Subrepresentation ρ` to `⟨U, fun g v hv => hU g v hv⟩`. Break down `h.eq_bot_or_eq_top S with e | e` into its components or cases.

Use `left`. Use `congrArg Subrepresentation.toSubmodule e` as an intermediate fact. Rewrite `this` using `[hbot]`. Conclude with `this`. Use `right`.

Use `congrArg Subrepresentation.toSubmodule e` as an intermediate fact. Rewrite `this` using `[htop]`. Conclude with `this`. Introduce and unpack `⟨hV, hU⟩ haveI : Nontrivial (Subrepresentation ρ) := by`. Use `⟨⟨⊥, ⊤, fun e => ?_⟩⟩` and prove the remaining obligations.

Use `congrArg Subrepresentation.toSubmodule e` as an intermediate fact. Rewrite `this` using `[hbot, htop]`. Conclude with `(bot_ne_top : (⊥ : Submodule ℂ V) ≠ ⊤) this`. Use `{ eq_bot_or_eq_top := ?_ }` and prove the remaining obligations. Introduce `S`.

Break down `hU S.toSubmodule (fun g v hv => S.apply_mem_toSubmodule g hv) with e | e` into its components or cases. Use `left`. Apply `Subrepresentation.toSubmodule_injective` to reduce the goal to its premises. Rewrite using `[hbot]`. Conclude with `e`.

Use `right`. Apply `Subrepresentation.toSubmodule_injective` to reduce the goal to its premises. Rewrite using `[htop]`. Conclude with `e`.
-/
theorem main : ∀ {G : Type} [inst : Group G] {V : Type} [inst_1 : AddCommGroup V] [inst_2 : Module ℂ V] (ρ : Representation ℂ G V), Representation.IsIrreducible ρ ↔ Nontrivial V ∧ ∀ (U : Submodule ℂ V), (∀ (g : G), ∀ v ∈ U, ((ρ : G → V →ₗ[ℂ] V) g : V → V) v ∈ U) → U = ⊥ ∨ U = ⊤ := by
  intro G _ V _ _ ρ
  have hbot := subrep_bot_toSubmodule ρ
  have htop := subrep_top_toSubmodule ρ
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have hne : (⊥ : Subrepresentation ρ) ≠ ⊤ := bot_ne_top
      rw [← Submodule.nontrivial_iff ℂ]
      refine ⟨⟨⊥, ⊤, fun e => hne ?_⟩⟩
      apply Subrepresentation.toSubmodule_injective
      rw [hbot, htop]; exact e
    · intro U hU
      let S : Subrepresentation ρ := ⟨U, fun g v hv => hU g v hv⟩
      rcases h.eq_bot_or_eq_top S with e | e
      · left
        have := congrArg Subrepresentation.toSubmodule e
        rw [hbot] at this; exact this
      · right
        have := congrArg Subrepresentation.toSubmodule e
        rw [htop] at this; exact this
  · rintro ⟨hV, hU⟩
    haveI : Nontrivial (Subrepresentation ρ) := by
      refine ⟨⟨⊥, ⊤, fun e => ?_⟩⟩
      have := congrArg Subrepresentation.toSubmodule e
      rw [hbot, htop] at this
      exact (bot_ne_top : (⊥ : Submodule ℂ V) ≠ ⊤) this
    refine { eq_bot_or_eq_top := ?_ }
    intro S
    rcases hU S.toSubmodule (fun g v hv => S.apply_mem_toSubmodule g hv) with e | e
    · left; apply Subrepresentation.toSubmodule_injective; rw [hbot]; exact e
    · right; apply Subrepresentation.toSubmodule_injective; rw [htop]; exact e

end GlobalTheory.SubrepTopBot
