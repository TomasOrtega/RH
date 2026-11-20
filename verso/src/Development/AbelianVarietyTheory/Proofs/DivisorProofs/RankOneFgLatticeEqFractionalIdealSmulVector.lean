import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointShiftSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Dets
open NumberField

namespace GlobalTheory

/- English proof (translation)
Introduce `hr hfg`. Unfold `ReciprocityTheory.GeometryOfNumbersTheory.latRank at hr`. Take `⟨w, hw0, hw⟩` from `(finrank_eq_one_iff').mp hr`. Establish `hvW : (w : Fin m → K) ≠ 0`. Introduce `h`.

Conclude with `hw0 (Subtype.ext h)`. Establish `hmul : ∀ e ∈ ell, ∃ β : K, e = β • (w : Fin m → K)`. Introduce `e he`. Take `⟨c, hc⟩` from `hw ⟨e, Submodule.subset_span he⟩`. Use `⟨c, ?_⟩` and prove the remaining obligations.

Use `congrArg Subtype.val hc` as an intermediate fact. Conclude with `this.symm`. Set `f : K →ₗ[𝓞 K] (Fin m → K)` to `{ toFun := fun β => β • (w : Fin m → K) map_add' := fun a b => add_smul a b _ map_smul' := fun r b => by`. Simplify using `only [RingHom.id_apply]`. Conclude with `smul_assoc r b _ }`.

Establish `hf : ∀ β, f β = β • (w : Fin m → K)` using `fun _ => rfl`. Establish `finj : Function.Injective f`. Introduce `a b hab`. Rewrite `hab` using `[hf, hf]`. Establish `: (a - b) • (w : Fin m → K) = 0` using `by rw [sub_smul, hab, sub_self]`.

Break down `smul_eq_zero.mp this with h | h` into its components or cases. Conclude with `sub_eq_zero.mp h`. Conclude with `absurd h hvW`. Use `⟨w, hvW, ell.comap f, ?_, ?_, ?_⟩` and prove the remaining obligations. Apply `Submodule.fg_of_fg_map_injective f finj` to reduce the goal to its premises.

Establish `: (ell.comap f).map f = ell`. Apply `le_antisymm (Submodule.map_comap_le _ _)` to reduce the goal to its premises. Introduce `e he`. Take `⟨β, rfl⟩` from `hmul e he`. Conclude with `⟨β, he, rfl⟩`.

Rewrite using `[this]`. Conclude with `hfg`. Introduce `hbot`. Apply `hw0` to reduce the goal to its premises. Establish `hell : ell = ⊥`.

Rewrite using `[eq_bot_iff]`. Introduce `e he`. Take `⟨β, rfl⟩` from `hmul e he`. Establish `: β ∈ ell.comap f` using `he`. Rewrite `this` using `[hbot, Submodule.mem_bot]`.

Simplify using `[this]`. Establish `hW : Submodule.span K (ell : Set (Fin m → K)) = ⊥` using `by simp [hell]`. Establish `h0 : ∀ x ∈ Submodule.span K (ell : Set (Fin m → K)), x = 0`. Rewrite using `[hW]`. Introduce `x hx`.

Conclude with `(Submodule.mem_bot K).mp hx`. Conclude with `Subtype.ext (h0 _ w.2)`. Introduce `e`. Prove the components needed by the constructor for the conclusion. Introduce `he`.

Take `⟨β, rfl⟩` from `hmul e he`. Conclude with `⟨β, he, rfl⟩`. Introduce and unpack `⟨β, hβ, rfl⟩`. Conclude with `hβ`.
-/
theorem latRank_one_eq_ideal_smul {K : Type} [Field K] [NumberField K] {m : ℕ}
    (ell : Submodule (𝓞 K) (Fin m → K)) :
    ReciprocityTheory.GeometryOfNumbersTheory.latRank K ell = 1 → ell.FG →
    ∃ v : Fin m → K, v ≠ 0 ∧ ∃ 𝔟 : Submodule (𝓞 K) K, 𝔟.FG ∧ 𝔟 ≠ ⊥ ∧
      ∀ e, e ∈ ell ↔ ∃ β ∈ 𝔟, e = β • v := by
  intro hr hfg
  unfold ReciprocityTheory.GeometryOfNumbersTheory.latRank at hr
  obtain ⟨w, hw0, hw⟩ := (finrank_eq_one_iff').mp hr
  have hvW : (w : Fin m → K) ≠ 0 := by
    intro h; exact hw0 (Subtype.ext h)
  have hmul : ∀ e ∈ ell, ∃ β : K, e = β • (w : Fin m → K) := by
    intro e he
    obtain ⟨c, hc⟩ := hw ⟨e, Submodule.subset_span he⟩
    refine ⟨c, ?_⟩
    have := congrArg Subtype.val hc
    exact this.symm
  let f : K →ₗ[𝓞 K] (Fin m → K) :=
    { toFun := fun β => β • (w : Fin m → K)
      map_add' := fun a b => add_smul a b _
      map_smul' := fun r b => by
        simp only [RingHom.id_apply]
        exact smul_assoc r b _ }
  have hf : ∀ β, f β = β • (w : Fin m → K) := fun _ => rfl
  have finj : Function.Injective f := by
    intro a b hab
    rw [hf, hf] at hab
    have : (a - b) • (w : Fin m → K) = 0 := by rw [sub_smul, hab, sub_self]
    rcases smul_eq_zero.mp this with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hvW
  refine ⟨w, hvW, ell.comap f, ?_, ?_, ?_⟩
  · apply Submodule.fg_of_fg_map_injective f finj
    have : (ell.comap f).map f = ell := by
      apply le_antisymm (Submodule.map_comap_le _ _)
      intro e he
      obtain ⟨β, rfl⟩ := hmul e he
      exact ⟨β, he, rfl⟩
    rw [this]; exact hfg
  · intro hbot
    apply hw0
    have hell : ell = ⊥ := by
      rw [eq_bot_iff]; intro e he
      obtain ⟨β, rfl⟩ := hmul e he
      have : β ∈ ell.comap f := he
      rw [hbot, Submodule.mem_bot] at this
      simp [this]
    have hW : Submodule.span K (ell : Set (Fin m → K)) = ⊥ := by simp [hell]
    have h0 : ∀ x ∈ Submodule.span K (ell : Set (Fin m → K)), x = 0 := by
      rw [hW]; intro x hx; exact (Submodule.mem_bot K).mp hx
    exact Subtype.ext (h0 _ w.2)
  · intro e
    constructor
    · intro he
      obtain ⟨β, rfl⟩ := hmul e he
      exact ⟨β, he, rfl⟩
    · rintro ⟨β, hβ, rfl⟩
      exact hβ

end GlobalTheory
