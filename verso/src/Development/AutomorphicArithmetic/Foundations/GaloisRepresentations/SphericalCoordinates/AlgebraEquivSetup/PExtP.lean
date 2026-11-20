import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.HeckeTraceEq

open Formalism.UG GlobalTheory.LKDef.HeckeTraceForms UpperTheory.Gal.W2.Seed
open scoped Classical

/- English proof (translation)
Introduce `Γ X X₂ V _ _ _ _ _ ι K K₂ ξ φ h1 h2`. Set `F : X × X₂ → V` to `fun p => if h : ∃ γ : Γ, (ι γ).2⁻¹ * p.2 ∈ K₂ then ξ h.choose (φ ((ι h.choose).1⁻¹ * p.1)) else 0`. Establish `key : ∀ (γ : Γ) (g : X) (g₂ : X₂), (ι γ).2⁻¹ * g₂ ∈ K₂ → F (g, g₂) = ξ γ (φ ((ι γ).1⁻¹ * g))`. Introduce `γ g g₂ hγ`. Establish `h : ∃ γ : Γ, (ι γ).2⁻¹ * g₂ ∈ K₂` using `⟨γ, hγ⟩`.

Simplify using `only [F]`. Rewrite using `[dif_pos h]`. Establish `hδ` using `h.choose_spec`. Generalize the expression as in `h.choose = δ at hδ ⊢`. Establish `hε : (ι (δ⁻¹ * γ)).2 ∈ K₂`.

Establish `e : (ι (δ⁻¹ * γ)).2 = ((ι δ).2⁻¹ * g₂) * ((ι γ).2⁻¹ * g₂)⁻¹`. Simplify using `only [map_mul, map_inv, Prod.snd_mul, Prod.snd_inv]`. Use `group`. Rewrite using `[e]`. Conclude with `K₂.mul_mem hδ (K₂.inv_mem hγ)`.

Establish `e2 : (ι (δ⁻¹ * γ)).1 * ((ι γ).1⁻¹ * g) = (ι δ).1⁻¹ * g`. Simplify using `only [map_mul, map_inv, Prod.fst_mul, Prod.fst_inv]`. Use `group`. Rewrite using `[← e2, h1 _ hε, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]`. Establish `zero : ∀ (g : X) (g₂ : X₂), (¬ ∃ γ : Γ, (ι γ).2⁻¹ * g₂ ∈ K₂) → F (g, g₂) = 0`.

Introduce `g g₂ h`. Simplify using `only [F]`. Rewrite using `[dif_neg h]`. Establish `mem : F ∈ forms ι (K.prod K₂) ξ`. Use `⟨fun γ p => ?_, fun k hk p => ?_⟩` and prove the remaining obligations.

Take `⟨g, g₂⟩` from `p`. Establish `e : ι γ * (g, g₂) = ((ι γ).1 * g, (ι γ).2 * g₂)` using `rfl`. Rewrite using `[e]`. Distinguish the cases in `h : ∃ δ : Γ, (ι δ).2⁻¹ * g₂ ∈ K₂`. Take `⟨δ, hδ⟩` from `h`.

Establish `hs : (ι (γ * δ)).2⁻¹ * ((ι γ).2 * g₂) ∈ K₂`. Simplify `hδ` using `[map_mul, mul_assoc]`. Rewrite using `[key δ g g₂ hδ, key (γ * δ) _ _ hs, ← Module.End.mul_apply, ← map_mul]`. Use `congr 2`. Simplify using `[mul_assoc]`.

Rewrite using `[zero g g₂ h, map_zero]`. Apply `zero` to reduce the goal to its premises. Introduce and unpack `⟨δ, hδ⟩`. Apply `h` to reduce the goal to its premises. Use `⟨γ⁻¹ * δ, ?_⟩` and prove the remaining obligations.

Simplify `hδ` using `[map_mul, mul_assoc]`. Take `⟨g, g₂⟩` from `p`. Take `⟨k1, k2⟩` from `k`. Rewrite `hk` using `[Subgroup.mem_prod]`. Establish `hk1 : k1 ∈ K` using `hk.1`.

Establish `hk2 : k2 ∈ K₂` using `hk.2`. Establish `e : (g, g₂) * (k1, k2) = (g * k1, g₂ * k2)` using `rfl`. Rewrite using `[e]`. Distinguish the cases in `h : ∃ δ : Γ, (ι δ).2⁻¹ * g₂ ∈ K₂`. Take `⟨δ, hδ⟩` from `h`.

Establish `hs : (ι δ).2⁻¹ * (g₂ * k2) ∈ K₂`. Rewrite using `[← mul_assoc]`. Conclude with `K₂.mul_mem hδ hk2`. Rewrite using `[key δ g g₂ hδ, key δ (g * k1) (g₂ * k2) hs, ← mul_assoc, h2 k1 hk1]`. Rewrite using `[zero g g₂ h, zero]`.

Introduce and unpack `⟨δ, hδ⟩`. Apply `h` to reduce the goal to its premises. Use `⟨δ, ?_⟩` and prove the remaining obligations. Use `K₂.mul_mem hδ (K₂.inv_mem hk2)` as an intermediate fact. Simplify `this` using `[mul_assoc]`.

Use `⟨⟨F, mem⟩, fun g => ?_, fun g₂ => ?_⟩` and prove the remaining obligations. Use `show F (g, 1) = φ g`. Rewrite using `[key 1 g 1 (by simp)]`. Simplify using the standard rewrite rules. Distinguish the cases in `h : ∃ δ : Γ, (ι δ).2⁻¹ * g₂ ∈ K₂`.

Take `⟨δ, hδ⟩` from `h`. Conclude with `Or.inr ⟨δ, fun g => key δ g g₂ hδ⟩`. Conclude with `Or.inl fun g => zero g g₂ h`.
-/
theorem UpperTheory.Gal.W2.Seed.pExtP :
    ExtP := by
  intro Γ X X₂ V _ _ _ _ _ ι K K₂ ξ φ h1 h2
  let F : X × X₂ → V := fun p =>
    if h : ∃ γ : Γ, (ι γ).2⁻¹ * p.2 ∈ K₂ then ξ h.choose (φ ((ι h.choose).1⁻¹ * p.1)) else 0
  have key : ∀ (γ : Γ) (g : X) (g₂ : X₂), (ι γ).2⁻¹ * g₂ ∈ K₂ →
      F (g, g₂) = ξ γ (φ ((ι γ).1⁻¹ * g)) := by
    intro γ g g₂ hγ
    have h : ∃ γ : Γ, (ι γ).2⁻¹ * g₂ ∈ K₂ := ⟨γ, hγ⟩
    dsimp only [F]
    rw [dif_pos h]
    have hδ := h.choose_spec
    generalize h.choose = δ at hδ ⊢
    have hε : (ι (δ⁻¹ * γ)).2 ∈ K₂ := by
      have e : (ι (δ⁻¹ * γ)).2 = ((ι δ).2⁻¹ * g₂) * ((ι γ).2⁻¹ * g₂)⁻¹ := by
        simp only [map_mul, map_inv, Prod.snd_mul, Prod.snd_inv]
        group
      rw [e]
      exact K₂.mul_mem hδ (K₂.inv_mem hγ)
    have e2 : (ι (δ⁻¹ * γ)).1 * ((ι γ).1⁻¹ * g) = (ι δ).1⁻¹ * g := by
      simp only [map_mul, map_inv, Prod.fst_mul, Prod.fst_inv]
      group
    rw [← e2, h1 _ hε, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
  have zero : ∀ (g : X) (g₂ : X₂), (¬ ∃ γ : Γ, (ι γ).2⁻¹ * g₂ ∈ K₂) → F (g, g₂) = 0 := by
    intro g g₂ h
    dsimp only [F]
    rw [dif_neg h]
  have mem : F ∈ forms ι (K.prod K₂) ξ := by
    refine ⟨fun γ p => ?_, fun k hk p => ?_⟩
    · obtain ⟨g, g₂⟩ := p
      have e : ι γ * (g, g₂) = ((ι γ).1 * g, (ι γ).2 * g₂) := rfl
      rw [e]
      by_cases h : ∃ δ : Γ, (ι δ).2⁻¹ * g₂ ∈ K₂
      · obtain ⟨δ, hδ⟩ := h
        have hs : (ι (γ * δ)).2⁻¹ * ((ι γ).2 * g₂) ∈ K₂ := by
          simpa [map_mul, mul_assoc] using hδ
        rw [key δ g g₂ hδ, key (γ * δ) _ _ hs, ← Module.End.mul_apply, ← map_mul]
        congr 2
        simp [mul_assoc]
      · rw [zero g g₂ h, map_zero]
        apply zero
        rintro ⟨δ, hδ⟩
        apply h
        refine ⟨γ⁻¹ * δ, ?_⟩
        simpa [map_mul, mul_assoc] using hδ
    · obtain ⟨g, g₂⟩ := p
      obtain ⟨k1, k2⟩ := k
      rw [Subgroup.mem_prod] at hk
      have hk1 : k1 ∈ K := hk.1
      have hk2 : k2 ∈ K₂ := hk.2
      have e : (g, g₂) * (k1, k2) = (g * k1, g₂ * k2) := rfl
      rw [e]
      by_cases h : ∃ δ : Γ, (ι δ).2⁻¹ * g₂ ∈ K₂
      · obtain ⟨δ, hδ⟩ := h
        have hs : (ι δ).2⁻¹ * (g₂ * k2) ∈ K₂ := by
          rw [← mul_assoc]
          exact K₂.mul_mem hδ hk2
        rw [key δ g g₂ hδ, key δ (g * k1) (g₂ * k2) hs, ← mul_assoc, h2 k1 hk1]
      · rw [zero g g₂ h, zero]
        rintro ⟨δ, hδ⟩
        apply h
        refine ⟨δ, ?_⟩
        have := K₂.mul_mem hδ (K₂.inv_mem hk2)
        simpa [mul_assoc] using this
  refine ⟨⟨F, mem⟩, fun g => ?_, fun g₂ => ?_⟩
  · show F (g, 1) = φ g
    rw [key 1 g 1 (by simp)]
    simp
  · by_cases h : ∃ δ : Γ, (ι δ).2⁻¹ * g₂ ∈ K₂
    · obtain ⟨δ, hδ⟩ := h
      exact Or.inr ⟨δ, fun g => key δ g g₂ hδ⟩
    · exact Or.inl fun g => zero g g₂ h
