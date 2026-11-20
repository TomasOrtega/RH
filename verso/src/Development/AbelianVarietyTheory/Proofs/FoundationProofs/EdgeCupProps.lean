import Development.AbelianVarietyTheory.Definitions.Foundations.CobOn
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFirstChernClassOfLineBundle
open GlobalTheory.KEdge GlobalTheory.NeedB Polynomial

namespace GlobalTheory.KEdge

/- English proof (translation)
Introduce `Γ _ N Δ hN x y η hC`. Establish `hmul : ∀ (z : Γ →* Multiplicative (ZMod N)) (a b : Γ), (z (a * b)).toAdd = (z a).toAdd + (z b).toAdd`. Introduce `z a b`. Rewrite using `[z.map_mul]`. Both sides reduce to the same expression.

Establish `hconj : ∀ (z : Γ →* Multiplicative (ZMod N)) (s a : Γ), (z (s * a * s⁻¹)).toAdd = (z a).toAdd`. Introduce `z s a`. Rewrite using `[hmul, hmul, z.map_inv, toAdd_inv]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `σ h hh h' hh'`. Establish `m1 : σ * h * σ⁻¹ ∈ Δ` using `hN.conj_mem h hh σ`. Establish `m2 : σ * h' * σ⁻¹ ∈ Δ` using `hN.conj_mem h' hh' σ`. Establish `e1` using `hC _ m1 _ m2`. Establish `e2` using `hC h hh h' hh'`.

Establish `g : σ * (h * h') * σ⁻¹ = (σ * h * σ⁻¹) * (σ * h' * σ⁻¹)` using `by group`. Simplify using `only [edge]`. Rewrite using `[g, hmul x h h', hmul y h h']`. Rewrite `e1` using `[hconj x, hconj y]`. Take the linear combination `e1 - e2`.

Introduce `σ τ h _`. Establish `g : σ * τ * h * (σ * τ)⁻¹ = σ * (τ * h * τ⁻¹) * σ⁻¹` using `by group`. Simplify using `only [edge]`. Rewrite using `[g, hmul x σ τ, hmul y σ τ, hconj x τ h, hconj y τ h]`. Expand and normalize the polynomial expressions, which then agree.

Introduce `σ hσ h hh`. Establish `m1 : σ * h * σ⁻¹ ∈ Δ` using `hN.conj_mem h hh σ`. Establish `e1` using `hC _ m1 σ hσ`. Establish `e2` using `hC σ hσ h hh`. Establish `g : σ * h * σ⁻¹ * σ = σ * h` using `by group`.

Rewrite `e1` using `[g, hconj x]`. Simplify using `only [edge]`. Take the linear combination `e2 - e1`.
-/
theorem edge_cup_props : ∀ (Γ : Type) [Group Γ] (N : ℕ) (Δ : Subgroup Γ) [Δ.Normal] (x y : Γ →* Multiplicative (ZMod N)) (η : Γ → ZMod N),
  CobOn Δ x y η →
  (∀ σ, ∀ h ∈ Δ, ∀ h' ∈ Δ, edge x y η σ (h * h') = edge x y η σ h + edge x y η σ h') ∧
  (∀ σ τ, ∀ h ∈ Δ, edge x y η (σ * τ) h = edge x y η σ (τ * h * τ⁻¹) + edge x y η τ h) ∧
  (∀ σ ∈ Δ, ∀ h ∈ Δ, edge x y η σ h = 0) := by
  intro Γ _ N Δ hN x y η hC
  have hmul : ∀ (z : Γ →* Multiplicative (ZMod N)) (a b : Γ), (z (a * b)).toAdd = (z a).toAdd + (z b).toAdd := by
    intro z a b; rw [z.map_mul]; rfl
  have hconj : ∀ (z : Γ →* Multiplicative (ZMod N)) (s a : Γ), (z (s * a * s⁻¹)).toAdd = (z a).toAdd := by
    intro z s a
    rw [hmul, hmul, z.map_inv, toAdd_inv]; ring
  refine ⟨?_, ?_, ?_⟩
  · intro σ h hh h' hh'
    have m1 : σ * h * σ⁻¹ ∈ Δ := hN.conj_mem h hh σ
    have m2 : σ * h' * σ⁻¹ ∈ Δ := hN.conj_mem h' hh' σ
    have e1 := hC _ m1 _ m2
    have e2 := hC h hh h' hh'
    have g : σ * (h * h') * σ⁻¹ = (σ * h * σ⁻¹) * (σ * h' * σ⁻¹) := by group
    simp only [edge]
    rw [g, hmul x h h', hmul y h h']
    rw [hconj x, hconj y] at e1
    linear_combination e1 - e2
  · intro σ τ h _
    have g : σ * τ * h * (σ * τ)⁻¹ = σ * (τ * h * τ⁻¹) * σ⁻¹ := by group
    simp only [edge]
    rw [g, hmul x σ τ, hmul y σ τ, hconj x τ h, hconj y τ h]
    ring
  · intro σ hσ h hh
    have m1 : σ * h * σ⁻¹ ∈ Δ := hN.conj_mem h hh σ
    have e1 := hC _ m1 σ hσ
    have e2 := hC σ hσ h hh
    have g : σ * h * σ⁻¹ * σ = σ * h := by group
    rw [g, hconj x] at e1
    simp only [edge]
    linear_combination e2 - e1

end GlobalTheory.KEdge
