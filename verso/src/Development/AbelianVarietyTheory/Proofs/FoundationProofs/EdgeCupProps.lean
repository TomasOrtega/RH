import Development.AbelianVarietyTheory.Definitions.Foundations.CobOn
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFirstChernClassOfLineBundle
open GlobalTheory.KEdge GlobalTheory.NeedB Polynomial

namespace GlobalTheory.KEdge

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Take a linear combination of the given relations to obtain the conclusion.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Take a linear combination of the given relations to obtain the conclusion.
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
