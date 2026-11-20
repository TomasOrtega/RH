import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeModelVacuumTranslateClassesIndependent
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Gam0
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalThetaPairExistence
open Matrix

namespace GlobalTheory.Hk3.GramSep

/- English proof (translation)
Introduce `L _ _ ϖ σ q δ ψ hU hδ hne r e Δ hΔ hψ j k`. Establish `hσ` using `hU.1`. Establish `hv` using `hU.2.1`. Establish `hw : δ * (Δ j k * ϖ ^ max (e j) (e k)) ∈ Formalism.UG.intL L`. Use `GlobalTheory.Hk3.int_of_psi hU ψ hne _ (fun b hb => ?_)` and prove the remaining obligations.

Use `set c : L := b * ϖ ^ max (e j) (e k) with hc`. Establish `hcv : Valued.v c ≤ Valued.v ϖ ^ max (e j) (e k)`. Rewrite using `[hc, map_mul, map_pow]`. Conclude with `mul_le_of_le_one_left' hb`. Establish `hmem : Matrix.single k j c + Matrix.single j k (-σ c) ∈ gam σ ϖ e`.

Use `⟨fun a a' => ?_, fun a a' => ?_⟩` and prove the remaining obligations. Apply the tactic sequence `simp only [Matrix.add_apply, Matrix.single_apply, map_add, apply_ite σ, map_neg, hσ, map_zero, and_comm (a := k = a'), and_comm (a := j = a')] split_ifs <;> ring`. Rewrite using `[Matrix.add_apply]`. Use `(Valuation.map_add _ _ _).trans (max_le ?_ ?_)` and prove the remaining obligations. Rewrite using `[Matrix.single_apply] split_ifs with h`.

Take `⟨rfl, rfl⟩` from `h`. Rewrite using `[max_comm]`. Conclude with `hcv`. Simplify using the standard rewrite rules. Rewrite using `[Matrix.single_apply] split_ifs with h`.

Take `⟨rfl, rfl⟩` from `h`. Rewrite using `[Valuation.map_neg, hv]`. Conclude with `hcv`. Simplify using the standard rewrite rules. Establish `h` using `hψ _ hmem`.

Establish `e1 : b * (δ * (Δ j k * ϖ ^ max (e j) (e k))) = δ * (c * Δ j k)` using `by rw [hc]; ring`. Rewrite using `[e1, map_mul, map_mul σ c, hδ.2, hΔ, ← h]`. Use `congr 1`. Rewrite using `[Matrix.add_mul, Matrix.trace_add, Matrix.trace_single_mul, Matrix.trace_single_mul]`. Simplify using `only [smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite `hw` using `[GlobalTheory.Hk3.mem_intL_iff, map_mul, hδ.1, one_mul]`. Conclude with `hw`.
-/
theorem int_of_psi_trace_gam : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L) (ψ : AddChar L ℂ),
  Formalism.UG.IsUnramInv ϖ σ q → (Valued.v δ = 1 ∧ σ δ = -δ) →
  (∃ a ∈ Formalism.UG.intL L, σ a = a ∧ ψ (ϖ⁻¹ * a) ≠ 1) →
  ∀ (r : ℕ) (e : Fin r → ℕ) (Δ : Matrix (Fin r) (Fin r) L), (∀ j k, σ (Δ j k) = Δ k j) →
  (∀ Γ ∈ GlobalTheory.Hk3.GramSep.gam σ ϖ e, ψ (δ * Matrix.trace (Γ * Δ)) = 1) →
  ∀ j k, Δ j k * ϖ ^ max (e j) (e k) ∈ Formalism.UG.intL L := by
  intro L _ _ ϖ σ q δ ψ hU hδ hne r e Δ hΔ hψ j k
  have hσ := hU.1
  have hv := hU.2.1
  have hw : δ * (Δ j k * ϖ ^ max (e j) (e k)) ∈ Formalism.UG.intL L := by
    refine GlobalTheory.Hk3.int_of_psi hU ψ hne _ (fun b hb => ?_)
    set c : L := b * ϖ ^ max (e j) (e k) with hc
    have hcv : Valued.v c ≤ Valued.v ϖ ^ max (e j) (e k) := by
      rw [hc, map_mul, map_pow]
      exact mul_le_of_le_one_left' hb
    have hmem : Matrix.single k j c + Matrix.single j k (-σ c) ∈ gam σ ϖ e := by
      refine ⟨fun a a' => ?_, fun a a' => ?_⟩
      · simp only [Matrix.add_apply, Matrix.single_apply, map_add, apply_ite σ, map_neg, hσ, map_zero,
          and_comm (a := k = a'), and_comm (a := j = a')]
        split_ifs <;> ring
      · rw [Matrix.add_apply]
        refine (Valuation.map_add _ _ _).trans (max_le ?_ ?_)
        · rw [Matrix.single_apply]
          split_ifs with h
          · obtain ⟨rfl, rfl⟩ := h
            rw [max_comm]; exact hcv
          · simp
        · rw [Matrix.single_apply]
          split_ifs with h
          · obtain ⟨rfl, rfl⟩ := h
            rw [Valuation.map_neg, hv]; exact hcv
          · simp
    have h := hψ _ hmem
    have e1 : b * (δ * (Δ j k * ϖ ^ max (e j) (e k))) = δ * (c * Δ j k) := by rw [hc]; ring
    rw [e1, map_mul, map_mul σ c, hδ.2, hΔ, ← h]
    congr 1
    rw [Matrix.add_mul, Matrix.trace_add, Matrix.trace_single_mul, Matrix.trace_single_mul]
    simp only [smul_eq_mul]
    ring
  rw [GlobalTheory.Hk3.mem_intL_iff, map_mul, hδ.1, one_mul] at hw
  exact hw

end GlobalTheory.Hk3.GramSep
