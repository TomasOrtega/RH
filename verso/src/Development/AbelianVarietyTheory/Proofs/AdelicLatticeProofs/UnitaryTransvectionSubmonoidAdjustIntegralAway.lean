import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.IsHermHyperbolic
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsTraceZeroAdjustmentOfHermitianLatticeStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.TransvectionIdentitiesUnitaryStatement
open NumberField IsDedekindDomain Matrix GlobalTheory.UTrans GlobalTheory.AdLat
open scoped TensorProduct

namespace GlobalTheory.UTrans

/- English proof (translation)
Introduce `F E _ _ _ _ _ c n G hFE hG L hL hsp m hm b hb`. Proceed by induction on `hm using Submonoid.closure_induction with`. Consider the case `mem m hm`. Introduce `N`. Take `⟨x, t, hx, ht, rfl⟩` from `hm`.

Take `⟨t', k, e, ht', hk, H⟩` from `GlobalTheory.T.exists_traceZero_adjustment_of_hermitian_lattice F E c n G hFE hG L hL hsp x t (b ^ (N + 1)) (by positivity) ht`. Establish `hinv : (tv (c : E →+* E) G x t')⁻¹ = tv (c : E →+* E) G x (-t')`. Apply `Matrix.inv_eq_right_inv` to reduce the goal to its premises. Rewrite using `[(GlobalTheory.T.transvection_identities_unitary E n (c : E →+* E) G hG.invol hG.herm).2.2.1, hx]`. Use extensionality with `i j`.

Simplify using `[tv]`. Use `⟨_, Submonoid.subset_closure ⟨x, t', hx, ht', rfl⟩, k, (N + 1) * e, (Nat.coprime_pow_right_iff (Nat.succ_pos N) _ _).1 hk, fun v hv => ?_⟩` and prove the remaining obligations. Take `⟨⟨w, hw, h1⟩, h2, h3⟩` from `H v hv`. Use `⟨⟨b • w, L.smul_of_tower_mem _ hw, ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[h1, smul_smul, pow_succ]`.

Rewrite using `[pow_mul]` and apply the resulting hypothesis. Rewrite using `[pow_mul, hinv]` and apply the resulting hypothesis. Consider the case `one`. Introduce `N`. Apply the tactic sequence `refine ⟨1, one_mem _, 1, 0, by simp, fun v hv => ⟨⟨0, zero_mem _, by simp⟩, ?_, ?_⟩⟩ <;> simpa using hv`.

Consider the case `mul m₁ m₂ _ _ ih₁ ih₂`. Introduce `N`. Take `⟨p, -, k₀, e₀, hk₀, H₀⟩` from `ih₁ 0`. Establish `hden : ∀ v ∈ L, (k₀ * b ^ e₀) • (m₁ *ᵥ v) ∈ L`. Introduce `v hv`.

Take `⟨⟨w, hw, h1⟩, h2, -⟩` from `H₀ v hv`. Establish `: (k₀ * b ^ e₀) • (m₁ *ᵥ v) = k₀ • b ^ e₀ • (p *ᵥ v) - b ^ e₀ • (b ^ 0 • w)`. Rewrite using `[← h1]`. Use `module`. Rewrite using `[this]`.

Conclude with `sub_mem (L.smul_of_tower_mem _ h2) (L.smul_of_tower_mem _ (L.smul_of_tower_mem _ hw))`. Take `⟨q₂, hq₂, k₂, e₂, hk₂, H₂⟩` from `ih₂ (N + e₀)`. Take `⟨q₁, hq₁, k₁, e₁, hk₁, H₁⟩` from `ih₁ (N + e₂)`. Use `⟨q₁ * q₂, mul_mem hq₁ hq₂, k₀ * k₁ * k₂, e₁ + e₂, Nat.Coprime.mul_left (Nat.Coprime.mul_left hk₀ hk₁) hk₂, fun v hv => ⟨?_, ?_, ?_⟩⟩` and prove the remaining obligations. Take `⟨⟨w₂, hw₂, a1⟩, a2, -⟩` from `H₂ v hv`.

Take `⟨⟨w₁, hw₁, b1⟩, -, -⟩` from `H₁ _ a2`. Establish `hb' : ((b : E) ^ e₂) ≠ 0` using `pow_ne_zero _ (Nat.cast_ne_zero.2 hb.ne')`. Establish `b2 : k₁ • (q₁ *ᵥ (q₂ *ᵥ v) - m₁ *ᵥ (q₂ *ᵥ v)) = b ^ N • w₁`. Apply `smul_right_injective (Fin n → E) hb'` to reduce the goal to its premises. Simplify using `only [Matrix.mulVec_smul] at b1`.

Take the linear combination `(norm := module) b1`. Establish `a3 : k₂ • (m₁ *ᵥ (q₂ *ᵥ v) - m₁ *ᵥ (m₂ *ᵥ v)) = b ^ (N + e₀) • (m₁ *ᵥ w₂)`. Rewrite using `[← Matrix.mulVec_smul, ← a1, Matrix.mulVec_smul, Matrix.mulVec_sub]`. Use `⟨(k₀ * k₂) • w₁ + k₁ • (k₀ * b ^ e₀) • (m₁ *ᵥ w₂), add_mem (L.smul_of_tower_mem _ hw₁) (L.smul_of_tower_mem _ (hden _ hw₂)), ?_⟩` and prove the remaining obligations. Rewrite using `[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]`.

Take the linear combination `(norm := module) (k₀ * k₂) • b2 + (k₀ * k₁) • a3`. Use `(H₁ _ (H₂ v hv).2.1).2.1` as an intermediate fact. Rewrite `this` using `[Matrix.mulVec_smul, smul_smul, ← pow_add, Matrix.mulVec_mulVec]`. Then use the resulting hypothesis. Use `(H₂ _ (H₁ v hv).2.2).2.2` as an intermediate fact. Rewrite `this` using `[Matrix.mulVec_smul, smul_smul, ← pow_add, Matrix.mulVec_mulVec, ← Matrix.mul_inv_rev, add_comm]`. Then use the resulting hypothesis.
-/
theorem tvGen_adjust : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), Module.finrank F E = 2 → IsHerm (c : E →+* E) G → ∀ L : Submodule (𝓞 E) (Fin n → E), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → ∀ m ∈ TvGen (c : E →+* E) G, ∀ b : ℕ, 0 < b → ∀ N : ℕ, ∃ m' ∈ TvGen (c : E →+* E) G, ∃ k e : ℕ, k.Coprime b ∧ ∀ v ∈ L, (∃ w ∈ L, k • (m' *ᵥ v - m *ᵥ v) = b ^ N • w) ∧ b ^ e • (m' *ᵥ v) ∈ L ∧ b ^ e • (m'⁻¹ *ᵥ v) ∈ L := by
  intro F E _ _ _ _ _ c n G hFE hG L hL hsp m hm b hb
  induction hm using Submonoid.closure_induction with
  | mem m hm =>
    intro N
    obtain ⟨x, t, hx, ht, rfl⟩ := hm
    obtain ⟨t', k, e, ht', hk, H⟩ := GlobalTheory.T.exists_traceZero_adjustment_of_hermitian_lattice F E c n G hFE hG L hL hsp x t (b ^ (N + 1)) (by positivity) ht
    have hinv : (tv (c : E →+* E) G x t')⁻¹ = tv (c : E →+* E) G x (-t') := by
      apply Matrix.inv_eq_right_inv
      rw [(GlobalTheory.T.transvection_identities_unitary E n (c : E →+* E) G hG.invol hG.herm).2.2.1, hx]
      ext i j
      simp [tv]
    refine ⟨_, Submonoid.subset_closure ⟨x, t', hx, ht', rfl⟩, k, (N + 1) * e,
      (Nat.coprime_pow_right_iff (Nat.succ_pos N) _ _).1 hk, fun v hv => ?_⟩
    obtain ⟨⟨w, hw, h1⟩, h2, h3⟩ := H v hv
    refine ⟨⟨b • w, L.smul_of_tower_mem _ hw, ?_⟩, ?_, ?_⟩
    · rw [h1, smul_smul, pow_succ]
    · rwa [pow_mul]
    · rwa [pow_mul, hinv]
  | one =>
    intro N
    refine ⟨1, one_mem _, 1, 0, by simp, fun v hv => ⟨⟨0, zero_mem _, by simp⟩, ?_, ?_⟩⟩ <;> simpa using hv
  | mul m₁ m₂ _ _ ih₁ ih₂ =>
    intro N
    obtain ⟨p, -, k₀, e₀, hk₀, H₀⟩ := ih₁ 0
    have hden : ∀ v ∈ L, (k₀ * b ^ e₀) • (m₁ *ᵥ v) ∈ L := by
      intro v hv
      obtain ⟨⟨w, hw, h1⟩, h2, -⟩ := H₀ v hv
      have : (k₀ * b ^ e₀) • (m₁ *ᵥ v) = k₀ • b ^ e₀ • (p *ᵥ v) - b ^ e₀ • (b ^ 0 • w) := by
        rw [← h1]; module
      rw [this]
      exact sub_mem (L.smul_of_tower_mem _ h2) (L.smul_of_tower_mem _ (L.smul_of_tower_mem _ hw))
    obtain ⟨q₂, hq₂, k₂, e₂, hk₂, H₂⟩ := ih₂ (N + e₀)
    obtain ⟨q₁, hq₁, k₁, e₁, hk₁, H₁⟩ := ih₁ (N + e₂)
    refine ⟨q₁ * q₂, mul_mem hq₁ hq₂, k₀ * k₁ * k₂, e₁ + e₂,
      Nat.Coprime.mul_left (Nat.Coprime.mul_left hk₀ hk₁) hk₂, fun v hv => ⟨?_, ?_, ?_⟩⟩
    · obtain ⟨⟨w₂, hw₂, a1⟩, a2, -⟩ := H₂ v hv
      obtain ⟨⟨w₁, hw₁, b1⟩, -, -⟩ := H₁ _ a2
      have hb' : ((b : E) ^ e₂) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hb.ne')
      have b2 : k₁ • (q₁ *ᵥ (q₂ *ᵥ v) - m₁ *ᵥ (q₂ *ᵥ v)) = b ^ N • w₁ := by
        apply smul_right_injective (Fin n → E) hb'
        simp only [Matrix.mulVec_smul] at b1
        linear_combination (norm := module) b1
      have a3 : k₂ • (m₁ *ᵥ (q₂ *ᵥ v) - m₁ *ᵥ (m₂ *ᵥ v)) = b ^ (N + e₀) • (m₁ *ᵥ w₂) := by
        rw [← Matrix.mulVec_smul, ← a1, Matrix.mulVec_smul, Matrix.mulVec_sub]
      refine ⟨(k₀ * k₂) • w₁ + k₁ • (k₀ * b ^ e₀) • (m₁ *ᵥ w₂),
        add_mem (L.smul_of_tower_mem _ hw₁) (L.smul_of_tower_mem _ (hden _ hw₂)), ?_⟩
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      linear_combination (norm := module) (k₀ * k₂) • b2 + (k₀ * k₁) • a3
    · have := (H₁ _ (H₂ v hv).2.1).2.1
      rwa [Matrix.mulVec_smul, smul_smul, ← pow_add, Matrix.mulVec_mulVec] at this
    · have := (H₂ _ (H₁ v hv).2.2).2.2
      rwa [Matrix.mulVec_smul, smul_smul, ← pow_add, Matrix.mulVec_mulVec, ← Matrix.mul_inv_rev, add_comm] at this

end GlobalTheory.UTrans
