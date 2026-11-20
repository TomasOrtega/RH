import Mathlib

namespace GlobalTheory.CompanionTheory.FFNorm

/- English proof (translation)
Introduce `κ _ _ τ hinv hne c hc`. Set `F : Subfield κ` to `RingHom.eqLocusField τ (RingHom.id κ)`. Establish `hF : ∀ y : F, τ (y : κ) = y` using `fun y => y.2`. Set `σ : κ ≃ₐ[F] κ` to `AlgEquiv.ofRingEquiv (f := RingEquiv.ofRingHom τ τ (RingHom.ext hinv) (RingHom.ext hinv)) (fun y => hF y)`. Establish `hσ : ∀ x, σ x = τ x` using `fun x => rfl`.

Establish `hσ1 : σ ≠ 1`. Take `⟨x, hx⟩` from `hne`. Introduce `h`. Conclude with `hx (by rw [← hσ, h]; rfl)`. Establish `hall : ∀ ρ : κ ≃ₐ[F] κ, ρ = 1 ∨ ρ = σ`.

Establish `hfix : IntermediateField.fixedField (Subgroup.zpowers σ) = ⊥`. Rewrite using `[eq_bot_iff]`. Introduce `x hx`. Establish `: σ x = x` using `hx ⟨σ, Subgroup.mem_zpowers σ⟩`. Conclude with `IntermediateField.mem_bot.2 ⟨⟨x, this⟩, rfl⟩`.

Establish `htop : Subgroup.zpowers σ = ⊤`. Rewrite using `[← IntermediateField.fixingSubgroup_fixedField (Subgroup.zpowers σ), hfix]`. Conclude with `IntermediateField.fixingSubgroup_bot`. Introduce `ρ`. Establish `hρ : ρ ∈ Subgroup.zpowers σ` using `htop ▸ Subgroup.mem_top ρ`.

Establish `hsq : σ ^ 2 = 1`. Use extensionality with `x`. Simplify using `[pow_two, hσ, hinv]`. Take `⟨n, rfl⟩` from `hρ`. Break down `Int.even_or_odd' n with ⟨k, rfl | rfl⟩` into its components or cases.

Use `left`. Simplify using `[zpow_mul, hsq]`. Use `right`. Simplify using `[zpow_add, zpow_mul, hsq]`. Establish `huniv : (Finset.univ : Finset (κ ≃ₐ[F] κ)) = {1, σ}`.

Use extensionality with `ρ`. Simplify using `using hall ρ`. Take `⟨a, ha⟩` from `FiniteField.norm_surjective F κ (⟨c, hc⟩ : F)`. Use `⟨a, ?_⟩` and prove the remaining obligations. Establish `h` using `Algebra.norm_eq_prod_automorphisms F a`.

Rewrite `h` using `[huniv, Finset.prod_pair hσ1.symm, ha]`. Establish `h2 : algebraMap F κ (⟨c, hc⟩ : F) = c` using `rfl`. Rewrite `h` using `[h2]`. Simplify `h.symm` using `[hσ, mul_comm]`.
-/
theorem exists_conj_mul_eq : ∀ (κ : Type) [Field κ] [Finite κ] (τ : κ →+* κ), (∀ x, τ (τ x) = x) →
    (∃ x, τ x ≠ x) → ∀ c : κ, τ c = c → ∃ s : κ, τ s * s = c := by
  intro κ _ _ τ hinv hne c hc
  classical
  let F : Subfield κ := RingHom.eqLocusField τ (RingHom.id κ)
  have hF : ∀ y : F, τ (y : κ) = y := fun y => y.2
  let σ : κ ≃ₐ[F] κ := AlgEquiv.ofRingEquiv (f := RingEquiv.ofRingHom τ τ
      (RingHom.ext hinv) (RingHom.ext hinv)) (fun y => hF y)
  have hσ : ∀ x, σ x = τ x := fun x => rfl
  have hσ1 : σ ≠ 1 := by
    obtain ⟨x, hx⟩ := hne
    intro h
    exact hx (by rw [← hσ, h]; rfl)
  have hall : ∀ ρ : κ ≃ₐ[F] κ, ρ = 1 ∨ ρ = σ := by
    have hfix : IntermediateField.fixedField (Subgroup.zpowers σ) = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have : σ x = x := hx ⟨σ, Subgroup.mem_zpowers σ⟩
      exact IntermediateField.mem_bot.2 ⟨⟨x, this⟩, rfl⟩
    have htop : Subgroup.zpowers σ = ⊤ := by
      rw [← IntermediateField.fixingSubgroup_fixedField (Subgroup.zpowers σ), hfix]
      exact IntermediateField.fixingSubgroup_bot
    intro ρ
    have hρ : ρ ∈ Subgroup.zpowers σ := htop ▸ Subgroup.mem_top ρ
    have hsq : σ ^ 2 = 1 := by
      ext x
      simp [pow_two, hσ, hinv]
    obtain ⟨n, rfl⟩ := hρ
    rcases Int.even_or_odd' n with ⟨k, rfl | rfl⟩
    · left; simp [zpow_mul, hsq]
    · right; simp [zpow_add, zpow_mul, hsq]
  have huniv : (Finset.univ : Finset (κ ≃ₐ[F] κ)) = {1, σ} := by
    ext ρ
    simpa using hall ρ
  obtain ⟨a, ha⟩ := FiniteField.norm_surjective F κ (⟨c, hc⟩ : F)
  refine ⟨a, ?_⟩
  have h := Algebra.norm_eq_prod_automorphisms F a
  rw [huniv, Finset.prod_pair hσ1.symm, ha] at h
  have h2 : algebraMap F κ (⟨c, hc⟩ : F) = c := rfl
  rw [h2] at h
  simpa [hσ, mul_comm] using h.symm

end GlobalTheory.CompanionTheory.FFNorm
