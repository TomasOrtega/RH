import Mathlib

/- English proof (translation)
Introduce `K M _ _ _ _ _ _ h2 σ hσ τ τ' hne hc`. Take `⟨ρ, hρ⟩` from `NumberField.ComplexEmbedding.exists_comp_symm_eq_of_comp_eq τ τ' hc`. Establish `hcard : Nat.card Gal(M/K) = 2`. Rewrite using `[IsGalois.card_aut_eq_finrank, h2]`. Take `⟨y, -, hy⟩` from `(Nat.card_eq_two_iff' (1 : Gal(M/K))).1 hcard`.

Establish `h1 : ρ.symm ≠ 1`. Introduce `h`. Apply `hne` to reduce the goal to its premises. Rewrite using `[← hρ, h]`. Use extensionality with `x`.

Both sides reduce to the same expression. Establish `h3 : σ = ρ.symm` using `(hy σ hσ).trans (hy _ h1).symm`. Rewrite using `[← hρ, h3]`. Use extensionality with `x`. Both sides reduce to the same expression.
-/
theorem UpperTheory.Reformulated.B.Qe21.emb_two :
    ∀ {K M : Type} [inst : Field K] [NumberField K]
    [inst_2 : Field M] [NumberField M] [inst_4 : Algebra K M] [IsGalois K M],
    Module.finrank K M = (2 : ℕ) →
      ∀ (σ : Gal(M/K)),
        σ ≠ (1 : Gal(M/K)) →
          ∀ (τ τ' : M →+* ℂ),
            τ ≠ τ' →
              τ.comp (Algebra.algebraMap K M) = τ'.comp (Algebra.algebraMap K M) →
                τ.comp σ.toRingEquiv.toRingHom = τ' := by
  intro K M _ _ _ _ _ _ h2 σ hσ τ τ' hne hc
  obtain ⟨ρ, hρ⟩ := NumberField.ComplexEmbedding.exists_comp_symm_eq_of_comp_eq τ τ' hc
  have hcard : Nat.card Gal(M/K) = 2 := by
    rw [IsGalois.card_aut_eq_finrank, h2]
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : Gal(M/K))).1 hcard
  have h1 : ρ.symm ≠ 1 := by
    intro h
    apply hne
    rw [← hρ, h]
    ext x
    rfl
  have h3 : σ = ρ.symm := (hy σ hσ).trans (hy _ h1).symm
  rw [← hρ, h3]
  ext x
  rfl
