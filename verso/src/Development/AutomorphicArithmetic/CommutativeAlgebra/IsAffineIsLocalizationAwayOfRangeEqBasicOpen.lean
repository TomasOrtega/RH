import Mathlib

open CategoryTheory Limits AlgebraicGeometry

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Introduce a local definition for the expression. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Extract witnesses or component facts from the available result. Supply the required witnesses or components.

A detailed English derivation is pending.
-/
theorem UpperTheory.isAffine_isLocalizationAway_of_range_eq_basicOpen :
    ∀ {U W : Scheme.{0}} [IsAffine U] (a : W ⟶ U) [IsOpenImmersion a] (t : Γ(U, ⊤)),
        Set.range a = (U.basicOpen t : Set U) →
        IsAffine W ∧ (∀ x : Γ(W, ⊤), ∃ (k : ℕ) (y : Γ(U, ⊤)), a.appTop.hom t ^ k * x = a.appTop.hom y) ∧
          ∀ y : Γ(U, ⊤), a.appTop.hom y = 0 → ∃ k : ℕ, t ^ k * y = 0 := by
  intro U W _ a _ t h
  have hr : Set.range a = Set.range (U.basicOpen t).ι := by
    rw [Scheme.Opens.range_ι]
    exact h
  let χ := IsOpenImmersion.isoOfRangeEq a (U.basicOpen t).ι hr
  have hfac : χ.hom ≫ (U.basicOpen t).ι = a := IsOpenImmersion.isoOfRangeEq_hom_fac a _ hr
  haveI : IsAffine (U.basicOpen t) := (isAffineOpen_top U).basicOpen t
  have hW : IsAffine W := IsAffine.of_isIso χ.hom
  have happ : ∀ r, a.appTop.hom r =
      χ.hom.appTop.hom (algebraMap Γ(U, ⊤) Γ(U.basicOpen t, ⊤) r) := by
    intro r
    rw [← hfac, Scheme.Hom.comp_appTop]
    rfl
  have hl : ∀ x, χ.inv.appTop.hom (χ.hom.appTop.hom x) = x := by
    intro x
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, χ.inv_hom_id]
    simp
  have hr' : ∀ x, χ.hom.appTop.hom (χ.inv.appTop.hom x) = x := by
    intro x
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, χ.hom_inv_id]
    simp
  refine ⟨hW, ?_, ?_⟩
  · intro x
    obtain ⟨⟨ℓ, m⟩, hℓ⟩ := IsLocalization.surj (Submonoid.powers t) (χ.inv.appTop.hom x)
    obtain ⟨k, hk⟩ := m.2
    have hk' : t ^ k = (m : Γ(U, ⊤)) := hk
    have hℓ' : χ.inv.appTop.hom x * algebraMap Γ(U, ⊤) Γ(U.basicOpen t, ⊤) (t ^ k) =
        algebraMap Γ(U, ⊤) Γ(U.basicOpen t, ⊤) ℓ := by
      rw [hk']
      exact hℓ
    refine ⟨k, ℓ, ?_⟩
    rw [happ, happ, ← hℓ']
    simp only [map_pow, map_mul, hr']
    ring
  · intro y hy
    have h0 : algebraMap Γ(U, ⊤) Γ(U.basicOpen t, ⊤) y = 0 := by
      have h2 := congrArg χ.inv.appTop.hom ((happ y).symm.trans hy)
      rwa [hl, map_zero] at h2
    obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers t) _ y).mp h0
    exact ⟨k, hk⟩
