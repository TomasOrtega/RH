import Development.EtaleCohomology.EtaleSheaves.SpectrumLimits

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LevelsGenPf
open LateralTheory.E.CechLevelsPf LateralTheory.E.LevelsPf

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result. By extensionality, compare the relevant components.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem quotCop : QuotCop := by
  intro A A' B _ _ _ φ χ ι l hl I hcop R _ g c hg
  have hg' : ∀ i, ((g i).comp (Ideal.Quotient.mk (I.map φ))).comp φ = c.comp (Ideal.Quotient.mk I) := by
    intro i
    rw [RingHom.comp_assoc, ← qm_comp, ← RingHom.comp_assoc, hg i]
  obtain ⟨h', ⟨h'l, h'c⟩, h'u⟩ := hcop R _ _ hg'
  have hk : ∀ b ∈ I.map χ, h' b = 0 := by
    intro b hb
    have : I.map χ ≤ RingHom.ker h' := by
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      change h' (χ a) = 0
      rw [← RingHom.comp_apply, h'c, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero]
    exact this hb
  refine ⟨Ideal.Quotient.lift _ h' hk, ⟨fun i => ?_, ?_⟩, fun h2 ⟨h2l, h2c⟩ => ?_⟩
  · apply Ideal.Quotient.ringHom_ext
    ext x
    simp only [RingHom.comp_apply, lq, Ideal.quotientMap_mk, Ideal.Quotient.lift_mk]
    rw [← RingHom.comp_apply h' (l i), h'l i, RingHom.comp_apply]
  · apply Ideal.Quotient.ringHom_ext
    ext x
    simp only [RingHom.comp_apply, qm, Ideal.quotientMap_mk, Ideal.Quotient.lift_mk]
    rw [← RingHom.comp_apply h' χ, h'c, RingHom.comp_apply]
  · apply Ideal.Quotient.ringHom_ext
    have : h2.comp (Ideal.Quotient.mk _) = h' := by
      apply h'u
      refine ⟨fun i => ?_, ?_⟩
      · rw [RingHom.comp_assoc, ← Ideal.quotientMap_comp_mk (le_l φ χ (l i) (hl i) I), ← RingHom.comp_assoc]
        exact congrArg (fun f => RingHom.comp f (Ideal.Quotient.mk (I.map φ))) (h2l i)
      · rw [RingHom.comp_assoc, ← qm_comp, ← RingHom.comp_assoc, h2c]
    rw [this]
    ext x
    simp

end LateralTheory.E.LevelsGenPf
