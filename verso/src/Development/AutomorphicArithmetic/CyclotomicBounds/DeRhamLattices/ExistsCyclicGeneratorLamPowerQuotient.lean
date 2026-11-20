import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConstOneMem
open GlobalTheory.UseLoc.Cases

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Unfold both sides to obtain the same proposition, which implies itself. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem _root_.UpperTheory.KN.exists_cyclic_generator_lam_power_quotient :
    ∀ {O : Type} (LL : Type) [CommRing O] [Field LL] [Algebra O LL], Function.Injective (algebraMap O LL) →
      ∀ (lam : O) (a : ℕ), algebraMap O LL lam ≠ 0 → ∃ x₀ : ↥(Xq LL lam a), ∀ x : ↥(Xq LL lam a), ∃ c : O, x = c • x₀ := by
  intro O LL _ _ _ _ lam a hlam
  have hK : algebraMap O LL (lam ^ a) ≠ 0 := by
    rw [map_pow]; exact pow_ne_zero _ hlam
  have hmem : ∀ s : LL, Submodule.Quotient.mk (p := intO (O := O) LL) s ∈ Xq LL lam a ↔
      ∃ c : O, algebraMap O LL c = lam ^ a • s := by
    intro s
    simp only [Xq, LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply]
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact Iff.rfl
  refine ⟨⟨Submodule.Quotient.mk (algebraMap O LL (lam ^ a))⁻¹, (hmem _).2 ⟨1, ?_⟩⟩, ?_⟩
  · rw [Algebra.smul_def, mul_inv_cancel₀ hK, map_one]
  · rintro ⟨x, hx⟩
    obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨c, hc⟩ := (hmem s).1 hx
    refine ⟨c, Subtype.ext ?_⟩
    have hs : s = c • (algebraMap O LL (lam ^ a))⁻¹ := by
      rw [Algebra.smul_def, hc, Algebra.smul_def, mul_comm (algebraMap O LL (lam ^ a)) s, mul_assoc,
        mul_inv_cancel₀ hK, mul_one]
    change Submodule.Quotient.mk s = c • Submodule.Quotient.mk (p := intO (O := O) LL) (algebraMap O LL (lam ^ a))⁻¹
    rw [← Submodule.Quotient.mk_smul, ← hs]
