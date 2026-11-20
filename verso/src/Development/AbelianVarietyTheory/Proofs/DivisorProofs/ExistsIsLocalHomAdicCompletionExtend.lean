import Mathlib

open IsLocalRing

namespace GlobalTheory

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations.

Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem exists_isLocalHom_adicCompletion_extend (O : Type) [CommRing O] [IsLocalRing O]
    [IsNoetherianRing O] (V : Type) [CommRing V] [IsLocalRing V]
    [IsAdicComplete (maximalIdeal V) V] (ψ : O →+* V) (hψ : IsLocalHom ψ) :
    ∃ ev₀ : AdicCompletion (maximalIdeal O) O →+* V,
      IsLocalHom ev₀ ∧ ∀ a, ev₀ (algebraMap O _ a) = ψ a := by
  have h1 : maximalIdeal O ≤ (maximalIdeal V).comap ψ :=
    (IsLocalRing.maximalIdeal_comap ψ).ge
  have hn : ∀ n : ℕ, maximalIdeal O ^ n ≤ (maximalIdeal V ^ n).comap ψ := fun n =>
    (Ideal.pow_right_mono h1 n).trans (Ideal.le_comap_pow ψ n)
  let f : (n : ℕ) → AdicCompletion (maximalIdeal O) O →+* V ⧸ maximalIdeal V ^ n := fun n =>
    (Ideal.quotientMap _ ψ (hn n)).comp (AdicCompletion.evalₐ (maximalIdeal O) n : _ →+* _)
  have hf : ∀ {m n : ℕ} (hle : m ≤ n),
      (Ideal.Quotient.factorPow (maximalIdeal V) hle).comp (f n) = f m := by
    intro m n hle
    refine RingHom.ext fun x => ?_
    obtain ⟨c, rfl⟩ := AdicCompletion.mk_surjective _ _ x
    simp only [f, RingHom.comp_apply, RingHom.coe_coe, AdicCompletion.evalₐ_mk,
      Ideal.quotientMap_mk, Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]
    rw [Ideal.Quotient.eq, ← map_sub]
    apply hn m
    have := c.2 hle
    rw [SModEq.sub_mem] at this
    have h2 := neg_mem this
    simpa using h2
  have hev : ∀ a, IsAdicComplete.liftRingHom (maximalIdeal V) f hf (algebraMap O _ a) = ψ a := by
    intro a
    refine congrFun (IsHausdorff.funext' (maximalIdeal V)
      (f := fun a => IsAdicComplete.liftRingHom (maximalIdeal V) f hf (algebraMap O _ a))
      (g := fun a => ψ a) fun n b => ?_) a
    rw [IsAdicComplete.mk_liftRingHom]
    simp only [f, RingHom.comp_apply, RingHom.coe_coe, AlgHom.commutes]
    exact Ideal.quotientMap_mk
  refine ⟨IsAdicComplete.liftRingHom (maximalIdeal V) f hf, ?_, hev⟩
  apply ((IsLocalRing.local_hom_TFAE _).out 0 2).mpr
  rw [AdicCompletion.maximalIdeal_eq_map, Ideal.map_map, Ideal.map_le_iff_le_comap]
  intro a ha
  rw [Ideal.mem_comap, RingHom.comp_apply, hev]
  exact h1 ha

end GlobalTheory
