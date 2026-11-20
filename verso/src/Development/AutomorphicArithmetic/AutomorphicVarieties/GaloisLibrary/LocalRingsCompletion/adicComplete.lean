import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.IsCharOneOfSubsingleton
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.MemMaxPow

open PowerSeries IsLocalRing UpperTheory.V.abelian₂
open IsDiscreteValuationRing (addVal)
open scoped Pointwise TensorProduct Topology

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. By extensionality, compare the relevant components. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Extract witnesses or component facts from the available result. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify to obtain the desired conclusion from the available facts.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.V.abelian₂.adicComplete :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsAdicComplete (maximalIdeal O) O],
      IsAdicComplete (maximalIdeal O⟦X⟧) O⟦X⟧ := by
  intro O _ _ _
  have key : ∀ (x y : O⟦X⟧) (n : ℕ),
      x ≡ y [SMOD (maximalIdeal O⟦X⟧) ^ n • (⊤ : Submodule O⟦X⟧ O⟦X⟧)] ↔
        ∀ i, coeff i x - coeff i y ∈ maximalIdeal O ^ (n - i) := by
    intro x y n
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, mem_max_pow]
    simp only [map_sub]
  refine { haus' := ?_, prec' := ?_ }
  · intro x hx
    ext i
    apply eq_of_sub_mem_pow (maximalIdeal O)
    intro n
    have h := (key x 0 (n + i)).1 (hx (n + i)) i
    simpa using h
  · intro f hf
    have hc : ∀ i, ∃ L : O, ∀ n, coeff i (f (n + i)) - L ∈ maximalIdeal O ^ n := by
      intro i
      obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := maximalIdeal O) (M := O)
        (fun m => coeff i (f (m + i))) (by
          intro m n hmn
          have h := (key _ _ (m + i)).1 (hf (Nat.add_le_add_right hmn i)) i
          rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
          simpa using h)
      refine ⟨L, fun n => ?_⟩
      have h := hL n
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h
      exact h
    choose L hL using hc
    refine ⟨PowerSeries.mk L, fun n => ?_⟩
    rw [key]
    intro i
    rw [coeff_mk]
    rcases le_or_gt i n with hin | hin
    · have h := hL i (n - i)
      rwa [Nat.sub_add_cancel hin] at h
    · rw [Nat.sub_eq_zero_of_le hin.le, pow_zero, Ideal.one_eq_top]
      exact Submodule.mem_top
