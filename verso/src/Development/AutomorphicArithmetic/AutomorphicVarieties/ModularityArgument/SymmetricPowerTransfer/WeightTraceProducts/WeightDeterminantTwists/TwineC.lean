import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeightTraceProducts.ThFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeightTraceProducts.WeightDeterminantTwists.FinMH
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeightTraceProducts.WeightDeterminantTwists.TrSwap
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeightTraceProducts.WeightDeterminantTwists.HomogeneousTraceDiagonal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeightTraceProducts.WeightDeterminantTwists.HqThree

open Polynomial UpperTheory.V.Z.Sym.Wt

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
private theorem tr_pi {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    [∀ i, FiniteDimensional ℂ (V i)] (f : ∀ i, Module.End ℂ (V i)) (F : Module.End ℂ (∀ i, V i)) (h : ∀ x i, F x i = f i (x i)) :
    LinearMap.trace ℂ _ F = ∑ i, LinearMap.trace ℂ _ (f i) := by
  have e : F = ∑ i, (LinearMap.single ℂ V i) ∘ₗ (f i ∘ₗ LinearMap.proj i) := by
    refine LinearMap.ext fun x => funext fun k => ?_
    rw [h, LinearMap.sum_apply, Finset.sum_apply, Finset.sum_eq_single k]
    · simp
    · intro b _ hb
      simp [Pi.single_eq_of_ne hb.symm]
    · simp
  rw [e, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.trace_comp_comm']
  congr 1
  ext x
  simp

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the hypotheses and the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the hypotheses and the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities.

Simplify using the standard rewrite rules. Take a linear combination of the given relations to obtain the conclusion. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem UpperTheory.V.Z.Sym.Wt.twineC :
    UpperTheory.V.Z.Sym.Wt.TwineC := by
  intro I _ _ j hj g τ h
  haveI : ∀ S : I → Bool, FiniteDimensional ℂ (Bi 3 (dg j S)) := fun S => finMH _ _ _
  rw [tr_pi (fun S : I → Bool => sg S • (biRep 3 (dg j S) g * swp 3 (dg j S))) _ fun x S => by
    rw [Module.End.mul_apply, repG_apply, thG_apply, map_smul]; rfl]
  simp only [map_smul, trSwap _, smul_eq_mul, sg, ← Finset.prod_mul_distrib, dg]
  rw [← Fintype.piFinset_univ, ← Finset.prod_univ_sum (fun _ : I => (Finset.univ : Finset Bool))
    fun v b => (if b = true then (-1 : ℂ) else 1) * tr1 3 (if b = true then j - 1 else j) (g v * invT ℂ 3 (g v))]
  refine Finset.prod_congr rfl fun v _ => ?_
  obtain ⟨a, ha⟩ : ∃ a : ℂ, a * a = τ v ^ 2 - 4 := IsAlgClosed.exists_eq_mul_self _ |>.imp fun _ h => h.symm
  have h1 : (τ v + a) / 2 + (τ v - a) / 2 = τ v := by ring
  have h2 : (τ v + a) / 2 * ((τ v - a) / 2) = 1 := by linear_combination (-1 / 4 : ℂ) * ha
  have hc : ((g v * invT ℂ 3 (g v) : GL (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ).charpoly =
      ∏ i, (X - C (![(τ v + a) / 2, 1, (τ v - a) / 2] i)) := by
    rw [h, Fin.prod_univ_three]
    have e1 := congrArg (C : ℂ →+* ℂ[X]) h1
    have e2 := congrArg (C : ℂ →+* ℂ[X]) h2
    rw [map_add] at e1
    rw [map_mul, map_one] at e2
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, map_one]
    linear_combination (X - 1) * X * e1 - (X - 1) * e2
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  have := hqThree k ((τ v + a) / 2) ((τ v - a) / 2)
  rw [h1, h2] at this
  rw [Fintype.sum_bool, ← this]
  simp only [if_true, Bool.false_eq_true, if_false, Nat.add_sub_cancel, trOne _ _ _ _ hc]
  ring
