import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeightTraceProducts.ThFacts

open Polynomial UpperTheory.V.Z.Sym.Wt

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
private theorem mRep_scal {K : Type} [Fintype K] {d : ℕ} (n : K → ℕ) (s : K → ℂˣ) (Q : MH d n) :
    mRep d n (fun k => Matrix.GeneralLinearGroup.scalar (Fin d) (s k)) Q = (∏ k, (s k : ℂ) ^ n k) • Q := by
  apply Subtype.ext
  apply MvPolynomial.funext
  intro x
  rw [eval_mRep]
  have hact : act (fun k => Matrix.GeneralLinearGroup.scalar (Fin d) (s k)) x = fun p => (s p.1 : ℂ) * x p := by
    funext p
    simp [act, Matrix.scalar_apply, Matrix.diagonal_apply, mul_comm]
  rw [hact, Q.2 (fun k => (s k : ℂ)) x]
  simp

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem invT_scal {d : ℕ} (s : ℂˣ) :
    invT ℂ d (Matrix.GeneralLinearGroup.scalar (Fin d) s) = Matrix.GeneralLinearGroup.scalar (Fin d) s⁻¹ := by
  refine Units.ext ?_
  rw [invT_val, ← map_inv]
  exact Matrix.diagonal_transpose _

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Extract witnesses or component facts from the available result.

Apply the first step, then apply the next step to every resulting obligation. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities.

Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Apply an available result and prove the equalities needed to match it to the conclusion. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Put the expressions in a common number system so they can be compared.
-/
theorem UpperTheory.V.Z.Sym.Wt.scalars :
    UpperTheory.V.Z.Sym.Wt.Scalars := by
  intro I _ s
  refine ⟨fun j => ?_, fun n e => ?_⟩
  · have hd : dbl 3 (fun v ↦ Matrix.GeneralLinearGroup.scalar (Fin 3) (s v)) =
        fun k => Matrix.GeneralLinearGroup.scalar (Fin 3) (if k.2 then (s k.1)⁻¹ else s k.1) := by
      funext k
      obtain ⟨v, b⟩ := k
      cases b <;> simp [dbl, invT_scal]
    apply LinearMap.ext
    intro P
    funext S
    rw [repG_apply, Module.End.one_apply]
    change mRep 3 (fun k => dg j S k.1) (dbl 3 _) (P S) = P S
    rw [hd, mRep_scal]
    convert one_smul ℂ (P S)
    rw [Fintype.prod_prod_type]
    apply Finset.prod_eq_one
    intro v _
    rw [Fintype.prod_bool]
    simp
  · apply LinearMap.ext
    intro P
    rw [repD_apply, LinearMap.smul_apply, mRep_scal, smul_smul, LinearMap.smul_apply, Module.End.one_apply]
    congr 1
    simp only [detE, MonoidHom.coe_mk, OneHom.coe_mk, Units.coe_prod, Units.val_zpow_eq_zpow_val]
    simp
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    have ha : (s v : ℂ) ≠ 0 := (s v).ne_zero
    rw [zpow_add₀ ha, zpow_mul, zpow_natCast, mul_comm]
    norm_cast
