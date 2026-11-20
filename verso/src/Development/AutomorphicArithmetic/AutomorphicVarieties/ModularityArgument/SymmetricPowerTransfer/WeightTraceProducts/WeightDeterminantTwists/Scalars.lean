import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeightTraceProducts.ThFacts

open Polynomial UpperTheory.V.Z.Sym.Wt

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Apply `MvPolynomial.funext` to reduce the goal to its premises. Introduce `x`. Rewrite using `[eval_mRep]`. Establish `hact : act (fun k => Matrix.GeneralLinearGroup.scalar (Fin d) (s k)) x = fun p => (s p.1 : ℂ) * x p`.

Use function extensionality and compare the values at `p`. Simplify using `[act, Matrix.scalar_apply, Matrix.diagonal_apply, mul_comm]`. Rewrite using `[hact, Q.2 (fun k => (s k : ℂ)) x]`. Simplify using the standard rewrite rules.
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
Use `Units.ext ?_` and prove the remaining obligations. Rewrite using `[invT_val, ← map_inv]`. Conclude with `Matrix.diagonal_transpose _`.
-/
private theorem invT_scal {d : ℕ} (s : ℂˣ) :
    invT ℂ d (Matrix.GeneralLinearGroup.scalar (Fin d) s) = Matrix.GeneralLinearGroup.scalar (Fin d) s⁻¹ := by
  refine Units.ext ?_
  rw [invT_val, ← map_inv]
  exact Matrix.diagonal_transpose _

/- English proof (translation)
Introduce `I _ s`. Use `⟨fun j => ?_, fun n e => ?_⟩` and prove the remaining obligations. Establish `hd : dbl 3 (fun v ↦ Matrix.GeneralLinearGroup.scalar (Fin 3) (s v)) = fun k => Matrix.GeneralLinearGroup.scalar (Fin 3) (if k.2 then (s k.1)⁻¹ else s k.1)`. Use function extensionality and compare the values at `k`. Take `⟨v, b⟩` from `k`.

Apply the tactic sequence `cases b <;> simp [dbl, invT_scal]`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `P`. Use function extensionality and compare the values at `S`. Rewrite using `[repG_apply, Module.End.one_apply]`.

Express the relevant statement in the definitionally equal form `mRep 3 (fun k => dg j S k.1) (dbl 3 _) (P S) = P S`. Rewrite using `[hd, mRep_scal]`. Use `one_smul ℂ (P S)` and compare the differences between its conclusion and the goal. Rewrite using `[Fintype.prod_prod_type]`. Apply `Finset.prod_eq_one` to reduce the goal to its premises.

Introduce `v _`. Rewrite using `[Fintype.prod_bool]`. Simplify using the standard rewrite rules. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `P`.

Rewrite using `[repD_apply, LinearMap.smul_apply, mRep_scal, smul_smul, LinearMap.smul_apply, Module.End.one_apply]`. Use `congr 1`. Simplify using `only [detE, MonoidHom.coe_mk, OneHom.coe_mk, Units.coe_prod, Units.val_zpow_eq_zpow_val]`. Simplify using the standard rewrite rules. Rewrite using `[← Finset.prod_mul_distrib]`.

Use `Finset.prod_congr rfl fun v _ => ?_` and prove the remaining obligations. Establish `ha : (s v : ℂ) ≠ 0` using `(s v).ne_zero`. Rewrite using `[zpow_add₀ ha, zpow_mul, zpow_natCast, mul_comm]`. Use `norm_cast`.
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
