import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.NormOneIsCoboundaryUnramifiedQuadratic

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Simplify using the standard rewrite rules. Supply the required witnesses or components.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.V.Z.Sym.Loc.sqrtO : UpperTheory.V.Z.Sym.Loc.SqrtO := by
  intro O K _ _ _ _ _ Δ hL x r₀ hr hx
  haveI := hL.compl
  haveI := IsAdicComplete.henselianRing O (IsLocalRing.maximalIdeal O)
  have hmon : (Polynomial.X ^ 2 - Polynomial.C x : Polynomial O).Monic :=
    Polynomial.monic_X_pow_sub_C x two_ne_zero
  have h0 : Polynomial.eval r₀ (Polynomial.X ^ 2 - Polynomial.C x) ∈ IsLocalRing.maximalIdeal O := by
    rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
    have h := (IsLocalRing.maximalIdeal O).neg_mem hx
    rwa [neg_sub] at h
  have h1 : IsUnit ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal O))
      (Polynomial.eval r₀ (Polynomial.derivative (Polynomial.X ^ 2 - Polynomial.C x)))) := by
    apply IsUnit.map
    simp
    exact ⟨by simpa [one_add_one_eq_two] using hL.two, hr⟩
  obtain ⟨a, ha, ha'⟩ := HenselianRing.is_henselian _ hmon r₀ h0 h1
  refine ⟨a, ?_, ha'⟩
  have h := ha.eq_zero
  rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at h
  exact sub_eq_zero.mp h
