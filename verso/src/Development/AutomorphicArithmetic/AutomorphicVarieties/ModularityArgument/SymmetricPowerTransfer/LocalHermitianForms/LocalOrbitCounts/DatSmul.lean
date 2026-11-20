import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.NormOneIsCoboundaryUnramifiedQuadratic

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Apply the first step, then apply the next step to every resulting obligation. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Apply the first step, then apply the next step to every resulting obligation. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem UpperTheory.V.Z.Sym.Loc.datSmul : UpperTheory.V.Z.Sym.Loc.DatSmul := by
  intro K _ Δ τ c d m h t
  have hsig : sigL ((t : K) • m) = (t : K) • sigL m := by
    ext <;> simp [sigL]
  have hst : ∀ z : EL Δ τ, star ((t : K) • z) = (t : K) • star z := by
    intro z
    ext <;> simp <;> ring
  refine ⟨h.reg, h.c_ne, h.d_norm, ?_, ?_, ?_⟩
  · rw [Algebra.smul_def]
    exact (t.isUnit.map (algebraMap K (EL Δ τ))).mul h.m_unit
  · rw [hsig, hst, h.m_star]
  · rw [hsig, h.m_sig, smul_mul_assoc, smul_mul_assoc]
