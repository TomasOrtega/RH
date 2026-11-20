import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.FormsFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.TraceFibreCardinality.OrbReps

open UpperTheory.V.Z.Sym MulAction in
/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify to obtain the desired conclusion from the available facts.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem UpperTheory.V.Z.Sym.Tf.orbOne :
    UpperTheory.V.Z.Sym.Tf.OrbOne := by
  intro T G _ _ ι C θ U f δ hinv hδ hC hcov
  have h := orbReps T G ι C θ U f δ hinv hδ Unit {()} (fun _ => 1)
    (fun i _ j _ _ _ _ _ => rfl)
    (fun y hy => by
      obtain ⟨t, u, hu, e⟩ := hcov y hy
      exact ⟨t, (), Finset.mem_singleton_self _, u, hu, by simpa using e⟩)
  rw [h, Finset.sum_singleton]
  have hr : (Subgroup.comap ι (stabilizer G ((1 : G) : G ⧸ U))).relIndex C = 1 := by
    rw [Subgroup.relIndex_eq_one]
    intro c hc
    rw [Subgroup.mem_comap, mem_stabilizer_iff, MulAction.Quotient.smul_mk, QuotientGroup.eq]
    simpa using hC (Subgroup.mem_map_of_mem ι hc)
  rw [hr]
  simp
