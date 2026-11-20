import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.FormsFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.TraceFibreCardinality.OrbReps

open UpperTheory.V.Z.Sym MulAction in
/- English proof (translation)
Introduce `T G _ _ ι C θ U f δ hinv hδ hC hcov`. Establish `h` using `orbReps T G ι C θ U f δ hinv hδ Unit {()} (fun _ => 1) (fun i _ j _ _ _ _ _ => rfl) (fun y hy => by`. Take `⟨t, u, hu, e⟩` from `hcov y hy`. Conclude with `⟨t, (), Finset.mem_singleton_self _, u, hu, by simpa using e⟩)`. Rewrite using `[h, Finset.sum_singleton]`.

Establish `hr : (Subgroup.comap ι (stabilizer G ((1 : G) : G ⧸ U))).relIndex C = 1`. Rewrite using `[Subgroup.relIndex_eq_one]`. Introduce `c hc`. Rewrite using `[Subgroup.mem_comap, mem_stabilizer_iff, MulAction.Quotient.smul_mk, QuotientGroup.eq]`. Simplify using `using hC (Subgroup.mem_map_of_mem ι hc)`.

Rewrite using `[hr]`. Simplify using the standard rewrite rules.
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
