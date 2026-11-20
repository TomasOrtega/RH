import Formalism.LocalToGlobal.InertKernelTheory.StatementIota
import ReciprocityTheory.ReductiveGroups.LatticeEmbeddings.IotaPlaceB

noncomputable section

namespace Formalism.L2.KerInert

open NumberField Formalism.BasicNotions

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem lattice_extension : LamExt := by
  intro p _ lam
  have : Algebra.IsAlgebraic ℚ Formalism.MainNotions.TaylorLogMetric.Qbar := algebraicClosure.isAlgebraic ℚ ℂ
  have hR : Cardinal.mk Formalism.MainNotions.TaylorLogMetric.Qbar ≤ Cardinal.aleph0 :=
    (Algebra.IsAlgebraic.cardinalMk_le_max ℚ Formalism.MainNotions.TaylorLogMetric.Qbar).trans
      (max_le Cardinal.mk_le_aleph0 le_rfl)
  obtain ⟨σ, hσ⟩ := ReciprocityTheory.ChartRestriction.B3.iop_extEmb (algebraMap Formalism.MainNotions.TaylorLogMetric.Qbar ℂ) lam hR
    (by simp [Cardinal.mk_complex, Cardinal.aleph0_lt_continuum])
    (Cardinal.mk_complex.trans (ReciprocityTheory.ChartRestriction.T1.lat_mk_Cp p).symm)
  exact ⟨σ, fun x => hσ x⟩

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem lattice_embedding : LamCIota := by
  intro p _ lam ι h
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · unfold Formalism.MainNotions.TaylorLogMetric.lamC
    rw [dif_pos hx]
    exact (h ⟨x, hx⟩).symm
  · unfold Formalism.MainNotions.TaylorLogMetric.lamC
    rw [dif_neg hx]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. A detailed English derivation is pending.
-/
theorem power_series_embedding : PSerIota := by
  intro D N N' p _ lam ι h G hG
  ext α
  rw [MvPowerSeries.coeff_map]
  change Formalism.MainNotions.TaylorLogMetric.lamC lam (Formalism.MainNotions.TaylorLogMetric.taylor D G α) = ι (Formalism.MainNotions.TaylorLogMetric.taylor D G α)
  exact (lattice_embedding p lam ι h).1 _ (hG α)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem lamExt : LamExt := lattice_extension
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem lamCIota : LamCIota := lattice_embedding
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem pSerIota : PSerIota := power_series_embedding

end Formalism.L2.KerInert
