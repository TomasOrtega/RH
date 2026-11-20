import Formalism.LocalToGlobal.InertKernelTheory.StatementIota
import ReciprocityTheory.ReductiveGroups.LatticeEmbeddings.IotaPlaceB

noncomputable section

namespace Formalism.L2.KerInert

open NumberField Formalism.BasicNotions

/- English proof (translation)
Introduce `p _ lam`. Establish `: Algebra.IsAlgebraic ℚ Formalism.MainNotions.TaylorLogMetric.Qbar` using `algebraicClosure.isAlgebraic ℚ ℂ`. Establish `hR : Cardinal.mk Formalism.MainNotions.TaylorLogMetric.Qbar ≤ Cardinal.aleph0` using `(Algebra.IsAlgebraic.cardinalMk_le_max ℚ Formalism.MainNotions.TaylorLogMetric.Qbar).trans (max_le Cardinal.mk_le_aleph0 le_rfl)`. Take `⟨σ, hσ⟩` from `ReciprocityTheory.ChartRestriction.B3.iop_extEmb (algebraMap Formalism.MainNotions.TaylorLogMetric.Qbar ℂ) lam hR (by simp [Cardinal.mk_complex, Cardinal.aleph0_lt_continuum]) (Cardinal.mk_complex.trans (ReciprocityTheory.ChartRestriction.T1.lat_mk_Cp p).symm)`. Conclude with `⟨σ, fun x => hσ x⟩`.
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
Introduce `p _ lam ι h`. Use `⟨fun x hx => ?_, fun x hx => ?_⟩` and prove the remaining obligations. Unfold `Formalism.MainNotions.TaylorLogMetric.lamC`. Rewrite using `[dif_pos hx]`. Conclude with `(h ⟨x, hx⟩).symm`.

Unfold `Formalism.MainNotions.TaylorLogMetric.lamC`. Rewrite using `[dif_neg hx]`.
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
Introduce `D N N' p _ lam ι h G hG`. Use extensionality with `α`. Rewrite using `[MvPowerSeries.coeff_map]`. Express the relevant statement in the definitionally equal form `Formalism.MainNotions.TaylorLogMetric.lamC lam (Formalism.MainNotions.TaylorLogMetric.taylor D G α) = ι (Formalism.MainNotions.TaylorLogMetric.taylor D G α)`. Conclude with `(lattice_embedding p lam ι h).1 _ (hG α)`.
-/
theorem power_series_embedding : PSerIota := by
  intro D N N' p _ lam ι h G hG
  ext α
  rw [MvPowerSeries.coeff_map]
  change Formalism.MainNotions.TaylorLogMetric.lamC lam (Formalism.MainNotions.TaylorLogMetric.taylor D G α) = ι (Formalism.MainNotions.TaylorLogMetric.taylor D G α)
  exact (lattice_embedding p lam ι h).1 _ (hG α)

/- English proof (translation)
The claim follows from `lattice_extension`.
-/
theorem lamExt : LamExt := lattice_extension
/- English proof (translation)
The claim follows from `lattice_embedding`.
-/
theorem lamCIota : LamCIota := lattice_embedding
/- English proof (translation)
The claim follows from `power_series_embedding`.
-/
theorem pSerIota : PSerIota := power_series_embedding

end Formalism.L2.KerInert
