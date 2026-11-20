import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.WavePacketL1L2
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.MulVecApplyOfRow

open Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S WlocSk.UnitaryGroupBasics

noncomputable section

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components. Fix the arbitrary inputs or assume the hypotheses.

Supply the required witnesses or components. Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components.
-/
theorem subgroup_hypothesis_holds : WlocSk.SGrp := by
  intro k r z c hz _
  refine ⟨fun h hh => hh.1, fun m hm => hm.1, ?_, ?_, ?_⟩
  · intro h hh h' hh'
    exact ⟨uw_mul hh hh', uw_inv hh, Matrix.mul_nonsing_inv _ (isUnit_of_uh hh.1)⟩
  · intro m hm m' hm'
    exact ⟨mem_n_mul hm hm', mem_n_inv hm, Matrix.mul_nonsing_inv _ (isUnit_of_uh hm.1),
      psiGen_mul z c hz hm hm', psiGen_norm z c m⟩
  · intro h hh m hm
    exact ⟨uw_conj_mem hh hm, psiGen_conj z c hh⟩
