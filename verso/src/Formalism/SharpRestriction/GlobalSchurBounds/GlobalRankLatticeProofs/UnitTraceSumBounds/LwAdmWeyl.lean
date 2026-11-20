import Formalism.SharpRestriction.GlobalSchurBounds.AdmittedWeylDimension
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeWeylDS

noncomputable section

namespace Formalism.MainNotions.Ext.Lw

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Reduce the equality to equality of the corresponding arguments. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem weyl_dimension_formula_holds (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.StandardLattice.AdmittedWeylDimension D := by
  intro k u H _ _ π hHC
  obtain ⟨_, _, hU, hK⟩ := hHC
  have hU' : Formalism.MainNotions.S.IsURepOn (Formalism.REAL.Kset (Formalism.MainNotions.S.allPos k)) π :=
    ReciprocityTheory.ChartRestriction.DS.HW.hw_isURepOn_mono (ReciprocityTheory.ChartRestriction.DS.HW.hw_kset_subset _) hU
  have h := weylForU_closed k (Formalism.QuantumDeterminants.lowK (Formalism.MainNotions.S.allPos k) u) H π ⊤ hU' hK
  rw [finrank_top] at h
  rw [h]
  unfold Formalism.MainNotions.StandardLattice.dimV Formalism.MainNotions.StandardLattice.facProd Formalism.MainNotions.StandardLattice.vand
  congr 1
  refine Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl fun b _ => ?_
  simp only [Formalism.QuantumDeterminants.lowK, Pi.add_apply, Pi.sub_apply, ReciprocityTheory.ChartRestriction.DS.HW.hw_rhoN_allPos,
    ReciprocityTheory.ChartRestriction.DS.HW.hw_rhoC_allPos]
  ring

end Formalism.MainNotions.Ext.Lw
