import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.StatementD
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.ThmBGaussOrthOf

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.Top

open CAux

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem ThmBInt_of (hC : CalcP) (hS : ShapeCM) : ThmBInt := by
  intro dK L _ hmod hcm p _ h5 hd ι hW O _ _ τ hτ
  obtain ⟨hFr, hF1, hall, hbin⟩ := hC dK L hmod hcm p h5 ι hW
  obtain ⟨-, hu, -⟩ := frame L ι hW
  exact Formalism.L2.Th1.G.intDThmB ℂ_[p] _ _ _ dK hFr hu hF1 (hS dK L hmod hcm p hd ι hW)
    (norm_pos_iff.mpr (d_ne hmod)) (norm_d_lt hd) (norm_two (ne_two hmod hd)) O τ
    (fun α => (hall _ _ (hτ α)).1)
    (fun z hz => hbin _ (by have := hτ z; rwa [hz] at this))
    (fun α => (hall _ _ (hτ α)).2.1) (fun α => (hall _ _ (hτ α)).2.2)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem ThmBGaussInt_of (hC : CalcP) (hS : ShapeCM) : ThmBGaussInt := by
  intro dK L hsq hmod hcm p _ h5 hd ι hW O _ _ τ hτ
  obtain ⟨hFr, hF1, hall, hbin⟩ := hC dK L hmod hcm p h5 ι hW
  obtain ⟨-, hu, -⟩ := frame L ι hW
  have hSh := hS dK L hmod hcm p hd ι hW
  have hSh' : Formalism.L2.Th1.G.ShapeAt (Formalism.L2.Th1.A.logSer (Formalism.L2.Th1.E.curveL p L ι))
      (Formalism.L2.Th1.A.expSer (Formalism.L2.Th1.E.curveL p L ι)) (phC p L ι) p := by
    refine ⟨?_, hSh.2⟩
    rw [← norm_d_eq hsq hd]
    exact hSh.1
  exact Formalism.L2.Th1.G.intDThmBGauss p _ _ _ hFr hu hF1 hSh' (norm_two (ne_two hmod hd)) O τ
    (fun α => (hall _ _ (hτ α)).1)
    (fun z hz => hbin _ (by have := hτ z; rwa [hz] at this))
    (fun α => (hall _ _ (hτ α)).2.1) (fun α => (hall _ _ (hτ α)).2.2)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem IntOpInt_of (hC : CalcP) (hJ : JetsCM) : IntOpInt := by
  intro dK L _ hmod hcm p _ h5 hd ι hW O _ _ τ hτ
  obtain ⟨hFr, hF1, hall, hbin⟩ := hC dK L hmod hcm p h5 ι hW
  obtain ⟨-, hu, -⟩ := frame L ι hW
  exact Formalism.L2.Th1.G.intUnram ℂ_[p] _ _ _ hFr hu hF1 (hJ dK L hmod hcm p (by omega) hd ι hW) O τ
    (fun α => (hall _ _ (hτ α)).1)
    (fun z hz => hbin _ (by have := hτ z; rwa [hz] at this))
    (fun α => (hall _ _ (hτ α)).2.1) (fun α => (hall _ _ (hτ α)).2.2)

end Formalism.L2.Th1.Top
