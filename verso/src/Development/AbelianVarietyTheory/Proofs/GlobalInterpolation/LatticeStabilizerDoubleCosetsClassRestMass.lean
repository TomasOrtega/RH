import Mathlib
import Formalism.LocalToGlobal.GlobalTheory.GL5.PClassDecomp
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DoubleCosetsMassLevel
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefClassDecompIff
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ClassRestObj

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities.

Supply the required witnesses or components.
-/
theorem defClassRest : ∀ D : D7, DefClassRest D := by
  intro D W hW hsig
  obtain ⟨⟨θ, hθ⟩, A, hA⟩ := GlobalTheory.DecompCompare.exists_data D W hW hsig
  have hK : KSub D W W.rank 0 θ A = StabFin.SFin D.sp.cm.sig W.gram (L0c D W) :=
    SetLike.coe_injective (StabFin.KSub_eq D W hW hsig θ hθ A hA)
  obtain ⟨-, n, g, hcov, hdisj, -, hsum⟩ := GlobalTheory.DefiniteDecompObj.doubleCosets_mass D W hW hsig θ hθ A hA
  rw [hK] at hcov hdisj hsum
  exact ⟨n, g, hcov, hdisj, hsum⟩

end GlobalTheory.ClassRestObj
