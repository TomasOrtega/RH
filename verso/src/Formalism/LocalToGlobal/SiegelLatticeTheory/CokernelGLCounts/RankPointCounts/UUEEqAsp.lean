import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.OmpCoset

noncomputable section

open scoped Classical
open Module Matrix
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.FourierDecayAlt
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.TermOp

namespace Formalism.L2.SG.NGCut.NormalVectorPairings

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Use `le_antisymm ?_ ?_` and prove the remaining obligations. Establish `hX' : F'.fl.X ≤ Asp F.fl F'.fl` using `by rw [← Asp_symm]; exact X_le_Asp F'.fl F.fl`. Establish `hz' : F'.fl.z ∈ Asp F.fl F'.fl` using `by rw [← Asp_symm]; exact z_mem_Asp F'.fl F.fl`. Establish `key : UU Λ F F' ≤ (Asp F.fl F'.fl).restrictScalars (𝓞 D.host.E)`. Unfold `UU`.

Use `sup_le (sup_le (sup_le ?_ ?_) ?_) ?_` and prove the remaining obligations. Introduce `y hy`. Conclude with `X_le_Asp F.fl F'.fl (Submodule.mem_inf.1 hy).2`. Rewrite using `[Submodule.span_le, Set.singleton_subset_iff, hL.2]`. Conclude with `z_mem_Asp F.fl F'.fl`.

Introduce `y hy`. Conclude with `hX' (Submodule.mem_inf.1 hy).2`. Rewrite using `[Submodule.span_le, Set.singleton_subset_iff, hL'.2]`. Conclude with `hz'`. Unfold `UUE spanE`.

Rewrite using `[Submodule.span_le]`. Introduce `x hx`. Conclude with `key hx`. Rewrite using `[Asp, Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`.

Conclude with `PI.PairCorankPos.W.frame_mem_UUE Λ hΛ F F' hL hL' i`.
-/
theorem UUE_eq_Asp {D : D7} {T T' : D.host.E} (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (hΛ : Submodule.IsLattice D.host.E Λ) (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T')
    (hL : IsLift Λ F) (hL' : IsLift Λ F') : UUE Λ F F' = Asp F.fl F'.fl := by
  refine le_antisymm ?_ ?_
  · have hX' : F'.fl.X ≤ Asp F.fl F'.fl := by rw [← Asp_symm]; exact X_le_Asp F'.fl F.fl
    have hz' : F'.fl.z ∈ Asp F.fl F'.fl := by rw [← Asp_symm]; exact z_mem_Asp F'.fl F.fl
    have key : UU Λ F F' ≤ (Asp F.fl F'.fl).restrictScalars (𝓞 D.host.E) := by
      unfold UU
      refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
      · intro y hy
        exact X_le_Asp F.fl F'.fl (Submodule.mem_inf.1 hy).2
      · rw [Submodule.span_le, Set.singleton_subset_iff, hL.2]
        exact z_mem_Asp F.fl F'.fl
      · intro y hy
        exact hX' (Submodule.mem_inf.1 hy).2
      · rw [Submodule.span_le, Set.singleton_subset_iff, hL'.2]
        exact hz'
    unfold UUE spanE
    rw [Submodule.span_le]
    intro x hx
    exact key hx
  · rw [Asp, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact PI.PairCorankPos.W.frame_mem_UUE Λ hΛ F F' hL hL' i

end Formalism.L2.SG.NGCut.NormalVectorPairings
