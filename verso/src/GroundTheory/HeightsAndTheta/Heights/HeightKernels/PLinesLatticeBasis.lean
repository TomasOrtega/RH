import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsLines
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

/- English proof (translation)
Introduce `V _ _ _ ι _ hcard M hM`. Set `b0` to `Module.Free.chooseBasis ℤ M`. Set `B : Module.Basis (Module.Free.ChooseBasisIndex ℤ M) ℚ V` to `b0.extendOfIsLattice ℚ`. Establish `hc : Fintype.card (Module.Free.ChooseBasisIndex ℤ M) = Fintype.card ι`. Rewrite using `[hcard, Module.finrank_eq_card_basis B]`.

Set `e` to `Fintype.equivOfCardEq hc`. Use `⟨B.reindex e, ?_⟩` and prove the remaining obligations. Rewrite using `[Module.Basis.range_reindex]`. Establish `hB : Set.range B = M.subtype '' Set.range b0`. Rewrite using `[← Set.range_comp]`.

Use extensionality with `x`. Simplify using `[B, Module.Basis.extendOfIsLattice_apply]`. Rewrite using `[hB, ← Submodule.map_span, b0.span_eq, Submodule.map_top, Submodule.range_subtype]`.
-/
theorem LinesLatticeBasis.proof : LinesLatticeBasis.Statement := by
  intro V _ _ _ ι _ hcard M hM
  let b0 := Module.Free.chooseBasis ℤ M
  let B : Module.Basis (Module.Free.ChooseBasisIndex ℤ M) ℚ V := b0.extendOfIsLattice ℚ
  have hc : Fintype.card (Module.Free.ChooseBasisIndex ℤ M) = Fintype.card ι := by
    rw [hcard, Module.finrank_eq_card_basis B]
  let e := Fintype.equivOfCardEq hc
  refine ⟨B.reindex e, ?_⟩
  rw [Module.Basis.range_reindex]
  have hB : Set.range B = M.subtype '' Set.range b0 := by
    rw [← Set.range_comp]
    ext x
    simp [B, Module.Basis.extendOfIsLattice_apply]
  rw [hB, ← Submodule.map_span, b0.span_eq, Submodule.map_top, Submodule.range_subtype]

end GroundTheory.Heights₂.Heights
