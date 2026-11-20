import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelOpenCompactSmooth
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.LevelOK

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. By extensionality, compare the relevant components.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem levOK_all : ∀ D : D7, LevOK D := by
  intro D V β L
  obtain ⟨hO, hC, hS, U, hU, hk⟩ := GlobalTheory.Mem.LevelSmooth.level_open_compact_smooth D V β L
  refine ⟨⟨hC, ?_⟩, U, hU, fun k hkU hkG => ?_⟩
  · have : (((Lev.levA V (lev D.sp.cm (HSpace.gram V) β L)).subgroupOf (GfC V)) : Set (GfC V)) =
        Subtype.val ⁻¹' ((Subgroup.comap (Lev.finE V) (lev D.sp.cm (HSpace.gram V) β L)) : Set (GA D V)) := by
      ext x; simp [Subgroup.mem_subgroupOf, Lev.levA, x.2]
    rw [this]; exact hO.preimage continuous_subtype_val
  · obtain ⟨h1, h2⟩ := hk k hkU hkG
    exact ⟨h1, h2⟩
end GlobalTheory.Mem.LevelOK
