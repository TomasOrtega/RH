import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsScalarPreservesIntegralMatricesSubst
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LawLoc
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod GlobalTheory.LocOm
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LocOm.enl_scalar_denominator` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FExistsScalarPreservesIntegralMatricesSubst.lean&line=29#L29)
-/
theorem _root_.GlobalTheory.T.exists_scalar_preservesIntegralMatricesSubst : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (gk : GL Y' k) (hk : GL Y k), ∃ c : kˣ, ∀ zk : GL Y k, (zk : Matrix Y Y k) = (c : k) • (1 : Matrix Y Y k) → Enl gk (hk * zk⁻¹) ∧ Enl (1 : GL Y' k) zk⁻¹ := by
  first | exact @GlobalTheory.LocOm.enl_scalar_denominator | exact GlobalTheory.LocOm.enl_scalar_denominator | (intros; apply GlobalTheory.LocOm.enl_scalar_denominator <;> assumption)
