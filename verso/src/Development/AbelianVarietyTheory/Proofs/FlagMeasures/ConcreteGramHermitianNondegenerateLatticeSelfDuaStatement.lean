import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ConcreteGramHermitianNondegenerateLatticeSelfDua
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Direct
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CovDom.herm_selfDual` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FConcreteGramHermitianNondegenerateLatticeSelfDua.lean&line=37#L37)
-/
theorem _root_.GlobalTheory.T.concrete_gram_hermitian_nondegenerate_lattice_selfDual : ∀ (D : D7) (X : HidaSetting D), Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsHermND D.sp.cm.sig (Jc X) ∧ GlobalTheory.SgGlob.SelfDual (D.sp.cm.sig : D.host.E →+* D.host.E) (Jc X) (Lc X) := by
  first | exact @GlobalTheory.CovDom.herm_selfDual | exact GlobalTheory.CovDom.herm_selfDual | (intros; apply GlobalTheory.CovDom.herm_selfDual <;> assumption)
