import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.StrongApproxN
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.BridgeFinK

noncomputable section

open Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.TypedSets
open Matrix

namespace MassDataMassesW.NBr

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem incAf_finHA {D : Formalism.BasicNotions.D7} (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I)
    (x : X.B.I.Gf) :
    Formalism.L2.SG.Sub.incAf X.B.I.cm.sig X.B.I.J (finHA X hb x) =
      Formalism.UG.bc (Formalism.L2.SG.AdBridge.prF X.B.I)
        (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) X.B.I.cm.sig X.B.I.J
          (Formalism.L2.SG.AdBridge.toHA X.B.I hb (1, x))) := rfl

/- English proof (translation)
Introduce `D X hb x`. Establish `hbr' : X.B.I.fmat x = _` using `(hb.choose_spec (1, x)).2`. Establish `hK : x ∈ X.B.I.Kset ↔ Formalism.L2.SG.AdBridge.toHA X.B.I hb (1, x) ∈ Formalism.L2.SG.AdBridge.KfHA X.B.I`. Use `Iff.trans ?_ (adelic_compact_finite_places X.B.I (Formalism.L2.SG.AdBridge.toHA X.B.I hb (1, x)))` and prove the remaining obligations. Use `show (∀ y, y ∈ X.B.I.Lf ↔ X.B.I.fmat x *ᵥ y ∈ X.B.I.Lf) ↔ _`.

Rewrite using `[hbr']`. Both sides reduce to the same expression. Use `hK.trans ?_` and prove the remaining obligations. Simplify using `only [KX, Formalism.L2.SG.Sub.Kf, Subgroup.mem_iInf, Subgroup.mem_comap, MonoidHom.comp_apply, incAf_finHA]`. Both sides reduce to the same expression.
-/
theorem bridgeK_holds : BridgeK := by
  intro D X hb x
  have hbr' : X.B.I.fmat x = _ := (hb.choose_spec (1, x)).2
  have hK : x ∈ X.B.I.Kset ↔
      Formalism.L2.SG.AdBridge.toHA X.B.I hb (1, x) ∈ Formalism.L2.SG.AdBridge.KfHA X.B.I := by
    refine Iff.trans ?_ (adelic_compact_finite_places X.B.I (Formalism.L2.SG.AdBridge.toHA X.B.I hb (1, x)))
    show (∀ y, y ∈ X.B.I.Lf ↔ X.B.I.fmat x *ᵥ y ∈ X.B.I.Lf) ↔ _
    rw [hbr']
    rfl
  refine hK.trans ?_
  simp only [KX, Formalism.L2.SG.Sub.Kf, Subgroup.mem_iInf, Subgroup.mem_comap, MonoidHom.comp_apply,
    incAf_finHA]
  rfl

end MassDataMassesW.NBr
