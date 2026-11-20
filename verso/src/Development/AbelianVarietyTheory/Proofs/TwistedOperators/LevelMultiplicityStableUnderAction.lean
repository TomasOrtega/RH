import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IdemOfIsPrimeIdem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelGroupActionIsAction

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FlagAct

/- English proof (translation)
Introduce `D V S θ M β L g0 T hT`. Distinguish the cases in `hk : ∃ κ, IsLevelLift V β L g0 κ`. Establish `hκ` using `hk.choose_spec`. Rewrite `hT` using `[GlobalTheory.MultMem.mem_mult_iff]`. Establish `hact : ∀ v, ((levChi V β (flagL L) hk.choose)⁻¹ • heckeOn M {hk.choose} T) v = actG0 V β L g0 (T v)`.

Introduce `v`. Unfold `actG0`. Rewrite using `[dif_pos hk]`. Use function extensionality and compare the values at `g`. Simplify using `[heckeOn, postOn_apply, heckeLin_apply]`.

Establish `h0 : IsMultMap θ M ∅ (levChi V β (flag1L L)) ((levChi V β (flagL L) hk.choose)⁻¹ • heckeOn M {hk.choose} T)`. Rewrite using `[← GlobalTheory.MultMem.mem_mult_iff]`. Conclude with `Submodule.smul_mem _ _ ((GlobalTheory.MultMem.mem_mult_iff ..).2 (GlobalTheory.SphericalOps.isMultMap_single hT hκ.1))`. Use `⟨_, Submodule.subset_span ⟨h0.aut, h0.cusp, fun v k hk' g => ?_, h0.equiv, h0.cont⟩, hact⟩` and prove the remaining obligations. Rewrite using `[hact]`.

Conclude with `GlobalTheory.FlagAction.act_hasType (fun k hk => hT.lev v k hk) hk k hk' g`. Use `⟨0, Submodule.zero_mem _, fun v => ?_⟩` and prove the remaining obligations. Unfold `actG0`. Rewrite using `[dif_neg hk]`. Both sides reduce to the same expression.
-/
theorem finiteGroupAction_preserves_principalFlagMultiplicity : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S) (β : GL (Fin V.rank) (Lev.EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) (g0 : Formalism.L2.DIV.G0 L.Pg L.r), ∀ T ∈ Mult θ M (levG V β (flag1L L) : Set (GA D V)) (levChi V β (flag1L L)), ∃ T' ∈ Mult θ M (levG V β (flag1L L) : Set (GA D V)) (levChi V β (flag1L L)), ∀ v, T' v = actG0 V β L g0 (T v) := by
  intro D V S θ M β L g0 T hT
  by_cases hk : ∃ κ, IsLevelLift V β L g0 κ
  · have hκ := hk.choose_spec
    rw [GlobalTheory.MultMem.mem_mult_iff] at hT
    have hact : ∀ v, ((levChi V β (flagL L) hk.choose)⁻¹ • heckeOn M {hk.choose} T) v =
        actG0 V β L g0 (T v) := by
      intro v
      unfold actG0
      rw [dif_pos hk]
      funext g
      simp [heckeOn, postOn_apply, heckeLin_apply]
    have h0 : IsMultMap θ M ∅ (levChi V β (flag1L L))
        ((levChi V β (flagL L) hk.choose)⁻¹ • heckeOn M {hk.choose} T) := by
      rw [← GlobalTheory.MultMem.mem_mult_iff]
      exact Submodule.smul_mem _ _
        ((GlobalTheory.MultMem.mem_mult_iff ..).2 (GlobalTheory.SphericalOps.isMultMap_single hT hκ.1))
    refine ⟨_, Submodule.subset_span ⟨h0.aut, h0.cusp, fun v k hk' g => ?_, h0.equiv, h0.cont⟩, hact⟩
    rw [hact]
    exact GlobalTheory.FlagAction.act_hasType (fun k hk => hT.lev v k hk) hk k hk' g
  · refine ⟨0, Submodule.zero_mem _, fun v => ?_⟩
    unfold actG0
    rw [dif_neg hk]
    rfl

end GlobalTheory.FlagAct
