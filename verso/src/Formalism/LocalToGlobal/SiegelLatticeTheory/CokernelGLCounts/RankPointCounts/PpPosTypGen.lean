import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocalFactorsPosTypicalGeneral
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcValVolOrdFull
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.ParabolicVolume

noncomputable section

open scoped Classical TensorProduct

namespace Formalism.L2.SG.Pf.ProdConvCut2

open MeasureTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcVal
  Formalism.L2.SG.Pf.NcVal.VolOrdW

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Establish `hTF` using `Formalism.L2.SG.Pf.typFacts_holds X hb u u' ⟨v, hv⟩`. Establish `hnt : X.B.I.cm.sig ≠ AlgHom.id X.B.I.F X.B.I.E`. Establish `hmax : v.asIdeal.IsMaximal` using `v.isMaximal`. Take `⟨P, hPmax, -⟩` from `Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 X.B.I.E) v.asIdeal (by`. Rewrite using `[(RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective (𝓞 X.B.I.F) (𝓞 X.B.I.E))]`.

Conclude with `bot_le)`. Take `⟨θ, t, htθ, hnot⟩` from `X.B.I.cm.cmUnram.2.2 P hPmax`. Introduce `h`. Apply `hnot` to reduce the goal to its premises. Establish `hθ : (t : X.B.I.E) = θ`.

Establish `h1 : X.B.I.cm.sig (θ : X.B.I.E) = star (θ : X.B.I.E)` using `rfl`. Rewrite `h1` using `[h, AlgHom.id_apply]`. Establish `htθ' : (t : X.B.I.E) = star (θ : X.B.I.E)` using `htθ`. Rewrite using `[htθ', ← h1]`. Establish `: θ - t = 0` using `by ext; simp [hθ]`.

Rewrite using `[this]`. Conclude with `P.zero_mem`. Establish `hid : ∃ x : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E, x * x = x ∧ x ≠ 0 ∧ x ≠ 1`. Assume the negation of the conclusion as `h`. Establish `he` using `hTF.2.2.1`.

Unfold `etaV at he`. Rewrite `he` using `[if_neg h]`. Conclude with `absurd he (by decide)`. Establish `hS : PI.UnitaryGroupMassFormula.LocJacTyp.SplitHyp X.B.I.cm.sig v` using `⟨X.B.I.cm.deg2, hnt, hid⟩`. Establish `hg : 0 < gAt X v` using `hTF.1.pos`.

Establish `hA` using `SdW.sdFromAnn_holds ψ v (dV v) hψ X.B.I.cm.deg2 (dV_ne_zero v) (annX_of X ψ Formalism.L2.SG.Pf.conductor_inverse_different hψ hs v) Unit`. Use `haveI := hA.1`. Establish `hP` using `PI.UnitaryGroupMassFormula.LocJacTyp.parabolic_volume X.B.I.cm.sig v (gAt X v) D.R.rS (Tw u) (Tw u') (absV v (dV v) ^ Fintype.card Unit) hS hg hTF.2.2.2.1 (sdE (E := X.B.I.E) ψ v Unit) hA.1 hA.2.2 l`. Establish `hP' : ((sdE (E` using `X.B.I.E) ψ v Unit) ((fun c : Unit → Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E => c ()) ⁻¹' PPTyp X.B.I.cm.sig v (gAt X v) D.R.rS (Tw u) (Tw u') l)).toReal = absV v (dV v) ^ Fintype.card Unit * PI.LocJacTyp.absV v (gAt X v : Fv X.B.I.F v) ^ 3 * (PI.LocJacTyp.absV v (PI.LocJacTyp.alp v D.R.r …`. Unfold `PPX volC`.

Rewrite using `[if_pos hv, hP']`. Establish `hd : 0 < absV v (dV v)` using `absV_pos v (dV_ne_zero v)`. Establish `hgv : (gAt X v : Fv X.B.I.F v) ≠ 0` using `by exact_mod_cast hg.ne'`. Establish `h1 : 0 < PI.LocJacTyp.absV v (gAt X v : Fv X.B.I.F v)` using `PI.UnitaryGroupMassFormula.LocJacTyp.absV_pos v hgv`. Establish `ha : PI.LocJacTyp.alp v D.R.rS l ≠ 0` using `alp_ne_zero v D.R.rS l`.

Establish `h2 : 0 < PI.LocJacTyp.absV v (PI.LocJacTyp.alp v D.R.rS l)` using `PI.UnitaryGroupMassFormula.LocJacTyp.absV_pos v ha`. Check the signs of the components of the expression.
-/
theorem pp_pos_typ_gen {D : D7} (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (ψ : AddChar (AF X.B.I.F) ℂ)
    (hψ : IsCharAF X.B.I.F ψ) (hs : IsStdChar ψ) (u u' : D.what₂.Word) (v : PlX X) (hv : TypAt X v)
    (l : Fin (D.R.rS + 1)) : 0 < PPX X u u' ψ l v := by
  have hTF := Formalism.L2.SG.Pf.typFacts_holds X hb u u' ⟨v, hv⟩

  have hnt : X.B.I.cm.sig ≠ AlgHom.id X.B.I.F X.B.I.E := by
    have hmax : v.asIdeal.IsMaximal := v.isMaximal
    obtain ⟨P, hPmax, -⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 X.B.I.E) v.asIdeal
      (by
        rw [(RingHom.injective_iff_ker_eq_bot _).mp
          (FaithfulSMul.algebraMap_injective (𝓞 X.B.I.F) (𝓞 X.B.I.E))]
        exact bot_le)
    obtain ⟨θ, t, htθ, hnot⟩ := X.B.I.cm.cmUnram.2.2 P hPmax
    intro h
    apply hnot
    have hθ : (t : X.B.I.E) = θ := by
      have h1 : X.B.I.cm.sig (θ : X.B.I.E) = star (θ : X.B.I.E) := rfl
      rw [h, AlgHom.id_apply] at h1
      have htθ' : (t : X.B.I.E) = star (θ : X.B.I.E) := htθ
      rw [htθ', ← h1]
    have : θ - t = 0 := by ext; simp [hθ]
    rw [this]
    exact P.zero_mem

  have hid : ∃ x : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E, x * x = x ∧ x ≠ 0 ∧ x ≠ 1 := by
    by_contra h
    have he := hTF.2.2.1
    unfold etaV at he
    rw [if_neg h] at he
    exact absurd he (by decide)
  have hS : PI.UnitaryGroupMassFormula.LocJacTyp.SplitHyp X.B.I.cm.sig v := ⟨X.B.I.cm.deg2, hnt, hid⟩
  have hg : 0 < gAt X v := hTF.1.pos
  have hA := SdW.sdFromAnn_holds ψ v (dV v) hψ X.B.I.cm.deg2 (dV_ne_zero v)
    (annX_of X ψ Formalism.L2.SG.Pf.conductor_inverse_different hψ hs v) Unit
  haveI := hA.1
  have hP := PI.UnitaryGroupMassFormula.LocJacTyp.parabolic_volume X.B.I.cm.sig v (gAt X v) D.R.rS (Tw u) (Tw u')
    (absV v (dV v) ^ Fintype.card Unit) hS hg hTF.2.2.2.1 (sdE (E := X.B.I.E) ψ v Unit) hA.1 hA.2.2 l
  have hP' : ((sdE (E := X.B.I.E) ψ v Unit) ((fun c : Unit → Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E => c ()) ⁻¹'
      PPTyp X.B.I.cm.sig v (gAt X v) D.R.rS (Tw u) (Tw u') l)).toReal =
      absV v (dV v) ^ Fintype.card Unit * PI.LocJacTyp.absV v (gAt X v : Fv X.B.I.F v) ^ 3 *
        (PI.LocJacTyp.absV v (PI.LocJacTyp.alp v D.R.rS l) ^ 4)⁻¹ := hP
  unfold PPX volC
  rw [if_pos hv, hP']
  have hd : 0 < absV v (dV v) := absV_pos v (dV_ne_zero v)
  have hgv : (gAt X v : Fv X.B.I.F v) ≠ 0 := by exact_mod_cast hg.ne'
  have h1 : 0 < PI.LocJacTyp.absV v (gAt X v : Fv X.B.I.F v) := PI.UnitaryGroupMassFormula.LocJacTyp.absV_pos v hgv
  have ha : PI.LocJacTyp.alp v D.R.rS l ≠ 0 := alp_ne_zero v D.R.rS l
  have h2 : 0 < PI.LocJacTyp.absV v (PI.LocJacTyp.alp v D.R.rS l) := PI.UnitaryGroupMassFormula.LocJacTyp.absV_pos v ha
  positivity

/- English proof (translation)
The claim follows from `pp_pos_typ_gen T.X T.hb T.ψ T.ψ_char T.ψ_std u u' v hv l`.
-/
theorem pp_pos_typ {D : D7} (T : Formalism.L2.SG.SpectralTiesReal.STies D) (u u' : D.what₂.Word) (v : PlX T.X) (hv : TypAt T.X v)
    (l : Fin (D.R.rS + 1)) : 0 < PPX T.X u u' T.ψ l v :=
  pp_pos_typ_gen T.X T.hb T.ψ T.ψ_char T.ψ_std u u' v hv l

end Formalism.L2.SG.Pf.ProdConvCut2
