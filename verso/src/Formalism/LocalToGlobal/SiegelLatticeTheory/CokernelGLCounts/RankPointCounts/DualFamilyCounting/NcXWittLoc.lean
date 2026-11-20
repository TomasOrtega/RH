import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcXLocSB
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcXWSp
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcXSplSPf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.HformSmulLeft

noncomputable section

namespace Formalism.L2.SG.Pf.NcX.WittLocPf

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain
open scoped TensorProduct

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ n J a X0 hCM hJ hdet v X hX`. Establish `: FiniteDimensional F E` using `Module.Finite.of_restrictScalars_finite ℚ F E`. Use `set Y := ratTup (F := F) (Fv F v) X0 with hYdef`. Establish `hYG : gramR (Fv F v) σ J Y = (gramE σ J X0).map (inclR (F` using `F) (Fv F v)) := PI.VolStabW.LocPosW.gramR_ratTup (Fv F v) σ J X0`. Establish `hunit : IsUnit ((gramE σ J X0).map (inclR (F` using `F) (Fv F v))).det := by`.

Establish `e : ((gramE σ J X0).map (inclR (F` using `F) (Fv F v))).det = inclR (F := F) (Fv F v) (gramE σ J X0).det := (RingHom.map_det (inclR (F := F) (Fv F v)) (gramE σ J X0)).symm`. Rewrite using `[e]`. Conclude with `(Ne.isUnit hdet).map (inclR (F := F) (Fv F v))`. Establish `hYind : LinearIndependent (Fv F v ⊗[F] E) Y` using `PI.VolStabW.linIndep_of_isUnit_det (Fv F v) σ J Y (hYG ▸ hunit)`. Establish `hXind : LinearIndependent (Fv F v ⊗[F] E) X` using `PI.VolStabW.linIndep_of_isUnit_det (Fv F v) σ J X (hX ▸ hunit)`.

Distinguish the cases in `hK : IsField (Fv F v ⊗[F] E)`. Use `letI : Field (Fv F v ⊗[F] E) := hK.toField`. Establish `hσ : ∀ x, σ (σ x) = x` using `PI.VolStabW.sigma_invol_cm σ hCM`. Establish `hinv : ∀ x, sigR (Fv F v) σ (sigR (Fv F v) σ x) = x`. Introduce `x`.

Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul r t => simp [sigR, hσ]`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy]`. Use `letI : StarRing (Fv F v ⊗[F] E) := PI.VolStabW.starOfInv (sigR (Fv F v) σ) hinv`.

Use `haveI : CharZero (Fv F v ⊗[F] E) := charZero_of_injective_algebraMap (algebraMap F (Fv F v ⊗[F] E)).injective`. Establish `hs : starRingEnd (Fv F v ⊗[F] E) = sigR (Fv F v) σ` using `RingHom.ext fun _ => rfl`. Establish `hJ' : ∀ i j, starRingEnd (Fv F v ⊗[F] E) (JR (F` using `F) (Fv F v) J j i) = JR (F := F) (Fv F v) J i j := by`. Introduce `i j`. Rewrite using `[hs]`.

Simplify using `only [JR, Matrix.map_apply]`. Rewrite using `[(fun x => by simp [sigR, inclR] : ∀ x : E, sigR (Fv F v) σ (inclR (F := F) (Fv F v) x) = inclR (F := F) (Fv F v) (σ x)), hJ.1 i j]`. Establish `hdetJ : (JR (F` using `F) (Fv F v) J).det ≠ 0 := by`. Establish `e : (JR (F` using `F) (Fv F v) J).det = inclR (F := F) (Fv F v) J.det := by`. Rewrite using `[RingHom.map_det]`.

Both sides reduce to the same expression. Rewrite using `[e]`. Introduce `h`. Apply `hJ.2` to reduce the goal to its premises. Conclude with `(inclR (F := F) (Fv F v)).injective (h.trans (map_zero _).symm)`.

Establish `hGg : ∀ i j, Formalism.UG.hform (starRingEnd (Fv F v ⊗[F] E)) (JR (F` using `F) (Fv F v) J) (X i) (X j) = Formalism.UG.hform (starRingEnd (Fv F v ⊗[F] E)) (JR (F := F) (Fv F v) J) (Y i) (Y j) := by`. Introduce `i j`. Rewrite using `[hs]`. Conclude with `congrFun (congrFun (hX.trans hYG.symm) i) j`. Take `⟨g, hg, hgX⟩` from `PI.VolStabW.witt_tuple (JR (F := F) (Fv F v) J) hJ' hdetJ Y X hYind hXind hGg`.

Rewrite `hg` using `[hs]`. Conclude with `⟨⟨g, hg⟩, funext fun i => hgX i⟩`. Take `⟨π₁, π₂, h1, h2, -, h4, h5⟩` from `Formalism.L2.SG.Pf.NcX.LT.splitStr σ v hCM hK`. Conclude with `Formalism.L2.SG.Pf.NcX.LT.WSp.witt_split σ J hJ v π₁ π₂ h1 h2 h4 h5 Y X hYind hXind (hYG.trans hX.symm)`.
-/
theorem local_witt_theorem : Formalism.L2.SG.Pf.NcX.LocSBPf.WittLocT := by
  intro F E _ _ _ _ _ σ n J a X0 hCM hJ hdet v X hX
  classical
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  set Y := ratTup (F := F) (Fv F v) X0 with hYdef
  have hYG : gramR (Fv F v) σ J Y = (gramE σ J X0).map (inclR (F := F) (Fv F v)) :=
    PI.VolStabW.LocPosW.gramR_ratTup (Fv F v) σ J X0
  have hunit : IsUnit ((gramE σ J X0).map (inclR (F := F) (Fv F v))).det := by
    have e : ((gramE σ J X0).map (inclR (F := F) (Fv F v))).det = inclR (F := F) (Fv F v) (gramE σ J X0).det :=
      (RingHom.map_det (inclR (F := F) (Fv F v)) (gramE σ J X0)).symm
    rw [e]
    exact (Ne.isUnit hdet).map (inclR (F := F) (Fv F v))
  have hYind : LinearIndependent (Fv F v ⊗[F] E) Y :=
    PI.VolStabW.linIndep_of_isUnit_det (Fv F v) σ J Y (hYG ▸ hunit)
  have hXind : LinearIndependent (Fv F v ⊗[F] E) X :=
    PI.VolStabW.linIndep_of_isUnit_det (Fv F v) σ J X (hX ▸ hunit)
  by_cases hK : IsField (Fv F v ⊗[F] E)
  · letI : Field (Fv F v ⊗[F] E) := hK.toField
    have hσ : ∀ x, σ (σ x) = x := PI.VolStabW.sigma_invol_cm σ hCM
    have hinv : ∀ x, sigR (Fv F v) σ (sigR (Fv F v) σ x) = x := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul r t => simp [sigR, hσ]
      | add x y hx hy => rw [map_add, map_add, hx, hy]
    letI : StarRing (Fv F v ⊗[F] E) := PI.VolStabW.starOfInv (sigR (Fv F v) σ) hinv
    haveI : CharZero (Fv F v ⊗[F] E) :=
      charZero_of_injective_algebraMap (algebraMap F (Fv F v ⊗[F] E)).injective
    have hs : starRingEnd (Fv F v ⊗[F] E) = sigR (Fv F v) σ := RingHom.ext fun _ => rfl
    have hJ' : ∀ i j, starRingEnd (Fv F v ⊗[F] E) (JR (F := F) (Fv F v) J j i) = JR (F := F) (Fv F v) J i j := by
      intro i j
      rw [hs]
      simp only [JR, Matrix.map_apply]
      rw [(fun x => by simp [sigR, inclR] : ∀ x : E, sigR (Fv F v) σ (inclR (F := F) (Fv F v) x) =
        inclR (F := F) (Fv F v) (σ x)), hJ.1 i j]
    have hdetJ : (JR (F := F) (Fv F v) J).det ≠ 0 := by
      have e : (JR (F := F) (Fv F v) J).det = inclR (F := F) (Fv F v) J.det := by
        rw [RingHom.map_det]
        rfl
      rw [e]
      intro h
      apply hJ.2
      exact (inclR (F := F) (Fv F v)).injective (h.trans (map_zero _).symm)
    have hGg : ∀ i j, Formalism.UG.hform (starRingEnd (Fv F v ⊗[F] E)) (JR (F := F) (Fv F v) J) (X i) (X j) =
        Formalism.UG.hform (starRingEnd (Fv F v ⊗[F] E)) (JR (F := F) (Fv F v) J) (Y i) (Y j) := by
      intro i j
      rw [hs]
      exact congrFun (congrFun (hX.trans hYG.symm) i) j
    obtain ⟨g, hg, hgX⟩ := PI.VolStabW.witt_tuple (JR (F := F) (Fv F v) J) hJ' hdetJ Y X hYind hXind hGg
    rw [hs] at hg
    exact ⟨⟨g, hg⟩, funext fun i => hgX i⟩
  · obtain ⟨π₁, π₂, h1, h2, -, h4, h5⟩ := Formalism.L2.SG.Pf.NcX.LT.splitStr σ v hCM hK
    exact Formalism.L2.SG.Pf.NcX.LT.WSp.witt_split σ J hJ v π₁ π₂ h1 h2 h4 h5 Y X hYind hXind (hYG.trans hX.symm)

end Formalism.L2.SG.Pf.NcX.WittLocPf
