import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeDEqSumOfAgree
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.GlobEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.PhiEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.LocBase
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.EvenVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.RhoBij
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.RhoGlob
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.RhoDiv
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.RhoInt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.RhoStar
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.IntsOv
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.IsoVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.IsoAbs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.IsoJ
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.SplitCore
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.ExistsUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.FinitePartIsomorphismSurjective
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.MemSUAIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.PhiGUnitary
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.MapOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.FinitePartSplitInfinite
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.MemKGLIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.KglIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.OkConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.IntegralCongrOfForallAbove
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.UaFacts

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Introduce `L _ _ _ hU`. Take `⟨Δ, e, h1, h2, h3⟩` from `globEx L`. Take `⟨φ, h4, h5⟩` from `phiEx L`. Set `P : Pre L` to `⟨Δ, e, h1, h2, φ, h4, h5⟩`. Use `⟨⟨Δ, e, h1, h2, h3, fun v hv => ?_, P.rho, rhoGlob L P, fun v x hx => ?_, fun v a => ?_, rhoInt L P, rhoStar L P, fun v w h a => ?_⟩⟩` and prove the remaining obligations.

Take `⟨a, b, c, d⟩` from `locBase (Lp L) v`. Conclude with `⟨a, b, c, d hv, evenVal L P hU v⟩`. Conclude with `(rhoBij L P v).1 (funext fun w => (hx w.1 w.2).trans (map_zero _).symm)`. Take `⟨x, hx⟩` from `(rhoBij L P v).2 fun w => pLoc L w.1 a`. Conclude with `⟨x, fun w h => congrFun hx ⟨w, h⟩⟩`.

Establish `: P.rho v w h (algebraMap _ _ a) = P.φ v w h a`. Express the relevant statement in the definitionally equal form `P.φ v w h (algebraMap (Kv v) (Lsq (Kv v) (cv v P.Δ)) a).re + P.φ v w h (algebraMap (Kv v) (Lsq (Kv v) (cv v P.Δ)) a).im * P.rt w = _`. Simplify using the standard rewrite rules. Rewrite using `[this]`. Conclude with `rhoDiv L P v w h a`.
-/
theorem UpperTheory.V.Z.Sym.Dict.Br.ringEx : RingEx := by
  intro L _ _ _ hU
  obtain ⟨Δ, e, h1, h2, h3⟩ := globEx L
  obtain ⟨φ, h4, h5⟩ := phiEx L
  let P : Pre L := ⟨Δ, e, h1, h2, φ, h4, h5⟩
  refine ⟨⟨Δ, e, h1, h2, h3, fun v hv => ?_, P.rho, rhoGlob L P, fun v x hx => ?_, fun v a => ?_, rhoInt L P, rhoStar L P,
    fun v w h a => ?_⟩⟩
  · obtain ⟨a, b, c, d⟩ := locBase (Lp L) v
    exact ⟨a, b, c, d hv, evenVal L P hU v⟩
  · exact (rhoBij L P v).1 (funext fun w => (hx w.1 w.2).trans (map_zero _).symm)
  · obtain ⟨x, hx⟩ := (rhoBij L P v).2 fun w => pLoc L w.1 a
    exact ⟨x, fun w h => congrFun hx ⟨w, h⟩⟩
  · have : P.rho v w h (algebraMap _ _ a) = P.φ v w h a := by
      change P.φ v w h (algebraMap (Kv v) (Lsq (Kv v) (cv v P.Δ)) a).re + P.φ v w h (algebraMap (Kv v) (Lsq (Kv v) (cv v P.Δ)) a).im * P.rt w = _
      simp
    rw [this]
    exact rhoDiv L P v w h a

/- English proof (translation)
Introduce `L _ _ _ R`. Take `⟨a, ha⟩` from `bGEx L R`. Take `⟨b, hb⟩` from `bSEx L R`. Take `⟨c, hc, hc'⟩` from `rGEx L R`. Take `⟨d, hd, hd'⟩` from `rSEx L R`.

Conclude with `⟨⟨R, a, ha, b, hb, c, hc, hc', d, hd, hd'⟩, rfl⟩`.
-/
theorem UpperTheory.V.Z.Sym.Dict.Br.groupEx : GroupEx := by
  intro L _ _ _ R
  obtain ⟨a, ha⟩ := bGEx L R
  obtain ⟨b, hb⟩ := bSEx L R
  obtain ⟨c, hc, hc'⟩ := rGEx L R
  obtain ⟨d, hd, hd'⟩ := rSEx L R
  exact ⟨⟨R, a, ha, b, hb, c, hc, hc', d, hd, hd'⟩, rfl⟩

/- English proof (translation)
Take `⟨s, hs, i, h0, hρ⟩` from `splitCore L R w hw`. Establish `hi : IsoOk i` using `⟨fun a => by`. Establish `e : i a = R.ρ _ w rfl (algebraMap _ _ a)`. Rewrite using `[hρ]`. Use `congr 1`.

Express the relevant statement in the definitionally equal form `a = (algebraMap (Kv (un w)) (Lsq (Kv (un w)) (cv (un w) R.Δ)) a).re + s * (algebraMap (Kv (un w)) (Lsq (Kv (un w)) (cv (un w) R.Δ)) a).im`. Simplify using the standard rewrite rules. Rewrite using `[← (intsOv L w).2, ← (intsOv (Lp L) (un w)).2, e]`. Conclude with `R.ρ_div _ w rfl a⟩`. Take `⟨v1, v2, v3, v4⟩` from `isoVal _ _ i hi`.

Take `⟨j1, j2⟩` from `isoJ _ _ i hi`. Use `⟨⟨s, hs, h0, i, hρ, v1, isoAbs _ _ i hi, v2, v4, v3, j1, fun n g => ?_⟩⟩` and prove the remaining obligations. Rewrite using `[← GlobalTheory.HeckeEigConj.KO_eq_KGL]`. Conclude with `j2 n g`.
-/
theorem UpperTheory.V.Z.Sym.Dict.Br.splitEx (L : Type) [Field L] [NumberField L] [IsCMField L] (R : RingBr L) (w : Plc L)
    (hw : IsSplitAt w) : Nonempty (R.Split w) := by
  obtain ⟨s, hs, i, h0, hρ⟩ := splitCore L R w hw
  have hi : IsoOk i := ⟨fun a => by
    have e : i a = R.ρ _ w rfl (algebraMap _ _ a) := by
      rw [hρ]
      congr 1
      change a = (algebraMap (Kv (un w)) (Lsq (Kv (un w)) (cv (un w) R.Δ)) a).re + s * (algebraMap (Kv (un w)) (Lsq (Kv (un w)) (cv (un w) R.Δ)) a).im
      simp
    rw [← (intsOv L w).2, ← (intsOv (Lp L) (un w)).2, e]
    exact R.ρ_div _ w rfl a⟩
  obtain ⟨v1, v2, v3, v4⟩ := isoVal _ _ i hi
  obtain ⟨j1, j2⟩ := isoJ _ _ i hi
  refine ⟨⟨s, hs, h0, i, hρ, v1, isoAbs _ _ i hi, v2, v4, v3, j1, fun n g => ?_⟩⟩
  rw [← GlobalTheory.HeckeEigConj.KO_eq_KGL]
  exact j2 n g

/- English proof (translation)
Introduce `L _ _ _ hU`. Take `⟨R⟩` from `ringEx L hU`. Take `⟨B, -⟩` from `groupEx L R`. Conclude with `⟨B, splitEx L _, chiEx L _, (okFin L B).1, (okFin L B).2, (okG L B).1, (okG L B).2.1, (okG L B).2.2, (okS L B).1, (okS L B).2.1, (okS L B).2.2, okConj L B, integral_congr_of_forall_above L B⟩`.
-/
theorem UpperTheory.V.Z.Sym.Dict.Br.bridgeEx : BridgeEx := by
  intro L _ _ _ hU
  obtain ⟨R⟩ := ringEx L hU
  obtain ⟨B, -⟩ := groupEx L R
  exact ⟨B, splitEx L _, chiEx L _, (okFin L B).1, (okFin L B).2, (okG L B).1, (okG L B).2.1, (okG L B).2.2,
    (okS L B).1, (okS L B).2.1, (okS L B).2.2, okConj L B, integral_congr_of_forall_above L B⟩
