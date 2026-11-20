import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsLocalizationConeVarMap
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo IsLocalRing

noncomputable section

set_option maxHeartbeats 400000 in

/- English proof (translation)
Introduce `K _ ι _ P W hP hW hPW`. Use `hP.1` as an intermediate fact. Use `hW.1` as an intermediate fact. Use `choose v hv using hW.2.2`. Establish `hA` using `regularityLocalFlat_holds.isLocalRing hPW`.

Establish `hloc` using `regularityLocalFlat_holds.isLocalization_coneVarMap hPW hP.2.1 hW.2.1 v hv`. Set `_` to `(regularityLocalFlat_holds.coneVarMap P W hPW v).toRingHom.toAlgebra`. Use `regularityLocalFlat_holds.isPrime_map_C K (maximalIdeal (locRing P W))` as an intermediate fact. Establish `: IsScalarTower (locRing P W) (MvPolynomial K (locRing P W)) (coneLocRing P W hPW)` using `IsScalarTower.of_algebraMap_eq fun x => ((regularityLocalFlat_holds.coneVarMap P W hPW v).commutes x).symm`. Establish `hR : IsLocalRing (coneLocRing P W hPW)` using `IsLocalization.AtPrime.isLocalRing (coneLocRing P W hPW) ((maximalIdeal (locRing P W)).map (C : locRing P W →+* MvPolynomial K _))`.

Use `⟨hA, hR, ?_, ?_⟩` and prove the remaining obligations. Use `IsLocalization.flat (coneLocRing P W hPW) ((maximalIdeal (locRing P W)).map (C : locRing P W →+* MvPolynomial K _)).primeCompl` as an intermediate fact. Establish `: Module.Free (locRing P W) (MvPolynomial K (locRing P W))` using `Module.Free.of_basis (MvPolynomial.basisMonomials K (locRing P W))`. Establish `: Module.Flat (locRing P W) (MvPolynomial K (locRing P W))` using `Module.Flat.of_free`. Conclude with `Module.Flat.trans _ (MvPolynomial K (locRing P W)) _`.

Rewrite using `[← IsLocalization.AtPrime.map_eq_maximalIdeal ((maximalIdeal (locRing P W)).map (C : locRing P W →+* MvPolynomial K _)) (coneLocRing P W hPW), Ideal.map_map, ← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_eq]`.
-/
theorem regularityLocalFlat_holds.proof : regularityLocalFlat_holds.Statement := by
  intro K _ ι _ P W hP hW hPW
  have := hP.1
  have := hW.1
  choose v hv using hW.2.2
  have hA := regularityLocalFlat_holds.isLocalRing hPW
  have hloc := regularityLocalFlat_holds.isLocalization_coneVarMap hPW hP.2.1 hW.2.1 v hv
  let _ := (regularityLocalFlat_holds.coneVarMap P W hPW v).toRingHom.toAlgebra
  have := regularityLocalFlat_holds.isPrime_map_C K (maximalIdeal (locRing P W))
  have : IsScalarTower (locRing P W) (MvPolynomial K (locRing P W)) (coneLocRing P W hPW) :=
    IsScalarTower.of_algebraMap_eq fun x => ((regularityLocalFlat_holds.coneVarMap P W hPW v).commutes x).symm
  have hR : IsLocalRing (coneLocRing P W hPW) :=
    IsLocalization.AtPrime.isLocalRing (coneLocRing P W hPW)
      ((maximalIdeal (locRing P W)).map (C : locRing P W →+* MvPolynomial K _))
  refine ⟨hA, hR, ?_, ?_⟩
  · have := IsLocalization.flat (coneLocRing P W hPW)
      ((maximalIdeal (locRing P W)).map (C : locRing P W →+* MvPolynomial K _)).primeCompl
    have : Module.Free (locRing P W) (MvPolynomial K (locRing P W)) :=
      Module.Free.of_basis (MvPolynomial.basisMonomials K (locRing P W))
    have : Module.Flat (locRing P W) (MvPolynomial K (locRing P W)) := Module.Flat.of_free
    exact Module.Flat.trans _ (MvPolynomial K (locRing P W)) _
  · rw [← IsLocalization.AtPrime.map_eq_maximalIdeal
      ((maximalIdeal (locRing P W)).map (C : locRing P W →+* MvPolynomial K _))
      (coneLocRing P W hPW), Ideal.map_map, ← MvPolynomial.algebraMap_eq,
      ← IsScalarTower.algebraMap_eq]

end

end GroundTheory.Heights₂.Heights.Inter
