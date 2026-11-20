import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCharacterGroupIso
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleBaseOfCompleteNormalLocalCharZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PsiCoordinateTwoNsmulAssociatedPowFourStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarisedAbelianPartIsoOfBundleSquareIsoStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DegenerationCharMapEqOnEvenCharactersStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PsiCoordinatesEvenCharactersFourthPowersAssociatStatement
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory.LN GlobalTheory
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SqUnifCoord

/- English proof (translation)
Distinguish the cases in `ha : a = 0`. Substitute `ha` using the available equality. Rewrite `h` using `[zero_pow hn.ne']`. Rewrite using `[(pow_eq_zero_iff hn.ne').1 ((associated_zero_iff_eq_zero _).1 h.symm)]`. Establish `hb : b ≠ 0`.

Introduce and unpack `rfl`. Rewrite `h` using `[zero_pow hn.ne']`. Conclude with `ha ((pow_eq_zero_iff hn.ne').1 ((associated_zero_iff_eq_zero _).1 h))`. Take `⟨u, hu⟩` from `h`. Use `set K := FractionRing R`.

Establish `inj` using `IsFractionRing.injective R K`. Establish `ha' : algebraMap R K a ≠ 0` using `fun h0 => ha (inj (h0.trans (map_zero _).symm))`. Establish `hb' : algebraMap R K b ≠ 0` using `fun h0 => hb (inj (h0.trans (map_zero _).symm))`. Establish `hx : (algebraMap R K b / algebraMap R K a) ^ n = algebraMap R K (u : R)`. Rewrite using `[div_pow, div_eq_iff (pow_ne_zero _ ha'), ← map_pow, ← map_pow, ← map_mul, ← hu, mul_comm]`.

Establish `hy : (algebraMap R K a / algebraMap R K b) ^ n = algebraMap R K ((u⁻¹ : Rˣ) : R)`. Rewrite using `[div_pow, div_eq_iff (pow_ne_zero _ hb'), ← map_pow, ← map_pow, ← map_mul, ← hu, mul_comm, mul_assoc, Units.mul_inv, mul_one]`. Take `⟨c, hc⟩` from `IsIntegrallyClosed.isIntegral_iff.1 (IsIntegral.of_pow hn (hx ▸ isIntegral_algebraMap))`. Take `⟨d, hd⟩` from `IsIntegrallyClosed.isIntegral_iff.1 (IsIntegral.of_pow hn (hy ▸ isIntegral_algebraMap))`. Establish `hcd : c * d = 1` using `inj (by rw [map_mul, hc, hd, map_one, div_mul_div_comm, mul_comm (algebraMap R K b), div_self (mul_ne_zero ha' hb')])`.

Use `⟨⟨c, d, hcd, by rw [mul_comm, hcd]⟩, inj ?_⟩` and prove the remaining obligations. Use `show algebraMap R K (a * c) = algebraMap R K b`. Rewrite using `[map_mul, hc, mul_div_cancel₀ _ ha']`.
-/
theorem associated_of_pow {R : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] {a b : R} {n : ℕ}
    (hn : 0 < n) (h : Associated (a ^ n) (b ^ n)) : Associated a b := by
  by_cases ha : a = 0
  · subst ha
    rw [zero_pow hn.ne'] at h
    rw [(pow_eq_zero_iff hn.ne').1 ((associated_zero_iff_eq_zero _).1 h.symm)]
  have hb : b ≠ 0 := by
    rintro rfl
    rw [zero_pow hn.ne'] at h
    exact ha ((pow_eq_zero_iff hn.ne').1 ((associated_zero_iff_eq_zero _).1 h))
  obtain ⟨u, hu⟩ := h
  set K := FractionRing R
  have inj := IsFractionRing.injective R K
  have ha' : algebraMap R K a ≠ 0 := fun h0 => ha (inj (h0.trans (map_zero _).symm))
  have hb' : algebraMap R K b ≠ 0 := fun h0 => hb (inj (h0.trans (map_zero _).symm))
  have hx : (algebraMap R K b / algebraMap R K a) ^ n = algebraMap R K (u : R) := by
    rw [div_pow, div_eq_iff (pow_ne_zero _ ha'), ← map_pow, ← map_pow, ← map_mul, ← hu, mul_comm]
  have hy : (algebraMap R K a / algebraMap R K b) ^ n = algebraMap R K ((u⁻¹ : Rˣ) : R) := by
    rw [div_pow, div_eq_iff (pow_ne_zero _ hb'), ← map_pow, ← map_pow, ← map_mul, ← hu, mul_comm,
      mul_assoc, Units.mul_inv, mul_one]
  obtain ⟨c, hc⟩ := IsIntegrallyClosed.isIntegral_iff.1
    (IsIntegral.of_pow hn (hx ▸ isIntegral_algebraMap))
  obtain ⟨d, hd⟩ := IsIntegrallyClosed.isIntegral_iff.1
    (IsIntegral.of_pow hn (hy ▸ isIntegral_algebraMap))
  have hcd : c * d = 1 := inj (by rw [map_mul, hc, hd, map_one, div_mul_div_comm, mul_comm (algebraMap R K b),
    div_self (mul_ne_zero ha' hb')])
  refine ⟨⟨c, d, hcd, by rw [mul_comm, hcd]⟩, inj ?_⟩
  show algebraMap R K (a * c) = algebraMap R K b
  rw [map_mul, hc, mul_div_cancel₀ _ ha']

/- English proof (translation)
Introduce `R _ _ _ hR G _ _ hsa D D' A A' U U' hL`. Establish `hA` using `admissibleBase_of_completeNormalLocalCharZero hR`. Use `haveI : CharZero R := hR.2.2.2`. Use `haveI : IsIntegrallyClosed R := hR.2.1`. Take `⟨xe, hxe⟩` from `unifPre_characterGroup_iso R _ hA D D' A A' G hsa U.toUnifPre U'.toUnifPre`.

Take `⟨Φ, w, wL, hw, hwL, hm, hp⟩` from `GlobalTheory.T.polarisedAbelianPart_iso_of_bundleSquare_iso R hR G hsa D D' A A' U U' hL`. Establish `hc` using `GlobalTheory.T.degenerationCharMap_eq_on_even_characters R hR G hsa D D' A A' U U' hL Φ w hw hm (fun e => (hp e).1) xe hxe`. Use `⟨xe, fun y r r' hr hr' => ?_⟩` and prove the remaining obligations. Take `⟨⟨s, hs, -⟩, -⟩` from `GlobalTheory.PsiCoordLocal.main R D hR.2.1 (xe (2 • y))`. Take `⟨⟨s', hs', -⟩, -⟩` from `GlobalTheory.PsiCoordLocal.main R D' hR.2.1 (2 • y)`.

Establish `a1 : Associated s (r ^ 4)` using `GlobalTheory.T.psiCoordinate_two_nsmul_associated_pow_four R _ D (xe y) r s hr (by rw [← map_nsmul]; exact hs)`. Establish `a2 : Associated s' (r' ^ 4)` using `GlobalTheory.T.psiCoordinate_two_nsmul_associated_pow_four R _ D' y r' s' hr' hs'`. Establish `a3 : Associated (s ^ 4) (s' ^ 4)` using `GlobalTheory.T.psiCoordinates_evenCharacters_fourthPowers_associated R hR G hsa D D' A A' U U' hL Φ w wL hw hwL hm hp xe hxe hc y s s' hs hs'`. Use `associated_of_pow (n := 8) (by norm_num) ?_` and prove the remaining obligations. Establish `e1 : (r ^ 2) ^ 8 = (r ^ 4) ^ 4` using `by ring`.

Establish `e2 : (r' ^ 2) ^ 8 = (r' ^ 4) ^ 4` using `by ring`. Rewrite using `[e1, e2]`. Conclude with `((a1.pow_pow (n := 4)).symm.trans a3).trans (a2.pow_pow (n := 4))`.
-/
theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D D' : DegData R (maximalIdeal R)) (A A' : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal R) D' A' G), LBIso (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) → ∃ ε : D'.toPre.X ≃+ D.toPre.X, ∀ y r r', PsiCoord D.toPre (ε y) r → PsiCoord D'.toPre y r' → Associated (r ^ 2) (r' ^ 2) := by
  intro R _ _ _ hR G _ _ hsa D D' A A' U U' hL
  have hA := admissibleBase_of_completeNormalLocalCharZero hR
  haveI : CharZero R := hR.2.2.2
  haveI : IsIntegrallyClosed R := hR.2.1
  obtain ⟨xe, hxe⟩ := unifPre_characterGroup_iso R _ hA D D' A A' G hsa U.toUnifPre U'.toUnifPre
  obtain ⟨Φ, w, wL, hw, hwL, hm, hp⟩ := GlobalTheory.T.polarisedAbelianPart_iso_of_bundleSquare_iso R hR G hsa D D' A A' U U' hL
  have hc := GlobalTheory.T.degenerationCharMap_eq_on_even_characters R hR G hsa D D' A A' U U' hL Φ w hw hm (fun e => (hp e).1) xe hxe
  refine ⟨xe, fun y r r' hr hr' => ?_⟩
  obtain ⟨⟨s, hs, -⟩, -⟩ := GlobalTheory.PsiCoordLocal.main R D hR.2.1 (xe (2 • y))
  obtain ⟨⟨s', hs', -⟩, -⟩ := GlobalTheory.PsiCoordLocal.main R D' hR.2.1 (2 • y)
  have a1 : Associated s (r ^ 4) := GlobalTheory.T.psiCoordinate_two_nsmul_associated_pow_four R _ D (xe y) r s hr (by rw [← map_nsmul]; exact hs)
  have a2 : Associated s' (r' ^ 4) := GlobalTheory.T.psiCoordinate_two_nsmul_associated_pow_four R _ D' y r' s' hr' hs'
  have a3 : Associated (s ^ 4) (s' ^ 4) :=
    GlobalTheory.T.psiCoordinates_evenCharacters_fourthPowers_associated R hR G hsa D D' A A' U U' hL Φ w wL hw hwL hm hp xe hxe hc y s s' hs hs'
  refine associated_of_pow (n := 8) (by norm_num) ?_
  have e1 : (r ^ 2) ^ 8 = (r ^ 4) ^ 4 := by ring
  have e2 : (r' ^ 2) ^ 8 = (r' ^ 4) ^ 4 := by ring
  rw [e1, e2]
  exact ((a1.pow_pow (n := 4)).symm.trans a3).trans (a2.pow_pow (n := 4))

end GlobalTheory.SqUnifCoord
