import Mathlib
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsEllipticCurvePolarisedLatticeFamilyStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.EllipticCurveLatticeBaseChangeStableStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsLieNormSqIffEqPiDivCovolume
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LatticeUnifFibreEqOfPeriod
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.QuadraticEquationOfDerivative
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsCmCurvesOfWeierstrassCurves
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsNumberFieldDefiningCmCurveHomsStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MeanLogLieNormSqEqMeanLogEtaStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RingOfIntegersSqrtNegThreeModFour

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open scoped CategoryTheory.Obj UpperHalfPlane

namespace GlobalTheory

/- English proof (translation)
Establish `e : 4 * ((1 + d) / 4) = 1 + d` using `by omega`. Establish `e' : (4 : K) * (((1 + d) / 4 : ℕ) : K) = 1 + d` using `by exact_mod_cast congrArg (Nat.cast : ℕ → K) e`. Establish `e4 : (4 : K) ≠ 0` using `by norm_num`. Use `mul_left_cancel₀ e4 ?_` and prove the remaining obligations. Establish `hr' : r = 2 * w - 1` using `by linear_combination -hw`.

Substitute `hr'` using the available equality. Take the linear combination `e' + hr`.
-/
theorem half_one_add_sqrt_quadratic {K : Type} [Field K] [CharZero K] {d : ℕ} (h4 : d % 4 = 3) {r w : K}
    (hr : r ^ 2 = -(d : K)) (hw : 2 * w = 1 + r) : w * w + (((1 + d) / 4 : ℕ) : K) = w := by
  have e : 4 * ((1 + d) / 4) = 1 + d := by omega
  have e' : (4 : K) * (((1 + d) / 4 : ℕ) : K) = 1 + d := by exact_mod_cast congrArg (Nat.cast : ℕ → K) e
  have e4 : (4 : K) ≠ 0 := by norm_num
  refine mul_left_cancel₀ e4 ?_
  have hr' : r = 2 * w - 1 := by linear_combination -hw
  subst hr'
  linear_combination e' + hr

/- English proof (translation)
Introduce `hU hB hE d _ hs h4 K _ _ h2 ⟨r, hr⟩`. Take `⟨w, bar, hw, -, hgen, hσ, σ₀, hσ₀⟩` from `ringOfIntegers_sqrt_neg_three_mod_four d hs h4 K h2 r hr`. Establish `hnr` using `(hσ σ₀).1`. Use `choose 𝔟 h𝔟 using ClassGroup.mk0_surjective (R := 𝓞 K)`. Take `⟨M, hM, κ, P, v, L₀, Q, t, L, δ, hκ, hP, hQ, hδ, hc, hβ⟩` from `GlobalTheory.T.exists_numberField_defining_cm_curve_homs hU hB K h2 σ₀ hnr 𝔟 (exists_cm_curves_of_weierstrass_curves (GlobalTheory.T.exists_ellipticCurve_polarised_lattice_family hU hB) K h2 σ₀ hnr 𝔟)`.

Establish `hv : IsTangent v` using `hP.2.1.1 0`. Establish `hwc : ((κ (w : K) : M) : ℂ) = (1 + Complex.I * √d) / 2`. Establish `e` using `congrArg σ₀ hw`. Rewrite `e` using `[map_mul, map_add, map_one, map_ofNat, hσ₀]`. Rewrite using `[hκ]`.

Take the linear combination `e / 2`. Use `⟨M, hM, κ (w : K), P, v, hwc, hP.1, hP.2.1, ?_, ?_, fun s => ?_, GlobalTheory.T.mean_log_lieNormSq_eq_mean_log_eta_alt hU hB hE K h2 σ₀ hnr 𝔟 h𝔟 M κ P v L₀ Q t L δ ⟨hκ, hP, hQ, hδ, hc⟩ hβ⟩` and prove the remaining obligations. Take `⟨P₀, φ, hφ⟩` from `exists_isPolFibre hB (algebraMap (𝓞 M) M) P`. Take `⟨v₀, hv₀, -⟩` from `existsUnique_isVecOver hφ.2.1.1 v`. Take `⟨β, -, hend, -⟩` from `hβ`.

Take `⟨W, hW, hWv⟩` from `hend w P₀ P₀ φ φ v₀ v₀ hφ hφ hv₀ hv₀`. Establish `hP₀` using `GlobalTheory.T.ellipticCurve_lattice_baseChange_stable _ P v L₀ M _ P₀ φ v₀ hP hφ hv₀`. Use `⟨P₀, φ, v₀, W, hφ, hv₀, hP₀.2.1, hW, ?_, hWv⟩` and prove the remaining obligations. Use `LieMultiple.quadratic_equation_of_derivative hU hB M (algebraMap M ℂ) P₀ v₀ W _ _ (hP₀.2.1.1 0) hP₀.2.2.1 hW hWv ?_` and prove the remaining obligations. Establish `e` using `congrArg κ (half_one_add_sqrt_quadratic h4 hr hw)`.

Rewrite `e` using `[map_add, map_mul, map_natCast]`. Then use the resulting hypothesis. Take `⟨c, hc0, hc⟩` from `hc`. Use `lattice_unif_fibre_eq_of_period hU _ P v _ (L₀ _) c _ hP.1 hv (hP.2.2.2 _) hc0 fun z => ?_` and prove the remaining obligations. Rewrite using `[hc, hκ]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨a, rfl⟩`. Take `⟨m, n, rfl⟩` from `hgen a`. Conclude with `⟨m, n, by simp⟩`. Introduce and unpack `⟨m, n, rfl⟩`. Conclude with `⟨m + n * w, by simp⟩`.

Conclude with `⟨_, isLieNormSq_iff_eq_pi_div_covolume hU hB _ P v _ (L₀ _) hP.1 hv (hP.2.2.2 _)⟩`.
-/
theorem cmCurve_of_uniformisation : ThetaUnifAV → Out.PolBaseChangeSt → (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → CMCurve := by
  intro hU hB hE d _ hs h4 K _ _ h2 ⟨r, hr⟩
  obtain ⟨w, bar, hw, -, hgen, hσ, σ₀, hσ₀⟩ := ringOfIntegers_sqrt_neg_three_mod_four d hs h4 K h2 r hr
  have hnr := (hσ σ₀).1
  choose 𝔟 h𝔟 using ClassGroup.mk0_surjective (R := 𝓞 K)
  obtain ⟨M, hM, κ, P, v, L₀, Q, t, L, δ, hκ, hP, hQ, hδ, hc, hβ⟩ := GlobalTheory.T.exists_numberField_defining_cm_curve_homs hU hB K h2 σ₀ hnr 𝔟
    (exists_cm_curves_of_weierstrass_curves (GlobalTheory.T.exists_ellipticCurve_polarised_lattice_family hU hB) K h2 σ₀ hnr 𝔟)
  have hv : IsTangent v := hP.2.1.1 0
  have hwc : ((κ (w : K) : M) : ℂ) = (1 + Complex.I * √d) / 2 := by
    have e := congrArg σ₀ hw
    rw [map_mul, map_add, map_one, map_ofNat, hσ₀] at e
    rw [hκ]
    linear_combination e / 2
  refine ⟨M, hM, κ (w : K), P, v, hwc, hP.1, hP.2.1, ?_, ?_, fun s => ?_,
    GlobalTheory.T.mean_log_lieNormSq_eq_mean_log_eta_alt hU hB hE K h2 σ₀ hnr 𝔟 h𝔟 M κ P v L₀ Q t L δ ⟨hκ, hP, hQ, hδ, hc⟩ hβ⟩
  · obtain ⟨P₀, φ, hφ⟩ := exists_isPolFibre hB (algebraMap (𝓞 M) M) P
    obtain ⟨v₀, hv₀, -⟩ := existsUnique_isVecOver hφ.2.1.1 v
    obtain ⟨β, -, hend, -⟩ := hβ
    obtain ⟨W, hW, hWv⟩ := hend w P₀ P₀ φ φ v₀ v₀ hφ hφ hv₀ hv₀
    have hP₀ := GlobalTheory.T.ellipticCurve_lattice_baseChange_stable _ P v L₀ M _ P₀ φ v₀ hP hφ hv₀
    refine ⟨P₀, φ, v₀, W, hφ, hv₀, hP₀.2.1, hW, ?_, hWv⟩
    refine LieMultiple.quadratic_equation_of_derivative hU hB M (algebraMap M ℂ) P₀ v₀ W _ _ (hP₀.2.1.1 0)
      hP₀.2.2.1 hW hWv ?_
    have e := congrArg κ (half_one_add_sqrt_quadratic h4 hr hw)
    rwa [map_add, map_mul, map_natCast] at e
  · obtain ⟨c, hc0, hc⟩ := hc
    refine lattice_unif_fibre_eq_of_period hU _ P v _ (L₀ _) c _ hP.1 hv (hP.2.2.2 _) hc0 fun z => ?_
    rw [hc, hκ]
    constructor
    · rintro ⟨a, rfl⟩
      obtain ⟨m, n, rfl⟩ := hgen a
      exact ⟨m, n, by simp⟩
    · rintro ⟨m, n, rfl⟩
      exact ⟨m + n * w, by simp⟩
  · exact ⟨_, isLieNormSq_iff_eq_pi_div_covolume hU hB _ P v _ (L₀ _) hP.1 hv (hP.2.2.2 _)⟩

end GlobalTheory
