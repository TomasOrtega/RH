import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Formalism.LocalToGlobal.ProjectiveLattices.L2DefiniteCuspForms
import Formalism.LocalToGlobal.ProjectiveLattices.NonnegIffOfLiesTotal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.NonvanishingNearMaximum
import Formalism.LocalToGlobal.ProjectiveLattices.AxHSupA
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointBaseChangeAlgebraMap
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointBaseChangeUniqueReflIff
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueFrameChangeByMatrices
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeCommBaseChange
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedModuliAlgebraicLawsChartWeightIntegrality

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamT.RatFn

/- English proof (translation)
Set `X₀ : ∀ b, Matrix (Fin (m b)) (Fin (m b)) (MvPolynomial (FrVar m) K)` to `fun b => Matrix.of fun i j => MvPolynomial.X ⟨b, (j, i)⟩`. Set `d : MvPolynomial (FrVar m) K` to `∏ b, (X₀ b).det`. Set `A` to `Localization.Away d`. Set `jA : MvPolynomial (FrVar m) K →ₐ[F] A` to `IsScalarTower.toAlgHom F _ A`. Establish `hd : IsUnit (algebraMap (MvPolynomial (FrVar m) K) A d)` using `IsLocalization.Away.algebraMap_isUnit d`.

Use `⟨A, inferInstance, inferInstance, jA.comp (IsScalarTower.toAlgHom F K _), fun b => (X₀ b).map (algebraMap _ A), inferInstance, fun b => ?_, fun t => ?_⟩` and prove the remaining obligations. Use `beta_reduce`. Rewrite using `[← RingHom.mapMatrix_apply, ← RingHom.map_det]`. Conclude with `isUnit_of_dvd_unit (map_dvd _ (Finset.dvd_prod_of_mem (fun b => (X₀ b).det) (Finset.mem_univ b))) hd`. Take `⟨N, P, hP⟩` from `IsLocalization.Away.surj d t`.

Use `⟨P, N, fun S _ _ φ Y hY => ?_⟩` and prove the remaining obligations. Set `e : MvPolynomial (FrVar m) K →+* S` to `MvPolynomial.eval₂Hom φ.toRingHom (fun v : FrVar m => Y v.1 v.2.2 v.2.1)`. Establish `heX : ∀ b, (X₀ b).map e = Y b` using `fun b => by`. Use extensionality with `i j`. Simplify using `[e, X₀]`.

Establish `hed : e d = ∏ b, (Y b).det`. Simplify using `only [d, map_prod]`. Use `Finset.prod_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[RingHom.map_det, RingHom.mapMatrix_apply, heX]`. Establish `hu : IsUnit (e d)`.

Rewrite using `[hed]`. Conclude with `IsUnit.prod_univ_iff.2 hY`. Set `k₀ : A →+* S` to `IsLocalization.Away.lift d hu`. Establish `hk : ∀ p, k₀ (algebraMap _ A p) = e p` using `fun p => IsLocalization.Away.lift_eq d hu p`. Establish `hC : ∀ x : K, e (algebraMap K _ x) = φ x` using `fun x => by simp [e]`.

Set `k : A →ₐ[F] S` to `{ k₀ with commutes' := fun r => by`. Express the relevant statement in the definitionally equal form `k₀ (algebraMap F A r) = _`. Rewrite using `[IsScalarTower.algebraMap_apply F (MvPolynomial (FrVar m) K) A, hk, IsScalarTower.algebraMap_apply F K (MvPolynomial (FrVar m) K), hC, φ.commutes] }`. Use `⟨k, ?_, fun b => ?_, ?_⟩` and prove the remaining obligations. Use extensionality with `x`.

Conclude with `(hk _).trans (hC x)`. Rewrite using `[← heX b]`. Use extensionality with `i j`. Conclude with `hk _`. Establish `h` using `congrArg k₀ hP`.

Rewrite `h` using `[map_mul, map_pow, hk, hk, hed]`. Express the relevant statement in the definitionally equal form `_ * k₀ t = _`. Rewrite using `[mul_comm, h, evalFr, MvPolynomial.eval_map]`. Both sides reduce to the same expression.
-/
theorem exists_genericRing (F K : Type) [Field F] [Field K] [Algebra F K] (B : Type) [Fintype B] (m : B → ℕ) :
    ∃ (A : Type) (_ : CommRing A) (_ : Algebra F A) (π : K →ₐ[F] A) (X : ∀ b, Matrix (Fin (m b)) (Fin (m b)) A),
      _root_.IsReduced A ∧ (∀ b, IsUnit (X b).det) ∧ ∀ t : A, ∃ (P : MvPolynomial (FrVar m) K) (N : ℕ),
        ∀ (S : Type) [CommRing S] [Algebra F S] (φ : K →ₐ[F] S) (Y : ∀ b, Matrix (Fin (m b)) (Fin (m b)) S),
          (∀ b, IsUnit (Y b).det) → ∃ k : A →ₐ[F] S, k.comp π = φ ∧ (∀ b, (X b).map k = Y b) ∧
            (∏ b, (Y b).det) ^ N * k t = evalFr (MvPolynomial.map φ.toRingHom P) Y := by
  classical
  let X₀ : ∀ b, Matrix (Fin (m b)) (Fin (m b)) (MvPolynomial (FrVar m) K) :=
    fun b => Matrix.of fun i j => MvPolynomial.X ⟨b, (j, i)⟩
  let d : MvPolynomial (FrVar m) K := ∏ b, (X₀ b).det
  let A := Localization.Away d
  let jA : MvPolynomial (FrVar m) K →ₐ[F] A := IsScalarTower.toAlgHom F _ A
  have hd : IsUnit (algebraMap (MvPolynomial (FrVar m) K) A d) := IsLocalization.Away.algebraMap_isUnit d
  refine ⟨A, inferInstance, inferInstance, jA.comp (IsScalarTower.toAlgHom F K _),
    fun b => (X₀ b).map (algebraMap _ A), inferInstance, fun b => ?_, fun t => ?_⟩
  · beta_reduce
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact isUnit_of_dvd_unit (map_dvd _ (Finset.dvd_prod_of_mem (fun b => (X₀ b).det) (Finset.mem_univ b))) hd
  · obtain ⟨N, P, hP⟩ := IsLocalization.Away.surj d t
    refine ⟨P, N, fun S _ _ φ Y hY => ?_⟩
    let e : MvPolynomial (FrVar m) K →+* S :=
      MvPolynomial.eval₂Hom φ.toRingHom (fun v : FrVar m => Y v.1 v.2.2 v.2.1)
    have heX : ∀ b, (X₀ b).map e = Y b := fun b => by
      ext i j
      simp [e, X₀]
    have hed : e d = ∏ b, (Y b).det := by
      simp only [d, map_prod]
      refine Finset.prod_congr rfl fun b _ => ?_
      rw [RingHom.map_det, RingHom.mapMatrix_apply, heX]
    have hu : IsUnit (e d) := by
      rw [hed]
      exact IsUnit.prod_univ_iff.2 hY
    let k₀ : A →+* S := IsLocalization.Away.lift d hu
    have hk : ∀ p, k₀ (algebraMap _ A p) = e p := fun p => IsLocalization.Away.lift_eq d hu p
    have hC : ∀ x : K, e (algebraMap K _ x) = φ x := fun x => by simp [e]
    let k : A →ₐ[F] S :=
      { k₀ with
        commutes' := fun r => by
          change k₀ (algebraMap F A r) = _
          rw [IsScalarTower.algebraMap_apply F (MvPolynomial (FrVar m) K) A, hk,
            IsScalarTower.algebraMap_apply F K (MvPolynomial (FrVar m) K), hC, φ.commutes] }
    refine ⟨k, ?_, fun b => ?_, ?_⟩
    · ext x
      exact (hk _).trans (hC x)
    · rw [← heX b]
      ext i j
      exact hk _
    · have h := congrArg k₀ hP
      rw [map_mul, map_pow, hk, hk, hed] at h
      change _ * k₀ t = _
      rw [mul_comm, h, evalFr, MvPolynomial.eval_map]
      rfl

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c K _ _ _ y a n F hF`. Establish `hB : Out.SecBaseChangeSt` using `GlobalTheory.lawsFieldsSeparately.2.1`. Take `⟨-, -, hWD, -⟩` from `GlobalTheory.Frames.algebraic_laws hB E H Dw l Xo c`. Establish `hT : AllTest Xo c` using `GlobalTheory.Frames.allTest_of_secBaseChange hB E H Dw l Xo c`. Take `⟨A, _, _, π, X, hred, hX, hA⟩` from `exists_genericRing c.F K (E →+* ℂ) Dw.mult`.

Take `⟨u₀, hu₀⟩` from `GlobalTheory.Frames.FramedBaseChange.exists_frMap hB E H Dw l Xo c K A π y`. Take `⟨u, hu, -⟩` from `GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c A u₀ (fun b => (X b).transpose) 1 (fun b => by rw [Matrix.det_transpose]; exact hX b)`. Take `⟨P, N, hP⟩` from `hA (evR Xo c F u)`. Use `⟨P, N, fun S _ _ φ z z' Y hY hz hz' => ?_⟩` and prove the remaining obligations. Take `⟨k, hkπ, hkX, hk⟩` from `hP S φ Y hY`.

Take `⟨w, hw⟩` from `GlobalTheory.Frames.FramedBaseChange.exists_frMap hB E H Dw l Xo c A S k u₀`. Establish `hw' : FrMap (k.comp π) y w` using `frMap_trans (Xo := Xo) (c := c) _ _ _ π k y u₀ w hu₀ hw`. Rewrite `hw'` using `[hkπ]`. Establish `hwz : w = z` using `(GlobalTheory.Frames.frMap_unique_refl_iff E H Dw l Xo c K S φ y).1 w z hw' hz`. Substitute `hwz` using the available equality.

Establish `hm : FrMap k u z'`. Use `(GlobalTheory.Frames.ChgBC.frChg_baseChange E H Dw l Xo c A S k u₀ u w z' _ _ hu hw).2 ?_` and prove the remaining obligations. Establish `e : (fun τ => ((X τ).transpose).map k) = fun b => (Y b).transpose`. Use function extensionality and compare the values at `fun b => by rw [Matrix.transpose_map, hkX]`. Rewrite using `[e, Units.val_one, map_one]`.

Conclude with `hz'`. Rewrite using `[evR_frMap hWD F hF.1 k u (hT _ u) z' hm]`. Conclude with `hk`.
-/
theorem exists_poly_div_det : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ F ∈ sec Xo c a n, ∃ (P : MvPolynomial (FrVar Dw.mult) K) (N : ℕ), ∀ (S : Type) [CommRing S] [Algebra c.F S] (φ : K →ₐ[c.F] S) (z z' : FrPt Xo c S) (Y : (∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) S)), (∀ b, IsUnit (Y b).det) → FrMap φ y z → FrChg (fun b => (Y b).transpose) 1 z z' → (∏ b, (Y b).det) ^ N * evR Xo c F z' = evalFr (MvPolynomial.map φ.toRingHom P) Y := by
  intro E _ _ _ H Dw l Xo c K _ _ _ y a n F hF
  have hB : Out.SecBaseChangeSt := GlobalTheory.lawsFieldsSeparately.2.1
  obtain ⟨-, -, hWD, -⟩ := GlobalTheory.Frames.algebraic_laws hB E H Dw l Xo c
  have hT : AllTest Xo c := GlobalTheory.Frames.allTest_of_secBaseChange hB E H Dw l Xo c
  obtain ⟨A, _, _, π, X, hred, hX, hA⟩ := exists_genericRing c.F K (E →+* ℂ) Dw.mult
  obtain ⟨u₀, hu₀⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap hB E H Dw l Xo c K A π y
  obtain ⟨u, hu, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c A u₀ (fun b => (X b).transpose) 1
    (fun b => by rw [Matrix.det_transpose]; exact hX b)
  obtain ⟨P, N, hP⟩ := hA (evR Xo c F u)
  refine ⟨P, N, fun S _ _ φ z z' Y hY hz hz' => ?_⟩
  obtain ⟨k, hkπ, hkX, hk⟩ := hP S φ Y hY
  obtain ⟨w, hw⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap hB E H Dw l Xo c A S k u₀
  have hw' : FrMap (k.comp π) y w := frMap_trans (Xo := Xo) (c := c) _ _ _ π k y u₀ w hu₀ hw
  rw [hkπ] at hw'
  have hwz : w = z := (GlobalTheory.Frames.frMap_unique_refl_iff E H Dw l Xo c K S φ y).1 w z hw' hz
  subst hwz
  have hm : FrMap k u z' := by
    refine (GlobalTheory.Frames.ChgBC.frChg_baseChange E H Dw l Xo c A S k u₀ u w z' _ _ hu hw).2 ?_
    have e : (fun τ => ((X τ).transpose).map k) = fun b => (Y b).transpose :=
      funext fun b => by rw [Matrix.transpose_map, hkX]
    rw [e, Units.val_one, map_one]
    exact hz'
  rw [evR_frMap hWD F hF.1 k u (hT _ u) z' hm]
  exact hk

end GlobalTheory.LamT.RatFn
