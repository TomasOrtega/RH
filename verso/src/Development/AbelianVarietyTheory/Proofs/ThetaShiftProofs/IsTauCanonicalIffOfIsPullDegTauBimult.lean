import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback

noncomputable section

namespace GlobalTheory.TauCanPull

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.TauTwist GlobalTheory.ArcPull
open GlobalTheory.PsiEvenPull (proj)

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'}

/- English proof (translation)
Rewrite using `[cP, toUnit_unit, Category.id_comp]`.
-/
theorem cPoint_unit (D : DegPre R) (y : D.X) : cP D (𝟙_ (Over (Sp R))) y = D.c y := by
  rw [cP, toUnit_unit, Category.id_comp]

/- English proof (translation)
Rewrite using `[← cPoint_unit D (n • y), ← cPoint_unit D 0, cPoint_nsmul, cPoint_zero, cPoint_unit]`.
-/
theorem c_pow_eq_one_iff (D : DegPre R) (n : ℕ) (y : D.X) : D.c y ^ n = 1 ↔ D.c (n • y) = D.c 0 := by
  rw [← cPoint_unit D (n • y), ← cPoint_unit D 0, cPoint_nsmul, cPoint_zero, cPoint_unit]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `Over.OverMorphism.ext ((pull_grp hD).1.hom_ext ?_ (by rw [Over.w, Over.w]))` and prove the remaining obligations. Rewrite using `[hD.c_pr, hD.c_pr, h]`. Introduce `h haveI : IsDominant (spMap φ) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical φ).2 (by`.

Rewrite using `[(RingHom.injective_iff_ker_eq_bot φ).1 hφ]`. Conclude with `bot_le)⟩`. Use `haveI : IsProper D.P.A.hom := D.P.isAb.proper`. Conclude with `Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated (X := Sp R) D.P.A.hom ((Over.w _).trans (Over.w _).symm) (spMap φ) ((hD.c_pr x).symm.trans ((congrArg (fun q => q.left ≫ _) h).trans (hD.c_pr x'))))`.
-/
theorem c_eq_iff (hD : IsPullDeg φ D D') (hφ : Function.Injective φ) (x x' : D'.X) :
    D.c (hD.xe x) = D.c (hD.xe x') ↔ D'.c x = D'.c x' := by
  constructor
  · intro h
    refine Over.OverMorphism.ext ((pull_grp hD).1.hom_ext ?_ (by rw [Over.w, Over.w]))
    rw [hD.c_pr, hD.c_pr, h]
  · intro h
    haveI : IsDominant (spMap φ) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical φ).2 (by
      rw [(RingHom.injective_iff_ker_eq_bot φ).1 hφ]; exact bot_le)⟩
    haveI : IsProper D.P.A.hom := D.P.isAb.proper
    exact Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated (X := Sp R) D.P.A.hom
      ((Over.w _).trans (Over.w _).symm) (spMap φ)
      ((hD.c_pr x).symm.trans ((congrArg (fun q => q.left ≫ _) h).trans (hD.c_pr x'))))

/- English proof (translation)
Rewrite using `[hD.xe.surjective.forall]`. Use `forall_congr' fun y => ?_` and prove the remaining obligations. Rewrite using `[c_pow_eq_one_iff, c_pow_eq_one_iff, ← c_eq_iff hD hφ, map_nsmul, map_zero]`.
-/
theorem torsion_iff (hD : IsPullDeg φ D D') (hφ : Function.Injective φ) (n : ℕ) :
    (∀ y, D.c y ^ n = 1) ↔ ∀ y, D'.c y ^ n = 1 := by
  rw [hD.xe.surjective.forall]
  refine forall_congr' fun y => ?_
  rw [c_pow_eq_one_iff, c_pow_eq_one_iff, ← c_eq_iff hD hφ, map_nsmul, map_zero]

/- English proof (translation)
Establish `h : LB.Gen.Corr D.P.L _ _ _ _ (D.tau (n • a) (n • b)) (scaleGen (unitOn (kappa hc a b)) (LB.oneGen D.P.L))` using `corr_of_val D.P.isLB fun y I hI => (unitAt_kappa hc a b hI).symm.trans ((val_scale _ _ _ hI).trans ((congrArg₂ (· * ·) rfl (val_one _)).trans (_root_.mul_one _))).symm`. Conclude with `(val_corr hJ h r).trans ((val_scale _ _ _ hJ).trans ((congrArg₂ (· * ·) rfl (val_one _)).trans (_root_.mul_one _)))`.
-/
theorem val_tau_kappa {n : ℕ} (hc : ∀ y, D.c y ^ n = 1) (a b : D.X) {Z : Scheme.{0}} (r : Z ⟶ (TK R).left) {z : Z} {J}
    (hJ : Good D.P.L z J) : val (D.tau (n • a) (n • b)) r z J = unitAt r z (kappa hc a b) := by
  have h : LB.Gen.Corr D.P.L _ _ _ _ (D.tau (n • a) (n • b)) (scaleGen (unitOn (kappa hc a b)) (LB.oneGen D.P.L)) :=
    corr_of_val D.P.isLB fun y I hI => (unitAt_kappa hc a b hI).symm.trans
      ((val_scale _ _ _ hI).trans ((congrArg₂ (· * ·) rfl (val_one _)).trans (_root_.mul_one _))).symm
  exact (val_corr hJ h r).trans ((val_scale _ _ _ hJ).trans ((congrArg₂ (· * ·) rfl (val_one _)).trans
    (_root_.mul_one _)))

/- English proof (translation)
Set `z : (TK R').left` to `IsLocalRing.closedPoint (FractionRing R')`. Take `⟨J, hJ⟩` from `DegPull.exists_good' D.P.isLB z`. Take `⟨J', hJ'⟩` from `DegPull.exists_good' D'.P.isLB z`. Establish `e` using `tau_val hD _ _ (fracMap_sq hφ) hJ hJ' (n • a) (n • b)`. Establish `a₁ : ∀ w : D'.X, D'.xK (n • w) = (1 : TK R' ⟶ D'.P.A).left` using `fun w => congrArg (fun q => q.left) (cPoint_nsmul_eq_one hc' (TK R') w)`.

Rewrite `e` using `[map_nsmul, map_nsmul, val_tau_kappa hc _ _ _ hJ, val_tau_kappa hc' _ _ _ hJ', ← nsmul_add, a₁, a₁, a₁, inv_mul_cancel, _root_.one_mul, mul_inv_cancel, _root_.one_mul]`. Use `unitAt_injective z (e.symm.trans ?_)` and prove the remaining obligations. Conclude with `(congrArg (fun q => unitAt q z _) (Category.id_comp (genMap hφ)).symm).trans (unitAt_spMap (𝟙 _) (fracMap hφ) z _)`.
-/
theorem kappa_pull (hD : IsPullDeg φ D D') (hφ : Function.Injective φ) {n : ℕ} (hc : ∀ y, D.c y ^ n = 1)
    (hc' : ∀ y, D'.c y ^ n = 1) (a b : D'.X) :
    kappa hc' a b = Units.map (fracMap hφ).toMonoidHom (kappa hc (hD.xe a) (hD.xe b)) := by
  let z : (TK R').left := IsLocalRing.closedPoint (FractionRing R')
  obtain ⟨J, hJ⟩ := DegPull.exists_good' D.P.isLB z
  obtain ⟨J', hJ'⟩ := DegPull.exists_good' D'.P.isLB z
  have e := tau_val hD _ _ (fracMap_sq hφ) hJ hJ' (n • a) (n • b)
  have a₁ : ∀ w : D'.X, D'.xK (n • w) = (1 : TK R' ⟶ D'.P.A).left := fun w =>
    congrArg (fun q => q.left) (cPoint_nsmul_eq_one hc' (TK R') w)
  rw [map_nsmul, map_nsmul, val_tau_kappa hc _ _ _ hJ, val_tau_kappa hc' _ _ _ hJ', ← nsmul_add, a₁, a₁, a₁,
    inv_mul_cancel, _root_.one_mul, mul_inv_cancel, _root_.one_mul] at e
  refine unitAt_injective z (e.symm.trans ?_)
  exact (congrArg (fun q => unitAt q z _) (Category.id_comp (genMap hφ)).symm).trans
    (unitAt_spMap (𝟙 _) (fracMap hφ) z _)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hc, h⟩`. Use `⟨(torsion_iff hD hφ n).1 hc, fun y y' => ?_⟩` and prove the remaining obligations. Rewrite using `[kappa_pull hD hφ hc, h, map_one]`. Introduce and unpack `⟨hc', h⟩`.

Use `⟨(torsion_iff hD hφ n).2 hc', fun y y' => ?_⟩` and prove the remaining obligations. Take `⟨y, rfl⟩` from `hD.xe.surjective y`. Take `⟨y', rfl⟩` from `hD.xe.surjective y'`. Apply `Units.map_injective (f := (fracMap hφ).toMonoidHom) (fracMap hφ).injective` to reduce the goal to its premises. Rewrite using `[← kappa_pull hD hφ _ hc', h, map_one]`.
-/
theorem tauCan_iff (hD : IsPullDeg φ D D') (hφ : Function.Injective φ) (n : ℕ) :
    ArcCM.TauCan D n ↔ ArcCM.TauCan D' n := by
  constructor
  · rintro ⟨hc, h⟩
    refine ⟨(torsion_iff hD hφ n).1 hc, fun y y' => ?_⟩
    rw [kappa_pull hD hφ hc, h, map_one]
  · rintro ⟨hc', h⟩
    refine ⟨(torsion_iff hD hφ n).2 hc', fun y y' => ?_⟩
    obtain ⟨y, rfl⟩ := hD.xe.surjective y
    obtain ⟨y', rfl⟩ := hD.xe.surjective y'
    apply Units.map_injective (f := (fracMap hφ).toMonoidHom) (fracMap hφ).injective
    rw [← kappa_pull hD hφ _ hc', h, map_one]

end

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

/- English proof (translation)
Introduce `_ _ _ _ _ _ _ _ _ _ _ _ p n hf _ _` and use `tauCan_iff p hf n`.
-/
theorem tauCan_iff_of_isPullDeg : Known → ∀ (R R' : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [CommRing R'] [IsDomain R'] [IsNoetherianRing R'] (f : R →+* R') (D₀ : Out.DegPre R) (D₁ : Out.DegPre R') (p : Out.IsPullDeg f D₀ D₁) (n : ℕ), Function.Injective f → D₀.TauBimult → D₁.TauBimult → (TauCan D₀ n ↔ TauCan D₁ n) :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ p n hf _ _ => tauCan_iff p hf n

end GlobalTheory.TauCanPull
