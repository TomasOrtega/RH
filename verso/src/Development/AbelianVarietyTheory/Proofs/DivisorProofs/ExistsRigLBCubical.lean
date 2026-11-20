import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsOfPoint
import Development.AbelianVarietyTheory.Definitions.Divisors.PerFactor
import Development.AbelianVarietyTheory.Definitions.Divisors.IsMumfordFamOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Divisors.IsBasOpens
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpPullbackId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteEtaleOfEtale
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullEqZeroOfChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymLam
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteMulByNatAbelianVariety
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleTrivialOfSamePolarization
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentDatumCompatibleOfLineBundleIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentCocycleDefectOfCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleDescentFiniteFlatStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelObjectPullbackExistsAndPrincipal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubicalStrOfTrivTheta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamPolarizationFormPrimitive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TheoremOfCubeAbelianSchemeOverArbitraryBase
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FlatAndSurjectiveOfIsFiniteAbelianEnd
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsIsGenOfUniqueFactorizationMonoid
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleObstructionZeroOfRestrictionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleLiftSquareZeroOfMumfordBundleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoMumfordLambdaOfLocalQuotientStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleRootLiftsFromResidueCompleteLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleRootExistsOverFgSubalgebraStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteLocalGeomDomainStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSeparablePointOfGeometricallyDomainStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricTwoCocycleFiniteCommGroupSchemeCoboundaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareBundleDescentOfDefectKilledStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescentCocycleDefectIsTripleCocycleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitKillingSquareTripleFibreCocycleMulTwoStatement

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolBundleLoc

open GlobalTheory.PolRoot GlobalTheory.CechPic GlobalTheory.LamOfDouble

/- English proof (translation)
Establish `hR : Out.Rigidified B L` using `GlobalTheory.LB.exists_isGen_of_isLocalRing (R := R) (pull_isLB hL _)`. Conclude with `GlobalTheory.Moduli.cubicalStr_of_triv_theta GlobalTheory.abelianSchemeLaws_all.1 _ B hB L hL hR (GlobalTheory.HodgeWeil.triv_theta GlobalTheory.CubeTop.cubeTheorem hB hL)`.
-/
theorem exists_rigLB_cubical (R : Type) [CommRing R] [IsLocalRing R] (B : Over (Sp R)) [GrpObj B] [IsCommMonObj B]
    (hB : IsAbelianScheme B) (L : LB B.left) (hL : L.IsLB) : ∃ M : RigLB B, M.L = L ∧ Nonempty (CubicalStr B M) := by
  have hR : Out.Rigidified B L := GlobalTheory.LB.exists_isGen_of_isLocalRing (R := R) (pull_isLB hL _)
  exact GlobalTheory.Moduli.cubicalStr_of_triv_theta GlobalTheory.abelianSchemeLaws_all.1 _ B hB L hL hR
    (GlobalTheory.HodgeWeil.triv_theta GlobalTheory.CubeTop.cubeTheorem hB hL)

/- English proof (translation)
Establish `hf` using `GlobalTheory.MulFinite.isFinite_mul K A hA 2 (by norm_num)`. Establish `hm : IsMonHom ((𝟙 A) ^ 2 : A ⟶ A)`. Rewrite using `[← GlobalTheory.GrpTangent.mulN_eq_pow]`. Use `infer_instance`. Take `⟨hfl, hsu⟩` from `GlobalTheory.flat_and_surjective_of_isFinite_abelianEnd GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected K A hA _ hm hf`.

Use `hA.smooth` as an intermediate fact. Establish `: IsLocallyNoetherian A.left` using `LocallyOfFiniteType.isLocallyNoetherian A.hom`. Take `⟨φ, hφ⟩` from `GlobalTheory.LBDescent.descCompat_of_lbIso _ M hM H`. Take `⟨D, hD⟩` from `GlobalTheory.T.exists_descentCocycleDefect_of_compatible _ M φ hM hφ`. Take `⟨u, hu⟩` from `GlobalTheory.T.exists_unit_killing_square_tripleFibreCocycle_mulTwo K A hA hf D (GlobalTheory.T.descentCocycleDefect_isTripleCocycle _ _ _ M hM φ D hD)`.

Take `⟨M₂, ψ, hM₂, e, hc, hco⟩` from `GlobalTheory.T.exists_squareBundle_descent_of_defect_killed _ _ _ M hM φ D u hφ hD hu`. Take `⟨L, hL, e'⟩` from `GlobalTheory.T.exists_lineBundle_descent_finiteFlat _ _ ((𝟙 A) ^ 2 : A ⟶ A).left M₂ hM₂ ψ hc hco`. Establish `hP : (lbPow M 2).IsLB` using `LB.isLB_linComb hM _ _`. Conclude with `⟨L, hL, (cls_eq_iff hP (pull_isLB hL _)).1 (((cls_eq_iff hP hM₂).2 e).trans ((cls_eq_iff hM₂ (pull_isLB hL _)).2 e'))⟩`.
-/
theorem exists_descent_two {K : Type} [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A]
    (hA : IsAbelianScheme A) {M : LB A.left} (hM : M.IsLB)
    (H : LBIso (M.pull (pullback.fst ((𝟙 A) ^ 2 : A ⟶ A).left ((𝟙 A) ^ 2 : A ⟶ A).left))
      (M.pull (pullback.snd ((𝟙 A) ^ 2 : A ⟶ A).left ((𝟙 A) ^ 2 : A ⟶ A).left))) :
    ∃ L : LB A.left, L.IsLB ∧ LBIso (lbPow M 2) (L.pull ((𝟙 A) ^ 2 : A ⟶ A).left) := by
  have hf := GlobalTheory.MulFinite.isFinite_mul K A hA 2 (by norm_num)
  have hm : IsMonHom ((𝟙 A) ^ 2 : A ⟶ A) := by
    rw [← GlobalTheory.GrpTangent.mulN_eq_pow]; infer_instance
  obtain ⟨hfl, hsu⟩ := GlobalTheory.flat_and_surjective_of_isFinite_abelianEnd
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected K A hA _ hm hf
  have := hA.smooth
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  obtain ⟨φ, hφ⟩ := GlobalTheory.LBDescent.descCompat_of_lbIso _ M hM H
  obtain ⟨D, hD⟩ := GlobalTheory.T.exists_descentCocycleDefect_of_compatible _ M φ hM hφ
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_unit_killing_square_tripleFibreCocycle_mulTwo K A hA hf D (GlobalTheory.T.descentCocycleDefect_isTripleCocycle _ _ _ M hM φ D hD)
  obtain ⟨M₂, ψ, hM₂, e, hc, hco⟩ := GlobalTheory.T.exists_squareBundle_descent_of_defect_killed _ _ _ M hM φ D u hφ hD hu
  obtain ⟨L, hL, e'⟩ := GlobalTheory.T.exists_lineBundle_descent_finiteFlat _ _ ((𝟙 A) ^ 2 : A ⟶ A).left M₂ hM₂ ψ hc hco
  have hP : (lbPow M 2).IsLB := LB.isLB_linComb hM _ _
  exact ⟨L, hL, (cls_eq_iff hP (pull_isLB hL _)).1
    (((cls_eq_iff hP hM₂).2 e).trans ((cls_eq_iff hM₂ (pull_isLB hL _)).2 e'))⟩

/- English proof (translation)
Establish `e : cls P hP = ev (cls P hP) (snd A A) (fst A A)` using `(cls_eq_iff hP (pull_isLB hP _)).2 hs`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem ev_symm {S : Scheme.{0}} {A : Over S} {P : LB (A ⊗ A).left} (hP : P.IsLB)
    (hs : LBIso P (P.pull (lift (snd A A) (fst A A)).left)) (T : Over S) (x y : T ⟶ A) :
    ev (cls P hP) x y = ev (cls P hP) y x := by
  have e : cls P hP = ev (cls P hP) (snd A A) (fst A A) := (cls_eq_iff hP (pull_isLB hP _)).2 hs
  calc ev (cls P hP) x y = pull (lift x y).left (ev (cls P hP) (snd A A) (fst A A)) := by rw [← e]; rfl
    _ = ev (cls P hP) y x := by rw [pull_ev, lift_fst, lift_snd]

/- English proof (translation)
Establish `hLaws : Out.Laws` using `GlobalTheory.lawsAndExpansions.1.1`. Establish `hM : (P.pull (lift (𝟙 A) (𝟙 A)).left).IsLB` using `pull_isLB hP _`. Establish `bP : Biadd (cls P hP)` using `biadd_of_axes hLaws.globalFns hA _ hM ha _ hP r₁ r₂`. Establish `sy` using `ev_symm hP hs`. Use `set p := cls P hP with hp`.

Establish `hm : ∀ (T : Over (Sp K)) (x : T ⟶ A), pull x.left (cls _ hM) = ev p x x` using `fun T x => (pull_ev x p (𝟙 A) (𝟙 A)).trans (by rw [Category.comp_id])`. Establish `h1 : ∀ (T : Over (Sp K)) (y : T ⟶ A), ev p 1 y = 0` using `fun T y => by`. Use `(bP T 1 1 y).1` as an intermediate fact. Rewrite `this` using `[_root_.mul_one]`. Conclude with `left_eq_add.1 this`.

Establish `hψ : ∀ {T : Over (Sp K)} (x : T ⟶ A), x ≫ ((𝟙 A) ^ 2 : A ⟶ A) = x * x` using `fun x => by`. Rewrite using `[MonObj.comp_pow, Category.comp_id, pow_two]`. Establish `hker : ∀ (T : Over (Sp K)) (t : T ⟶ A), t * t = 1 → ev p t t = 0`. Introduce `T t ht`. Establish `hf` using `GlobalTheory.MulFinite.isFinite_mul K A hA 2 (by norm_num)`.

Set `N` to `pullback ((𝟙 A) ^ 2 : A ⟶ A).left (η[A]).left`. Establish `hfin : IsFinite (pullback.snd ((𝟙 A) ^ 2 : A ⟶ A).left (η[A]).left)` using `inferInstance`. Use `haveI : IsAffine (𝟙_ (Over (Sp K))).left := inferInstanceAs (IsAffine (Sp K))`. Establish `haff : IsAffine N` using `isAffine_of_isAffineHom (pullback.snd ((𝟙 A) ^ 2 : A ⟶ A).left (η[A]).left)`. Use `haveI : IsAffine (𝟙_ (Over (Sp K))).left := inferInstanceAs (IsAffine (Sp K))`.

Establish `hN : Finite N` using `by haveI : IsFinite (𝟙_ (Over (Sp K))).hom := inferInstanceAs (IsFinite (𝟙 (Sp K)))`. Establish `hq` using `((pullback.snd ((𝟙 A) ^ 2 : A ⟶ A).left (η[A]).left) ≫ (𝟙_ (Over (Sp K))).hom).finite_preimage_singleton (⊥ : PrimeSpectrum K)`. Conclude with `Set.finite_univ_iff.1 (hq.subset fun x _ => Subsingleton.elim _ _)`. Establish `w : t.left ≫ ((𝟙 A) ^ 2 : A ⟶ A).left = T.hom ≫ (η[A]).left`. Rewrite using `[← Over.comp_left, hψ, ht]`.

Both sides reduce to the same expression. Establish `z : pull (pullback.fst ((𝟙 A) ^ 2 : A ⟶ A).left (η[A]).left) (cls _ hM) = 0` using `(cls_eq_zero_iff (pull_isLB hM _)).2 (GlobalTheory.exists_isGen_of_finite (pull_isLB hM _))`. Rewrite using `[← hm, ← pullback.lift_fst t.left T.hom w, pull_comp, z, map_zero]`. Take `⟨L, hL, e⟩` from `exists_descent_two A hA hM (by`. Set `f` to `((𝟙 A) ^ 2 : A ⟶ A).left`.

Set `T : Over (Sp K)` to `Over.mk (pullback.fst f f ≫ A.hom)`. Set `x : T ⟶ A` to `Over.homMk (pullback.fst f f) rfl`. Set `y : T ⟶ A` to `Over.homMk (pullback.snd f f) (by show pullback.snd f f ≫ A.hom = pullback.fst f f ≫ A.hom`. Rewrite using `[← Over.w ((𝟙 A) ^ 2 : A ⟶ A), ← Category.assoc, ← Category.assoc]`. Conclude with `congrArg (· ≫ A.hom) pullback.condition.symm)`.

Establish `exy : x * x = y * y`. Rewrite using `[← hψ, ← hψ]`. Conclude with `Over.OverMorphism.ext pullback.condition`. Establish `ht : (x⁻¹ * y) * (x⁻¹ * y) = 1`. Rewrite using `[_root_.mul_mul_mul_comm, ← exy, ← mul_inv, inv_mul_cancel]`.

Use `(cls_eq_iff (pull_isLB hM _) (pull_isLB hM _)).1 ((hm T x).trans (Eq.trans ?_ (hm T y).symm))` and prove the remaining obligations. Establish `ey : y = x * (x⁻¹ * y)` using `by rw [mul_inv_cancel_left]`. Generalize the expression as in `x⁻¹ * y = t at ht ey`. Establish `h2 : ev p t x + ev p t x = 0` using `by rw [← (bP T t t x).1, ht, h1]`. Rewrite using `[ey, (bP T _ _ _).1, (bP T _ _ _).2, (bP T _ _ _).2, hker T t ht, sy T x t, add_zero, add_assoc, h2, add_zero])`.

Establish `hΛ` using `GlobalTheory.SymBiextHalf.lam_iso hLaws hA hM ha hP bP sy hL e`. Use `⟨L, hL, hΛ, ?_⟩` and prove the remaining obligations. Establish `hLam : (abelian₂ A L).IsLB` using `LB.isLB_linComb hL _ _`. Establish `hPow : (lbPow (P.pull (lift (𝟙 A) (𝟙 A)).left) 2).IsLB` using `LB.isLB_linComb hM _ _`. Establish `hL2 : (lbPow L 2).IsLB` using `LB.isLB_linComb hL _ _`.

Establish `c₁ : p = lam (cls L hL) (fst A A) (snd A A)` using `((cls_eq_iff hLam hP).2 hΛ).symm.trans (cls_cube_two hL _ _ hLam)`. Establish `c₂ : 2 • cls _ hM = pull ((𝟙 A) ^ 2 : A ⟶ A).left (cls L hL)` using `(cls_lbPow hM 2 hPow).symm.trans ((cls_eq_iff hPow (pull_isLB hL _)).2 e)`. Establish `c₃ : cls _ hM = lam (cls L hL) (𝟙 A) (𝟙 A)`. Use `hm A (𝟙 A)` as an intermediate fact. Rewrite `this` using `[Over.id_left, pull_id]`.

Rewrite using `[this, ev, c₁, pull_lam, lift_fst, lift_snd]`. Establish `c₄ : pull (1 : A ⟶ A).left (cls L hL) = 0`. Establish `z : pull (η[A]).left (cls L hL) = 0` using `(cls_eq_zero_iff (pull_isLB hL _)).2 (GlobalTheory.LB.exists_isGen_of_isLocalRing (R := K) (pull_isLB hL _))`. Use `show pull (toUnit A ≫ η[A]).left _ = 0`. Rewrite using `[Over.comp_left, pull_comp, z, map_zero]`.

Establish `c₅ : cls _ hL2 = cls _ hM`. Rewrite using `[cls_lbPow hL 2 hL2]`. Rewrite `c₃` using `[lam, c₄, ← pow_two, ← c₂, Over.id_left, pull_id]`. Take the linear combination `(norm := abel) c₃`. Use `hA.proper` as an intermediate fact.

Rewrite using `[relAmple_iff_isAmpleLB_of_isAffine A hL, ← isAmpleLB_pow_iff hL (k := 2) (by norm_num), isAmpleLB_congr hL2 hM ((cls_eq_iff hL2 hM).1 c₅), ← relAmple_iff_isAmpleLB_of_isAffine A hM]`. Conclude with `ha`.
-/
theorem exists_ample_root {K : Type} [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A]
    (hA : IsAbelianScheme A) {P : LB (G2 A).left} (hP : P.IsLB)
    (r₁ : ∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen)
    (r₂ : ∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen)
    (hs : LBIso P (P.pull (lift (snd A A) (fst A A)).left)) (ha : RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left)) :
    ∃ L : LB A.left, L.IsLB ∧ LBIso (abelian₂ A L) P ∧ RelAmple A L := by
  have hLaws : Out.Laws := GlobalTheory.lawsAndExpansions.1.1
  have hM : (P.pull (lift (𝟙 A) (𝟙 A)).left).IsLB := pull_isLB hP _
  have bP : Biadd (cls P hP) := biadd_of_axes hLaws.globalFns hA _ hM ha _ hP r₁ r₂
  have sy := ev_symm hP hs
  set p := cls P hP with hp
  have hm : ∀ (T : Over (Sp K)) (x : T ⟶ A), pull x.left (cls _ hM) = ev p x x := fun T x =>
    (pull_ev x p (𝟙 A) (𝟙 A)).trans (by rw [Category.comp_id])
  have h1 : ∀ (T : Over (Sp K)) (y : T ⟶ A), ev p 1 y = 0 := fun T y => by
    have := (bP T 1 1 y).1
    rw [_root_.mul_one] at this
    exact left_eq_add.1 this
  have hψ : ∀ {T : Over (Sp K)} (x : T ⟶ A), x ≫ ((𝟙 A) ^ 2 : A ⟶ A) = x * x := fun x => by
    rw [MonObj.comp_pow, Category.comp_id, pow_two]

  have hker : ∀ (T : Over (Sp K)) (t : T ⟶ A), t * t = 1 → ev p t t = 0 := by
    intro T t ht
    have hf := GlobalTheory.MulFinite.isFinite_mul K A hA 2 (by norm_num)
    let N := pullback ((𝟙 A) ^ 2 : A ⟶ A).left (η[A]).left
    have hfin : IsFinite (pullback.snd ((𝟙 A) ^ 2 : A ⟶ A).left (η[A]).left) := inferInstance
    haveI : IsAffine (𝟙_ (Over (Sp K))).left := inferInstanceAs (IsAffine (Sp K))
    have haff : IsAffine N := isAffine_of_isAffineHom (pullback.snd ((𝟙 A) ^ 2 : A ⟶ A).left (η[A]).left)
    haveI : IsAffine (𝟙_ (Over (Sp K))).left := inferInstanceAs (IsAffine (Sp K))
    have hN : Finite N := by
      haveI : IsFinite (𝟙_ (Over (Sp K))).hom := inferInstanceAs (IsFinite (𝟙 (Sp K)))
      have hq := ((pullback.snd ((𝟙 A) ^ 2 : A ⟶ A).left (η[A]).left) ≫ (𝟙_ (Over (Sp K))).hom).finite_preimage_singleton
        (⊥ : PrimeSpectrum K)
      exact Set.finite_univ_iff.1 (hq.subset fun x _ => Subsingleton.elim _ _)
    have w : t.left ≫ ((𝟙 A) ^ 2 : A ⟶ A).left = T.hom ≫ (η[A]).left := by
      rw [← Over.comp_left, hψ, ht]; rfl
    have z : pull (pullback.fst ((𝟙 A) ^ 2 : A ⟶ A).left (η[A]).left) (cls _ hM) = 0 :=
      (cls_eq_zero_iff (pull_isLB hM _)).2 (GlobalTheory.exists_isGen_of_finite (pull_isLB hM _))
    rw [← hm, ← pullback.lift_fst t.left T.hom w, pull_comp, z, map_zero]
  obtain ⟨L, hL, e⟩ := exists_descent_two A hA hM (by
    let f := ((𝟙 A) ^ 2 : A ⟶ A).left
    let T : Over (Sp K) := Over.mk (pullback.fst f f ≫ A.hom)
    let x : T ⟶ A := Over.homMk (pullback.fst f f) rfl
    let y : T ⟶ A := Over.homMk (pullback.snd f f) (by
      show pullback.snd f f ≫ A.hom = pullback.fst f f ≫ A.hom
      rw [← Over.w ((𝟙 A) ^ 2 : A ⟶ A), ← Category.assoc, ← Category.assoc]
      exact congrArg (· ≫ A.hom) pullback.condition.symm)
    have exy : x * x = y * y := by
      rw [← hψ, ← hψ]
      exact Over.OverMorphism.ext pullback.condition
    have ht : (x⁻¹ * y) * (x⁻¹ * y) = 1 := by
      rw [_root_.mul_mul_mul_comm, ← exy, ← mul_inv, inv_mul_cancel]
    refine (cls_eq_iff (pull_isLB hM _) (pull_isLB hM _)).1 ((hm T x).trans (Eq.trans ?_ (hm T y).symm))
    have ey : y = x * (x⁻¹ * y) := by rw [mul_inv_cancel_left]
    generalize x⁻¹ * y = t at ht ey
    have h2 : ev p t x + ev p t x = 0 := by rw [← (bP T t t x).1, ht, h1]
    rw [ey, (bP T _ _ _).1, (bP T _ _ _).2, (bP T _ _ _).2, hker T t ht, sy T x t, add_zero, add_assoc, h2, add_zero])
  have hΛ := GlobalTheory.SymBiextHalf.lam_iso hLaws hA hM ha hP bP sy hL e
  refine ⟨L, hL, hΛ, ?_⟩
  have hLam : (abelian₂ A L).IsLB := LB.isLB_linComb hL _ _
  have hPow : (lbPow (P.pull (lift (𝟙 A) (𝟙 A)).left) 2).IsLB := LB.isLB_linComb hM _ _
  have hL2 : (lbPow L 2).IsLB := LB.isLB_linComb hL _ _
  have c₁ : p = lam (cls L hL) (fst A A) (snd A A) :=
    ((cls_eq_iff hLam hP).2 hΛ).symm.trans (cls_cube_two hL _ _ hLam)
  have c₂ : 2 • cls _ hM = pull ((𝟙 A) ^ 2 : A ⟶ A).left (cls L hL) :=
    (cls_lbPow hM 2 hPow).symm.trans ((cls_eq_iff hPow (pull_isLB hL _)).2 e)
  have c₃ : cls _ hM = lam (cls L hL) (𝟙 A) (𝟙 A) := by
    have := hm A (𝟙 A)
    rw [Over.id_left, pull_id] at this
    rw [this, ev, c₁, pull_lam, lift_fst, lift_snd]
  have c₄ : pull (1 : A ⟶ A).left (cls L hL) = 0 := by
    have z : pull (η[A]).left (cls L hL) = 0 :=
      (cls_eq_zero_iff (pull_isLB hL _)).2 (GlobalTheory.LB.exists_isGen_of_isLocalRing (R := K) (pull_isLB hL _))
    show pull (toUnit A ≫ η[A]).left _ = 0
    rw [Over.comp_left, pull_comp, z, map_zero]
  have c₅ : cls _ hL2 = cls _ hM := by
    rw [cls_lbPow hL 2 hL2]
    rw [lam, c₄, ← pow_two, ← c₂, Over.id_left, pull_id] at c₃
    linear_combination (norm := abel) c₃
  have := hA.proper
  rw [relAmple_iff_isAmpleLB_of_isAffine A hL, ← isAmpleLB_pow_iff hL (k := 2) (by norm_num),
    isAmpleLB_congr hL2 hM ((cls_eq_iff hL2 hM).1 c₅), ← relAmple_iff_isAmpleLB_of_isAffine A hM]
  exact ha

section Siegel

variable {o : Type} [CommRing o] {ζ : o} {g n : ℕ} (F : SFam g n ζ)

/- English proof (translation)
Take `⟨φ, φ₂, pb, sq, iso, -⟩` from `h`. Establish `hΛ : (abelian₂ c.A L).IsLB` using `LB.isLB_linComb hL _ _`. Conclude with `⟨c.A, inferInstance, inferInstance, φ, φ₂, pb, sq, L, hL, LBIso.trans hΛ c.isLB (pull_isLB F.univ.isLB _) e iso⟩`.
-/
theorem root_of_siegPB {S' : Scheme.{0}} {s' : S' ⟶ Sp o} (c : SiegPre g n ζ s') (x : S' ⟶ F.X)
    (h : SiegPB c F.univ x) (L : LB c.A.left) (hL : L.IsLB) (e : LBIso (abelian₂ c.A L) c.P) :
    Root F.univ.A F.univ.P x := by
  obtain ⟨φ, φ₂, pb, sq, iso, -⟩ := h
  have hΛ : (abelian₂ c.A L).IsLB := LB.isLB_linComb hL _ _
  exact ⟨c.A, inferInstance, inferInstance, φ, φ₂, pb, sq, L, hL,
    LBIso.trans hΛ c.isLB (pull_isLB F.univ.isLB _) e iso⟩

/- English proof (translation)
Take `⟨⟨c, hc⟩, hpr⟩` from `GlobalTheory.siegPre_pullback g n o ζ F.X (Sp K) F.s (x ≫ F.s) x F.univ rfl`. Establish `hcp` using `hpr c hc F.princ`. Take `⟨L, hL, e, -⟩` from `exists_ample_root c.A c.ab c.isLB c.rig₁ c.rig₂ c.symm hcp.1`. Conclude with `root_of_siegPB F c x hc L hL e`.
-/
theorem root_geom (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ F.X) : Root F.univ.A F.univ.P x := by
  obtain ⟨⟨c, hc⟩, hpr⟩ := GlobalTheory.siegPre_pullback g n o ζ F.X (Sp K) F.s (x ≫ F.s) x F.univ rfl
  have hcp := hpr c hc F.princ
  obtain ⟨L, hL, e, -⟩ := exists_ample_root c.A c.ab c.isLB c.rig₁ c.rig₂ c.symm hcp.1
  exact root_of_siegPB F c x hc L hL e

end Siegel

end GlobalTheory.PolBundleLoc
