import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.AdelicGL2ExtOfLocalComponents
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PowEqScaleAndExistsUniqueTorsion
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TheoremOfCubeProjectiveAbelianSchemeAffineBaseStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubicalStrOfTrivTheta
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FiniteFlatSurjectiveMulByNAbelianSchemeStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RatioTranslate
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubWeilPerfectOfGenericStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FiniteSections
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.KTrivOfGeometricPointsAndTangentsStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubWeilOfGen
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleIffVeryAmpleBy
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.KrullDimLEAndIsLocalRingQuotientPow
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct

noncomputable section
namespace GlobalTheory.GenericKTriv

section Pull

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A']
  {φ : A'.left ⟶ A.left} {L : LB A.left} {L' : LB A'.left}

/- English proof (translation)
Use `⟨fun x y e => Over.OverMorphism.ext (h.1.hom_ext (congrArg (fun q => q.left) e) (by rw [Over.w, Over.w])), fun x => ?_⟩` and prove the remaining obligations. Conclude with `⟨Over.homMk (h.1.lift x.left T.hom (Over.w x)) (h.1.lift_snd _ _ _), Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩`.
-/
theorem pushHom_bijective (h : IsGrpPullback A' A f φ) (T : Over S') : Function.Bijective (pushHom h T) := by
  refine ⟨fun x y e => Over.OverMorphism.ext
    (h.1.hom_ext (congrArg (fun q => q.left) e) (by rw [Over.w, Over.w])), fun x => ?_⟩
  exact ⟨Over.homMk (h.1.lift x.left T.hom (Over.w x)) (h.1.lift_snd _ _ _),
    Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩

/- English proof (translation)
Take `⟨w, hw⟩` from `e`. Take `⟨c, hc⟩` from `hx`. Set `T₀ : Over S` to `Over.mk (T.hom ≫ f)`. Set `a : Over.mk ((T ⊗ A').hom ≫ f) ⟶ T₀` to `Over.homMk (fst T A').left (by show (fst T A').left ≫ T.hom ≫ f = (T ⊗ A').hom ≫ f`. Rewrite using `[← Category.assoc, Over.w])`.

Set `j : Over.mk ((T ⊗ A').hom ≫ f) ⟶ T₀ ⊗ A` to `lift a (pushPt h.1.w (snd T A'))`. Establish `k₂ : j.left ≫ (snd T₀ A).left = (snd T A').left ≫ φ` using `congrArg (fun q => q.left) (lift_snd a (pushPt h.1.w (snd T A')))`. Establish `k₁ : j.left ≫ ((fst T₀ A ≫ pushHom h T x) * snd T₀ A).left = ((fst T A' ≫ x) * snd T A').left ≫ φ`. Establish `e : j ≫ ((fst T₀ A ≫ pushHom h T x) * snd T₀ A) = (a ≫ pushHom h T x) * pushPt h.1.w (snd T A')`. Rewrite using `[MonObj.comp_mul, lift_fst_assoc, lift_snd]`.

Establish `e₁` using `h.2 (T ⊗ A') (fst T A' ≫ x) (snd T A') (a ≫ pushHom h T x) (pushPt h.1.w (snd T A')) (Category.assoc (fst T A').left x.left φ).symm rfl`. Rewrite `e₁` using `[← e]`. Conclude with `e₁`. Establish `h4 : Triv (LB.LinComb L (K` using `Fin 2) (fun i => j.left ≫ ![(lift (fst T₀ A ≫ pushHom h T x) (snd T₀ A) ≫ μ[A]).left, (snd T₀ A).left] i) ![1, -1]) := ⟨_, DVR.pullGen_isGen _ _ _ c hc _⟩`. Establish `h3 : (fun i => j.left ≫ ![(lift (fst T₀ A ≫ pushHom h T x) (snd T₀ A) ≫ μ[A]).left, (snd T₀ A).left] i) = fun i => ![(lift (fst T A' ≫ x) (snd T A') ≫ μ[A']).left, (snd T A').left] i ≫ φ`.

Use function extensionality and compare the values at `i`. Use `fin_cases i`. Use `exacts [k₁, k₂]`. Rewrite `h4` using `[h3]`. Take `⟨c', hc'⟩` from `h4`.

Conclude with `exists_down ((isGen_iff w).1 hw) hL hL' c' hc'`.
-/
theorem triv_pull (h : IsGrpPullback A' A f φ) (hL : L.IsLB) (hL' : L'.IsLB) (e : LBIso L' (L.pull φ))
    {T : Over S'} (x : T ⟶ A') (hx : Triv (Out.translDiff A L (pushHom h T x))) :
    Triv (Out.translDiff A' L' x) := by
  obtain ⟨w, hw⟩ := e
  obtain ⟨c, hc⟩ := hx
  let T₀ : Over S := Over.mk (T.hom ≫ f)
  let a : Over.mk ((T ⊗ A').hom ≫ f) ⟶ T₀ := Over.homMk (fst T A').left (by
    show (fst T A').left ≫ T.hom ≫ f = (T ⊗ A').hom ≫ f
    rw [← Category.assoc, Over.w])
  let j : Over.mk ((T ⊗ A').hom ≫ f) ⟶ T₀ ⊗ A := lift a (pushPt h.1.w (snd T A'))
  have k₂ : j.left ≫ (snd T₀ A).left = (snd T A').left ≫ φ := congrArg (fun q => q.left) (lift_snd a (pushPt h.1.w (snd T A')))
  have k₁ : j.left ≫ ((fst T₀ A ≫ pushHom h T x) * snd T₀ A).left = ((fst T A' ≫ x) * snd T A').left ≫ φ := by
    have e : j ≫ ((fst T₀ A ≫ pushHom h T x) * snd T₀ A) = (a ≫ pushHom h T x) * pushPt h.1.w (snd T A') := by
      rw [MonObj.comp_mul, lift_fst_assoc, lift_snd]
    have e₁ := h.2 (T ⊗ A') (fst T A' ≫ x) (snd T A') (a ≫ pushHom h T x) (pushPt h.1.w (snd T A'))
      (Category.assoc (fst T A').left x.left φ).symm rfl
    rw [← e] at e₁
    exact e₁
  have h4 : Triv (LB.LinComb L (K := Fin 2) (fun i => j.left ≫
      ![(lift (fst T₀ A ≫ pushHom h T x) (snd T₀ A) ≫ μ[A]).left, (snd T₀ A).left] i) ![1, -1]) :=
    ⟨_, DVR.pullGen_isGen _ _ _ c hc _⟩
  have h3 : (fun i => j.left ≫
      ![(lift (fst T₀ A ≫ pushHom h T x) (snd T₀ A) ≫ μ[A]).left, (snd T₀ A).left] i) =
      fun i => ![(lift (fst T A' ≫ x) (snd T A') ≫ μ[A']).left, (snd T A').left] i ≫ φ := by
    funext i
    fin_cases i
    exacts [k₁, k₂]
  rw [h3] at h4
  obtain ⟨c', hc'⟩ := h4
  exact exists_down ((isGen_iff w).1 hw) hL hL' c' hc'

/- English proof (translation)
Substitute `hs` using the available equality. Take `⟨y, rfl⟩` from `(pushHom_bijective h (Over.mk t)).2 x`. Take `⟨c, hc⟩` from `triv_pull h hL hL' e y hx`. Establish `: y = 1` using `hK R t y fun p => ⟨⊤, trivial, _, LB.isGen_genPull _ c hc _⟩`. Rewrite using `[this]`.

Conclude with `map_one (pushHom h (Over.mk t))`.
-/
theorem eq_one_of_factor (h : IsGrpPullback A' A f φ) (hL : L.IsLB) (hL' : L'.IsLB) (e : LBIso L' (L.pull φ))
    (hK : Out.KTriv A' L') {R : Type} [CommRing R] (t : Sp R ⟶ S') {s : Sp R ⟶ S} (hs : s = t ≫ f)
    (x : Over.mk s ⟶ A) (hx : Triv (Out.translDiff A L x)) : x = 1 := by
  subst hs
  obtain ⟨y, rfl⟩ := (pushHom_bijective h (Over.mk t)).2 x
  obtain ⟨c, hc⟩ := triv_pull h hL hL' e y hx
  have : y = 1 := hK R t y fun p => ⟨⊤, trivial, _, LB.isGen_genPull _ c hc _⟩
  rw [this]
  exact map_one (pushHom h (Over.mk t))

/- English proof (translation)
Substitute `hs` using the available equality. Set `E` to `MulEquiv.ofBijective _ (pushHom_bijective h (Over.mk t))`. Use `(Nat.card_congr (E.toEquiv.subtypeEquiv fun x => ?_)).symm` and prove the remaining obligations. Use `show x ^ n = 1 ↔ E x ^ n = 1`. Rewrite using `[← map_pow, MulEquiv.map_eq_one_iff]`.
-/
theorem card_torsion (h : IsGrpPullback A' A f φ) {Y : Scheme.{0}} (t : Y ⟶ S') {s : Y ⟶ S} (hs : s = t ≫ f)
    (n : ℕ) : Nat.card {x : Over.mk s ⟶ A // x ^ n = 1} = Nat.card {x : Over.mk t ⟶ A' // x ^ n = 1} := by
  subst hs
  let E := MulEquiv.ofBijective _ (pushHom_bijective h (Over.mk t))
  refine (Nat.card_congr (E.toEquiv.subtypeEquiv fun x => ?_)).symm
  show x ^ n = 1 ↔ E x ^ n = 1
  rw [← map_pow, MulEquiv.map_eq_one_iff]

end Pull

/- English proof (translation)
Substitute `hs` using the available equality. Establish `h` using `PullbackComparison.isGrpPullback f A`. Establish `hM'` using `pull_isLB hM (PullbackComparison.pφ f A)`. Establish `e : LBIso (M.pull (PullbackComparison.pφ f A)) (M.pull (PullbackComparison.pφ f A))` using `PolBaseChange.lbIso_refl hM'`. Establish `hA'` using `PolPull.isAbelianScheme_of_isGrpPullback hA h`.

Use `hA'.comm` as an intermediate fact. Take `⟨y, rfl⟩` from `(pushHom_bijective h (Out.baseOver (Sp k))).2 x`. Establish `hy` using `triv_pull h hM hM' e y hx`. Take `⟨w, hw⟩` from `e`. Take `⟨m, hm, hy⟩` from `AmpleStabTorsion.exists_pow_eq_one hL k _ hA' _ hM' (relAmple_pull h.1 hM hM' ((isGen_iff w).1 hw) ⊤ (isAffineOpen_top _) (fun _ => trivial) hamp) y hy`.

Use `⟨m, hm, ?_⟩` and prove the remaining obligations. Conclude with `(map_pow (pushHom h _) y m).symm.trans ((congrArg (pushHom h _) hy).trans (map_one _))`.
-/
theorem field_torsion (hL : Out.Laws) {O : Type} [CommRing O] (A : Over (Sp O)) [GrpObj A] [IsCommMonObj A]
    (hA : IsAbelianScheme A) {M : LB A.left} (hM : M.IsLB) (hamp : Out.RelAmple A M) {k : Type} [Field k]
    [IsAlgClosed k] (f : Sp k ⟶ Sp O) {s : Sp k ⟶ Sp O} (hs : s = 𝟙 _ ≫ f) (x : Over.mk s ⟶ A)
    (hx : Triv (Out.translDiff A M x)) : ∃ m : ℕ, 1 ≤ m ∧ x ^ m = 1 := by
  subst hs
  have h := PullbackComparison.isGrpPullback f A
  have hM' := pull_isLB hM (PullbackComparison.pφ f A)
  have e : LBIso (M.pull (PullbackComparison.pφ f A)) (M.pull (PullbackComparison.pφ f A)) := PolBaseChange.lbIso_refl hM'
  have hA' := PolPull.isAbelianScheme_of_isGrpPullback hA h
  have := hA'.comm
  obtain ⟨y, rfl⟩ := (pushHom_bijective h (Out.baseOver (Sp k))).2 x
  have hy := triv_pull h hM hM' e y hx
  obtain ⟨w, hw⟩ := e
  obtain ⟨m, hm, hy⟩ := AmpleStabTorsion.exists_pow_eq_one hL k _ hA' _ hM'
    (relAmple_pull h.1 hM hM' ((isGen_iff w).1 hw) ⊤ (isAffineOpen_top _) (fun _ => trivial) hamp) y hy
  refine ⟨m, hm, ?_⟩
  exact (map_pow (pushHom h _) y m).symm.trans ((congrArg (pushHom h _) hy).trans (map_one _))

/- English proof (translation)
Set `F` to `FractionRing O`. Set `iF : F →+* K` to `IsFractionRing.lift hi`. Set `jF : F →+* R` to `IsLocalization.lift (M := nonZeroDivisors O) (g := j) fun y => hj y (nonZeroDivisors.ne_zero y.2)`. Use `letI : Algebra F K := iF.toAlgebra`. Use `letI : Algebra F R := jF.toAlgebra`.

Use `⟨R ⊗[F] K, inferInstance, algebraMap R (R ⊗[F] K), (Algebra.TensorProduct.includeRight : K →ₐ[F] R ⊗[F] K).toRingHom, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[RingHom.faithfullyFlat_algebraMap_iff] infer_instance`. Use extensionality with `o`. Establish `h₁ : j o = algebraMap F R (algebraMap O F o)` using `(IsLocalization.lift_eq _ o).symm`. Establish `h₂ : i o = algebraMap F K (algebraMap O F o)` using `(IsFractionRing.lift_algebraMap hi o).symm`.

Use `show algebraMap R (R ⊗[F] K) (j o) = (Algebra.TensorProduct.includeRight : K →ₐ[F] R ⊗[F] K) (i o)`. Rewrite using `[h₁, h₂, AlgHom.commutes, ← IsScalarTower.algebraMap_apply]`.
-/
theorem exists_cover {O K R : Type} [CommRing O] [IsDomain O] [Field K] [CommRing R] (i : O →+* K)
    (hi : Function.Injective i) (j : O →+* R) (hj : ∀ a : O, a ≠ 0 → IsUnit (j a)) :
    ∃ (R' : Type) (_ : CommRing R') (a : R →+* R') (b : K →+* R'), a.FaithfullyFlat ∧ a.comp j = b.comp i := by
  let F := FractionRing O
  let iF : F →+* K := IsFractionRing.lift hi
  let jF : F →+* R := IsLocalization.lift (M := nonZeroDivisors O) (g := j)
    fun y => hj y (nonZeroDivisors.ne_zero y.2)
  letI : Algebra F K := iF.toAlgebra
  letI : Algebra F R := jF.toAlgebra
  refine ⟨R ⊗[F] K, inferInstance, algebraMap R (R ⊗[F] K),
    (Algebra.TensorProduct.includeRight : K →ₐ[F] R ⊗[F] K).toRingHom, ?_, ?_⟩
  · rw [RingHom.faithfullyFlat_algebraMap_iff]
    infer_instance
  · ext o
    have h₁ : j o = algebraMap F R (algebraMap O F o) := (IsLocalization.lift_eq _ o).symm
    have h₂ : i o = algebraMap F K (algebraMap O F o) := (IsFractionRing.lift_algebraMap hi o).symm
    show algebraMap R (R ⊗[F] K) (j o) = (Algebra.TensorProduct.includeRight : K →ₐ[F] R ⊗[F] K) (i o)
    rw [h₁, h₂, AlgHom.commutes, ← IsScalarTower.algebraMap_apply]

/- English proof (translation)
Take `⟨R', _, a, b, ha, hab⟩` from `exists_cover _ hi _ hj`. Set `q : Over.mk (spMap a ≫ (specO O R).hom) ⟶ specO O R` to `Over.homMk (spMap a) rfl`. Establish `hs : spMap a ≫ (specO O R).hom = spMap b ≫ spMap (algebraMap O K)` using `by show spMap a ≫ spMap (algebraMap O R) = _`. Rewrite using `[← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hab]`. Establish `h₁ : q ≫ x = 1` using `eq_one_of_factor h hM P.isLB e P.ktriv (spMap b) hs _ (ArtinReduction.exists_isGen_translDiff_comp A M q x hx)`.

Take `⟨_, _⟩` from `(flat_and_surjective_SpecMap_iff (CommRingCat.ofHom a)).2 ha`. Establish `: Epi (spMap a)` using `Flat.epi_of_flat_of_surjective _`. Establish `h₂ : q ≫ x = q ≫ 1` using `by rw [h₁, MonObj.comp_one]`. Conclude with `Over.OverMorphism.ext ((cancel_epi (spMap a)).1 (congrArg (fun z => z.left) h₂))`.
-/
theorem eq_one_of_generic {O K R : Type} [CommRing O] [IsDomain O] [Field K] [Algebra O K] [CommRing R]
    [Algebra O R] (hi : Function.Injective (algebraMap O K)) (hj : ∀ a : O, a ≠ 0 → IsUnit (algebraMap O R a))
    {A : Over (Sp O)} [GrpObj A] {M : LB A.left} (hM : M.IsLB) (P : Out.PolAV (Sp K)) {φ : P.A.left ⟶ A.left}
    (h : IsGrpPullback P.A A (spMap (algebraMap O K)) φ) (e : LBIso P.L (M.pull φ)) (x : specO O R ⟶ A)
    (hx : Triv (Out.translDiff A M x)) : x = 1 := by
  obtain ⟨R', _, a, b, ha, hab⟩ := exists_cover _ hi _ hj
  let q : Over.mk (spMap a ≫ (specO O R).hom) ⟶ specO O R := Over.homMk (spMap a) rfl
  have hs : spMap a ≫ (specO O R).hom = spMap b ≫ spMap (algebraMap O K) := by
    show spMap a ≫ spMap (algebraMap O R) = _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hab]
  have h₁ : q ≫ x = 1 := eq_one_of_factor h hM P.isLB e P.ktriv (spMap b) hs _
    (ArtinReduction.exists_isGen_translDiff_comp A M q x hx)
  obtain ⟨_, _⟩ := (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom a)).2 ha
  have : Epi (spMap a) := Flat.epi_of_flat_of_surjective _
  have h₂ : q ≫ x = q ≫ 1 := by rw [h₁, MonObj.comp_one]
  exact Over.OverMorphism.ext ((cancel_epi (spMap a)).1 (congrArg (fun z => z.left) h₂))

/- English proof (translation)
Take `⟨w, hw, -⟩` from `(TangentPow.pow_eq_scale_and_existsUnique_torsion O A k p x hx).2 hp`. Establish `hm : ∀ n : ℕ, mulN A n = 𝟙 A ^ n` using `fun n => by`. Proceed by induction on `n with`. Consider the case `zero => rfl`. Consider the case `succ n ih => rw [pow_succ, ← ih]`.

Both sides reduce to the same expression. Establish `hι : torsion.ι A p ≫ mulN A p = 1`. Use `pullback.condition.trans ?_` and prove the remaining obligations. Rewrite using `[toUnit_unique (pullback.snd _ _) (toUnit _)]`. Both sides reduce to the same expression.

Rewrite `hι` using `[hm, MonObj.comp_pow, Category.comp_id]`. Rewrite using `[← hw, ← MonObj.comp_pow, hι, MonObj.comp_one]`.
-/
theorem tangent_pow {O k : Type} [CommRing O] [CommRing k] [Algebra O k] (A : Over (Sp O)) [GrpObj A] {p : ℕ}
    (hp : (p : k) = 0) (x : specO O (DualNumber k) ⟶ A) (hx : ptMap (TrivSqZeroExt.fstHom O k k) ≫ x = 1) :
    x ^ p = 1 := by
  obtain ⟨w, hw, -⟩ := (TangentPow.pow_eq_scale_and_existsUnique_torsion O A k p x hx).2 hp
  have hm : ∀ n : ℕ, mulN A n = 𝟙 A ^ n := fun n => by
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ, ← ih]; rfl
  have hι : torsion.ι A p ≫ mulN A p = 1 := by
    refine pullback.condition.trans ?_
    rw [toUnit_unique (pullback.snd _ _) (toUnit _)]
    rfl
  rw [hm, MonObj.comp_pow, Category.comp_id] at hι
  rw [← hw, ← MonObj.comp_pow, hι, MonObj.comp_one]

/- English proof (translation)
Introduce `hL O K _ _ _ _ _ _ _ hi hq A _ hA g hg M hM hrig hamp P φ h e`. Use `hA.comm` as an intermediate fact. Take `⟨d, -, m, s, hs⟩` from `(Unif.relAmple_iff_veryAmpleBy O A M hM).1 hamp`. Establish `hproj : IsProjBy A.hom` using `⟨_, isLB_pw hM d, m, s, hs⟩`. Take `⟨L, rfl, ⟨c⟩⟩` from `Moduli.cubicalStr_of_triv_theta hL _ A hA M hM hrig (GlobalTheory.T.theorem_of_cube_projective_abelianScheme_affineBase hL O A hA hproj M hM)`.

Use `smoothOfRelativeDimension_isStableUnderBaseChange.{0} g` as an intermediate fact. Establish `hgP : P.g = g` using `H1.dim_unique P.A.hom P.smoothDim (MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension g) h.1 hg) ((η[P.A]).left (Nonempty.some (inferInstanceAs (Nonempty (Sp K)))))`. Establish `tors : ∀ (n : ℕ), 1 ≤ n → ∀ (T : Over (Sp O)) (x : T ⟶ A), x ^ n = 1 → Triv (Out.translDiff A L.L x) → x = 1`. Introduce `n hn T x hxn hx`. Establish `hnK : (n : K) ≠ 0` using `Nat.cast_ne_zero.2 (by omega)`.

Take `⟨f₁, f₂, f₃⟩` from `GlobalTheory.T.finite_flat_surjective_mul_by_n_abelianScheme hL O A hA L.L hM hamp n hn`. Use `GlobalTheory.T.eq_one_of_cubWeil_trivial_of_generic O K hi A g hg L c n hn f₁ f₂ ?_ ?_ T x hxn fun T' ρ y hy => ?_` and prove the remaining obligations. Rewrite using `[← hgP, ← (hL.mulN _ P n hn).2.2.2.2 K (𝟙 _) hnK]`. Conclude with `card_torsion h (𝟙 _) (Category.id_comp _).symm n`. Introduce `y hy hp`.

Conclude with `eq_one_of_factor h hM P.isLB e P.ktriv (𝟙 _) (Category.id_comp _).symm y (CubNondeg.main hL _ A hA L c K _ n hnK f₁ f₂ f₃ y hy hp)`. Use `UU.KerPair.cubWeil_of_gen hL.globalFns _ A hA L c n T' _ y ?_ hy (ArtinReduction.exists_isGen_translDiff_comp A L.L ρ x hx)` and prove the remaining obligations. Rewrite using `[← MonObj.comp_pow, hxn, MonObj.comp_one]`. Use `GlobalTheory.T.kTriv_of_geometric_points_and_tangents hL O A hA hproj L.L hM fun k _ _ _ => ⟨fun x hx => ?_, fun x hx₀ hx => ?_⟩` and prove the remaining obligations. Take `⟨n, hn, hxn⟩` from `field_torsion hL A hA hM hamp _ (Category.id_comp _).symm x hx`.

Conclude with `tors n hn _ x hxn hx`. Distinguish the cases in `hk : RingHom.ker (algebraMap O k) = ⊥`. Use `eq_one_of_generic hi (fun a ha => ?_) hM P h e x hx` and prove the remaining obligations. Establish `ha' : algebraMap O k a ≠ 0` using `fun h0 => ha (by`. Establish `: a ∈ RingHom.ker (algebraMap O k)` using `h0`.

Rewrite using `[hk] at this)` and apply the resulting hypothesis. Rewrite using `[TrivSqZeroExt.isUnit_iff_isUnit_fst]`. Conclude with `(congrArg IsUnit ((TrivSqZeroExt.fstHom O k k).commutes a)).mpr ha'.isUnit`. Take `⟨p, hp, hpq⟩` from `hq _ (RingHom.ker_isPrime _) hk`. Establish `hp0 : (p : k) = 0` using `by rw [← map_natCast (algebraMap O k)]; exact hpq`.

Conclude with `tors p hp.one_le _ x (tangent_pow A hp0 x hx₀) hx`.
-/
theorem kTriv_of_generic : Out.Laws → ∀ (O K : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [Field K] [IsAlgClosed K] [CharZero K] [Algebra O K], Function.Injective (algebraMap O K) → (∀ q : Ideal O, q.IsPrime → q ≠ ⊥ → ∃ p : ℕ, p.Prime ∧ (p : O) ∈ q) → ∀ (A : Over (Sp O)) [GrpObj A], IsAbelianScheme A → ∀ (g : ℕ), SmoothOfRelativeDimension g A.hom → ∀ M : LB A.left, M.IsLB → Out.Rigidified A M → Out.RelAmple A M → ∀ (P : Out.PolAV (Sp K)) (φ : P.A.left ⟶ A.left), IsGrpPullback P.A A (spMap (algebraMap O K)) φ → LBIso P.L (M.pull φ) → Out.KTriv A M := by
  intro hL O K _ _ _ _ _ _ _ hi hq A _ hA g hg M hM hrig hamp P φ h e
  have := hA.comm
  obtain ⟨d, -, m, s, hs⟩ := (Unif.relAmple_iff_veryAmpleBy O A M hM).1 hamp
  have hproj : IsProjBy A.hom := ⟨_, isLB_pw hM d, m, s, hs⟩
  obtain ⟨L, rfl, ⟨c⟩⟩ := Moduli.cubicalStr_of_triv_theta hL _ A hA M hM hrig (GlobalTheory.T.theorem_of_cube_projective_abelianScheme_affineBase hL O A hA hproj M hM)
  have := smoothOfRelativeDimension_isStableUnderBaseChange.{0} g
  have hgP : P.g = g := H1.dim_unique P.A.hom P.smoothDim
    (MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension g) h.1 hg)
    ((η[P.A]).left (Nonempty.some (inferInstanceAs (Nonempty (Sp K)))))
  have tors : ∀ (n : ℕ), 1 ≤ n → ∀ (T : Over (Sp O)) (x : T ⟶ A), x ^ n = 1 → Triv (Out.translDiff A L.L x) →
      x = 1 := by
    intro n hn T x hxn hx
    have hnK : (n : K) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    obtain ⟨f₁, f₂, f₃⟩ := GlobalTheory.T.finite_flat_surjective_mul_by_n_abelianScheme hL O A hA L.L hM hamp n hn
    refine GlobalTheory.T.eq_one_of_cubWeil_trivial_of_generic O K hi A g hg L c n hn f₁ f₂ ?_ ?_ T x hxn fun T' ρ y hy => ?_
    · rw [← hgP, ← (hL.mulN _ P n hn).2.2.2.2 K (𝟙 _) hnK]
      exact card_torsion h (𝟙 _) (Category.id_comp _).symm n
    · intro y hy hp
      exact eq_one_of_factor h hM P.isLB e P.ktriv (𝟙 _) (Category.id_comp _).symm y
        (CubNondeg.main hL _ A hA L c K _ n hnK f₁ f₂ f₃ y hy hp)
    · refine UU.KerPair.cubWeil_of_gen hL.globalFns _ A hA L c n T' _ y ?_ hy
        (ArtinReduction.exists_isGen_translDiff_comp A L.L ρ x hx)
      rw [← MonObj.comp_pow, hxn, MonObj.comp_one]
  refine GlobalTheory.T.kTriv_of_geometric_points_and_tangents hL O A hA hproj L.L hM fun k _ _ _ => ⟨fun x hx => ?_, fun x hx₀ hx => ?_⟩
  · obtain ⟨n, hn, hxn⟩ := field_torsion hL A hA hM hamp _ (Category.id_comp _).symm x hx
    exact tors n hn _ x hxn hx
  · by_cases hk : RingHom.ker (algebraMap O k) = ⊥
    · refine eq_one_of_generic hi (fun a ha => ?_) hM P h e x hx
      have ha' : algebraMap O k a ≠ 0 := fun h0 => ha (by
        have : a ∈ RingHom.ker (algebraMap O k) := h0
        rwa [hk] at this)
      rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]
      exact (congrArg IsUnit ((TrivSqZeroExt.fstHom O k k).commutes a)).mpr ha'.isUnit
    · obtain ⟨p, hp, hpq⟩ := hq _ (RingHom.ker_isPrime _) hk
      have hp0 : (p : k) = 0 := by rw [← map_natCast (algebraMap O k)]; exact hpq
      exact tors p hp.one_le _ x (tangent_pow A hp0 x hx₀) hx

end GlobalTheory.GenericKTriv
