import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.MinSt5OfMinSt4
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCompleteDvrIntegralClosureFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticLevelRootsFiniteExtCharZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueExtendPointAbelianSchemeDVRStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingEqOfFractionFieldDomainStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelObjectOfSymplecticLevelPointsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LevelAfterExt

/- English proof (translation)
Introduce `n hn3 _ V _ _ _ hV _ b PB r c`. Establish `hn0 : n ≠ 0` using `by omega`. Use `haveI := hV.2.2.1`. Use `haveI := hV.2.2.2`. Use `haveI : CharZero (FractionRing V) := charZero_of_injective_ringHom (IsFractionRing.injective V (FractionRing V))`.

Set `ze : (cycAway n)ˣ` to `(GlobalTheory.LowChart.isUnit_zetaAway n hn3).unit`. Set `ζ : (FractionRing V)ˣ` to `Units.map ((algebraMap V (FractionRing V)).comp b).toMonoidHom ze`. Establish `hζ : IsPrimitiveRoot ζ n` using `IsPrimitiveRoot.coe_units_iff.1 (isPrimitiveRoot_map hn0 ((algebraMap V (FractionRing V)).comp b))`. Take `⟨L, _, _, _, lev, d, hadd, htor, hweil, hd⟩` from `GlobalTheory.T.exists_symplecticLevel_roots_finite_ext_charZero V PB (FractionRing V) (algebraMap V (FractionRing V)) n (by omega) ζ hζ r (fun i => c (Pi.single i 1))`. Take `⟨W, _, _, _, hcW, _, _, _, hcomp, hfin, hinj, hloc, -, -⟩` from `GlobalTheory.SS.exists_complete_dvr_finite_extension V (FractionRing V) L`.

Generalize the expression as in `hT : (algebraMap (FractionRing V) L).comp (algebraMap V (FractionRing V)) = T at lev d hadd htor hweil hd`. Establish `hT' : (algebraMap W L).comp (algebraMap V W) = T` using `hcomp.trans hT`. Substitute `hT'` using the available equality. Set `f₁ : V →+* W` to `algebraMap V W`. Set `e : Over.mk (spMap ((algebraMap W L).comp f₁)) ⟶ Over.mk (spMap f₁)` to `Over.homMk (spMap (algebraMap W L)) (by show Spec.map _ ≫ Spec.map _ = Spec.map _; rw [← Spec.map_comp]; rfl)`.

Establish `hel : e.left = spMap (algebraMap W L)` using `rfl`. Establish `uniq : ∀ y y' : Over.mk (spMap f₁) ⟶ PB.A, e ≫ y = e ≫ y' → y = y'` using `fun y y' h => (GlobalTheory.T.exists_unique_extend_point_abelianScheme_DVR V PB W L f₁ (e ≫ y)).unique (rfl : spMap (algebraMap W L) ≫ y.left = (e ≫ y).left) (show spMap (algebraMap W L) ≫ y'.left = (e ≫ y).left by rw [h]; rfl)`. Establish `lift : ∀ x : Over.mk (spMap ((algebraMap W L).comp f₁)) ⟶ PB.A, ∃ y, e ≫ y = x` using `fun x => by`. Take `⟨y, hy, -⟩` from `GlobalTheory.T.exists_unique_extend_point_abelianScheme_DVR V PB W L f₁ x`. Conclude with `⟨y, Over.OverMorphism.ext hy⟩`.

Use `choose lev₁ hlev₁ using fun a => lift (lev a)`. Use `choose d₁ hd₁ using fun i => lift (d i)`. Establish `add₁ : ∀ x y, lev₁ (x + y) = lev₁ x * lev₁ y` using `fun x y => uniq _ _ (by rw [MonObj.comp_mul, hlev₁, hlev₁, hlev₁, hadd])`. Establish `tor₁ : ∀ x, lev₁ x ^ n = 1` using `fun x => uniq _ _ (by rw [MonObj.comp_pow, hlev₁, htor, MonObj.comp_one])`. Establish `div₁ : ∀ i, d₁ i ^ n = toUnit _ ≫ c (Pi.single i 1)` using `fun i => uniq _ _ (by rw [MonObj.comp_pow, hd₁, hd, ← Category.assoc, toUnit_unique (e ≫ toUnit _) (toUnit _)])`.

Establish `weil₁ : ∀ x y, Out.WeilIs PB.A PB.L n (lev₁ x) (lev₁ y) (unitOn (Units.map (f₁.comp b).toMonoidHom ze ^ omegaStd x y))` using `fun x y => by`. Use `GlobalTheory.T.weilPairing_eq_of_fractionField_domain V PB W L f₁ e hel n _ _ (tor₁ x) (tor₁ y) _ ?_` and prove the remaining obligations. Rewrite using `[hlev₁, hlev₁, map_zpow]`. Establish `hz : Units.map (algebraMap W L).toMonoidHom (Units.map (f₁.comp b).toMonoidHom ze) = Units.map (algebraMap (FractionRing V) L).toMonoidHom ζ` using `Units.ext (by show (algebraMap W L) (f₁ (b (zetaAway n))) = (algebraMap (FractionRing V) L) ((algebraMap V (FractionRing V)) (b (zetaAway n)))`. Conclude with `congrArg (fun q : V →+* L => q (b (zetaAway n))) hcomp)`.

Rewrite using `[hz]`. Conclude with `hweil x y`. Take `⟨s, β₁, β₁₂, d', hP, hpb, hsq, hlb, hdd⟩` from `GlobalTheory.T.exists_siegelObject_of_symplecticLevel_points n hn3 V W f₁ b PB lev₁ r d₁ (fun i => c (Pi.single i 1)) add₁ tor₁ weil₁ div₁`. Use `⟨W, inferInstance, inferInstance, inferInstance, f₁, s, β₁, β₁₂, d', ⟨inferInstance, inferInstance, hcW, charZero_of_injective_ringHom hinj⟩, inferInstance, hinj, RingHom.finite_algebraMap.2 hfin, hloc, hP, hpb, hsq, hlb, hdd⟩` and prove the remaining obligations.
-/
theorem exists_siegPre_divPoints : ∀ (n : ℕ), 3 ≤ n → Odd n → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → IsDiscreteValuationRing V → ∀ (b : cycAway n →+* V) (PB : PolAV (Sp V)) (r : ℕ) (c : (Fin r → ℤ) → (𝟙_ (Over (Sp V)) ⟶ PB.A)), ∃ (V₁ : Type) (_ : CommRing V₁) (_ : IsDomain V₁) (_ : IsLocalRing V₁) (f₁ : V →+* V₁) (s : SiegPre PB.g n (zetaAway n) (spMap (f₁.comp b))) (β₁ : s.A.left ⟶ PB.A.left) (β₁₂ : (G2 s.A).left ⟶ (G2 PB.A).left) (d : Fin r → (𝟙_ (Over (Sp V₁)) ⟶ s.A)), IsCN V₁ ∧ IsDiscreteValuationRing V₁ ∧ Function.Injective f₁ ∧ f₁.Finite ∧ IsLocalHom f₁ ∧ s.Principal ∧ IsGrpPullback s.A PB.A (spMap f₁) β₁ ∧ IsSquare β₁ β₁₂ ∧ LBIso s.P ((abelian₂ PB.A PB.L).pull β₁₂) ∧ ∀ i, (d i ^ n).left ≫ β₁ = spMap f₁ ≫ (c (Pi.single i 1)).left := by
  intro n hn3 _ V _ _ _ hV _ b PB r c
  have hn0 : n ≠ 0 := by omega
  haveI := hV.2.2.1
  haveI := hV.2.2.2
  haveI : CharZero (FractionRing V) := charZero_of_injective_ringHom (IsFractionRing.injective V (FractionRing V))
  let ze : (cycAway n)ˣ := (GlobalTheory.LowChart.isUnit_zetaAway n hn3).unit
  let ζ : (FractionRing V)ˣ := Units.map ((algebraMap V (FractionRing V)).comp b).toMonoidHom ze
  have hζ : IsPrimitiveRoot ζ n :=
    IsPrimitiveRoot.coe_units_iff.1 (isPrimitiveRoot_map hn0 ((algebraMap V (FractionRing V)).comp b))
  obtain ⟨L, _, _, _, lev, d, hadd, htor, hweil, hd⟩ :=
    GlobalTheory.T.exists_symplecticLevel_roots_finite_ext_charZero V PB (FractionRing V) (algebraMap V (FractionRing V)) n (by omega) ζ hζ r (fun i => c (Pi.single i 1))
  obtain ⟨W, _, _, _, hcW, _, _, _, hcomp, hfin, hinj, hloc, -, -⟩ :=
    GlobalTheory.SS.exists_complete_dvr_finite_extension V (FractionRing V) L
  generalize hT : (algebraMap (FractionRing V) L).comp (algebraMap V (FractionRing V)) = T at lev d hadd htor hweil hd
  have hT' : (algebraMap W L).comp (algebraMap V W) = T := hcomp.trans hT
  subst hT'
  let f₁ : V →+* W := algebraMap V W
  let e : Over.mk (spMap ((algebraMap W L).comp f₁)) ⟶ Over.mk (spMap f₁) :=
    Over.homMk (spMap (algebraMap W L)) (by show Spec.map _ ≫ Spec.map _ = Spec.map _; rw [← Spec.map_comp]; rfl)
  have hel : e.left = spMap (algebraMap W L) := rfl
  have uniq : ∀ y y' : Over.mk (spMap f₁) ⟶ PB.A, e ≫ y = e ≫ y' → y = y' := fun y y' h =>
    (GlobalTheory.T.exists_unique_extend_point_abelianScheme_DVR V PB W L f₁ (e ≫ y)).unique (rfl : spMap (algebraMap W L) ≫ y.left = (e ≫ y).left)
      (show spMap (algebraMap W L) ≫ y'.left = (e ≫ y).left by rw [h]; rfl)
  have lift : ∀ x : Over.mk (spMap ((algebraMap W L).comp f₁)) ⟶ PB.A, ∃ y, e ≫ y = x := fun x => by
    obtain ⟨y, hy, -⟩ := GlobalTheory.T.exists_unique_extend_point_abelianScheme_DVR V PB W L f₁ x
    exact ⟨y, Over.OverMorphism.ext hy⟩
  choose lev₁ hlev₁ using fun a => lift (lev a)
  choose d₁ hd₁ using fun i => lift (d i)
  have add₁ : ∀ x y, lev₁ (x + y) = lev₁ x * lev₁ y := fun x y =>
    uniq _ _ (by rw [MonObj.comp_mul, hlev₁, hlev₁, hlev₁, hadd])
  have tor₁ : ∀ x, lev₁ x ^ n = 1 := fun x =>
    uniq _ _ (by rw [MonObj.comp_pow, hlev₁, htor, MonObj.comp_one])
  have div₁ : ∀ i, d₁ i ^ n = toUnit _ ≫ c (Pi.single i 1) := fun i =>
    uniq _ _ (by rw [MonObj.comp_pow, hd₁, hd, ← Category.assoc, toUnit_unique (e ≫ toUnit _) (toUnit _)])
  have weil₁ : ∀ x y, Out.WeilIs PB.A PB.L n (lev₁ x) (lev₁ y)
      (unitOn (Units.map (f₁.comp b).toMonoidHom ze ^ omegaStd x y)) := fun x y => by
    refine GlobalTheory.T.weilPairing_eq_of_fractionField_domain V PB W L f₁ e hel n _ _ (tor₁ x) (tor₁ y) _ ?_
    rw [hlev₁, hlev₁, map_zpow]
    have hz : Units.map (algebraMap W L).toMonoidHom (Units.map (f₁.comp b).toMonoidHom ze) =
        Units.map (algebraMap (FractionRing V) L).toMonoidHom ζ := Units.ext (by
      show (algebraMap W L) (f₁ (b (zetaAway n))) = (algebraMap (FractionRing V) L) ((algebraMap V (FractionRing V)) (b (zetaAway n)))
      exact congrArg (fun q : V →+* L => q (b (zetaAway n))) hcomp)
    rw [hz]
    exact hweil x y
  obtain ⟨s, β₁, β₁₂, d', hP, hpb, hsq, hlb, hdd⟩ :=
    GlobalTheory.T.exists_siegelObject_of_symplecticLevel_points n hn3 V W f₁ b PB lev₁ r d₁ (fun i => c (Pi.single i 1)) add₁ tor₁ weil₁ div₁
  refine ⟨W, inferInstance, inferInstance, inferInstance, f₁, s, β₁, β₁₂, d',
    ⟨inferInstance, inferInstance, hcW, charZero_of_injective_ringHom hinj⟩, inferInstance, hinj,
    RingHom.finite_algebraMap.2 hfin, hloc, hP, hpb, hsq, hlb, hdd⟩

end GlobalTheory.LevelAfterExt
