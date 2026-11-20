import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotSymEOfNe
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelCoverMatrices
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSharpGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePointsCycAway
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SharpPolarizationPullbackStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalModelNormalisationDedekind
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChartFiniteEtaleCoverGenericPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelModuliIntegralNormalLocallyNoetherianStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsBigThetaSysWithAction
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsThetaSystemOfPolarisedLevel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsSharpAndPrim
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelShapePrimitivityPullbackDescent
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemePullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsE8IsSharpBasis
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPolAVHypSRetract
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelObjectLoweredLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothProjectiveStalkFactorial
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaFamilyOverThetaPointScheme
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFractionFieldOfFinitelyManyProportionalImaStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.SiegLevSys
open GlobalTheory.ThetaSysOfObj ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH

/- English proof (translation)
Introduce `n g hn ho`. Take `⟨hL, hL₂⟩` from `GlobalTheory.abelianSchemeLaws_all`. Take `⟨k, j₁, hk, hj₁, big⟩` from `exists_big g n hn.two_le`. Use `⟨k, j₁ + 2 * k, fun j hj => ?_⟩` and prove the remaining obligations. Take `⟨j, rfl⟩ : ∃ j', j = j' + k * 2` from `⟨j - k * 2, by omega⟩`.

Rewrite using `[pow_add, pow_mul]`. Introduce `o Ω _ _ _ hb R J b u w₁ w₂ v hR hΩ hpr hth hfin`. Use `u.ab.comm` as an intermediate fact. Establish `: NeZero ((n ^ j * (n ^ k) ^ 2) ^ 2)` using `⟨by have := hn.pos; positivity⟩`. Establish `hS : ZH.HypS u.A u.L` using `⟨u.act w₁, u.act w₂, u.hom w₁, u.hom w₂, hpr.1, hpr.2.2, hpr.2.1⟩`.

Establish `hun : IsUnit (n : o)` using `isUnit_of_dvd_unit (Nat.cast_dvd_cast (((dvd_pow_self n (by omega : j ≠ 0)).trans (dvd_mul_right _ _)).trans (dvd_pow_self _ two_ne_zero))) b.unit`. Take `⟨lev, hlev⟩` from `exists_level R u`. Take `⟨S, ρ, h, φ, -, hN, hr, hg, hp, hlb, hpt⟩` from `GlobalTheory.ThetaReal.exists_thetaSys_real hL hL₂ o Ω R hR hΩ u.pol n k j b.ζ hn ho hk (by omega) hun hS lev`. Rewrite `hpt` using `[hlev]`. Use `⟨S, ρ, h, φ, big j (by omega) o Ω S hg hN hr, hg, hN, ?_, hp, hlb⟩` and prove the remaining obligations.

Take `⟨x, a, hx, hx', hk'⟩` from `exists_points u S ρ hg hp hpt`. Set `w : Over.mk (spMap S.R.val.toRingHom) ⟶ Out.baseOver (Sp S.R)` to `Over.homMk (spMap S.R.val.toRingHom) (by simp)`. Establish `ef : spMap R.val.toRingHom ≫ 𝟙 _ = spMap S.R.val.toRingHom ≫ spMap (Subalgebra.inclusion h).toRingHom` using `(Category.comp_id _).trans (Spec.map_comp (CommRingCat.ofHom (Subalgebra.inclusion h).toRingHom) (CommRingCat.ofHom S.R.val.toRingHom))`. Establish `Q` using `hasTh_baseChange hL₂ o g _ J b _ _ u R Ω R.val.toRingHom _ v hth`. Rewrite `Q` using `[ef]`.

Establish `Q'` using `(ThetaPtUp.isThetaPt_iff (P₀ := u.pol) (P := ρ.P) (T := Over.mk (spMap S.R.val.toRingHom)) hp hlb (x := fun i => w ≫ x i) (fun i => (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (hx' i).symm).trans (Category.assoc _ _ _).symm)) (fun i => by rw [← MonObj.comp_pow, hk', MonObj.co …`. Take `⟨c, hc, hv⟩` from `exists_unit_generic hL hL₂ S ρ x a hx _ (by rw [hN, hr]) w rfl Q'`. Conclude with `finite_of_ratios hc (fun i => (hv i).elim fun m hm => ⟨_, hm⟩) hfin`.
-/
theorem exists_big_thetaSys_genus : ∀ (ℓ g : ℕ), ℓ.Prime → Odd ℓ → ∃ k j₀ : ℕ, ∀ j ≥ j₀, ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [GlobalTheory.ZH.ArithBase o Ω] (R : Subalgebra o Ω) (J : Type) (b : TBase o ((ℓ ^ j) ^ 2)) (u : TObj g ((ℓ ^ j) ^ 2) J b (spMap (algebraMap o R))) (w w' : J) (v : Ix g ((ℓ ^ j) ^ 2) → R), R.FG → (∀ x : Ω, ∃ a ∈ R, ∃ c ∈ R, x = a / c) → u.Prim w w' → u.HasTh (𝟙 _) v → Module.Finite (Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i i', x = (v i : Ω) / (v i' : Ω)})) Ω → ∃ (S : GlobalTheory.ZH.ThetaSys o Ω) (ρ : S.Real) (hR : R ≤ S.R) (φ : ρ.P.A.left ⟶ u.A.left), S.Big ∧ S.g = g ∧ S.N = (ℓ ^ k) ^ 2 ∧ Module.Finite (Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i i', x = S.th i' / S.th i})) Ω ∧ IsGrpPullback ρ.P.A u.A (spMap (Subalgebra.inclusion hR).toRingHom) φ ∧ LBIso ρ.P.L (u.L.pull φ) := by
  intro n g hn ho
  obtain ⟨hL, hL₂⟩ := GlobalTheory.abelianSchemeLaws_all
  obtain ⟨k, j₁, hk, hj₁, big⟩ := exists_big g n hn.two_le
  refine ⟨k, j₁ + 2 * k, fun j hj => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j', j = j' + k * 2 := ⟨j - k * 2, by omega⟩
  rw [pow_add, pow_mul]
  intro o Ω _ _ _ hb R J b u w₁ w₂ v hR hΩ hpr hth hfin
  have := u.ab.comm
  have : NeZero ((n ^ j * (n ^ k) ^ 2) ^ 2) := ⟨by have := hn.pos; positivity⟩
  have hS : ZH.HypS u.A u.L := ⟨u.act w₁, u.act w₂, u.hom w₁, u.hom w₂, hpr.1, hpr.2.2, hpr.2.1⟩
  have hun : IsUnit (n : o) := isUnit_of_dvd_unit (Nat.cast_dvd_cast
    (((dvd_pow_self n (by omega : j ≠ 0)).trans (dvd_mul_right _ _)).trans (dvd_pow_self _ two_ne_zero))) b.unit
  obtain ⟨lev, hlev⟩ := exists_level R u
  obtain ⟨S, ρ, h, φ, -, hN, hr, hg, hp, hlb, hpt⟩ :=
    GlobalTheory.ThetaReal.exists_thetaSys_real hL hL₂ o Ω R hR hΩ u.pol n k j b.ζ hn ho hk (by omega) hun hS lev
  rw [hlev] at hpt
  refine ⟨S, ρ, h, φ, big j (by omega) o Ω S hg hN hr, hg, hN, ?_, hp, hlb⟩
  obtain ⟨x, a, hx, hx', hk'⟩ := exists_points u S ρ hg hp hpt
  let w : Over.mk (spMap S.R.val.toRingHom) ⟶ Out.baseOver (Sp S.R) := Over.homMk (spMap S.R.val.toRingHom) (by simp)
  have ef : spMap R.val.toRingHom ≫ 𝟙 _ =
      spMap S.R.val.toRingHom ≫ spMap (Subalgebra.inclusion h).toRingHom :=
    (Category.comp_id _).trans (Spec.map_comp (CommRingCat.ofHom (Subalgebra.inclusion h).toRingHom)
      (CommRingCat.ofHom S.R.val.toRingHom))
  have Q := hasTh_baseChange hL₂ o g _ J b _ _ u R Ω R.val.toRingHom _ v hth
  rw [ef] at Q
  have Q' := (ThetaPtUp.isThetaPt_iff (P₀ := u.pol) (P := ρ.P) (T := Over.mk (spMap S.R.val.toRingHom)) hp hlb
    (x := fun i => w ≫ x i) (fun i => (Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) (hx' i).symm).trans (Category.assoc _ _ _).symm))
    (fun i => by rw [← MonObj.comp_pow, hk', MonObj.comp_one]) _).2 Q
  obtain ⟨c, hc, hv⟩ := exists_unit_generic hL hL₂ S ρ x a hx _ (by rw [hN, hr]) w rfl Q'
  exact finite_of_ratios hc (fun i => (hv i).elim fun m hm => ⟨_, hm⟩) hfin

end GlobalTheory.SiegLevSys
end

noncomputable section
namespace GlobalTheory.SiegLevSys
open GlobalTheory.SiegLev GlobalTheory.AbLaw GlobalTheory.Poinc

def rootBase {n k : ℕ} (hn : n ≠ 0) (hk : k ≠ 0) : TBase (cycAway (n * k)) k where
  ζ := (cycBase (mul_ne_zero hn hk)).ζ ^ n
  unit := (IsUnit.mul_iff.1 (by rw [← Nat.cast_mul]; exact isUnit_natCast (mul_ne_zero hn hk))).2
  prim K _ β := by
    rw [Units.val_pow_eq_pow_val, map_pow, cycBase_ζ]
    exact (isPrimitiveRoot_map (mul_ne_zero hn hk) β).pow (Nat.pos_of_ne_zero (mul_ne_zero hn hk)) rfl

/- English proof (translation)
Use `show ((cycBase (mul_ne_zero hn hk)).ζ ^ n) ^ k = 1`. Rewrite using `[← pow_mul]`. Conclude with `Units.ext ((Units.val_pow_eq_pow_val _ _).trans (Subtype.ext (Complex.isPrimitiveRoot_exp _ (mul_ne_zero hn hk)).pow_eq_one))`.
-/
theorem rootBase_pow {n k : ℕ} (hn : n ≠ 0) (hk : k ≠ 0) : (rootBase hn hk).ζ ^ k = 1 := by
  show ((cycBase (mul_ne_zero hn hk)).ζ ^ n) ^ k = 1
  rw [← pow_mul]
  exact Units.ext ((Units.val_pow_eq_pow_val _ _).trans
    (Subtype.ext (Complex.isPrimitiveRoot_exp _ (mul_ne_zero hn hk)).pow_eq_one))

def lowerLev {h M N d : ℕ} {B : Type} [CommRing B] {ζ' ζ : B} {S : Scheme.{0}} {s : S ⟶ Sp B}
    (C : SiegPre h M ζ' s) (hM : M = N * d) (h0 : M ≠ 0) (hζ : ζ = ζ' ^ d) : SiegPre h N ζ s where
  A := C.A
  ab := C.ab
  P := C.P
  isLB := C.isLB
  rig₁ := C.rig₁
  rig₂ := C.rig₂
  symm := C.symm
  lev a := C.lev a ^ d
  lev_add := (SiegLower.lower C hM h0 (RingHom.id B) hζ).lev_add
  lev_tors := (SiegLower.lower C hM h0 (RingHom.id B) hζ).lev_tors
  geom K _ _ x β z hx hz := (SiegLower.lower C hM h0 (RingHom.id B) hζ).geom K x β z
    (by rw [show spMap (RingHom.id B) = 𝟙 _ from Spec.map_id _, Category.comp_id]; exact hx) hz

/- English proof (translation)
Establish `e` using `C.lev_add 0 0`. Rewrite `e` using `[add_zero]`. Conclude with `(mul_eq_left.1 e.symm)`.
-/
theorem lev_zero {h M : ℕ} {B : Type} [CommRing B] {ζ : B} {S : Scheme.{0}} {s : S ⟶ Sp B}
    (C : SiegPre h M ζ s) : C.lev 0 = 1 := by
  have e := C.lev_add 0 0
  rw [add_zero] at e
  exact (mul_eq_left.1 e.symm)

/- English proof (translation)
Establish `hk : k ≠ 0` using `by omega`. Establish `hnk : n * k ≠ 0` using `mul_ne_zero hn.ne' hk`. Set `b` to `rootBase hn.ne' hk`. Establish `hbζ : (b.ζ : cycAway (n * k)) = zetaAway (n * k) ^ n` using `Units.val_pow_eq_pow_val _ _`. Set `c : SiegPre g k (b.ζ : cycAway (n * k)) F'.s` to `lowerLev F'.univ (mul_comm n k) hnk hbζ`.

Establish `hc : c.Principal` using `F'.princ`. Establish `hd : SmoothOfRelativeDimension g c.A.hom` using `SiegSharpCover.smoothDim c (by omega) b.ζ.isUnit b.unit`. Take `⟨L₁, L₂⟩` from `abelianSchemeLaws_all`. Use `haveI : IsDedekindDomain (cycAway (n * k)) := GlobalTheory.CycAwayReg.isDedekindDomain_cycAway _`. Use `haveI : IsLocallyNoetherian (Sp (cycAway (n * k))) := inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of _)))`.

Use `haveI := F'.smooth`. Use `haveI : Smooth F'.s := SmoothOfRelativeDimension.smooth (g * (g + 1) / 2) F'.s`. Use `haveI : IsLocallyNoetherian F'.X := LocallyOfFiniteType.isLocallyNoetherian F'.s`. Take `⟨t, ht, hp⟩` from `GlobalTheory.exists_isSharp_and_prim L₁ L₂ Moduli.cube_of_isLB g (8 * g) W J a w w' bas hW hb hw hw' hs k (cycAway (n * k)) b F'.X F'.s c (rootBase_pow hn.ne' hk) hko hc hd`. Establish `h00 : SiegLev.SRel c F.univ 0 0 q`.

Take `⟨φ, hφ, hsq, hlev⟩` from `hq`. Use `⟨φ, hφ, hsq, fun x => ?_⟩` and prove the remaining obligations. Establish `e` using `hlev 0`. Rewrite `e` using `[lev_zero, lev_zero, one_pow, pow_one]`. Rewrite using `[pow_zero, pow_zero]`.

Conclude with `e`. Use `⟨b, c, t, ht, h00, hp, ?_⟩` and prove the remaining obligations. Set `cT : SiegPre g n (zetaAway n) (F'.s ≫ spMap κ)` to `SiegLower.lower F'.univ (n := n) (d := k) rfl hnk κ hζ`. Establish `hPB : SiegPB cT F.univ q`. Take `⟨φ, hφ, ⟨φ₂, hsq, hP⟩, hlev⟩` from `hq`.

Conclude with `⟨φ, φ₂, hφ, hsq, hP, fun a => by have e := hlev a; rw [pow_one] at e; exact e⟩`. Take `⟨pr, h1, h2, h3, -, -⟩` from `ht`. Unfold `SharpOver`. Rewrite using `[hqs]`. Conclude with `⟨cT, hPB, pr, h1, h2, h3⟩`.
-/
theorem exists_sharp_cover (g n k : ℕ) (F : SFam g n (zetaAway n)) (F' : SFam g (n * k) (zetaAway (n * k)))
    (κ : cycAway n →+* cycAway (n * k)) (q : F'.X ⟶ F.X) (hn : 0 < n) (hk3 : 3 ≤ k) (hko : Odd k)
    (hζ : κ (zetaAway n) = zetaAway (n * k) ^ k) (hqs : q ≫ F.s = F'.s ≫ spMap κ)
    (hq : SiegLev.SRel F'.univ F.univ k 1 q) (W : Matrix (Fin 8) (Fin 8) ℤ) (J : Type) [Finite J]
    (a : J → Matrix (Fin 8) (Fin 8) ℤ) (w w' : J)
    (bas : (Fin (2 * (8 * g)) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin g ⊕ Fin g → ℤ))) (hW : IsE8 W) (hb : IsSharpBasis W bas)
    (hw : (W + W.transpose) * a w = W) (hw' : (W + W.transpose) * a w' = W.transpose)
    (hs : ∀ u v, ∃ j, a j = Matrix.single u v 1) :
    ∃ (b : TBase (cycAway (n * k)) k) (c : SiegPre g k (b.ζ : cycAway (n * k)) F'.s) (t : TObj (8 * g) k J b F'.s),
      IsSharp W a bas t c ∧ SiegLev.SRel c F.univ 0 0 q ∧ t.Prim w w' ∧ SharpOver F W t.pol q := by
  have hk : k ≠ 0 := by omega
  have hnk : n * k ≠ 0 := mul_ne_zero hn.ne' hk
  let b := rootBase hn.ne' hk
  have hbζ : (b.ζ : cycAway (n * k)) = zetaAway (n * k) ^ n := Units.val_pow_eq_pow_val _ _
  let c : SiegPre g k (b.ζ : cycAway (n * k)) F'.s := lowerLev F'.univ (mul_comm n k) hnk hbζ
  have hc : c.Principal := F'.princ
  have hd : SmoothOfRelativeDimension g c.A.hom :=
    SiegSharpCover.smoothDim c (by omega) b.ζ.isUnit b.unit
  obtain ⟨L₁, L₂⟩ := abelianSchemeLaws_all
  haveI : IsDedekindDomain (cycAway (n * k)) := GlobalTheory.CycAwayReg.isDedekindDomain_cycAway _
  haveI : IsLocallyNoetherian (Sp (cycAway (n * k))) :=
    inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of _)))
  haveI := F'.smooth
  haveI : Smooth F'.s := SmoothOfRelativeDimension.smooth (g * (g + 1) / 2) F'.s
  haveI : IsLocallyNoetherian F'.X := LocallyOfFiniteType.isLocallyNoetherian F'.s
  obtain ⟨t, ht, hp⟩ := GlobalTheory.exists_isSharp_and_prim L₁ L₂ Moduli.cube_of_isLB g (8 * g) W J a w w' bas hW hb hw hw'
    hs k (cycAway (n * k)) b F'.X F'.s c (rootBase_pow hn.ne' hk) hko hc hd
  have h00 : SiegLev.SRel c F.univ 0 0 q := by
    obtain ⟨φ, hφ, hsq, hlev⟩ := hq
    refine ⟨φ, hφ, hsq, fun x => ?_⟩
    have e := hlev 0
    rw [lev_zero, lev_zero, one_pow, pow_one] at e
    rw [pow_zero, pow_zero]
    exact e
  refine ⟨b, c, t, ht, h00, hp, ?_⟩
  let cT : SiegPre g n (zetaAway n) (F'.s ≫ spMap κ) := SiegLower.lower F'.univ (n := n) (d := k) rfl hnk κ hζ
  have hPB : SiegPB cT F.univ q := by
    obtain ⟨φ, hφ, ⟨φ₂, hsq, hP⟩, hlev⟩ := hq
    exact ⟨φ, φ₂, hφ, hsq, hP, fun a => by have e := hlev a; rw [pow_one] at e; exact e⟩
  obtain ⟨pr, h1, h2, h3, -, -⟩ := ht
  unfold SharpOver
  rw [hqs]
  exact ⟨cT, hPB, pr, h1, h2, h3⟩

end GlobalTheory.SiegLevSys
end

noncomputable section
namespace GlobalTheory.SiegLevSys
open GlobalTheory.SiegLev GlobalTheory.AbLaw GlobalTheory.Poinc

/- English proof (translation)
The claim follows from `GlobalTheory.T.finite_fractionField_of_finitely_many_proportional_images`.
-/
theorem finite_ratios_of_finite_fibres : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) (X : Scheme.{0}) (x : Sp R ⟶ X) (I : Type) [Finite I] (v : I → R), R.FG → (∀ z : Ω, ∃ a ∈ R, ∃ c ∈ R, z = a / c) → ((spMap R.val.toRingHom ≫ x).stalkMap (genericPoint (Sp Ω))).hom.Finite → (∀ (K : Type) [Field K] [IsAlgClosed K] (c : I → K), Set.Finite {y : Sp K ⟶ X | ∃ σ : R →+* K, spMap σ ≫ x = y ∧ ∃ u : K, u ≠ 0 ∧ ∀ i, σ (v i) = u * c i}) → Module.Finite (Subfield.closure (Set.range (algebraMap o Ω) ∪ {z | ∃ i i', z = (v i : Ω) / (v i' : Ω)})) Ω :=
  GlobalTheory.T.finite_fractionField_of_finitely_many_proportional_images

/- English proof (translation)
Introduce `o Ω _ _ _ R g N' J b t hN hfg hfr`. Take `⟨hL, hL₂⟩` from `abelianSchemeLaws_all`. Take `⟨f, hf0, w, hw⟩` from `GenericSpread.exists_hasTh_away hL hL₂ t hN`. Establish `hf0' : (f : Ω) ≠ 0` using `fun h => hf0 (Subtype.ext h)`. Set `R' : Subalgebra o Ω` to `R ⊔ Algebra.adjoin o (({(f : Ω)⁻¹} : Finset Ω) : Set Ω)`.

Establish `hR : R ≤ R'` using `le_sup_left`. Establish `hinv : (f : Ω)⁻¹ ∈ R'` using `(le_sup_right : _ ≤ R') (Algebra.subset_adjoin (by simp))`. Set `i : R →+* R'` to `(Subalgebra.inclusion hR).toRingHom`. Establish `hu : IsUnit (i f)` using `IsUnit.of_mul_eq_one (⟨(f : Ω)⁻¹, hinv⟩ : R') (Subtype.ext (mul_inv_cancel₀ hf0'))`. Set `e : Localization.Away f →+* R'` to `IsLocalization.Away.lift f hu`.

Establish `he : e.comp (algebraMap R (Localization.Away f)) = i` using `IsLocalization.Away.lift_comp f hu`. Establish `hs : spMap i ≫ spMap (algebraMap o R) = spMap (algebraMap o R')`. Simplify using `only [spMap, ← Spec.map_comp]`. Both sides reduce to the same expression. Take `⟨t', ht'⟩` from `GlobalTheory.tObj_pull o g _ J b _ _ _ _ (spMap i) t hs`.

Establish `H` using `GlobalTheory.hasTh_baseChange hL₂ o g N' J b _ _ t _ R' e _ w hw`. Establish `hsp : spMap e ≫ spMap (algebraMap R (Localization.Away f)) = spMap i`. Rewrite using `[← he]`. Simplify using `only [spMap, ← Spec.map_comp]`. Both sides reduce to the same expression.

Rewrite `H` using `[hsp]`. Use `⟨R', hR, t', fun a => e (w a), hfg.sup (Subalgebra.fg_adjoin_finset _), fun z => ?_, ht', ?_⟩` and prove the remaining obligations. Take `⟨a, ha, c, hc, rfl⟩` from `hfr z`. Conclude with `⟨a, hR ha, c, hR hc, rfl⟩`. Use `(GlobalTheory.hasTh_iff_of_tmap o g N' J b _ _ t _ _ t' (spMap i) R' (𝟙 _) _ ht').2 ?_` and prove the remaining obligations.

Rewrite using `[Category.id_comp]`. Conclude with `H`.
-/
theorem exists_hasTh_shrink : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (t : TObj g (N' ^ 2) J b (spMap (algebraMap o R))), Odd N' → R.FG → (∀ z : Ω, ∃ a ∈ R, ∃ c ∈ R, z = a / c) → ∃ (R' : Subalgebra o Ω) (hR : R ≤ R') (t' : TObj g (N' ^ 2) J b (spMap (algebraMap o R'))) (v : Ix g (N' ^ 2) → R'), R'.FG ∧ (∀ z : Ω, ∃ a ∈ R', ∃ c ∈ R', z = a / c) ∧ TMap t' t (spMap (Subalgebra.inclusion hR).toRingHom) ∧ t'.HasTh (𝟙 _) v := by
  intro o Ω _ _ _ R g N' J b t hN hfg hfr
  obtain ⟨hL, hL₂⟩ := abelianSchemeLaws_all
  obtain ⟨f, hf0, w, hw⟩ := GenericSpread.exists_hasTh_away hL hL₂ t hN
  have hf0' : (f : Ω) ≠ 0 := fun h => hf0 (Subtype.ext h)
  let R' : Subalgebra o Ω := R ⊔ Algebra.adjoin o (({(f : Ω)⁻¹} : Finset Ω) : Set Ω)
  have hR : R ≤ R' := le_sup_left
  have hinv : (f : Ω)⁻¹ ∈ R' := (le_sup_right : _ ≤ R') (Algebra.subset_adjoin (by simp))
  let i : R →+* R' := (Subalgebra.inclusion hR).toRingHom
  have hu : IsUnit (i f) :=
    IsUnit.of_mul_eq_one (⟨(f : Ω)⁻¹, hinv⟩ : R') (Subtype.ext (mul_inv_cancel₀ hf0'))
  let e : Localization.Away f →+* R' := IsLocalization.Away.lift f hu
  have he : e.comp (algebraMap R (Localization.Away f)) = i := IsLocalization.Away.lift_comp f hu
  have hs : spMap i ≫ spMap (algebraMap o R) = spMap (algebraMap o R') := by
    simp only [spMap, ← Spec.map_comp]
    rfl
  obtain ⟨t', ht'⟩ := GlobalTheory.tObj_pull o g _ J b _ _ _ _ (spMap i) t hs
  have H := GlobalTheory.hasTh_baseChange hL₂ o g N' J b _ _ t _ R' e _ w hw
  have hsp : spMap e ≫ spMap (algebraMap R (Localization.Away f)) = spMap i := by
    rw [← he]
    simp only [spMap, ← Spec.map_comp]
    rfl
  rw [hsp] at H
  refine ⟨R', hR, t', fun a => e (w a), hfg.sup (Subalgebra.fg_adjoin_finset _), fun z => ?_, ht', ?_⟩
  · obtain ⟨a, ha, c, hc, rfl⟩ := hfr z
    exact ⟨a, hR ha, c, hR hc, rfl⟩
  · refine (GlobalTheory.hasTh_iff_of_tmap o g N' J b _ _ t _ _ t' (spMap i) R' (𝟙 _) _ ht').2 ?_
    rw [Category.id_comp]
    exact H

/- English proof (translation)
Introduce `g n F _ o Ω _ _ _ _ κ hκ p hp hst hgen`. Use `haveI : IsDedekindDomain (cycAway n) := GlobalTheory.CycAwayReg.isDedekindDomain_cycAway _`. Use `haveI : IsSeparated F.s := F.isSeparated`. Take `⟨N, j, -, hjq, hjs⟩` from `F.qproj`. Use `haveI := isProper_str (cycAway n) N`.

Use `haveI : QuasiCompact F.s := by rw [← hjs]; infer_instance`. Use `haveI := F.smooth`. Use `haveI : Smooth F.s := SmoothOfRelativeDimension.smooth (g * (g + 1) / 2) F.s`. Take `⟨M, π, hMn, hπ, hcomp⟩` from `GlobalTheory.Poinc.exists_ratModel_normalization (cycAway n) o Ω κ hκ F.X F.s inferInstance inferInstance inferInstance p hp hst`. Use `⟨M, π, hMn, hπ, ⟨fun x => ?_⟩, ?_, hcomp⟩` and prove the remaining obligations.

Establish `hcl : IsClosed (Set.range π)` using `π.isClosedMap.isClosed_range`. Establish `hmem : genericPoint F.X ∈ Set.range π` using `⟨M.pt (IsLocalRing.closedPoint Ω), by rw [← hgen (IsLocalRing.closedPoint Ω), ← hcomp]; rfl⟩`. Conclude with `(genericPoint_specializes x).mem_closed hcl hmem`. Use `ext_of_isDominant_of_isSeparated (spMap (algebraMap ℤ (cycAway n))) (specZIsTerminal.hom_ext _ _) M.pt ?_` and prove the remaining obligations. Rewrite using `[← Category.assoc, hcomp, hp, ← Category.assoc, M.pt_s]`.

Simplify using `only [spMap, ← Spec.map_comp]`. Both sides reduce to the same expression.
-/
theorem exists_levModel : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) [IsIntegral F.X] (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (κ : cycAway n →+* o), κ.Finite → ∀ p : Sp Ω ⟶ F.X, p ≫ F.s = spMap ((algebraMap o Ω).comp κ) → (p.stalkMap (genericPoint (Sp Ω))).hom.Finite → (∀ w, p w = genericPoint F.X) → ∃ (Y : RatModel o Ω) (q : Y.Z ⟶ F.X), Geo.Tor.IsNormalScheme Y.Z ∧ IsFinite q ∧ Surjective q ∧ q ≫ F.s = Y.s ≫ spMap κ ∧ Y.pt ≫ q = p := by
  intro g n F _ o Ω _ _ _ _ κ hκ p hp hst hgen
  haveI : IsDedekindDomain (cycAway n) := GlobalTheory.CycAwayReg.isDedekindDomain_cycAway _
  haveI : IsSeparated F.s := F.isSeparated
  obtain ⟨N, j, -, hjq, hjs⟩ := F.qproj
  haveI := isProper_str (cycAway n) N
  haveI : QuasiCompact F.s := by rw [← hjs]; infer_instance
  haveI := F.smooth
  haveI : Smooth F.s := SmoothOfRelativeDimension.smooth (g * (g + 1) / 2) F.s
  obtain ⟨M, π, hMn, hπ, hcomp⟩ := GlobalTheory.Poinc.exists_ratModel_normalization (cycAway n) o Ω κ hκ F.X F.s
    inferInstance inferInstance inferInstance p hp hst
  refine ⟨M, π, hMn, hπ, ⟨fun x => ?_⟩, ?_, hcomp⟩
  · have hcl : IsClosed (Set.range π) := π.isClosedMap.isClosed_range
    have hmem : genericPoint F.X ∈ Set.range π :=
      ⟨M.pt (IsLocalRing.closedPoint Ω), by rw [← hgen (IsLocalRing.closedPoint Ω), ← hcomp]; rfl⟩
    exact (genericPoint_specializes x).mem_closed hcl hmem
  · refine ext_of_isDominant_of_isSeparated (spMap (algebraMap ℤ (cycAway n))) (specZIsTerminal.hom_ext _ _) M.pt ?_
    rw [← Category.assoc, hcomp, hp, ← Category.assoc, M.pt_s]
    simp only [spMap, ← Spec.map_comp]
    rfl

/- English proof (translation)
Use `show closure {genericPoint X} ∈ irreducibleComponents X`. Rewrite using `[(genericPoint_spec X).def]`. Simplify using `[irreducibleComponents_eq_singleton]`.
-/
theorem genericPoint_mem (X : Scheme.{0}) [IsIntegral X] : genericPoint X ∈ genericPoints X := by
  show closure {genericPoint X} ∈ irreducibleComponents X
  rw [(genericPoint_spec X).def]
  simp [irreducibleComponents_eq_singleton]

end GlobalTheory.SiegLevSys
end

noncomputable section
namespace GlobalTheory.SiegLevSys
open GlobalTheory.SiegLev GlobalTheory.AbLaw GlobalTheory.Poinc

/- English proof (translation)
Introduce `ℓ hℓ hℓo j₀ g n hg hn hodd F W hW hℓn ⟨bas, hbas⟩`. Take `⟨hint, -, -⟩` from `GlobalTheory.T.siegelModuli_integral_normal_locallyNoetherian g n hg hn hodd F`. Take `⟨j₁, hj₁⟩` from `ThetaQuasiFinite.finite_theta_fibres g ℓ hℓ hℓo W bas hW`. Take `⟨k, j₂, hsys⟩` from `exists_big_thetaSys_genus ℓ (8 * g) hℓ hℓo`. Use `set j := max (max j₁ j₂) 1 with hjdef`.

Establish `hj1 : 1 ≤ j` using `le_max_right _ _`. Establish `hjj₁ : j₁ ≤ j` using `le_trans (le_max_left _ _) (le_max_left _ _)`. Establish `hjj₂ : j₂ ≤ j` using `le_trans (le_max_right _ _) (le_max_left _ _)`. Establish `h3 : 3 ≤ ℓ`. Establish `h2` using `hℓ.two_le`.

Establish `: ℓ ≠ 2` using `fun e => by rw [e] at hℓo; exact absurd hℓo (by decide)`. Use linear arithmetic over natural numbers and integers. Establish `hk3 : 3 ≤ (ℓ ^ j) ^ 2` using `le_trans (le_trans h3 (Nat.le_self_pow (by omega) _)) (Nat.le_self_pow (by omega) _)`. Establish `hko : Odd ((ℓ ^ j) ^ 2)` using `hℓo.pow.pow`. Take `⟨κ, F', q, ⟨hinj, hζ, hfin, -, -⟩, ⟨hqs, hqfin, hqet, hqsurj, hq⟩, -⟩` from `GlobalTheory.SiegLevCover.exists_levelCover g n ℓ j F hg hn hodd hℓ hℓn hj1`.

Take `⟨a, w, w', hw, hw', hs⟩` from `EighthPowerFactor.exists_matrices hW.2`. Take `⟨b, c, t', hsh, h00, hp', hsh'⟩` from `exists_sharp_cover g n _ F F' κ q (by omega) hk3 hko hζ hqs hq W _ a w w' bas hW hbas hw hw' hs`. Use `haveI := F.smooth`. Use `haveI : Smooth F.s := SmoothOfRelativeDimension.smooth (g * (g + 1) / 2) F.s`. Use `haveI := F'.smooth`.

Use `haveI : Smooth F'.s := SmoothOfRelativeDimension.smooth (g * (g + 1) / 2) F'.s`. Take `⟨Ω, _, _, _, R, y, hRfg, hfrac, hys, hpt, hstalk⟩` from `GlobalTheory.T.exists_chart_finite_etale_cover_generic_point n (n * (ℓ ^ j) ^ 2) F.X F'.X F.s F'.s q (by omega) (by positivity) inferInstance inferInstance hqfin hqet hqsurj (genericPoint F.X) (genericPoint_mem F.X)`. Take `⟨t, ht⟩` from `GlobalTheory.tObj_pull _ (8 * g) _ _ b F'.X (Sp R) F'.s (spMap (algebraMap _ R)) y t' hys`. Establish `hp : t.Prim w w'` using `(GlobalTheory.shape_prim_pull_and_descend _ _ _ _ b (fun _ => 0) 0 w w' _ _ _ _ y t' t ht).2.1 hp'`. Take `⟨R', hRR', t'', v, hR'fg, hfrac', ht'', hth⟩` from `exists_hasTh_shrink _ Ω R (8 * g) (ℓ ^ j) _ b t hℓo.pow hRfg hfrac`.

Establish `hp'' : t''.Prim w w'` using `(GlobalTheory.shape_prim_pull_and_descend _ _ _ _ b (fun _ => 0) 0 w w' _ _ _ _ _ t t'' ht'').2.1 hp`. Take `⟨hL₁, hL₂⟩` from `abelianSchemeLaws_all`. Set `i₁ : R →+* R'` to `(Subalgebra.inclusion hRR').toRingHom`. Set `x' : Sp R' ⟶ F.X` to `spMap i₁ ≫ y ≫ q`. Establish `ef1 : spMap R'.val.toRingHom ≫ spMap i₁ = spMap R.val.toRingHom` using `(Spec.map_comp (CommRingCat.ofHom i₁) (CommRingCat.ofHom R'.val.toRingHom)).symm`.

Establish `hstalk' : ((spMap R'.val.toRingHom ≫ x').stalkMap (genericPoint (Sp Ω))).hom.Finite`. Simplify using `only [x']`. Rewrite using `[← Category.assoc, ef1]`. Conclude with `hstalk`. Use `haveI : NeZero ((ℓ ^ j) ^ 2) := ⟨by positivity⟩`.

Establish `hfinv` using `finite_ratios_of_finite_fibres _ Ω R' F.X x' _ v hR'fg hfrac' hstalk' (fun K _ _ cc => by`. Use `((hj₁ j hjj₁ n (n * (ℓ ^ j) ^ 2) (by omega) (by positivity) F b F'.X F'.s q c _ a t' h00 hsh K).1 cc).subset ?_` and prove the remaining obligations. Introduce and unpack `Y ⟨σ, hσ, u, hu, hv⟩`. Use `⟨spMap σ ≫ spMap i₁ ≫ y, by rw [← hσ]; simp only [x', Category.assoc], ?_⟩` and prove the remaining obligations. Establish `s1` using `GlobalTheory.hasTh_baseChange hL₂ _ _ _ _ b _ _ t'' R' K σ (𝟙 _) v hth`.

Rewrite `s1` using `[Category.comp_id]`. Establish `s2` using `(GlobalTheory.hasTh_iff_of_tmap _ _ _ _ b _ _ t _ _ t'' (spMap i₁) K (spMap σ) _ ht'').1 s1`. Establish `s3` using `(GlobalTheory.hasTh_iff_of_tmap _ _ _ _ b _ _ t' _ _ t y K (spMap σ ≫ spMap i₁) _ ht).1 s2`. Rewrite `s3` using `[Category.assoc]`. Conclude with `GenericSpread.hasTh_unit_mul u⁻¹ (isUnit_iff_ne_zero.2 (inv_ne_zero hu)) (fun a => by rw [hv a, ← _root_.mul_assoc, inv_mul_cancel₀ hu, _root_.one_mul]) s3)`.

Take `⟨S, ρ, hR, φ, hbig, hSg, -, hfinS, hpb, hL⟩` from `hsys j hjj₂ _ Ω R' _ b t'' w w' v hR'fg hfrac' hp'' hth hfinv`. Set `i₂ : R' →+* S.R` to `(Subalgebra.inclusion hR).toRingHom`. Set `u : Sp S.R ⟶ F.X` to `spMap i₂ ≫ x'`. Establish `ef2 : spMap S.R.val.toRingHom ≫ spMap i₂ = spMap R'.val.toRingHom` using `(Spec.map_comp (CommRingCat.ofHom i₂) (CommRingCat.ofHom S.R.val.toRingHom)).symm`. Establish `hpe : spMap S.R.val.toRingHom ≫ u = spMap R.val.toRingHom ≫ y ≫ q`.

Simplify using `only [u, x']`. Rewrite using `[← Category.assoc, ef2, ← Category.assoc, ef1]`. Take `⟨ψ, hψ, hψL, -, -⟩` from `ht`. Take `⟨ψ', hψ', hψL', -, -⟩` from `ht''`. Establish `s1 : SharpOver F W t.pol (y ≫ q)` using `sharpOver_pullback _ _ _ _ F W _ _ t'.pol t.pol q y ψ hsh' hψ hψL`.

Establish `s2 : SharpOver F W t''.pol x'` using `sharpOver_pullback _ _ _ _ F W _ _ t.pol t''.pol _ (spMap i₁) ψ' s1 hψ' hψL'`. Establish `s3 : SharpOver F W ρ.P u` using `sharpOver_pullback _ _ _ _ F W _ _ t''.pol ρ.P x' (spMap i₂) φ s2 hpb hL`. Establish `hbase : spMap R.val.toRingHom ≫ y ≫ q ≫ F.s = spMap ((algebraMap _ Ω).comp κ)`. Rewrite using `[hqs, ← Category.assoc y, hys]`. Simplify using `only [spMap, ← Spec.map_comp]`.

Both sides reduce to the same expression. Establish `hκ : κ.Finite` using `(IsFinite.SpecMap_iff _).1 hfin`. Use `haveI := hint`. Take `⟨Y, qY, hYn, hYfin, hYsurj, hYs, hYpt⟩` from `exists_levModel g n F _ Ω κ hκ (spMap S.R.val.toRingHom ≫ u) (by rw [hpe]; simpa only [Category.assoc] using hbase) (by rw [hpe]; exact hstalk) (fun w => by rw [hpe]; exact hpt w)`. Establish `hu : u ≫ F.s = spMap (algebraMap _ S.R) ≫ spMap κ`.

Simplify using `only [u, x', Category.assoc]`. Rewrite using `[hqs, ← Category.assoc y, hys]`. Simplify using `only [spMap, ← Spec.map_comp]`. Both sides reduce to the same expression. Conclude with `⟨_, Ω, inferInstance, inferInstance, inferInstance, inferInstance, κ, S, ρ, u, Y, qY, ⟨hκ, hinj, hSg, s3, hu⟩, ⟨hYn, hYfin, hYsurj, hYs, hYpt⟩, hbig, hfinS⟩`.
-/
theorem exists_sys_levModel : ∀ (ℓ : ℕ), ℓ.Prime → Odd ℓ → ∀ j₀ : ℕ, ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ℓ ∣ n → (∃ bas : (Fin (2 * (8 * g)) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin g ⊕ Fin g → ℤ)), IsSharpBasis W bas) → ∃ (o Ω : Type) (_ : CommRing o) (_ : Field Ω) (_ : Algebra o Ω) (_ : ArithBase o Ω) (β : cycAway n →+* o) (S : ThetaSys o Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X) (Y : RatModel o Ω) (q : Y.Z ⟶ F.X), SysAt F W β S ρ u ∧ LevAt F β u Y q ∧ S.Big ∧ Module.Finite (Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i j, x = S.th j / S.th i})) Ω := by
  intro ℓ hℓ hℓo j₀ g n hg hn hodd F W hW hℓn ⟨bas, hbas⟩
  obtain ⟨hint, -, -⟩ := GlobalTheory.T.siegelModuli_integral_normal_locallyNoetherian g n hg hn hodd F
  obtain ⟨j₁, hj₁⟩ := ThetaQuasiFinite.finite_theta_fibres g ℓ hℓ hℓo W bas hW
  obtain ⟨k, j₂, hsys⟩ := exists_big_thetaSys_genus ℓ (8 * g) hℓ hℓo
  set j := max (max j₁ j₂) 1 with hjdef
  have hj1 : 1 ≤ j := le_max_right _ _
  have hjj₁ : j₁ ≤ j := le_trans (le_max_left _ _) (le_max_left _ _)
  have hjj₂ : j₂ ≤ j := le_trans (le_max_right _ _) (le_max_left _ _)
  have h3 : 3 ≤ ℓ := by
    have h2 := hℓ.two_le
    have : ℓ ≠ 2 := fun e => by rw [e] at hℓo; exact absurd hℓo (by decide)
    omega
  have hk3 : 3 ≤ (ℓ ^ j) ^ 2 :=
    le_trans (le_trans h3 (Nat.le_self_pow (by omega) _)) (Nat.le_self_pow (by omega) _)
  have hko : Odd ((ℓ ^ j) ^ 2) := hℓo.pow.pow
  obtain ⟨κ, F', q, ⟨hinj, hζ, hfin, -, -⟩, ⟨hqs, hqfin, hqet, hqsurj, hq⟩, -⟩ :=
    GlobalTheory.SiegLevCover.exists_levelCover g n ℓ j F hg hn hodd hℓ hℓn hj1
  obtain ⟨a, w, w', hw, hw', hs⟩ := EighthPowerFactor.exists_matrices hW.2
  obtain ⟨b, c, t', hsh, h00, hp', hsh'⟩ := exists_sharp_cover g n _ F F' κ q (by omega) hk3 hko hζ hqs hq W _ a w w'
    bas hW hbas hw hw' hs
  haveI := F.smooth
  haveI : Smooth F.s := SmoothOfRelativeDimension.smooth (g * (g + 1) / 2) F.s
  haveI := F'.smooth
  haveI : Smooth F'.s := SmoothOfRelativeDimension.smooth (g * (g + 1) / 2) F'.s
  obtain ⟨Ω, _, _, _, R, y, hRfg, hfrac, hys, hpt, hstalk⟩ :=
    GlobalTheory.T.exists_chart_finite_etale_cover_generic_point n (n * (ℓ ^ j) ^ 2) F.X F'.X F.s F'.s q (by omega) (by positivity) inferInstance inferInstance
      hqfin hqet hqsurj (genericPoint F.X) (genericPoint_mem F.X)
  obtain ⟨t, ht⟩ := GlobalTheory.tObj_pull _ (8 * g) _ _ b F'.X (Sp R) F'.s (spMap (algebraMap _ R)) y t' hys
  have hp : t.Prim w w' :=
    (GlobalTheory.shape_prim_pull_and_descend _ _ _ _ b (fun _ => 0) 0 w w' _ _ _ _ y t' t ht).2.1 hp'
  obtain ⟨R', hRR', t'', v, hR'fg, hfrac', ht'', hth⟩ :=
    exists_hasTh_shrink _ Ω R (8 * g) (ℓ ^ j) _ b t hℓo.pow hRfg hfrac
  have hp'' : t''.Prim w w' :=
    (GlobalTheory.shape_prim_pull_and_descend _ _ _ _ b (fun _ => 0) 0 w w' _ _ _ _ _ t t'' ht'').2.1 hp
  obtain ⟨hL₁, hL₂⟩ := abelianSchemeLaws_all
  let i₁ : R →+* R' := (Subalgebra.inclusion hRR').toRingHom
  let x' : Sp R' ⟶ F.X := spMap i₁ ≫ y ≫ q
  have ef1 : spMap R'.val.toRingHom ≫ spMap i₁ = spMap R.val.toRingHom :=
    (Spec.map_comp (CommRingCat.ofHom i₁) (CommRingCat.ofHom R'.val.toRingHom)).symm
  have hstalk' : ((spMap R'.val.toRingHom ≫ x').stalkMap (genericPoint (Sp Ω))).hom.Finite := by
    simp only [x']
    rw [← Category.assoc, ef1]
    exact hstalk
  haveI : NeZero ((ℓ ^ j) ^ 2) := ⟨by positivity⟩
  have hfinv := finite_ratios_of_finite_fibres _ Ω R' F.X x' _ v hR'fg hfrac' hstalk' (fun K _ _ cc => by
    refine ((hj₁ j hjj₁ n (n * (ℓ ^ j) ^ 2) (by omega) (by positivity) F b F'.X F'.s q c _ a t' h00 hsh K).1 cc).subset ?_
    rintro Y ⟨σ, hσ, u, hu, hv⟩
    refine ⟨spMap σ ≫ spMap i₁ ≫ y, by rw [← hσ]; simp only [x', Category.assoc], ?_⟩
    have s1 := GlobalTheory.hasTh_baseChange hL₂ _ _ _ _ b _ _ t'' R' K σ (𝟙 _) v hth
    rw [Category.comp_id] at s1
    have s2 := (GlobalTheory.hasTh_iff_of_tmap _ _ _ _ b _ _ t _ _ t'' (spMap i₁) K (spMap σ) _ ht'').1 s1
    have s3 := (GlobalTheory.hasTh_iff_of_tmap _ _ _ _ b _ _ t' _ _ t y K (spMap σ ≫ spMap i₁) _ ht).1 s2
    rw [Category.assoc] at s3
    exact GenericSpread.hasTh_unit_mul u⁻¹ (isUnit_iff_ne_zero.2 (inv_ne_zero hu))
      (fun a => by rw [hv a, ← _root_.mul_assoc, inv_mul_cancel₀ hu, _root_.one_mul]) s3)
  obtain ⟨S, ρ, hR, φ, hbig, hSg, -, hfinS, hpb, hL⟩ := hsys j hjj₂ _ Ω R' _ b t'' w w' v hR'fg hfrac' hp'' hth hfinv
  let i₂ : R' →+* S.R := (Subalgebra.inclusion hR).toRingHom
  let u : Sp S.R ⟶ F.X := spMap i₂ ≫ x'
  have ef2 : spMap S.R.val.toRingHom ≫ spMap i₂ = spMap R'.val.toRingHom :=
    (Spec.map_comp (CommRingCat.ofHom i₂) (CommRingCat.ofHom S.R.val.toRingHom)).symm
  have hpe : spMap S.R.val.toRingHom ≫ u = spMap R.val.toRingHom ≫ y ≫ q := by
    simp only [u, x']
    rw [← Category.assoc, ef2, ← Category.assoc, ef1]
  obtain ⟨ψ, hψ, hψL, -, -⟩ := ht
  obtain ⟨ψ', hψ', hψL', -, -⟩ := ht''
  have s1 : SharpOver F W t.pol (y ≫ q) := sharpOver_pullback _ _ _ _ F W _ _ t'.pol t.pol q y ψ hsh' hψ hψL
  have s2 : SharpOver F W t''.pol x' := sharpOver_pullback _ _ _ _ F W _ _ t.pol t''.pol _ (spMap i₁) ψ' s1 hψ' hψL'
  have s3 : SharpOver F W ρ.P u := sharpOver_pullback _ _ _ _ F W _ _ t''.pol ρ.P x' (spMap i₂) φ s2 hpb hL
  have hbase : spMap R.val.toRingHom ≫ y ≫ q ≫ F.s = spMap ((algebraMap _ Ω).comp κ) := by
    rw [hqs, ← Category.assoc y, hys]
    simp only [spMap, ← Spec.map_comp]
    rfl
  have hκ : κ.Finite := (IsFinite.SpecMap_iff _).1 hfin
  haveI := hint
  obtain ⟨Y, qY, hYn, hYfin, hYsurj, hYs, hYpt⟩ := exists_levModel g n F _ Ω κ hκ (spMap S.R.val.toRingHom ≫ u)
    (by rw [hpe]; simpa only [Category.assoc] using hbase) (by rw [hpe]; exact hstalk) (fun w => by rw [hpe]; exact hpt w)
  have hu : u ≫ F.s = spMap (algebraMap _ S.R) ≫ spMap κ := by
    simp only [u, x', Category.assoc]
    rw [hqs, ← Category.assoc y, hys]
    simp only [spMap, ← Spec.map_comp]
    rfl
  exact ⟨_, Ω, inferInstance, inferInstance, inferInstance, inferInstance, κ, S, ρ, u, Y, qY,
    ⟨hκ, hinj, hSg, s3, hu⟩, ⟨hYn, hYfin, hYsurj, hYs, hYpt⟩, hbig, hfinS⟩

end GlobalTheory.SiegLevSys
end
