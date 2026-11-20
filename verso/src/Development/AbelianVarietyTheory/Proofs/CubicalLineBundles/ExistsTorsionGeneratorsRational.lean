import Mathlib
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLinearEquivOfPeriod
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIntermediateFieldOfPowEqOne
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLinearOfIsMonHom
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PolCountableAndTangentExt
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsLieCombOneIffComp
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HermFormPrincipalDimOne
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SubsingletonPrimeSpectrum

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Serre
open scoped CategoryTheory.Obj UpperHalfPlane TensorProduct

namespace GlobalTheory.TorsionGenerators

variable {R : Type} [CommRing R]

/- English proof (translation)
Take `⟨P', φ, h⟩` from `exists_isPolFibre hL.polBaseChange t P`. Take `⟨β, hβ⟩` from `UnifPoint.exists_pointEquiv h.2.1`. Use `⟨P', φ, β, h, hβ, fun n x y c H => ?_⟩` and prove the remaining obligations. Establish `H'` using `(weilIs_grpPullback_of_comm _ _ P.A P'.A _ φ P.L P'.L P.isLB P'.isLB h.2.1 (LBIso.symm h.2.2) _ n x y (pushPt h.2.1.1.w x) (pushPt h.2.1.1.w y) c rfl rfl).1 H`. Conclude with `UnifPoint.weilIs_congr (Category.id_comp _) (hβ x).symm (hβ y).symm H'`.
-/
theorem exists_fibre (hL : Out.Laws) (P : Out.PolAV (Sp R)) [IsCommMonObj P.A] {k : Type} [CommRing k] (t : R →+* k) :
    ∃ (P' : Out.PolAV (Sp k)) (φ : P'.A.left ⟶ P.A.left)
      (β : (𝟙_ (Over (Sp k)) ⟶ P'.A) ≃* (Over.mk (spMap t) ⟶ P.A)), IsPolFibre t P P' φ ∧
      (∀ x, (β x).left = x.left ≫ φ) ∧ ∀ (n : ℤ) x y (c : Γ(Sp k, ⊤)ˣ),
        Out.WeilIs P'.A P'.L n x y c → Out.WeilIs P.A P.L n (β x) (β y) c := by
  obtain ⟨P', φ, h⟩ := exists_isPolFibre hL.polBaseChange t P
  obtain ⟨β, hβ⟩ := UnifPoint.exists_pointEquiv h.2.1
  refine ⟨P', φ, β, h, hβ, fun n x y c H => ?_⟩
  have H' := (weilIs_grpPullback_of_comm _ _ P.A P'.A _ φ P.L P'.L P.isLB P'.isLB h.2.1 (LBIso.symm h.2.2) _ n x y
    (pushPt h.2.1.1.w x) (pushPt h.2.1.1.w y) c rfl rfl).1 H
  exact UnifPoint.weilIs_congr (Category.id_comp _) (hβ x).symm (hβ y).symm H'

/- English proof (translation)
Take `⟨P', φ, β, h, -, -⟩` from `exists_fibre hL P t`. Establish `h1 : 1 ≤ n` using `Nat.pos_of_ne_zero fun e => hn (by simp [e])`. Use `(hL.mulN _ P' n h1).2.2.2.2 k (𝟙 _) hn` as an intermediate fact. Rewrite using `[← h.1, ← this]`. Use `(Nat.card_congr (β.toEquiv.subtypeEquiv fun x => ?_)).symm` and prove the remaining obligations.

Use `show x ^ n = 1 ↔ β x ^ n = 1`. Rewrite using `[← map_pow, MulEquiv.map_eq_one_iff]`.
-/
theorem card_torsion (hL : Out.Laws) (P : Out.PolAV (Sp R)) [IsCommMonObj P.A] {k : Type} [Field k] [IsAlgClosed k]
    (t : R →+* k) {n : ℕ} (hn : (n : k) ≠ 0) :
    Nat.card {x : Over.mk (spMap t) ⟶ P.A // x ^ n = 1} = n ^ (2 * P.g) := by
  obtain ⟨P', φ, β, h, -, -⟩ := exists_fibre hL P t
  have h1 : 1 ≤ n := Nat.pos_of_ne_zero fun e => hn (by simp [e])
  have := (hL.mulN _ P' n h1).2.2.2.2 k (𝟙 _) hn
  rw [← h.1, ← this]
  refine (Nat.card_congr (β.toEquiv.subtypeEquiv fun x => ?_)).symm
  show x ^ n = 1 ↔ β x ^ n = 1
  rw [← map_pow, MulEquiv.map_eq_one_iff]

/- English proof (translation)
Take `⟨P', φ, β, h, -, H⟩` from `exists_fibre hL P t`. Take `⟨x, rfl⟩` from `β.surjective x`. Take `⟨y, rfl⟩` from `β.surjective y`. Rewrite `hx`, `hy` using `[← map_pow, MulEquiv.map_eq_one_iff]`. Take `⟨c, hc, -⟩` from `(hL.weil _ P' n _).1 x y hx hy`.

Use `⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom.toMonoidHom c, ?_⟩` and prove the remaining obligations. Establish `e : unitOn (Units.map (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom.toMonoidHom c) = c` using `Units.ext (CommRingCat.inv_hom_apply (Scheme.ΓSpecIso (CommRingCat.of k)) c.val)`. Rewrite using `[e]`. Conclude with `H n x y c hc`.
-/
theorem exists_weilIs (hL : Out.Laws) (P : Out.PolAV (Sp R)) [IsCommMonObj P.A] {k : Type} [Field k]
    (t : R →+* k) {n : ℕ} {x y : Over.mk (spMap t) ⟶ P.A} (hx : x ^ n = 1) (hy : y ^ n = 1) :
    ∃ u : kˣ, Out.WeilIs P.A P.L n x y (unitOn u) := by
  obtain ⟨P', φ, β, h, -, H⟩ := exists_fibre hL P t
  obtain ⟨x, rfl⟩ := β.surjective x
  obtain ⟨y, rfl⟩ := β.surjective y
  rw [← map_pow, MulEquiv.map_eq_one_iff] at hx hy
  obtain ⟨c, hc, -⟩ := (hL.weil _ P' n _).1 x y hx hy
  refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom.toMonoidHom c, ?_⟩
  have e : unitOn (Units.map (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom.toMonoidHom c) = c :=
    Units.ext (CommRingCat.inv_hom_apply (Scheme.ΓSpecIso (CommRingCat.of k)) c.val)
  rw [e]
  exact H n x y c hc

/- English proof (translation)
Introduce `a b h` and use `Units.ext ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k)).inv).1 (congrArg Units.val h))`.
-/
theorem unitOn_injective {k : Type} [CommRing k] : Function.Injective (unitOn (R := k)) := fun a b h =>
  Units.ext ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k)).inv).1 (congrArg Units.val h))

section Ext

variable {K k : Type} [Field K] [Field k] {t : R →+* K} {t' : R →+* k} {β : K →+* k}

def extPt (e : β.comp t = t') : Over.mk (spMap t') ⟶ Over.mk (spMap t) :=
  Over.homMk (spMap β) ((spMap_comp_spMap _ _).trans (congrArg spMap e))

/- English proof (translation)
Establish `: Epi (extPt e).left` using `TorsionSeparable.epi_specMap β`. Establish `: Epi (extPt e)` using `Over.epi_of_epi_left _`. Conclude with `(cancel_epi _).1 h`.
-/
theorem extPt_injective (e : β.comp t = t') {A : Over (Sp R)} {x y : Over.mk (spMap t) ⟶ A}
    (h : extPt e ≫ x = extPt e ≫ y) : x = y := by
  have : Epi (extPt e).left := TorsionSeparable.epi_specMap β
  have : Epi (extPt e) := Over.epi_of_epi_left _
  exact (cancel_epi _).1 h

/- English proof (translation)
Establish `H'` using `CommPairing.weilIs_pull hL.globalFns P.isAb P.isLB (extPt e) H`. Establish `e' : Units.map (extPt e).left.appTop.hom.toMonoidHom (unitOn u) = unitOn (Units.map β.toMonoidHom u)` using `Units.ext (congrArg (fun q => q.hom u.val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom β))).symm`. Rewrite `H'` using `[e']`. Then use the resulting hypothesis.
-/
theorem weilIs_extPt (hL : Out.Laws) (P : Out.PolAV (Sp R)) (e : β.comp t = t') {n : ℤ}
    {x y : Over.mk (spMap t) ⟶ P.A} {u : Kˣ} (H : Out.WeilIs P.A P.L n x y (unitOn u)) :
    Out.WeilIs P.A P.L n (extPt e ≫ x) (extPt e ≫ y) (unitOn (Units.map β.toMonoidHom u)) := by
  have H' := CommPairing.weilIs_pull hL.globalFns P.isAb P.isLB (extPt e) H
  have e' : Units.map (extPt e).left.appTop.hom.toMonoidHom (unitOn u) = unitOn (Units.map β.toMonoidHom u) :=
    Units.ext (congrArg (fun q => q.hom u.val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom β))).symm
  rwa [e'] at H'

/- English proof (translation)
Establish `hK : (n : K) ≠ 0` using `Nat.cast_ne_zero.2 hn.ne'`. Establish `hk : (n : k) ≠ 0` using `by rw [← map_natCast β]; exact (map_ne_zero β).2 hK`. Set `f : {x : Over.mk (spMap t) ⟶ P.A // x ^ n = 1} → {x : Over.mk (spMap t') ⟶ P.A // x ^ n = 1}` to `fun y => ⟨extPt e ≫ y.1, by rw [← comp_pow, y.2, comp_one]⟩`. Establish `hf : Function.Injective f` using `fun a b h => Subtype.ext (extPt_injective e (congrArg Subtype.val h))`. Establish `: Finite {x : Over.mk (spMap t') ⟶ P.A // x ^ n = 1}` using `Nat.finite_of_card_ne_zero (by rw [card_torsion hL P t' hk]; positivity)`.

Take `⟨y, hy⟩` from `(hf.bijective_of_nat_card_le (by rw [card_torsion hL P t' hk, card_torsion hL P t hK])).2 ⟨x, hx⟩`. Conclude with `⟨y.1, congrArg Subtype.val hy⟩`.
-/
theorem exists_torsion_extPt (hL : Out.Laws) (P : Out.PolAV (Sp R)) [IsCommMonObj P.A] [IsAlgClosed K] [IsAlgClosed k]
    [CharZero K] (e : β.comp t = t') {n : ℕ} (hn : 0 < n) {x : Over.mk (spMap t') ⟶ P.A} (hx : x ^ n = 1) :
    ∃ y, extPt e ≫ y = x := by
  have hK : (n : K) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have hk : (n : k) ≠ 0 := by rw [← map_natCast β]; exact (map_ne_zero β).2 hK
  let f : {x : Over.mk (spMap t) ⟶ P.A // x ^ n = 1} → {x : Over.mk (spMap t') ⟶ P.A // x ^ n = 1} :=
    fun y => ⟨extPt e ≫ y.1, by rw [← comp_pow, y.2, comp_one]⟩
  have hf : Function.Injective f := fun a b h => Subtype.ext (extPt_injective e (congrArg Subtype.val h))
  have : Finite {x : Over.mk (spMap t') ⟶ P.A // x ^ n = 1} :=
    Nat.finite_of_card_ne_zero (by rw [card_torsion hL P t' hk]; positivity)
  obtain ⟨y, hy⟩ := (hf.bijective_of_nat_card_le
    (by rw [card_torsion hL P t' hk, card_torsion hL P t hK])).2 ⟨x, hx⟩
  exact ⟨y.1, congrArg Subtype.val hy⟩

end Ext

section System

variable {O : Type} [CommRing O] (P : Out.PolAV (Sp R)) (a : OAct O P.A) (tr : O → ℤ)

def IsGenSystem {k : Type} [Field k] (t : R →+* k) (ε : ℕ → (Over.mk (spMap t) ⟶ P.A)) (ζ : ℕ → kˣ) : Prop :=
  (∀ n, 0 < n → IsPrimitiveRoot (ζ n) n) ∧
  (∀ n m, 0 < n → 0 < m → ζ (n * m) ^ m = ζ n ∧ ε (n * m) ^ m = ε n) ∧
  (∀ n, 0 < n → (∀ c : O, ε n ≫ a.act c = 1 ↔ ∃ c' : O, c = n * c') ∧
    (∀ x, x ^ n = 1 ↔ ∃ c : O, x = ε n ≫ a.act c) ∧
    ∀ c : O, Out.WeilIs P.A P.L n (ε n ≫ a.act c) (ε n) (unitOn (ζ n ^ tr c)))

variable {P a tr} {K k : Type} [Field K] [Field k] {t : R →+* K} {t' : R →+* k} {β : K →+* k}

/- English proof (translation)
The claim follows from `((h.2.2 n hn).2.1 _).2 ⟨1, by rw [a.one, Category.comp_id]⟩`.
-/
theorem IsGenSystem.pow_eq_one {ε : ℕ → (Over.mk (spMap t) ⟶ P.A)} {ζ : ℕ → Kˣ} (h : IsGenSystem P a tr t ε ζ)
    {n : ℕ} (hn : 0 < n) : ε n ^ n = 1 :=
  ((h.2.2 n hn).2.1 _).2 ⟨1, by rw [a.one, Category.comp_id]⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h => extPt_injective e (h.trans (comp_one _).symm), fun h => by rw [h, comp_one]⟩`.
-/
theorem extPt_eq_one_iff (e : β.comp t = t') {x : Over.mk (spMap t) ⟶ P.A} : extPt e ≫ x = 1 ↔ x = 1 :=
  ⟨fun h => extPt_injective e (h.trans (comp_one _).symm), fun h => by rw [h, comp_one]⟩

/- English proof (translation)
The claim follows from `Units.map_injective β.injective`.
-/
theorem unitsMap_injective (β : K →+* k) : Function.Injective (Units.map β.toMonoidHom) :=
  Units.map_injective β.injective

/- English proof (translation)
Use `⟨fun n hn => (h.1 n hn).map_of_injective (unitsMap_injective β), fun n m hn hm => ⟨?_, ?_⟩, fun n hn => ⟨fun c => ?_, fun x => ⟨fun hx => ?_, ?_⟩, fun c => ?_⟩⟩` and prove the remaining obligations. Rewrite using `[← map_pow, (h.2.1 n m hn hm).1]`. Rewrite using `[← comp_pow, (h.2.1 n m hn hm).2]`. Rewrite using `[Category.assoc, extPt_eq_one_iff, (h.2.2 n hn).1]`. Take `⟨y, rfl⟩` from `exists_torsion_extPt hL P e hn hx`.

Rewrite `hx` using `[← comp_pow, extPt_eq_one_iff]`. Take `⟨c, rfl⟩` from `((h.2.2 n hn).2.1 y).1 hx`. Conclude with `⟨c, (Category.assoc _ _ _).symm⟩`. Introduce and unpack `⟨c, rfl⟩`. Rewrite using `[Category.assoc, ← comp_pow, ((h.2.2 n hn).2.1 _).2 ⟨c, rfl⟩, comp_one]`.

Rewrite using `[Category.assoc, ← map_zpow]`. Conclude with `weilIs_extPt hL P e ((h.2.2 n hn).2.2 c)`.
-/
theorem IsGenSystem.up (hL : Out.Laws) [IsCommMonObj P.A] [IsAlgClosed K] [IsAlgClosed k] [CharZero K]
    (e : β.comp t = t') {ε : ℕ → (Over.mk (spMap t) ⟶ P.A)} {ζ : ℕ → Kˣ} (h : IsGenSystem P a tr t ε ζ) :
    IsGenSystem P a tr t' (fun n => extPt e ≫ ε n) (fun n => Units.map β.toMonoidHom (ζ n)) := by
  refine ⟨fun n hn => (h.1 n hn).map_of_injective (unitsMap_injective β), fun n m hn hm => ⟨?_, ?_⟩,
    fun n hn => ⟨fun c => ?_, fun x => ⟨fun hx => ?_, ?_⟩, fun c => ?_⟩⟩
  · rw [← map_pow, (h.2.1 n m hn hm).1]
  · rw [← comp_pow, (h.2.1 n m hn hm).2]
  · rw [Category.assoc, extPt_eq_one_iff, (h.2.2 n hn).1]
  · obtain ⟨y, rfl⟩ := exists_torsion_extPt hL P e hn hx
    rw [← comp_pow, extPt_eq_one_iff] at hx
    obtain ⟨c, rfl⟩ := ((h.2.2 n hn).2.1 y).1 hx
    exact ⟨c, (Category.assoc _ _ _).symm⟩
  · rintro ⟨c, rfl⟩
    rw [Category.assoc, ← comp_pow, ((h.2.2 n hn).2.1 _).2 ⟨c, rfl⟩, comp_one]
  · rw [Category.assoc, ← map_zpow]
    exact weilIs_extPt hL P e ((h.2.2 n hn).2.2 c)

/- English proof (translation)
Establish `: NeZero n` using `⟨hn.ne'⟩`. Take `⟨z', hz'⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot K n`. Take `⟨i, -, hi⟩` from `(hz'.map_of_injective β.injective).eq_pow_of_pow_eq_one (show (z : k) ^ n = 1 by rw [← Units.val_pow_eq_pow_val, hz, Units.val_one])`. Use `⟨(hz'.isUnit hn.ne').unit ^ i, Units.ext ?_⟩` and prove the remaining obligations. Rewrite using `[← hi]`.

Simplify using the standard rewrite rules.
-/
theorem exists_unit_of_pow [IsAlgClosed K] [CharZero K] (β : K →+* k) {n : ℕ} (hn : 0 < n) {z : kˣ}
    (hz : z ^ n = 1) : ∃ u : Kˣ, Units.map β.toMonoidHom u = z := by
  have : NeZero n := ⟨hn.ne'⟩
  obtain ⟨z', hz'⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K n
  obtain ⟨i, -, hi⟩ := (hz'.map_of_injective β.injective).eq_pow_of_pow_eq_one
    (show (z : k) ^ n = 1 by rw [← Units.val_pow_eq_pow_val, hz, Units.val_one])
  refine ⟨(hz'.isUnit hn.ne').unit ^ i, Units.ext ?_⟩
  rw [← hi]
  simp

/- English proof (translation)
Establish `h1 : ∀ n, ∃ y, 0 < n → extPt e ≫ y = ε n` using `fun n => by`. Distinguish the cases in `hn : 0 < n`. Conclude with `(exists_torsion_extPt hL P e hn (h.pow_eq_one hn)).imp fun _ h _ => h`. Conclude with `⟨1, fun h => absurd h hn⟩`. Establish `h2 : ∀ n, ∃ u : Kˣ, 0 < n → Units.map β.toMonoidHom u = ζ n` using `fun n => by`.

Distinguish the cases in `hn : 0 < n`. Conclude with `(exists_unit_of_pow β hn (h.1 n hn).pow_eq_one).imp fun _ h _ => h`. Conclude with `⟨1, fun h => absurd h hn⟩`. Use `choose ε' hε using h1`. Use `choose ζ' hζ using h2`.

Establish `h3 : ∀ n, 0 < n → ∀ x, x ^ n = 1 ↔ ∃ c : O, x = ε' n ≫ a.act c` using `fun n hn x => by`. Rewrite using `[← extPt_eq_one_iff e, comp_pow, (h.2.2 n hn).2.1]`. Use `exists_congr fun c => ?_` and prove the remaining obligations. Rewrite using `[← hε n hn, Category.assoc]`. Conclude with `⟨extPt_injective e, fun h => by rw [h]⟩`.

Use `⟨ε', ζ', fun n hn => ?_, fun n m hn hm => ⟨?_, ?_⟩, fun n hn => ⟨fun c => ?_, h3 n hn, fun c => ?_⟩⟩` and prove the remaining obligations. Conclude with `IsPrimitiveRoot.of_map_of_injective (hζ n hn ▸ h.1 n hn) (unitsMap_injective β)`. Apply `unitsMap_injective β` to reduce the goal to its premises. Rewrite using `[map_pow, hζ _ (Nat.mul_pos hn hm), hζ n hn, (h.2.1 n m hn hm).1]`. Apply `extPt_injective e` to reduce the goal to its premises.

Rewrite using `[comp_pow, hε _ (Nat.mul_pos hn hm), hε n hn, (h.2.1 n m hn hm).2]`. Rewrite using `[← extPt_eq_one_iff e, ← Category.assoc, hε n hn, (h.2.2 n hn).1]`. Take `⟨u, hu⟩` from `exists_weilIs hL P t ((h3 n hn _).2 ⟨c, rfl⟩) ((h3 n hn (ε' n)).2 ⟨1, by rw [a.one, Category.comp_id]⟩)`. Establish `H` using `weilIs_extPt hL P e hu`. Rewrite `H` using `[← Category.assoc, hε n hn]`.

Establish `e'` using `unitOn_injective (CommutatorPairing.weilIs_unique hL.globalFns P.isAb P.isLB H ((h.2.2 n hn).2.2 c))`. Rewrite `e'` using `[← hζ n hn, ← map_zpow]`. Rewrite using `[← unitsMap_injective β e']` and apply the resulting hypothesis.
-/
theorem IsGenSystem.down (hL : Out.Laws) [IsCommMonObj P.A] [IsAlgClosed K] [IsAlgClosed k] [CharZero K]
    (e : β.comp t = t') {ε : ℕ → (Over.mk (spMap t') ⟶ P.A)} {ζ : ℕ → kˣ} (h : IsGenSystem P a tr t' ε ζ) :
    ∃ ε' ζ', IsGenSystem P a tr t ε' ζ' := by
  have h1 : ∀ n, ∃ y, 0 < n → extPt e ≫ y = ε n := fun n => by
    by_cases hn : 0 < n
    · exact (exists_torsion_extPt hL P e hn (h.pow_eq_one hn)).imp fun _ h _ => h
    · exact ⟨1, fun h => absurd h hn⟩
  have h2 : ∀ n, ∃ u : Kˣ, 0 < n → Units.map β.toMonoidHom u = ζ n := fun n => by
    by_cases hn : 0 < n
    · exact (exists_unit_of_pow β hn (h.1 n hn).pow_eq_one).imp fun _ h _ => h
    · exact ⟨1, fun h => absurd h hn⟩
  choose ε' hε using h1
  choose ζ' hζ using h2
  have h3 : ∀ n, 0 < n → ∀ x, x ^ n = 1 ↔ ∃ c : O, x = ε' n ≫ a.act c := fun n hn x => by
    rw [← extPt_eq_one_iff e, comp_pow, (h.2.2 n hn).2.1]
    refine exists_congr fun c => ?_
    rw [← hε n hn, Category.assoc]
    exact ⟨extPt_injective e, fun h => by rw [h]⟩
  refine ⟨ε', ζ', fun n hn => ?_, fun n m hn hm => ⟨?_, ?_⟩, fun n hn => ⟨fun c => ?_, h3 n hn, fun c => ?_⟩⟩
  · exact IsPrimitiveRoot.of_map_of_injective (hζ n hn ▸ h.1 n hn) (unitsMap_injective β)
  · apply unitsMap_injective β
    rw [map_pow, hζ _ (Nat.mul_pos hn hm), hζ n hn, (h.2.1 n m hn hm).1]
  · apply extPt_injective e
    rw [comp_pow, hε _ (Nat.mul_pos hn hm), hε n hn, (h.2.1 n m hn hm).2]
  · rw [← extPt_eq_one_iff e, ← Category.assoc, hε n hn, (h.2.2 n hn).1]
  · obtain ⟨u, hu⟩ := exists_weilIs hL P t ((h3 n hn _).2 ⟨c, rfl⟩)
      ((h3 n hn (ε' n)).2 ⟨1, by rw [a.one, Category.comp_id]⟩)
    have H := weilIs_extPt hL P e hu
    rw [← Category.assoc, hε n hn] at H
    have e' := unitOn_injective
      (CommutatorPairing.weilIs_unique hL.globalFns P.isAb P.isLB H ((h.2.2 n hn).2.2 c))
    rw [← hζ n hn, ← map_zpow] at e'
    rwa [← unitsMap_injective β e']

end System

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨A, i, _, q, ht⟩ : ∃ (A : CommRingCat.{0}) (i : Spec A ⟶ X) (_ : IsOpenImmersion i) (t : Spec A), i t = x (IsLocalRing.closedPoint Ω) := by`. Take `⟨n, t, ht⟩` from `X.affineCover.exists_eq (x (IsLocalRing.closedPoint Ω))`. Conclude with `⟨_, X.affineCover.f n, X.affineCover.map_prop n, t, ht⟩`. Establish `hr : Set.range x ⊆ Set.range i`. Introduce and unpack `_ ⟨u, rfl⟩`.

Conclude with `⟨q, ht.trans (congrArg x (Subsingleton.elim _ _))⟩`. Take `⟨φ, hφ⟩` from `Spec.map_surjective (IsOpenImmersion.lift i x hr)`. Establish `hφa : Spec.map φ ≫ i = x` using `by rw [hφ, IsOpenImmersion.lift_fac]`. Take `⟨ψ, hψ⟩` from `Spec.map_surjective (i ≫ p)`. Establish `h₂ : LocallyOfFiniteType (Spec.map ψ)` using `by rw [hψ]; infer_instance`.

Rewrite `h₂` using `[HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]`. Establish `hc : ψ ≫ φ = CommRingCat.ofHom t`. Rewrite using `[← Spec.map_inj, Spec.map_comp, hψ, ← Category.assoc, hφa, hx]`. Set `: Algebra R A` to `ψ.hom.toAlgebra`. Establish `: Algebra.FiniteType R A` using `h₂`.

Take `⟨s, hs⟩` from `Algebra.FiniteType.out (R := R) (A := A)`. Use `⟨φ.hom '' (s : Set A), s.finite_toSet.image _, fun B _ io hio h1 h2 => ?_⟩` and prove the remaining obligations. Establish `hmem : ∀ y, φ.hom y ∈ io.range`. Introduce `y`. Establish `hy : y ∈ Algebra.adjoin R (s : Set A)` using `by simp [hs]`.

Proceed by induction on `hy using Algebra.adjoin_induction with`. Consider the case `mem y hy => exact h2 _ ⟨y, hy, rfl⟩`. Consider the case `algebraMap c => exact (congr($hc c) : φ.hom (algebraMap R A c) = t c) ▸ h1 c`. Consider the case `add y z _ _ hy hz => rw [map_add]`. Conclude with `add_mem hy hz`.

Consider the case `mul y z _ _ hy hz => rw [map_mul]`. Conclude with `mul_mem hy hz`. Set `e : B ≃+* io.range` to `RingEquiv.ofBijective io.rangeRestrict ⟨fun a b h => hio (congrArg Subtype.val h), io.rangeRestrict_surjective⟩`. Use `⟨Spec.map (CommRingCat.ofHom (e.symm.toRingHom.comp (φ.hom.codRestrict io.range hmem))) ≫ i, ?_⟩` and prove the remaining obligations. Rewrite using `[← hφa, ← Spec.map_comp_assoc]`.

Use `congr 2`. Use extensionality with `y`. Conclude with `congrArg Subtype.val (e.apply_symm_apply ⟨φ.hom y, hmem y⟩)`.
-/
theorem exists_finite_coordinates {Ω : Type} [Field Ω] {X : Scheme.{0}} (p : X ⟶ Sp R) [LocallyOfFiniteType p]
    (t : R →+* Ω) (x : Sp Ω ⟶ X) (hx : x ≫ p = spMap t) :
    ∃ s : Set Ω, s.Finite ∧ ∀ (B : Type) [CommRing B] (io : B →+* Ω), Function.Injective io → (∀ c, t c ∈ io.range) →
      (∀ y ∈ s, y ∈ io.range) → ∃ b : Sp B ⟶ X, spMap io ≫ b = x := by
  obtain ⟨A, i, _, q, ht⟩ : ∃ (A : CommRingCat.{0}) (i : Spec A ⟶ X) (_ : IsOpenImmersion i)
      (t : Spec A), i t = x (IsLocalRing.closedPoint Ω) := by
    obtain ⟨n, t, ht⟩ := X.affineCover.exists_eq (x (IsLocalRing.closedPoint Ω))
    exact ⟨_, X.affineCover.f n, X.affineCover.map_prop n, t, ht⟩
  have hr : Set.range x ⊆ Set.range i := by
    rintro _ ⟨u, rfl⟩
    exact ⟨q, ht.trans (congrArg x (Subsingleton.elim _ _))⟩
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (IsOpenImmersion.lift i x hr)
  have hφa : Spec.map φ ≫ i = x := by rw [hφ, IsOpenImmersion.lift_fac]
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (i ≫ p)
  have h₂ : LocallyOfFiniteType (Spec.map ψ) := by rw [hψ]; infer_instance
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at h₂
  have hc : ψ ≫ φ = CommRingCat.ofHom t := by
    rw [← Spec.map_inj, Spec.map_comp, hψ, ← Category.assoc, hφa, hx]
  let : Algebra R A := ψ.hom.toAlgebra
  have : Algebra.FiniteType R A := h₂
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := R) (A := A)
  refine ⟨φ.hom '' (s : Set A), s.finite_toSet.image _, fun B _ io hio h1 h2 => ?_⟩
  have hmem : ∀ y, φ.hom y ∈ io.range := by
    intro y
    have hy : y ∈ Algebra.adjoin R (s : Set A) := by simp [hs]
    induction hy using Algebra.adjoin_induction with
    | mem y hy => exact h2 _ ⟨y, hy, rfl⟩
    | algebraMap c => exact (congr($hc c) : φ.hom (algebraMap R A c) = t c) ▸ h1 c
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | mul y z _ _ hy hz => rw [map_mul]; exact mul_mem hy hz
  let e : B ≃+* io.range := RingEquiv.ofBijective io.rangeRestrict
    ⟨fun a b h => hio (congrArg Subtype.val h), io.rangeRestrict_surjective⟩
  refine ⟨Spec.map (CommRingCat.ofHom (e.symm.toRingHom.comp (φ.hom.codRestrict io.range hmem))) ≫ i, ?_⟩
  rw [← hφa, ← Spec.map_comp_assoc]
  congr 2
  ext y
  exact congrArg Subtype.val (e.apply_symm_apply ⟨φ.hom y, hmem y⟩)

/- English proof (translation)
Use `letI := io.toAlgebra`. Use `letI := β.toAlgebra`. Use `haveI : IsScalarTower ℚ K Q := .of_algebraMap_eq' (Subsingleton.elim _ _)`. Use `haveI : Algebra.IsAlgebraic K Q := Algebra.IsAlgebraic.tower_top (K := ℚ) K`. Conclude with `⟨(IsAlgClosed.lift : Q →ₐ[K] k).toRingHom, (IsAlgClosed.lift : Q →ₐ[K] k).comp_algebraMap⟩`.
-/
theorem exists_extend {K Q k : Type} [Field K] [Field Q] [Field k] [CharZero K] [CharZero Q]
    [Algebra.IsAlgebraic ℚ Q] [IsAlgClosed k] (io : K →+* Q) (β : K →+* k) : ∃ β' : Q →+* k, β'.comp io = β := by
  letI := io.toAlgebra
  letI := β.toAlgebra
  haveI : IsScalarTower ℚ K Q := .of_algebraMap_eq' (Subsingleton.elim _ _)
  haveI : Algebra.IsAlgebraic K Q := Algebra.IsAlgebraic.tower_top (K := ℚ) K
  exact ⟨(IsAlgClosed.lift : Q →ₐ[K] k).toRingHom, (IsAlgClosed.lift : Q →ₐ[K] k).comp_algebraMap⟩

/- English proof (translation)
Rewrite using `[spMap_comp_spMap, spMap_comp_spMap]`. Use `congr 1`. Use `RingHom.ext fun x => ?_` and prove the remaining obligations. Apply the tactic sequence `ext <;> simp [Chart.dualMapR, epsScaleR, _root_.mul_comm]`.
-/
theorem spMap_dual_scale {R' : Type} [CommRing R'] (s : R →+* R') (c : R) :
    spMap (Chart.dualMapR s) ≫ spMap (epsScaleR c) = spMap (epsScaleR (s c)) ≫ spMap (Chart.dualMapR s) := by
  rw [spMap_comp_spMap, spMap_comp_spMap]
  congr 1
  refine RingHom.ext fun x => ?_
  ext <;> simp [Chart.dualMapR, epsScaleR, _root_.mul_comm]

/- English proof (translation)
Take `⟨P', φ, β, h, hβ, hW⟩` from `exists_fibre hL P s`. Take `⟨v', hv', -⟩` from `existsUnique_isVecOver h.2.1.1 v`. Take `⟨rig, hrig⟩` from `P'.rigid`. Take `⟨u, Hm, χ, Ef, hA, -, hd, -, hlin, -, hE, hB, hw⟩` from `hU P' rig hrig`. Establish `ht` using `hv'.isTangent h.2.1 hv`.

Take `⟨w, hw', -⟩` from `hd v' ht`. Take `⟨hw0, hl⟩` from `hΛ P' φ v' u w h hv' hw'`. Establish `hg' : P'.g = 1` using `h.1.trans hg`. Use `⟨fun z => β (u.ex (z • w)), fun z z' => by simp only [add_smul, u.ex_add, map_mul], fun x => ?_, fun z => by simp only [MulEquiv.map_eq_one_iff, u.ker, hl], fun f c hf hc z => ?_, fun n x y m c hn hx hy hm hc => ?_⟩` and prove the remaining obligations. Take `⟨x, rfl⟩` from `β.surjective x`.

Take `⟨y, rfl⟩` from `u.ex_onto x`. Establish `: Subsingleton (Fin P'.g)` using `by rw [hg']; infer_instance`. Take `⟨i, hi⟩` from `Function.ne_iff.1 hw0`. Use `⟨y i / w i, congrArg (fun q => β (u.ex q)) (funext fun j => ?_)⟩` and prove the remaining obligations. Rewrite using `[Subsingleton.elim j i, Pi.smul_apply, smul_eq_mul, div_mul_cancel₀ _ hi]`.

Take `⟨f', hf', ef⟩` from `HomDescent.exists_isMonHom_pull h.2.1 h.2.1 f`. Take `⟨F, hF⟩` from `hlin f' hf'`. Establish `d1` using `HomLinear.isDiff_comp u u f' F hF ht hw'`. Establish `hc' : IsLieComb ![s c] ![v'] (v' ≫ f')`. Rewrite `hc`, the goal using `[LieMultiple.isLieComb_one_iff]`.

Use `h.2.1.1.hom_ext ?_ ?_` and prove the remaining obligations. Establish `hv'' : v'.left ≫ φ = _` using `hv'`. Rewrite using `[Over.comp_left, Category.assoc, ef, ← Category.assoc, hv'', Category.assoc, ← Over.comp_left, hc, Category.assoc, hv'', ← Category.assoc, ← Category.assoc, spMap_dual_scale]`. Conclude with `(Over.w _).trans (Over.w (Chart.spMap (Chart.scaleD (s c)) ≫ v')).symm`. Establish `d2` using `UnifDifferential.isDiff_scale u hw' (s c)`.

Rewrite `d2` using `[← (LieMultiple.isLieComb_one_iff_comp _ _ _).1 hc']`. Establish `e : F w = s c • w` using `(hd _ (HomLinear.isTangent_comp f' ht)).unique d1 d2`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Use `show (β (u.ex (z • w)) ≫ f).left = (β (u.ex ((s c * z) • w))).left`. Rewrite using `[_root_.mul_comm, mul_smul, ← e, ← map_smul, hF, Over.comp_left, hβ, hβ, Over.comp_left, Category.assoc, Category.assoc, ef]`.

Establish `H` using `hw n ⟨x • w, (hl x).1 hx⟩ ⟨y • w, (hl y).1 hy⟩ c hn ?_`. Simplify using `only [mul_smul]`. Conclude with `hW _ _ _ _ H`. Establish `e` using `hE ⟨x • w, (hl x).1 hx⟩ ⟨y • w, (hl y).1 hy⟩`. Rewrite `e` using `[hermForm_principal_dim_one _ u.Λ w L Hm Ef hg' hw0 hl hA.1 (hA.2.1 w hw0) hE hB, Complex.div_ofReal_im, ← hm]`.

Rewrite using `[hc, Int.cast_injective e]`.
-/
theorem exists_exp (hU : ThetaUnifAV) (hL : Out.Laws) (s : R →+* ℂ) (P : Out.PolAV (Sp R)) [IsCommMonObj P.A]
    (v : epsR R ⟶ P.A) (L : PeriodPair) (hg : P.g = 1) (hv : IsTangent v)
    (hΛ : ∀ (P' : Out.PolAV (Sp ℂ)) (φ' : P'.A.left ⟶ P.A.left) (v' : epsR ℂ ⟶ P'.A) (u' : HolUnif P'.A P'.L P'.g)
      (w' : Fin P'.g → ℂ), IsPolFibre s P P' φ' → IsVecOver s φ' v v' → u'.IsDiff w' v' →
      w' ≠ 0 ∧ ∀ z : ℂ, z ∈ L.lattice ↔ z • w' ∈ u'.Λ) :
    ∃ E : ℂ → (Over.mk (spMap s) ⟶ P.A), (∀ z z', E (z + z') = E z * E z') ∧ Function.Surjective E ∧
      (∀ z, E z = 1 ↔ z ∈ L.lattice) ∧
      (∀ (f : P.A ⟶ P.A) (c : R), IsMonHom f → IsLieComb ![c] ![v] (v ≫ f) → ∀ z, E z ≫ f = E (s c * z)) ∧
      ∀ (n : ℕ) (x y : ℂ) (m : ℤ) (c : ℂˣ), 0 < n → x ∈ L.lattice → y ∈ L.lattice →
        (m : ℝ) = (x * starRingEnd ℂ y).im / |(L.ω₁ * starRingEnd ℂ L.ω₂).im| →
        (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * m / n) →
        Out.WeilIs P.A P.L n (E ((n : ℂ)⁻¹ * x)) (E ((n : ℂ)⁻¹ * y)) (unitOn c) := by
  obtain ⟨P', φ, β, h, hβ, hW⟩ := exists_fibre hL P s
  obtain ⟨v', hv', -⟩ := existsUnique_isVecOver h.2.1.1 v
  obtain ⟨rig, hrig⟩ := P'.rigid
  obtain ⟨u, Hm, χ, Ef, hA, -, hd, -, hlin, -, hE, hB, hw⟩ := hU P' rig hrig
  have ht := hv'.isTangent h.2.1 hv
  obtain ⟨w, hw', -⟩ := hd v' ht
  obtain ⟨hw0, hl⟩ := hΛ P' φ v' u w h hv' hw'
  have hg' : P'.g = 1 := h.1.trans hg
  refine ⟨fun z => β (u.ex (z • w)), fun z z' => by simp only [add_smul, u.ex_add, map_mul], fun x => ?_,
    fun z => by simp only [MulEquiv.map_eq_one_iff, u.ker, hl], fun f c hf hc z => ?_, fun n x y m c hn hx hy hm hc => ?_⟩
  · obtain ⟨x, rfl⟩ := β.surjective x
    obtain ⟨y, rfl⟩ := u.ex_onto x
    have : Subsingleton (Fin P'.g) := by rw [hg']; infer_instance
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hw0
    refine ⟨y i / w i, congrArg (fun q => β (u.ex q)) (funext fun j => ?_)⟩
    rw [Subsingleton.elim j i, Pi.smul_apply, smul_eq_mul, div_mul_cancel₀ _ hi]
  · obtain ⟨f', hf', ef⟩ := HomDescent.exists_isMonHom_pull h.2.1 h.2.1 f
    obtain ⟨F, hF⟩ := hlin f' hf'
    have d1 := HomLinear.isDiff_comp u u f' F hF ht hw'
    have hc' : IsLieComb ![s c] ![v'] (v' ≫ f') := by
      rw [LieMultiple.isLieComb_one_iff] at hc ⊢
      refine h.2.1.1.hom_ext ?_ ?_
      · have hv'' : v'.left ≫ φ = _ := hv'
        rw [Over.comp_left, Category.assoc, ef, ← Category.assoc, hv'', Category.assoc, ← Over.comp_left, hc,
          Category.assoc, hv'', ← Category.assoc, ← Category.assoc, spMap_dual_scale]
      · exact (Over.w _).trans (Over.w (Chart.spMap (Chart.scaleD (s c)) ≫ v')).symm
    have d2 := UnifDifferential.isDiff_scale u hw' (s c)
    rw [← (LieMultiple.isLieComb_one_iff_comp _ _ _).1 hc'] at d2
    have e : F w = s c • w := (hd _ (HomLinear.isTangent_comp f' ht)).unique d1 d2
    apply Over.OverMorphism.ext
    show (β (u.ex (z • w)) ≫ f).left = (β (u.ex ((s c * z) • w))).left
    rw [_root_.mul_comm, mul_smul, ← e, ← map_smul, hF, Over.comp_left, hβ, hβ, Over.comp_left, Category.assoc,
      Category.assoc, ef]
  · have H := hw n ⟨x • w, (hl x).1 hx⟩ ⟨y • w, (hl y).1 hy⟩ c hn ?_
    · simp only [mul_smul]
      exact hW _ _ _ _ H
    · have e := hE ⟨x • w, (hl x).1 hx⟩ ⟨y • w, (hl y).1 hy⟩
      rw [hermForm_principal_dim_one _ u.Λ w L Hm Ef hg' hw0 hl hA.1 (hA.2.1 w hw0) hE hB,
        Complex.div_ofReal_im, ← hm] at e
      rw [hc, Int.cast_injective e]

end GlobalTheory.TorsionGenerators

namespace GlobalTheory

end GlobalTheory
