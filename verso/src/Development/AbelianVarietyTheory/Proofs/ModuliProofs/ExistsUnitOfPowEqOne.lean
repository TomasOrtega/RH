import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilPairingFieldExtensionIffStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionPointsFieldExtensionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.TateIsoFieldExt

/- English proof (translation)
Use `haveI : NeZero n := ⟨hn.ne'⟩`. Use `haveI : NeZero (n : K) := ⟨Nat.cast_ne_zero.mpr hn.ne'⟩`. Take `⟨ξ, hξ⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot K n`. Establish `h2 : IsPrimitiveRoot (i ξ) n` using `hξ.map_of_injective i.injective`. Establish `hz' : (z : Ω) ^ n = 1` using `by rw [← Units.val_pow_eq_pow_val, hz, Units.val_one]`.

Take `⟨j, -, hj⟩` from `h2.eq_pow_of_pow_eq_one hz'`. Use `⟨(hξ.isUnit hn.ne').unit ^ j, Units.ext ?_⟩` and prove the remaining obligations. Simplify using `using hj`.
-/
theorem exists_unit_of_pow_eq_one {K Ω : Type} [Field K] [Field Ω] [IsAlgClosed K] [CharZero K]
    (i : K →+* Ω) (n : ℕ) (hn : 0 < n) (z : Ωˣ) (hz : z ^ n = 1) :
    ∃ u : Kˣ, Units.map i.toMonoidHom u = z := by
  haveI : NeZero n := ⟨hn.ne'⟩
  haveI : NeZero (n : K) := ⟨Nat.cast_ne_zero.mpr hn.ne'⟩
  obtain ⟨ξ, hξ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K n
  have h2 : IsPrimitiveRoot (i ξ) n := hξ.map_of_injective i.injective
  have hz' : (z : Ω) ^ n = 1 := by rw [← Units.val_pow_eq_pow_val, hz, Units.val_one]
  obtain ⟨j, -, hj⟩ := h2.eq_pow_of_pow_eq_one hz'
  refine ⟨(hξ.isUnit hn.ne').unit ^ j, Units.ext ?_⟩
  simpa using hj

section Abstract

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
  {K Ω : Type} [Field K] [Field Ω] (i : K →+* Ω) {Q Q' : Type} [Group Q] [Group Q'] (f : Q →* Q')
  {act : 𝓞 E → Q → Q} {act' : 𝓞 E → Q' → Q'}
  {e : ℕ → Q → Q → Kˣ → Prop} {e' : ℕ → Q' → Q' → Ωˣ → Prop}

/- English proof (translation)
The claim follows from `Units.map_injective i.injective`.
-/
theorem units_map_injective : Function.Injective (Units.map i.toMonoidHom) :=
  Units.map_injective i.injective

/- English proof (translation)
Use `⟨{ ζ := fun n => Units.map i.toMonoidHom (I.ζ n) ζ_prim := fun n hn => (I.ζ_prim n hn).map_of_injective (units_map_injective i) ζ_pow := fun n m hn hm => by rw [← map_pow, I.ζ_pow n m hn hm] ev := fun n v => f (I.ev n v) add := fun n a b => by rw [I.add, map_mul] lin := fun n c a …` and prove the remaining obligations. Take `⟨y, hy, rfl⟩` from `honto n hn z hz`. Take `⟨a, rfl⟩` from `(I.onto n hn y).1 hy`. Conclude with `⟨a, rfl⟩`. Introduce and unpack `⟨a, rfl⟩`.

Rewrite using `[← map_pow, (I.onto n hn _).2 ⟨a, rfl⟩, map_one]`.
-/
theorem up (hinj : Function.Injective f)
    (honto : ∀ n, 0 < n → ∀ z : Q', z ^ n = 1 → ∃ y : Q, y ^ n = 1 ∧ f y = z)
    (hact : ∀ c y, f (act c y) = act' c (f y))
    (he : ∀ n y y' c, e' n (f y) (f y') (Units.map i.toMonoidHom c) ↔ e n y y' c)
    (I : TateIso D K Q act e) :
    ∃ I' : TateIso D Ω Q' act' e', ∀ n, 0 < n → (I'.ζ n : Ω) = i (I.ζ n) ∧ ∀ v, I'.ev n v = f (I.ev n v) := by
  refine ⟨{ ζ := fun n => Units.map i.toMonoidHom (I.ζ n)
            ζ_prim := fun n hn => (I.ζ_prim n hn).map_of_injective (units_map_injective i)
            ζ_pow := fun n m hn hm => by rw [← map_pow, I.ζ_pow n m hn hm]
            ev := fun n v => f (I.ev n v)
            add := fun n a b => by rw [I.add, map_mul]
            lin := fun n c a => by rw [I.lin, hact]
            ker := fun n hn a => by rw [← I.ker n hn a, map_eq_one_iff f hinj]
            onto := fun n hn z => ⟨fun hz => ?_, ?_⟩
            tower := fun n m hn hm a => by rw [← map_pow, I.tower n m hn hm]
            isom := fun n hn a b => by rw [← map_zpow, he]; exact I.isom n hn a b },
    fun n _ => ⟨rfl, fun _ => rfl⟩⟩
  · obtain ⟨y, hy, rfl⟩ := honto n hn z hz
    obtain ⟨a, rfl⟩ := (I.onto n hn y).1 hy
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    rw [← map_pow, (I.onto n hn _).2 ⟨a, rfl⟩, map_one]

/- English proof (translation)
Establish `h1 : ∀ n, ∃ u : Kˣ, 0 < n → Units.map i.toMonoidHom u = I'.ζ n` using `fun n => by`. Distinguish the cases in `hn : 0 < n`. Take `⟨u, hu⟩` from `exists_unit_of_pow_eq_one i n hn _ (I'.ζ_prim n hn).pow_eq_one`. Conclude with `⟨u, fun _ => hu⟩`. Conclude with `⟨1, fun h => absurd h hn⟩`.

Establish `h2 : ∀ n v, ∃ y : Q, (0 < n → f y = I'.ev n v) ∧ (¬ 0 < n → y = 1)` using `fun n v => by`. Distinguish the cases in `hn : 0 < n`. Take `⟨y, -, hy⟩` from `honto n hn _ ((I'.onto n hn _).2 ⟨v, rfl⟩)`. Conclude with `⟨y, fun _ => hy, fun h => absurd hn h⟩`. Conclude with `⟨1, fun h => absurd h hn, fun _ => rfl⟩`.

Use `choose ζ hζ using h1`. Use `choose ev hev hev0 using h2`. Use `⟨{ ζ := ζ ζ_prim := fun n hn => ?_ ζ_pow := fun n m hn hm => units_map_injective i ?_ ev := ev add := fun n a b => ?_ lin := fun n c a => ?_ ker := fun n hn a => by rw [← I'.ker n hn a, ← hev n a hn, map_eq_one_iff f hinj] onto := fun n hn z => ?_ tower := fun n m hn hm a => hinj …` and prove the remaining obligations. Use `IsPrimitiveRoot.of_map_of_injective ?_ (units_map_injective i)` and prove the remaining obligations. Rewrite using `[hζ n hn]`.

Conclude with `I'.ζ_prim n hn`. Rewrite using `[map_pow, hζ _ (Nat.mul_pos hn hm), hζ n hn, I'.ζ_pow n m hn hm]`. Distinguish the cases in `hn : 0 < n`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[map_mul, hev _ _ hn, hev _ _ hn, hev _ _ hn, I'.add]`.

Rewrite using `[hev0 _ _ hn, hev0 _ _ hn, hev0 _ _ hn, _root_.mul_one]`. Distinguish the cases in `hn : 0 < n`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[hact, hev _ _ hn, hev _ _ hn, I'.lin]`. Rewrite using `[hev0 _ _ hn, hev0 _ _ hn, hone]`.

Rewrite using `[← map_eq_one_iff f hinj, map_pow, I'.onto n hn]`. Use `exists_congr fun a => ?_` and prove the remaining obligations. Rewrite using `[← hev n a hn, hinj.eq_iff]`. Rewrite using `[map_pow, hev _ _ (Nat.mul_pos hn hm), hev _ _ hn, I'.tower n m hn hm]`. Rewrite using `[← he, map_zpow, hζ n hn, hev _ _ hn, hev _ _ hn]`.

Conclude with `I'.isom n hn a b`.
-/
theorem down [IsAlgClosed K] [CharZero K] (hinj : Function.Injective f)
    (honto : ∀ n, 0 < n → ∀ z : Q', z ^ n = 1 → ∃ y : Q, y ^ n = 1 ∧ f y = z)
    (hact : ∀ c y, f (act c y) = act' c (f y)) (hone : ∀ c, act c 1 = 1)
    (he : ∀ n y y' c, e' n (f y) (f y') (Units.map i.toMonoidHom c) ↔ e n y y' c)
    (I' : TateIso D Ω Q' act' e') :
    ∃ I : TateIso D K Q act e, ∀ n, 0 < n → (I'.ζ n : Ω) = i (I.ζ n) ∧ ∀ v, I'.ev n v = f (I.ev n v) := by
  have h1 : ∀ n, ∃ u : Kˣ, 0 < n → Units.map i.toMonoidHom u = I'.ζ n := fun n => by
    by_cases hn : 0 < n
    · obtain ⟨u, hu⟩ := exists_unit_of_pow_eq_one i n hn _ (I'.ζ_prim n hn).pow_eq_one
      exact ⟨u, fun _ => hu⟩
    · exact ⟨1, fun h => absurd h hn⟩
  have h2 : ∀ n v, ∃ y : Q, (0 < n → f y = I'.ev n v) ∧ (¬ 0 < n → y = 1) := fun n v => by
    by_cases hn : 0 < n
    · obtain ⟨y, -, hy⟩ := honto n hn _ ((I'.onto n hn _).2 ⟨v, rfl⟩)
      exact ⟨y, fun _ => hy, fun h => absurd hn h⟩
    · exact ⟨1, fun h => absurd h hn, fun _ => rfl⟩
  choose ζ hζ using h1
  choose ev hev hev0 using h2
  refine ⟨{ ζ := ζ
            ζ_prim := fun n hn => ?_
            ζ_pow := fun n m hn hm => units_map_injective i ?_
            ev := ev
            add := fun n a b => ?_
            lin := fun n c a => ?_
            ker := fun n hn a => by rw [← I'.ker n hn a, ← hev n a hn, map_eq_one_iff f hinj]
            onto := fun n hn z => ?_
            tower := fun n m hn hm a => hinj ?_
            isom := fun n hn a b => ?_ },
    fun n hn => ⟨by rw [← hζ n hn]; rfl, fun v => (hev n v hn).symm⟩⟩
  · refine IsPrimitiveRoot.of_map_of_injective ?_ (units_map_injective i)
    rw [hζ n hn]; exact I'.ζ_prim n hn
  · rw [map_pow, hζ _ (Nat.mul_pos hn hm), hζ n hn, I'.ζ_pow n m hn hm]
  · by_cases hn : 0 < n
    · apply hinj
      rw [map_mul, hev _ _ hn, hev _ _ hn, hev _ _ hn, I'.add]
    · rw [hev0 _ _ hn, hev0 _ _ hn, hev0 _ _ hn, _root_.mul_one]
  · by_cases hn : 0 < n
    · apply hinj
      rw [hact, hev _ _ hn, hev _ _ hn, I'.lin]
    · rw [hev0 _ _ hn, hev0 _ _ hn, hone]
  · rw [← map_eq_one_iff f hinj, map_pow, I'.onto n hn]
    refine exists_congr fun a => ?_
    rw [← hev n a hn, hinj.eq_iff]
  · rw [map_pow, hev _ _ (Nat.mul_pos hn hm), hev _ _ hn, I'.tower n m hn hm]
  · rw [← he, map_zpow, hζ n hn, hev _ _ hn, hev _ _ hn]
    exact I'.isom n hn a b

end Abstract

noncomputable def precomp {S : Scheme.{0}} {T T' : Over S} (g : T' ⟶ T) (A : Over S) [GrpObj A] :
    (T ⟶ A) →* (T' ⟶ A) where
  toFun y := g ≫ y
  map_one' := MonObj.comp_one g
  map_mul' a b := MonObj.comp_mul g a b

/- English proof (translation)
Introduce `hL E _ _ _ H D S P act K Ω _ _ _ _ _ i x`. Take `⟨hinj, honto⟩` from `GlobalTheory.T.torsion_points_descend_field_extension hL S P K Ω i x`. Set `g : Over.mk (spMap i ≫ x) ⟶ Over.mk x` to `Over.homMk (spMap i) rfl`. Establish `honto' : ∀ n, 0 < n → ∀ z : Over.mk (spMap i ≫ x) ⟶ P.A, z ^ n = 1 → ∃ y : Over.mk x ⟶ P.A, y ^ n = 1 ∧ precomp g P.A y = z` using `fun n hn z hz => honto n z (Nat.cast_ne_zero.mpr hn.ne') hz`. Use `⟨fun I => up D i (precomp g P.A) hinj honto' (fun c y => (Category.assoc g y (act c)).symm) (fun n y y' c => GlobalTheory.T.weilPairing_fieldExtension_iff S P.A K Ω i x P.L n y y' c P.isAb P.isLB) I, fun I' hm => down D i (precomp g P.A) hinj honto' (fun c y => (Category.assoc g …` and prove the remaining obligations.

Use `haveI := hm c`. Conclude with `MonObj.one_comp (act c)`.
-/
theorem tateIso_fieldExt : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (S : Scheme.{0}) (P : Out.PolAV S) (act : 𝓞 E → (P.A ⟶ P.A)) (K Ω : Type) [Field K] [Field Ω] [IsAlgClosed K] [IsAlgClosed Ω] [CharZero K] (i : K →+* Ω) (x : Sp K ⟶ S), (∀ I : TateIso D K (Over.mk x ⟶ P.A) (fun c y => y ≫ act c) (fun n y y' c => Out.WeilIs P.A P.L n y y' (unitOn c)), ∃ I' : TateIso D Ω (Over.mk (spMap i ≫ x) ⟶ P.A) (fun c y => y ≫ act c) (fun n y y' c => Out.WeilIs P.A P.L n y y' (unitOn c)), ∀ n, 0 < n → (I'.ζ n : Ω) = i (I.ζ n) ∧ ∀ v, I'.ev n v = (Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ x) ⟶ Over.mk x) ≫ I.ev n v) ∧ ∀ I' : TateIso D Ω (Over.mk (spMap i ≫ x) ⟶ P.A) (fun c y => y ≫ act c) (fun n y y' c => Out.WeilIs P.A P.L n y y' (unitOn c)), (∀ c, IsMonHom (act c)) → ∃ I : TateIso D K (Over.mk x ⟶ P.A) (fun c y => y ≫ act c) (fun n y y' c => Out.WeilIs P.A P.L n y y' (unitOn c)), ∀ n, 0 < n → (I'.ζ n : Ω) = i (I.ζ n) ∧ ∀ v, I'.ev n v = (Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ x) ⟶ Over.mk x) ≫ I.ev n v := by
  intro hL E _ _ _ H D S P act K Ω _ _ _ _ _ i x
  obtain ⟨hinj, honto⟩ := GlobalTheory.T.torsion_points_descend_field_extension hL S P K Ω i x
  let g : Over.mk (spMap i ≫ x) ⟶ Over.mk x := Over.homMk (spMap i) rfl
  have honto' : ∀ n, 0 < n → ∀ z : Over.mk (spMap i ≫ x) ⟶ P.A, z ^ n = 1 →
      ∃ y : Over.mk x ⟶ P.A, y ^ n = 1 ∧ precomp g P.A y = z :=
    fun n hn z hz => honto n z (Nat.cast_ne_zero.mpr hn.ne') hz
  refine ⟨fun I => up D i (precomp g P.A) hinj honto' (fun c y => (Category.assoc g y (act c)).symm)
      (fun n y y' c => GlobalTheory.T.weilPairing_fieldExtension_iff S P.A K Ω i x P.L n y y' c P.isAb P.isLB) I,
    fun I' hm => down D i (precomp g P.A) hinj honto' (fun c y => (Category.assoc g y (act c)).symm)
      (fun c => ?_) (fun n y y' c => GlobalTheory.T.weilPairing_fieldExtension_iff S P.A K Ω i x P.L n y y' c P.isAb P.isLB) I'⟩
  haveI := hm c
  exact MonObj.one_comp (act c)

end GlobalTheory.TateIsoFieldExt
