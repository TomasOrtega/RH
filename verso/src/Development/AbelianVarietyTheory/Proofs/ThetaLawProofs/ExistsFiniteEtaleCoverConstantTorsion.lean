import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.AtOfNumberField
import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteEtaleLatticeTorsionHom
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushEquivSymmLeft
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CardTorsionPointsUnconditional

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

namespace GlobalTheory.TorsionCover

section Group

/- English proof (translation)
Establish `hH : Nat.card H = n ^ r`. Rewrite using `[← hc n dvd_rfl]`. Conclude with `(Nat.card_congr (Equiv.subtypeUnivEquiv hk)).symm`. Establish `hfin : Finite H` using `Nat.finite_of_card_ne_zero (by rw [hH]; exact pow_ne_zero _ hn)`. Introduce `s`.

Proceed by induction on `s with`. Consider the case `zero => exact fun _ => ⟨Fin.elim0, fun _ _ i => i.elim0⟩`. Consider the case `succ s ih`. Introduce `hs`. Take `⟨v, hv⟩` from `ih (by omega)`.

Set `ψ : Multiplicative (Fin s → ℤ) →* H` to `MonoidHom.mk' (fun c => ∏ i, v i ^ c.toAdd i) fun a b => by`. Simplify using `only [toAdd_mul, Pi.add_apply, zpow_add, Finset.prod_mul_distrib]`. Set `T` to `ψ.range`. Take `⟨q, hq⟩ : Monoid.exponent (H ⧸ T) ∣ n` from `Monoid.exponent_dvd_of_forall_pow_eq_one fun y => by`. Take `⟨x, rfl⟩` from `QuotientGroup.mk_surjective y`.

Rewrite using `[← QuotientGroup.mk_pow, hk, QuotientGroup.mk_one]`. Use `set m := Monoid.exponent (H ⧸ T) with hm`. Establish `hm0 : m ≠ 0` using `fun e => hn (by rw [hq, e, zero_mul])`. Establish `hq0 : q ≠ 0` using `fun e => hn (by rw [hq, e, mul_zero])`. Establish `hq1 : q = 1`.

Set `φ : H →* H` to `powMonoidHom m`. Establish `h1 : Nat.card φ.ker = m ^ r` using `hc m ⟨q, hq⟩`. Establish `h2 : Nat.card φ.range = q ^ r`. Use `Subgroup.card_mul_index φ.ker` as an intermediate fact. Rewrite `this` using `[Subgroup.index_ker, h1, hH, hq, mul_pow]`.

Conclude with `Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (pow_ne_zero _ hm0)) this`. Establish `: NeZero q` using `⟨hq0⟩`. Set `F : (Fin s → ZMod q) → φ.range` to `fun d => ⟨φ (∏ i, v i ^ (d i).val), _, rfl⟩`. Establish `hF : Function.Surjective F`. Introduce and unpack `⟨_, x, rfl⟩`.

Establish `hx : φ x ∈ T`. Rewrite using `[← QuotientGroup.eq_one_iff]`. Conclude with `(QuotientGroup.mk_pow T x m).trans (Monoid.pow_exponent_eq_one _)`. Take `⟨c, hc⟩` from `hx`. Establish `hc' : ∏ i, v i ^ c.toAdd i = x ^ m` using `hc`.

Establish `h3 : ∀ i, (m : ℤ) ∣ c.toAdd i` using `fun i => by`. Use `hv (fun i => c.toAdd i * q) (by` as an intermediate fact. Simplify using `only [zpow_mul, zpow_natCast]`. Rewrite using `[Finset.prod_pow, hc', ← pow_mul, ← hq, hk]) i`. Rewrite `this` using `[hq, Nat.cast_mul]`.

Conclude with `Int.dvd_of_mul_dvd_mul_right (by exact_mod_cast hq0) this`. Use `choose e he using h3`. Use `⟨fun i => (e i : ZMod q), Subtype.ext ?_⟩` and prove the remaining obligations. Use `show (∏ i, v i ^ ((e i : ZMod q)).val) ^ m = x ^ m`. Rewrite using `[← hc', ← Finset.prod_pow]`.

Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[he, zpow_mul, zpow_natCast, ← pow_mul, mul_comm, pow_mul, ← zpow_natCast, ZMod.val_intCast, ← zpow_eq_zpow_emod' _ (by rw [← pow_mul, ← hq, hk])]`. Establish `h4` using `Nat.card_le_card_of_surjective F hF`. Rewrite `h4` using `[h2, Nat.card_fun, Nat.card_zmod, Nat.card_fin]`. Assume the negation of the conclusion as `h5`.

Conclude with `absurd h4 (not_le.2 (Nat.pow_lt_pow_right (by omega) (by omega)))`. Rewrite `hq` using `[hq1, _root_.mul_one]`. Take `⟨y, hy⟩` from `Monoid.exists_orderOf_eq_exponent (G := H ⧸ T) Monoid.ExponentExists.of_finite`. Take `⟨x, rfl⟩` from `QuotientGroup.mk_surjective y`. Use `⟨Fin.cons x v, fun c h => ?_⟩` and prove the remaining obligations.

Rewrite `h` using `[Fin.prod_univ_succ]`. Simplify using `only [Fin.cons_zero, Fin.cons_succ] at h`. Establish `h0 : (n : ℤ) ∣ c 0`. Rewrite using `[hq, hm, ← hy, orderOf_dvd_iff_zpow_eq_one, ← QuotientGroup.mk_zpow, QuotientGroup.eq_one_iff, eq_inv_of_mul_eq_one_left h]`. Conclude with `T.inv_mem ⟨Multiplicative.ofAdd fun i => c i.succ, rfl⟩`.

Establish `h1 : x ^ c 0 = 1`. Take `⟨e, he⟩` from `h0`. Rewrite using `[he, zpow_mul, zpow_natCast, hk, one_zpow]`. Rewrite `h` using `[h1, _root_.one_mul]`. Conclude with `Fin.cases h0 (hv _ h)`.
-/
theorem exists_free_of_killed {H : Type} [CommGroup H] {n r : ℕ} (hn : n ≠ 0) (hk : ∀ x : H, x ^ n = 1)
    (hc : ∀ d, d ∣ n → Nat.card {x : H // x ^ d = 1} = d ^ r) :
    ∀ s, s ≤ r → ∃ v : Fin s → H, ∀ c : Fin s → ℤ, ∏ i, v i ^ c i = 1 → ∀ i, (n : ℤ) ∣ c i := by
  have hH : Nat.card H = n ^ r := by
    rw [← hc n dvd_rfl]
    exact (Nat.card_congr (Equiv.subtypeUnivEquiv hk)).symm
  have hfin : Finite H := Nat.finite_of_card_ne_zero (by rw [hH]; exact pow_ne_zero _ hn)
  intro s
  induction s with
  | zero => exact fun _ => ⟨Fin.elim0, fun _ _ i => i.elim0⟩
  | succ s ih =>
    intro hs
    obtain ⟨v, hv⟩ := ih (by omega)
    let ψ : Multiplicative (Fin s → ℤ) →* H := MonoidHom.mk' (fun c => ∏ i, v i ^ c.toAdd i) fun a b => by
      simp only [toAdd_mul, Pi.add_apply, zpow_add, Finset.prod_mul_distrib]
    let T := ψ.range
    obtain ⟨q, hq⟩ : Monoid.exponent (H ⧸ T) ∣ n := Monoid.exponent_dvd_of_forall_pow_eq_one fun y => by
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
      rw [← QuotientGroup.mk_pow, hk, QuotientGroup.mk_one]
    set m := Monoid.exponent (H ⧸ T) with hm
    have hm0 : m ≠ 0 := fun e => hn (by rw [hq, e, zero_mul])
    have hq0 : q ≠ 0 := fun e => hn (by rw [hq, e, mul_zero])
    have hq1 : q = 1 := by
      let φ : H →* H := powMonoidHom m
      have h1 : Nat.card φ.ker = m ^ r := hc m ⟨q, hq⟩
      have h2 : Nat.card φ.range = q ^ r := by
        have := Subgroup.card_mul_index φ.ker
        rw [Subgroup.index_ker, h1, hH, hq, mul_pow] at this
        exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (pow_ne_zero _ hm0)) this
      have : NeZero q := ⟨hq0⟩
      let F : (Fin s → ZMod q) → φ.range := fun d => ⟨φ (∏ i, v i ^ (d i).val), _, rfl⟩
      have hF : Function.Surjective F := by
        rintro ⟨_, x, rfl⟩
        have hx : φ x ∈ T := by
          rw [← QuotientGroup.eq_one_iff]
          exact (QuotientGroup.mk_pow T x m).trans (Monoid.pow_exponent_eq_one _)
        obtain ⟨c, hc⟩ := hx
        have hc' : ∏ i, v i ^ c.toAdd i = x ^ m := hc
        have h3 : ∀ i, (m : ℤ) ∣ c.toAdd i := fun i => by
          have := hv (fun i => c.toAdd i * q) (by
            simp only [zpow_mul, zpow_natCast]
            rw [Finset.prod_pow, hc', ← pow_mul, ← hq, hk]) i
          rw [hq, Nat.cast_mul] at this
          exact Int.dvd_of_mul_dvd_mul_right (by exact_mod_cast hq0) this
        choose e he using h3
        refine ⟨fun i => (e i : ZMod q), Subtype.ext ?_⟩
        show (∏ i, v i ^ ((e i : ZMod q)).val) ^ m = x ^ m
        rw [← hc', ← Finset.prod_pow]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [he, zpow_mul, zpow_natCast, ← pow_mul, mul_comm, pow_mul, ← zpow_natCast,
          ZMod.val_intCast, ← zpow_eq_zpow_emod' _ (by rw [← pow_mul, ← hq, hk])]
      have h4 := Nat.card_le_card_of_surjective F hF
      rw [h2, Nat.card_fun, Nat.card_zmod, Nat.card_fin] at h4
      by_contra h5
      exact absurd h4 (not_le.2 (Nat.pow_lt_pow_right (by omega) (by omega)))
    rw [hq1, _root_.mul_one] at hq
    obtain ⟨y, hy⟩ := Monoid.exists_orderOf_eq_exponent (G := H ⧸ T) Monoid.ExponentExists.of_finite
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    refine ⟨Fin.cons x v, fun c h => ?_⟩
    rw [Fin.prod_univ_succ] at h
    simp only [Fin.cons_zero, Fin.cons_succ] at h
    have h0 : (n : ℤ) ∣ c 0 := by
      rw [hq, hm, ← hy, orderOf_dvd_iff_zpow_eq_one, ← QuotientGroup.mk_zpow, QuotientGroup.eq_one_iff,
        eq_inv_of_mul_eq_one_left h]
      exact T.inv_mem ⟨Multiplicative.ofAdd fun i => c i.succ, rfl⟩
    have h1 : x ^ c 0 = 1 := by
      obtain ⟨e, he⟩ := h0
      rw [he, zpow_mul, zpow_natCast, hk, one_zpow]
    rw [h1, _root_.one_mul] at h
    exact Fin.cases h0 (hv _ h)

/- English proof (translation)
Establish `: NeZero n` using `⟨hn⟩`. Take `⟨v, hv⟩` from `exists_free_of_killed (H := (powMonoidHom n : G →* G).ker) (r := r) hn (fun x => Subtype.ext x.2) (fun d hd => by`. Rewrite using `[← hc d hd]`. Take `⟨e, he⟩` from `hd`. Use `Nat.card_congr ⟨fun x => ⟨x.1.1, congrArg Subtype.val x.2⟩, fun x => ⟨⟨x.1, ?_⟩, Subtype.ext x.2⟩, fun _ => rfl, fun _ => rfl⟩` and prove the remaining obligations.

Use `show x.1 ^ n = 1`. Rewrite using `[he, pow_mul, x.2, one_pow]) r le_rfl`. Use `⟨fun i => (v i).1, fun i => (v i).2, fun c h => funext fun i => ?_⟩` and prove the remaining obligations. Use `hv (fun i => ((c i).val : ℤ)) (Subtype.ext (by simpa [-ZMod.natCast_val] using h)) i` as an intermediate fact. Rewrite `this` using `[← ZMod.intCast_zmod_eq_zero_iff_dvd]`.

Simplify using `using this`.
-/
theorem exists_free {G : Type} [CommGroup G] {n r : ℕ} (hn : n ≠ 0)
    (hc : ∀ d, d ∣ n → Nat.card {x : G // x ^ d = 1} = d ^ r) :
    ∃ v : Fin r → G, (∀ i, v i ^ n = 1) ∧ ∀ c : Fin r → ZMod n, ∏ i, v i ^ (c i).val = 1 → c = 0 := by
  have : NeZero n := ⟨hn⟩
  obtain ⟨v, hv⟩ := exists_free_of_killed (H := (powMonoidHom n : G →* G).ker) (r := r) hn
    (fun x => Subtype.ext x.2) (fun d hd => by
      rw [← hc d hd]
      obtain ⟨e, he⟩ := hd
      refine Nat.card_congr ⟨fun x => ⟨x.1.1, congrArg Subtype.val x.2⟩, fun x => ⟨⟨x.1, ?_⟩, Subtype.ext x.2⟩,
        fun _ => rfl, fun _ => rfl⟩
      show x.1 ^ n = 1
      rw [he, pow_mul, x.2, one_pow]) r le_rfl
  refine ⟨fun i => (v i).1, fun i => (v i).2, fun c h => funext fun i => ?_⟩
  have := hv (fun i => ((c i).val : ℤ)) (Subtype.ext (by simpa [-ZMod.natCast_val] using h)) i
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at this
  simpa using this

def combHom {G : Type} [CommGroup G] {n r : ℕ} [NeZero n] (v : Fin r → G) (hv : ∀ i, v i ^ n = 1) :
    Multiplicative (Fin r → ZMod n) →* G :=
  MonoidHom.mk' (fun c => ∏ i, v i ^ (c.toAdd i).val) fun a b => by
    show ∏ i, v i ^ (a.toAdd i + b.toAdd i).val = _
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => by rw [ZMod.val_add, ← pow_eq_pow_mod _ (hv i), pow_add]

/- English proof (translation)
Rewrite using `[← map_pow]`. Establish `: c ^ n = 1` using `Multiplicative.toAdd.injective (by ext i; simp)`. Rewrite using `[this, map_one]`.
-/
theorem hom_pow_eq_one {G : Type} [Group G] {n r : ℕ} (j : Multiplicative (Fin r → ZMod n) →* G)
    (c : Multiplicative (Fin r → ZMod n)) : j c ^ n = 1 := by
  rw [← map_pow]
  have : c ^ n = 1 := Multiplicative.toAdd.injective (by ext i; simp)
  rw [this, map_one]

/- English proof (translation)
Use `⟨fun hx => ?_, fun ⟨c, e⟩ => e ▸ hom_pow_eq_one j c⟩` and prove the remaining obligations. Establish `: Finite {x : G // x ^ n = 1}` using `Nat.finite_of_card_ne_zero (by rw [hc]; exact pow_ne_zero _ (NeZero.ne n))`. Set `F : Multiplicative (Fin r → ZMod n) → {x : G // x ^ n = 1}` to `fun c => ⟨j c, hom_pow_eq_one j c⟩`. Establish `hF : Function.Injective F` using `fun a b e => (injective_iff_map_eq_one j).2 hj (congrArg Subtype.val e)`. Establish `hb` using `(Nat.bijective_iff_injective_and_card F).2 ⟨hF, by`.

Rewrite using `[hc, Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_fin]⟩`. Take `⟨c, e⟩` from `hb.2 ⟨x, hx⟩`. Conclude with `⟨c, (congrArg Subtype.val e).symm⟩`.
-/
theorem pow_eq_one_iff_of_card {G : Type} [Group G] {n r : ℕ} [NeZero n]
    (hc : Nat.card {x : G // x ^ n = 1} = n ^ r) (j : Multiplicative (Fin r → ZMod n) →* G)
    (hj : ∀ c, j c = 1 → c = 1) (x : G) : x ^ n = 1 ↔ ∃ c, x = j c := by
  refine ⟨fun hx => ?_, fun ⟨c, e⟩ => e ▸ hom_pow_eq_one j c⟩
  have : Finite {x : G // x ^ n = 1} :=
    Nat.finite_of_card_ne_zero (by rw [hc]; exact pow_ne_zero _ (NeZero.ne n))
  let F : Multiplicative (Fin r → ZMod n) → {x : G // x ^ n = 1} := fun c => ⟨j c, hom_pow_eq_one j c⟩
  have hF : Function.Injective F := fun a b e =>
    (injective_iff_map_eq_one j).2 hj (congrArg Subtype.val e)
  have hb := (Nat.bijective_iff_injective_and_card F).2 ⟨hF, by
    rw [hc, Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_fin]⟩
  obtain ⟨c, e⟩ := hb.2 ⟨x, hx⟩
  exact ⟨c, (congrArg Subtype.val e).symm⟩

end Group

section Geometry

variable {S : Scheme.{0}}

/- English proof (translation)
Use `(hn.map t.appTop.hom).map (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom` as an intermediate fact. Rewrite `this` using `[map_natCast, map_natCast]`. Conclude with `this.ne_zero`.
-/
theorem natCast_ne_zero {n : ℕ} (hn : IsUnit (n : Γ(S, ⊤))) {k : Type} [Field k] (t : Sp k ⟶ S) :
    (n : k) ≠ 0 := by
  have := (hn.map t.appTop.hom).map (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom
  rw [map_natCast, map_natCast] at this
  exact this.ne_zero

/- English proof (translation)
Establish `h` using `isGrpPullback_pullback A t`. Use `smoothOfRelativeDimension_isStableUnderBaseChange.{0} g` as an intermediate fact. Establish `key` using `GlobalTheory.UU.TorsionCount.card_torsion_points_unconditional k _ g n (GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA h) (MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension g) h.1 hg) hn`. Establish `e : (𝟙_ (Over (Sp k))).hom ≫ t = t` using `Category.id_comp t`. Rewrite using `[← e, ← key]`.

Set `Φ` to `GlobalTheory.ObjPull.pushEquiv h (𝟙_ (Over (Sp k)))`. Conclude with `(Nat.card_congr (Φ.toEquiv.subtypeEquiv fun x => by`. Rewrite using `[← map_eq_one_iff Φ Φ.injective, map_pow]`. Use the proof step `rfl)).symm`.
-/
theorem card_torsion (A : Over S) [GrpObj A] {g : ℕ} (hA : IsAbelianScheme A)
    (hg : SmoothOfRelativeDimension g A.hom) {k : Type} [Field k] [IsAlgClosed k] (t : Sp k ⟶ S) {n : ℕ}
    (hn : (n : k) ≠ 0) : Nat.card {x : Over.mk t ⟶ A // x ^ n = 1} = n ^ (2 * g) := by
  have h := isGrpPullback_pullback A t
  have := smoothOfRelativeDimension_isStableUnderBaseChange.{0} g
  have key := GlobalTheory.UU.TorsionCount.card_torsion_points_unconditional k _ g n
    (GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA h)
    (MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension g) h.1 hg) hn
  have e : (𝟙_ (Over (Sp k))).hom ≫ t = t := Category.id_comp t
  rw [← e, ← key]
  let Φ := GlobalTheory.ObjPull.pushEquiv h (𝟙_ (Over (Sp k)))
  exact (Nat.card_congr (Φ.toEquiv.subtypeEquiv fun x => by
    rw [← map_eq_one_iff Φ Φ.injective, map_pow]; rfl)).symm

/- English proof (translation)
Set `ρ : (T ⟶ A) →* (T' ⟶ A)` to `preHom f`. Conclude with `(map_prod ρ _ _).trans (Finset.prod_congr rfl fun i _ => map_pow ρ _ _)`.
-/
theorem comp_comb {A T T' : Over S} [GrpObj A] [IsCommMonObj A] (f : T' ⟶ T) {r : ℕ} (v : Fin r → (T ⟶ A))
    (a : Fin r → ℕ) : f ≫ ∏ i, v i ^ a i = ∏ i, (f ≫ v i) ^ a i := by
  let ρ : (T ⟶ A) →* (T' ⟶ A) := preHom f
  exact (map_prod ρ _ _).trans (Finset.prod_congr rfl fun i _ => map_pow ρ _ _)

/- English proof (translation)
Take `⟨-, hfin, het⟩` from `GrpTangent.finiteEtale_mulN_torsion A hn`. Take `⟨y, hy, -⟩` from `LatticeTorsion.existsUnique_torsion A n x hx`. Take `⟨y₁, hy₁, -⟩` from `LatticeTorsion.existsUnique_torsion A n (1 : Z ⟶ A) (one_pow n)`. Use `⟨Set.range (FinEt.agreeι y y₁), ⟨(FinEt.agreeι y y₁).isClosedEmbedding.isClosed_range, (FinEt.agreeι y y₁).isOpenEmbedding.isOpen_range⟩, fun T z => ?_⟩` and prove the remaining obligations. Rewrite using `[← FinEt.comp_eq_comp_iff_range]`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `(LatticeTorsion.existsUnique_torsion A n (1 : T ⟶ A) (one_pow n)).unique (y₁ := z ≫ y) (y₂ := z ≫ y₁) (by rw [Category.assoc, hy, h]) (by rw [Category.assoc, hy₁, MonObj.comp_one])` as an intermediate fact. Conclude with `congr(($this).left)`. Introduce `h`.

Establish `: z ≫ y = z ≫ y₁` using `Over.OverMorphism.ext h`. Rewrite using `[← hy, ← Category.assoc, this, Category.assoc, hy₁, MonObj.comp_one]`.
-/
theorem exists_clopen_eq_one (A : Over S) [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A) {n : ℕ}
    (hn : IsUnit (n : Γ(S, ⊤))) {Z : Over S} (x : Z ⟶ A) (hx : x ^ n = 1) :
    ∃ C : Set Z.left, IsClopen C ∧ ∀ (T : Over S) (z : T ⟶ Z), z ≫ x = 1 ↔ Set.range z.left ⊆ C := by
  obtain ⟨-, hfin, het⟩ := GrpTangent.finiteEtale_mulN_torsion A hn
  obtain ⟨y, hy, -⟩ := LatticeTorsion.existsUnique_torsion A n x hx
  obtain ⟨y₁, hy₁, -⟩ := LatticeTorsion.existsUnique_torsion A n (1 : Z ⟶ A) (one_pow n)
  refine ⟨Set.range (FinEt.agreeι y y₁), ⟨(FinEt.agreeι y y₁).isClosedEmbedding.isClosed_range,
    (FinEt.agreeι y y₁).isOpenEmbedding.isOpen_range⟩, fun T z => ?_⟩
  rw [← FinEt.comp_eq_comp_iff_range]
  constructor
  · intro h
    have := (LatticeTorsion.existsUnique_torsion A n (1 : T ⟶ A) (one_pow n)).unique
      (y₁ := z ≫ y) (y₂ := z ≫ y₁) (by rw [Category.assoc, hy, h])
      (by rw [Category.assoc, hy₁, MonObj.comp_one])
    exact congr(($this).left)
  · intro h
    have : z ≫ y = z ≫ y₁ := Over.OverMorphism.ext h
    rw [← hy, ← Category.assoc, this, Category.assoc, hy₁, MonObj.comp_one]

/- English proof (translation)
Take `⟨-, hfin, het⟩` from `GrpTangent.finiteEtale_mulN_torsion A hn`. Set `Z` to `Out.powObj (torsion A n) (2 * g)`. Establish `hZ₁ : IsFinite Z.hom` using `LatticeTorsion.prop_powObj @IsFinite _ hfin _`. Establish `hZ₂ : Etale Z.hom` using `LatticeTorsion.prop_powObj @Etale _ het _`. Set `x : Fin (2 * g) → (Z ⟶ A)` to `fun i => Out.powPr (torsion A n) i ≫ torsion.ι A n`.

Establish `hx : ∀ i, x i ^ n = 1` using `fun i => by`. Rewrite using `[← MonObj.comp_pow, LatticeTorsion.torsionι_pow_eq_one, MonObj.comp_one]`. Set `j₀` to `combHom x hx`. Use `choose C hC hCz using fun c => exists_clopen_eq_one A hA hn (j₀ c) (hom_pow_eq_one j₀ c)`. Establish `hU : IsClopen (⋂ c, ⋂ _ : c ≠ 1, (C c)ᶜ)` using `isClopen_iInter_of_finite fun c => isClopen_iInter_of_finite fun _ => (hC c).compl`.

Set `U : Z.left.Opens` to `⟨_, hU.isOpen⟩`. Establish `: IsClosedImmersion U.ι` using `.of_isPreimmersion _ (by`. Rewrite using `[Scheme.Opens.range_ι]`. Conclude with `hU.isClosed)`. Set `u : Over.mk (U.ι ≫ Z.hom) ⟶ Z` to `Over.homMk U.ι rfl`.

Use `⟨Over.mk (U.ι ≫ Z.hom), (preHom u).comp j₀, inferInstanceAs (IsFinite (U.ι ≫ Z.hom)), inferInstanceAs (Etale (U.ι ≫ Z.hom)), ⟨fun s => ?_⟩, fun T z ⟨p⟩ c hc => ?_⟩` and prove the remaining obligations. Set `k` to `AlgebraicClosure (S.residueField s)`. Set `t : Sp k ⟶ S` to `spMap (algebraMap (S.residueField s) k) ≫ S.fromSpecResidueField s`. Take `⟨v, hv, hfree⟩` from `exists_free (G := Over.mk t ⟶ A) (r := 2 * g) (NeZero.ne n) fun d hd => card_torsion A hA hg t (by`. Take `⟨e, he⟩` from `hd`.

Use `natCast_ne_zero hn t` as an intermediate fact. Rewrite `this` using `[he, Nat.cast_mul]`. Conclude with `left_ne_zero_of_mul this)`. Use `choose y hy _ using fun i => LatticeTorsion.existsUnique_torsion A n (v i) (hv i)`. Set `h : Over.mk t ⟶ Z` to `(Out.powIsLimit (torsion A n) (2 * g)).lift (Fan.mk _ y)`.

Establish `hh : ∀ i, h ≫ x i = v i` using `fun i => by`. Establish `: h ≫ Out.powPr (torsion A n) i = y i` using `(Out.powIsLimit (torsion A n) (2 * g)).fac (Fan.mk _ y) ⟨i⟩`. Rewrite using `[← hy i, ← this]`. Conclude with `(Category.assoc _ _ _).symm`. Take `⟨w⟩ : Nonempty (Sp k)` from `inferInstance`.

Establish `hw : h.left w ∈ U` using `Set.mem_iInter.2 fun c => Set.mem_iInter.2 fun hc hm => hc <| by`. Establish `h1 : h ≫ j₀ c = 1` using `(hCz c _ h).2 (by`. Introduce and unpack `_ ⟨w', rfl⟩`. Rewrite using `[Subsingleton.elim (α := Sp k) w' w])` and apply the resulting hypothesis. Establish `h2` using `(comp_comb h x _).symm.trans h1`.

Simplify using `only [hh] at h2`. Conclude with `Multiplicative.toAdd.injective (hfree _ h2)`. Use `⟨⟨h.left w, hw⟩, ?_⟩` and prove the remaining obligations. Establish `h3 : t w = s`. Establish `: t w ∈ Set.range (S.fromSpecResidueField s)` using `⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩`.

Rewrite `this` using `[Scheme.range_fromSpecResidueField]`. Then use the resulting hypothesis. Use `Eq.trans ?_ h3` and prove the remaining obligations. Establish `h4 : h.left ≫ Z.hom = t` using `Over.w h`. Conclude with `(Scheme.Hom.comp_apply U.ι Z.hom _).trans ((Scheme.Hom.comp_apply h.left Z.hom w).symm.trans (congrArg (fun f : Sp k ⟶ S => f w) h4))`. Assume the negation of the conclusion as `h1`.

Establish `h2` using `(hCz c T (z ≫ u)).1 ((Category.assoc _ _ _).trans hc) ⟨p, rfl⟩`. Establish `h3 : (z ≫ u).left p ∈ U`. Establish `: (z ≫ u).left p ∈ Set.range U.ι` using `⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩`. Rewrite `this` using `[Scheme.Opens.range_ι]`. Then use the resulting hypothesis. Conclude with `Set.mem_iInter.1 (Set.mem_iInter.1 h3 c) h1 h2`.
-/
theorem exists_cover (A : Over S) [GrpObj A] [IsCommMonObj A] {g n : ℕ} [NeZero n] (hA : IsAbelianScheme A)
    (hg : SmoothOfRelativeDimension g A.hom) (hn : IsUnit (n : Γ(S, ⊤))) :
    ∃ (W : Over S) (j : Multiplicative (Fin (2 * g) → ZMod n) →* (W ⟶ A)),
      IsFinite W.hom ∧ Etale W.hom ∧ Surjective W.hom ∧
      ∀ (T : Over S) (z : T ⟶ W), Nonempty T.left → ∀ c, z ≫ j c = 1 → c = 1 := by
  obtain ⟨-, hfin, het⟩ := GrpTangent.finiteEtale_mulN_torsion A hn
  let Z := Out.powObj (torsion A n) (2 * g)
  have hZ₁ : IsFinite Z.hom := LatticeTorsion.prop_powObj @IsFinite _ hfin _
  have hZ₂ : Etale Z.hom := LatticeTorsion.prop_powObj @Etale _ het _
  let x : Fin (2 * g) → (Z ⟶ A) := fun i => Out.powPr (torsion A n) i ≫ torsion.ι A n
  have hx : ∀ i, x i ^ n = 1 := fun i => by
    rw [← MonObj.comp_pow, LatticeTorsion.torsionι_pow_eq_one, MonObj.comp_one]
  let j₀ := combHom x hx
  choose C hC hCz using fun c => exists_clopen_eq_one A hA hn (j₀ c) (hom_pow_eq_one j₀ c)
  have hU : IsClopen (⋂ c, ⋂ _ : c ≠ 1, (C c)ᶜ) :=
    isClopen_iInter_of_finite fun c => isClopen_iInter_of_finite fun _ => (hC c).compl
  let U : Z.left.Opens := ⟨_, hU.isOpen⟩
  have : IsClosedImmersion U.ι := .of_isPreimmersion _ (by
    rw [Scheme.Opens.range_ι]; exact hU.isClosed)
  let u : Over.mk (U.ι ≫ Z.hom) ⟶ Z := Over.homMk U.ι rfl
  refine ⟨Over.mk (U.ι ≫ Z.hom), (preHom u).comp j₀, inferInstanceAs (IsFinite (U.ι ≫ Z.hom)),
    inferInstanceAs (Etale (U.ι ≫ Z.hom)), ⟨fun s => ?_⟩, fun T z ⟨p⟩ c hc => ?_⟩
  · let k := AlgebraicClosure (S.residueField s)
    let t : Sp k ⟶ S := spMap (algebraMap (S.residueField s) k) ≫ S.fromSpecResidueField s
    obtain ⟨v, hv, hfree⟩ := exists_free (G := Over.mk t ⟶ A) (r := 2 * g) (NeZero.ne n) fun d hd =>
      card_torsion A hA hg t (by
        obtain ⟨e, he⟩ := hd
        have := natCast_ne_zero hn t
        rw [he, Nat.cast_mul] at this
        exact left_ne_zero_of_mul this)
    choose y hy _ using fun i => LatticeTorsion.existsUnique_torsion A n (v i) (hv i)
    let h : Over.mk t ⟶ Z := (Out.powIsLimit (torsion A n) (2 * g)).lift (Fan.mk _ y)
    have hh : ∀ i, h ≫ x i = v i := fun i => by
      have : h ≫ Out.powPr (torsion A n) i = y i :=
        (Out.powIsLimit (torsion A n) (2 * g)).fac (Fan.mk _ y) ⟨i⟩
      rw [← hy i, ← this]
      exact (Category.assoc _ _ _).symm
    obtain ⟨w⟩ : Nonempty (Sp k) := inferInstance
    have hw : h.left w ∈ U := Set.mem_iInter.2 fun c => Set.mem_iInter.2 fun hc hm => hc <| by
      have h1 : h ≫ j₀ c = 1 := (hCz c _ h).2 (by
        rintro _ ⟨w', rfl⟩
        rwa [Subsingleton.elim (α := Sp k) w' w])
      have h2 := (comp_comb h x _).symm.trans h1
      simp only [hh] at h2
      exact Multiplicative.toAdd.injective (hfree _ h2)
    refine ⟨⟨h.left w, hw⟩, ?_⟩
    have h3 : t w = s := by
      have : t w ∈ Set.range (S.fromSpecResidueField s) := ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩
      rwa [Scheme.range_fromSpecResidueField] at this
    refine Eq.trans ?_ h3
    have h4 : h.left ≫ Z.hom = t := Over.w h
    exact (Scheme.Hom.comp_apply U.ι Z.hom _).trans ((Scheme.Hom.comp_apply h.left Z.hom w).symm.trans
      (congrArg (fun f : Sp k ⟶ S => f w) h4))
  · by_contra h1
    have h2 := (hCz c T (z ≫ u)).1 ((Category.assoc _ _ _).trans hc) ⟨p, rfl⟩
    have h3 : (z ≫ u).left p ∈ U := by
      have : (z ≫ u).left p ∈ Set.range U.ι := ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩
      rwa [Scheme.Opens.range_ι] at this
    exact Set.mem_iInter.1 (Set.mem_iInter.1 h3 c) h1 h2

/- English proof (translation)
Establish `: IsAffine W` using `isAffine_of_isAffineHom π`. Take `⟨φ, hφ⟩` from `Spec.map_surjective (W.isoSpec.inv ≫ π)`. Use `letI := φ.hom.toAlgebra`. Establish `h1 : IsFinite (Spec.map φ)` using `by rw [hφ]; infer_instance`. Establish `h2 : Etale (Spec.map φ)` using `by rw [hφ]; infer_instance`.

Establish `h3 : Surjective (Spec.map φ)` using `by rw [hφ]; infer_instance`. Establish `h4 : Algebra.Etale R Γ(W, ⊤)` using `RingHom.etale_algebraMap.1 ((HasRingHomProperty.Spec_iff (P := @Etale)).1 h2)`. Conclude with `⟨Γ(W, ⊤), inferInstance, inferInstance, W.isoSpec.inv, ⟨(IsFinite.SpecMap_iff φ).1 h1, h4, .of_comap_surjective h3.surj⟩, hφ.symm⟩`.
-/
theorem exists_algebra {R : Type} [CommRing R] {W : Scheme.{0}} (π : W ⟶ Sp R) [IsFinite π] [Etale π]
    [Surjective π] : ∃ (R₁ : Type) (_ : CommRing R₁) (_ : Algebra R R₁) (e : Sp R₁ ⟶ W),
      (Module.Finite R R₁ ∧ Algebra.Etale R R₁ ∧ Module.FaithfullyFlat R R₁) ∧
      e ≫ π = spMap (algebraMap R R₁) := by
  have : IsAffine W := isAffine_of_isAffineHom π
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (W.isoSpec.inv ≫ π)
  letI := φ.hom.toAlgebra
  have h1 : IsFinite (Spec.map φ) := by rw [hφ]; infer_instance
  have h2 : Etale (Spec.map φ) := by rw [hφ]; infer_instance
  have h3 : Surjective (Spec.map φ) := by rw [hφ]; infer_instance
  have h4 : Algebra.Etale R Γ(W, ⊤) :=
    RingHom.etale_algebraMap.1 ((HasRingHomProperty.Spec_iff (P := @Etale)).1 h2)
  exact ⟨Γ(W, ⊤), inferInstance, inferInstance, W.isoSpec.inv,
    ⟨(IsFinite.SpecMap_iff φ).1 h1, h4, .of_comap_surjective h3.surj⟩, hφ.symm⟩

end Geometry

/- English proof (translation)
Introduce `R _ _ A _ g n hA hg hn`. Use `hA.comm` as an intermediate fact. Break down `eq_or_ne n 0 with rfl | hn0` into its components or cases. Establish `: Subsingleton R` using `subsingleton_of_zero_eq_one (isUnit_zero_iff.1 (by simpa using hn))`. Use `⟨R, inferInstance, inferInstance, ⟨inferInstance, inferInstance, inferInstance⟩, fun A₁ _ _ φ _ => ⟨1, fun k _ _ t => ?_⟩⟩` and prove the remaining obligations.

Take `⟨w⟩ : Nonempty (Sp k)` from `inferInstance`. Conclude with `absurd (Subsingleton.elim _ _) (t w : PrimeSpectrum R).2.ne_top`. Establish `: NeZero n` using `⟨hn0⟩`. Establish `hn' : IsUnit (n : Γ(Sp R, ⊤))`. Use `hn.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom` as an intermediate fact.

Rewrite `this` using `[map_natCast]`. Then use the resulting hypothesis. Take `⟨W, j, h1, h2, h3, hj⟩` from `exists_cover A hA hg hn'`. Take `⟨R₁, _, _, e, hR, he⟩` from `exists_algebra W.hom`. Use `⟨R₁, inferInstance, inferInstance, hR, fun A₁ _ _ φ h => ?_⟩` and prove the remaining obligations. Set `u : ∀ T : Over (Sp R₁), Over.mk (T.hom ≫ spMap (algebraMap R R₁)) ⟶ W` to `fun T => Over.homMk (T.hom ≫ e) ((Category.assoc _ _ _).trans (congrArg (T.hom ≫ ·) he))`.

Set `i` to `(GlobalTheory.ObjPull.pushEquiv h (𝟙_ _)).symm.toMonoidHom.comp ((preHom (u _)).comp j)`. Establish `hi : ∀ (T : Over (Sp R₁)) c, GlobalTheory.ObjPull.pushEquiv h T (toUnit T ≫ i c) = u T ≫ j c` using `fun T c => by`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Establish `: (i c).left ≫ φ = (u (𝟙_ _) ≫ j c).left` using `GlobalTheory.ObjPull.pushEquiv_symm_left h _ _`. Rewrite using `[GlobalTheory.ObjPull.pushEquiv_left, Over.comp_left, Category.assoc, this, GlobalTheory.ObjPull.toUnit_left']`.

Use `show T.hom ≫ (𝟙 _ ≫ e) ≫ _ = (T.hom ≫ e) ≫ _`. Rewrite using `[Category.id_comp, Category.assoc]`. Use `⟨i, fun k _ _ t => ?_⟩` and prove the remaining obligations. Set `Φ` to `GlobalTheory.ObjPull.pushEquiv h (Over.mk t)`. Establish `hinj : ∀ c, toUnit (Over.mk t) ≫ i c = 1 → c = 1` using `fun c hc => hj _ (u (Over.mk t)) (inferInstanceAs (Nonempty (Sp k))) c (by rw [← hi, hc, map_one])`.

Use `⟨pow_eq_one_iff_of_card (r := 2 * g) ?_ ((preHom (toUnit _)).comp i) hinj, hinj⟩` and prove the remaining obligations. Rewrite using `[← card_torsion A hA hg (t ≫ spMap (algebraMap R R₁)) (natCast_ne_zero hn' (t ≫ spMap (algebraMap R R₁)))]`. Conclude with `Nat.card_congr (Φ.toEquiv.subtypeEquiv fun x => by`. Rewrite using `[← map_eq_one_iff Φ Φ.injective, map_pow]`. Use the proof step `rfl)`.
-/
theorem exists_torsion_basis_cover : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (g n : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → IsUnit (n : R) → ∃ (R₁ : Type) (_ : CommRing R₁) (_ : Algebra R R₁), (Module.Finite R R₁ ∧ Algebra.Etale R R₁ ∧ Module.FaithfullyFlat R R₁) ∧ ∀ (A₁ : Over (Sp R₁)) [GrpObj A₁] [IsCommMonObj A₁] (φ : A₁.left ⟶ A.left), IsGrpPullback A₁ A (spMap (algebraMap R R₁)) φ → ∃ i : Multiplicative (Fin (2 * g) → ZMod n) →* (𝟙_ (Over (Sp R₁)) ⟶ A₁), (∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R₁), (∀ x : Over.mk t ⟶ A₁, x ^ n = 1 ↔ ∃ c, x = toUnit _ ≫ i c) ∧ ∀ c, toUnit (Over.mk t) ≫ i c = 1 → c = 1) := by
  intro R _ _ A _ g n hA hg hn
  have := hA.comm
  rcases eq_or_ne n 0 with rfl | hn0
  · have : Subsingleton R := subsingleton_of_zero_eq_one (isUnit_zero_iff.1 (by simpa using hn))
    refine ⟨R, inferInstance, inferInstance, ⟨inferInstance, inferInstance, inferInstance⟩,
      fun A₁ _ _ φ _ => ⟨1, fun k _ _ t => ?_⟩⟩
    obtain ⟨w⟩ : Nonempty (Sp k) := inferInstance
    exact absurd (Subsingleton.elim _ _) (t w : PrimeSpectrum R).2.ne_top
  have : NeZero n := ⟨hn0⟩
  have hn' : IsUnit (n : Γ(Sp R, ⊤)) := by
    have := hn.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    rwa [map_natCast] at this
  obtain ⟨W, j, h1, h2, h3, hj⟩ := exists_cover A hA hg hn'
  obtain ⟨R₁, _, _, e, hR, he⟩ := exists_algebra W.hom
  refine ⟨R₁, inferInstance, inferInstance, hR, fun A₁ _ _ φ h => ?_⟩
  let u : ∀ T : Over (Sp R₁), Over.mk (T.hom ≫ spMap (algebraMap R R₁)) ⟶ W := fun T =>
    Over.homMk (T.hom ≫ e) ((Category.assoc _ _ _).trans (congrArg (T.hom ≫ ·) he))
  let i := (GlobalTheory.ObjPull.pushEquiv h (𝟙_ _)).symm.toMonoidHom.comp ((preHom (u _)).comp j)
  have hi : ∀ (T : Over (Sp R₁)) c, GlobalTheory.ObjPull.pushEquiv h T (toUnit T ≫ i c) = u T ≫ j c := fun T c => by
    apply Over.OverMorphism.ext
    have : (i c).left ≫ φ = (u (𝟙_ _) ≫ j c).left := GlobalTheory.ObjPull.pushEquiv_symm_left h _ _
    rw [GlobalTheory.ObjPull.pushEquiv_left, Over.comp_left, Category.assoc, this, GlobalTheory.ObjPull.toUnit_left']
    show T.hom ≫ (𝟙 _ ≫ e) ≫ _ = (T.hom ≫ e) ≫ _
    rw [Category.id_comp, Category.assoc]
  refine ⟨i, fun k _ _ t => ?_⟩
  let Φ := GlobalTheory.ObjPull.pushEquiv h (Over.mk t)
  have hinj : ∀ c, toUnit (Over.mk t) ≫ i c = 1 → c = 1 := fun c hc =>
    hj _ (u (Over.mk t)) (inferInstanceAs (Nonempty (Sp k))) c (by rw [← hi, hc, map_one])
  refine ⟨pow_eq_one_iff_of_card (r := 2 * g) ?_ ((preHom (toUnit _)).comp i) hinj, hinj⟩
  rw [← card_torsion A hA hg (t ≫ spMap (algebraMap R R₁)) (natCast_ne_zero hn' (t ≫ spMap (algebraMap R R₁)))]
  exact Nat.card_congr (Φ.toEquiv.subtypeEquiv fun x => by
    rw [← map_eq_one_iff Φ Φ.injective, map_pow]; rfl)

end GlobalTheory.TorsionCover
