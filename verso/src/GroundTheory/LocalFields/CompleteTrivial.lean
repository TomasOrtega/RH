import Mathlib
import GroundTheory.LocalFields.FilteredSurj

namespace GroundTheory.LocalField

open Finset Filter

section Tate

variable (G M : Type*) [Group G] [Fintype G] [CommGroup M] [MulDistribMulAction G M]

def tateNorm : M →* M where
  toFun x := ∏ g : G, g • x
  map_one' := by simp
  map_mul' x y := by simp only [smul_mul', prod_mul_distrib]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem tateNorm_apply (x : M) : tateNorm G M x = ∏ g : G, g • x := rfl

def invariants : Subgroup M where
  carrier := {x | ∀ g : G, g • x = x}
  one_mem' g := smul_one g
  mul_mem' {x y} hx hy g := by rw [smul_mul', hx g, hy g]
  inv_mem' {x} hx g := by rw [smul_inv', hx g]

omit [Fintype G] in
/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_invariants {x : M} : x ∈ invariants G M ↔ ∀ g : G, g • x = x := Iff.rfl

def augmentation : Subgroup M :=
  Subgroup.closure {y | ∃ (g : G) (x : M), g • x / x = y}

abbrev TateZero : Type _ :=
  invariants G M ⧸ (tateNorm G M).range.subgroupOf (invariants G M)

abbrev TateNegOne : Type _ :=
  (tateNorm G M).ker ⧸ (augmentation G M).subgroupOf (tateNorm G M).ker

def augMap : (G → M) →* M where
  toFun m := ∏ g : G, g • m g / m g
  map_one' := by simp
  map_mul' m m' := by
    simp only [Pi.mul_apply, smul_mul', ← prod_mul_distrib, div_mul_div_comm]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem augMap_apply (m : G → M) : augMap G M m = ∏ g : G, g • m g / m g := rfl

variable {G M}

/- English proof (translation)
Rewrite using `[tateNorm_apply, Finset.smul_prod']`. Repeatedly rewrite using `[smul_smul]`. Conclude with `Fintype.prod_equiv (Equiv.mulLeft g) _ _ (fun _ => rfl)`.
-/
theorem smul_tateNorm (g : G) (x : M) : g • tateNorm G M x = tateNorm G M x := by
  rw [tateNorm_apply, Finset.smul_prod']
  simp_rw [smul_smul]
  exact Fintype.prod_equiv (Equiv.mulLeft g) _ _ (fun _ => rfl)

/- English proof (translation)
Repeatedly rewrite using `[tateNorm_apply, smul_smul]`. Conclude with `Fintype.prod_equiv (Equiv.mulRight g) _ _ (fun _ => rfl)`.
-/
theorem tateNorm_smul (g : G) (x : M) : tateNorm G M (g • x) = tateNorm G M x := by
  simp_rw [tateNorm_apply, smul_smul]
  exact Fintype.prod_equiv (Equiv.mulRight g) _ _ (fun _ => rfl)

/- English proof (translation)
Introduce `g` and use `smul_tateNorm g x`.
-/
theorem tateNorm_mem_invariants (x : M) : tateNorm G M x ∈ invariants G M :=
  fun g => smul_tateNorm g x

/- English proof (translation)
Rewrite using `[augMap_apply, map_prod]`. Use `prod_eq_one fun g _ => ?_` and prove the remaining obligations. Rewrite using `[map_div, tateNorm_smul, div_self']`.
-/
theorem tateNorm_augMap (m : G → M) : tateNorm G M (augMap G M m) = 1 := by
  rw [augMap_apply, map_prod]
  refine prod_eq_one fun g _ => ?_
  rw [map_div, tateNorm_smul, div_self']

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[augmentation, Subgroup.closure_le]`. Introduce and unpack `_ ⟨g, x, rfl⟩`. Use `⟨Pi.mulSingle g x, ?_⟩` and prove the remaining obligations. Rewrite using `[augMap_apply, Fintype.prod_eq_single g (fun h hh => by simp [Pi.mulSingle_eq_of_ne hh])]`.

Simplify using the standard rewrite rules. Introduce and unpack `_ ⟨m, rfl⟩`. Conclude with `Subgroup.prod_mem _ fun g _ => Subgroup.subset_closure ⟨g, m g, rfl⟩`.
-/
theorem augmentation_eq_range : augmentation G M = (augMap G M).range := by
  classical
  apply le_antisymm
  · rw [augmentation, Subgroup.closure_le]
    rintro _ ⟨g, x, rfl⟩
    refine ⟨Pi.mulSingle g x, ?_⟩
    rw [augMap_apply, Fintype.prod_eq_single g (fun h hh => by simp [Pi.mulSingle_eq_of_ne hh])]
    simp
  · rintro _ ⟨m, rfl⟩
    exact Subgroup.prod_mem _ fun g _ => Subgroup.subset_closure ⟨g, m g, rfl⟩

/- English proof (translation)
Rewrite using `[QuotientGroup.subsingleton_iff, Subgroup.subgroupOf_eq_top]`. Conclude with `⟨fun h x hx => h hx, fun h x hx => h x hx⟩`.
-/
theorem subsingleton_tateZero_iff :
    Subsingleton (TateZero G M) ↔ ∀ x : M, (∀ g : G, g • x = x) → ∃ y, tateNorm G M y = x := by
  rw [QuotientGroup.subsingleton_iff, Subgroup.subgroupOf_eq_top]
  exact ⟨fun h x hx => h hx, fun h x hx => h x hx⟩

/- English proof (translation)
Rewrite using `[QuotientGroup.subsingleton_iff, Subgroup.subgroupOf_eq_top]`. Conclude with `⟨fun h x hx => h hx, fun h x hx => h x hx⟩`.
-/
theorem subsingleton_tateNegOne_iff :
    Subsingleton (TateNegOne G M) ↔ ∀ x : M, tateNorm G M x = 1 → x ∈ augmentation G M := by
  rw [QuotientGroup.subsingleton_iff, Subgroup.subgroupOf_eq_top]
  exact ⟨fun h x hx => h hx, fun h x hx => h x hx⟩

end Tate

section Filtration

structure StableFiltration (G V : Type*) [Group G] [CommGroup V] [MulDistribMulAction G V] where

  F : ℕ → Subgroup V

  antitone : Antitone F

  smul_mem : ∀ (n : ℕ) (g : G) {x : V}, x ∈ F n → g • x ∈ F n

namespace StableFiltration

variable {G V : Type*} [Group G] [CommGroup V] [MulDistribMulAction G V]
  (S : StableFiltration G V)

instance instMulDistribMulActionF (n : ℕ) : MulDistribMulAction G (S.F n) where
  smul g x := ⟨g • (x : V), S.smul_mem n g x.2⟩
  one_smul x := Subtype.ext (one_smul G (x : V))
  mul_smul g h x := Subtype.ext (mul_smul g h (x : V))
  smul_mul g x y := Subtype.ext (smul_mul' g (x : V) y)
  smul_one g := Subtype.ext (smul_one g)

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_smul_F {n : ℕ} (g : G) (x : S.F n) : ((g • x : S.F n) : V) = g • (x : V) := rfl

def gr (n : ℕ) : Type _ := S.F n ⧸ (S.F (n + 1)).subgroupOf (S.F n)

instance instCommGroupGr (n : ℕ) : CommGroup (S.gr n) :=
  QuotientGroup.Quotient.commGroup _

def grMk (n : ℕ) : S.F n →* S.gr n := QuotientGroup.mk' _

/- English proof (translation)
The claim follows from `QuotientGroup.mk'_surjective _`.
-/
theorem grMk_surjective (n : ℕ) : Function.Surjective (S.grMk n) :=
  QuotientGroup.mk'_surjective _

/- English proof (translation)
The claim follows from `(QuotientGroup.eq_one_iff x).trans Subgroup.mem_subgroupOf`.
-/
theorem grMk_eq_one_iff {n : ℕ} (x : S.F n) : S.grMk n x = 1 ↔ (x : V) ∈ S.F (n + 1) :=
  (QuotientGroup.eq_one_iff x).trans Subgroup.mem_subgroupOf

/- English proof (translation)
Rewrite using `[← div_eq_one, ← map_div, grMk_eq_one_iff]`. Both sides reduce to the same expression.
-/
theorem grMk_eq_grMk_iff {n : ℕ} (x y : S.F n) :
    S.grMk n x = S.grMk n y ↔ (x : V) / y ∈ S.F (n + 1) := by
  rw [← div_eq_one, ← map_div, grMk_eq_one_iff]
  rfl

def grAct (n : ℕ) (g : G) : S.gr n →* S.gr n :=
  QuotientGroup.map _ _ (MulDistribMulAction.toMonoidHom (S.F n) g) fun x hx => by
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf] at *
    exact S.smul_mem (n + 1) g hx

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem grAct_grMk {n : ℕ} (g : G) (x : S.F n) : S.grAct n g (S.grMk n x) = S.grMk n (g • x) :=
  rfl

instance instMulDistribMulActionGr (n : ℕ) : MulDistribMulAction G (S.gr n) where
  smul g q := S.grAct n g q
  one_smul q := by
    obtain ⟨x, rfl⟩ := S.grMk_surjective n q
    exact (S.grAct_grMk 1 x).trans (congrArg _ (one_smul G x))
  mul_smul g h q := by
    obtain ⟨x, rfl⟩ := S.grMk_surjective n q
    change S.grAct n (g * h) (S.grMk n x) = S.grAct n g (S.grAct n h (S.grMk n x))
    rw [grAct_grMk, grAct_grMk, grAct_grMk, mul_smul]
  smul_mul g q r := map_mul (S.grAct n g) q r
  smul_one g := map_one (S.grAct n g)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem smul_grMk {n : ℕ} (g : G) (x : S.F n) : g • S.grMk n x = S.grMk n (g • x) := rfl

variable [Fintype G]

/- English proof (translation)
Rewrite using `[tateNorm_apply, tateNorm_apply, SubmonoidClass.coe_finsetProd]`. Both sides reduce to the same expression.
-/
theorem coe_tateNorm_F {n : ℕ} (x : S.F n) : ((tateNorm G (S.F n) x : S.F n) : V) = tateNorm G V x := by
  rw [tateNorm_apply, tateNorm_apply, SubmonoidClass.coe_finsetProd]
  rfl

/- English proof (translation)
Rewrite using `[augMap_apply, augMap_apply, SubmonoidClass.coe_finsetProd]`. Both sides reduce to the same expression.
-/
theorem coe_augMap_F {n : ℕ} (m : G → S.F n) :
    ((augMap G (S.F n) m : S.F n) : V) = augMap G V (fun g => (m g : V)) := by
  rw [augMap_apply, augMap_apply, SubmonoidClass.coe_finsetProd]
  rfl

/- English proof (translation)
Rewrite using `[tateNorm_apply, tateNorm_apply, map_prod]`. Both sides reduce to the same expression.
-/
theorem tateNorm_grMk {n : ℕ} (x : S.F n) :
    tateNorm G (S.gr n) (S.grMk n x) = S.grMk n (tateNorm G (S.F n) x) := by
  rw [tateNorm_apply, tateNorm_apply, map_prod]
  rfl

/- English proof (translation)
Rewrite using `[augMap_apply, augMap_apply, map_prod]`. Simplify using `only [map_div, smul_grMk]`.
-/
theorem augMap_grMk {n : ℕ} (m : G → S.F n) :
    augMap G (S.gr n) (fun g => S.grMk n (m g)) = S.grMk n (augMap G (S.F n) m) := by
  rw [augMap_apply, augMap_apply, map_prod]
  simp only [map_div, smul_grMk]

/- English proof (translation)
The claim follows from `Subgroup.prod_mem _ fun g _ => S.smul_mem n g hx`.
-/
theorem tateNorm_mem {n : ℕ} {x : V} (hx : x ∈ S.F n) : tateNorm G V x ∈ S.F n :=
  Subgroup.prod_mem _ fun g _ => S.smul_mem n g hx

/- English proof (translation)
The claim follows from `Subgroup.prod_mem _ fun g _ => Subgroup.div_mem _ (S.smul_mem n g (hm g)) (hm g)`.
-/
theorem augMap_mem {n : ℕ} {m : G → V} (hm : ∀ g, m g ∈ S.F n) : augMap G V m ∈ S.F n :=
  Subgroup.prod_mem _ fun g _ => Subgroup.div_mem _ (S.smul_mem n g (hm g)) (hm g)

/- English proof (translation)
Rewrite using `[subsingleton_tateZero_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `h x hx hinv`. Take `⟨q, hq⟩` from `h (S.grMk n ⟨x, hx⟩) fun g => by`. Rewrite using `[smul_grMk, grMk_eq_grMk_iff]`.

Conclude with `hinv g`. Take `⟨y, rfl⟩` from `S.grMk_surjective n q`. Rewrite `hq` using `[tateNorm_grMk, eq_comm, grMk_eq_grMk_iff, coe_tateNorm_F]`. Conclude with `⟨y, y.2, hq⟩`. Introduce `h q hq`.

Take `⟨x, rfl⟩` from `S.grMk_surjective n q`. Take `⟨y, hy, hxy⟩` from `h x x.2 fun g => by`. Use `hq g` as an intermediate fact. Rewrite `this` using `[smul_grMk, grMk_eq_grMk_iff]`. Conclude with `this`.

Use `⟨S.grMk n ⟨y, hy⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[tateNorm_grMk, eq_comm, grMk_eq_grMk_iff, coe_tateNorm_F]`. Conclude with `hxy`.
-/
theorem subsingleton_tateZero_gr_iff (n : ℕ) :
    Subsingleton (TateZero G (S.gr n)) ↔
      ∀ x ∈ S.F n, (∀ g : G, g • x / x ∈ S.F (n + 1)) →
        ∃ y ∈ S.F n, x / tateNorm G V y ∈ S.F (n + 1) := by
  rw [subsingleton_tateZero_iff]
  constructor
  · intro h x hx hinv
    obtain ⟨q, hq⟩ := h (S.grMk n ⟨x, hx⟩) fun g => by
      rw [smul_grMk, grMk_eq_grMk_iff]
      exact hinv g
    obtain ⟨y, rfl⟩ := S.grMk_surjective n q
    rw [tateNorm_grMk, eq_comm, grMk_eq_grMk_iff, coe_tateNorm_F] at hq
    exact ⟨y, y.2, hq⟩
  · intro h q hq
    obtain ⟨x, rfl⟩ := S.grMk_surjective n q
    obtain ⟨y, hy, hxy⟩ := h x x.2 fun g => by
      have := hq g
      rw [smul_grMk, grMk_eq_grMk_iff] at this
      exact this
    refine ⟨S.grMk n ⟨y, hy⟩, ?_⟩
    rw [tateNorm_grMk, eq_comm, grMk_eq_grMk_iff, coe_tateNorm_F]
    exact hxy

/- English proof (translation)
Rewrite using `[subsingleton_tateNegOne_iff, augmentation_eq_range]`. Prove the components needed by the constructor for the conclusion. Introduce `h x hx hN`. Take `⟨q, hq⟩` from `h (S.grMk n ⟨x, hx⟩) (by`. Rewrite using `[tateNorm_grMk, grMk_eq_one_iff, coe_tateNorm_F]`.

Conclude with `hN)`. Establish `hl : ∀ g, ∃ y, S.grMk n y = q g` using `fun g => S.grMk_surjective n (q g)`. Use `choose m hm using hl`. Establish `e : q = fun g => S.grMk n (m g)` using `funext fun g => (hm g).symm`. Rewrite `hq` using `[e, augMap_grMk, eq_comm, grMk_eq_grMk_iff, coe_augMap_F]`.

Conclude with `⟨fun g => (m g : V), fun g => (m g).2, hq⟩`. Introduce `h q hq`. Take `⟨x, rfl⟩` from `S.grMk_surjective n q`. Rewrite `hq` using `[tateNorm_grMk, grMk_eq_one_iff, coe_tateNorm_F]`. Take `⟨m, hm, hxm⟩` from `h x x.2 hq`.

Use `⟨fun g => S.grMk n ⟨m g, hm g⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[augMap_grMk, eq_comm, grMk_eq_grMk_iff, coe_augMap_F]`. Conclude with `hxm`.
-/
theorem subsingleton_tateNegOne_gr_iff (n : ℕ) :
    Subsingleton (TateNegOne G (S.gr n)) ↔
      ∀ x ∈ S.F n, tateNorm G V x ∈ S.F (n + 1) →
        ∃ m : G → V, (∀ g, m g ∈ S.F n) ∧ x / augMap G V m ∈ S.F (n + 1) := by
  rw [subsingleton_tateNegOne_iff, augmentation_eq_range]
  constructor
  · intro h x hx hN
    obtain ⟨q, hq⟩ := h (S.grMk n ⟨x, hx⟩) (by
      rw [tateNorm_grMk, grMk_eq_one_iff, coe_tateNorm_F]
      exact hN)
    have hl : ∀ g, ∃ y, S.grMk n y = q g := fun g => S.grMk_surjective n (q g)
    choose m hm using hl
    have e : q = fun g => S.grMk n (m g) := funext fun g => (hm g).symm
    rw [e, augMap_grMk, eq_comm, grMk_eq_grMk_iff, coe_augMap_F] at hq
    exact ⟨fun g => (m g : V), fun g => (m g).2, hq⟩
  · intro h q hq
    obtain ⟨x, rfl⟩ := S.grMk_surjective n q
    rw [tateNorm_grMk, grMk_eq_one_iff, coe_tateNorm_F] at hq
    obtain ⟨m, hm, hxm⟩ := h x x.2 hq
    refine ⟨fun g => S.grMk n ⟨m g, hm g⟩, ?_⟩
    rw [augMap_grMk, eq_comm, grMk_eq_grMk_iff, coe_augMap_F]
    exact hxm

end StableFiltration

end Filtration

section Complete

variable {V : Type*} [CommGroup V]

/- English proof (translation)
Introduce `x hx`. Establish `hxi : ∀ i, FiltrationCauchy F fun k => x k i`. Introduce `i N`. Take `⟨M, hM⟩` from `hx N`. Conclude with `⟨M, fun m hm n hn => (Subgroup.mem_pi _).mp (hM m hm n hn) i (Set.mem_univ i)⟩`.

Use `choose y hy using fun i => hc _ (hxi i)`. Use `⟨y, fun N => ?_⟩` and prove the remaining obligations. Use `choose M hM using fun i => hy i N`. Use `⟨Finset.univ.sup M, fun n hn => (Subgroup.mem_pi _).mpr fun i _ => ?_⟩` and prove the remaining obligations. Conclude with `hM i n ((Finset.le_sup (Finset.mem_univ i)).trans hn)`.
-/
theorem filtrationComplete_pi {ι : Type*} [Fintype ι] {F : ℕ → Subgroup V}
    (hc : FiltrationComplete F) :
    FiltrationComplete fun n => Subgroup.pi Set.univ fun _ : ι => F n := by
  intro x hx
  have hxi : ∀ i, FiltrationCauchy F fun k => x k i := by
    intro i N
    obtain ⟨M, hM⟩ := hx N
    exact ⟨M, fun m hm n hn => (Subgroup.mem_pi _).mp (hM m hm n hn) i (Set.mem_univ i)⟩
  choose y hy using fun i => hc _ (hxi i)
  refine ⟨y, fun N => ?_⟩
  choose M hM using fun i => hy i N
  refine ⟨Finset.univ.sup M, fun n hn => (Subgroup.mem_pi _).mpr fun i _ => ?_⟩
  exact hM i n ((Finset.le_sup (Finset.mem_univ i)).trans hn)

variable {G : Type*} [Group G] [Fintype G] [MulDistribMulAction G V]

/- English proof (translation)
Rewrite using `[subsingleton_tateZero_iff]`. Introduce `x hx`. Set `f : V →* invariants G V` to `(tateNorm G V).codRestrict _ tateNorm_mem_invariants`. Set `E : ℕ → Subgroup (invariants G V)` to `fun n => (S.F n).subgroupOf (invariants G V)`. Establish `key` using `map_eq_of_graded_surjective (F := S.F) (E := E) S.antitone (fun a b hab y hy => Subgroup.mem_subgroupOf.mpr (S.antitone hab (Subgroup.mem_subgroupOf.mp hy))) hc (fun y hy => Subtype.ext (hs _ fun n => Subgroup.mem_subgroupOf.mp (hy n))) f tendsto_id 0 (fun n _ y hy => Subgroup.me …`.

Establish `hh' : (h : V) ∈ S.F n` using `Subgroup.mem_subgroupOf.mp hh`. Take `⟨y, hy, hhy⟩` from `(S.subsingleton_tateZero_gr_iff n).mp (hgr n) h hh' fun g => by`. Rewrite using `[h.2 g, div_self']`. Conclude with `Subgroup.one_mem _`. Conclude with `⟨y, hy, Subgroup.mem_subgroupOf.mpr hhy⟩)`.

Establish `hx0 : (⟨x, (mem_invariants G V).mpr hx⟩ : invariants G V) ∈ (S.F 0).map f`. Rewrite using `[key]`. Express the relevant statement in the definitionally equal form `_ ∈ E 0`. Rewrite using `[Subgroup.mem_subgroupOf, h0]`. Conclude with `Subgroup.mem_top _`.

Take `⟨y, -, hy⟩` from `hx0`. Conclude with `⟨y, congrArg Subtype.val hy⟩`.
-/
theorem subsingleton_tateZero_of_complete (S : StableFiltration G V) (h0 : S.F 0 = ⊤)
    (hc : FiltrationComplete S.F) (hs : FiltrationSeparated S.F)
    (hgr : ∀ n, Subsingleton (TateZero G (S.gr n))) : Subsingleton (TateZero G V) := by
  rw [subsingleton_tateZero_iff]
  intro x hx
  let f : V →* invariants G V := (tateNorm G V).codRestrict _ tateNorm_mem_invariants
  let E : ℕ → Subgroup (invariants G V) := fun n => (S.F n).subgroupOf (invariants G V)
  have key := map_eq_of_graded_surjective (F := S.F) (E := E) S.antitone
    (fun a b hab y hy => Subgroup.mem_subgroupOf.mpr (S.antitone hab (Subgroup.mem_subgroupOf.mp hy)))
    hc (fun y hy => Subtype.ext (hs _ fun n => Subgroup.mem_subgroupOf.mp (hy n))) f tendsto_id 0
    (fun n _ y hy => Subgroup.mem_subgroupOf.mpr (S.tateNorm_mem hy))
    (fun n _ h hh => by
      have hh' : (h : V) ∈ S.F n := Subgroup.mem_subgroupOf.mp hh
      obtain ⟨y, hy, hhy⟩ := (S.subsingleton_tateZero_gr_iff n).mp (hgr n) h hh' fun g => by
        rw [h.2 g, div_self']
        exact Subgroup.one_mem _
      exact ⟨y, hy, Subgroup.mem_subgroupOf.mpr hhy⟩)
  have hx0 : (⟨x, (mem_invariants G V).mpr hx⟩ : invariants G V) ∈ (S.F 0).map f := by
    rw [key]
    change _ ∈ E 0
    rw [Subgroup.mem_subgroupOf, h0]
    exact Subgroup.mem_top _
  obtain ⟨y, -, hy⟩ := hx0
  exact ⟨y, congrArg Subtype.val hy⟩

/- English proof (translation)
Rewrite using `[subsingleton_tateNegOne_iff, augmentation_eq_range]`. Introduce `x hx`. Set `f : (G → V) →* (tateNorm G V).ker` to `(augMap G V).codRestrict _ tateNorm_augMap`. Set `P : ℕ → Subgroup (G → V)` to `fun n => Subgroup.pi Set.univ fun _ : G => S.F n`. Set `E : ℕ → Subgroup (tateNorm G V).ker` to `fun n => (S.F n).subgroupOf (tateNorm G V).ker`.

Establish `key` using `map_eq_of_graded_surjective (F := P) (E := E) (fun a b hab m hm => (Subgroup.mem_pi _).mpr fun g _ => S.antitone hab ((Subgroup.mem_pi _).mp hm g (Set.mem_univ g))) (fun a b hab y hy => Subgroup.mem_subgroupOf.mpr (S.antitone hab (Subgroup.mem_subgroupOf.mp hy))) (filtrationCompl …`. Establish `hh' : (h : V) ∈ S.F n` using `Subgroup.mem_subgroupOf.mp hh`. Establish `hN : tateNorm G V h ∈ S.F (n + 1)`. Rewrite using `[h.2]`. Conclude with `Subgroup.one_mem _`.

Take `⟨m, hm, hhm⟩` from `(S.subsingleton_tateNegOne_gr_iff n).mp (hgr n) h hh' hN`. Conclude with `⟨m, (Subgroup.mem_pi _).mpr fun g _ => hm g, Subgroup.mem_subgroupOf.mpr hhm⟩)`. Establish `hx0 : (⟨x, MonoidHom.mem_ker.mpr hx⟩ : (tateNorm G V).ker) ∈ (P 0).map f`. Rewrite using `[key]`. Express the relevant statement in the definitionally equal form `_ ∈ E 0`.

Rewrite using `[Subgroup.mem_subgroupOf, h0]`. Conclude with `Subgroup.mem_top _`. Take `⟨m, -, hm⟩` from `hx0`. Conclude with `⟨m, congrArg Subtype.val hm⟩`.
-/
theorem subsingleton_tateNegOne_of_complete (S : StableFiltration G V) (h0 : S.F 0 = ⊤)
    (hc : FiltrationComplete S.F) (hs : FiltrationSeparated S.F)
    (hgr : ∀ n, Subsingleton (TateNegOne G (S.gr n))) : Subsingleton (TateNegOne G V) := by
  rw [subsingleton_tateNegOne_iff, augmentation_eq_range]
  intro x hx
  let f : (G → V) →* (tateNorm G V).ker := (augMap G V).codRestrict _ tateNorm_augMap
  let P : ℕ → Subgroup (G → V) := fun n => Subgroup.pi Set.univ fun _ : G => S.F n
  let E : ℕ → Subgroup (tateNorm G V).ker := fun n => (S.F n).subgroupOf (tateNorm G V).ker
  have key := map_eq_of_graded_surjective (F := P) (E := E)
    (fun a b hab m hm => (Subgroup.mem_pi _).mpr fun g _ =>
      S.antitone hab ((Subgroup.mem_pi _).mp hm g (Set.mem_univ g)))
    (fun a b hab y hy => Subgroup.mem_subgroupOf.mpr (S.antitone hab (Subgroup.mem_subgroupOf.mp hy)))
    (filtrationComplete_pi hc)
    (fun y hy => Subtype.ext (hs _ fun n => Subgroup.mem_subgroupOf.mp (hy n))) f tendsto_id 0
    (fun n _ m hm => Subgroup.mem_subgroupOf.mpr
      (S.augMap_mem fun g => (Subgroup.mem_pi _).mp hm g (Set.mem_univ g)))
    (fun n _ h hh => by
      have hh' : (h : V) ∈ S.F n := Subgroup.mem_subgroupOf.mp hh
      have hN : tateNorm G V h ∈ S.F (n + 1) := by
        rw [h.2]
        exact Subgroup.one_mem _
      obtain ⟨m, hm, hhm⟩ := (S.subsingleton_tateNegOne_gr_iff n).mp (hgr n) h hh' hN
      exact ⟨m, (Subgroup.mem_pi _).mpr fun g _ => hm g, Subgroup.mem_subgroupOf.mpr hhm⟩)
  have hx0 : (⟨x, MonoidHom.mem_ker.mpr hx⟩ : (tateNorm G V).ker) ∈ (P 0).map f := by
    rw [key]
    change _ ∈ E 0
    rw [Subgroup.mem_subgroupOf, h0]
    exact Subgroup.mem_top _
  obtain ⟨m, -, hm⟩ := hx0
  exact ⟨m, congrArg Subtype.val hm⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨subsingleton_tateZero_of_complete S h0 hc hs hgr0, subsingleton_tateNegOne_of_complete S h0 hc hs hgr1⟩`.
-/
theorem subsingleton_tate_of_complete (S : StableFiltration G V) (h0 : S.F 0 = ⊤)
    (hc : FiltrationComplete S.F) (hs : FiltrationSeparated S.F)
    (hgr0 : ∀ n, Subsingleton (TateZero G (S.gr n)))
    (hgr1 : ∀ n, Subsingleton (TateNegOne G (S.gr n))) :
    Subsingleton (TateZero G V) ∧ Subsingleton (TateNegOne G V) :=
  ⟨subsingleton_tateZero_of_complete S h0 hc hs hgr0,
    subsingleton_tateNegOne_of_complete S h0 hc hs hgr1⟩

end Complete

end GroundTheory.LocalField
