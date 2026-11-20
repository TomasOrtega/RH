import Mathlib
import Formalism.TameInertiaTowers.StatementGroup
import Formalism.TameInertiaTowers.CentralOrderTwo.TwoAdic

namespace Formalism.TwoAdicCyclotomicDecomposition

/- English proof (translation)
Establish `h : ((5:ℤ) ^ 2 - 1) = ((2 ^ 3 * 3 : ℕ) : ℤ)` using `by norm_num`. Rewrite using `[h, padicValInt.of_nat, padicValNat.mul (show 2 ^ 3 ≠ 0 by norm_num) (show 3 ≠ 0 by norm_num), padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd (show ¬ 2 ∣ 3 by norm_num)]`.
-/
lemma pv24 : padicValInt 2 ((5:ℤ) ^ 2 - 1) = 3 := by
  have h : ((5:ℤ) ^ 2 - 1) = ((2 ^ 3 * 3 : ℕ) : ℤ) := by norm_num
  rw [h, padicValInt.of_nat, padicValNat.mul (show 2 ^ 3 ≠ 0 by norm_num) (show 3 ≠ 0 by norm_num),
    padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd (show ¬ 2 ∣ 3 by norm_num)]

/- English proof (translation)
Simplify using `[u5, ZMod.coe_unitOfCoprime]`.
-/
lemma five_unit_coe_int (n : ℕ) : ((u5 n : (ZMod (2 ^ n))ˣ) : ZMod (2 ^ n)) = ((5 : ℤ) : ZMod (2 ^ n)) := by simp [u5, ZMod.coe_unitOfCoprime]

/- English proof (translation)
Establish `h` using `ZMod.intCast_eq_intCast_iff_dvd_sub 5 1 (2 ^ n)`. Rewrite `h` using `[Int.cast_one]`. Rewrite using `[h]`. Use `push_cast`. Apply the tactic sequence `constructor <;> intro h' <;> simpa using h'`.
-/
private lemma intCast_five_zmod_two_pow_eq_one_iff (n : ℕ) : ((5:ℤ) : ZMod (2 ^ n)) = 1 ↔ (2:ℤ) ^ n ∣ 4 := by
  have h := ZMod.intCast_eq_intCast_iff_dvd_sub 5 1 (2 ^ n)
  rw [Int.cast_one] at h
  rw [h]
  push_cast
  constructor <;> intro h' <;> simpa using h'

/- English proof (translation)
Establish `h` using `twoAdicOrder (m + 2) 5 ⟨2, by norm_num⟩ (by norm_num)`. Rewrite `h` using `[pv24]`. Rewrite using `[← orderOf_units, five_unit_coe_int, h]`. Break down `m with _ | k` into its components or cases. Rewrite using `[if_pos ((intCast_five_zmod_two_pow_eq_one_iff (0 + 2)).2 ⟨1, by norm_num⟩)]`.

Both sides reduce to the same expression. Rewrite using `[if_neg]`. Use `congr 1`. Introduce `h1`. Establish `h2` using `(intCast_five_zmod_two_pow_eq_one_iff (k + 1 + 2)).1 h1`.

Establish `h8 : (8:ℤ) ∣ 2 ^ (k + 1 + 2)` using `⟨2 ^ k, by ring⟩`. Establish `h3` using `h8.trans h2`. Use linear arithmetic over natural numbers and integers.
-/
lemma ord5 (m : ℕ) : orderOf (u5 (m + 2)) = 2 ^ m := by
  have h := twoAdicOrder (m + 2) 5 ⟨2, by norm_num⟩ (by norm_num)
  rw [pv24] at h
  rw [← orderOf_units, five_unit_coe_int, h]
  rcases m with _ | k
  · rw [if_pos ((intCast_five_zmod_two_pow_eq_one_iff (0 + 2)).2 ⟨1, by norm_num⟩)]
    rfl
  · rw [if_neg]
    · congr 1
    · intro h1
      have h2 := (intCast_five_zmod_two_pow_eq_one_iff (k + 1 + 2)).1 h1
      have h8 : (8:ℤ) ∣ 2 ^ (k + 1 + 2) := ⟨2 ^ k, by ring⟩
      have h3 := h8.trans h2
      omega

/- English proof (translation)
Simplify using `[u5, ZMod.coe_unitOfCoprime]`.
-/
lemma five_unit_coe_nat (n : ℕ) : ((u5 n : (ZMod (2 ^ n))ˣ) : ZMod (2 ^ n)) = ((5 : ℕ) : ZMod (2 ^ n)) := by simp [u5, ZMod.coe_unitOfCoprime]

/- English proof (translation)
Use `ext`. Rewrite using `[ZMod.unitsMap_def, Units.coe_map, five_unit_coe_int, five_unit_coe_int]`. Conclude with `map_intCast (ZMod.castHom h (ZMod (2 ^ b))) 5`.
-/
lemma unitsMap_five {a b : ℕ} (h : 2 ^ b ∣ 2 ^ a) : ZMod.unitsMap h (u5 a) = u5 b := by
  ext
  rw [ZMod.unitsMap_def, Units.coe_map, five_unit_coe_int, five_unit_coe_int]
  exact map_intCast (ZMod.castHom h (ZMod (2 ^ b))) 5

/- English proof (translation)
Use `ext`. Simplify using `[ZMod.unitsMap_def]`.
-/
lemma unitsMap_neg_one' {a b : ℕ} (h : b ∣ a) : ZMod.unitsMap h (-1) = -1 := by
  ext
  simp [ZMod.unitsMap_def]

noncomputable def r4 (n : ℕ) : (ZMod (2 ^ (n + 2)))ˣ →* (ZMod (2 ^ 2))ˣ :=
  ZMod.unitsMap (pow_dvd_pow 2 (by omega))

/- English proof (translation)
Use `ext`. Rewrite using `[five_unit_coe_int, Units.val_one]`. Conclude with `(intCast_five_zmod_two_pow_eq_one_iff 2).2 ⟨1, by norm_num⟩`.
-/
lemma five_unit_mod_four : u5 2 = 1 := by
  ext
  rw [five_unit_coe_int, Units.val_one]
  exact (intCast_five_zmod_two_pow_eq_one_iff 2).2 ⟨1, by norm_num⟩

/- English proof (translation)
Rewrite using `[r4, unitsMap_five, five_unit_mod_four]`.
-/
lemma mod_four_reduction_five (n : ℕ) : r4 n (u5 (n + 2)) = 1 := by rw [r4, unitsMap_five, five_unit_mod_four]

/- English proof (translation)
Rewrite using `[r4, unitsMap_neg_one']`.
-/
lemma mod_four_reduction_neg_one (n : ℕ) : r4 n (-1) = -1 := by rw [r4, unitsMap_neg_one']

/- English proof (translation)
Use `haveI : Fact (2 < 2 ^ 2) := ⟨by norm_num⟩`. Introduce `h`. Apply `ZMod.neg_one_ne_one (n := 2 ^ 2)` to reduce the goal to its premises. Simplify using `using congrArg Units.val h`.
-/
lemma neg_one_ne_one_units_zmod_four : (-1 : (ZMod (2 ^ 2))ˣ) ≠ 1 := by
  haveI : Fact (2 < 2 ^ 2) := ⟨by norm_num⟩
  intro h
  apply ZMod.neg_one_ne_one (n := 2 ^ 2)
  simpa using congrArg Units.val h

/- English proof (translation)
Introduce `h`. Apply `neg_one_ne_one_units_zmod_four` to reduce the goal to its premises. Establish `h1` using `congrArg (r4 n) h`. Rewrite `h1` using `[mod_four_reduction_neg_one, map_one]`. Then use the resulting hypothesis.
-/
lemma neg_ne_one (n : ℕ) : (-1 : (ZMod (2 ^ (n + 2)))ˣ) ≠ 1 := by
  intro h
  apply neg_one_ne_one_units_zmod_four
  have h1 := congrArg (r4 n) h
  rwa [mod_four_reduction_neg_one, map_one] at h1

/- English proof (translation)
Introduce `h`. Establish `h1` using `congrArg (r4 n) h`. Rewrite `h1` using `[mod_four_reduction_neg_one, map_pow, mod_four_reduction_five, one_pow]`. Conclude with `neg_one_ne_one_units_zmod_four h1`.
-/
lemma neg_one_ne_pow_five (n k : ℕ) : (-1 : (ZMod (2 ^ (n + 2)))ˣ) ≠ u5 (n + 2) ^ k := by
  intro h
  have h1 := congrArg (r4 n) h
  rw [mod_four_reduction_neg_one, map_pow, mod_four_reduction_five, one_pow] at h1
  exact neg_one_ne_one_units_zmod_four h1

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hx`. Take `⟨k, rfl⟩` from `Subgroup.mem_zpowers_iff.1 hx`. Establish `h2 : g ^ (2:ℤ) = 1` using `by rw [zpow_two, ← pow_two]; exact hg`. Take `⟨j, rfl | rfl⟩` from `Int.even_or_odd' k`.

Use `left`. Rewrite using `[zpow_mul, h2, one_zpow]`. Use `right`. Rewrite using `[zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]`. Introduce and unpack `(rfl | rfl)`.

Conclude with `Subgroup.one_mem _`. Conclude with `Subgroup.mem_zpowers _`.
-/
lemma mem_zpowers_sq {G : Type*} [Group G] {g x : G} (hg : g ^ 2 = 1) :
    x ∈ Subgroup.zpowers g ↔ x = 1 ∨ x = g := by
  constructor
  · intro hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    have h2 : g ^ (2:ℤ) = 1 := by rw [zpow_two, ← pow_two]; exact hg
    obtain ⟨j, rfl | rfl⟩ := Int.even_or_odd' k
    · left
      rw [zpow_mul, h2, one_zpow]
    · right
      rw [zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _

/- English proof (translation)
The claim follows from `neg_one_sq`.
-/
lemma neg_one_sq_units {n : ℕ} : (-1 : (ZMod (2 ^ n))ˣ) ^ 2 = 1 := neg_one_sq

/- English proof (translation)
Rewrite using `[Prod.pow_mk, Prod.pow_mk, neg_one_sq_units, one_pow]`. Apply the tactic sequence `all_goals rfl`.
-/
lemma gen_sq {n : ℕ} : ((-1, 1, 1) : GalL n) ^ 2 = 1 := by
  rw [Prod.pow_mk, Prod.pow_mk, neg_one_sq_units, one_pow]
  all_goals rfl

abbrev QQ (s : ℕ) : Type := (ZMod (2 ^ (s + 2)))ˣ ⧸ Subgroup.zpowers (-1 : (ZMod (2 ^ (s + 2)))ˣ)

/- English proof (translation)
Rewrite using `[Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime_pow Nat.prime_two (by omega), show s + 2 - 1 = s + 1 by omega]`. Evaluate the numerical expressions.
-/
lemma card_units (s : ℕ) : Nat.card (ZMod (2 ^ (s + 2)))ˣ = 2 ^ (s + 1) := by
  rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime_pow Nat.prime_two (by omega),
    show s + 2 - 1 = s + 1 by omega]
  norm_num

/- English proof (translation)
Rewrite using `[Nat.card_zpowers]`. Conclude with `orderOf_eq_prime neg_one_sq_units (neg_ne_one s)`.
-/
lemma card_zp_neg (s : ℕ) : Nat.card (Subgroup.zpowers (-1 : (ZMod (2 ^ (s + 2)))ˣ)) = 2 := by
  rw [Nat.card_zpowers]
  exact orderOf_eq_prime neg_one_sq_units (neg_ne_one s)

/- English proof (translation)
Establish `h` using `Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.zpowers (-1 : (ZMod (2 ^ (s + 2)))ˣ))`. Rewrite `h` using `[card_units, card_zp_neg, pow_succ]`. Conclude with `(Nat.eq_of_mul_eq_mul_right (by norm_num) h).symm`.
-/
lemma card_QQ (s : ℕ) : Nat.card (QQ s) = 2 ^ s := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.zpowers (-1 : (ZMod (2 ^ (s + 2)))ˣ))
  rw [card_units, card_zp_neg, pow_succ] at h
  exact (Nat.eq_of_mul_eq_mul_right (by norm_num) h).symm

/- English proof (translation)
Break down `s with _ | k` into its components or cases. Simplify using `[five_unit_mod_four]`. Apply `orderOf_eq_prime_pow` to reduce the goal to its premises. Rewrite using `[← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_zpowers_sq neg_one_sq_units]`. Introduce and unpack `(h | h)`.

Use `pow_ne_one_of_lt_orderOf (by positivity) ?_ h` and prove the remaining obligations. Rewrite using `[ord5, pow_succ]`. Use `Nat.two_pow_pos k` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Conclude with `neg_one_ne_pow_five (k + 1) (2 ^ k) h.symm`.

Establish `h1` using `pow_orderOf_eq_one (u5 (k + 1 + 2))`. Rewrite `h1` using `[ord5]`. Rewrite using `[← QuotientGroup.mk_pow, h1, QuotientGroup.mk_one]`.
-/
lemma ord_QQ (s : ℕ) : orderOf (QuotientGroup.mk (u5 (s + 2)) : QQ s) = 2 ^ s := by
  rcases s with _ | k
  · simp [five_unit_mod_four]
  · apply orderOf_eq_prime_pow
    · rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_zpowers_sq neg_one_sq_units]
      rintro (h | h)
      · refine pow_ne_one_of_lt_orderOf (by positivity) ?_ h
        rw [ord5, pow_succ]
        have := Nat.two_pow_pos k
        omega
      · exact neg_one_ne_pow_five (k + 1) (2 ^ k) h.symm
    · have h1 := pow_orderOf_eq_one (u5 (k + 1 + 2))
      rw [ord5] at h1
      rw [← QuotientGroup.mk_pow, h1, QuotientGroup.mk_one]

/- English proof (translation)
Conclude with `isCyclic_of_orderOf_eq_card (QuotientGroup.mk (u5 (s + 2)) : QQ s) (by rw [ord_QQ, card_QQ])`.
-/
lemma cyc_QQ (s : ℕ) : IsCyclic (QQ s) := by
  exact isCyclic_of_orderOf_eq_card (QuotientGroup.mk (u5 (s + 2)) : QQ s) (by rw [ord_QQ, card_QQ])

/- English proof (translation)
Rewrite using `[Nat.card_congr Multiplicative.ofAdd.symm, Nat.card_zmod]`.
-/
lemma card_mz (n : ℕ) : Nat.card (Multiplicative (ZMod n)) = n := by
  rw [Nat.card_congr Multiplicative.ofAdd.symm, Nat.card_zmod]

noncomputable def eQQ (s : ℕ) : QQ s ≃* Multiplicative (ZMod (2 ^ s)) :=
  @mulEquivOfCyclicCardEq _ _ _ _ (cyc_QQ s) _ (by rw [card_QQ, card_mz])

noncomputable def phiE (s : ℕ) : GalL (s + 2) →* QQ s × ℤˣ × ℤˣ :=
  MonoidHom.prodMap (QuotientGroup.mk' _) (MonoidHom.id _)

/- English proof (translation)
Introduce and unpack `⟨q, b⟩`. Take `⟨u, rfl⟩` from `QuotientGroup.mk'_surjective _ q`. Conclude with `⟨(u, b), rfl⟩`.
-/
lemma phiE_surj (s : ℕ) : Function.Surjective (phiE s) := by
  rintro ⟨q, b⟩
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective _ q
  exact ⟨(u, b), rfl⟩

/- English proof (translation)
Use extensionality with `⟨u, b⟩`. Rewrite using `[MonoidHom.mem_ker, mem_zpowers_sq gen_sq]`. Express the relevant statement in the definitionally equal form `(QuotientGroup.mk' _ u, b) = 1 ↔ _`. Rewrite using `[Prod.mk_eq_one, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_zpowers_sq neg_one_sq_units]`. Simplify using `only [Prod.ext_iff, Prod.fst_one, Prod.snd_one]`.

The claim follows by propositional logic.
-/
lemma phiE_ker (s : ℕ) : (phiE s).ker = Subgroup.zpowers ((-1, 1, 1) : GalL (s + 2)) := by
  ext ⟨u, b⟩
  rw [MonoidHom.mem_ker, mem_zpowers_sq gen_sq]
  change (QuotientGroup.mk' _ u, b) = 1 ↔ _
  rw [Prod.mk_eq_one, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_zpowers_sq neg_one_sq_units]
  simp only [Prod.ext_iff, Prod.fst_one, Prod.snd_one]
  tauto

noncomputable def eGamE (s : ℕ) : GamE s ≃* Multiplicative (ZMod (2 ^ s)) × ℤˣ × ℤˣ :=
  ((QuotientGroup.quotientMulEquivOfEq (phiE_ker s).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (phiE_surj s))).trans
    (MulEquiv.prodCongr (eQQ s) (MulEquiv.refl _))

/- English proof (translation)
Rewrite using `[Nat.card_eq_fintype_card, Fintype.card_units_int]`.
-/
private lemma card_int_units_eq_two : Nat.card ℤˣ = 2 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_units_int]

/- English proof (translation)
Rewrite using `[Nat.card_congr (eGamE s).toEquiv, Nat.card_prod, Nat.card_prod, card_mz, card_int_units_eq_two]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma card_GamE (s : ℕ) : Nat.card (GamE s) = 2 ^ (s + 2) := by
  rw [Nat.card_congr (eGamE s).toEquiv, Nat.card_prod, Nat.card_prod, card_mz, card_int_units_eq_two]
  ring

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma resMap_apply {s m : ℕ} (h : s ≤ m) (u : (ZMod (2 ^ (m + 2)))ˣ) (a b : ℤˣ) :
    resMap h (u, a, b) = (ZMod.unitsMap (pow_dvd_pow 2 (by omega)) u, a, b) := rfl

/- English proof (translation)
Unfold `GG`. Rewrite using `[MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]`.
-/
lemma mem_GG {s m : ℕ} (h : s ≤ m) (x : GalL (m + 2)) :
    x ∈ GG h ↔ resMap h x ∈ Subgroup.zpowers ((-1, 1, 1) : GalL (s + 2)) := by
  unfold GG
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

/- English proof (translation)
Introduce and unpack `⟨u, a, b⟩`. Take `⟨v, hv⟩` from `ZMod.unitsMap_surjective (pow_dvd_pow 2 (by omega : s + 2 ≤ m + 2)) u`. Conclude with `⟨(v, a, b), by rw [resMap_apply, hv]⟩`.
-/
lemma resMap_surj {s m : ℕ} (h : s ≤ m) : Function.Surjective (resMap h) := by
  rintro ⟨u, a, b⟩
  obtain ⟨v, hv⟩ := ZMod.unitsMap_surjective (pow_dvd_pow 2 (by omega : s + 2 ≤ m + 2)) u
  exact ⟨(v, a, b), by rw [resMap_apply, hv]⟩

/- English proof (translation)
Rewrite using `[Nat.card_prod, Nat.card_prod, card_units, card_int_units_eq_two]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma card_GalL (n : ℕ) : Nat.card (GalL (n + 2)) = 2 ^ (n + 3) := by
  rw [Nat.card_prod, Nat.card_prod, card_units, card_int_units_eq_two]
  ring

/- English proof (translation)
Establish `hs : Function.Surjective ((QuotientGroup.mk' (Subgroup.zpowers ((-1, 1, 1) : GalL (s + 2)))).comp (resMap h))` using `(QuotientGroup.mk'_surjective _).comp (resMap_surj h)`. Establish `e` using `QuotientGroup.quotientKerEquivOfSurjective _ hs`. Establish `h1` using `Subgroup.card_eq_card_quotient_mul_card_subgroup ((QuotientGroup.mk' (Subgroup.zpowers ((-1, 1, 1) : GalL (s + 2)))).comp (resMap h)).ker`. Rewrite `h1` using `[Nat.card_congr e.toEquiv, card_GalL, card_GamE]`. Establish `h3 : (2:ℕ) ^ (m + 3) = 2 ^ (s + 2) * 2 ^ (m - s + 1)`.

Rewrite using `[← pow_add]`. Use `congr 1`. Use linear arithmetic over natural numbers and integers. Rewrite `h1` using `[h3]`. Conclude with `(Nat.eq_of_mul_eq_mul_left (by positivity) h1).symm`.
-/
lemma card_GG {s m : ℕ} (h : s ≤ m) : Nat.card (GG h) = 2 ^ (m - s + 1) := by
  have hs : Function.Surjective
      ((QuotientGroup.mk' (Subgroup.zpowers ((-1, 1, 1) : GalL (s + 2)))).comp (resMap h)) :=
    (QuotientGroup.mk'_surjective _).comp (resMap_surj h)
  have e := QuotientGroup.quotientKerEquivOfSurjective _ hs
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((QuotientGroup.mk' (Subgroup.zpowers ((-1, 1, 1) : GalL (s + 2)))).comp (resMap h)).ker
  rw [Nat.card_congr e.toEquiv, card_GalL, card_GamE] at h1
  have h3 : (2:ℕ) ^ (m + 3) = 2 ^ (s + 2) * 2 ^ (m - s + 1) := by
    rw [← pow_add]
    congr 1
    omega
  rw [h3] at h1
  exact (Nat.eq_of_mul_eq_mul_left (by positivity) h1).symm

noncomputable def iota (n : ℕ) : ℤˣ →* (ZMod (2 ^ n))ˣ :=
  Units.map (Int.castRingHom (ZMod (2 ^ n))).toMonoidHom

/- English proof (translation)
Use `ext`. Simplify using `[iota]`.
-/
lemma iota_neg (n : ℕ) : iota n (-1) = -1 := by
  ext
  simp [iota]

/- English proof (translation)
The claim follows from `map_one _`.
-/
lemma iota_one (n : ℕ) : iota n 1 = 1 := map_one _

noncomputable def wgen (s m : ℕ) : (ZMod (2 ^ (m + 2)))ˣ := u5 (m + 2) ^ (2 ^ s)

/- English proof (translation)
Establish `hd : 2 ^ s ∣ orderOf (u5 (m + 2))`. Rewrite using `[ord5]`. Conclude with `pow_dvd_pow 2 h`. Rewrite using `[wgen, orderOf_pow_of_dvd (by positivity) hd, ord5, Nat.pow_div h (by norm_num)]`.
-/
lemma ord_w {s m : ℕ} (h : s ≤ m) : orderOf (wgen s m) = 2 ^ (m - s) := by
  have hd : 2 ^ s ∣ orderOf (u5 (m + 2)) := by
    rw [ord5]
    exact pow_dvd_pow 2 h
  rw [wgen, orderOf_pow_of_dvd (by positivity) hd, ord5, Nat.pow_div h (by norm_num)]

/- English proof (translation)
Rewrite using `[wgen, map_pow, mod_four_reduction_five, one_pow]`.
-/
lemma mod_four_generator_eq_one (s m : ℕ) : r4 m (wgen s m) = 1 := by rw [wgen, map_pow, mod_four_reduction_five, one_pow]

/- English proof (translation)
Rewrite using `[wgen, map_pow, unitsMap_five]`. Establish `h1` using `pow_orderOf_eq_one (u5 (s + 2))`. Rewrite `h1` using `[ord5]`. Then use the resulting hypothesis.
-/
lemma um_w {s m : ℕ} (h : s ≤ m) :
    ZMod.unitsMap (pow_dvd_pow 2 (by omega : s + 2 ≤ m + 2)) (wgen s m) = 1 := by
  rw [wgen, map_pow, unitsMap_five]
  have h1 := pow_orderOf_eq_one (u5 (s + 2))
  rwa [ord5] at h1

noncomputable def psi {s m : ℕ} (h : s ≤ m) :
    ℤˣ × Multiplicative (ZMod (2 ^ (m - s))) →* GalL (m + 2) :=
  MonoidHom.mk' (fun p => (iota (m + 2) p.1 * wgen s m ^ (Multiplicative.toAdd p.2).val, 1, 1))
    (by
      rintro ⟨e1, k1⟩ ⟨e2, k2⟩
      simp only [Prod.mk_mul_mk, mul_one, toAdd_mul, map_mul]
      congr 1
      have key : ∀ n : ℕ, wgen s m ^ (n % 2 ^ (m - s)) = wgen s m ^ n := fun n => by
        rw [← ord_w h, pow_mod_orderOf]
      rw [ZMod.val_add, key, pow_add (wgen s m)]
      exact mul_mul_mul_comm _ _ _ _)

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma psi_apply {s m : ℕ} (h : s ≤ m) (e : ℤˣ) (k : Multiplicative (ZMod (2 ^ (m - s)))) :
    psi h (e, k) = (iota (m + 2) e * wgen s m ^ (Multiplicative.toAdd k).val, 1, 1) := rfl

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_one]`. Introduce and unpack `⟨e, k⟩ hk`. Rewrite `hk` using `[psi_apply]`. Establish `h1 : iota (m + 2) e * wgen s m ^ (Multiplicative.toAdd k).val = 1` using `congrArg Prod.fst hk`. Establish `he : e = 1`.

Break down `Int.units_eq_one_or e with rfl | rfl` into its components or cases. Both sides reduce to the same expression. It suffices to derive a contradiction. Establish `h2` using `congrArg (r4 m) h1`. Rewrite `h2` using `[map_mul, map_pow, mod_four_generator_eq_one, one_pow, mul_one, iota_neg, mod_four_reduction_neg_one, map_one]`.

Conclude with `neg_one_ne_one_units_zmod_four h2`. Substitute `he` using the available equality. Rewrite `h1` using `[iota_one, one_mul, ← orderOf_dvd_iff_pow_eq_one, ord_w h]`. Establish `hlt` using `ZMod.val_lt (Multiplicative.toAdd k)`. Establish `h0 : (Multiplicative.toAdd k).val = 0` using `Nat.eq_zero_of_dvd_of_lt h1 hlt`.

Rewrite `h0` using `[ZMod.val_eq_zero]`. Use `Prod.ext rfl ?_` and prove the remaining obligations. Use `show k = 1`. Rewrite using `[← ofAdd_toAdd k, h0, ofAdd_zero]`.
-/
lemma psi_inj {s m : ℕ} (h : s ≤ m) : Function.Injective (psi h) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨e, k⟩ hk
  rw [psi_apply] at hk
  have h1 : iota (m + 2) e * wgen s m ^ (Multiplicative.toAdd k).val = 1 := congrArg Prod.fst hk
  have he : e = 1 := by
    rcases Int.units_eq_one_or e with rfl | rfl
    · rfl
    · exfalso
      have h2 := congrArg (r4 m) h1
      rw [map_mul, map_pow, mod_four_generator_eq_one, one_pow, mul_one, iota_neg, mod_four_reduction_neg_one, map_one] at h2
      exact neg_one_ne_one_units_zmod_four h2
  subst he
  rw [iota_one, one_mul, ← orderOf_dvd_iff_pow_eq_one, ord_w h] at h1
  have hlt := ZMod.val_lt (Multiplicative.toAdd k)
  have h0 : (Multiplicative.toAdd k).val = 0 := Nat.eq_zero_of_dvd_of_lt h1 hlt
  rw [ZMod.val_eq_zero] at h0
  refine Prod.ext rfl ?_
  show k = 1
  rw [← ofAdd_toAdd k, h0, ofAdd_zero]

/- English proof (translation)
Rewrite using `[Nat.card_prod, card_int_units_eq_two, card_mz]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma card_dom (s m : ℕ) :
    Nat.card (ℤˣ × Multiplicative (ZMod (2 ^ (m - s)))) = 2 ^ (m - s + 1) := by
  rw [Nat.card_prod, card_int_units_eq_two, card_mz]
  ring

/- English proof (translation)
Rewrite using `[Subgroup.closure_le]`. Introduce and unpack `x (rfl | rfl)`. Rewrite using `[SetLike.mem_coe, mem_GG, resMap_apply, unitsMap_neg_one']`. Conclude with `Subgroup.mem_zpowers _`. Rewrite using `[SetLike.mem_coe, mem_GG, resMap_apply, show u5 (m + 2) ^ (2 ^ s) = wgen s m from rfl, um_w h]`.

Conclude with `Subgroup.one_mem _`.
-/
lemma closure_le_GG {s m : ℕ} (h : s ≤ m) :
    Subgroup.closure {((-1, 1, 1) : GalL (m + 2)), ((u5 (m + 2) ^ (2 ^ s), 1, 1) : GalL (m + 2))}
      ≤ GG h := by
  rw [Subgroup.closure_le]
  rintro x (rfl | rfl)
  · rw [SetLike.mem_coe, mem_GG, resMap_apply, unitsMap_neg_one']
    exact Subgroup.mem_zpowers _
  · rw [SetLike.mem_coe, mem_GG, resMap_apply, show u5 (m + 2) ^ (2 ^ s) = wgen s m from rfl, um_w h]
    exact Subgroup.one_mem _

/- English proof (translation)
Introduce and unpack `x ⟨⟨e, k⟩, rfl⟩`. Rewrite using `[psi_apply]`. Establish `hA : ((iota (m + 2) e, 1, 1) : GalL (m + 2)) ∈ Subgroup.closure {((-1, 1, 1) : GalL (m + 2)), ((u5 (m + 2) ^ (2 ^ s), 1, 1) : GalL (m + 2))}`. Break down `Int.units_eq_one_or e with rfl | rfl` into its components or cases. Rewrite using `[iota_one]`.

Conclude with `Subgroup.one_mem _`. Rewrite using `[iota_neg]`. Conclude with `Subgroup.subset_closure (Set.mem_insert _ _)`. Establish `hB : ((wgen s m, 1, 1) : GalL (m + 2)) ∈ Subgroup.closure {((-1, 1, 1) : GalL (m + 2)), ((u5 (m + 2) ^ (2 ^ s), 1, 1) : GalL (m + 2))}` using `Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton_iff.2 rfl))`. Establish `heq : ((iota (m + 2) e * wgen s m ^ (Multiplicative.toAdd k).val, 1, 1) : GalL (m + 2)) = (iota (m + 2) e, 1, 1) * (wgen s m, 1, 1) ^ (Multiplicative.toAdd k).val`.

Rewrite using `[Prod.pow_mk, Prod.pow_mk, one_pow, Prod.mk_mul_mk, Prod.mk_mul_mk, mul_one]`. Rewrite using `[heq]`. Conclude with `Subgroup.mul_mem _ hA (Subgroup.pow_mem _ hB _)`.
-/
lemma range_le_closure {s m : ℕ} (h : s ≤ m) :
    (psi h).range ≤
      Subgroup.closure {((-1, 1, 1) : GalL (m + 2)), ((u5 (m + 2) ^ (2 ^ s), 1, 1) : GalL (m + 2))} := by
  rintro x ⟨⟨e, k⟩, rfl⟩
  rw [psi_apply]
  have hA : ((iota (m + 2) e, 1, 1) : GalL (m + 2)) ∈ Subgroup.closure
      {((-1, 1, 1) : GalL (m + 2)), ((u5 (m + 2) ^ (2 ^ s), 1, 1) : GalL (m + 2))} := by
    rcases Int.units_eq_one_or e with rfl | rfl
    · rw [iota_one]
      exact Subgroup.one_mem _
    · rw [iota_neg]
      exact Subgroup.subset_closure (Set.mem_insert _ _)
  have hB : ((wgen s m, 1, 1) : GalL (m + 2)) ∈ Subgroup.closure
      {((-1, 1, 1) : GalL (m + 2)), ((u5 (m + 2) ^ (2 ^ s), 1, 1) : GalL (m + 2))} :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton_iff.2 rfl))
  have heq : ((iota (m + 2) e * wgen s m ^ (Multiplicative.toAdd k).val, 1, 1) : GalL (m + 2))
      = (iota (m + 2) e, 1, 1) * (wgen s m, 1, 1) ^ (Multiplicative.toAdd k).val := by
    rw [Prod.pow_mk, Prod.pow_mk, one_pow, Prod.mk_mul_mk, Prod.mk_mul_mk, mul_one]
  rw [heq]
  exact Subgroup.mul_mem _ hA (Subgroup.pow_mem _ hB _)

/- English proof (translation)
Apply `Subgroup.eq_of_le_of_card_ge ((range_le_closure h).trans (closure_le_GG h))` to reduce the goal to its premises. Conclude with `le_of_eq (by rw [card_GG h, ← Nat.card_congr (MonoidHom.ofInjective (psi_inj h)).toEquiv, card_dom])`.
-/
lemma range_eq_GG {s m : ℕ} (h : s ≤ m) : (psi h).range = GG h := by
  apply Subgroup.eq_of_le_of_card_ge ((range_le_closure h).trans (closure_le_GG h))
  exact le_of_eq (by rw [card_GG h, ← Nat.card_congr (MonoidHom.ofInjective (psi_inj h)).toEquiv, card_dom])

/- English proof (translation)
Unfold `GGModel`. Introduce `s m h`. Use `⟨card_GG h, ⟨(MulEquiv.subgroupCongr (range_eq_GG h)).symm.trans (MonoidHom.ofInjective (psi_inj h)).symm⟩, le_antisymm ?_ (closure_le_GG h)⟩` and prove the remaining obligations. Rewrite using `[← range_eq_GG h]`. Conclude with `range_le_closure h`.
-/
theorem ggModel : GGModel := by
  unfold GGModel
  intro s m h
  refine ⟨card_GG h, ⟨(MulEquiv.subgroupCongr (range_eq_GG h)).symm.trans
    (MonoidHom.ofInjective (psi_inj h)).symm⟩, le_antisymm ?_ (closure_le_GG h)⟩
  rw [← range_eq_GG h]
  exact range_le_closure h

/- English proof (translation)
Unfold `GamEModel`. Introduce `s`. Use `⟨card_GamE s, ⟨eGamE s⟩, ?_, ?_⟩` and prove the remaining obligations. Unfold `JJ`. Rewrite using `[QuotientGroup.eq, mem_zpowers_sq gen_sq]`.

Use `right`. Simplify using the standard rewrite rules. Apply `orderOf_eq_prime` to reduce the goal to its premises. Rewrite using `[← QuotientGroup.mk_pow]`. Establish `hJ : JJ (s + 2) ^ 2 = 1`.

Unfold `JJ`. Rewrite using `[Prod.pow_mk, Prod.pow_mk, neg_one_sq, neg_one_sq]`. Apply the tactic sequence `all_goals rfl`. Rewrite using `[hJ, QuotientGroup.mk_one]`. Rewrite using `[Ne, QuotientGroup.eq_one_iff, mem_zpowers_sq gen_sq]`.

Unfold `JJ`. Apply the tactic sequence `rintro (h1 | h1) <;>`. Establish `h2 : (-1 : ℤˣ) = 1` using `congrArg (fun x : GalL (s + 2) => x.2.1) h1`. Conclude with `absurd h2 (by decide)`.
-/
theorem gamEModel : GamEModel := by
  unfold GamEModel
  intro s
  refine ⟨card_GamE s, ⟨eGamE s⟩, ?_, ?_⟩
  · unfold JJ
    rw [QuotientGroup.eq, mem_zpowers_sq gen_sq]
    right
    simp
  · apply orderOf_eq_prime
    · rw [← QuotientGroup.mk_pow]
      have hJ : JJ (s + 2) ^ 2 = 1 := by
        unfold JJ
        rw [Prod.pow_mk, Prod.pow_mk, neg_one_sq, neg_one_sq]
        all_goals rfl
      rw [hJ, QuotientGroup.mk_one]
    · rw [Ne, QuotientGroup.eq_one_iff, mem_zpowers_sq gen_sq]
      unfold JJ
      rintro (h1 | h1) <;>
      · have h2 : (-1 : ℤˣ) = 1 := congrArg (fun x : GalL (s + 2) => x.2.1) h1
        exact absurd h2 (by decide)

end Formalism.TwoAdicCyclotomicDecomposition
