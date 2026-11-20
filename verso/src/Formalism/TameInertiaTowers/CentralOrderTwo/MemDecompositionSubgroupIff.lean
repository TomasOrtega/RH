import Mathlib
import Formalism.TameInertiaTowers.StatementGroup

open Subgroup

namespace Formalism.TwoAdicCyclotomicDecomposition

namespace ModelEmbedding

/- English proof (translation)
Evaluate the decidable proposition.
-/
lemma neg_one_ne_one_int : (-1 : ℤˣ) ≠ 1 := by
  decide

/- English proof (translation)
Use `first`. Consider the case `(rw [Nat.card_eq_fintype_card, Fintype.card_units_int])`. Consider the case `rfl`. Consider the case `simp [Nat.card_eq_fintype_card]`.
-/
lemma card_units_int : Nat.card ℤˣ = 2 := by
  first
    | (rw [Nat.card_eq_fintype_card, Fintype.card_units_int])
    | rfl
    | simp [Nat.card_eq_fintype_card]

/- English proof (translation)
Use `haveI : NeZero (2 ^ n) := ⟨by positivity⟩`. Rewrite using `[Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime_pow Nat.prime_two (by omega)]`. Simplify using the standard rewrite rules.
-/
lemma card_unitsTwoPow (n : ℕ) (hn : 1 ≤ n) : Nat.card (ZMod (2 ^ n))ˣ = 2 ^ (n - 1) := by
  haveI : NeZero (2 ^ n) := ⟨by positivity⟩
  rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
    Nat.totient_prime_pow Nat.prime_two (by omega)]
  simp

/- English proof (translation)
Rewrite using `[Nat.card_prod, Nat.card_prod, card_unitsTwoPow n hn, card_units_int]`. Take `⟨m, rfl⟩ : ∃ m, n = m + 1` from `⟨n - 1, by omega⟩`. Rewrite using `[Nat.add_sub_cancel]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma card_GalL (n : ℕ) (hn : 1 ≤ n) : Nat.card (GalL n) = 2 ^ (n + 1) := by
  rw [Nat.card_prod, Nat.card_prod, card_unitsTwoPow n hn, card_units_int]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  ring

/- English proof (translation)
Introduce `h`. Conclude with `neg_one_ne_one_int (congrArg (fun g : GalL n => g.2.1) h)`.
-/
lemma JJ_ne_one (n : ℕ) : JJ n ≠ 1 := by
  intro h
  exact neg_one_ne_one_int (congrArg (fun g : GalL n => g.2.1) h)

/- English proof (translation)
Simplify using `[JJ]`.
-/
lemma JJ_mul_self (n : ℕ) : JJ n * JJ n = 1 := by
  simp [JJ]

/- English proof (translation)
The claim follows from `orderOf_eq_prime (by rw [sq]; exact JJ_mul_self n) (JJ_ne_one n)`.
-/
lemma orderOf_JJ (n : ℕ) : orderOf (JJ n) = 2 := orderOf_eq_prime (by rw [sq]; exact JJ_mul_self n) (JJ_ne_one n)

/- English proof (translation)
Take `⟨k, rfl⟩` from `mem_zpowers_iff.1 h`. Rewrite using `[← zpow_mod_orderOf, orderOf_JJ]`. Break down `Int.emod_two_eq_zero_or_one k with hk | hk` into its components or cases. Use `left`. Simplify using `[hk]`.

Use `right`. Simplify using `[hk]`.
-/
lemma mem_zpowers_JJ {n : ℕ} {g : GalL n} (h : g ∈ zpowers (JJ n)) : g = 1 ∨ g = JJ n := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 h
  rw [← zpow_mod_orderOf, orderOf_JJ]
  rcases Int.emod_two_eq_zero_or_one k with hk | hk
  · left; simp [hk]
  · right; simp [hk]

/- English proof (translation)
Use `first`. Consider the case `exact Iff.rfl`. Consider the case `simp [D2]`.
-/
lemma mem_decomposition_subgroup_iff {n : ℕ} {g : GalL n} : g ∈ D2 n ↔ g.2.2 = 1 := by
  first
    | exact Iff.rfl
    | simp [D2]

end ModelEmbedding

open ModelEmbedding

/- English proof (translation)
Introduce `n`. Establish `hJ : JJ n ∉ D2 n`. Rewrite using `[mem_decomposition_subgroup_iff, JJ]`. Conclude with `neg_one_ne_one_int`. Use `⟨hJ, ?_, ?_⟩` and prove the remaining obligations.

Establish `hs : Function.Surjective ((MonoidHom.snd ℤˣ ℤˣ).comp (MonoidHom.snd (ZMod (2 ^ n))ˣ (ℤˣ × ℤˣ)))` using `fun e => ⟨(1, 1, e), rfl⟩`. Rewrite using `[D2, Subgroup.index_ker, MonoidHom.range_eq_top.2 hs, Subgroup.card_top, card_units_int]`. Prove the components needed by the constructor for the conclusion. Introduce `x y hxy`. Establish `hxy' : (QuotientGroup.mk (x : GalL n) : GalL n ⧸ zpowers (JJ n)) = QuotientGroup.mk (y : GalL n)` using `hxy`.

Establish `h` using `QuotientGroup.eq.1 hxy'`. Break down `mem_zpowers_JJ h with h1 | h1` into its components or cases. Conclude with `Subtype.ext (inv_mul_eq_one.1 h1)`. It suffices to derive a contradiction. Apply `hJ` to reduce the goal to its premises.

Rewrite using `[← h1]`. Conclude with `(D2 n).mul_mem ((D2 n).inv_mem x.2) y.2`. Introduce `q`. Take `⟨g, rfl⟩` from `QuotientGroup.mk_surjective q`. Distinguish the cases in `hg : g ∈ D2 n`.

Conclude with `⟨⟨g, hg⟩, rfl⟩`. Use `⟨⟨g * JJ n, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite `hg`, the goal using `[mem_decomposition_subgroup_iff]`. Establish `h2 : g.2.2 = -1` using `(Int.units_eq_one_or _).resolve_left hg`. Simplify using `[JJ, h2]`.

Use `show (QuotientGroup.mk (g * JJ n) : GalL n ⧸ zpowers (JJ n)) = QuotientGroup.mk g`. Use `QuotientGroup.eq.2 ?_` and prove the remaining obligations. Rewrite using `[mul_inv_rev, inv_mul_cancel_right]`. Conclude with `inv_mem (mem_zpowers _)`.
-/
theorem decompModel : DecompModel := by
  intro n
  have hJ : JJ n ∉ D2 n := by
    rw [mem_decomposition_subgroup_iff, JJ]; exact neg_one_ne_one_int
  refine ⟨hJ, ?_, ?_⟩
  · have hs : Function.Surjective
        ((MonoidHom.snd ℤˣ ℤˣ).comp (MonoidHom.snd (ZMod (2 ^ n))ˣ (ℤˣ × ℤˣ))) :=
      fun e => ⟨(1, 1, e), rfl⟩
    rw [D2, Subgroup.index_ker, MonoidHom.range_eq_top.2 hs, Subgroup.card_top, card_units_int]
  · constructor
    · intro x y hxy
      have hxy' : (QuotientGroup.mk (x : GalL n) : GalL n ⧸ zpowers (JJ n)) =
          QuotientGroup.mk (y : GalL n) := hxy
      have h := QuotientGroup.eq.1 hxy'
      rcases mem_zpowers_JJ h with h1 | h1
      · exact Subtype.ext (inv_mul_eq_one.1 h1)
      · exfalso
        apply hJ
        rw [← h1]
        exact (D2 n).mul_mem ((D2 n).inv_mem x.2) y.2
    · intro q
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
      by_cases hg : g ∈ D2 n
      · exact ⟨⟨g, hg⟩, rfl⟩
      · refine ⟨⟨g * JJ n, ?_⟩, ?_⟩
        · rw [mem_decomposition_subgroup_iff] at hg ⊢
          have h2 : g.2.2 = -1 := (Int.units_eq_one_or _).resolve_left hg
          simp [JJ, h2]
        · show (QuotientGroup.mk (g * JJ n) : GalL n ⧸ zpowers (JJ n)) = QuotientGroup.mk g
          refine QuotientGroup.eq.2 ?_
          rw [mul_inv_rev, inv_mul_cancel_right]
          exact inv_mem (mem_zpowers _)

/- English proof (translation)
Introduce `n`. Use `⟨?_, ?_, Subgroup.mem_zpowers _, Subgroup.mem_zpowers _, ?_⟩` and prove the remaining obligations. Simplify using `[JJ]`. Rewrite using `[I2, MonoidHom.mem_ker]`. Both sides reduce to the same expression.

Introduce `h`. Conclude with `neg_one_ne_one_int (congrArg (fun g : GalL n => g.2.1) h)`.
-/
theorem genusModel : GenusModel := by
  intro n
  refine ⟨?_, ?_, Subgroup.mem_zpowers _, Subgroup.mem_zpowers _, ?_⟩
  · simp [JJ]
  · rw [I2, MonoidHom.mem_ker]; rfl
  · intro h
    exact neg_one_ne_one_int (congrArg (fun g : GalL n => g.2.1) h)

namespace ModelEmbedding

/- English proof (translation)
Take `⟨c, rfl⟩` from `hd`. Break down `c with _ | _ | c` into its components or cases. Simplify using `at hb`. Simplify using `at hne`. Use the polynomial consequences of the given equalities and inequalities.
-/
lemma two_mul_le_of_dvd_ne {a b : ℕ} (hb : 0 < b) (hd : a ∣ b) (hne : b ≠ a) : 2 * a ≤ b := by
  obtain ⟨c, rfl⟩ := hd
  rcases c with _ | _ | c
  · simp at hb
  · simp at hne
  · nlinarith

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => exact ⟨0, by norm_num⟩`. Consider the case `succ m ih`. Take `⟨t, ht⟩` from `ih`. Use `⟨t + 2 ^ m * (2 * t + 1) ^ 2, ?_⟩` and prove the remaining obligations.

Rewrite using `[pow_succ 2 m, pow_mul, ht]`. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma exists_five_pow_two_pow_eq_one_add (m : ℕ) : ∃ t : ℕ, 5 ^ (2 ^ m) = 1 + 2 ^ (m + 2) * (2 * t + 1) := by
  induction m with
  | zero => exact ⟨0, by norm_num⟩
  | succ m ih =>
    obtain ⟨t, ht⟩ := ih
    refine ⟨t + 2 ^ m * (2 * t + 1) ^ 2, ?_⟩
    rw [pow_succ 2 m, pow_mul, ht]
    ring

/- English proof (translation)
Establish `hpow : ∀ N j : ℕ, u5 N ^ j = 1 ↔ 5 ^ j ≡ 1 [MOD 2 ^ N]`. Introduce `N j`. Rewrite using `[← ZMod.natCast_eq_natCast_iff, Units.ext_iff]`. Simplify using `[u5]`. Consider the cases of `k with`.

Consider the case `zero`. Rewrite using `[pow_zero, orderOf_eq_one_iff, ← pow_one (u5 (0 + 2)), hpow]`. Evaluate the decidable proposition. Consider the case `succ m`. Apply `orderOf_eq_prime_pow` to reduce the goal to its premises.

Rewrite using `[hpow]`. Take `⟨t, ht⟩` from `exists_five_pow_two_pow_eq_one_add m`. Rewrite using `[ht]`. Introduce `h`. Establish `h2` using `(Nat.modEq_iff_dvd' (by omega)).1 h.symm`.

Rewrite `h2` using `[Nat.add_sub_cancel_left, show m + 1 + 2 = (m + 2) + 1 by ring, pow_succ]`. Establish `h3` using `Nat.dvd_of_mul_dvd_mul_left (by positivity) h2`. Use linear arithmetic over natural numbers and integers. Rewrite using `[hpow]`. Take `⟨t, ht⟩` from `exists_five_pow_two_pow_eq_one_add (m + 1)`.

Rewrite using `[ht]`. Conclude with `((Nat.modEq_iff_dvd' (by omega)).2 (by rw [Nat.add_sub_cancel_left]; exact dvd_mul_right _ _)).symm`.
-/
lemma orderOf_five_units_two_pow (k : ℕ) : orderOf (u5 (k + 2)) = 2 ^ k := by
  have hpow : ∀ N j : ℕ, u5 N ^ j = 1 ↔ 5 ^ j ≡ 1 [MOD 2 ^ N] := by
    intro N j
    rw [← ZMod.natCast_eq_natCast_iff, Units.ext_iff]
    simp [u5]
  cases k with
  | zero =>
    rw [pow_zero, orderOf_eq_one_iff, ← pow_one (u5 (0 + 2)), hpow]
    decide
  | succ m =>
    apply orderOf_eq_prime_pow
    · rw [hpow]
      obtain ⟨t, ht⟩ := exists_five_pow_two_pow_eq_one_add m
      rw [ht]
      intro h
      have h2 := (Nat.modEq_iff_dvd' (by omega)).1 h.symm
      rw [Nat.add_sub_cancel_left, show m + 1 + 2 = (m + 2) + 1 by ring, pow_succ] at h2
      have h3 := Nat.dvd_of_mul_dvd_mul_left (by positivity) h2
      omega
    · rw [hpow]
      obtain ⟨t, ht⟩ := exists_five_pow_two_pow_eq_one_add (m + 1)
      rw [ht]
      exact ((Nat.modEq_iff_dvd' (by omega)).2
        (by rw [Nat.add_sub_cancel_left]; exact dvd_mul_right _ _)).symm

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Use `first`. Consider the case `(rw [ZMod.unitsMap_def, Units.coe_map, u5, ZMod.coe_unitOfCoprime, MonoidHom.coe_coe, map_natCast] decide)`. Consider the case `(simp only [ZMod.unitsMap_def, Units.coe_map, u5, ZMod.coe_unitOfCoprime, MonoidHom.coe_coe, map_natCast] decide)`. Consider the case `(rw [ZMod.unitsMap_def, Units.coe_map, u5, ZMod.coe_unitOfCoprime, ZMod.castHom_apply, ZMod.cast_natCast h] decide)`.
-/
lemma unitsMap_five_mod_four (n : ℕ) (h : 4 ∣ 2 ^ n) : ZMod.unitsMap h (u5 n) = 1 := by
  apply Units.ext
  first
    | (rw [ZMod.unitsMap_def, Units.coe_map, u5, ZMod.coe_unitOfCoprime, MonoidHom.coe_coe, map_natCast]
       decide)
    | (simp only [ZMod.unitsMap_def, Units.coe_map, u5, ZMod.coe_unitOfCoprime, MonoidHom.coe_coe, map_natCast]
       decide)
    | (rw [ZMod.unitsMap_def, Units.coe_map, u5, ZMod.coe_unitOfCoprime, ZMod.castHom_apply, ZMod.cast_natCast h]
       decide)

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Simplify using `[ZMod.unitsMap_def]`.
-/
lemma unitsMap_neg_one (n m : ℕ) (h : m ∣ n) :
    ZMod.unitsMap h (-1 : (ZMod n)ˣ) = -1 := by
  apply Units.ext
  simp [ZMod.unitsMap_def]

/- English proof (translation)
Use `set H := Subgroup.closure {(-1 : (ZMod (2 ^ (k + 2)))ˣ), u5 (k + 2)} with hH`. Establish `hZ : zpowers (u5 (k + 2)) ≤ H` using `Subgroup.zpowers_le.2 (Subgroup.subset_closure (by simp))`. Establish `hm : (-1 : (ZMod (2 ^ (k + 2)))ˣ) ∈ H` using `Subgroup.subset_closure (by simp)`. Establish `h4 : 4 ∣ 2 ^ (k + 2)` using `⟨2 ^ k, by ring⟩`. Establish `hnot : (-1 : (ZMod (2 ^ (k + 2)))ˣ) ∉ zpowers (u5 (k + 2))`.

Introduce `hmem`. Take `⟨j, hj⟩` from `mem_zpowers_iff.1 hmem`. Establish `h1` using `congrArg (ZMod.unitsMap h4) hj`. Rewrite `h1` using `[map_zpow, unitsMap_five_mod_four, one_zpow, unitsMap_neg_one]`. Conclude with `absurd h1 (by decide)`.

Establish `hcardZ : Nat.card (zpowers (u5 (k + 2))) = 2 ^ k`. Rewrite using `[Nat.card_zpowers, orderOf_five_units_two_pow]`. Establish `hcardG : Nat.card (ZMod (2 ^ (k + 2)))ˣ = 2 ^ (k + 1)`. Rewrite using `[card_unitsTwoPow (k + 2) (by omega)]`. Simplify using the standard rewrite rules.

Establish `hdvd : Nat.card (zpowers (u5 (k + 2))) ∣ Nat.card H` using `Subgroup.card_dvd_of_le hZ`. Establish `hne : Nat.card H ≠ Nat.card (zpowers (u5 (k + 2)))`. Introduce `heq`. Establish `h2 : zpowers (u5 (k + 2)) = H` using `Subgroup.eq_of_le_of_card_ge hZ (le_of_eq heq)`. Conclude with `hnot (h2 ▸ hm)`.

Establish `hle` using `two_mul_le_of_dvd_ne Nat.card_pos hdvd hne`. Apply `Subgroup.eq_top_of_card_eq` to reduce the goal to its premises. Use `le_antisymm (Nat.le_of_dvd Nat.card_pos (Subgroup.card_subgroup_dvd_card H)) ?_` and prove the remaining obligations. Rewrite using `[hcardG, pow_succ]`. Rewrite `hle` using `[hcardZ]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma closure_units (k : ℕ) :
    Subgroup.closure {(-1 : (ZMod (2 ^ (k + 2)))ˣ), u5 (k + 2)} = ⊤ := by
  set H := Subgroup.closure {(-1 : (ZMod (2 ^ (k + 2)))ˣ), u5 (k + 2)} with hH
  have hZ : zpowers (u5 (k + 2)) ≤ H := Subgroup.zpowers_le.2 (Subgroup.subset_closure (by simp))
  have hm : (-1 : (ZMod (2 ^ (k + 2)))ˣ) ∈ H := Subgroup.subset_closure (by simp)
  have h4 : 4 ∣ 2 ^ (k + 2) := ⟨2 ^ k, by ring⟩
  have hnot : (-1 : (ZMod (2 ^ (k + 2)))ˣ) ∉ zpowers (u5 (k + 2)) := by
    intro hmem
    obtain ⟨j, hj⟩ := mem_zpowers_iff.1 hmem
    have h1 := congrArg (ZMod.unitsMap h4) hj
    rw [map_zpow, unitsMap_five_mod_four, one_zpow, unitsMap_neg_one] at h1
    exact absurd h1 (by decide)
  have hcardZ : Nat.card (zpowers (u5 (k + 2))) = 2 ^ k := by
    rw [Nat.card_zpowers, orderOf_five_units_two_pow]
  have hcardG : Nat.card (ZMod (2 ^ (k + 2)))ˣ = 2 ^ (k + 1) := by
    rw [card_unitsTwoPow (k + 2) (by omega)]
    simp
  have hdvd : Nat.card (zpowers (u5 (k + 2))) ∣ Nat.card H := Subgroup.card_dvd_of_le hZ
  have hne : Nat.card H ≠ Nat.card (zpowers (u5 (k + 2))) := by
    intro heq
    have h2 : zpowers (u5 (k + 2)) = H := Subgroup.eq_of_le_of_card_ge hZ (le_of_eq heq)
    exact hnot (h2 ▸ hm)
  have hle := two_mul_le_of_dvd_ne Nat.card_pos hdvd hne
  apply Subgroup.eq_top_of_card_eq
  refine le_antisymm (Nat.le_of_dvd Nat.card_pos (Subgroup.card_subgroup_dvd_card H)) ?_
  rw [hcardG, pow_succ]
  rw [hcardZ] at hle
  linarith

/- English proof (translation)
The claim follows from `orderOf_eq_prime (by rw [sq]; exact h) h1`.
-/
lemma orderOf_eq_two_of_mul_self_eq_one {n : ℕ} (g : GalL n) (h : g * g = 1) (h1 : g ≠ 1) : orderOf g = 2 := orderOf_eq_prime (by rw [sq]; exact h) h1

end ModelEmbedding

open ModelEmbedding

/- English proof (translation)
Introduce `n hn`. Take `⟨k, rfl⟩ : ∃ k, n = k + 2` from `⟨n - 2, by omega⟩`. Establish `hI2 : I2 (k + 2) = Subgroup.closure {((-1, 1, 1) : GalL (k + 2)), ((u5 (k + 2), 1, 1) : GalL (k + 2))}`. Establish `h1 : I2 (k + 2) = (⊤ : Subgroup (ZMod (2 ^ (k + 2)))ˣ).map (MonoidHom.inl (ZMod (2 ^ (k + 2)))ˣ (ℤˣ × ℤˣ))`. Use extensionality with `g`.

Rewrite using `[I2, MonoidHom.mem_ker, Subgroup.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `⟨g.1, Subgroup.mem_top _, Prod.ext rfl h.symm⟩`. Introduce and unpack `⟨u, _, rfl⟩`.

Both sides reduce to the same expression. Rewrite using `[h1, ← closure_units k, MonoidHom.map_closure, Set.image_pair]`. Both sides reduce to the same expression. Establish `hsup : I2 (k + 2) ⊔ Iq (k + 2) ⊔ Id (k + 2) = ⊤`. Use `eq_top_iff.2 fun g _ => ?_` and prove the remaining obligations.

Establish `hg : g = (g.1, 1, 1) * (1, g.2.1, 1) * (1, 1, g.2.2)` using `Prod.ext (by simp) (Prod.ext (by simp) (by simp))`. Rewrite using `[hg]`. Use `Subgroup.mul_mem_sup (Subgroup.mul_mem_sup ?_ ?_) ?_` and prove the remaining obligations. Rewrite using `[I2, MonoidHom.mem_ker]`. Both sides reduce to the same expression.

Apply the tactic sequence `rcases Int.units_eq_one_or g.2.1 with h | h <;> rw [h]`. Conclude with `Subgroup.one_mem _`. Conclude with `Subgroup.mem_zpowers _`. Apply the tactic sequence `rcases Int.units_eq_one_or g.2.2 with h | h <;> rw [h]`. Conclude with `Subgroup.one_mem _`.

Conclude with `Subgroup.mem_zpowers _`. Establish `hq2 : orderOf ((1, -1, 1) : GalL (k + 2)) = 2` using `orderOf_eq_two_of_mul_self_eq_one _ (by simp) (fun h => neg_one_ne_one_int (congrArg (fun g : GalL (k + 2) => g.2.1) h))`. Establish `hd2 : orderOf ((1, 1, -1) : GalL (k + 2)) = 2` using `orderOf_eq_two_of_mul_self_eq_one _ (by simp) (fun h => neg_one_ne_one_int (congrArg (fun g : GalL (k + 2) => g.2.2) h))`. Use `⟨hsup, hI2, by rw [Iq, Nat.card_zpowers, hq2], by rw [Id, Nat.card_zpowers, hd2], ?_⟩` and prove the remaining obligations. Rewrite using `[eq_top_iff, ← hsup]`.

Use `sup_le (sup_le ?_ ?_) ?_` and prove the remaining obligations. Rewrite using `[hI2]`. Apply `Subgroup.closure_mono` to reduce the goal to its premises. Introduce `x hx`. Simplify using `only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢`.

The claim follows by propositional logic. Rewrite using `[Iq]; exact Subgroup.zpowers_le.2 (Subgroup.subset_closure (by simp))`. Rewrite using `[Id]; exact Subgroup.zpowers_le.2 (Subgroup.subset_closure (by simp))`.
-/
theorem gensModel : GensModel := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  have hI2 : I2 (k + 2) = Subgroup.closure {((-1, 1, 1) : GalL (k + 2)), ((u5 (k + 2), 1, 1) : GalL (k + 2))} := by
    have h1 : I2 (k + 2) =
        (⊤ : Subgroup (ZMod (2 ^ (k + 2)))ˣ).map (MonoidHom.inl (ZMod (2 ^ (k + 2)))ˣ (ℤˣ × ℤˣ)) := by
      ext g
      rw [I2, MonoidHom.mem_ker, Subgroup.mem_map]
      constructor
      · intro h; exact ⟨g.1, Subgroup.mem_top _, Prod.ext rfl h.symm⟩
      · rintro ⟨u, _, rfl⟩; rfl
    rw [h1, ← closure_units k, MonoidHom.map_closure, Set.image_pair]
    rfl
  have hsup : I2 (k + 2) ⊔ Iq (k + 2) ⊔ Id (k + 2) = ⊤ := by
    refine eq_top_iff.2 fun g _ => ?_
    have hg : g = (g.1, 1, 1) * (1, g.2.1, 1) * (1, 1, g.2.2) :=
      Prod.ext (by simp) (Prod.ext (by simp) (by simp))
    rw [hg]
    refine Subgroup.mul_mem_sup (Subgroup.mul_mem_sup ?_ ?_) ?_
    · rw [I2, MonoidHom.mem_ker]; rfl
    · rcases Int.units_eq_one_or g.2.1 with h | h <;> rw [h]
      · exact Subgroup.one_mem _
      · exact Subgroup.mem_zpowers _
    · rcases Int.units_eq_one_or g.2.2 with h | h <;> rw [h]
      · exact Subgroup.one_mem _
      · exact Subgroup.mem_zpowers _
  have hq2 : orderOf ((1, -1, 1) : GalL (k + 2)) = 2 :=
    orderOf_eq_two_of_mul_self_eq_one _ (by simp)
      (fun h => neg_one_ne_one_int (congrArg (fun g : GalL (k + 2) => g.2.1) h))
  have hd2 : orderOf ((1, 1, -1) : GalL (k + 2)) = 2 :=
    orderOf_eq_two_of_mul_self_eq_one _ (by simp)
      (fun h => neg_one_ne_one_int (congrArg (fun g : GalL (k + 2) => g.2.2) h))
  refine ⟨hsup, hI2, by rw [Iq, Nat.card_zpowers, hq2], by rw [Id, Nat.card_zpowers, hd2], ?_⟩
  rw [eq_top_iff, ← hsup]
  refine sup_le (sup_le ?_ ?_) ?_
  · rw [hI2]
    apply Subgroup.closure_mono
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    tauto
  · rw [Iq]; exact Subgroup.zpowers_le.2 (Subgroup.subset_closure (by simp))
  · rw [Id]; exact Subgroup.zpowers_le.2 (Subgroup.subset_closure (by simp))

namespace ModelEmbedding

/- English proof (translation)
Establish `h` using `Subgroup.card_eq_card_quotient_mul_card_subgroup (zpowers (JJ n))`. Rewrite `h` using `[card_GalL n hn, Nat.card_zpowers, orderOf_JJ, pow_succ]`. Conclude with `(Nat.eq_of_mul_eq_mul_right (by norm_num) h).symm`.
-/
lemma card_Q (n : ℕ) (hn : 1 ≤ n) : Nat.card (GalL n ⧸ zpowers (JJ n)) = 2 ^ n := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (zpowers (JJ n))
  rw [card_GalL n hn, Nat.card_zpowers, orderOf_JJ, pow_succ] at h
  exact (Nat.eq_of_mul_eq_mul_right (by norm_num) h).symm

def KK (n : ℕ) : Subgroup (GalL n) :=
  (powMonoidHom 2 : (GalL n ⧸ zpowers (JJ n)) →* _).range.comap
    (QuotientGroup.mk' (zpowers (JJ n)))

/- English proof (translation)
Rewrite using `[KK, Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective _)]`. Both sides reduce to the same expression.
-/
lemma card_QQ (n : ℕ) :
    Nat.card ((GalL n ⧸ zpowers (JJ n)) ⧸
      (powMonoidHom 2 : (GalL n ⧸ zpowers (JJ n)) →* _).range) = (KK n).index := by
  rw [KK, Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective _)]
  rfl

/- English proof (translation)
Rewrite using `[KK, Subgroup.mem_comap, MonoidHom.mem_range]`. Conclude with `⟨QuotientGroup.mk' _ g, by rw [powMonoidHom_apply, map_pow]⟩`.
-/
lemma sq_mem_KK {n : ℕ} (g : GalL n) : g ^ 2 ∈ KK n := by
  rw [KK, Subgroup.mem_comap, MonoidHom.mem_range]
  exact ⟨QuotientGroup.mk' _ g, by rw [powMonoidHom_apply, map_pow]⟩

/- English proof (translation)
Rewrite using `[KK, Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_zpowers _)]`. Conclude with `Subgroup.one_mem _`.
-/
lemma JJ_mem_KK (n : ℕ) : JJ n ∈ KK n := by
  rw [KK, Subgroup.mem_comap, QuotientGroup.mk'_apply,
    (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_zpowers _)]
  exact Subgroup.one_mem _

/- English proof (translation)
Rewrite using `[unitsMap_neg_one]`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[MulChar.coe_toUnitHom]`. Apply the tactic sequence `first | rfl | decide | simp | (simp; decide)`.
-/
private lemma chi4_unitsMap_neg_one_eq_neg_one {N : ℕ} (h : 4 ∣ N) :
    ZMod.χ₄.toUnitHom (ZMod.unitsMap h (-1 : (ZMod N)ˣ)) = -1 := by
  rw [unitsMap_neg_one]
  apply Units.ext
  rw [MulChar.coe_toUnitHom]
  first | rfl | decide | simp | (simp; decide)

/- English proof (translation)
Rewrite using `[unitsMap_neg_one]`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[MulChar.coe_toUnitHom]`. Apply the tactic sequence `first | rfl | decide | simp | (simp; decide)`.
-/
private lemma chi8_unitsMap_neg_one_eq_one {N : ℕ} (h : 8 ∣ N) :
    ZMod.χ₈.toUnitHom (ZMod.unitsMap h (-1 : (ZMod N)ˣ)) = 1 := by
  rw [unitsMap_neg_one]
  apply Units.ext
  rw [MulChar.coe_toUnitHom]
  first | rfl | decide | simp | (simp; decide)

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[MulChar.coe_toUnitHom]`. Establish `h5 : ((ZMod.unitsMap h (u5 (k + 3)) : (ZMod 8)ˣ) : ZMod 8) = 5` using `by first`. Consider the case `(rw [ZMod.unitsMap_def, Units.coe_map, u5, ZMod.coe_unitOfCoprime, MonoidHom.coe_coe, map_natCast]; rfl)`. Consider the case `(simp only [ZMod.unitsMap_def, Units.coe_map, u5, ZMod.coe_unitOfCoprime, MonoidHom.coe_coe, map_natCast]; rfl)`.

Consider the case `(rw [ZMod.unitsMap_def, Units.coe_map, u5, ZMod.coe_unitOfCoprime, ZMod.castHom_apply, ZMod.cast_natCast h]; rfl)`. Rewrite using `[h5]`. Apply the tactic sequence `first | rfl | decide`.
-/
private lemma chi8_unitsMap_u5_eq_neg_one (k : ℕ) (h : 8 ∣ 2 ^ (k + 3)) :
    ZMod.χ₈.toUnitHom (ZMod.unitsMap h (u5 (k + 3))) = -1 := by
  apply Units.ext
  rw [MulChar.coe_toUnitHom]
  have h5 : ((ZMod.unitsMap h (u5 (k + 3)) : (ZMod 8)ˣ) : ZMod 8) = 5 := by
    first
      | (rw [ZMod.unitsMap_def, Units.coe_map, u5, ZMod.coe_unitOfCoprime, MonoidHom.coe_coe, map_natCast]; rfl)
      | (simp only [ZMod.unitsMap_def, Units.coe_map, u5, ZMod.coe_unitOfCoprime, MonoidHom.coe_coe, map_natCast]; rfl)
      | (rw [ZMod.unitsMap_def, Units.coe_map, u5, ZMod.coe_unitOfCoprime, ZMod.castHom_apply, ZMod.cast_natCast h]; rfl)
  rw [h5]
  first | rfl | decide

/- English proof (translation)
Establish `h4 : 4 ∣ 2 ^ (k + 3)` using `⟨2 ^ (k + 1), by ring⟩`. Establish `h8 : 8 ∣ 2 ^ (k + 3)` using `⟨2 ^ k, by ring⟩`. Take `⟨c4, hc4a, hc4b⟩ : ∃ c : (ZMod (2 ^ (k + 3)))ˣ →* ℤˣ, c (-1) = -1 ∧ c (u5 (k + 3)) = 1` from `⟨ZMod.χ₄.toUnitHom.comp (ZMod.unitsMap h4), chi4_unitsMap_neg_one_eq_neg_one h4, by`. Rewrite using `[MonoidHom.comp_apply, unitsMap_five_mod_four, map_one]⟩`. Take `⟨c8, hc8a, hc8b⟩ : ∃ c : (ZMod (2 ^ (k + 3)))ˣ →* ℤˣ, c (-1) = 1 ∧ c (u5 (k + 3)) = -1` from `⟨ZMod.χ₈.toUnitHom.comp (ZMod.unitsMap h8), chi8_unitsMap_neg_one_eq_one h8, chi8_unitsMap_u5_eq_neg_one k h8⟩`.

Take `⟨φ, hφ⟩ : ∃ φ : GalL (k + 3) →* ℤˣ × ℤˣ × ℤˣ, ∀ g : GalL (k + 3), φ g = (c4 g.1 * g.2.1, c8 g.1, g.2.1 * g.2.2)` from `⟨MonoidHom.mk' (fun g => (c4 g.1 * g.2.1, c8 g.1, g.2.1 * g.2.2)) (by`. Introduce `a b`. Use `Prod.ext ?_ (Prod.ext ?_ ?_)` and prove the remaining obligations. Use `show c4 (a.1 * b.1) * (a.2.1 * b.2.1) = (c4 a.1 * a.2.1) * (c4 b.1 * b.2.1)`. Rewrite using `[map_mul, mul_mul_mul_comm]`.

Use `show c8 (a.1 * b.1) = c8 a.1 * c8 b.1`. Rewrite using `[map_mul]`. Use `show (a.2.1 * b.2.1) * (a.2.2 * b.2.2) = (a.2.1 * a.2.2) * (b.2.1 * b.2.2)`. Rewrite using `[mul_mul_mul_comm]), fun g => rfl⟩`. Establish `hker : φ.ker ≤ KK (k + 3)`.

Introduce and unpack `⟨u, e1, e2⟩ hg`. Rewrite `hg` using `[MonoidHom.mem_ker, hφ]`. Simplify using `only [Prod.mk_eq_one] at hg`. Take `⟨hg1, hg2, hg3⟩` from `hg`. Establish `hu : u ∈ Subgroup.closure {(-1 : (ZMod (2 ^ (k + 3)))ˣ), u5 (k + 3)}`.

Establish `hc : Subgroup.closure {(-1 : (ZMod (2 ^ (k + 3)))ˣ), u5 (k + 3)} = ⊤` using `closure_units (k + 1)`. Rewrite using `[hc]`. Conclude with `Subgroup.mem_top u`. Take `⟨m, n, rfl⟩` from `Subgroup.mem_closure_pair.1 hu`. Rewrite `hg2` using `[map_mul, map_zpow, map_zpow, hc8a, hc8b, one_zpow, one_mul]`.

Rewrite `hg1` using `[map_mul, map_zpow, map_zpow, hc4a, hc4b, one_zpow, mul_one]`. Break down `Int.even_or_odd n with hn | hn` into its components or cases. Use `swap`. It suffices to derive a contradiction. Rewrite `hg2` using `[hn.neg_one_zpow]`.

Conclude with `neg_one_ne_one_int hg2`. Take `⟨r, rfl⟩` from `hn`. Establish `hsq : ∀ s : ℤ, (((-1 : (ZMod (2 ^ (k + 3)))ˣ) ^ (s + s) * u5 (k + 3) ^ (r + r), (1 : ℤˣ), (1 : ℤˣ)) : GalL (k + 3)) ∈ KK (k + 3)`. Introduce `s`. Establish `key : (((-1 : (ZMod (2 ^ (k + 3)))ˣ) ^ (s + s) * u5 (k + 3) ^ (r + r), (1 : ℤˣ), (1 : ℤˣ)) : GalL (k + 3)) = ((-1) ^ s * u5 (k + 3) ^ r, 1, 1) ^ 2`.

Rewrite using `[sq, zpow_add, zpow_add]`. Simplify using `only [Prod.mk_mul_mk, mul_one]`. Rewrite using `[mul_mul_mul_comm]`. Rewrite using `[key]`. Conclude with `sq_mem_KK _`.

Break down `Int.even_or_odd m with hm | hm` into its components or cases. Rewrite `hg1` using `[hm.neg_one_zpow, one_mul]`. Substitute `hg1` using the available equality. Rewrite `hg3` using `[one_mul]`. Substitute `hg3` using the available equality.

Take `⟨s, rfl⟩` from `hm`. Conclude with `hsq s`. Rewrite `hg1` using `[hm.neg_one_zpow, neg_one_mul, neg_eq_iff_eq_neg]`. Substitute `hg1` using the available equality. Rewrite `hg3` using `[neg_one_mul, neg_eq_iff_eq_neg]`.

Substitute `hg3` using the available equality. Take `⟨s, rfl⟩` from `hm`. Establish `key2 : (((-1 : (ZMod (2 ^ (k + 3)))ˣ) ^ (2 * s + 1) * u5 (k + 3) ^ (r + r), (-1 : ℤˣ), (-1 : ℤˣ)) : GalL (k + 3)) = JJ (k + 3) * ((-1) ^ (s + s) * u5 (k + 3) ^ (r + r), 1, 1)`. Rewrite using `[JJ]`. Simplify using `only [Prod.mk_mul_mk, mul_one]`.

Rewrite using `[two_mul, zpow_add_one, mul_comm ((-1 : (ZMod (2 ^ (k + 3)))ˣ) ^ (s + s)) (-1), mul_assoc]`. Rewrite using `[key2]`. Conclude with `(KK (k + 3)).mul_mem (JJ_mem_KK _) (hsq s)`. Establish `hφle : φ.ker.index ≤ 8`. Rewrite using `[Subgroup.index_ker]`.

Combine the equalities or inequalities in the displayed calculation. Conclude with `(Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) (Subgroup.index_dvd_of_le hker)).trans hφle`.
-/
lemma index_KK_le (k : ℕ) : (KK (k + 3)).index ≤ 8 := by
  have h4 : 4 ∣ 2 ^ (k + 3) := ⟨2 ^ (k + 1), by ring⟩
  have h8 : 8 ∣ 2 ^ (k + 3) := ⟨2 ^ k, by ring⟩
  obtain ⟨c4, hc4a, hc4b⟩ : ∃ c : (ZMod (2 ^ (k + 3)))ˣ →* ℤˣ, c (-1) = -1 ∧ c (u5 (k + 3)) = 1 :=
    ⟨ZMod.χ₄.toUnitHom.comp (ZMod.unitsMap h4), chi4_unitsMap_neg_one_eq_neg_one h4, by
      rw [MonoidHom.comp_apply, unitsMap_five_mod_four, map_one]⟩
  obtain ⟨c8, hc8a, hc8b⟩ : ∃ c : (ZMod (2 ^ (k + 3)))ˣ →* ℤˣ, c (-1) = 1 ∧ c (u5 (k + 3)) = -1 :=
    ⟨ZMod.χ₈.toUnitHom.comp (ZMod.unitsMap h8), chi8_unitsMap_neg_one_eq_one h8, chi8_unitsMap_u5_eq_neg_one k h8⟩
  obtain ⟨φ, hφ⟩ : ∃ φ : GalL (k + 3) →* ℤˣ × ℤˣ × ℤˣ,
      ∀ g : GalL (k + 3), φ g = (c4 g.1 * g.2.1, c8 g.1, g.2.1 * g.2.2) :=
    ⟨MonoidHom.mk' (fun g => (c4 g.1 * g.2.1, c8 g.1, g.2.1 * g.2.2)) (by
      intro a b
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · show c4 (a.1 * b.1) * (a.2.1 * b.2.1) = (c4 a.1 * a.2.1) * (c4 b.1 * b.2.1)
        rw [map_mul, mul_mul_mul_comm]
      · show c8 (a.1 * b.1) = c8 a.1 * c8 b.1
        rw [map_mul]
      · show (a.2.1 * b.2.1) * (a.2.2 * b.2.2) = (a.2.1 * a.2.2) * (b.2.1 * b.2.2)
        rw [mul_mul_mul_comm]), fun g => rfl⟩
  have hker : φ.ker ≤ KK (k + 3) := by
    rintro ⟨u, e1, e2⟩ hg
    rw [MonoidHom.mem_ker, hφ] at hg
    simp only [Prod.mk_eq_one] at hg
    obtain ⟨hg1, hg2, hg3⟩ := hg
    have hu : u ∈ Subgroup.closure {(-1 : (ZMod (2 ^ (k + 3)))ˣ), u5 (k + 3)} := by
      have hc : Subgroup.closure {(-1 : (ZMod (2 ^ (k + 3)))ˣ), u5 (k + 3)} = ⊤ :=
        closure_units (k + 1)
      rw [hc]; exact Subgroup.mem_top u
    obtain ⟨m, n, rfl⟩ := Subgroup.mem_closure_pair.1 hu
    rw [map_mul, map_zpow, map_zpow, hc8a, hc8b, one_zpow, one_mul] at hg2
    rw [map_mul, map_zpow, map_zpow, hc4a, hc4b, one_zpow, mul_one] at hg1
    rcases Int.even_or_odd n with hn | hn
    swap
    · exfalso; rw [hn.neg_one_zpow] at hg2; exact neg_one_ne_one_int hg2
    obtain ⟨r, rfl⟩ := hn
    have hsq : ∀ s : ℤ, (((-1 : (ZMod (2 ^ (k + 3)))ˣ) ^ (s + s) * u5 (k + 3) ^ (r + r),
        (1 : ℤˣ), (1 : ℤˣ)) : GalL (k + 3)) ∈ KK (k + 3) := by
      intro s
      have key : (((-1 : (ZMod (2 ^ (k + 3)))ˣ) ^ (s + s) * u5 (k + 3) ^ (r + r),
          (1 : ℤˣ), (1 : ℤˣ)) : GalL (k + 3)) = ((-1) ^ s * u5 (k + 3) ^ r, 1, 1) ^ 2 := by
        rw [sq, zpow_add, zpow_add]
        simp only [Prod.mk_mul_mk, mul_one]
        rw [mul_mul_mul_comm]
      rw [key]; exact sq_mem_KK _
    rcases Int.even_or_odd m with hm | hm
    · rw [hm.neg_one_zpow, one_mul] at hg1
      subst hg1
      rw [one_mul] at hg3
      subst hg3
      obtain ⟨s, rfl⟩ := hm
      exact hsq s
    · rw [hm.neg_one_zpow, neg_one_mul, neg_eq_iff_eq_neg] at hg1
      subst hg1
      rw [neg_one_mul, neg_eq_iff_eq_neg] at hg3
      subst hg3
      obtain ⟨s, rfl⟩ := hm
      have key2 : (((-1 : (ZMod (2 ^ (k + 3)))ˣ) ^ (2 * s + 1) * u5 (k + 3) ^ (r + r),
          (-1 : ℤˣ), (-1 : ℤˣ)) : GalL (k + 3)) =
          JJ (k + 3) * ((-1) ^ (s + s) * u5 (k + 3) ^ (r + r), 1, 1) := by
        rw [JJ]
        simp only [Prod.mk_mul_mk, mul_one]
        rw [two_mul, zpow_add_one, mul_comm ((-1 : (ZMod (2 ^ (k + 3)))ˣ) ^ (s + s)) (-1), mul_assoc]
      rw [key2]
      exact (KK (k + 3)).mul_mem (JJ_mem_KK _) (hsq s)
  have hφle : φ.ker.index ≤ 8 := by
    rw [Subgroup.index_ker]
    calc Nat.card φ.range ≤ Nat.card (ℤˣ × ℤˣ × ℤˣ) :=
          Nat.card_le_card_of_injective _ Subtype.val_injective
      _ = 8 := by rw [Nat.card_prod, Nat.card_prod, card_units_int]
  exact (Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
    (Subgroup.index_dvd_of_le hker)).trans hφle

/- English proof (translation)
Assemble the required witnesses or components as `⟨2 ^ (k + 1), by ring⟩`.
-/
lemma h4dvd (k : ℕ) : 4 ∣ 2 ^ (k + 3) := ⟨2 ^ (k + 1), by ring⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨2 ^ k, by ring⟩`.
-/
lemma h8dvd (k : ℕ) : 8 ∣ 2 ^ (k + 3) := ⟨2 ^ k, by ring⟩

def chi4 (k : ℕ) : (ZMod (2 ^ (k + 3)))ˣ →* ℤˣ :=
  ZMod.χ₄.toUnitHom.comp (ZMod.unitsMap (h4dvd k))

def chi8 (k : ℕ) : (ZMod (2 ^ (k + 3)))ˣ →* ℤˣ :=
  ZMod.χ₈.toUnitHom.comp (ZMod.unitsMap (h8dvd k))

/- English proof (translation)
Rewrite using `[chi4, MonoidHom.comp_apply]`. Conclude with `chi4_unitsMap_neg_one_eq_neg_one _`.
-/
lemma mod_four_character_neg_one (k : ℕ) : chi4 k (-1) = -1 := by
  rw [chi4, MonoidHom.comp_apply]
  exact chi4_unitsMap_neg_one_eq_neg_one _

/- English proof (translation)
Rewrite using `[chi8, MonoidHom.comp_apply]`. Conclude with `chi8_unitsMap_neg_one_eq_one _`.
-/
lemma mod_eight_character_neg_one (k : ℕ) : chi8 k (-1) = 1 := by
  rw [chi8, MonoidHom.comp_apply]
  exact chi8_unitsMap_neg_one_eq_one _

/- English proof (translation)
Rewrite using `[chi4, MonoidHom.comp_apply, unitsMap_five_mod_four, map_one]`.
-/
lemma mod_four_character_five (k : ℕ) : chi4 k (u5 (k + 3)) = 1 := by
  rw [chi4, MonoidHom.comp_apply, unitsMap_five_mod_four, map_one]

/- English proof (translation)
Rewrite using `[chi8, MonoidHom.comp_apply]`. Conclude with `chi8_unitsMap_u5_eq_neg_one k _`.
-/
lemma mod_eight_character_five (k : ℕ) : chi8 k (u5 (k + 3)) = -1 := by
  rw [chi8, MonoidHom.comp_apply]
  exact chi8_unitsMap_u5_eq_neg_one k _

def psi (k : ℕ) : GalL (k + 3) →* ℤˣ × ℤˣ × ℤˣ :=
  MonoidHom.mk' (fun g => (chi4 k g.1 * g.2.1, chi8 k g.1, g.2.1 * g.2.2)) (by
    intro a b
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · show chi4 k (a.1 * b.1) * (a.2.1 * b.2.1) = (chi4 k a.1 * a.2.1) * (chi4 k b.1 * b.2.1)
      rw [map_mul, mul_mul_mul_comm]
    · show chi8 k (a.1 * b.1) = chi8 k a.1 * chi8 k b.1
      rw [map_mul]
    · show (a.2.1 * b.2.1) * (a.2.2 * b.2.2) = (a.2.1 * a.2.2) * (b.2.1 * b.2.2)
      rw [mul_mul_mul_comm])

/- English proof (translation)
Simplify using `[psi, JJ, mod_four_character_neg_one, mod_eight_character_neg_one]`.
-/
lemma psi_JJ (k : ℕ) : psi k (JJ (k + 3)) = 1 := by
  simp [psi, JJ, mod_four_character_neg_one, mod_eight_character_neg_one]

/- English proof (translation)
Introduce and unpack `⟨a, b, c⟩`. Break down `Int.units_eq_one_or b with rfl | rfl` into its components or cases. Use `⟨(1, a, a * c), ?_⟩` and prove the remaining obligations. Simplify using `[psi, ← mul_assoc, Int.units_mul_self]`. Use `⟨(u5 (k + 3), a, a * c), ?_⟩` and prove the remaining obligations.

Simplify using `[psi, mod_four_character_five, mod_eight_character_five, ← mul_assoc, Int.units_mul_self]`.
-/
lemma psi_surj (k : ℕ) : Function.Surjective (psi k) := by
  rintro ⟨a, b, c⟩
  rcases Int.units_eq_one_or b with rfl | rfl
  · refine ⟨(1, a, a * c), ?_⟩
    simp [psi, ← mul_assoc, Int.units_mul_self]
  · refine ⟨(u5 (k + 3), a, a * c), ?_⟩
    simp [psi, mod_four_character_five, mod_eight_character_five, ← mul_assoc, Int.units_mul_self]

/- English proof (translation)
Rewrite using `[Subgroup.index_ker, MonoidHom.range_eq_top.2 (psi_surj k), Subgroup.card_top, Nat.card_prod, Nat.card_prod, card_units_int]`.
-/
lemma index_ker_psi (k : ℕ) : (psi k).ker.index = 8 := by
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 (psi_surj k), Subgroup.card_top,
    Nat.card_prod, Nat.card_prod, card_units_int]

/- English proof (translation)
Introduce `g hg`. Rewrite `hg` using `[KK, Subgroup.mem_comap, MonoidHom.mem_range]`. Take `⟨q, hq⟩` from `hg`. Take `⟨h, rfl⟩` from `QuotientGroup.mk'_surjective (zpowers (JJ (k + 3))) q`. Establish `hq' : ((h ^ 2 : GalL (k + 3)) : GalL (k + 3) ⧸ zpowers (JJ (k + 3))) = g`.

Rewrite using `[QuotientGroup.mk_pow]`. Simplify using `using hq`. Establish `hm` using `QuotientGroup.eq.1 hq'`. Establish `hsq : ∀ x : ℤˣ × ℤˣ × ℤˣ, x ^ 2 = 1` using `fun x => Prod.ext (by simp [Int.units_sq]) (Prod.ext (by simp [Int.units_sq]) (by simp [Int.units_sq]))`. Rewrite using `[MonoidHom.mem_ker]`.

Break down `mem_zpowers_JJ hm with h1 | h1` into its components or cases. Rewrite using `[← inv_mul_eq_one.1 h1, map_pow, hsq]`. Rewrite using `[inv_mul_eq_iff_eq_mul.1 h1, map_mul, map_pow, hsq, psi_JJ, one_mul]`.
-/
lemma KK_le_ker (k : ℕ) : KK (k + 3) ≤ (psi k).ker := by
  intro g hg
  rw [KK, Subgroup.mem_comap, MonoidHom.mem_range] at hg
  obtain ⟨q, hq⟩ := hg
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (zpowers (JJ (k + 3))) q
  have hq' : ((h ^ 2 : GalL (k + 3)) : GalL (k + 3) ⧸ zpowers (JJ (k + 3))) = g := by
    rw [QuotientGroup.mk_pow]; simpa using hq
  have hm := QuotientGroup.eq.1 hq'
  have hsq : ∀ x : ℤˣ × ℤˣ × ℤˣ, x ^ 2 = 1 := fun x =>
    Prod.ext (by simp [Int.units_sq]) (Prod.ext (by simp [Int.units_sq]) (by simp [Int.units_sq]))
  rw [MonoidHom.mem_ker]
  rcases mem_zpowers_JJ hm with h1 | h1
  · rw [← inv_mul_eq_one.1 h1, map_pow, hsq]
  · rw [inv_mul_eq_iff_eq_mul.1 h1, map_mul, map_pow, hsq, psi_JJ, one_mul]

end ModelEmbedding

open ModelEmbedding

/- English proof (translation)
Introduce `n hn`. Establish `hQ` using `card_Q n hn`. Establish `hle : Nat.card ((GalL n ⧸ Subgroup.zpowers (JJ n)) ⧸ (powMonoidHom 2 : (GalL n ⧸ Subgroup.zpowers (JJ n)) →* _).range) ≤ Nat.card (GalL n ⧸ Subgroup.zpowers (JJ n))` using `Nat.le_of_dvd Nat.card_pos (Subgroup.index_dvd_card _)`. Establish `h8 : 3 ≤ n → Nat.card ((GalL n ⧸ Subgroup.zpowers (JJ n)) ⧸ (powMonoidHom 2 : (GalL n ⧸ Subgroup.zpowers (JJ n)) →* _).range) = 8`. Introduce `h3`.

Take `⟨m, rfl⟩ : ∃ m, n = m + 3` from `⟨n - 3, by omega⟩`. Rewrite using `[card_QQ]`. Use `le_antisymm (index_KK_le m) ?_` and prove the remaining obligations. Establish `hd : (psi m).ker.index ∣ (KK (m + 3)).index` using `Subgroup.index_dvd_of_le (KK_le_ker m)`. Rewrite `hd` using `[index_ker_psi]`.

Conclude with `Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) hd`. Use `⟨hQ, ?_, h8⟩` and prove the remaining obligations. Break down `(by omega : n ≤ 2 ∨ 3 ≤ n) with h | h` into its components or cases. Use `hle.trans ?_` and prove the remaining obligations. Rewrite using `[hQ]`.

Combine the equalities or inequalities in the displayed calculation. Conclude with `(h8 h).le`.
-/
theorem gmRank : GmRank := by
  intro n hn
  have hQ := card_Q n hn
  have hle : Nat.card ((GalL n ⧸ Subgroup.zpowers (JJ n)) ⧸
      (powMonoidHom 2 : (GalL n ⧸ Subgroup.zpowers (JJ n)) →* _).range) ≤
      Nat.card (GalL n ⧸ Subgroup.zpowers (JJ n)) :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.index_dvd_card _)
  have h8 : 3 ≤ n → Nat.card ((GalL n ⧸ Subgroup.zpowers (JJ n)) ⧸
      (powMonoidHom 2 : (GalL n ⧸ Subgroup.zpowers (JJ n)) →* _).range) = 8 := by
    intro h3
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    rw [card_QQ]
    refine le_antisymm (index_KK_le m) ?_
    have hd : (psi m).ker.index ∣ (KK (m + 3)).index := Subgroup.index_dvd_of_le (KK_le_ker m)
    rw [index_ker_psi] at hd
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) hd
  refine ⟨hQ, ?_, h8⟩
  rcases (by omega : n ≤ 2 ∨ 3 ≤ n) with h | h
  · refine hle.trans ?_
    rw [hQ]
    calc 2 ^ n ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 8 := by norm_num
  · exact (h8 h).le

end Formalism.TwoAdicCyclotomicDecomposition
