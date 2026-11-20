import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.StripEstimates.FaceMapCompSuccAboveCastSucc

open Finset

namespace GlobalTheory.CompanionTheory.SqrtCount

noncomputable def rootCount (n : ℤ) (e : ℕ) : ℕ := Nat.card {x : ZMod e // x ^ 2 = (n : ZMod e)}

/- English proof (translation)
Rewrite using `[rootCount, Nat.card_eq_fintype_card, Fintype.card_subtype]`.
-/
theorem rootCount_eq_card (n : ℤ) (e : ℕ) [NeZero e] :
    rootCount n e = (univ.filter (fun x : ZMod e => x ^ 2 = (n : ZMod e))).card := by
  classical
  rw [rootCount, Nat.card_eq_fintype_card, Fintype.card_subtype]

/- English proof (translation)
Unfold `rootCount`. Rewrite using `[← Nat.card_prod]`. Use `Nat.card_congr (Equiv.trans ?_ Equiv.subtypeProdEquivProd)` and prove the remaining obligations. Use `(ZMod.chineseRemainder h).toEquiv.subtypeEquiv ?_` and prove the remaining obligations. Introduce `x`.

Establish `h1 : x ^ 2 = (n : ZMod (e * e')) ↔ ZMod.chineseRemainder h (x ^ 2) = ZMod.chineseRemainder h (n : ZMod (e * e'))` using `(ZMod.chineseRemainder h).injective.eq_iff.symm`. Rewrite using `[h1, map_pow, map_intCast, Prod.ext_iff]`. Simplify using the standard rewrite rules.
-/
theorem rootCount_mul (n : ℤ) {e e' : ℕ} (h : Nat.Coprime e e') :
    rootCount n (e * e') = rootCount n e * rootCount n e' := by
  unfold rootCount
  rw [← Nat.card_prod]
  refine Nat.card_congr (Equiv.trans ?_ Equiv.subtypeProdEquivProd)
  refine (ZMod.chineseRemainder h).toEquiv.subtypeEquiv ?_
  intro x
  have h1 : x ^ 2 = (n : ZMod (e * e')) ↔
      ZMod.chineseRemainder h (x ^ 2) = ZMod.chineseRemainder h (n : ZMod (e * e')) :=
    (ZMod.chineseRemainder h).injective.eq_iff.symm
  rw [h1, map_pow, map_intCast, Prod.ext_iff]
  simp

/- English proof (translation)
Set `f : ZMod N →+ ZMod d` to `(ZMod.castHom hd (ZMod d)).toAddMonoidHom`. Establish `hs : Function.Surjective f` using `ZMod.castHom_surjective hd`. Establish `heq : ∀ c' : ZMod d, (univ.filter (fun y => f y = c')).card = (univ.filter (fun y => f y = c)).card` using `fun c' => AddMonoidHom.card_fiber_eq_of_mem_range f (hs c') (hs c)`. Establish `h2` using `Finset.card_eq_sum_card_fiberwise (f := f) (s := (univ : Finset (ZMod N))) (t := (univ : Finset (ZMod d))) (by intro x _; simp)`. Simplify using `only [heq, sum_const, card_univ, ZMod.card, smul_eq_mul] at h2`.

Rewrite using `[mul_comm]`. Conclude with `h2.symm`.
-/
theorem card_fiber {N d : ℕ} [NeZero N] [NeZero d] (hd : d ∣ N) (c : ZMod d) :
    (univ.filter (fun y : ZMod N => ZMod.castHom hd (ZMod d) y = c)).card * d = N := by
  classical
  let f : ZMod N →+ ZMod d := (ZMod.castHom hd (ZMod d)).toAddMonoidHom
  have hs : Function.Surjective f := ZMod.castHom_surjective hd
  have heq : ∀ c' : ZMod d, (univ.filter (fun y => f y = c')).card =
      (univ.filter (fun y => f y = c)).card :=
    fun c' => AddMonoidHom.card_fiber_eq_of_mem_range f (hs c') (hs c)
  have h2 := Finset.card_eq_sum_card_fiberwise (f := f) (s := (univ : Finset (ZMod N)))
    (t := (univ : Finset (ZMod d))) (by intro x _; simp)
  simp only [heq, sum_const, card_univ, ZMod.card, smul_eq_mul] at h2
  rw [mul_comm]
  exact h2.symm

/- English proof (translation)
Introduce `h`. Proceed by induction on `h with`. Consider the case `zero`. Introduce `j A B hA hd`. Simplify `hA) hd` using `using hp.pow_dvd_of_dvd_mul_left j (by simpa`.

Consider the case `succ h ih`. Introduce `j A B hA hd`. Distinguish the cases in `hpA : p ∣ A`. Take `⟨A', rfl⟩` from `hpA`. Break down `Nat.eq_zero_or_pos j with rfl | hj` into its components or cases.

Simplify using the standard rewrite rules. Take `⟨j, rfl⟩ : ∃ i, j = i + 1` from `⟨j - 1, by omega⟩`. Establish `hA' : ¬ p ^ (h + 1) ∣ A'`. Introduce `hc`. Apply `hA` to reduce the goal to its premises.

Rewrite using `[pow_succ' p (h + 1)]`. Conclude with `mul_dvd_mul_left p hc`. Establish `hd' : p ^ j ∣ A' * B`. Rewrite `hd` using `[pow_succ', mul_assoc]`. Conclude with `(mul_dvd_mul_iff_left hp.ne_zero).1 hd`.

Use `ih j A' B hA' hd'` as an intermediate fact. Simplify `this` using `[Nat.add_sub_add_right]`. Conclude with `(pow_dvd_pow p (Nat.sub_le j (h + 1))).trans (hp.pow_dvd_of_dvd_mul_left j hpA hd)`.
-/
theorem pow_dvd_of_pow_dvd_mul {p : ℤ} (hp : Prime p) :
    ∀ (h j : ℕ) (A B : ℤ), ¬ p ^ (h + 1) ∣ A → p ^ j ∣ A * B → p ^ (j - h) ∣ B := by
  intro h
  induction h with
  | zero =>
    intro j A B hA hd
    simpa using hp.pow_dvd_of_dvd_mul_left j (by simpa using hA) hd
  | succ h ih =>
    intro j A B hA hd
    by_cases hpA : p ∣ A
    · obtain ⟨A', rfl⟩ := hpA
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · simp
      · obtain ⟨j, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
        have hA' : ¬ p ^ (h + 1) ∣ A' := by
          intro hc
          apply hA
          rw [pow_succ' p (h + 1)]
          exact mul_dvd_mul_left p hc
        have hd' : p ^ j ∣ A' * B := by
          rw [pow_succ', mul_assoc] at hd
          exact (mul_dvd_mul_iff_left hp.ne_zero).1 hd
        have := ih j A' B hA' hd'
        simpa [Nat.add_sub_add_right] using this
    · exact (pow_dvd_pow p (Nat.sub_le j (h + 1))).trans (hp.pow_dvd_of_dvd_mul_left j hpA hd)

/- English proof (translation)
Establish `hpz : Prime (p : ℤ)` using `Nat.prime_iff_prime_int.1 hp`. Establish `hfac : a ^ 2 - b ^ 2 = (a - b) * (a + b)` using `by ring`. Rewrite `hd` using `[hfac]`. Distinguish the cases in `h1 : (p : ℤ) ^ (h + 1) ∣ a - b`. Establish `h2 : ¬ (p : ℤ) ^ (h + 1) ∣ a + b`.

Introduce `h2`. Establish `h3 : (p : ℤ) ^ (h + 1) ∣ 2 * b`. Use `dvd_sub h2 h1` as an intermediate fact. Establish `e : a + b - (a - b) = 2 * b` using `by ring`. Rewrite `this` using `[e]`. Then use the resulting hypothesis.

Establish `h4 : IsCoprime ((p : ℤ) ^ (h + 1)) 2`. Apply `IsCoprime.pow_left` to reduce the goal to its premises. Establish `: Nat.Coprime p 2` using `(Nat.coprime_primes hp Nat.prime_two).2 hodd`. Conclude with `Nat.isCoprime_iff_coprime.2 this` after adjusting the coercions. Conclude with `hb (h4.dvd_of_dvd_mul_left h3)`.

Use `left`. Rewrite `hd` using `[mul_comm]`. Conclude with `pow_dvd_of_pow_dvd_mul hpz h j _ _ h2 hd`. Use `right`. Conclude with `pow_dvd_of_pow_dvd_mul hpz h j _ _ h1 hd`.
-/
theorem key {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (a b : ℤ) (j h : ℕ)
    (hb : ¬ (p : ℤ) ^ (h + 1) ∣ b) (hd : (p : ℤ) ^ j ∣ a ^ 2 - b ^ 2) :
    (p : ℤ) ^ (j - h) ∣ a - b ∨ (p : ℤ) ^ (j - h) ∣ a + b := by
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have hfac : a ^ 2 - b ^ 2 = (a - b) * (a + b) := by ring
  rw [hfac] at hd
  by_cases h1 : (p : ℤ) ^ (h + 1) ∣ a - b
  · have h2 : ¬ (p : ℤ) ^ (h + 1) ∣ a + b := by
      intro h2
      have h3 : (p : ℤ) ^ (h + 1) ∣ 2 * b := by
        have := dvd_sub h2 h1
        have e : a + b - (a - b) = 2 * b := by ring
        rwa [e] at this
      have h4 : IsCoprime ((p : ℤ) ^ (h + 1)) 2 := by
        apply IsCoprime.pow_left
        have : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).2 hodd
        exact_mod_cast Nat.isCoprime_iff_coprime.2 this
      exact hb (h4.dvd_of_dvd_mul_left h3)
    left
    rw [mul_comm] at hd
    exact pow_dvd_of_pow_dvd_mul hpz h j _ _ h2 hd
  · right
    exact pow_dvd_of_pow_dvd_mul hpz h j _ _ h1 hd

/- English proof (translation)
Rewrite using `[← CharP.intCast_eq_zero_iff (ZMod N) N, Int.cast_sub, Int.cast_pow, sub_eq_zero]`.
-/
theorem cast_sq_iff (N : ℕ) (a n : ℤ) :
    (a : ZMod N) ^ 2 = (n : ZMod N) ↔ (N : ℤ) ∣ a ^ 2 - n := by
  rw [← CharP.intCast_eq_zero_iff (ZMod N) N, Int.cast_sub, Int.cast_pow, sub_eq_zero]

/- English proof (translation)
Establish `h` using `card_fiber (pow_dvd_pow p hk) c`. Establish `hpos : 0 < p ^ k` using `Nat.pos_of_ne_zero (NeZero.ne _)`. Use `Nat.eq_of_mul_eq_mul_right hpos ?_` and prove the remaining obligations. Rewrite using `[h, ← pow_add, Nat.sub_add_cancel hk]`.
-/
theorem card_fiber_pow {p : ℕ} [NeZero p] {j k : ℕ} (hk : k ≤ j) (c : ZMod (p ^ k)) :
    (univ.filter (fun y : ZMod (p ^ j) =>
      ZMod.castHom (pow_dvd_pow p hk) (ZMod (p ^ k)) y = c)).card = p ^ (j - k) := by
  have h := card_fiber (pow_dvd_pow p hk) c
  have hpos : 0 < p ^ k := Nat.pos_of_ne_zero (NeZero.ne _)
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  rw [h, ← pow_add, Nat.sub_add_cancel hk]

/- English proof (translation)
Establish `hp : p.Prime` using `Fact.out`. Rewrite using `[rootCount_eq_card]`. Distinguish the cases in `hne : ∃ x : ZMod (p ^ j), x ^ 2 = (n : ZMod (p ^ j))`. Take `⟨x, hx⟩` from `hne`. Take `⟨b, rfl⟩` from `ZMod.intCast_surjective x`.

Establish `hbn : (p : ℤ) ^ j ∣ b ^ 2 - n`. Use `(cast_sq_iff (p ^ j) b n).1 hx` as an intermediate fact. Simplify using `using this`. Establish `hb : ¬ (p : ℤ) ^ (v / 2 + 1) ∣ b`. Introduce `hc`.

Establish `h1 : (p : ℤ) ^ (v + 1) ∣ b ^ 2`. Establish `h2 : ((p : ℤ) ^ (v / 2 + 1)) ^ 2 ∣ b ^ 2` using `pow_dvd_pow_of_dvd hc 2`. Rewrite `h2` using `[← pow_mul]`. Conclude with `(pow_dvd_pow _ (by omega)).trans h2`. Establish `h3 : (p : ℤ) ^ (v + 1) ∣ b ^ 2 - n` using `(pow_dvd_pow _ (by omega)).trans hbn`.

Conclude with `hv ((dvd_sub_right h1).1 h3)`. Establish `hk : j - v / 2 ≤ j` using `Nat.sub_le _ _`. Set `φ` to `ZMod.castHom (pow_dvd_pow p hk) (ZMod (p ^ (j - v / 2)))`. Establish `hsub : univ.filter (fun y : ZMod (p ^ j) => y ^ 2 = (n : ZMod (p ^ j))) ⊆ univ.filter (fun y : ZMod (p ^ j) => φ y = (b : ZMod (p ^ (j - v / 2)))) ∪ univ.filter (fun y : ZMod (p ^ j) => φ y = ((-b : ℤ) : ZMod (p ^ (j - v / 2))))`. Introduce `y hy`.

Take `⟨a, rfl⟩` from `ZMod.intCast_surjective y`. Establish `han : (p : ℤ) ^ j ∣ a ^ 2 - n`. Use `(cast_sq_iff (p ^ j) a n).1 (by simpa using hy)` as an intermediate fact. Simplify using `using this`. Establish `hab : (p : ℤ) ^ j ∣ a ^ 2 - b ^ 2`.

Use `dvd_sub han hbn` as an intermediate fact. Establish `e : a ^ 2 - n - (b ^ 2 - n) = a ^ 2 - b ^ 2` using `by ring`. Rewrite `this` using `[e]`. Then use the resulting hypothesis. Establish `hφ : φ (a : ZMod (p ^ j)) = (a : ZMod (p ^ (j - v / 2)))` using `map_intCast φ a`. Break down `key hp hodd a b j (v / 2) hb hab with h | h` into its components or cases.

Use `mem_union_left _ (mem_filter.2 ⟨mem_univ _, ?_⟩)` and prove the remaining obligations. Rewrite using `[hφ, ZMod.intCast_eq_intCast_iff_dvd_sub]`. Establish `: (p : ℤ) ^ (j - v / 2) ∣ b - a`. Use `(dvd_neg).2 h` as an intermediate fact. Simplify using `using this`.

Simplify using `using this`. Use `mem_union_right _ (mem_filter.2 ⟨mem_univ _, ?_⟩)` and prove the remaining obligations. Rewrite using `[hφ, ZMod.intCast_eq_intCast_iff_dvd_sub]`. Establish `: (p : ℤ) ^ (j - v / 2) ∣ -b - a`. Use `(dvd_neg).2 h` as an intermediate fact.

Establish `e : -(a + b) = -b - a` using `by ring`. Rewrite `this` using `[e]`. Then use the resulting hypothesis. Simplify using `using this`. Use `(card_le_card hsub).trans ((card_union_le _ _).trans ?_)` and prove the remaining obligations. Rewrite using `[card_fiber_pow hk, card_fiber_pow hk, Nat.sub_sub_self (by omega)]`.

Use linear arithmetic over natural numbers and integers. Establish `: univ.filter (fun y : ZMod (p ^ j) => y ^ 2 = (n : ZMod (p ^ j))) = ∅`. Use extensionality with `y`. Simplify using `only [mem_filter, mem_univ, true_and, notMem_empty, iff_false]`. Conclude with `fun hy => hne ⟨y, hy⟩`.

Rewrite using `[this]`. Simplify using the standard rewrite rules.
-/
theorem rootCount_le_of_lt {p : ℕ} [Fact p.Prime] (hodd : p ≠ 2) (n : ℤ) (v j : ℕ)
    (hv : ¬ (p : ℤ) ^ (v + 1) ∣ n) (hj : v < j) : rootCount n (p ^ j) ≤ 2 * p ^ (v / 2) := by
  classical
  have hp : p.Prime := Fact.out
  rw [rootCount_eq_card]
  by_cases hne : ∃ x : ZMod (p ^ j), x ^ 2 = (n : ZMod (p ^ j))
  · obtain ⟨x, hx⟩ := hne
    obtain ⟨b, rfl⟩ := ZMod.intCast_surjective x
    have hbn : (p : ℤ) ^ j ∣ b ^ 2 - n := by
      have := (cast_sq_iff (p ^ j) b n).1 hx
      simpa using this
    have hb : ¬ (p : ℤ) ^ (v / 2 + 1) ∣ b := by
      intro hc
      have h1 : (p : ℤ) ^ (v + 1) ∣ b ^ 2 := by
        have h2 : ((p : ℤ) ^ (v / 2 + 1)) ^ 2 ∣ b ^ 2 := pow_dvd_pow_of_dvd hc 2
        rw [← pow_mul] at h2
        exact (pow_dvd_pow _ (by omega)).trans h2
      have h3 : (p : ℤ) ^ (v + 1) ∣ b ^ 2 - n := (pow_dvd_pow _ (by omega)).trans hbn
      exact hv ((dvd_sub_right h1).1 h3)
    have hk : j - v / 2 ≤ j := Nat.sub_le _ _
    let φ := ZMod.castHom (pow_dvd_pow p hk) (ZMod (p ^ (j - v / 2)))
    have hsub : univ.filter (fun y : ZMod (p ^ j) => y ^ 2 = (n : ZMod (p ^ j))) ⊆
        univ.filter (fun y : ZMod (p ^ j) => φ y = (b : ZMod (p ^ (j - v / 2)))) ∪
        univ.filter (fun y : ZMod (p ^ j) => φ y = ((-b : ℤ) : ZMod (p ^ (j - v / 2)))) := by
      intro y hy
      obtain ⟨a, rfl⟩ := ZMod.intCast_surjective y
      have han : (p : ℤ) ^ j ∣ a ^ 2 - n := by
        have := (cast_sq_iff (p ^ j) a n).1 (by simpa using hy)
        simpa using this
      have hab : (p : ℤ) ^ j ∣ a ^ 2 - b ^ 2 := by
        have := dvd_sub han hbn
        have e : a ^ 2 - n - (b ^ 2 - n) = a ^ 2 - b ^ 2 := by ring
        rwa [e] at this
      have hφ : φ (a : ZMod (p ^ j)) = (a : ZMod (p ^ (j - v / 2))) := map_intCast φ a
      rcases key hp hodd a b j (v / 2) hb hab with h | h
      · refine mem_union_left _ (mem_filter.2 ⟨mem_univ _, ?_⟩)
        rw [hφ, ZMod.intCast_eq_intCast_iff_dvd_sub]
        have : (p : ℤ) ^ (j - v / 2) ∣ b - a := by
          have := (dvd_neg).2 h
          simpa using this
        simpa using this
      · refine mem_union_right _ (mem_filter.2 ⟨mem_univ _, ?_⟩)
        rw [hφ, ZMod.intCast_eq_intCast_iff_dvd_sub]
        have : (p : ℤ) ^ (j - v / 2) ∣ -b - a := by
          have := (dvd_neg).2 h
          have e : -(a + b) = -b - a := by ring
          rwa [e] at this
        simpa using this
    refine (card_le_card hsub).trans ((card_union_le _ _).trans ?_)
    rw [card_fiber_pow hk, card_fiber_pow hk, Nat.sub_sub_self (by omega)]
    omega
  · have : univ.filter (fun y : ZMod (p ^ j) => y ^ 2 = (n : ZMod (p ^ j))) = ∅ := by
      ext y
      simp only [mem_filter, mem_univ, true_and, notMem_empty, iff_false]
      exact fun hy => hne ⟨y, hy⟩
    rw [this]
    simp

/- English proof (translation)
Establish `hp : p.Prime` using `Fact.out`. Break down `Nat.lt_or_ge v j with hj | hj` into its components or cases. Conclude with `(rootCount_le_of_lt hodd n v j hv hj).trans (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right hp.pos (Nat.div_le_self v 2)))`. Establish `h1 : rootCount n (p ^ j) ≤ p ^ j`. Rewrite using `[rootCount_eq_card]`.

Use `(card_le_univ _).trans ?_` and prove the remaining obligations. Rewrite using `[ZMod.card]`. Establish `h2 : p ^ j ≤ p ^ v` using `Nat.pow_le_pow_right hp.pos hj`. Use linear arithmetic over natural numbers and integers.
-/
theorem rootCount_le {p : ℕ} [Fact p.Prime] (hodd : p ≠ 2) (n : ℤ) (v j : ℕ)
    (hv : ¬ (p : ℤ) ^ (v + 1) ∣ n) : rootCount n (p ^ j) ≤ 2 * p ^ v := by
  classical
  have hp : p.Prime := Fact.out
  rcases Nat.lt_or_ge v j with hj | hj
  · exact (rootCount_le_of_lt hodd n v j hv hj).trans
      (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right hp.pos (Nat.div_le_self v 2)))
  · have h1 : rootCount n (p ^ j) ≤ p ^ j := by
      rw [rootCount_eq_card]
      refine (card_le_univ _).trans ?_
      rw [ZMod.card]
    have h2 : p ^ j ≤ p ^ v := Nat.pow_le_pow_right hp.pos hj
    omega

/- English proof (translation)
Use `rootCount_le hodd n _ j ?_` and prove the remaining obligations. Introduce `h`. Establish `hp : p.Prime` using `Fact.out`. Use `Nat.pow_succ_factorization_not_dvd (Int.natAbs_ne_zero.2 hn) hp ?_` and prove the remaining obligations. Rewrite using `[← Int.natCast_dvd]`.

Conclude with `h` after adjusting the coercions.
-/
theorem rootCount_le_factorization {p : ℕ} [Fact p.Prime] (hodd : p ≠ 2) {n : ℤ} (hn : n ≠ 0)
    (j : ℕ) : rootCount n (p ^ j) ≤ 2 * p ^ n.natAbs.factorization p := by
  refine rootCount_le hodd n _ j ?_
  intro h
  have hp : p.Prime := Fact.out
  refine Nat.pow_succ_factorization_not_dvd (Int.natAbs_ne_zero.2 hn) hp ?_
  rw [← Int.natCast_dvd]
  exact_mod_cast h

/- English proof (translation)
Establish `hpz : Prime (p : ℤ)` using `Nat.prime_iff_prime_int.1 hp`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Assume the negation of the conclusion as `hc`. Break down `Nat.eq_zero_or_pos ((j + 1) / 2) with h0 | h0` into its components or cases.

Rewrite `hc` using `[h0]`. Simplify using `at hc`. Take `⟨k, hk⟩ : ∃ k, (j + 1) / 2 = k + 1` from `⟨(j + 1) / 2 - 1, by omega⟩`. Rewrite `hc` using `[hk]`. Establish `h1` using `pow_dvd_of_pow_dvd_mul hpz k j a a hc (by rwa [← sq])`.

Apply `hc` to reduce the goal to its premises. Conclude with `(pow_dvd_pow _ (by omega)).trans h1`. Introduce `h`. Establish `h2 : ((p : ℤ) ^ ((j + 1) / 2)) ^ 2 ∣ a ^ 2` using `pow_dvd_pow_of_dvd h 2`. Rewrite `h2` using `[← pow_mul]`.

Conclude with `(pow_dvd_pow _ (by omega)).trans h2`.
-/
theorem pow_dvd_sq_iff {p : ℕ} (hp : p.Prime) (j : ℕ) (a : ℤ) :
    (p : ℤ) ^ j ∣ a ^ 2 ↔ (p : ℤ) ^ ((j + 1) / 2) ∣ a := by
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  constructor
  · intro h
    by_contra hc
    rcases Nat.eq_zero_or_pos ((j + 1) / 2) with h0 | h0
    · rw [h0] at hc
      simp at hc
    · obtain ⟨k, hk⟩ : ∃ k, (j + 1) / 2 = k + 1 := ⟨(j + 1) / 2 - 1, by omega⟩
      rw [hk] at hc
      have h1 := pow_dvd_of_pow_dvd_mul hpz k j a a hc (by rwa [← sq])
      apply hc
      exact (pow_dvd_pow _ (by omega)).trans h1
  · intro h
    have h2 : ((p : ℤ) ^ ((j + 1) / 2)) ^ 2 ∣ a ^ 2 := pow_dvd_pow_of_dvd h 2
    rw [← pow_mul] at h2
    exact (pow_dvd_pow _ (by omega)).trans h2

/- English proof (translation)
Establish `hp : p.Prime` using `Fact.out`. Establish `hk : (j + 1) / 2 ≤ j` using `by omega`. Rewrite using `[rootCount_eq_card]`. Establish `: univ.filter (fun y : ZMod (p ^ j) => y ^ 2 = ((0 : ℤ) : ZMod (p ^ j))) = univ.filter (fun y : ZMod (p ^ j) => ZMod.castHom (pow_dvd_pow p hk) (ZMod (p ^ ((j + 1) / 2))) y = 0)`. Use extensionality with `y`.

Take `⟨a, rfl⟩` from `ZMod.intCast_surjective y`. Simplify using `only [mem_filter, mem_univ, true_and]`. Rewrite using `[cast_sq_iff, map_intCast, CharP.intCast_eq_zero_iff (ZMod (p ^ ((j + 1) / 2))) (p ^ ((j + 1) / 2))]`. Simplify using `only [sub_zero, Nat.cast_pow]`. Conclude with `pow_dvd_sq_iff hp j a`.

Rewrite using `[this, card_fiber_pow hk]`. Use `congr 1`. Use linear arithmetic over natural numbers and integers.
-/
theorem rootCount_zero {p : ℕ} [Fact p.Prime] (j : ℕ) : rootCount 0 (p ^ j) = p ^ (j / 2) := by
  classical
  have hp : p.Prime := Fact.out
  have hk : (j + 1) / 2 ≤ j := by omega
  rw [rootCount_eq_card]
  have : univ.filter (fun y : ZMod (p ^ j) => y ^ 2 = ((0 : ℤ) : ZMod (p ^ j))) =
      univ.filter (fun y : ZMod (p ^ j) =>
        ZMod.castHom (pow_dvd_pow p hk) (ZMod (p ^ ((j + 1) / 2))) y = 0) := by
    ext y
    obtain ⟨a, rfl⟩ := ZMod.intCast_surjective y
    simp only [mem_filter, mem_univ, true_and]
    rw [cast_sq_iff, map_intCast, CharP.intCast_eq_zero_iff (ZMod (p ^ ((j + 1) / 2))) (p ^ ((j + 1) / 2))]
    simp only [sub_zero, Nat.cast_pow]
    exact pow_dvd_sq_iff hp j a
  rw [this, card_fiber_pow hk]
  congr 1
  omega

/- English proof (translation)
Establish `hpz : Prime (p : ℤ)` using `Nat.prime_iff_prime_int.1 hp`. Introduce `j`. Proceed by induction on `j with`. Consider the case `zero => exact ⟨b₀, by simpa using h₀⟩`. Consider the case `succ j ih`.

Take `⟨b, c, hc⟩` from `ih`. Establish `hp2 : ¬ (p : ℤ) ∣ 2 * b`. Introduce `h`. Break down `hpz.dvd_or_dvd h with h | h` into its components or cases. Establish `: p ∣ 2` using `by exact_mod_cast h`.

Conclude with `hodd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this)`. Apply `hn` to reduce the goal to its premises. Establish `h1 : (p : ℤ) ∣ b ^ 2` using `h.trans (dvd_pow_self b two_ne_zero)`. Establish `h2 : (p : ℤ) ∣ b ^ 2 - n` using `(dvd_pow_self (p : ℤ) (Nat.succ_ne_zero j)).trans ⟨c, hc⟩`. Conclude with `(dvd_sub_right h1).1 h2`.

Take `⟨u, w, huw⟩` from `((Prime.coprime_iff_not_dvd hpz).2 hp2).symm`. Use `⟨b + (-c * u) * (p : ℤ) ^ (j + 1), c * w + (c * u) ^ 2 * (p : ℤ) ^ j, ?_⟩` and prove the remaining obligations. Take the linear combination `hc - ((p : ℤ) ^ (j + 1) * c) * huw`.
-/
theorem exists_root {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) {n : ℤ} (hn : ¬ (p : ℤ) ∣ n) {b₀ : ℤ}
    (h₀ : (p : ℤ) ∣ b₀ ^ 2 - n) : ∀ j : ℕ, ∃ b : ℤ, (p : ℤ) ^ (j + 1) ∣ b ^ 2 - n := by
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  intro j
  induction j with
  | zero => exact ⟨b₀, by simpa using h₀⟩
  | succ j ih =>
    obtain ⟨b, c, hc⟩ := ih
    have hp2 : ¬ (p : ℤ) ∣ 2 * b := by
      intro h
      rcases hpz.dvd_or_dvd h with h | h
      · have : p ∣ 2 := by exact_mod_cast h
        exact hodd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this)
      · apply hn
        have h1 : (p : ℤ) ∣ b ^ 2 := h.trans (dvd_pow_self b two_ne_zero)
        have h2 : (p : ℤ) ∣ b ^ 2 - n := (dvd_pow_self (p : ℤ) (Nat.succ_ne_zero j)).trans ⟨c, hc⟩
        exact (dvd_sub_right h1).1 h2
    obtain ⟨u, w, huw⟩ := ((Prime.coprime_iff_not_dvd hpz).2 hp2).symm
    refine ⟨b + (-c * u) * (p : ℤ) ^ (j + 1), c * w + (c * u) ^ 2 * (p : ℤ) ^ j, ?_⟩
    linear_combination hc - ((p : ℤ) ^ (j + 1) * c) * huw

/- English proof (translation)
Establish `hd : p ∣ p ^ (j + 1)` using `dvd_pow_self p (Nat.succ_ne_zero j)`. Set `φ` to `ZMod.castHom hd (ZMod p)`. Use `⟨φ x, ?_⟩` and prove the remaining obligations. Rewrite using `[← sq, ← map_pow, hx, map_intCast]`.
-/
theorem isSquare_of_root {p : ℕ} {j : ℕ} {n : ℤ} (x : ZMod (p ^ (j + 1)))
    (hx : x ^ 2 = (n : ZMod (p ^ (j + 1)))) : IsSquare (n : ZMod p) := by
  have hd : p ∣ p ^ (j + 1) := dvd_pow_self p (Nat.succ_ne_zero j)
  let φ := ZMod.castHom hd (ZMod p)
  refine ⟨φ x, ?_⟩
  rw [← sq, ← map_pow, hx, map_intCast]

/- English proof (translation)
Establish `hp : p.Prime` using `Fact.out`. Establish `hpz : Prime (p : ℤ)` using `Nat.prime_iff_prime_int.1 hp`. Establish `hn0 : (n : ZMod p) ≠ 0`. Rewrite using `[Ne, CharP.intCast_eq_zero_iff (ZMod p) p]`. Conclude with `hn`.

Break down `legendreSym.eq_one_or_neg_one p hn0 with h | h` into its components or cases. Take `⟨r, hr⟩` from `(legendreSym.eq_one_iff p hn0).1 h`. Take `⟨b₀, rfl⟩` from `ZMod.intCast_surjective r`. Establish `h₀ : (p : ℤ) ∣ b₀ ^ 2 - n` using `(cast_sq_iff p b₀ n).1 (by rw [hr, sq])`. Take `⟨b, hb⟩` from `exists_root hp hodd hn h₀ j`.

Establish `hb' : (b : ZMod (p ^ (j + 1))) ^ 2 = (n : ZMod (p ^ (j + 1)))` using `(cast_sq_iff _ b n).2 (by simpa using hb)`. Establish `hne : (b : ZMod (p ^ (j + 1))) ≠ -(b : ZMod (p ^ (j + 1)))`. Introduce `he`. Establish `h2 : ((2 * b : ℤ) : ZMod (p ^ (j + 1))) = 0`. Use `push_cast`.

Take the linear combination `he`. Rewrite `h2` using `[CharP.intCast_eq_zero_iff (ZMod (p ^ (j + 1))) (p ^ (j + 1))]`. Establish `h3 : (p : ℤ) ∣ 2 * b`. Use `Dvd.dvd.trans ?_ h2` and prove the remaining obligations. Use `push_cast`.

Conclude with `dvd_pow_self _ (Nat.succ_ne_zero j)`. Break down `hpz.dvd_or_dvd h3 with h4 | h4` into its components or cases. Establish `: p ∣ 2` using `by exact_mod_cast h4`. Conclude with `hodd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this)`. Establish `h5 : (p : ℤ) ∣ b ^ 2` using `h4.trans (dvd_pow_self b two_ne_zero)`.

Establish `h6 : (p : ℤ) ∣ b ^ 2 - n` using `(dvd_pow_self (p : ℤ) (Nat.succ_ne_zero j)).trans hb`. Conclude with `hn ((dvd_sub_right h5).1 h6)`. Establish `hle : rootCount n (p ^ (j + 1)) ≤ 2`. Use `rootCount_le_of_lt hodd n 0 (j + 1) (by simpa using hn) (Nat.succ_pos j)` as an intermediate fact. Simplify using `using this`.

Establish `hge : 2 ≤ rootCount n (p ^ (j + 1))`. Establish `hsub : ({(b : ZMod (p ^ (j + 1))), -(b : ZMod (p ^ (j + 1)))} : Finset (ZMod (p ^ (j + 1)))) ⊆ univ.filter (fun x : ZMod (p ^ (j + 1)) => x ^ 2 = (n : ZMod (p ^ (j + 1))))`. Introduce `y hy`. Break down `mem_insert.1 hy with rfl | hy` into its components or cases. Conclude with `mem_filter.2 ⟨mem_univ _, hb'⟩`.

Rewrite using `[mem_singleton.1 hy]`. Conclude with `mem_filter.2 ⟨mem_univ _, by rw [neg_sq]; exact hb'⟩`. Establish `h2` using `card_le_card hsub`. Rewrite `h2` using `[card_pair hne, ← rootCount_eq_card]`. Then use the resulting hypothesis. Rewrite using `[h, show rootCount n (p ^ (j + 1)) = 2 by omega]`.

Evaluate the numerical expressions. Establish `hns` using `(legendreSym.eq_neg_one_iff p).1 h`. Establish `hempty : IsEmpty {x : ZMod (p ^ (j + 1)) // x ^ 2 = (n : ZMod (p ^ (j + 1)))}` using `⟨fun x => hns (isSquare_of_root x.1 x.2)⟩`. Establish `: rootCount n (p ^ (j + 1)) = 0`. Rewrite using `[rootCount]`.

Conclude with `Nat.card_of_isEmpty`. Rewrite using `[h, this]`. Evaluate the numerical expressions.
-/
theorem rootCount_of_not_dvd {p : ℕ} [Fact p.Prime] (hodd : p ≠ 2) {n : ℤ} (hn : ¬ (p : ℤ) ∣ n) (j : ℕ) :
    (rootCount n (p ^ (j + 1)) : ℤ) = 1 + legendreSym p n := by
  classical
  have hp : p.Prime := Fact.out
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have hn0 : (n : ZMod p) ≠ 0 := by
    rw [Ne, CharP.intCast_eq_zero_iff (ZMod p) p]
    exact hn
  rcases legendreSym.eq_one_or_neg_one p hn0 with h | h
  · obtain ⟨r, hr⟩ := (legendreSym.eq_one_iff p hn0).1 h
    obtain ⟨b₀, rfl⟩ := ZMod.intCast_surjective r
    have h₀ : (p : ℤ) ∣ b₀ ^ 2 - n := (cast_sq_iff p b₀ n).1 (by rw [hr, sq])
    obtain ⟨b, hb⟩ := exists_root hp hodd hn h₀ j
    have hb' : (b : ZMod (p ^ (j + 1))) ^ 2 = (n : ZMod (p ^ (j + 1))) :=
      (cast_sq_iff _ b n).2 (by simpa using hb)
    have hne : (b : ZMod (p ^ (j + 1))) ≠ -(b : ZMod (p ^ (j + 1))) := by
      intro he
      have h2 : ((2 * b : ℤ) : ZMod (p ^ (j + 1))) = 0 := by
        push_cast
        linear_combination he
      rw [CharP.intCast_eq_zero_iff (ZMod (p ^ (j + 1))) (p ^ (j + 1))] at h2
      have h3 : (p : ℤ) ∣ 2 * b := by
        refine Dvd.dvd.trans ?_ h2
        push_cast
        exact dvd_pow_self _ (Nat.succ_ne_zero j)
      rcases hpz.dvd_or_dvd h3 with h4 | h4
      · have : p ∣ 2 := by exact_mod_cast h4
        exact hodd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this)
      · have h5 : (p : ℤ) ∣ b ^ 2 := h4.trans (dvd_pow_self b two_ne_zero)
        have h6 : (p : ℤ) ∣ b ^ 2 - n := (dvd_pow_self (p : ℤ) (Nat.succ_ne_zero j)).trans hb
        exact hn ((dvd_sub_right h5).1 h6)
    have hle : rootCount n (p ^ (j + 1)) ≤ 2 := by
      have := rootCount_le_of_lt hodd n 0 (j + 1) (by simpa using hn) (Nat.succ_pos j)
      simpa using this
    have hge : 2 ≤ rootCount n (p ^ (j + 1)) := by
      have hsub : ({(b : ZMod (p ^ (j + 1))), -(b : ZMod (p ^ (j + 1)))} :
          Finset (ZMod (p ^ (j + 1)))) ⊆
          univ.filter (fun x : ZMod (p ^ (j + 1)) => x ^ 2 = (n : ZMod (p ^ (j + 1)))) := by
        intro y hy
        rcases mem_insert.1 hy with rfl | hy
        · exact mem_filter.2 ⟨mem_univ _, hb'⟩
        · rw [mem_singleton.1 hy]
          exact mem_filter.2 ⟨mem_univ _, by rw [neg_sq]; exact hb'⟩
      have h2 := card_le_card hsub
      rwa [card_pair hne, ← rootCount_eq_card] at h2
    rw [h, show rootCount n (p ^ (j + 1)) = 2 by omega]
    norm_num
  · have hns := (legendreSym.eq_neg_one_iff p).1 h
    have hempty : IsEmpty {x : ZMod (p ^ (j + 1)) // x ^ 2 = (n : ZMod (p ^ (j + 1)))} :=
      ⟨fun x => hns (isSquare_of_root x.1 x.2)⟩
    have : rootCount n (p ^ (j + 1)) = 0 := by
      rw [rootCount]
      exact Nat.card_of_isEmpty
    rw [h, this]
    norm_num

/- English proof (translation)
Rewrite using `[rootCount_of_not_dvd hodd hn, jacobiSym.legendreSym.to_jacobiSym]`.
-/
theorem rootCount_of_not_dvd_jacobi {p : ℕ} [Fact p.Prime] (hodd : p ≠ 2) {n : ℤ}
    (hn : ¬ (p : ℤ) ∣ n) (j : ℕ) :
    (rootCount n (p ^ (j + 1)) : ℤ) = 1 + jacobiSym n p := by
  rw [rootCount_of_not_dvd hodd hn, jacobiSym.legendreSym.to_jacobiSym]

/- English proof (translation)
Establish `: Unique {x : ZMod 1 // x ^ 2 = (n : ZMod 1)}` using `⟨⟨⟨0, Subsingleton.elim _ _⟩⟩, fun x => Subtype.ext (Subsingleton.elim _ _)⟩`. Rewrite using `[rootCount]`. Conclude with `Nat.card_unique`.
-/
theorem rootCount_one (n : ℤ) : rootCount n 1 = 1 := by
  have : Unique {x : ZMod 1 // x ^ 2 = (n : ZMod 1)} :=
    ⟨⟨⟨0, Subsingleton.elim _ _⟩⟩, fun x => Subtype.ext (Subsingleton.elim _ _)⟩
  rw [rootCount]
  exact Nat.card_unique

/- English proof (translation)
Rewrite using `[rootCount_eq_card, Ad3.S.NN]`. Use `Finset.card_bij (fun x _ => (x : ZMod e)) ?_ ?_ ?_` and prove the remaining obligations. Introduce `x hx`. Establish `h` using `(mem_filter.1 hx).2`. Use `mem_filter.2 ⟨mem_univ _, ?_⟩` and prove the remaining obligations.

Use `(cast_sq_iff e (x : ℤ) n).2 h` as an intermediate fact. Simplify using `using this`. Introduce `x hx y hy hxy`. Establish `h1` using `mem_range.1 (mem_filter.1 hx).1`. Establish `h2` using `mem_range.1 (mem_filter.1 hy).1`.

Use `(ZMod.natCast_eq_natCast_iff' x y e).1 hxy` as an intermediate fact. Rewrite `this` using `[Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2]`. Then use the resulting hypothesis. Introduce `y hy`. Use `⟨y.val, mem_filter.2 ⟨mem_range.2 (ZMod.val_lt y), ?_⟩, ZMod.natCast_zmod_val y⟩` and prove the remaining obligations. Use `(cast_sq_iff e (y.val : ℤ) n).1 ?_` and prove the remaining obligations.

Establish `h` using `(mem_filter.1 hy).2`. Simplify using `using h`.
-/
theorem NN_eq_rootCount (n : ℤ) (e : ℕ) [NeZero e] : Ad3.S.NN n e = rootCount n e := by
  classical
  rw [rootCount_eq_card, Ad3.S.NN]
  refine Finset.card_bij (fun x _ => (x : ZMod e)) ?_ ?_ ?_
  · intro x hx
    have h := (mem_filter.1 hx).2
    refine mem_filter.2 ⟨mem_univ _, ?_⟩
    have := (cast_sq_iff e (x : ℤ) n).2 h
    simpa using this
  · intro x hx y hy hxy
    have h1 := mem_range.1 (mem_filter.1 hx).1
    have h2 := mem_range.1 (mem_filter.1 hy).1
    have := (ZMod.natCast_eq_natCast_iff' x y e).1 hxy
    rwa [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at this
  · intro y hy
    refine ⟨y.val, mem_filter.2 ⟨mem_range.2 (ZMod.val_lt y), ?_⟩, ZMod.natCast_zmod_val y⟩
    refine (cast_sq_iff e (y.val : ℤ) n).1 ?_
    have h := (mem_filter.1 hy).2
    simpa using h

/- English proof (translation)
Simplify using `[Ad3.S.NN]`.
-/
theorem NN_zero_modulus (n : ℤ) : Ad3.S.NN n 0 = 0 := by
  simp [Ad3.S.NN]

/- English proof (translation)
Introduce `n`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[NN_eq_rootCount, rootCount_one]`. Introduce `e`. Rewrite using `[Ad3.S.NN]`.

Conclude with `(card_filter_le _ _).trans (by simp)`. Introduce `e e' h`. Break down `Nat.eq_zero_or_pos e with rfl | he` into its components or cases. Simplify using `[NN_zero_modulus]`. Break down `Nat.eq_zero_or_pos e' with rfl | he'` into its components or cases.

Simplify using `[NN_zero_modulus]`. Use `haveI : NeZero e := ⟨he.ne'⟩`. Use `haveI : NeZero e' := ⟨he'.ne'⟩`. Rewrite using `[NN_eq_rootCount, NN_eq_rootCount, NN_eq_rootCount, rootCount_mul n h]`. Introduce `p j hp hodd haveI : Fact p.Prime := ⟨hp⟩`.

Use `⟨fun hn => ?_, fun hn => ?_, fun hn => ?_⟩` and prove the remaining obligations. Rewrite using `[NN_eq_rootCount]`. Conclude with `rootCount_of_not_dvd_jacobi hodd hn j`. Rewrite using `[NN_eq_rootCount]`. Conclude with `rootCount_le_factorization hodd hn j`.

Substitute `hn` using the available equality. Rewrite using `[NN_eq_rootCount]`. Conclude with `rootCount_zero j`.
-/
theorem countingSquareRoots : Ad3.S.N2 := by
  intro n
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [NN_eq_rootCount, rootCount_one]
  · intro e
    rw [Ad3.S.NN]
    exact (card_filter_le _ _).trans (by simp)
  · intro e e' h
    rcases Nat.eq_zero_or_pos e with rfl | he
    · simp [NN_zero_modulus]
    rcases Nat.eq_zero_or_pos e' with rfl | he'
    · simp [NN_zero_modulus]
    haveI : NeZero e := ⟨he.ne'⟩
    haveI : NeZero e' := ⟨he'.ne'⟩
    rw [NN_eq_rootCount, NN_eq_rootCount, NN_eq_rootCount, rootCount_mul n h]
  · intro p j hp hodd
    haveI : Fact p.Prime := ⟨hp⟩
    refine ⟨fun hn => ?_, fun hn => ?_, fun hn => ?_⟩
    · rw [NN_eq_rootCount]
      exact rootCount_of_not_dvd_jacobi hodd hn j
    · rw [NN_eq_rootCount]
      exact rootCount_le_factorization hodd hn j
    · subst hn
      rw [NN_eq_rootCount]
      exact rootCount_zero j

end GlobalTheory.CompanionTheory.SqrtCount
