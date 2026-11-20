import Mathlib
import Formalism.PeriodIntegrals.UpqRep

namespace Formalism.FourierDecayAlt.P.CutBP.JmuHC

open Finset

/- English proof (translation)
Proceed by induction on `D using Finset.induction_on_max with`. Consider the case `empty => simp`. Consider the case `insert m D hlt ih`. Establish `hm : m ∉ D` using `fun h => lt_irrefl _ (hlt m h)`. Establish `h0' : 0 ∉ D` using `fun h => h0 (mem_insert_of_mem h)`.

Establish `hm0 : 0 < m` using `Nat.pos_of_ne_zero fun e => h0 (e ▸ mem_insert_self m D)`. Establish `hcard : D.card + 1 ≤ m`. Establish `hsub : D ⊆ (range m).erase 0` using `fun x hx => mem_erase.2 ⟨fun e => h0' (e ▸ hx), mem_range.2 (hlt x hx)⟩`. Use `card_le_card hsub` as an intermediate fact. Rewrite `this` using `[card_erase_of_mem (mem_range.2 hm0), card_range]`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[prod_insert hm, card_insert_of_notMem hm]`. Establish `ih'` using `ih h0'`. Establish `hP : 0 ≤ ∏ d ∈ D, (1 + 1 / (d : ℝ))` using `prod_nonneg fun d _ => by positivity`. Establish `hc : ((D.card : ℝ) + 1) ≤ (m : ℝ)` using `by exact_mod_cast hcard`.

Establish `hc0 : (0 : ℝ) < (D.card : ℝ) + 1` using `by positivity`. Establish `h1 : 1 + 1 / (m : ℝ) ≤ 1 + 1 / ((D.card : ℝ) + 1)`. Use `one_div_le_one_div_of_le hc0 hc` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Combine the equalities or inequalities in the displayed calculation.

Use `push_cast`. Clear the denominators using the available nonvanishing facts.
-/
theorem prod_one_add_inv_le (D : Finset ℕ) (h0 : 0 ∉ D) : ∏ d ∈ D, (1 + 1 / (d : ℝ)) ≤ D.card + 1 := by
  induction D using Finset.induction_on_max with
  | empty => simp
  | insert m D hlt ih =>
    have hm : m ∉ D := fun h => lt_irrefl _ (hlt m h)
    have h0' : 0 ∉ D := fun h => h0 (mem_insert_of_mem h)
    have hm0 : 0 < m := Nat.pos_of_ne_zero fun e => h0 (e ▸ mem_insert_self m D)
    have hcard : D.card + 1 ≤ m := by
      have hsub : D ⊆ (range m).erase 0 := fun x hx =>
        mem_erase.2 ⟨fun e => h0' (e ▸ hx), mem_range.2 (hlt x hx)⟩
      have := card_le_card hsub
      rw [card_erase_of_mem (mem_range.2 hm0), card_range] at this
      omega
    rw [prod_insert hm, card_insert_of_notMem hm]
    have ih' := ih h0'
    have hP : 0 ≤ ∏ d ∈ D, (1 + 1 / (d : ℝ)) := prod_nonneg fun d _ => by positivity
    have hc : ((D.card : ℝ) + 1) ≤ (m : ℝ) := by exact_mod_cast hcard
    have hc0 : (0 : ℝ) < (D.card : ℝ) + 1 := by positivity
    have h1 : 1 + 1 / (m : ℝ) ≤ 1 + 1 / ((D.card : ℝ) + 1) := by
      have := one_div_le_one_div_of_le hc0 hc
      linarith
    calc (1 + 1 / (m : ℝ)) * ∏ d ∈ D, (1 + 1 / (d : ℝ))
        ≤ (1 + 1 / ((D.card : ℝ) + 1)) * ((D.card : ℝ) + 1) :=
          mul_le_mul h1 ih' hP (by positivity)
      _ = ((D.card + 1 : ℕ) : ℝ) + 1 := by
          push_cast
          field_simp

variable {n : ℕ}

/- English proof (translation)
Establish `hne : ∀ t ∈ T, x s ≠ x t` using `fun t ht e => hs (hinj e ▸ ht)`. Rewrite using `[← prod_filter_mul_prod_filter_not T (fun t => x t < x s)]`. Establish `hlow : ∏ t ∈ T.filter (fun t => ¬ x t < x s), |x s + 1 - x t| / |x s - x t| ≤ 1`. Apply `prod_le_one (fun t _ => by positivity)` to reduce the goal to its premises. Introduce `t ht`.

Take `⟨ht, hlt⟩` from `mem_filter.1 ht`. Establish `hgt : x s < x t` using `lt_of_le_of_ne (not_lt.1 hlt) (hne t ht)`. Take `⟨m, hmv⟩` from `hint t s`. Establish `hm1 : (1 : ℝ) ≤ x t - x s`. Rewrite using `[hmv]`.

Establish `: (0 : ℤ) < m` using `by exact_mod_cast (hmv ▸ sub_pos.2 hgt)`. Conclude with `this` after adjusting the coercions. Rewrite using `[div_le_one (abs_pos.2 (sub_ne_zero.2 (hne t ht)))]`. Rewrite using `[abs_of_nonpos (by linarith), abs_of_neg (by linarith)]`. Combine the linear equalities and inequalities to obtain the conclusion.

Use `set Tp := T.filter (fun t => x t < x s) with hTp`. Set `dN : Fin n → ℕ` to `fun t => (⌊x s - x t⌋).toNat`. Establish `hdN : ∀ t ∈ Tp, ((dN t : ℕ) : ℝ) = x s - x t ∧ 1 ≤ x s - x t`. Introduce `t ht`. Take `⟨-, hlt⟩` from `mem_filter.1 ht`.

Take `⟨m, hmv⟩` from `hint s t`. Establish `hm0 : (0 : ℤ) < m` using `by exact_mod_cast (hmv ▸ sub_pos.2 hlt)`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Simplify using `only [dN, hmv, Int.floor_intCast]`. Rewrite using `[← Int.cast_natCast, Int.toNat_of_nonneg hm0.le]`.

Rewrite using `[hmv]`. Conclude with `hm0` after adjusting the coercions. Establish `hinjOn : Set.InjOn dN Tp`. Introduce `t ht t' ht' e`. Establish `h1` using `(hdN t ht).1`.

Establish `h2` using `(hdN t' ht').1`. Apply `hinj` to reduce the goal to its premises. Establish `: x s - x t = x s - x t'` using `by rw [← h1, ← h2, e]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hup : ∏ t ∈ Tp, |x s + 1 - x t| / |x s - x t| = ∏ d ∈ Tp.image dN, (1 + 1 / (d : ℝ))`.

Rewrite using `[prod_image hinjOn]`. Use `prod_congr rfl fun t ht => ?_` and prove the remaining obligations. Take `⟨h1, h2⟩` from `hdN t ht`. Rewrite using `[h1, abs_of_pos (by linarith), abs_of_pos (by linarith)]`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Establish `hD0 : 0 ∉ Tp.image dN`. Introduce `h`. Take `⟨t, ht, e⟩` from `mem_image.1 h`. Establish `h1` using `hdN t ht`.

Rewrite `h1` using `[e]`. Simplify using `at h1`. Combine the linear relations using `[h1.1, h1.2]`. Establish `hbound` using `prod_one_add_inv_le (Tp.image dN) hD0`. Rewrite `hbound` using `[card_image_of_injOn hinjOn]`.

Establish `hTcard : Tp.card + 1 ≤ n`. Establish `h1 : Tp.card ≤ T.card` using `card_le_card (filter_subset _ _)`. Establish `h2 : T.card < n`. Use `card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨subset_univ T, fun e => hs (e ▸ mem_univ s)⟩)` as an intermediate fact. Simplify using `using this`.

Use linear arithmetic over natural numbers and integers. Establish `hupnn : 0 ≤ ∏ t ∈ Tp, |x s + 1 - x t| / |x s - x t|` using `prod_nonneg fun t _ => by positivity`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_one, hup]`. Use `hbound.trans ?_` and prove the remaining obligations.

Conclude with `hTcard` after adjusting the coercions.
-/
theorem prod_ratio_le (x : Fin n → ℝ) (hinj : Function.Injective x) (hint : ∀ a b, ∃ m : ℤ, x a - x b = m)
    (s : Fin n) (T : Finset (Fin n)) (hs : s ∉ T) :
    ∏ t ∈ T, |x s + 1 - x t| / |x s - x t| ≤ n := by
  classical
  have hne : ∀ t ∈ T, x s ≠ x t := fun t ht e => hs (hinj e ▸ ht)
  rw [← prod_filter_mul_prod_filter_not T (fun t => x t < x s)]

  have hlow : ∏ t ∈ T.filter (fun t => ¬ x t < x s), |x s + 1 - x t| / |x s - x t| ≤ 1 := by
    apply prod_le_one (fun t _ => by positivity)
    intro t ht
    obtain ⟨ht, hlt⟩ := mem_filter.1 ht
    have hgt : x s < x t := lt_of_le_of_ne (not_lt.1 hlt) (hne t ht)
    obtain ⟨m, hmv⟩ := hint t s
    have hm1 : (1 : ℝ) ≤ x t - x s := by
      rw [hmv]
      have : (0 : ℤ) < m := by exact_mod_cast (hmv ▸ sub_pos.2 hgt)
      exact_mod_cast this
    rw [div_le_one (abs_pos.2 (sub_ne_zero.2 (hne t ht)))]
    rw [abs_of_nonpos (by linarith), abs_of_neg (by linarith)]
    linarith

  set Tp := T.filter (fun t => x t < x s) with hTp
  let dN : Fin n → ℕ := fun t => (⌊x s - x t⌋).toNat
  have hdN : ∀ t ∈ Tp, ((dN t : ℕ) : ℝ) = x s - x t ∧ 1 ≤ x s - x t := by
    intro t ht
    obtain ⟨-, hlt⟩ := mem_filter.1 ht
    obtain ⟨m, hmv⟩ := hint s t
    have hm0 : (0 : ℤ) < m := by exact_mod_cast (hmv ▸ sub_pos.2 hlt)
    refine ⟨?_, ?_⟩
    · simp only [dN, hmv, Int.floor_intCast]
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hm0.le]
    · rw [hmv]; exact_mod_cast hm0
  have hinjOn : Set.InjOn dN Tp := by
    intro t ht t' ht' e
    have h1 := (hdN t ht).1
    have h2 := (hdN t' ht').1
    apply hinj
    have : x s - x t = x s - x t' := by rw [← h1, ← h2, e]
    linarith
  have hup : ∏ t ∈ Tp, |x s + 1 - x t| / |x s - x t| = ∏ d ∈ Tp.image dN, (1 + 1 / (d : ℝ)) := by
    rw [prod_image hinjOn]
    refine prod_congr rfl fun t ht => ?_
    obtain ⟨h1, h2⟩ := hdN t ht
    rw [h1, abs_of_pos (by linarith), abs_of_pos (by linarith)]
    field_simp
    ring
  have hD0 : 0 ∉ Tp.image dN := by
    intro h
    obtain ⟨t, ht, e⟩ := mem_image.1 h
    have h1 := hdN t ht
    rw [e] at h1
    simp at h1
    linarith [h1.1, h1.2]
  have hbound := prod_one_add_inv_le (Tp.image dN) hD0
  rw [card_image_of_injOn hinjOn] at hbound
  have hTcard : Tp.card + 1 ≤ n := by
    have h1 : Tp.card ≤ T.card := card_le_card (filter_subset _ _)
    have h2 : T.card < n := by
      have := card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨subset_univ T, fun e => hs (e ▸ mem_univ s)⟩)
      simpa using this
    omega
  have hupnn : 0 ≤ ∏ t ∈ Tp, |x s + 1 - x t| / |x s - x t| := prod_nonneg fun t _ => by positivity
  calc (∏ t ∈ Tp, |x s + 1 - x t| / |x s - x t|) *
        ∏ t ∈ T.filter (fun t => ¬ x t < x s), |x s + 1 - x t| / |x s - x t|
      ≤ (∏ t ∈ Tp, |x s + 1 - x t| / |x s - x t|) * 1 := mul_le_mul_of_nonneg_left hlow hupnn
    _ ≤ (n : ℝ) := by
        rw [mul_one, hup]
        refine hbound.trans ?_
        exact_mod_cast hTcard

def numHC (x : Fin n → ℝ) : ℝ := ∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b), |x a - x b|

/- English proof (translation)
Establish `h1 : ∀ a : Fin n, ∏ b ∈ univ.erase a, g a b = (∏ b ∈ univ.filter (fun b : Fin n => a < b), g a b) * ∏ b ∈ univ.filter (fun b : Fin n => b < a), g a b`. Introduce `a`. Rewrite using `[← prod_union]`. Use `congr 1`. Use extensionality with `b`.

Simplify using `only [mem_erase, mem_univ, and_true, mem_union, mem_filter, true_and]`. Prove the components needed by the constructor for the conclusion. Apply the tactic sequence `intro h; rcases lt_or_gt_of_ne h with h | h <;> [exact Or.inr h; exact Or.inl h]`. Apply the tactic sequence `rintro (h | h) <;> [exact ne_of_gt h; exact ne_of_lt h]`. Rewrite using `[disjoint_filter]`.

Introduce `b _ h1 h2`. Conclude with `lt_asymm h1 h2`. Rewrite using `[prod_congr rfl (fun a _ => h1 a), prod_mul_distrib, sq]`. Use `congr 1`. Establish `hB : ∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => b < a), g a b = ∏ b : Fin n, ∏ a ∈ univ.filter (fun a : Fin n => b < a), g a b` using `prod_comm' (by intro a b; simp)`.

Rewrite using `[hB]`. Conclude with `prod_congr rfl fun b _ => prod_congr rfl fun a _ => hg b a`.
-/
theorem sq_prod_lt (g : Fin n → Fin n → ℝ) (hg : ∀ a b, g a b = g b a) :
    (∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b), g a b) ^ 2 = ∏ a : Fin n, ∏ b ∈ univ.erase a, g a b := by
  have h1 : ∀ a : Fin n, ∏ b ∈ univ.erase a, g a b =
      (∏ b ∈ univ.filter (fun b : Fin n => a < b), g a b) * ∏ b ∈ univ.filter (fun b : Fin n => b < a), g a b := by
    intro a
    rw [← prod_union]
    · congr 1
      ext b
      simp only [mem_erase, mem_univ, and_true, mem_union, mem_filter, true_and]
      constructor
      · intro h; rcases lt_or_gt_of_ne h with h | h <;> [exact Or.inr h; exact Or.inl h]
      · rintro (h | h) <;> [exact ne_of_gt h; exact ne_of_lt h]
    · rw [disjoint_filter]
      intro b _ h1 h2
      exact lt_asymm h1 h2
  rw [prod_congr rfl (fun a _ => h1 a), prod_mul_distrib, sq]
  congr 1
  have hB : ∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => b < a), g a b =
      ∏ b : Fin n, ∏ a ∈ univ.filter (fun a : Fin n => b < a), g a b :=
    prod_comm' (by intro a b; simp)
  rw [hB]
  exact prod_congr rfl fun b _ => prod_congr rfl fun a _ => hg b a

/- English proof (translation)
Use `set y : Fin n → ℝ := fun i => x i + if i ∈ I then 1 else 0 with hydef`. Use `set f : Fin n → Fin n → ℝ := fun a b => |y a - y b| / |x a - x b| with hf`. Establish `hx0 : ∀ a b, a ≠ b → |x a - x b| ≠ 0` using `fun a b h => abs_ne_zero.2 (sub_ne_zero.2 fun e => h (hinj e))`. Establish `hfs : ∀ a b, f a b = f b a` using `fun a b => by simp only [hf, abs_sub_comm]`. Establish `hy : ∀ a b, a ≠ b → |y a - y b| = f a b * |x a - x b|` using `fun a b h => by`.

Simplify using `only [hf]`. Rewrite using `[div_mul_cancel₀ _ (hx0 a b h)]`. Establish `hf1 : ∀ a b, a ≠ b → (a ∈ I ↔ b ∈ I) → f a b = 1`. Introduce `a b h hab`. Simplify using `only [hf, hydef]`.

Establish `: (x a + if a ∈ I then 1 else 0) - (x b + if b ∈ I then 1 else 0) = x a - x b`. Distinguish the cases in `ha : a ∈ I`. Rewrite using `[if_pos ha, if_pos (hab.1 ha)]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[if_neg ha, if_neg (fun hb => ha (hab.2 hb))]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, div_self (hx0 a b h)]`. Establish `hsqy : numHC y ^ 2 = ∏ a : Fin n, ∏ b ∈ univ.erase a, |y a - y b|` using `sq_prod_lt _ fun a b => abs_sub_comm _ _`. Establish `hsqx : numHC x ^ 2 = ∏ a : Fin n, ∏ b ∈ univ.erase a, |x a - x b|` using `sq_prod_lt _ fun a b => abs_sub_comm _ _`. Establish `hsplit : ∏ a : Fin n, ∏ b ∈ univ.erase a, |y a - y b| = (∏ a : Fin n, ∏ b ∈ univ.erase a, f a b) * numHC x ^ 2`.

Rewrite using `[hsqx, ← prod_mul_distrib]`. Use `prod_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[← prod_mul_distrib]`. Conclude with `prod_congr rfl fun b hb => hy a b (ne_of_mem_erase hb).symm`. Use `set Pr := ∏ s ∈ I, ∏ t ∈ univ \ I, f s t with hPr`.

Establish `hff : ∏ a : Fin n, ∏ b ∈ univ.erase a, f a b = Pr ^ 2`. Establish `hin : ∀ a ∈ I, ∏ b ∈ univ.erase a, f a b = ∏ b ∈ univ \ I, f a b`. Introduce `a ha`. Use `symm`. Apply `prod_subset` to reduce the goal to its premises.

Introduce `b hb`. Rewrite `hb` using `[mem_sdiff]`. Conclude with `mem_erase.2 ⟨fun e => hb.2 (e ▸ ha), mem_univ b⟩`. Introduce `b hb hb'`. Establish `hba : b ≠ a` using `ne_of_mem_erase hb`.

Establish `hbI : b ∈ I`. Assume the negation of the conclusion as `h`. Conclude with `hb' (mem_sdiff.2 ⟨mem_univ b, h⟩)`. Conclude with `hf1 a b hba.symm ⟨fun _ => hbI, fun _ => ha⟩`. Establish `hout : ∀ a ∉ I, ∏ b ∈ univ.erase a, f a b = ∏ b ∈ I, f a b`.

Introduce `a ha`. Use `symm`. Apply `prod_subset` to reduce the goal to its premises. Introduce `b hb`. Conclude with `mem_erase.2 ⟨fun e => ha (e ▸ hb), mem_univ b⟩`.

Introduce `b hb hb'`. Establish `hba : b ≠ a` using `ne_of_mem_erase hb`. Conclude with `hf1 a b hba.symm ⟨fun h => absurd h ha, fun h => absurd h hb'⟩`. Rewrite using `[← prod_filter_mul_prod_filter_not univ (fun a => a ∈ I)]`. Establish `e1 : univ.filter (fun a : Fin n => a ∈ I) = I` using `by ext a; simp`.

Establish `e2 : univ.filter (fun a : Fin n => a ∉ I) = univ \ I` using `by ext a; simp`. Rewrite using `[e1, e2, prod_congr rfl hin, prod_congr rfl (fun a ha => hout a (mem_sdiff.1 ha).2)]`. Establish `hC : ∏ a ∈ univ \ I, ∏ b ∈ I, f a b = ∏ b ∈ I, ∏ a ∈ univ \ I, f a b` using `prod_comm`. Rewrite using `[hC, sq]`. Use `congr 1`.

Conclude with `prod_congr rfl fun s _ => prod_congr rfl fun t _ => hfs t s`. Establish `hP0 : 0 ≤ Pr` using `prod_nonneg fun s _ => prod_nonneg fun t _ => by positivity`. Establish `hPn : Pr ≤ (n : ℝ) ^ I.card`. Rewrite using `[← prod_const]`. Use `prod_le_prod (fun s _ => prod_nonneg fun t _ => by positivity) fun s hs => ?_` and prove the remaining obligations.

Establish `e : ∏ t ∈ univ \ I, f s t = ∏ t ∈ univ \ I, |x s + 1 - x t| / |x s - x t|`. Use `prod_congr rfl fun t ht => ?_` and prove the remaining obligations. Establish `htI : t ∉ I` using `(mem_sdiff.1 ht).2`. Simplify using `only [hf, hydef, if_pos hs, if_neg htI]`. Use `congr 1`.

Put the polynomial expressions in normal form. Rewrite using `[e]`. Conclude with `prod_ratio_le x hinj hint s (univ \ I) (fun h => (mem_sdiff.1 h).2 hs)`. Establish `hny : 0 ≤ numHC y` using `prod_nonneg fun a _ => prod_nonneg fun b _ => abs_nonneg _`. Establish `hnx : 0 ≤ numHC x` using `prod_nonneg fun a _ => prod_nonneg fun b _ => abs_nonneg _`.

Establish `hsq : numHC y ^ 2 ≤ ((n : ℝ) ^ I.card * numHC x) ^ 2`. Rewrite using `[hsqy, hsplit, hff, mul_pow]`. Conclude with `mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hP0 hPn 2) (sq_nonneg _)`. Conclude with `(pow_le_pow_iff_left₀ hny (by positivity) two_ne_zero).1 hsq`.
-/
theorem numHC_addI_le (x : Fin n → ℝ) (hinj : Function.Injective x) (hint : ∀ a b, ∃ m : ℤ, x a - x b = m)
    (I : Finset (Fin n)) :
    numHC (fun i => x i + if i ∈ I then 1 else 0) ≤ (n : ℝ) ^ I.card * numHC x := by
  classical
  set y : Fin n → ℝ := fun i => x i + if i ∈ I then 1 else 0 with hydef
  set f : Fin n → Fin n → ℝ := fun a b => |y a - y b| / |x a - x b| with hf
  have hx0 : ∀ a b, a ≠ b → |x a - x b| ≠ 0 := fun a b h =>
    abs_ne_zero.2 (sub_ne_zero.2 fun e => h (hinj e))
  have hfs : ∀ a b, f a b = f b a := fun a b => by simp only [hf, abs_sub_comm]
  have hy : ∀ a b, a ≠ b → |y a - y b| = f a b * |x a - x b| := fun a b h => by
    simp only [hf]; rw [div_mul_cancel₀ _ (hx0 a b h)]
  have hf1 : ∀ a b, a ≠ b → (a ∈ I ↔ b ∈ I) → f a b = 1 := by
    intro a b h hab
    simp only [hf, hydef]
    have : (x a + if a ∈ I then 1 else 0) - (x b + if b ∈ I then 1 else 0) = x a - x b := by
      by_cases ha : a ∈ I
      · rw [if_pos ha, if_pos (hab.1 ha)]; ring
      · rw [if_neg ha, if_neg (fun hb => ha (hab.2 hb))]; ring
    rw [this, div_self (hx0 a b h)]
  have hsqy : numHC y ^ 2 = ∏ a : Fin n, ∏ b ∈ univ.erase a, |y a - y b| :=
    sq_prod_lt _ fun a b => abs_sub_comm _ _
  have hsqx : numHC x ^ 2 = ∏ a : Fin n, ∏ b ∈ univ.erase a, |x a - x b| :=
    sq_prod_lt _ fun a b => abs_sub_comm _ _
  have hsplit : ∏ a : Fin n, ∏ b ∈ univ.erase a, |y a - y b| =
      (∏ a : Fin n, ∏ b ∈ univ.erase a, f a b) * numHC x ^ 2 := by
    rw [hsqx, ← prod_mul_distrib]
    refine prod_congr rfl fun a _ => ?_
    rw [← prod_mul_distrib]
    exact prod_congr rfl fun b hb => hy a b (ne_of_mem_erase hb).symm
  set Pr := ∏ s ∈ I, ∏ t ∈ univ \ I, f s t with hPr
  have hff : ∏ a : Fin n, ∏ b ∈ univ.erase a, f a b = Pr ^ 2 := by
    have hin : ∀ a ∈ I, ∏ b ∈ univ.erase a, f a b = ∏ b ∈ univ \ I, f a b := by
      intro a ha
      symm
      apply prod_subset
      · intro b hb
        rw [mem_sdiff] at hb
        exact mem_erase.2 ⟨fun e => hb.2 (e ▸ ha), mem_univ b⟩
      · intro b hb hb'
        have hba : b ≠ a := ne_of_mem_erase hb
        have hbI : b ∈ I := by
          by_contra h
          exact hb' (mem_sdiff.2 ⟨mem_univ b, h⟩)
        exact hf1 a b hba.symm ⟨fun _ => hbI, fun _ => ha⟩
    have hout : ∀ a ∉ I, ∏ b ∈ univ.erase a, f a b = ∏ b ∈ I, f a b := by
      intro a ha
      symm
      apply prod_subset
      · intro b hb
        exact mem_erase.2 ⟨fun e => ha (e ▸ hb), mem_univ b⟩
      · intro b hb hb'
        have hba : b ≠ a := ne_of_mem_erase hb
        exact hf1 a b hba.symm ⟨fun h => absurd h ha, fun h => absurd h hb'⟩
    rw [← prod_filter_mul_prod_filter_not univ (fun a => a ∈ I)]
    have e1 : univ.filter (fun a : Fin n => a ∈ I) = I := by ext a; simp
    have e2 : univ.filter (fun a : Fin n => a ∉ I) = univ \ I := by ext a; simp
    rw [e1, e2, prod_congr rfl hin, prod_congr rfl (fun a ha => hout a (mem_sdiff.1 ha).2)]
    have hC : ∏ a ∈ univ \ I, ∏ b ∈ I, f a b = ∏ b ∈ I, ∏ a ∈ univ \ I, f a b := prod_comm
    rw [hC, sq]
    congr 1
    exact prod_congr rfl fun s _ => prod_congr rfl fun t _ => hfs t s
  have hP0 : 0 ≤ Pr := prod_nonneg fun s _ => prod_nonneg fun t _ => by positivity
  have hPn : Pr ≤ (n : ℝ) ^ I.card := by
    rw [← prod_const]
    refine prod_le_prod (fun s _ => prod_nonneg fun t _ => by positivity) fun s hs => ?_
    have e : ∏ t ∈ univ \ I, f s t = ∏ t ∈ univ \ I, |x s + 1 - x t| / |x s - x t| := by
      refine prod_congr rfl fun t ht => ?_
      have htI : t ∉ I := (mem_sdiff.1 ht).2
      simp only [hf, hydef, if_pos hs, if_neg htI]
      congr 1
      ring_nf
    rw [e]
    exact prod_ratio_le x hinj hint s (univ \ I) (fun h => (mem_sdiff.1 h).2 hs)
  have hny : 0 ≤ numHC y := prod_nonneg fun a _ => prod_nonneg fun b _ => abs_nonneg _
  have hnx : 0 ≤ numHC x := prod_nonneg fun a _ => prod_nonneg fun b _ => abs_nonneg _
  have hsq : numHC y ^ 2 ≤ ((n : ℝ) ^ I.card * numHC x) ^ 2 := by
    rw [hsqy, hsplit, hff, mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hP0 hPn 2) (sq_nonneg _)
  exact (pow_le_pow_iff_left₀ hny (by positivity) two_ne_zero).1 hsq

/- English proof (translation)
Unfold `PI.UpqRep.fdegHC`. Establish `hD : 0 ≤ ∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ))` using `prod_nonneg fun a _ => prod_nonneg fun b hb => by`. Use `(mem_filter.1 hb).2` as an intermediate fact. Establish `: ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ)` using `by exact_mod_cast this`. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite using `[mul_div_assoc']`. Conclude with `div_le_div_of_nonneg_right (numHC_addI_le x hinj hint I) hD`.
-/
theorem fdegHC_addI_le (x : Fin n → ℝ) (hinj : Function.Injective x) (hint : ∀ a b, ∃ m : ℤ, x a - x b = m)
    (I : Finset (Fin n)) :
    PI.UpqRep.fdegHC (fun i => x i + if i ∈ I then 1 else 0) ≤ (n : ℝ) ^ I.card * PI.UpqRep.fdegHC x := by
  unfold PI.UpqRep.fdegHC
  have hD : 0 ≤ ∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) :=
    prod_nonneg fun a _ => prod_nonneg fun b hb => by
      have := (mem_filter.1 hb).2
      have : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast this
      linarith
  rw [mul_div_assoc']
  exact div_le_div_of_nonneg_right (numHC_addI_le x hinj hint I) hD

end Formalism.FourierDecayAlt.P.CutBP.JmuHC
