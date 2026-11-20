import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TZero

open Finset GlobalTheory.CompanionTheory.CoefId

namespace GlobalTheory.CompanionTheory.CoefId.Unique

variable {n : ℕ}

/- English proof (translation)
Establish `h : ∀ a, v a * ((T.filter fun p => g p = a).card : ℤ) = ∑ p ∈ T.filter (fun p => g p = a), v (g p)`. Introduce `a`. Rewrite using `[Finset.sum_congr rfl (g := fun _ => v a) (fun p hp => by rw [(Finset.mem_filter.1 hp).2])]`. Simplify using `[mul_comm]`. Repeatedly rewrite using `[h]`.

Conclude with `Finset.sum_fiberwise T g (fun p => v (g p))`.
-/
theorem sum_mul_card_fiber (T : Finset (Fin n × Fin n)) (g : Fin n × Fin n → Fin n) (v : Fin n → ℤ) :
    ∑ a, v a * ((T.filter fun p => g p = a).card : ℤ) = ∑ p ∈ T, v (g p) := by
  have h : ∀ a, v a * ((T.filter fun p => g p = a).card : ℤ)
      = ∑ p ∈ T.filter (fun p => g p = a), v (g p) := by
    intro a
    rw [Finset.sum_congr rfl (g := fun _ => v a) (fun p hp => by rw [(Finset.mem_filter.1 hp).2])]
    simp [mul_comm]
  simp_rw [h]
  exact Finset.sum_fiberwise T g (fun p => v (g p))

/- English proof (translation)
Establish `h1 : ∑ a, v a * score T a = ∑ p ∈ T, v p.1 + ∑ p ∈ prs n \ T, v p.2`. Simplify using `only [score, mul_add, Finset.sum_add_distrib]`. Rewrite using `[sum_mul_card_fiber T Prod.fst v, sum_mul_card_fiber (prs n \ T) Prod.snd v]`. Establish `h2 : ∑ p ∈ prs n, (if p ∈ T then v p.1 else v p.2) = ∑ p ∈ prs n \ T, (if p ∈ T then v p.1 else v p.2) + ∑ p ∈ T, (if p ∈ T then v p.1 else v p.2)` using `(Finset.sum_sdiff hT).symm`. Establish `h3 : ∑ p ∈ prs n \ T, (if p ∈ T then v p.1 else v p.2) = ∑ p ∈ prs n \ T, v p.2` using `Finset.sum_congr rfl fun p hp => if_neg (Finset.mem_sdiff.1 hp).2`.

Establish `h4 : ∑ p ∈ T, (if p ∈ T then v p.1 else v p.2) = ∑ p ∈ T, v p.1` using `Finset.sum_congr rfl fun p hp => if_pos hp`. Rewrite using `[h1, h2, h3, h4, add_comm]`.
-/
theorem pair_sum (v : Fin n → ℤ) (T : Finset (Fin n × Fin n)) (hT : T ⊆ prs n) :
    ∑ a, v a * score T a = ∑ p ∈ prs n, (if p ∈ T then v p.1 else v p.2) := by
  have h1 : ∑ a, v a * score T a = ∑ p ∈ T, v p.1 + ∑ p ∈ prs n \ T, v p.2 := by
    simp only [score, mul_add, Finset.sum_add_distrib]
    rw [sum_mul_card_fiber T Prod.fst v, sum_mul_card_fiber (prs n \ T) Prod.snd v]
  have h2 : ∑ p ∈ prs n, (if p ∈ T then v p.1 else v p.2)
      = ∑ p ∈ prs n \ T, (if p ∈ T then v p.1 else v p.2)
        + ∑ p ∈ T, (if p ∈ T then v p.1 else v p.2) := (Finset.sum_sdiff hT).symm
  have h3 : ∑ p ∈ prs n \ T, (if p ∈ T then v p.1 else v p.2) = ∑ p ∈ prs n \ T, v p.2 :=
    Finset.sum_congr rfl fun p hp => if_neg (Finset.mem_sdiff.1 hp).2
  have h4 : ∑ p ∈ T, (if p ∈ T then v p.1 else v p.2) = ∑ p ∈ T, v p.1 :=
    Finset.sum_congr rfl fun p hp => if_pos hp
  rw [h1, h2, h3, h4, add_comm]

/- English proof (translation)
Rewrite using `[pair_sum v T hT]`. Use `Finset.sum_le_sum fun p _ => ?_` and prove the remaining obligations. Use `split_ifs`. Conclude with `le_max_left _ _`. Conclude with `le_max_right _ _`.
-/
theorem pair_le (v : Fin n → ℤ) (T : Finset (Fin n × Fin n)) (hT : T ⊆ prs n) :
    ∑ a, v a * score T a ≤ ∑ p ∈ prs n, max (v p.1) (v p.2) := by
  rw [pair_sum v T hT]
  refine Finset.sum_le_sum fun p _ => ?_
  split_ifs
  · exact le_max_left _ _
  · exact le_max_right _ _

/- English proof (translation)
The claim follows from `Finset.filter_subset _ _`.
-/
theorem tZero_subset (lev : Fin n → ℕ) : tZero lev ⊆ prs n := Finset.filter_subset _ _

/- English proof (translation)
Establish `hlt : p.1 < p.2` using `(Finset.mem_filter.1 hp).2`. Distinguish the cases in `h : lev p.1 < lev p.2`. Establish `hm : p ∈ tZero lev` using `Finset.mem_filter.2 ⟨hp, h⟩`. Rewrite using `[if_pos hm, max_eq_left (h1 _ _ h)]`. Establish `he : lev p.1 = lev p.2` using `le_antisymm (hlev hlt.le) (not_lt.1 h)`.

Establish `hm : p ∉ tZero lev` using `fun hm => h (Finset.mem_filter.1 hm).2`. Rewrite using `[if_neg hm, max_eq_right (h2 _ _ hlt he)]`.
-/
theorem tZero_term (lev : Fin n → ℕ) (hlev : Monotone lev) (v : Fin n → ℤ)
    (h1 : ∀ a b, lev a < lev b → v b ≤ v a) (h2 : ∀ a b, a < b → lev a = lev b → v a ≤ v b)
    (p : Fin n × Fin n) (hp : p ∈ prs n) :
    (if p ∈ tZero lev then v p.1 else v p.2) = max (v p.1) (v p.2) := by
  have hlt : p.1 < p.2 := (Finset.mem_filter.1 hp).2
  by_cases h : lev p.1 < lev p.2
  · have hm : p ∈ tZero lev := Finset.mem_filter.2 ⟨hp, h⟩
    rw [if_pos hm, max_eq_left (h1 _ _ h)]
  · have he : lev p.1 = lev p.2 := le_antisymm (hlev hlt.le) (not_lt.1 h)
    have hm : p ∉ tZero lev := fun hm => h (Finset.mem_filter.1 hm).2
    rw [if_neg hm, max_eq_right (h2 _ _ hlt he)]

/- English proof (translation)
Rewrite using `[pair_sum v _ (tZero_subset lev)]`. Conclude with `Finset.sum_congr rfl (tZero_term lev hlev v h1 h2)`.
-/
theorem tZero_eq (lev : Fin n → ℕ) (hlev : Monotone lev) (v : Fin n → ℤ)
    (h1 : ∀ a b, lev a < lev b → v b ≤ v a) (h2 : ∀ a b, a < b → lev a = lev b → v a ≤ v b) :
    ∑ a, v a * score (tZero lev) a = ∑ p ∈ prs n, max (v p.1) (v p.2) := by
  rw [pair_sum v _ (tZero_subset lev)]
  exact Finset.sum_congr rfl (tZero_term lev hlev v h1 h2)

/- English proof (translation)
Establish `hsplit : ∀ a b, f a b = (if a < b then f a b else 0) + (if b < a then f b a else 0) + (if a = b then f a a else 0)`. Introduce `a b`. Break down `lt_trichotomy a b with h | h | h` into its components or cases. Simplify using `[h, h.ne, h.le, not_lt.2 h.le]`. Substitute `h` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[h, h.ne', not_lt.2 h.le, hf a b]`. Establish `hA : ∑ a, ∑ b, (if a < b then f a b else 0) = ∑ p ∈ prs n, f p.1 p.2`. Rewrite using `[prs, Finset.sum_filter, ← Finset.univ_product_univ, Finset.sum_product]`. Establish `hB : ∑ a, ∑ b, (if b < a then f b a else 0) = ∑ p ∈ prs n, f p.1 p.2`.

Rewrite using `[Finset.sum_comm]`. Conclude with `hA`. Establish `hC : ∑ a, ∑ b, (if a = b then f a a else 0) = ∑ a, f a a` using `by simp`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Finset.sum_add_distrib]`.

Rewrite using `[hA, hB, hC]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_sym (f : Fin n → Fin n → ℤ) (hf : ∀ a b, f a b = f b a) :
    ∑ a, ∑ b, f a b = 2 * ∑ p ∈ prs n, f p.1 p.2 + ∑ a, f a a := by
  have hsplit : ∀ a b, f a b = (if a < b then f a b else 0) + (if b < a then f b a else 0)
      + (if a = b then f a a else 0) := by
    intro a b
    rcases lt_trichotomy a b with h | h | h
    · simp [h, h.ne, h.le, not_lt.2 h.le]
    · subst h; simp
    · simp [h, h.ne', not_lt.2 h.le, hf a b]
  have hA : ∑ a, ∑ b, (if a < b then f a b else 0) = ∑ p ∈ prs n, f p.1 p.2 := by
    rw [prs, Finset.sum_filter, ← Finset.univ_product_univ, Finset.sum_product]
  have hB : ∑ a, ∑ b, (if b < a then f b a else 0) = ∑ p ∈ prs n, f p.1 p.2 := by
    rw [Finset.sum_comm]; exact hA
  have hC : ∑ a, ∑ b, (if a = b then f a a else 0) = ∑ a, f a a := by simp
  calc ∑ a, ∑ b, f a b
      = ∑ a, ∑ b, ((if a < b then f a b else 0) + (if b < a then f b a else 0)
          + (if a = b then f a a else 0)) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => hsplit a b
    _ = 2 * ∑ p ∈ prs n, f p.1 p.2 + ∑ a, f a a := by
        simp only [Finset.sum_add_distrib]
        rw [hA, hB, hC]; ring

/- English proof (translation)
Establish `e1` using `sum_sym (fun a b => max (v (σ a)) (v (σ b))) (fun a b => max_comm _ _)`. Establish `e2` using `sum_sym (fun a b => max (v a) (v b)) (fun a b => max_comm _ _)`. Establish `e3 : ∑ a, ∑ b, max (v (σ a)) (v (σ b)) = ∑ a, ∑ b, max (v a) (v b)`. Rewrite using `[← Equiv.sum_comp σ (fun a => ∑ b, max (v a) (v b))]`. Conclude with `Finset.sum_congr rfl fun a _ => Equiv.sum_comp σ (fun b => max (v (σ a)) (v b))`.

Establish `e4 : ∑ a, max (v (σ a)) (v (σ a)) = ∑ a, max (v a) (v a)` using `Equiv.sum_comp σ (fun a => max (v a) (v a))`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem sum_max_perm (σ : Equiv.Perm (Fin n)) (v : Fin n → ℤ) :
    ∑ p ∈ prs n, max (v (σ p.1)) (v (σ p.2)) = ∑ p ∈ prs n, max (v p.1) (v p.2) := by
  have e1 := sum_sym (fun a b => max (v (σ a)) (v (σ b))) (fun a b => max_comm _ _)
  have e2 := sum_sym (fun a b => max (v a) (v b)) (fun a b => max_comm _ _)
  have e3 : ∑ a, ∑ b, max (v (σ a)) (v (σ b)) = ∑ a, ∑ b, max (v a) (v b) := by
    rw [← Equiv.sum_comp σ (fun a => ∑ b, max (v a) (v b))]
    exact Finset.sum_congr rfl fun a _ => Equiv.sum_comp σ (fun b => max (v (σ a)) (v b))
  have e4 : ∑ a, max (v (σ a)) (v (σ a)) = ∑ a, max (v a) (v a) :=
    Equiv.sum_comp σ (fun a => max (v a) (v a))
  linarith

/- English proof (translation)
Use `set j := lev a₀ with hj`. Use `set w : Fin n → ℤ := fun a => if lev a ≤ j then 1 else 0 with hw`. Establish `hw1 : ∀ a b, lev a < lev b → w b ≤ w a`. Introduce `a b h`. Simplify using `only [hw]`.

Apply the tactic sequence `split_ifs <;> first | omega | simp`. Establish `hw2 : ∀ a b, a < b → lev a = lev b → w a ≤ w b`. Introduce `a b _ h`. Simplify using `only [hw, h]`. Conclude with `le_refl _`.

Establish `hle : ∑ a, w a * score T a ≤ ∑ a, w a * score (tZero lev) a`. Rewrite using `[tZero_eq lev hlev w hw1 hw2]`. Conclude with `pair_le w T hT`. Establish `hsum : ∑ a, w a * (L a - L (σ a)) ≤ 0`. Establish `: ∑ a, w a * score T a = ∑ a, w a * score (tZero lev) a + 2 * ∑ a, w a * (L a - L (σ a))`.

Rewrite using `[Finset.mul_sum, ← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun a _ => by rw [hs a]; ring`. Combine the linear equalities and inequalities to obtain the conclusion. Use `set A : Finset (Fin n) := Finset.univ.filter fun a => lev a ≤ j with hA`. Establish `hAne : A.Nonempty` using `⟨a₀, by simp [hA, hj]⟩`.

Use `set b₀ := A.max' hAne with hb₀`. Establish `hb₀A : lev b₀ ≤ j`. Use `A.max'_mem hAne` as an intermediate fact. Simplify `this` using `[hA]`. Use `set τ : ℤ := L b₀ - 1 with hτ`.

Establish `hin : ∀ a, lev a ≤ j → 1 ≤ L a - τ`. Introduce `a ha`. Establish `: a ≤ b₀` using `A.le_max' a (by simp [hA, ha])`. Use `hL.antitone this` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Establish `hout : ∀ a, ¬ lev a ≤ j → L a - τ ≤ 0`. Introduce `a ha`. Establish `hlt : b₀ < a`. Assume the negation of the conclusion as `hc`. Conclude with `ha ((hlev (not_lt.1 hc)).trans hb₀A)`.

Use `hL hlt` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use `set u : Fin n → ℤ := fun a => w (σ.symm a) with hu`. Establish `hwσ : ∑ a, u a = ∑ a, w a` using `Equiv.sum_comp σ.symm w`. Establish `huL : ∑ a, w a * L (σ a) = ∑ a, u a * L a`.

Rewrite using `[← Equiv.sum_comp σ (fun a => u a * L a)]`. Simplify using `[hu]`. Establish `hid : ∑ a, (w a - u a) * (L a - τ) = ∑ a, w a * (L a - L (σ a))`. Establish `l : ∑ a, (w a - u a) * (L a - τ) = ∑ a, w a * L a - ∑ a, u a * L a - τ * (∑ a, w a - ∑ a, u a)`. Rewrite using `[← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib]`.

Conclude with `Finset.sum_congr rfl fun a _ => by ring`. Establish `m : ∑ a, w a * (L a - L (σ a)) = ∑ a, w a * L a - ∑ a, w a * L (σ a)`. Rewrite using `[← Finset.sum_sub_distrib]`. Conclude with `Finset.sum_congr rfl fun a _ => by ring`. Rewrite using `[l, m, huL, hwσ]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hu01 : ∀ a, 0 ≤ u a ∧ u a ≤ 1`. Introduce `a`. Simplify using `only [hu, hw]`. Apply the tactic sequence `split_ifs <;> simp`.

Establish `hnn : ∀ a, 0 ≤ (w a - u a) * (L a - τ)`. Introduce `a`. Distinguish the cases in `ha : lev a ≤ j`. Establish `hwa : w a = 1` using `by simp [hw, ha]`. Rewrite using `[hwa]`.

Conclude with `mul_nonneg (by linarith [(hu01 a).2]) (by linarith [hin a ha])`. Establish `hwa : w a = 0` using `by simp [hw, ha]`. Rewrite using `[hwa]`. Use polynomial arithmetic with `[(hu01 a).1, hout a ha]`. Establish `hz : ∑ a, (w a - u a) * (L a - τ) = 0` using `le_antisymm (hid ▸ hsum) (Finset.sum_nonneg fun a _ => hnn a)`.

Establish `hz₀` using `(Finset.sum_eq_zero_iff_of_nonneg (fun a _ => hnn a)).1 hz a₀ (Finset.mem_univ _)`. Assume the negation of the conclusion as `hc`. Establish `hu0 : u a₀ = 0` using `by simp [hu, hw, hc]`. Establish `hw0 : w a₀ = 1` using `by simp [hw, hj]`. Rewrite `hz₀` using `[hu0, hw0]`.

Use `hin a₀ le_rfl` as an intermediate fact. Simplify using `only [sub_zero, one_mul] at hz₀`. Use linear arithmetic over natural numbers and integers.
-/
theorem lev_symm_le {lev : Fin n → ℕ} (hlev : Monotone lev) {L : Fin n → ℤ} (hL : StrictAnti L)
    (σ : Equiv.Perm (Fin n)) (T : Finset (Fin n × Fin n)) (hT : T ⊆ prs n)
    (hs : ∀ a, score T a = score (tZero lev) a + 2 * (L a - L (σ a))) (a₀ : Fin n) :
    lev (σ.symm a₀) ≤ lev a₀ := by
  set j := lev a₀ with hj
  set w : Fin n → ℤ := fun a => if lev a ≤ j then 1 else 0 with hw
  have hw1 : ∀ a b, lev a < lev b → w b ≤ w a := by
    intro a b h
    simp only [hw]
    split_ifs <;> first | omega | simp
  have hw2 : ∀ a b, a < b → lev a = lev b → w a ≤ w b := by
    intro a b _ h
    simp only [hw, h]; exact le_refl _
  have hle : ∑ a, w a * score T a ≤ ∑ a, w a * score (tZero lev) a := by
    rw [tZero_eq lev hlev w hw1 hw2]; exact pair_le w T hT
  have hsum : ∑ a, w a * (L a - L (σ a)) ≤ 0 := by
    have : ∑ a, w a * score T a
        = ∑ a, w a * score (tZero lev) a + 2 * ∑ a, w a * (L a - L (σ a)) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun a _ => by rw [hs a]; ring
    linarith

  set A : Finset (Fin n) := Finset.univ.filter fun a => lev a ≤ j with hA
  have hAne : A.Nonempty := ⟨a₀, by simp [hA, hj]⟩
  set b₀ := A.max' hAne with hb₀
  have hb₀A : lev b₀ ≤ j := by
    have := A.max'_mem hAne
    simpa [hA] using this
  set τ : ℤ := L b₀ - 1 with hτ
  have hin : ∀ a, lev a ≤ j → 1 ≤ L a - τ := by
    intro a ha
    have : a ≤ b₀ := A.le_max' a (by simp [hA, ha])
    have := hL.antitone this
    omega
  have hout : ∀ a, ¬ lev a ≤ j → L a - τ ≤ 0 := by
    intro a ha
    have hlt : b₀ < a := by
      by_contra hc
      exact ha ((hlev (not_lt.1 hc)).trans hb₀A)
    have := hL hlt
    omega
  set u : Fin n → ℤ := fun a => w (σ.symm a) with hu
  have hwσ : ∑ a, u a = ∑ a, w a := Equiv.sum_comp σ.symm w
  have huL : ∑ a, w a * L (σ a) = ∑ a, u a * L a := by
    rw [← Equiv.sum_comp σ (fun a => u a * L a)]
    simp [hu]
  have hid : ∑ a, (w a - u a) * (L a - τ) = ∑ a, w a * (L a - L (σ a)) := by
    have l : ∑ a, (w a - u a) * (L a - τ)
        = ∑ a, w a * L a - ∑ a, u a * L a - τ * (∑ a, w a - ∑ a, u a) := by
      rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum,
        ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun a _ => by ring
    have m : ∑ a, w a * (L a - L (σ a)) = ∑ a, w a * L a - ∑ a, w a * L (σ a) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun a _ => by ring
    rw [l, m, huL, hwσ]; ring
  have hu01 : ∀ a, 0 ≤ u a ∧ u a ≤ 1 := by
    intro a
    simp only [hu, hw]
    split_ifs <;> simp
  have hnn : ∀ a, 0 ≤ (w a - u a) * (L a - τ) := by
    intro a
    by_cases ha : lev a ≤ j
    · have hwa : w a = 1 := by simp [hw, ha]
      rw [hwa]
      exact mul_nonneg (by linarith [(hu01 a).2]) (by linarith [hin a ha])
    · have hwa : w a = 0 := by simp [hw, ha]
      rw [hwa]
      nlinarith [(hu01 a).1, hout a ha]
  have hz : ∑ a, (w a - u a) * (L a - τ) = 0 :=
    le_antisymm (hid ▸ hsum) (Finset.sum_nonneg fun a _ => hnn a)
  have hz₀ := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => hnn a)).1 hz a₀ (Finset.mem_univ _)
  by_contra hc
  have hu0 : u a₀ = 0 := by simp [hu, hw, hc]
  have hw0 : w a₀ = 1 := by simp [hw, hj]
  rw [hu0, hw0] at hz₀
  have := hin a₀ le_rfl
  simp only [sub_zero, one_mul] at hz₀
  omega

/- English proof (translation)
Establish `hle : ∀ a, lev (σ.symm a) ≤ lev a` using `lev_symm_le hlev hL σ T hT hs`. Establish `hsum : ∑ a, lev (σ.symm a) = ∑ a, lev a` using `Equiv.sum_comp σ.symm lev`. Establish `h` using `(Finset.sum_eq_sum_iff_of_le (fun a _ => hle a)).1 hsum (σ a) (Finset.mem_univ _)`. Simplify using `using h.symm`.
-/
theorem lev_comp {lev : Fin n → ℕ} (hlev : Monotone lev) {L : Fin n → ℤ} (hL : StrictAnti L)
    (σ : Equiv.Perm (Fin n)) (T : Finset (Fin n × Fin n)) (hT : T ⊆ prs n)
    (hs : ∀ a, score T a = score (tZero lev) a + 2 * (L a - L (σ a))) (a : Fin n) :
    lev (σ a) = lev a := by
  have hle : ∀ a, lev (σ.symm a) ≤ lev a := lev_symm_le hlev hL σ T hT hs
  have hsum : ∑ a, lev (σ.symm a) = ∑ a, lev a := Equiv.sum_comp σ.symm lev
  have h := (Finset.sum_eq_sum_iff_of_le (fun a _ => hle a)).1 hsum (σ a) (Finset.mem_univ _)
  simpa using h.symm

def rk (lev : Fin n → ℕ) : Fin n → ℤ := fun a => -((n : ℤ) + 1) * (lev a : ℤ) + ((a : ℕ) : ℤ)

/- English proof (translation)
Simplify using `only [rk]`. Establish `ha : (0 : ℤ) ≤ ((a : ℕ) : ℤ)` using `by positivity`. Establish `hb : ((b : ℕ) : ℤ) < n` using `by exact_mod_cast b.2`. Establish `h' : (lev a : ℤ) + 1 ≤ lev b` using `by exact_mod_cast h`. Establish `hn : (0 : ℤ) ≤ (n : ℤ) + 1` using `by positivity`.

Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left h' hn]`.
-/
theorem rk_lt_of_lev {lev : Fin n → ℕ} {a b : Fin n} (h : lev a < lev b) :
    rk lev b < rk lev a := by
  simp only [rk]
  have ha : (0 : ℤ) ≤ ((a : ℕ) : ℤ) := by positivity
  have hb : ((b : ℕ) : ℤ) < n := by exact_mod_cast b.2
  have h' : (lev a : ℤ) + 1 ≤ lev b := by exact_mod_cast h
  have hn : (0 : ℤ) ≤ (n : ℤ) + 1 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h' hn]

/- English proof (translation)
Simplify using `only [rk, h]`. Establish `: ((a : ℕ) : ℤ) < ((b : ℕ) : ℤ)` using `by exact_mod_cast hab`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem rk_lt_of_eq {lev : Fin n → ℕ} {a b : Fin n} (hab : a < b) (h : lev a = lev b) :
    rk lev a < rk lev b := by
  simp only [rk, h]
  have : ((a : ℕ) : ℤ) < ((b : ℕ) : ℤ) := by exact_mod_cast hab
  linarith

/- English proof (translation)
Use `set t := score (tZero lev) with ht`. Use `set r := rk lev with hr`. Use `set d : Fin n → ℤ := fun a => ((σ a : ℕ) : ℤ) - ((a : ℕ) : ℤ) with hd`. Establish `hr1 : ∀ a b, lev a < lev b → r b ≤ r a` using `fun a b h => (rk_lt_of_lev h).le`. Establish `hr2 : ∀ a b, a < b → lev a = lev b → r a ≤ r b` using `fun a b h h' => (rk_lt_of_eq h h').le`.

Establish `hrd : ∀ a, r (σ a) = r a + d a`. Introduce `a`. Simplify using `only [hr, rk, hd, hl a]`. Expand and normalize the polynomial expressions, which then agree. Establish `hLd : ∀ a, L a - L (σ a) = d a` using `fun a => h3 a (σ a) (hl a).symm`.

Establish `hCd : ∀ a, t (σ a) - r (σ a) = t a - r a`. Introduce `a`. Use `h4 (σ a) a (hl a)` as an intermediate fact. Simplify using `only [hr, rk, hl a]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `key : ∑ a, r (σ a) * score T a ≤ ∑ a, r a * t a`. Combine the equalities or inequalities in the displayed calculation. Establish `e1 : ∑ a, r (σ a) * score T a = ∑ a, r a * t a + 3 * ∑ a, r a * d a + ∑ a, d a * (t a - r a) + 2 * ∑ a, d a ^ 2`. Rewrite using `[Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations.

Rewrite using `[hs a, hLd a, hrd a]`. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : ∑ a, d a * (t a - r a) = 0`. Establish `h` using `Equiv.sum_comp σ (fun a => r a * (t a - r a))`. Establish `h' : ∑ a, r (σ a) * (t (σ a) - r (σ a)) = ∑ a, r a * (t a - r a) + ∑ a, d a * (t a - r a)`.

Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[hCd a, hrd a]`. Expand and normalize the polynomial expressions, which then agree. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `e3 : 2 * ∑ a, r a * d a + ∑ a, d a ^ 2 = 0`. Establish `h` using `Equiv.sum_comp σ (fun a => r a ^ 2)`. Establish `h' : ∑ a, r (σ a) ^ 2 = ∑ a, r a ^ 2 + (2 * ∑ a, r a * d a + ∑ a, d a ^ 2)`. Rewrite using `[Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations.

Rewrite using `[hrd a]`. Expand and normalize the polynomial expressions, which then agree. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hdd : ∑ a, d a ^ 2 = 0`. Use `le_antisymm (by linarith) (Finset.sum_nonneg fun a _ => by positivity)` and prove the remaining obligations.

Use extensionality with `a`. Establish `h0` using `(Finset.sum_eq_zero_iff_of_nonneg (fun a _ => by positivity)).1 hdd a (Finset.mem_univ _)`. Establish `h1 : d a = 0` using `by simpa using h0`. Establish `h2 : ((σ a : ℕ) : ℤ) = ((a : ℕ) : ℤ)`. Simplify using `only [hd] at h1`.

Combine the linear equalities and inequalities to obtain the conclusion. Simplify using `using h2`.
-/
theorem sigma_eq_one {lev : Fin n → ℕ} (hlev : Monotone lev) {L : Fin n → ℤ}
    (h3 : ∀ a b, lev a = lev b → L a - L b = ((b : ℕ) : ℤ) - ((a : ℕ) : ℤ))
    (h4 : ∀ a b, lev a = lev b →
      score (tZero lev) a - ((a : ℕ) : ℤ) = score (tZero lev) b - ((b : ℕ) : ℤ))
    (σ : Equiv.Perm (Fin n)) (T : Finset (Fin n × Fin n)) (hT : T ⊆ prs n)
    (hs : ∀ a, score T a = score (tZero lev) a + 2 * (L a - L (σ a)))
    (hl : ∀ a, lev (σ a) = lev a) : σ = 1 := by
  set t := score (tZero lev) with ht
  set r := rk lev with hr
  set d : Fin n → ℤ := fun a => ((σ a : ℕ) : ℤ) - ((a : ℕ) : ℤ) with hd
  have hr1 : ∀ a b, lev a < lev b → r b ≤ r a := fun a b h => (rk_lt_of_lev h).le
  have hr2 : ∀ a b, a < b → lev a = lev b → r a ≤ r b := fun a b h h' => (rk_lt_of_eq h h').le
  have hrd : ∀ a, r (σ a) = r a + d a := by
    intro a
    simp only [hr, rk, hd, hl a]
    ring
  have hLd : ∀ a, L a - L (σ a) = d a := fun a => h3 a (σ a) (hl a).symm
  have hCd : ∀ a, t (σ a) - r (σ a) = t a - r a := by
    intro a
    have := h4 (σ a) a (hl a)
    simp only [hr, rk, hl a]
    linarith
  have key : ∑ a, r (σ a) * score T a ≤ ∑ a, r a * t a := by
    calc ∑ a, r (σ a) * score T a ≤ ∑ p ∈ prs n, max (r (σ p.1)) (r (σ p.2)) :=
          pair_le (fun a => r (σ a)) T hT
      _ = ∑ p ∈ prs n, max (r p.1) (r p.2) := sum_max_perm σ r
      _ = ∑ a, r a * t a := (tZero_eq lev hlev r hr1 hr2).symm
  have e1 : ∑ a, r (σ a) * score T a
      = ∑ a, r a * t a + 3 * ∑ a, r a * d a + ∑ a, d a * (t a - r a) + 2 * ∑ a, d a ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hs a, hLd a, hrd a]
    ring
  have e2 : ∑ a, d a * (t a - r a) = 0 := by
    have h := Equiv.sum_comp σ (fun a => r a * (t a - r a))
    have h' : ∑ a, r (σ a) * (t (σ a) - r (σ a))
        = ∑ a, r a * (t a - r a) + ∑ a, d a * (t a - r a) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hCd a, hrd a]
      ring
    linarith
  have e3 : 2 * ∑ a, r a * d a + ∑ a, d a ^ 2 = 0 := by
    have h := Equiv.sum_comp σ (fun a => r a ^ 2)
    have h' : ∑ a, r (σ a) ^ 2 = ∑ a, r a ^ 2 + (2 * ∑ a, r a * d a + ∑ a, d a ^ 2) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hrd a]
      ring
    linarith
  have hdd : ∑ a, d a ^ 2 = 0 := by
    refine le_antisymm (by linarith) (Finset.sum_nonneg fun a _ => by positivity)
  ext a
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => by positivity)).1 hdd a
    (Finset.mem_univ _)
  have h1 : d a = 0 := by simpa using h0
  have h2 : ((σ a : ℕ) : ℤ) = ((a : ℕ) : ℤ) := by
    simp only [hd] at h1
    linarith
  simpa using h2

/- English proof (translation)
Introduce `n lev hlev L hL h3 h4 σ T hT hs`. Establish `hσ : σ = 1` using `sigma_eq_one hlev h3 h4 σ T hT hs (lev_comp hlev hL σ T hT hs)`. Use `⟨hσ, ?_⟩` and prove the remaining obligations. Substitute `hσ` using the available equality. Establish `hst : ∀ a, score T a = score (tZero lev) a`.

Introduce `a`. Rewrite using `[hs a]`. Simplify using the standard rewrite rules. Establish `hr1 : ∀ a b, lev a < lev b → rk lev b ≤ rk lev a` using `fun a b h => (rk_lt_of_lev h).le`. Establish `hr2 : ∀ a b, a < b → lev a = lev b → rk lev a ≤ rk lev b` using `fun a b h h' => (rk_lt_of_eq h h').le`.

Establish `hsum : ∑ p ∈ prs n, (if p ∈ T then rk lev p.1 else rk lev p.2) = ∑ p ∈ prs n, max (rk lev p.1) (rk lev p.2)`. Rewrite using `[← pair_sum (rk lev) T hT, ← tZero_eq lev hlev (rk lev) hr1 hr2]`. Conclude with `Finset.sum_congr rfl fun a _ => by rw [hst a]`. Establish `hterm` using `(Finset.sum_eq_sum_iff_of_le (fun p _ => by split_ifs`. Conclude with `le_max_left _ _`.

Conclude with `le_max_right _ _)).1 hsum`. Use extensionality with `p`. Prove the components needed by the constructor for the conclusion. Introduce `hp`. Establish `hpp` using `hT hp`.

Establish `hlt : p.1 < p.2` using `(Finset.mem_filter.1 hpp).2`. Establish `h` using `hterm p hpp`. Rewrite `h` using `[if_pos hp]`. Use `Finset.mem_filter.2 ⟨hpp, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hc`.

Establish `he : lev p.1 = lev p.2` using `le_antisymm (hlev hlt.le) (not_lt.1 hc)`. Establish `h1` using `rk_lt_of_eq hlt he`. Establish `h2` using `le_max_right (rk lev p.1) (rk lev p.2)`. Use linear arithmetic over natural numbers and integers. Introduce `hp`.

Take `⟨hpp, hlt⟩` from `Finset.mem_filter.1 hp`. Assume the negation of the conclusion as `hc`. Establish `h` using `hterm p hpp`. Rewrite `h` using `[if_neg hc]`. Establish `h1` using `rk_lt_of_lev hlt`.

Establish `h2` using `le_max_left (rk lev p.1) (rk lev p.2)`. Use linear arithmetic over natural numbers and integers.
-/
theorem tournament_unique : ∀ {n : ℕ} (lev : Fin n → ℕ), Monotone lev → ∀ L : Fin n → ℤ, StrictAnti L →
    (∀ a b, lev a = lev b → L a - L b = ((b : ℕ) : ℤ) - ((a : ℕ) : ℤ)) →
    (∀ a b, lev a = lev b →
      score (tZero lev) a - ((a : ℕ) : ℤ) = score (tZero lev) b - ((b : ℕ) : ℤ)) →
    ∀ (σ : Equiv.Perm (Fin n)) (T : Finset (Fin n × Fin n)), T ⊆ prs n →
    (∀ a, score T a = score (tZero lev) a + 2 * (L a - L (σ a))) → σ = 1 ∧ T = tZero lev := by
  intro n lev hlev L hL h3 h4 σ T hT hs
  have hσ : σ = 1 :=
    sigma_eq_one hlev h3 h4 σ T hT hs (lev_comp hlev hL σ T hT hs)
  refine ⟨hσ, ?_⟩
  subst hσ
  have hst : ∀ a, score T a = score (tZero lev) a := by
    intro a
    rw [hs a]
    simp
  have hr1 : ∀ a b, lev a < lev b → rk lev b ≤ rk lev a := fun a b h => (rk_lt_of_lev h).le
  have hr2 : ∀ a b, a < b → lev a = lev b → rk lev a ≤ rk lev b :=
    fun a b h h' => (rk_lt_of_eq h h').le
  have hsum : ∑ p ∈ prs n, (if p ∈ T then rk lev p.1 else rk lev p.2)
      = ∑ p ∈ prs n, max (rk lev p.1) (rk lev p.2) := by
    rw [← pair_sum (rk lev) T hT, ← tZero_eq lev hlev (rk lev) hr1 hr2]
    exact Finset.sum_congr rfl fun a _ => by rw [hst a]
  have hterm := (Finset.sum_eq_sum_iff_of_le (fun p _ => by
    split_ifs
    · exact le_max_left _ _
    · exact le_max_right _ _)).1 hsum
  ext p
  constructor
  · intro hp
    have hpp := hT hp
    have hlt : p.1 < p.2 := (Finset.mem_filter.1 hpp).2
    have h := hterm p hpp
    rw [if_pos hp] at h
    refine Finset.mem_filter.2 ⟨hpp, ?_⟩
    by_contra hc
    have he : lev p.1 = lev p.2 := le_antisymm (hlev hlt.le) (not_lt.1 hc)
    have h1 := rk_lt_of_eq hlt he
    have h2 := le_max_right (rk lev p.1) (rk lev p.2)
    omega
  · intro hp
    obtain ⟨hpp, hlt⟩ := Finset.mem_filter.1 hp
    by_contra hc
    have h := hterm p hpp
    rw [if_neg hc] at h
    have h1 := rk_lt_of_lev hlt
    have h2 := le_max_left (rk lev p.1) (rk lev p.2)
    omega

end GlobalTheory.CompanionTheory.CoefId.Unique
