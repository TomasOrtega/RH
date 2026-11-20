import Mathlib

namespace Formalism.UG.P

open Finset

def satakeInv {α : Type} [LinearOrder α] (s S : Finset α) : ℕ :=
  ∑ a ∈ S, ((s \ S).filter (fun l => a < l)).card

/- English proof (translation)
Establish `hmS' : m ∉ s'` using `fun h => lt_irrefl m (hm m h)`. Establish `hmS : m ∉ S` using `fun h => hmS' (hS h)`. Unfold `satakeInv`. Rewrite using `[card_eq_sum_ones S, ← sum_add_distrib]`. Apply `sum_congr rfl` to reduce the goal to its premises.

Introduce `a ha`. Establish `e : (insert m s' \ S).filter (fun l => a < l) = insert m ((s' \ S).filter (fun l => a < l))`. Use extensionality with `x`. Distinguish the cases in `hx : x = m`. Simplify using `[hx, hmS, hm a (hS ha)]`.

Simplify using `[hx]`. Rewrite using `[e, card_insert_of_notMem (by simp [hmS'])]`.
-/
theorem satakeInv_insert_not_mem {α : Type} [LinearOrder α] (s' S : Finset α) (m : α)
    (hm : ∀ x ∈ s', x < m) (hS : S ⊆ s') :
    satakeInv (insert m s') S = satakeInv s' S + S.card := by
  have hmS' : m ∉ s' := fun h => lt_irrefl m (hm m h)
  have hmS : m ∉ S := fun h => hmS' (hS h)
  unfold satakeInv
  rw [card_eq_sum_ones S, ← sum_add_distrib]
  apply sum_congr rfl
  intro a ha
  have e : (insert m s' \ S).filter (fun l => a < l)
      = insert m ((s' \ S).filter (fun l => a < l)) := by
    ext x
    by_cases hx : x = m
    · simp [hx, hmS, hm a (hS ha)]
    · simp [hx]
  rw [e, card_insert_of_notMem (by simp [hmS'])]

/- English proof (translation)
Establish `hmS' : m ∉ s'` using `fun h => lt_irrefl m (hm m h)`. Establish `hmT : m ∉ T` using `fun h => hmS' (hT h)`. Unfold `satakeInv`. Rewrite using `[sum_insert hmT]`. Establish `e : insert m s' \ insert m T = s' \ T`.

Use extensionality with `x`. Distinguish the cases in `hx : x = m`. Simplify using `[hx, hmS']`. Simplify using `[hx]`. Rewrite using `[e]`.

Establish `h0 : ((s' \ T).filter (fun l => m < l)).card = 0`. Rewrite using `[card_eq_zero, filter_eq_empty_iff]`. Introduce `x hx`. Conclude with `not_lt.2 (le_of_lt (hm x (mem_sdiff.1 hx).1))`. Rewrite using `[h0, zero_add]`.
-/
theorem satakeInv_insert_mem {α : Type} [LinearOrder α] (s' T : Finset α) (m : α)
    (hm : ∀ x ∈ s', x < m) (hT : T ⊆ s') :
    satakeInv (insert m s') (insert m T) = satakeInv s' T := by
  have hmS' : m ∉ s' := fun h => lt_irrefl m (hm m h)
  have hmT : m ∉ T := fun h => hmS' (hT h)
  unfold satakeInv
  rw [sum_insert hmT]
  have e : insert m s' \ insert m T = s' \ T := by
    ext x
    by_cases hx : x = m
    · simp [hx, hmS']
    · simp [hx]
  rw [e]
  have h0 : ((s' \ T).filter (fun l => m < l)).card = 0 := by
    rw [card_eq_zero, filter_eq_empty_iff]
    intro x hx
    exact not_lt.2 (le_of_lt (hm x (mem_sdiff.1 hx).1))
  rw [h0, zero_add]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on_max`. Use `next =>`. Introduce `j`. Consider the cases of `j with`. Consider the case `zero => simp [satakeInv]`.

Consider the case `succ k`. Establish `h1 : powersetCard (k + 1) (∅ : Finset α) = ∅` using `powersetCard_eq_empty.2 (by simp)`. Rewrite using `[h1, sum_empty, zero_mul, prod_range_succ']`. Simplify using the standard rewrite rules. Use `next m s' hm ih =>`.

Establish `hmS' : m ∉ s'` using `fun h => lt_irrefl m (hm m h)`. Introduce `j`. Consider the cases of `j with`. Consider the case `zero => simp [satakeInv]`. Consider the case `succ k`.

Establish `hdisj : Disjoint (powersetCard (k + 1) s') ((powersetCard k s').image (insert m))`. Rewrite using `[disjoint_left]`. Introduce `S hS hS'`. Take `⟨T, -, rfl⟩` from `mem_image.1 hS'`. Conclude with `hmS' ((mem_powersetCard.1 hS).1 (mem_insert_self m T))`.

Establish `hinj : Set.InjOn (insert m) (powersetCard k s' : Set (Finset α))`. Introduce `T1 h1 T2 h2 h`. Establish `h1' : m ∉ T1` using `fun h' => hmS' ((mem_powersetCard.1 (mem_coe.1 h1)).1 h')`. Establish `h2' : m ∉ T2` using `fun h' => hmS' ((mem_powersetCard.1 (mem_coe.1 h2)).1 h')`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[powersetCard_succ_insert hmS', sum_union hdisj, sum_image hinj]`. Establish `e1 : ∑ S ∈ powersetCard (k + 1) s', q ^ satakeInv (insert m s') S = q ^ (k + 1) * ∑ S ∈ powersetCard (k + 1) s', q ^ satakeInv s' S`. Rewrite using `[mul_sum]`. Apply `sum_congr rfl` to reduce the goal to its premises. Introduce `S hS`.

Take `⟨hsub, hcard⟩` from `mem_powersetCard.1 hS`. Rewrite using `[satakeInv_insert_not_mem s' S m hm hsub, hcard, pow_add]`. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : ∑ T ∈ powersetCard k s', q ^ satakeInv (insert m s') (insert m T) = ∑ T ∈ powersetCard k s', q ^ satakeInv s' T` using `sum_congr rfl (fun T hT => by`. Rewrite using `[satakeInv_insert_mem s' T m hm (mem_powersetCard.1 hT).1])`.

Rewrite using `[e1, e2]`. Establish `hP : ∏ i ∈ range (k + 1), (q ^ (i + 1) - 1) = (∏ i ∈ range k, (q ^ (i + 1) - 1)) * (q ^ (k + 1) - 1)` using `prod_range_succ _ _`. Establish `hR : ∏ i ∈ range (k + 1), (q ^ (s'.card + 1 - i) - 1) = (∏ i ∈ range k, (q ^ (s'.card - i) - 1)) * (q ^ (s'.card + 1) - 1)`. Rewrite using `[prod_range_succ']`. Simplify using `only [Nat.add_sub_add_right, Nat.sub_zero]`.

Establish `hRk : ∏ i ∈ range (k + 1), (q ^ (s'.card - i) - 1) = (∏ i ∈ range k, (q ^ (s'.card - i) - 1)) * (q ^ (s'.card - k) - 1)` using `prod_range_succ _ _`. Establish `hsplit : (q ^ (k + 1) * ∑ S ∈ powersetCard (k + 1) s', q ^ satakeInv s' S + ∑ T ∈ powersetCard k s', q ^ satakeInv s' T) * ∏ i ∈ range (k + 1), (q ^ (i + 1) - 1) = q ^ (k + 1) * ((∑ S ∈ powersetCard (k + 1) s', q ^ satakeInv s' S) * ∏ i ∈ range (k + 1), (q ^ (i + 1) - 1)) + ((∑ T …`. Rewrite using `[hP]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[card_insert_of_notMem hmS', hR, hsplit, ih (k + 1), ih k, hRk]`.

Distinguish the cases in `hk : k ≤ s'.card`. Establish `hpow : q ^ (k + 1) * q ^ (s'.card - k) = q ^ (s'.card + 1)`. Rewrite using `[← pow_add]`. Use `congr 1`. Use linear arithmetic over natural numbers and integers.

Take the linear combination `(∏ i ∈ range k, (q ^ (s'.card - i) - 1)) * hpow`. Establish `hz : ∏ i ∈ range k, (q ^ (s'.card - i) - 1) = 0` using `prod_eq_zero (i := s'.card) (mem_range.2 (by omega)) (by simp)`. Rewrite using `[hz]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem satake_qbinom (q : ℤ) {α : Type} [LinearOrder α] (s : Finset α) :
    ∀ j : ℕ, (∑ S ∈ s.powersetCard j, q ^ satakeInv s S) * ∏ i ∈ range j, (q ^ (i + 1) - 1) =
      ∏ i ∈ range j, (q ^ (s.card - i) - 1) := by
  induction s using Finset.induction_on_max
  next =>
    intro j
    cases j with
    | zero => simp [satakeInv]
    | succ k =>
      have h1 : powersetCard (k + 1) (∅ : Finset α) = ∅ := powersetCard_eq_empty.2 (by simp)
      rw [h1, sum_empty, zero_mul, prod_range_succ']
      simp
  next m s' hm ih =>
    have hmS' : m ∉ s' := fun h => lt_irrefl m (hm m h)
    intro j
    cases j with
    | zero => simp [satakeInv]
    | succ k =>
      have hdisj : Disjoint (powersetCard (k + 1) s') ((powersetCard k s').image (insert m)) := by
        rw [disjoint_left]
        intro S hS hS'
        obtain ⟨T, -, rfl⟩ := mem_image.1 hS'
        exact hmS' ((mem_powersetCard.1 hS).1 (mem_insert_self m T))
      have hinj : Set.InjOn (insert m) (powersetCard k s' : Set (Finset α)) := by
        intro T1 h1 T2 h2 h
        have h1' : m ∉ T1 := fun h' => hmS' ((mem_powersetCard.1 (mem_coe.1 h1)).1 h')
        have h2' : m ∉ T2 := fun h' => hmS' ((mem_powersetCard.1 (mem_coe.1 h2)).1 h')
        calc T1 = (insert m T1).erase m := (erase_insert h1').symm
          _ = (insert m T2).erase m := by rw [h]
          _ = T2 := erase_insert h2'
      rw [powersetCard_succ_insert hmS', sum_union hdisj, sum_image hinj]
      have e1 : ∑ S ∈ powersetCard (k + 1) s', q ^ satakeInv (insert m s') S
          = q ^ (k + 1) * ∑ S ∈ powersetCard (k + 1) s', q ^ satakeInv s' S := by
        rw [mul_sum]
        apply sum_congr rfl
        intro S hS
        obtain ⟨hsub, hcard⟩ := mem_powersetCard.1 hS
        rw [satakeInv_insert_not_mem s' S m hm hsub, hcard, pow_add]
        ring
      have e2 : ∑ T ∈ powersetCard k s', q ^ satakeInv (insert m s') (insert m T)
          = ∑ T ∈ powersetCard k s', q ^ satakeInv s' T :=
        sum_congr rfl (fun T hT => by
          rw [satakeInv_insert_mem s' T m hm (mem_powersetCard.1 hT).1])
      rw [e1, e2]
      have hP : ∏ i ∈ range (k + 1), (q ^ (i + 1) - 1)
          = (∏ i ∈ range k, (q ^ (i + 1) - 1)) * (q ^ (k + 1) - 1) := prod_range_succ _ _
      have hR : ∏ i ∈ range (k + 1), (q ^ (s'.card + 1 - i) - 1)
          = (∏ i ∈ range k, (q ^ (s'.card - i) - 1)) * (q ^ (s'.card + 1) - 1) := by
        rw [prod_range_succ']
        simp only [Nat.add_sub_add_right, Nat.sub_zero]
      have hRk : ∏ i ∈ range (k + 1), (q ^ (s'.card - i) - 1)
          = (∏ i ∈ range k, (q ^ (s'.card - i) - 1)) * (q ^ (s'.card - k) - 1) :=
        prod_range_succ _ _
      have hsplit :
          (q ^ (k + 1) * ∑ S ∈ powersetCard (k + 1) s', q ^ satakeInv s' S
              + ∑ T ∈ powersetCard k s', q ^ satakeInv s' T) * ∏ i ∈ range (k + 1), (q ^ (i + 1) - 1)
            = q ^ (k + 1) * ((∑ S ∈ powersetCard (k + 1) s', q ^ satakeInv s' S)
                * ∏ i ∈ range (k + 1), (q ^ (i + 1) - 1))
              + ((∑ T ∈ powersetCard k s', q ^ satakeInv s' T) * ∏ i ∈ range k, (q ^ (i + 1) - 1))
                * (q ^ (k + 1) - 1) := by
        rw [hP]; ring
      rw [card_insert_of_notMem hmS', hR, hsplit, ih (k + 1), ih k, hRk]
      by_cases hk : k ≤ s'.card
      · have hpow : q ^ (k + 1) * q ^ (s'.card - k) = q ^ (s'.card + 1) := by
          rw [← pow_add]; congr 1; omega
        linear_combination (∏ i ∈ range k, (q ^ (s'.card - i) - 1)) * hpow
      · have hz : ∏ i ∈ range k, (q ^ (s'.card - i) - 1) = 0 :=
          prod_eq_zero (i := s'.card) (mem_range.2 (by omega)) (by simp)
        rw [hz]; ring

/- English proof (translation)
Establish `hmS : m ∉ S` using `fun h => lt_irrefl m (hm m h)`. Unfold `satakeInv`. Rewrite using `[sum_insert hmS]`. Establish `h1 : (s \ insert m S).filter (fun l => m < l) = s.filter (fun l => m < l)`. Use extensionality with `x`.

Simplify using `only [mem_filter, mem_sdiff, mem_insert]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨hx, -⟩, h⟩`. Conclude with `⟨hx, h⟩`. Introduce and unpack `⟨hx, h⟩`.

Use `⟨⟨hx, ?_⟩, h⟩` and prove the remaining obligations. Introduce and unpack `(rfl | hxS)`. Conclude with `lt_irrefl _ h`. Conclude with `lt_asymm h (hm x hxS)`. Establish `h2 : ∀ a ∈ S, ((s \ S).filter (fun l => a < l)).card = ((s \ insert m S).filter (fun l => a < l)).card + 1`.

Introduce `a ha`. Establish `e : (s \ S).filter (fun l => a < l) = insert m ((s \ insert m S).filter (fun l => a < l))`. Use extensionality with `x`. Distinguish the cases in `hx : x = m`. Simplify using `[hx, hms, hmS, hm a ha]`.

Simplify using `[hx]`. Rewrite using `[e, card_insert_of_notMem (by simp)]`. Rewrite using `[h1, sum_congr rfl h2, sum_add_distrib, sum_const, smul_eq_mul, mul_one]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem satakeInv_insert_max_add_card {α : Type} [LinearOrder α] (s S : Finset α) (m : α)
    (hm : ∀ x ∈ S, x < m) (hms : m ∈ s) :
    satakeInv s (insert m S) + S.card = satakeInv s S + (s.filter (fun l => m < l)).card := by
  have hmS : m ∉ S := fun h => lt_irrefl m (hm m h)
  unfold satakeInv
  rw [sum_insert hmS]
  have h1 : (s \ insert m S).filter (fun l => m < l) = s.filter (fun l => m < l) := by
    ext x
    simp only [mem_filter, mem_sdiff, mem_insert]
    constructor
    · rintro ⟨⟨hx, -⟩, h⟩
      exact ⟨hx, h⟩
    · rintro ⟨hx, h⟩
      refine ⟨⟨hx, ?_⟩, h⟩
      rintro (rfl | hxS)
      · exact lt_irrefl _ h
      · exact lt_asymm h (hm x hxS)
  have h2 : ∀ a ∈ S, ((s \ S).filter (fun l => a < l)).card
      = ((s \ insert m S).filter (fun l => a < l)).card + 1 := by
    intro a ha
    have e : (s \ S).filter (fun l => a < l)
        = insert m ((s \ insert m S).filter (fun l => a < l)) := by
      ext x
      by_cases hx : x = m
      · simp [hx, hms, hmS, hm a ha]
      · simp [hx]
    rw [e, card_insert_of_notMem (by simp)]
  rw [h1, sum_congr rfl h2, sum_add_distrib, sum_const, smul_eq_mul, mul_one]
  ring

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on_max`. Use `next => simp [satakeInv]`. Use `next m S' hm ih =>`. Establish `hmS' : m ∉ S'` using `fun h => lt_irrefl m (hm m h)`. Establish `L` using `satakeInv_insert_max_add_card (univ : Finset (Fin n)) S' m hm (mem_univ m)`.

Establish `hc : ((univ : Finset (Fin n)).filter (fun l => m < l)).card = n - 1 - (m : ℕ)`. Rewrite using `[Finset.filter_lt_eq_Ioi, Fin.card_Ioi]`. Rewrite `L` using `[hc]`. Establish `hlt : (m : ℕ) < n` using `m.isLt`. Establish `hsub : (((n - 1 - (m : ℕ) : ℕ)) : ℤ) = (n : ℤ) - 1 - (m : ℕ)` using `by omega`.

Establish `L'` using `congrArg (fun x : ℕ => (x : ℤ)) L`. Simplify using `only [Nat.cast_add] at L'`. Rewrite `L'` using `[hsub]`. Rewrite using `[sum_insert hmS', card_insert_of_notMem hmS']`. Use `push_cast`.

Take the linear combination `2 * L' + ih`.
-/
theorem satakeInv_two_mul {n : ℕ} (S : Finset (Fin n)) :
    2 * (satakeInv univ S : ℤ) =
      ∑ a ∈ S, ((n : ℤ) - 1 - 2 * (a : ℕ)) + (S.card : ℤ) * ((n : ℤ) - S.card) := by
  induction S using Finset.induction_on_max
  next => simp [satakeInv]
  next m S' hm ih =>
    have hmS' : m ∉ S' := fun h => lt_irrefl m (hm m h)
    have L := satakeInv_insert_max_add_card (univ : Finset (Fin n)) S' m hm (mem_univ m)
    have hc : ((univ : Finset (Fin n)).filter (fun l => m < l)).card = n - 1 - (m : ℕ) := by
      rw [Finset.filter_lt_eq_Ioi, Fin.card_Ioi]
    rw [hc] at L
    have hlt : (m : ℕ) < n := m.isLt
    have hsub : (((n - 1 - (m : ℕ) : ℕ)) : ℤ) = (n : ℤ) - 1 - (m : ℕ) := by omega
    have L' := congrArg (fun x : ℕ => (x : ℤ)) L
    simp only [Nat.cast_add] at L'
    rw [hsub] at L'
    rw [sum_insert hmS', card_insert_of_notMem hmS']
    push_cast
    linear_combination 2 * L' + ih

end Formalism.UG.P
