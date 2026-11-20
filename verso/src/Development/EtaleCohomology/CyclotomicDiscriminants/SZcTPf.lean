import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LemmaKOfSteps

noncomputable section

namespace LateralTheory.Q.SZcT

open UpperTheory.V.ZK

def wd {q : ℕ} (e : ℕ) (j : Fin (e + 1) → ZMod q) : Fin (2 * e + 1 + 1) → Cq q :=
  fun i => if (i : ℕ) % 2 = 0 then Multiplicative.ofAdd (j ⟨i / 2, by omega⟩) else Multiplicative.ofAdd 1

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem zc_eq (q : ℕ) [NeZero q] (e : ℕ) :
    zc q e = ∑ j : Fin (e + 1) → ZMod q, Finsupp.single (wd e j) 1 := rfl

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih fun a ha => h a (by omega), ← h n (by omega), pow_succ (-1 : A) (2 * n + 1)]`. Simplify using the standard rewrite rules.
-/
theorem alt_range {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] (T : ℕ → M) (n : ℕ)
    (h : ∀ a, a < n → T (2 * a) = T (2 * a + 1)) :
    ∑ p ∈ Finset.range (2 * n), ((-1 : A) ^ (p + 1)) • T p = 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      ih fun a ha => h a (by omega), ← h n (by omega), pow_succ (-1 : A) (2 * n + 1)]
    simp

/- English proof (translation)
Establish `key` using `alt_range (A := A) (fun p => if hp : p < 2 * e + 1 + 1 then S ⟨p, hp⟩ else 0) (e + 1) (by`. Introduce `a ha`. Rewrite using `[dif_pos (by omega), dif_pos (by omega)]`. Conclude with `h a ha)`. Rewrite `key` using `[show 2 * (e + 1) = 2 * e + 1 + 1 by ring, ← Fin.sum_univ_eq_sum_range (fun p => ((-1 : A) ^ (p + 1)) • (if hp : p < 2 * e + 1 + 1 then S ⟨p, hp⟩ else 0))]`.

Rewrite using `[← key]`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Rewrite using `[dif_pos p.2]`.
-/
theorem alt_fin {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] (e : ℕ) (S : Fin (2 * e + 1 + 1) → M)
    (h : ∀ (a : ℕ) (ha : a < e + 1), S ⟨2 * a, by omega⟩ = S ⟨2 * a + 1, by omega⟩) :
    ∑ p : Fin (2 * e + 1 + 1), ((-1 : A) ^ ((p : ℕ) + 1)) • S p = 0 := by
  have key := alt_range (A := A) (fun p => if hp : p < 2 * e + 1 + 1 then S ⟨p, hp⟩ else 0) (e + 1) (by
    intro a ha
    rw [dif_pos (by omega), dif_pos (by omega)]
    exact h a ha)
  rw [show 2 * (e + 1) = 2 * e + 1 + 1 by ring, ← Fin.sum_univ_eq_sum_range
    (fun p => ((-1 : A) ^ (p + 1)) • (if hp : p < 2 * e + 1 + 1 then S ⟨p, hp⟩ else 0))] at key
  rw [← key]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [dif_pos p.2]

/- English proof (translation)
Unfold `wd`. Rewrite using `[if_pos (by omega)]`. Use `congr 2`. Use `ext`. Use `show (i : ℕ) / 2 = k`.

Use linear arithmetic over natural numbers and integers.
-/
theorem wd_even {q : ℕ} (e : ℕ) (j : Fin (e + 1) → ZMod q) (i : Fin (2 * e + 1 + 1)) (k : Fin (e + 1))
    (h : (i : ℕ) = 2 * k) : wd e j i = Multiplicative.ofAdd (j k) := by
  unfold wd
  rw [if_pos (by omega)]
  congr 2
  ext
  show (i : ℕ) / 2 = k
  omega

/- English proof (translation)
Unfold `wd`. Rewrite using `[if_neg (by omega)]`.
-/
theorem wd_odd {q : ℕ} (e : ℕ) (j : Fin (e + 1) → ZMod q) (i : Fin (2 * e + 1 + 1))
    (h : (i : ℕ) % 2 = 1) : wd e j i = Multiplicative.ofAdd 1 := by
  unfold wd
  rw [if_neg (by omega)]

/- English proof (translation)
Break down `Nat.mod_two_eq_zero_or_one i with hi | hi` into its components or cases. Establish `hk : (i : ℕ) = 2 * ((⟨i / 2, by omega⟩ : Fin (e + 1)) : ℕ)` using `by show (i : ℕ) = 2 * (i / 2)`. Use linear arithmetic over natural numbers and integers. Rewrite using `[wd_even e j i _ hk, wd_even e j' i _ hk, h _ hk]`. Rewrite using `[wd_odd e j i hi, wd_odd e j' i hi]`.
-/
theorem wd_congr {q : ℕ} (e : ℕ) (j j' : Fin (e + 1) → ZMod q) (i : Fin (2 * e + 1 + 1))
    (h : ∀ k : Fin (e + 1), (i : ℕ) = 2 * k → j k = j' k) : wd e j i = wd e j' i := by
  rcases Nat.mod_two_eq_zero_or_one i with hi | hi
  · have hk : (i : ℕ) = 2 * ((⟨i / 2, by omega⟩ : Fin (e + 1)) : ℕ) := by
      show (i : ℕ) = 2 * (i / 2)
      omega
    rw [wd_even e j i _ hk, wd_even e j' i _ hk, h _ hk]
  · rw [wd_odd e j i hi, wd_odd e j' i hi]

/- English proof (translation)
Rewrite using `[← (Fin.consEquiv fun _ : Fin (e + 1) => ZMod q).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]`. Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations. Establish `h : ∀ x : ZMod q, (fun i : Fin (2 * e + 1) => wd e (Fin.consEquiv (fun _ => ZMod q) (x, j)) i.succ) = fun i : Fin (2 * e + 1) => wd e (Fin.consEquiv (fun _ => ZMod q) (0, j)) i.succ`. Introduce `x`. Use function extensionality and compare the values at `i`.

Use `wd_congr e _ _ _ fun k hk => ?_` and prove the remaining obligations. Proceed by induction on `k using Fin.cases with`. Consider the case `zero => simp at hk`. Consider the case `succ k => simp [Fin.consEquiv]`. Simplify using `only [h]`.

Rewrite using `[Finset.sum_const, Finset.card_univ, ZMod.card, Finsupp.smul_single]`. Simplify using the standard rewrite rules.
-/
theorem tail_sum (q : ℕ) [NeZero q] (e : ℕ) :
    (∑ j : Fin (e + 1) → ZMod q, Finsupp.single (fun i : Fin (2 * e + 1) => wd e j i.succ) 1 :
      Ch (ZMod q) (Cq q) (2 * e + 1)) = 0 := by
  rw [← (Fin.consEquiv fun _ : Fin (e + 1) => ZMod q).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_eq_zero fun j _ => ?_
  have h : ∀ x : ZMod q, (fun i : Fin (2 * e + 1) => wd e (Fin.consEquiv (fun _ => ZMod q) (x, j)) i.succ) =
      fun i : Fin (2 * e + 1) => wd e (Fin.consEquiv (fun _ => ZMod q) (0, j)) i.succ := by
    intro x
    funext i
    refine wd_congr e _ _ _ fun k hk => ?_
    induction k using Fin.cases with
    | zero => simp at hk
    | succ k => simp [Fin.consEquiv]
  simp only [h]
  rw [Finset.sum_const, Finset.card_univ, ZMod.card, Finsupp.smul_single]
  simp

def sh (q e a : ℕ) : Fin (e + 1) → ZMod q := fun k => if (k : ℕ) = a then 1 else if (k : ℕ) = a + 1 then -1 else 0

/- English proof (translation)
Use function extensionality and compare the values at `i`. Establish `hi` using `i.2`. Break down `lt_trichotomy (i : ℕ) (2 * a) with h | h | h` into its components or cases. Rewrite using `[Fin.contractNth_apply_of_lt _ _ _ _ h, Fin.contractNth_apply_of_lt _ _ _ _ (by show (i : ℕ) < 2 * a + 1; omega)]`. Use `wd_congr e _ _ _ fun k hk => ?_` and prove the remaining obligations.

Rewrite `hk` using `[Fin.val_castSucc]`. Rewrite using `[Pi.add_apply, sh, if_neg (by omega), if_neg (by omega), add_zero]`. Rewrite using `[Fin.contractNth_apply_of_eq _ _ _ _ h, Fin.contractNth_apply_of_lt _ _ _ _ (by show (i : ℕ) < 2 * a + 1; omega), wd_even e j i.castSucc ⟨a, ha⟩ h, wd_even e _ i.castSucc ⟨a, ha⟩ h, wd_odd e j i.succ (by rw [Fin.val_succ]; omega), Pi.add_apply, sh, if_pos rfl, ofAdd_add]`. Rewrite using `[Fin.contractNth_apply_of_gt _ _ _ _ h]`. Break down `(show (i : ℕ) = 2 * a + 1 ∨ 2 * a + 1 < i by omega) with h' | h'` into its components or cases.

Establish `hk : ((i.succ : Fin (2 * e + 1 + 1)) : ℕ) = 2 * ((⟨a + 1, by omega⟩ : Fin (e + 1)) : ℕ)`. Rewrite using `[Fin.val_succ]`. Use `show (i : ℕ) + 1 = 2 * (a + 1)`. Use linear arithmetic over natural numbers and integers. Rewrite using `[Fin.contractNth_apply_of_eq _ _ _ _ h', wd_even e j _ _ hk, wd_even e _ _ _ hk, wd_odd e _ i.castSucc (by rw [Fin.val_castSucc]; omega), Pi.add_apply, sh, if_neg (by simp), if_pos rfl, ← ofAdd_add]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Fin.contractNth_apply_of_gt _ _ _ _ h']`. Use `wd_congr e _ _ _ fun k hk => ?_` and prove the remaining obligations. Rewrite `hk` using `[Fin.val_succ]`.

Rewrite using `[Pi.add_apply, sh, if_neg (by omega), if_neg (by omega), add_zero]`.
-/
theorem contract_eq {q : ℕ} (e a : ℕ) (ha : a < e + 1) (j : Fin (e + 1) → ZMod q) :
    Fin.contractNth (⟨2 * a, by omega⟩ : Fin (2 * e + 1 + 1)) (· * ·) (wd e j) =
      Fin.contractNth (⟨2 * a + 1, by omega⟩ : Fin (2 * e + 1 + 1)) (· * ·) (wd e (j + sh q e a)) := by
  funext i
  have hi := i.2
  rcases lt_trichotomy (i : ℕ) (2 * a) with h | h | h
  · rw [Fin.contractNth_apply_of_lt _ _ _ _ h, Fin.contractNth_apply_of_lt _ _ _ _ (by show (i : ℕ) < 2 * a + 1; omega)]
    refine wd_congr e _ _ _ fun k hk => ?_
    rw [Fin.val_castSucc] at hk
    rw [Pi.add_apply, sh, if_neg (by omega), if_neg (by omega), add_zero]
  · rw [Fin.contractNth_apply_of_eq _ _ _ _ h, Fin.contractNth_apply_of_lt _ _ _ _ (by show (i : ℕ) < 2 * a + 1; omega),
      wd_even e j i.castSucc ⟨a, ha⟩ h, wd_even e _ i.castSucc ⟨a, ha⟩ h,
      wd_odd e j i.succ (by rw [Fin.val_succ]; omega), Pi.add_apply, sh, if_pos rfl, ofAdd_add]
  · rw [Fin.contractNth_apply_of_gt _ _ _ _ h]
    rcases (show (i : ℕ) = 2 * a + 1 ∨ 2 * a + 1 < i by omega) with h' | h'
    · have hk : ((i.succ : Fin (2 * e + 1 + 1)) : ℕ) = 2 * ((⟨a + 1, by omega⟩ : Fin (e + 1)) : ℕ) := by
        rw [Fin.val_succ]
        show (i : ℕ) + 1 = 2 * (a + 1)
        omega
      rw [Fin.contractNth_apply_of_eq _ _ _ _ h', wd_even e j _ _ hk, wd_even e _ _ _ hk,
        wd_odd e _ i.castSucc (by rw [Fin.val_castSucc]; omega), Pi.add_apply, sh, if_neg (by simp), if_pos rfl,
        ← ofAdd_add]
      congr 1
      ring
    · rw [Fin.contractNth_apply_of_gt _ _ _ _ h']
      refine wd_congr e _ _ _ fun k hk => ?_
      rw [Fin.val_succ] at hk
      rw [Pi.add_apply, sh, if_neg (by omega), if_neg (by omega), add_zero]

/- English proof (translation)
Introduce `q _ e`. Unfold `Cyc`. Rewrite using `[zc_eq, map_sum]`. Simplify using `only [bd, Finsupp.linearCombination_single, one_smul]`. Rewrite using `[Finset.sum_add_distrib, tail_sum, zero_add, Finset.sum_comm]`.

Simplify using `only [← Finset.smul_sum]`. Use `alt_fin (A := ZMod q) e (fun p => ∑ j : Fin (e + 1) → ZMod q, (Finsupp.single (Fin.contractNth p (· * ·) (wd e j)) 1 : Ch (ZMod q) (Cq q) (2 * e + 1))) fun a ha => ?_` and prove the remaining obligations. Use `Fintype.sum_equiv (Equiv.addRight (sh q e a)) _ _ fun j => ?_` and prove the remaining obligations. Rewrite using `[contract_eq e a ha j]`. Both sides reduce to the same expression.
-/
theorem SZc_of : SZc := by
  intro q _ e
  unfold Cyc
  rw [zc_eq, map_sum]
  simp only [bd, Finsupp.linearCombination_single, one_smul]
  rw [Finset.sum_add_distrib, tail_sum, zero_add, Finset.sum_comm]
  simp only [← Finset.smul_sum]
  refine alt_fin (A := ZMod q) e (fun p => ∑ j : Fin (e + 1) → ZMod q,
    (Finsupp.single (Fin.contractNth p (· * ·) (wd e j)) 1 : Ch (ZMod q) (Cq q) (2 * e + 1))) fun a ha => ?_
  refine Fintype.sum_equiv (Equiv.addRight (sh q e a)) _ _ fun j => ?_
  rw [contract_eq e a ha j]
  rfl

end LateralTheory.Q.SZcT

end
