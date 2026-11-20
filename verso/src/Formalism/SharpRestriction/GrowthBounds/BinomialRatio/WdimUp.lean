import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.CountUp

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G Function

def WdimUpAt : Prop :=
  ∀ (r : ℕ) [NeZero r] (lam : Fin r → ℤ), Antitone lam → wdim lam ≤ ∏ l, (sdXi r (lam l).natAbs : ℚ)

/- English proof (translation)
Establish `hfin : (support f).Finite`. Assume the negation of the conclusion as `hinf`. Rewrite `hs` using `[finsum_of_infinite_support hinf]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[← hs]`.

Conclude with `single_le_finsum a hfin hnn`.
-/
theorem le_finsum_of_nonneg {α : Type*} (f : α → ℚ) (c : ℚ) (hc : 0 < c) (hs : ∑ᶠ x, f x = c) (hnn : ∀ x, 0 ≤ f x) (a : α) :
    f a ≤ c := by
  have hfin : (support f).Finite := by
    by_contra hinf
    rw [finsum_of_infinite_support hinf] at hs
    linarith
  rw [← hs]
  exact single_le_finsum a hfin hnn

/- English proof (translation)
Establish `h1` using `hCD (N + 1) r LL`. Unfold `chainSum at h1`. Establish `hpos : (0 : ℚ) < ∏ i, (sdXi r (LL.deg i) : ℚ)` using `Finset.prod_pos fun i _ => by exact_mod_cast sdXi_pos _ _ (Nat.pos_of_ne_zero (NeZero.ne r))`. Use `(le_of_eq ?_).trans (le_finsum_of_nonneg _ _ hpos h1 ?_ ka)` and prove the remaining obligations. Rewrite using `[if_pos ⟨h, fun k => k.elim0⟩]`.

Introduce `x split_ifs with hx`. Conclude with `(wdim_pos (IsChain.anti_last hx.1)).le`. Conclude with `le_rfl`.
-/
theorem wu_single (hCD : ChainDimAt) {N r : ℕ} [NeZero r] (LL : ChainLetters (N + 1))
    (ka : Fin (N + 1 + 1) → Fin r → ℤ) (h : IsChain LL ka) :
    wdim (ka (Fin.last (N + 1))) ≤ ∏ i, (sdXi r (LL.deg i) : ℚ) := by
  have h1 := hCD (N + 1) r LL
  unfold chainSum at h1
  have hpos : (0 : ℚ) < ∏ i, (sdXi r (LL.deg i) : ℚ) :=
    Finset.prod_pos fun i _ => by exact_mod_cast sdXi_pos _ _ (Nat.pos_of_ne_zero (NeZero.ne r))
  refine (le_of_eq ?_).trans (le_finsum_of_nonneg _ _ hpos h1 ?_ ka)
  · rw [if_pos ⟨h, fun k => k.elim0⟩]
  · intro x
    split_ifs with hx
    · exact (wdim_pos (IsChain.anti_last hx.1)).le
    · exact le_rfl

def wuLam {r : ℕ} (lam : Fin r → ℤ) (y : ℕ) : ℤ := if h : y < r then lam ⟨y, h⟩ else 0

/- English proof (translation)
Unfold `wuLam`. Rewrite using `[dif_pos l.2]`.
-/
theorem wuLam_val {r : ℕ} (lam : Fin r → ℤ) (l : Fin r) : wuLam lam l.val = lam l := by
  unfold wuLam
  rw [dif_pos l.2]

def wuDeg {r : ℕ} (lam : Fin r → ℤ) (a : ℕ) : ℕ :=
  if a < r then (wuLam lam a).toNat else if a < 2 * r then (-(wuLam lam (2 * r - 1 - a))).toNat else 0

def wuLL {r : ℕ} (lam : Fin r → ℤ) : ChainLetters (2 * r + 1) where
  vec := fun a => decide (a.val < r ∨ a.val = 2 * r)
  deg := fun a => wuDeg lam a.val

def wuSt {r : ℕ} (lam : Fin r → ℤ) (n : ℕ) (l : Fin r) : ℤ :=
  if n ≤ r then (if l.val < n then max (lam l) 0 else 0)
  else (if 2 * r ≤ l.val + n then lam l else max (lam l) 0)

/- English proof (translation)
Rewrite using `[← Finset.sum_sub_distrib, Finset.sum_eq_single l0]`. Conclude with `h0`. Introduce `b _ hb`. Rewrite using `[h b hb, sub_self]`. Introduce `hn`.

Conclude with `absurd (Finset.mem_univ _) hn`.
-/
theorem wu_sum {r : ℕ} (f g : Fin r → ℤ) (l0 : Fin r) (c : ℤ) (h0 : f l0 - g l0 = c) (h : ∀ l, l ≠ l0 → f l = g l) :
    ∑ l, f l - ∑ l, g l = c := by
  rw [← Finset.sum_sub_distrib, Finset.sum_eq_single l0]
  · exact h0
  · intro b _ hb
    rw [h b hb, sub_self]
  · intro hn
    exact absurd (Finset.mem_univ _) hn

/- English proof (translation)
Establish `hadj : ∀ i j : Fin r, i.val + 1 = j.val → lam j ≤ lam i` using `fun i j hij => hlam (Fin.le_def.mpr (by omega))`. Break down `lt_or_ge a r with h1 | h1` into its components or cases. Rewrite using `[if_pos (by rw [decide_eq_true_eq]; omega)]`. Use `⟨fun l => ?_, fun i j hij => ?_, ?_⟩` and prove the remaining obligations. Unfold `wuSt`.

Use `l.2` as an intermediate fact. Apply the tactic sequence `split_ifs <;> omega`. Unfold `wuSt`. Use `hadj i j hij` as an intermediate fact. Use `i.2` as an intermediate fact.

Use `j.2` as an intermediate fact. Apply the tactic sequence `split_ifs <;> omega`. Establish `e : wuDeg lam a = (lam ⟨a, h1⟩).toNat`. Unfold `wuDeg wuLam`. Rewrite using `[if_pos h1, dif_pos h1]`.

Rewrite using `[e]`. Apply `wu_sum _ _ ⟨a, h1⟩` to reduce the goal to its premises. Apply the tactic sequence `unfold wuSt dsimp only split_ifs <;> omega`. Introduce `l hl`. Establish `hl' : l.val ≠ a` using `fun h => hl (Fin.ext h)`.

Unfold `wuSt`. Apply the tactic sequence `split_ifs <;> omega`. Break down `lt_or_ge a (2 * r) with h2 | h2` into its components or cases. Rewrite using `[if_neg (by rw [decide_eq_true_eq]; omega)]`. Establish `h3 : 2 * r - 1 - a < r` using `by omega`.

Use `⟨fun l => ?_, fun i j hij => ?_, ?_⟩` and prove the remaining obligations. Unfold `wuSt`. Use `l.2` as an intermediate fact. Apply the tactic sequence `split_ifs <;> omega`. Unfold `wuSt`.

Use `hadj i j hij` as an intermediate fact. Use `i.2` as an intermediate fact. Use `j.2` as an intermediate fact. Apply the tactic sequence `split_ifs <;> omega`. Establish `e : wuDeg lam a = (-(lam ⟨2 * r - 1 - a, h3⟩)).toNat`.

Unfold `wuDeg wuLam`. Rewrite using `[if_neg (by omega), if_pos h2, dif_pos h3]`. Rewrite using `[e]`. Apply `wu_sum _ _ ⟨2 * r - 1 - a, h3⟩` to reduce the goal to its premises. Apply the tactic sequence `unfold wuSt dsimp only split_ifs <;> omega`.

Introduce `l hl`. Establish `hl' : l.val ≠ 2 * r - 1 - a` using `fun h => hl (Fin.ext h)`. Use `l.2` as an intermediate fact. Unfold `wuSt`. Apply the tactic sequence `split_ifs <;> omega`.

Establish `h4 : a = 2 * r` using `by omega`. Rewrite using `[if_pos (by rw [decide_eq_true_eq]; omega)]`. Establish `e : wuDeg lam a = 0`. Unfold `wuDeg`. Rewrite using `[if_neg (by omega), if_neg (by omega)]`.

Rewrite using `[e]`. Use `⟨fun l => ?_, fun i j hij => ?_, ?_⟩` and prove the remaining obligations. Unfold `wuSt`. Use `l.2` as an intermediate fact. Apply the tactic sequence `split_ifs <;> omega`.

Unfold `wuSt`. Use `hadj i j hij` as an intermediate fact. Use `i.2` as an intermediate fact. Use `j.2` as an intermediate fact. Apply the tactic sequence `split_ifs <;> omega`.

Establish `: wuSt lam (a + 1) = wuSt lam a`. Use function extensionality and compare the values at `l`. Use `l.2` as an intermediate fact. Unfold `wuSt`. Apply the tactic sequence `split_ifs <;> omega`.

Rewrite using `[this]`. Simplify using the standard rewrite rules.
-/
theorem wu_step {r : ℕ} (lam : Fin r → ℤ) (hlam : Antitone lam) (a : ℕ) (ha : a < 2 * r + 1) :
    if decide (a < r ∨ a = 2 * r) = true then Strip (wuSt lam (a + 1)) (wuSt lam a) (wuDeg lam a)
      else Strip (wuSt lam a) (wuSt lam (a + 1)) (wuDeg lam a) := by
  have hadj : ∀ i j : Fin r, i.val + 1 = j.val → lam j ≤ lam i := fun i j hij =>
    hlam (Fin.le_def.mpr (by omega))
  rcases lt_or_ge a r with h1 | h1
  · rw [if_pos (by rw [decide_eq_true_eq]; omega)]
    refine ⟨fun l => ?_, fun i j hij => ?_, ?_⟩
    · unfold wuSt
      have := l.2
      split_ifs <;> omega
    · unfold wuSt
      have := hadj i j hij
      have := i.2
      have := j.2
      split_ifs <;> omega
    · have e : wuDeg lam a = (lam ⟨a, h1⟩).toNat := by
        unfold wuDeg wuLam
        rw [if_pos h1, dif_pos h1]
      rw [e]
      apply wu_sum _ _ ⟨a, h1⟩
      · unfold wuSt
        dsimp only
        split_ifs <;> omega
      · intro l hl
        have hl' : l.val ≠ a := fun h => hl (Fin.ext h)
        unfold wuSt
        split_ifs <;> omega
  · rcases lt_or_ge a (2 * r) with h2 | h2
    · rw [if_neg (by rw [decide_eq_true_eq]; omega)]
      have h3 : 2 * r - 1 - a < r := by omega
      refine ⟨fun l => ?_, fun i j hij => ?_, ?_⟩
      · unfold wuSt
        have := l.2
        split_ifs <;> omega
      · unfold wuSt
        have := hadj i j hij
        have := i.2
        have := j.2
        split_ifs <;> omega
      · have e : wuDeg lam a = (-(lam ⟨2 * r - 1 - a, h3⟩)).toNat := by
          unfold wuDeg wuLam
          rw [if_neg (by omega), if_pos h2, dif_pos h3]
        rw [e]
        apply wu_sum _ _ ⟨2 * r - 1 - a, h3⟩
        · unfold wuSt
          dsimp only
          split_ifs <;> omega
        · intro l hl
          have hl' : l.val ≠ 2 * r - 1 - a := fun h => hl (Fin.ext h)
          have := l.2
          unfold wuSt
          split_ifs <;> omega
    · have h4 : a = 2 * r := by omega
      rw [if_pos (by rw [decide_eq_true_eq]; omega)]
      have e : wuDeg lam a = 0 := by
        unfold wuDeg
        rw [if_neg (by omega), if_neg (by omega)]
      rw [e]
      refine ⟨fun l => ?_, fun i j hij => ?_, ?_⟩
      · unfold wuSt
        have := l.2
        split_ifs <;> omega
      · unfold wuSt
        have := hadj i j hij
        have := i.2
        have := j.2
        split_ifs <;> omega
      · have : wuSt lam (a + 1) = wuSt lam a := by
          funext l
          have := l.2
          unfold wuSt
          split_ifs <;> omega
        rw [this]
        simp

/- English proof (translation)
Use `⟨?_, fun i => ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `l show wuSt lam 0 l = 0`. Unfold `wuSt`. Simplify using the standard rewrite rules. Conclude with `wu_step lam hlam i.val i.2`.
-/
theorem wu_chain {r : ℕ} (lam : Fin r → ℤ) (hlam : Antitone lam) :
    IsChain (wuLL lam) (fun n : Fin (2 * r + 1 + 1) => wuSt lam n.val) := by
  refine ⟨?_, fun i => ?_⟩
  · funext l
    show wuSt lam 0 l = 0
    unfold wuSt
    simp
  · exact wu_step lam hlam i.val i.2

/- English proof (translation)
Unfold `sdXi`. Simplify using the standard rewrite rules.
-/
theorem sdXi_zero (r : ℕ) : sdXi r 0 = 1 := by
  unfold sdXi
  simp

/- English proof (translation)
Use `show ∏ i : Fin (2 * r + 1), (sdXi r (wuDeg lam i.val) : ℚ) = _`. Rewrite using `[Fin.prod_univ_eq_prod_range (fun a => (sdXi r (wuDeg lam a) : ℚ)) (2 * r + 1), Finset.prod_range_succ, two_mul, Finset.prod_range_add]`. Establish `e1 : ∀ x ∈ Finset.range r, (sdXi r (wuDeg lam x) : ℚ) = (sdXi r (wuLam lam x).toNat : ℚ)` using `fun x hx => by`. Use `Finset.mem_range.mp hx` as an intermediate fact. Unfold `wuDeg`.

Rewrite using `[if_pos this]`. Establish `e2 : ∀ x ∈ Finset.range r, (sdXi r (wuDeg lam (r + x)) : ℚ) = (fun y => (sdXi r (-(wuLam lam y)).toNat : ℚ)) (r - 1 - x)` using `fun x hx => by`. Use `Finset.mem_range.mp hx` as an intermediate fact. Unfold `wuDeg`. Rewrite using `[if_neg (by omega), if_pos (by omega)]`.

Establish `e : 2 * r - 1 - (r + x) = r - 1 - x` using `by omega`. Rewrite using `[e]`. Establish `e3 : wuDeg lam (r + r) = 0`. Unfold `wuDeg`. Rewrite using `[if_neg (by omega), if_neg (by omega)]`.

Rewrite using `[Finset.prod_congr rfl e1, Finset.prod_congr rfl e2, Finset.prod_range_reflect (fun y => (sdXi r (-(wuLam lam y)).toNat : ℚ)) r, e3, sdXi_zero, Nat.cast_one, mul_one, ← Finset.prod_mul_distrib, ← Fin.prod_univ_eq_prod_range (fun x => (sdXi r (wuLam lam x).toNat : ℚ) * (sdXi r (-( …`. Use `Finset.prod_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[wuLam_val]`. Break down `le_total 0 (lam l) with h | h` into its components or cases. Establish `a1 : (-(lam l)).toNat = 0` using `by omega`.

Establish `a2 : (lam l).toNat = (lam l).natAbs` using `by omega`. Rewrite using `[a1, a2, sdXi_zero, Nat.cast_one, mul_one]`. Establish `a1 : (lam l).toNat = 0` using `by omega`. Establish `a2 : (-(lam l)).toNat = (lam l).natAbs` using `by omega`. Rewrite using `[a1, a2, sdXi_zero, Nat.cast_one, one_mul]`.
-/
theorem wu_prod {r : ℕ} (lam : Fin r → ℤ) :
    ∏ i, (sdXi r ((wuLL lam).deg i) : ℚ) = ∏ l, (sdXi r (lam l).natAbs : ℚ) := by
  show ∏ i : Fin (2 * r + 1), (sdXi r (wuDeg lam i.val) : ℚ) = _
  rw [Fin.prod_univ_eq_prod_range (fun a => (sdXi r (wuDeg lam a) : ℚ)) (2 * r + 1), Finset.prod_range_succ, two_mul,
    Finset.prod_range_add]
  have e1 : ∀ x ∈ Finset.range r, (sdXi r (wuDeg lam x) : ℚ) = (sdXi r (wuLam lam x).toNat : ℚ) := fun x hx => by
    have := Finset.mem_range.mp hx
    unfold wuDeg
    rw [if_pos this]
  have e2 : ∀ x ∈ Finset.range r, (sdXi r (wuDeg lam (r + x)) : ℚ) =
      (fun y => (sdXi r (-(wuLam lam y)).toNat : ℚ)) (r - 1 - x) := fun x hx => by
    have := Finset.mem_range.mp hx
    unfold wuDeg
    rw [if_neg (by omega), if_pos (by omega)]
    have e : 2 * r - 1 - (r + x) = r - 1 - x := by omega
    rw [e]
  have e3 : wuDeg lam (r + r) = 0 := by
    unfold wuDeg
    rw [if_neg (by omega), if_neg (by omega)]
  rw [Finset.prod_congr rfl e1, Finset.prod_congr rfl e2,
    Finset.prod_range_reflect (fun y => (sdXi r (-(wuLam lam y)).toNat : ℚ)) r, e3, sdXi_zero, Nat.cast_one, mul_one,
    ← Finset.prod_mul_distrib, ← Fin.prod_univ_eq_prod_range
      (fun x => (sdXi r (wuLam lam x).toNat : ℚ) * (sdXi r (-(wuLam lam x)).toNat : ℚ)) r]
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [wuLam_val]
  rcases le_total 0 (lam l) with h | h
  · have a1 : (-(lam l)).toNat = 0 := by omega
    have a2 : (lam l).toNat = (lam l).natAbs := by omega
    rw [a1, a2, sdXi_zero, Nat.cast_one, mul_one]
  · have a1 : (lam l).toNat = 0 := by omega
    have a2 : (-(lam l)).toNat = (lam l).natAbs := by omega
    rw [a1, a2, sdXi_zero, Nat.cast_one, one_mul]

/- English proof (translation)
Introduce `r _ lam hlam`. Establish `h` using `wu_single hCD (wuLL lam) _ (wu_chain lam hlam)`. Rewrite `h` using `[wu_prod]`. Establish `e : wuSt lam (Fin.last (2 * r + 1)).val = lam`. Use function extensionality and compare the values at `l`.

Use `l.2` as an intermediate fact. Use `show wuSt lam (2 * r + 1) l = lam l`. Unfold `wuSt`. Rewrite using `[if_neg (by omega), if_pos (by omega)]`. Rewrite `h` using `[e]`. Then use the resulting hypothesis.
-/
theorem wdimUp_of (hCD : ChainDimAt) : WdimUpAt := by
  intro r _ lam hlam
  have h := wu_single hCD (wuLL lam) _ (wu_chain lam hlam)
  rw [wu_prod] at h
  have e : wuSt lam (Fin.last (2 * r + 1)).val = lam := by
    funext l
    have := l.2
    show wuSt lam (2 * r + 1) l = lam l
    unfold wuSt
    rw [if_neg (by omega), if_pos (by omega)]
  rwa [e] at h

end Formalism.MainNotions.ColumnSystems.Pf
