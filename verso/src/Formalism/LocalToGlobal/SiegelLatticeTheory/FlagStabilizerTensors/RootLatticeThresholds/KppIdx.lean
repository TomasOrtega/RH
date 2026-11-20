import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsKpp

noncomputable section

open Matrix Finset

namespace Formalism.L2.SG.Pf.KppIdx

open Formalism.MainNotions.ArithmeticCylinders Formalism.L2.SG.Pf.AllRowsKpp

variable {s kk r : ℕ}

def xI (hr : r = kk + 2 * s + 1) (a : Fin s) : Fin r := ⟨a.1, by omega⟩
def wI (hr : r = kk + 2 * s + 1) (i : Fin kk) : Fin r := ⟨s + i.1, by omega⟩
def zI (hr : r = kk + 2 * s + 1) : Fin r := ⟨s + kk, by omega⟩
def yI (hr : r = kk + 2 * s + 1) (a : Fin s) : Fin r := ⟨s + kk + 1 + a.1, by omega⟩

/- English proof (translation)
Break down `lt_or_ge j.1 s with h | h` into its components or cases. Conclude with `Or.inl ⟨⟨j.1, h⟩, Fin.ext rfl⟩`. Break down `lt_or_ge j.1 (s + kk) with h' | h'` into its components or cases. Conclude with `Or.inr (Or.inl ⟨⟨j.1 - s, by omega⟩, Fin.ext (by show j.1 = s + (j.1 - s); omega)⟩)`. Break down `eq_or_lt_of_le h' with h'' | h''` into its components or cases.

Conclude with `Or.inr (Or.inr (Or.inl (Fin.ext (by show j.1 = s + kk; omega))))`. Conclude with `Or.inr (Or.inr (Or.inr ⟨⟨j.1 - (s + kk + 1), by omega⟩, Fin.ext (by show j.1 = s + kk + 1 + (j.1 - (s + kk + 1)); omega)⟩))`.
-/
theorem kind_cases (hr : r = kk + 2 * s + 1) (j : Fin r) :
    (∃ a, j = xI hr a) ∨ (∃ i, j = wI hr i) ∨ j = zI hr ∨ ∃ a, j = yI hr a := by
  rcases lt_or_ge j.1 s with h | h
  · exact Or.inl ⟨⟨j.1, h⟩, Fin.ext rfl⟩
  rcases lt_or_ge j.1 (s + kk) with h' | h'
  · exact Or.inr (Or.inl ⟨⟨j.1 - s, by omega⟩, Fin.ext (by show j.1 = s + (j.1 - s); omega)⟩)
  rcases eq_or_lt_of_le h' with h'' | h''
  · exact Or.inr (Or.inr (Or.inl (Fin.ext (by show j.1 = s + kk; omega))))
  · exact Or.inr (Or.inr (Or.inr ⟨⟨j.1 - (s + kk + 1), by omega⟩,
      Fin.ext (by show j.1 = s + kk + 1 + (j.1 - (s + kk + 1)); omega)⟩))

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem xI_val (hr : r = kk + 2 * s + 1) (a : Fin s) : (xI hr a).1 = a.1 := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem wI_val (hr : r = kk + 2 * s + 1) (i : Fin kk) : (wI hr i).1 = s + i.1 := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem zI_val (hr : r = kk + 2 * s + 1) : (zI hr).1 = s + kk := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem yI_val (hr : r = kk + 2 * s + 1) (a : Fin s) : (yI hr a).1 = s + kk + 1 + a.1 := rfl

variable {g : ℕ}

/- English proof (translation)
Use `⟨fun a b => ⟨hlow a b, fun h => h ▸ hdiag a⟩, fun a ha1 ha2 => ?_⟩` and prove the remaining obligations. Unfold `entN`. Rewrite using `[dif_pos ⟨by omega, by omega⟩]`. Use `hwz ⟨a - s, by omega⟩` as an intermediate fact. Apply the tactic sequence `convert this using 2 <;> ext <;> simp <;> omega`.
-/
theorem jPred_of (hr : r = kk + 2 * s + 1) {N : Matrix (Fin r) (Fin r) (ZMod g)}
    (hlow : ∀ a b : Fin r, b < a → N a b = 0) (hdiag : ∀ a, N a a = 1) (hwz : ∀ i, N (wI hr i) (zI hr) = 0) :
    JPred kk s N := by
  refine ⟨fun a b => ⟨hlow a b, fun h => h ▸ hdiag a⟩, fun a ha1 ha2 => ?_⟩
  unfold entN
  rw [dif_pos ⟨by omega, by omega⟩]
  have := hwz ⟨a - s, by omega⟩
  convert this using 2 <;> ext <;> simp <;> omega

/- English proof (translation)
The claim follows from `(hJ.1 a b).1 h`.
-/
theorem low_of {N : Matrix (Fin r) (Fin r) (ZMod g)} (hJ : JPred kk s N) (a b : Fin r) (h : b < a) : N a b = 0 :=
  (hJ.1 a b).1 h

/- English proof (translation)
The claim follows from `(hJ.1 a a).2 rfl`.
-/
theorem diag_of {N : Matrix (Fin r) (Fin r) (ZMod g)} (hJ : JPred kk s N) (a : Fin r) : N a a = 1 :=
  (hJ.1 a a).2 rfl

/- English proof (translation)
Establish `e` using `congrFun (congrFun h1 ⟨i, by omega⟩) ⟨i + 1, hi⟩`. Rewrite `e` using `[Matrix.mul_apply, Matrix.one_apply_ne (by intro h; have := congrArg Fin.val h; simp at this)]`. Establish `hne : (⟨i, by omega⟩ : Fin r) ≠ ⟨i + 1, hi⟩` using `by intro h; have := congrArg Fin.val h; simp at this`. Rewrite `e` using `[Finset.sum_eq_add (⟨i, by omega⟩ : Fin r) ⟨i + 1, hi⟩ hne (fun c _ hc => ?_) (by simp) (by simp)]`. Rewrite `e` using `[diag_of hJ, diag_of hJ', one_mul, mul_one]`.

Unfold `entN`. Rewrite using `[dif_pos ⟨by omega, hi⟩, dif_pos ⟨by omega, hi⟩]`. Take the linear combination `e`. Break down `lt_or_gt_of_ne (show c.1 ≠ i from fun h => hc.1 (Fin.ext h)) with h | h` into its components or cases. Rewrite using `[low_of hJ _ _ (show c < ⟨i, by omega⟩ from h), zero_mul]`.

Establish `: i + 1 < c.1`. Break down `lt_or_gt_of_ne (show c.1 ≠ i + 1 from fun h => hc.2 (Fin.ext h)) with h' | h'` into its components or cases. Use linear arithmetic over natural numbers and integers. Conclude with `h'`. Rewrite using `[low_of hJ' _ _ (show (⟨i + 1, hi⟩ : Fin r) < c from this), mul_zero]`.
-/
theorem inv_super {N N' : Matrix (Fin r) (Fin r) (ZMod g)} (hJ : JPred kk s N) (hJ' : JPred kk s N')
    (h1 : N * N' = 1) (i : ℕ) (hi : i + 1 < r) : entN N' i (i + 1) = -entN N i (i + 1) := by
  have e := congrFun (congrFun h1 ⟨i, by omega⟩) ⟨i + 1, hi⟩
  rw [Matrix.mul_apply, Matrix.one_apply_ne (by intro h; have := congrArg Fin.val h; simp at this)] at e
  have hne : (⟨i, by omega⟩ : Fin r) ≠ ⟨i + 1, hi⟩ := by intro h; have := congrArg Fin.val h; simp at this
  rw [Finset.sum_eq_add (⟨i, by omega⟩ : Fin r) ⟨i + 1, hi⟩ hne (fun c _ hc => ?_) (by simp) (by simp)] at e
  · rw [diag_of hJ, diag_of hJ', one_mul, mul_one] at e
    unfold entN
    rw [dif_pos ⟨by omega, hi⟩, dif_pos ⟨by omega, hi⟩]
    linear_combination e
  · rcases lt_or_gt_of_ne (show c.1 ≠ i from fun h => hc.1 (Fin.ext h)) with h | h
    · rw [low_of hJ _ _ (show c < ⟨i, by omega⟩ from h), zero_mul]
    · have : i + 1 < c.1 := by
        rcases lt_or_gt_of_ne (show c.1 ≠ i + 1 from fun h => hc.2 (Fin.ext h)) with h' | h'
        · omega
        · exact h'
      rw [low_of hJ' _ _ (show (⟨i + 1, hi⟩ : Fin r) < c from this), mul_zero]

def dN (s kk : ℕ) (ob : Bool) (j : ℕ) : ZMod g :=
  if s + kk + 1 ≤ j then (-1) ^ (j - (s + kk + 1))
  else if ob = false ∧ s ≤ j ∧ j < s + kk then (-1) ^ (j - s) else 1

/- English proof (translation)
Unfold `dN`. Apply the tactic sequence `split_ifs <;> simp [← pow_add, ← two_mul, pow_mul]`.
-/
theorem dN_sq (ob : Bool) (j : ℕ) : dN (g := g) s kk ob j * dN s kk ob j = 1 := by
  unfold dN
  split_ifs <;> simp [← pow_add, ← two_mul, pow_mul]

/- English proof (translation)
Unfold `dN; rw [if_neg (by omega), if_neg (fun h' => absurd h'.2.1 (by omega))]`.
-/
theorem index_diag_isotropic (ob : Bool) {j : ℕ} (h : j < s) : dN (g := g) s kk ob j = 1 := by
  unfold dN; rw [if_neg (by omega), if_neg (fun h' => absurd h'.2.1 (by omega))]

/- English proof (translation)
Unfold `dN; rw [if_neg (by omega), if_neg (fun h' => absurd h'.1 (by simp))]`.
-/
theorem dN_wt {j : ℕ} (h1 : s ≤ j) (h2 : j < s + kk) : dN (g := g) s kk true j = 1 := by
  unfold dN; rw [if_neg (by omega), if_neg (fun h' => absurd h'.1 (by simp))]

/- English proof (translation)
Unfold `dN; rw [if_neg (by omega), if_pos ⟨rfl, h1, h2⟩]`.
-/
theorem dN_wf {j : ℕ} (h1 : s ≤ j) (h2 : j < s + kk) : dN (g := g) s kk false j = (-1) ^ (j - s) := by
  unfold dN; rw [if_neg (by omega), if_pos ⟨rfl, h1, h2⟩]

/- English proof (translation)
Unfold `dN; rw [if_neg (by omega), if_neg (fun h' => absurd h'.2.2 (by omega))]`.
-/
theorem dN_add_eq_one (ob : Bool) : dN (g := g) s kk ob (s + kk) = 1 := by
  unfold dN; rw [if_neg (by omega), if_neg (fun h' => absurd h'.2.2 (by omega))]

/- English proof (translation)
Unfold `dN`. Rewrite using `[if_pos h]`.
-/
theorem dN_y (ob : Bool) {j : ℕ} (h : s + kk + 1 ≤ j) : dN (g := g) s kk ob j = (-1) ^ (j - (s + kk + 1)) := by
  unfold dN; rw [if_pos h]

/- English proof (translation)
Rewrite using `[← pow_add, ← two_mul, pow_mul]`. Simplify using the standard rewrite rules.
-/
theorem neg_one_sq (i : ℕ) : ((-1 : ZMod g) ^ i) * (-1) ^ i = 1 := by
  rw [← pow_add, ← two_mul, pow_mul]; simp

def dM (s kk : ℕ) (ob : Bool) : Matrix (Fin r) (Fin r) (ZMod g) := Matrix.diagonal fun j => dN s kk ob j.1

/- English proof (translation)
Rewrite using `[dM, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `j`. Conclude with `dN_sq ob j.1`.
-/
theorem dM_sq (ob : Bool) : dM (r := r) (g := g) s kk ob * dM s kk ob = 1 := by
  rw [dM, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext j
  exact dN_sq ob j.1

/- English proof (translation)
Unfold `entN`. Use `split_ifs with h`. Simplify using `[dM, Matrix.diagonal_mul, Matrix.mul_diagonal]`. Simplify using the standard rewrite rules.
-/
theorem entN_conj (ob : Bool) (N : Matrix (Fin r) (Fin r) (ZMod g)) (a b : ℕ) :
    entN (dM s kk ob * N * dM s kk ob) a b = dN s kk ob a * entN N a b * dN s kk ob b := by
  unfold entN
  split_ifs with h
  · simp [dM, Matrix.diagonal_mul, Matrix.mul_diagonal]
  · simp

/- English proof (translation)
Use `jPred_of hr (fun a b h => ?_) (fun a => ?_) (fun i => ?_)` and prove the remaining obligations. Simplify using `only [dM, Matrix.diagonal_mul, Matrix.mul_diagonal]`. Rewrite using `[low_of hJ a b h]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [dM, Matrix.diagonal_mul, Matrix.mul_diagonal]`.

Rewrite using `[diag_of hJ a, mul_one]`. Conclude with `dN_sq ob a.1`. Use `(hJ.2 (s + i.1) (by omega) (by omega))` as an intermediate fact. Unfold `entN at this`. Rewrite `this` using `[dif_pos ⟨by omega, by omega⟩]`.

Simplify using `only [dM, Matrix.diagonal_mul, Matrix.mul_diagonal]`. Establish `e : N (wI hr i) (zI hr) = 0` using `this`. Rewrite using `[e]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem jPred_conj (hr : r = kk + 2 * s + 1) (ob : Bool) {N : Matrix (Fin r) (Fin r) (ZMod g)}
    (hJ : JPred kk s N) : JPred kk s (dM s kk ob * N * dM s kk ob) := by
  refine jPred_of hr (fun a b h => ?_) (fun a => ?_) (fun i => ?_)
  · simp only [dM, Matrix.diagonal_mul, Matrix.mul_diagonal]
    rw [low_of hJ a b h]; ring
  · simp only [dM, Matrix.diagonal_mul, Matrix.mul_diagonal]
    rw [diag_of hJ a, mul_one]
    exact dN_sq ob a.1
  · have := (hJ.2 (s + i.1) (by omega) (by omega))
    unfold entN at this
    rw [dif_pos ⟨by omega, by omega⟩] at this
    simp only [dM, Matrix.diagonal_mul, Matrix.mul_diagonal]
    have e : N (wI hr i) (zI hr) = 0 := this
    rw [e]; ring

/- English proof (translation)
Consider the cases of `n with`. Consider the case `zero => simp`. Consider the case `succ t`. Rewrite using `[Finset.sum_range_succ, if_neg (by omega), add_zero, Nat.add_sub_cancel]`. Conclude with `Finset.sum_congr rfl fun a ha => by rw [Finset.mem_range] at ha; rw [if_pos (by omega)]`.
-/
theorem sum_range_pred (f : ℕ → ZMod g) (n : ℕ) :
    ∑ a ∈ range n, (if a + 1 < n then f a else 0) = ∑ a ∈ range (n - 1), f a := by
  cases n with
  | zero => simp
  | succ t =>
    rw [Finset.sum_range_succ, if_neg (by omega), add_zero, Nat.add_sub_cancel]
    exact Finset.sum_congr rfl fun a ha => by rw [Finset.mem_range] at ha; rw [if_pos (by omega)]

/- English proof (translation)
Consider the cases of `n with`. Consider the case `zero => simp`. Consider the case `succ t`. Rewrite using `[Finset.sum_range_succ, if_neg (by omega), if_pos (by omega)]`. Rewrite using `[Finset.sum_eq_zero fun a ha => by rw [Finset.mem_range] at ha; rw [if_pos (by omega)], zero_add]`.
-/
theorem sum_range_last (c : ZMod g) (n : ℕ) :
    ∑ a ∈ range n, (if a + 1 < n then 0 else c) = if 1 ≤ n then c else 0 := by
  cases n with
  | zero => simp
  | succ t =>
    rw [Finset.sum_range_succ, if_neg (by omega), if_pos (by omega)]
    rw [Finset.sum_eq_zero fun a ha => by rw [Finset.mem_range] at ha; rw [if_pos (by omega)], zero_add]

/- English proof (translation)
Establish `split1 : ∀ a ∈ range s, (if a + 1 < s then entN N a (a + 1) + entN N' (s + kk + 1 + (s - 2 - a)) (s + kk + 1 + (s - 1 - a)) else entN N a (s + kk) - entN N' (s + kk) (s + kk + 1)) = (if a + 1 < s then entN N a (a + 1) else 0) + (if a + 1 < s then entN N' (s + kk + 1 + (s - 2 - a) …`. Introduce `a ha`. Rewrite `ha` using `[Finset.mem_range]`. Use `split_ifs with h`. Expand and normalize the polynomial expressions, which then agree.

Establish `: a = s - 1` using `by omega`. Substitute `this` using the available equality. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Finset.sum_congr rfl split1, Finset.sum_add_distrib, Finset.sum_add_distrib, sum_range_pred, sum_range_pred, sum_range_last, sum_range_pred (fun i => if ob then entN N (s + i) (s + i + 1) else entN N' (s + (kk - 2 - i)) (s + (kk - 1 - i))) kk]`. Establish `ry : ∑ a ∈ range (s - 1), entN N' (s + kk + 1 + (s - 2 - a)) (s + kk + 1 + (s - 1 - a)) = -∑ i ∈ range (s - 1), entN N (s + kk + 1 + i) (s + kk + 2 + i)`.

Rewrite using `[← Finset.sum_range_reflect, ← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun a ha => ?_` and prove the remaining obligations. Rewrite `ha` using `[Finset.mem_range]`. Establish `e1 : s + kk + 1 + (s - 2 - (s - 1 - 1 - a)) = s + kk + 1 + a` using `by omega`. Establish `e2 : s + kk + 1 + (s - 1 - (s - 1 - 1 - a)) = s + kk + 1 + a + 1` using `by omega`.

Rewrite using `[e1, e2, hinv _ (by omega), show s + kk + 1 + a + 1 = s + kk + 2 + a by omega]`. Establish `rw' : ∑ i ∈ range (kk - 1), (if ob then entN N (s + i) (s + i + 1) else entN N' (s + (kk - 2 - i)) (s + (kk - 1 - i))) = (if ob then 1 else -1) * ∑ a ∈ range (kk - 1), entN N (s + a) (s + a + 1)`. Consider the cases of `ob`. Simplify using `only [Bool.false_eq_true, if_false, neg_one_mul]`. Rewrite using `[← Finset.sum_range_reflect, ← Finset.sum_neg_distrib]`.

Use `Finset.sum_congr rfl fun a ha => ?_` and prove the remaining obligations. Rewrite `ha` using `[Finset.mem_range]`. Establish `e1 : s + (kk - 2 - (kk - 1 - 1 - a)) = s + a` using `by omega`. Establish `e2 : s + (kk - 1 - (kk - 1 - 1 - a)) = s + a + 1` using `by omega`. Rewrite using `[e1, e2, hinv _ (by omega)]`.

Simplify using the standard rewrite rules. Rewrite using `[ry, rw']`. Unfold `phiJ`. Simplify using `only [entN_conj]`. Establish `hx : ∀ i ∈ range (s - 1), dN (g` using `g) s kk ob i * entN N i (i + 1) * dN s kk ob (i + 1) = entN N i (i + 1) := by`.

Introduce `i hi`. Rewrite `hi` using `[Finset.mem_range]`. Rewrite using `[index_diag_isotropic ob (by omega), index_diag_isotropic ob (by omega)]; ring`. Establish `hy : ∀ i ∈ range (s - 1), dN (g` using `g) s kk ob (s + kk + 1 + i) * entN N (s + kk + 1 + i) (s + kk + 2 + i) * dN s kk ob (s + kk + 2 + i) = -entN N (s + kk + 1 + i) (s + kk + 2 + i) := by`. Introduce `i hi`.

Rewrite using `[dN_y ob (by omega), dN_y ob (by omega)]`. Establish `e1 : s + kk + 1 + i - (s + kk + 1) = i` using `by omega`. Establish `e2 : s + kk + 2 + i - (s + kk + 1) = i + 1` using `by omega`. Rewrite using `[e1, e2, pow_succ]`. Take the linear combination `(-(entN N (s + kk + 1 + i) (s + kk + 2 + i))) * neg_one_sq (g := g) i`.

Establish `hw : ∀ a ∈ range (kk - 1), dN (g` using `g) s kk ob (s + a) * entN N (s + a) (s + a + 1) * dN s kk ob (s + a + 1) = (if ob then 1 else -1) * entN N (s + a) (s + a + 1) := by`. Introduce `a ha`. Rewrite `ha` using `[Finset.mem_range]`. Consider the cases of `ob`. Rewrite using `[dN_wf (by omega) (by omega), dN_wf (by omega) (by omega)]`.

Establish `e1 : s + a - s = a` using `by omega`. Establish `e2 : s + a + 1 - s = a + 1` using `by omega`. Rewrite using `[e1, e2, pow_succ]`. Simplify using `only [Bool.false_eq_true, if_false]`. Take the linear combination `(-(entN N (s + a) (s + a + 1))) * neg_one_sq (g := g) a`.

Rewrite using `[dN_wt (by omega) (by omega), dN_wt (by omega) (by omega)]`. Simplify using the standard rewrite rules. Rewrite using `[Finset.sum_congr rfl hx, Finset.sum_congr rfl hy, Finset.sum_congr rfl hw, ← Finset.mul_sum]`. Distinguish the cases in `hs : 1 ≤ s`. Rewrite using `[if_pos hs, if_pos hs]`.

Establish `h1 : dN (g` using `g) s kk ob (s - 1) = 1 := index_diag_isotropic ob (by omega)`. Establish `h2 : dN (g` using `g) s kk ob (s + kk) = 1 := dN_add_eq_one ob`. Establish `h3 : dN (g` using `g) s kk ob (s + kk + 1) = 1 := by rw [dN_y ob le_rfl]; simp`. Rewrite using `[h1, h2, h3, hinv _ (by omega), Finset.sum_neg_distrib]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[if_neg hs, if_neg hs]`. Establish `: s - 1 = 0` using `by omega`. Rewrite using `[this]`. Simplify using the standard rewrite rules.
-/
theorem phi_key (hr : r = kk + 2 * s + 1) (ob : Bool) {N N' : Matrix (Fin r) (Fin r) (ZMod g)}
    (hinv : ∀ i, i + 1 < r → entN N' i (i + 1) = -entN N i (i + 1)) :
    phiJ kk s (dM s kk ob * N * dM s kk ob) =
      (∑ a ∈ range s, (if a + 1 < s then entN N a (a + 1) + entN N' (s + kk + 1 + (s - 2 - a)) (s + kk + 1 + (s - 1 - a))
        else entN N a (s + kk) - entN N' (s + kk) (s + kk + 1))) +
      ∑ i ∈ range kk, (if i + 1 < kk then (if ob then entN N (s + i) (s + i + 1)
        else entN N' (s + (kk - 2 - i)) (s + (kk - 1 - i))) else 0) := by
  have split1 : ∀ a ∈ range s, (if a + 1 < s then entN N a (a + 1) + entN N' (s + kk + 1 + (s - 2 - a)) (s + kk + 1 + (s - 1 - a))
        else entN N a (s + kk) - entN N' (s + kk) (s + kk + 1)) =
      (if a + 1 < s then entN N a (a + 1) else 0) +
      (if a + 1 < s then entN N' (s + kk + 1 + (s - 2 - a)) (s + kk + 1 + (s - 1 - a)) else 0) +
      (if a + 1 < s then 0 else entN N (s - 1) (s + kk) - entN N' (s + kk) (s + kk + 1)) := by
    intro a ha
    rw [Finset.mem_range] at ha
    split_ifs with h
    · ring
    · have : a = s - 1 := by omega
      subst this; ring
  rw [Finset.sum_congr rfl split1, Finset.sum_add_distrib, Finset.sum_add_distrib, sum_range_pred, sum_range_pred,
    sum_range_last, sum_range_pred (fun i => if ob then entN N (s + i) (s + i + 1)
        else entN N' (s + (kk - 2 - i)) (s + (kk - 1 - i))) kk]

  have ry : ∑ a ∈ range (s - 1), entN N' (s + kk + 1 + (s - 2 - a)) (s + kk + 1 + (s - 1 - a)) =
      -∑ i ∈ range (s - 1), entN N (s + kk + 1 + i) (s + kk + 2 + i) := by
    rw [← Finset.sum_range_reflect, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [Finset.mem_range] at ha
    have e1 : s + kk + 1 + (s - 2 - (s - 1 - 1 - a)) = s + kk + 1 + a := by omega
    have e2 : s + kk + 1 + (s - 1 - (s - 1 - 1 - a)) = s + kk + 1 + a + 1 := by omega
    rw [e1, e2, hinv _ (by omega), show s + kk + 1 + a + 1 = s + kk + 2 + a by omega]
  have rw' : ∑ i ∈ range (kk - 1), (if ob then entN N (s + i) (s + i + 1)
        else entN N' (s + (kk - 2 - i)) (s + (kk - 1 - i))) =
      (if ob then 1 else -1) * ∑ a ∈ range (kk - 1), entN N (s + a) (s + a + 1) := by
    cases ob
    · simp only [Bool.false_eq_true, if_false, neg_one_mul]
      rw [← Finset.sum_range_reflect, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [Finset.mem_range] at ha
      have e1 : s + (kk - 2 - (kk - 1 - 1 - a)) = s + a := by omega
      have e2 : s + (kk - 1 - (kk - 1 - 1 - a)) = s + a + 1 := by omega
      rw [e1, e2, hinv _ (by omega)]
    · simp
  rw [ry, rw']
  unfold phiJ
  simp only [entN_conj]

  have hx : ∀ i ∈ range (s - 1), dN (g := g) s kk ob i * entN N i (i + 1) * dN s kk ob (i + 1) = entN N i (i + 1) := by
    intro i hi; rw [Finset.mem_range] at hi
    rw [index_diag_isotropic ob (by omega), index_diag_isotropic ob (by omega)]; ring
  have hy : ∀ i ∈ range (s - 1), dN (g := g) s kk ob (s + kk + 1 + i) * entN N (s + kk + 1 + i) (s + kk + 2 + i) *
      dN s kk ob (s + kk + 2 + i) = -entN N (s + kk + 1 + i) (s + kk + 2 + i) := by
    intro i hi
    rw [dN_y ob (by omega), dN_y ob (by omega)]
    have e1 : s + kk + 1 + i - (s + kk + 1) = i := by omega
    have e2 : s + kk + 2 + i - (s + kk + 1) = i + 1 := by omega
    rw [e1, e2, pow_succ]
    linear_combination (-(entN N (s + kk + 1 + i) (s + kk + 2 + i))) * neg_one_sq (g := g) i
  have hw : ∀ a ∈ range (kk - 1), dN (g := g) s kk ob (s + a) * entN N (s + a) (s + a + 1) * dN s kk ob (s + a + 1) =
      (if ob then 1 else -1) * entN N (s + a) (s + a + 1) := by
    intro a ha; rw [Finset.mem_range] at ha
    cases ob
    · rw [dN_wf (by omega) (by omega), dN_wf (by omega) (by omega)]
      have e1 : s + a - s = a := by omega
      have e2 : s + a + 1 - s = a + 1 := by omega
      rw [e1, e2, pow_succ]
      simp only [Bool.false_eq_true, if_false]
      linear_combination (-(entN N (s + a) (s + a + 1))) * neg_one_sq (g := g) a
    · rw [dN_wt (by omega) (by omega), dN_wt (by omega) (by omega)]
      simp
  rw [Finset.sum_congr rfl hx, Finset.sum_congr rfl hy, Finset.sum_congr rfl hw, ← Finset.mul_sum]
  by_cases hs : 1 ≤ s
  · rw [if_pos hs, if_pos hs]
    have h1 : dN (g := g) s kk ob (s - 1) = 1 := index_diag_isotropic ob (by omega)
    have h2 : dN (g := g) s kk ob (s + kk) = 1 := dN_add_eq_one ob
    have h3 : dN (g := g) s kk ob (s + kk + 1) = 1 := by rw [dN_y ob le_rfl]; simp
    rw [h1, h2, h3, hinv _ (by omega), Finset.sum_neg_distrib]
    ring
  · rw [if_neg hs, if_neg hs]
    have : s - 1 = 0 := by omega
    rw [this]
    simp

end Formalism.L2.SG.Pf.KppIdx
