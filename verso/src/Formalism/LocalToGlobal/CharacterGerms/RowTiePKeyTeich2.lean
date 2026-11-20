import Formalism.LocalToGlobal.CharacterGerms.RowTiePKeyTeichDef

noncomputable section

namespace Formalism.L2.FormalSeriesBounds

namespace RowTiePKeyTeich

open RowTiePKey RowTiePE0

section Lim

variable {C : Type} [Field C] {V : VF C} {n : ℕ}

/- English proof (translation)
Distinguish the cases in `h : V.v x = ⊤`. Conclude with `⟨0, show ((0 : ℝ) : WithTop ℝ) ≤ V.v x by rw [h]; exact le_top⟩`. Take `⟨r, hr⟩` from `WithTop.ne_top_iff_exists.1 h`. Conclude with `⟨r, show ((r : ℝ) : WithTop ℝ) ≤ V.v x from le_of_eq hr⟩`.
-/
private theorem exists_ge_character_germs (x : C) : ∃ B : ℝ, V.Ge B x := by
  by_cases h : V.v x = ⊤
  · exact ⟨0, show ((0 : ℝ) : WithTop ℝ) ≤ V.v x by rw [h]; exact le_top⟩
  · obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 h
    exact ⟨r, show ((r : ℝ) : WithTop ℝ) ≤ V.v x from le_of_eq hr⟩

/- English proof (translation)
Take `⟨Bx, hBx⟩` from `exists_ge_character_germs (V := V) x`. Take `⟨By, hBy⟩` from `exists_ge_character_germs (V := V) y`. Unfold `Tends at hs ht ⊢`. Introduce `w`. Take `⟨n1, hn1⟩` from `ht By`.

Take `⟨n2, hn2⟩` from `ht (w - Bx)`. Take `⟨n3, hn3⟩` from `hs (w - By)`. Use `⟨max n1 (max n2 n3), fun k hk => ?_⟩` and prove the remaining obligations. Establish `h1 : n1 ≤ k` using `le_trans (le_max_left _ _) hk`. Establish `h2 : n2 ≤ k` using `le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hk`.

Establish `h3 : n3 ≤ k` using `le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hk`. Establish `ht' : V.Ge By (t k)`. Establish `e : t k = y + -(y - t k)` using `by ring`. Rewrite using `[e]`. Conclude with `hBy.add (hn1 k h1).neg`.

Use `show V.Ge w (x * y - s k * t k)`. Establish `e : x * y - s k * t k = x * (y - t k) + (x - s k) * t k` using `by ring`. Rewrite using `[e]`. Conclude with `VF.Ge.add ((hBx.mul (hn2 k h2)).mono (by linarith)) (((hn3 k h3).mul ht').mono (by linarith))`.
-/
private theorem tends_mul' {s t : ℕ → C} {x y : C} (hs : Tends V s x) (ht : Tends V t y) :
    Tends V (fun k => s k * t k) (x * y) := by
  obtain ⟨Bx, hBx⟩ := exists_ge_character_germs (V := V) x
  obtain ⟨By, hBy⟩ := exists_ge_character_germs (V := V) y
  unfold Tends at hs ht ⊢
  intro w
  obtain ⟨n1, hn1⟩ := ht By
  obtain ⟨n2, hn2⟩ := ht (w - Bx)
  obtain ⟨n3, hn3⟩ := hs (w - By)
  refine ⟨max n1 (max n2 n3), fun k hk => ?_⟩
  have h1 : n1 ≤ k := le_trans (le_max_left _ _) hk
  have h2 : n2 ≤ k := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hk
  have h3 : n3 ≤ k := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hk
  have ht' : V.Ge By (t k) := by
    have e : t k = y + -(y - t k) := by ring
    rw [e]
    exact hBy.add (hn1 k h1).neg
  show V.Ge w (x * y - s k * t k)
  have e : x * y - s k * t k = x * (y - t k) + (x - s k) * t k := by ring
  rw [e]
  exact VF.Ge.add ((hBx.mul (hn2 k h2)).mono (by linarith)) (((hn3 k h3).mul ht').mono (by linarith))

/- English proof (translation)
Unfold `Tends at h ⊢`. Introduce `w`. Use `choose! n0 hn0 using fun i hi => h i hi w`. Use `⟨S.sup n0, fun k hk => ?_⟩` and prove the remaining obligations. Use `show V.Ge w (∑ i ∈ S, g i - ∑ i ∈ S, f i k)`.

Rewrite using `[← Finset.sum_sub_distrib]`. Conclude with `VF.Ge.sum fun i hi => hn0 i hi k (le_trans (Finset.le_sup hi) hk)`.
-/
private theorem tends_finset_sum {ι : Type} (S : Finset ι) {f : ι → ℕ → C} {g : ι → C}
    (h : ∀ i ∈ S, Tends V (f i) (g i)) : Tends V (fun k => ∑ i ∈ S, f i k) (∑ i ∈ S, g i) := by
  unfold Tends at h ⊢
  intro w
  choose! n0 hn0 using fun i hi => h i hi w
  refine ⟨S.sup n0, fun k hk => ?_⟩
  show V.Ge w (∑ i ∈ S, g i - ∑ i ∈ S, f i k)
  rw [← Finset.sum_sub_distrib]
  exact VF.Ge.sum fun i hi => hn0 i hi k (le_trans (Finset.le_sup hi) hk)

/- English proof (translation)
Simplify using `only [Matrix.mul_apply]`. Conclude with `tends_finset_sum (f := fun m k => s k i m * t k m j) (g := fun m => x i m * y m j) Finset.univ (fun m _ => tends_mul' (hs i m) (ht m j))`.
-/
theorem tends_mul {s t : ℕ → Matrix (Fin n) (Fin n) C} {x y : Matrix (Fin n) (Fin n) C}
    (hs : ∀ i j, Tends V (fun k => s k i j) (x i j)) (ht : ∀ i j, Tends V (fun k => t k i j) (y i j)) (i j : Fin n) :
    Tends V (fun k => (s k * t k) i j) ((x * y) i j) := by
  simp only [Matrix.mul_apply]
  exact tends_finset_sum (f := fun m k => s k i m * t k m j) (g := fun m => x i m * y m j) Finset.univ
    (fun m _ => tends_mul' (hs i m) (ht m j))

/- English proof (translation)
Proceed by induction on `m generalizing i j with`. Consider the case `zero`. Simplify using `only [pow_zero]`. Unfold `Tends`. Introduce `w`.

Conclude with `⟨0, fun k _ => by simp only [sub_self]; exact VF.Ge.zero w⟩`. Consider the case `succ m ih`. Simplify using `only [pow_succ]`. Conclude with `tends_mul (fun i j => ih i j) hs i j`.
-/
theorem tends_pow {s : ℕ → Matrix (Fin n) (Fin n) C} {x : Matrix (Fin n) (Fin n) C}
    (hs : ∀ i j, Tends V (fun k => s k i j) (x i j)) (m : ℕ) (i j : Fin n) :
    Tends V (fun k => (s k ^ m) i j) ((x ^ m) i j) := by
  induction m generalizing i j with
  | zero =>
    simp only [pow_zero]
    unfold Tends
    intro w
    exact ⟨0, fun k _ => by simp only [sub_self]; exact VF.Ge.zero w⟩
  | succ m ih =>
    simp only [pow_succ]
    exact tends_mul (fun i j => ih i j) hs i j

/- English proof (translation)
Unfold `Tends at h ⊢`. Introduce `w`. Take `⟨n0, hn0⟩` from `h w`. Conclude with `⟨n0, fun k hk => hn0 (k + 1) (by omega)⟩`.
-/
theorem tends_shift {s : ℕ → C} {x : C} (h : Tends V s x) : Tends V (fun k => s (k + 1)) x := by
  unfold Tends at h ⊢
  intro w
  obtain ⟨n0, hn0⟩ := h w
  exact ⟨n0, fun k hk => hn0 (k + 1) (by omega)⟩

def IntM (V : VF C) (n : ℕ) : Subring (Matrix (Fin n) (Fin n) C) where
  carrier := {M | ∀ i j, V.Ge 0 (M i j)}
  mul_mem' := fun {a b} ha hb i j => by
    simp only [Matrix.mul_apply]
    exact VF.Ge.sum fun m _ => ((ha i m).mul (hb m j)).mono (by norm_num)
  one_mem' := fun i j => by
    by_cases h : i = j
    · simp only [Matrix.one_apply, h, if_true]; exact VF.Ge.one
    · simp only [Matrix.one_apply, h, if_false]; exact VF.Ge.zero 0
  add_mem' := fun {a b} ha hb i j => (ha i j).add (hb i j)
  zero_mem' := fun _ _ => VF.Ge.zero 0
  neg_mem' := fun {a} ha i j => (ha i j).neg

end Lim

/- English proof (translation)
Introduce `h0`. Establish `h4` using `V.4`. Rewrite `h4` using `[h0, AddValuation.map_zero]`. Conclude with `WithTop.top_ne_coe (h4.trans WithTop.coe_one.symm)`.
-/
private theorem l_cast_ne_zero {C : Type} [Field C] (V : VF C) : (V.l : C) ≠ 0 := by
  intro h0
  have h4 := V.4
  rw [h0, AddValuation.map_zero] at h4
  exact WithTop.top_ne_coe (h4.trans WithTop.coe_one.symm)

/- English proof (translation)
The claim follows from `show ((1 : ℝ) : WithTop ℝ) ≤ V.v (V.l : C) from le_of_eq (by rw [V.4, WithTop.coe_one])`.
-/
private theorem ge_one_l {C : Type} [Field C] (V : VF C) : V.Ge 1 (V.l : C) :=
  show ((1 : ℝ) : WithTop ℝ) ≤ V.v (V.l : C) from le_of_eq (by rw [V.4, WithTop.coe_one])

/- English proof (translation)
Proceed by induction on `c with`. Consider the case `zero => rw [Nat.cast_zero]`. Conclude with `VF.Ge.zero 0`. Consider the case `succ c ih => rw [Nat.cast_succ]`. Conclude with `ih.add VF.Ge.one`.
-/
private theorem ge_zero_natCast {C : Type} [Field C] (V : VF C) (c : ℕ) : V.Ge 0 (c : C) := by
  induction c with
  | zero => rw [Nat.cast_zero]; exact VF.Ge.zero 0
  | succ c ih => rw [Nat.cast_succ]; exact ih.add VF.Ge.one

/- English proof (translation)
Take `⟨m, rfl⟩` from `h`. Rewrite using `[Nat.cast_mul]`. Conclude with `((ge_one_l V).mul (ge_zero_natCast V m)).mono (by norm_num)`.
-/
private theorem ge_one_natCast_of_l_dvd {C : Type} [Field C] {V : VF C} {c : ℕ} (h : V.l ∣ c) : V.Ge 1 (c : C) := by
  obtain ⟨m, rfl⟩ := h
  rw [Nat.cast_mul]
  exact ((ge_one_l V).mul (ge_zero_natCast V m)).mono (by norm_num)

/- English proof (translation)
Establish `e1 : e = (V.l : C) * ((V.l : C)⁻¹ * e)`. Rewrite using `[← mul_assoc, mul_inv_cancel₀ (l_cast_ne_zero V), one_mul]`. Establish `h2 : ((w + 1 : ℝ) : WithTop ℝ) ≤ V.v (V.l : C) + V.v ((V.l : C)⁻¹ * e)`. Rewrite using `[← AddValuation.map_mul, ← e1]`. Conclude with `he`.

Rewrite `h2` using `[V.4]`. Use `show ((w : ℝ) : WithTop ℝ) ≤ V.v ((V.l : C)⁻¹ * e)`. Generalize the expression as in `V.v ((V.l : C)⁻¹ * e) = u at h2 ⊢`. Proceed by induction on `u using WithTop.recTopCoe with`. Consider the case `top => exact le_top`.

Consider the case `coe r`. Rewrite `h2` using `[← WithTop.coe_one, ← WithTop.coe_add, WithTop.coe_le_coe]`. Rewrite using `[WithTop.coe_le_coe]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem ge_inv_l_mul_of_ge_add_one {C : Type} [Field C] {V : VF C} {w : ℝ} {e : C} (he : V.Ge (w + 1) e) :
    V.Ge w ((V.l : C)⁻¹ * e) := by
  have e1 : e = (V.l : C) * ((V.l : C)⁻¹ * e) := by
    rw [← mul_assoc, mul_inv_cancel₀ (l_cast_ne_zero V), one_mul]
  have h2 : ((w + 1 : ℝ) : WithTop ℝ) ≤ V.v (V.l : C) + V.v ((V.l : C)⁻¹ * e) := by
    rw [← AddValuation.map_mul, ← e1]
    exact he
  rw [V.4] at h2
  show ((w : ℝ) : WithTop ℝ) ≤ V.v ((V.l : C)⁻¹ * e)
  generalize V.v ((V.l : C)⁻¹ * e) = u at h2 ⊢
  induction u using WithTop.recTopCoe with
  | top => exact le_top
  | coe r =>
    rw [← WithTop.coe_one, ← WithTop.coe_add, WithTop.coe_le_coe] at h2
    rw [WithTop.coe_le_coe]
    linarith

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Establish `hne' : V.v (a - c) ≠ ⊤`. Rewrite using `[Ne, AddValuation.top_iff]`. Conclude with `sub_ne_zero.2 hne`. Take `⟨r, hr⟩` from `WithTop.ne_top_iff_exists.1 hne'`.

Unfold `Tends at ha hc`. Take `⟨n1, hn1⟩` from `ha (r + 1)`. Take `⟨n2, hn2⟩` from `hc (r + 1)`. Establish `h` using `(hn1 (max n1 n2) (le_max_left _ _)).add (hn2 (max n1 n2) (le_max_right _ _)).neg`. Establish `e : a - u (max n1 n2) + -(c - u (max n1 n2)) = a - c` using `by ring`.

Rewrite `h` using `[e]`. Establish `h' : ((r + 1 : ℝ) : WithTop ℝ) ≤ (r : WithTop ℝ)`. Rewrite using `[hr]`. Conclude with `h`. Rewrite `h'` using `[WithTop.coe_le_coe]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem eq_of_tends_of_tends {C : Type} [Field C] {V : VF C} {u : ℕ → C} {a c : C}
    (ha : Tends V u a) (hc : Tends V u c) : a = c := by
  by_contra hne
  have hne' : V.v (a - c) ≠ ⊤ := by
    rw [Ne, AddValuation.top_iff]
    exact sub_ne_zero.2 hne
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 hne'
  unfold Tends at ha hc
  obtain ⟨n1, hn1⟩ := ha (r + 1)
  obtain ⟨n2, hn2⟩ := hc (r + 1)
  have h := (hn1 (max n1 n2) (le_max_left _ _)).add (hn2 (max n1 n2) (le_max_right _ _)).neg
  have e : a - u (max n1 n2) + -(c - u (max n1 n2)) = a - c := by ring
  rw [e] at h
  have h' : ((r + 1 : ℝ) : WithTop ℝ) ≤ (r : WithTop ℝ) := by
    rw [hr]
    exact h
  rw [WithTop.coe_le_coe] at h'
  linarith

/- English proof (translation)
Introduce `i j`. Rewrite using `[Matrix.mul_apply]`. Conclude with `VF.Ge.sum fun m _ => (hP i m).mul (hR m j)`.
-/
private theorem ge_add_matrix_mul_entry_of_ge {C : Type} [Field C] {V : VF C} {n : ℕ} {P R : Matrix (Fin n) (Fin n) C}
    {a b : ℝ} (hP : ∀ i j, V.Ge a (P i j)) (hR : ∀ i j, V.Ge b (R i j)) :
    ∀ i j, V.Ge (a + b) ((P * R) i j) := by
  intro i j
  rw [Matrix.mul_apply]
  exact VF.Ge.sum fun m _ => (hP i m).mul (hR m j)

/- English proof (translation)
Distinguish the cases in `h : i = j`. Simplify using `only [Matrix.one_apply, h, if_true]`. Conclude with `VF.Ge.one`. Simplify using `only [Matrix.one_apply, h, if_false]`. Conclude with `VF.Ge.zero 0`.
-/
private theorem ge_zero_matrix_one_entry {C : Type} [Field C] (V : VF C) (n : ℕ) (i j : Fin n) :
    V.Ge 0 ((1 : Matrix (Fin n) (Fin n) C) i j) := by
  by_cases h : i = j
  · simp only [Matrix.one_apply, h, if_true]
    exact VF.Ge.one
  · simp only [Matrix.one_apply, h, if_false]
    exact VF.Ge.zero 0

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero`. Introduce `i j`. Rewrite using `[pow_zero]`. Apply the tactic sequence `exact ge_zero_matrix_one_entry V n i j`.

Consider the case `succ m ih`. Introduce `i j`. Rewrite using `[pow_succ]`. Conclude with `(ge_add_matrix_mul_entry_of_ge ih hP i j).mono (by norm_num)`.
-/
private theorem ge_zero_matrix_pow_entry_of_ge_zero {C : Type} [Field C] {V : VF C} {n : ℕ} {P : Matrix (Fin n) (Fin n) C}
    (hP : ∀ i j, V.Ge 0 (P i j)) (m : ℕ) : ∀ i j, V.Ge 0 ((P ^ m) i j) := by
  induction m with
  | zero =>
    intro i j
    rw [pow_zero]
    exact ge_zero_matrix_one_entry V n i j
  | succ m ih =>
    intro i j
    rw [pow_succ]
    exact (ge_add_matrix_mul_entry_of_ge ih hP i j).mono (by norm_num)

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero`. Introduce `i j`. Rewrite using `[pow_zero]`. Apply the tactic sequence `exact (ge_zero_matrix_one_entry V n i j).mono (by simp)`.

Consider the case `succ m ih`. Introduce `i j`. Rewrite using `[pow_succ]`. Conclude with `(ge_add_matrix_mul_entry_of_ge ih hP i j).mono (le_of_eq (by push_cast; ring))`.
-/
private theorem ge_nsmul_matrix_pow_entry_of_ge {C : Type} [Field C] {V : VF C} {n : ℕ} {P : Matrix (Fin n) (Fin n) C}
    {t : ℝ} (hP : ∀ i j, V.Ge t (P i j)) (m : ℕ) : ∀ i j, V.Ge ((m : ℝ) * t) ((P ^ m) i j) := by
  induction m with
  | zero =>
    intro i j
    rw [pow_zero]
    exact (ge_zero_matrix_one_entry V n i j).mono (by simp)
  | succ m ih =>
    intro i j
    rw [pow_succ]
    exact (ge_add_matrix_mul_entry_of_ge ih hP i j).mono (le_of_eq (by push_cast; ring))

/- English proof (translation)
Unfold `TeichSt`. Introduce `C _ V hcomp n d hd A hadd hneg hmul hcomm hint hclos hfrob b hb`. Establish `h0 : (0 : Matrix (Fin n) (Fin n) C) ∈ A`. Simplify using `using hadd b hb (-b) (hneg b hb)`. Establish `hsub : ∀ a ∈ A, ∀ c ∈ A, a - c ∈ A` using `fun a ha c hc => by`.

Rewrite using `[sub_eq_add_neg]`. Conclude with `hadd a ha _ (hneg c hc)`. Establish `hpow : ∀ a ∈ A, ∀ k : ℕ, a ^ (k + 1) ∈ A`. Introduce `a ha k`. Proceed by induction on `k with`.

Consider the case `zero`. Rewrite using `[zero_add, pow_one]`. Conclude with `ha`. Consider the case `succ k ih`. Rewrite using `[pow_succ]`.

Conclude with `hmul _ ih _ ha`. Establish `hpowA : ∀ a ∈ A, ∀ k : ℕ, 0 < k → a ^ k ∈ A`. Introduce `a ha k hk`. Take `⟨k', rfl⟩` from `Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.1 hk)`. Conclude with `hpow a ha k'`.

Establish `Rl : ∀ x ∈ A, ∀ y ∈ A, ∀ t : ℝ, 1 ≤ t → (∀ i j, V.Ge t ((y - x) i j)) → ∀ i j, V.Ge (t + 1) ((y ^ V.l - x ^ V.l) i j)`. Introduce `x hx y hy t ht hδ`. Establish `hc : Commute x (y - x)` using `by show x * (y - x) = (y - x) * x`. Rewrite using `[mul_sub, sub_mul, hcomm x hx y hy]`. Establish `hexp : y ^ V.l - x ^ V.l = ∑ m ∈ Finset.range V.l, x ^ m * (y - x) ^ (V.l - m) * ((V.l.choose m : ℕ) : Matrix (Fin n) (Fin n) C)`.

Establish `e : x + (y - x) = y` using `by abel`. Establish `h1` using `hc.add_pow V.l`. Rewrite `h1` using `[e, Finset.sum_range_succ, Nat.sub_self, pow_zero, mul_one, Nat.choose_self, Nat.cast_one, mul_one]`. Rewrite using `[h1]`. Normalize the expressions using the abelian group laws.

Establish `hl2 : 2 ≤ V.l` using `V.3.two_le`. Establish `ht0 : (0 : ℝ) ≤ t` using `by linarith`. Introduce `i j`. Rewrite using `[hexp, Matrix.sum_apply]`. Use `VF.Ge.sum fun m hm => ?_` and prove the remaining obligations.

Rewrite `hm` using `[Finset.mem_range]`. Rewrite using `[← nsmul_eq_mul', Matrix.smul_apply, nsmul_eq_mul]`. Establish `hP` using `ge_add_matrix_mul_entry_of_ge (ge_zero_matrix_pow_entry_of_ge_zero (hint x hx) m) (ge_nsmul_matrix_pow_entry_of_ge hδ (V.l - m)) i j`. Break down `Nat.eq_zero_or_pos m with rfl | hm0` into its components or cases. Establish `hL : (2 : ℝ) ≤ ((V.l - 0 : ℕ) : ℝ)` using `by exact_mod_cast (by omega : 2 ≤ V.l - 0)`.

Use `((ge_zero_natCast V (V.l.choose 0)).mul hP).mono ?_` and prove the remaining obligations. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_right hL ht0]`. Establish `hdiv : V.l ∣ V.l.choose m` using `V.3.dvd_choose_self (by omega) hm`. Establish `hL : (1 : ℝ) ≤ ((V.l - m : ℕ) : ℝ)` using `by exact_mod_cast (by omega : 1 ≤ V.l - m)`. Use `((ge_one_natCast_of_l_dvd hdiv).mul hP).mono ?_` and prove the remaining obligations.

Use polynomial arithmetic with `[mul_le_mul_of_nonneg_right hL ht0]`. Establish `Rd : ∀ e : ℕ, ∀ x ∈ A, ∀ y ∈ A, ∀ t : ℝ, 1 ≤ t → (∀ i j, V.Ge t ((y - x) i j)) → ∀ i j, V.Ge (t + e) ((y ^ V.l ^ e - x ^ V.l ^ e) i j)`. Introduce `e`. Proceed by induction on `e with`. Consider the case `zero`.

Introduce `x hx y hy t ht h i j`. Simplify using `only [pow_zero, pow_one, Nat.cast_zero, add_zero]`. Conclude with `h i j`. Consider the case `succ e ih`. Introduce `x hx y hy t ht h i j`.

Establish `hpos : 0 < V.l ^ e` using `pow_pos V.3.pos e`. Establish `h1` using `ih x hx y hy t ht h`. Establish `he0 : (0 : ℝ) ≤ e` using `Nat.cast_nonneg e`. Establish `h2` using `Rl _ (hpowA x hx _ hpos) _ (hpowA y hy _ hpos) (t + e) (by linarith) h1 i j`. Rewrite using `[pow_succ, pow_mul, pow_mul]`.

Conclude with `h2.mono (le_of_eq (by push_cast; ring))`. Take `⟨s, hs⟩ : ∃ s : ℕ → Matrix (Fin n) (Fin n) C, ∀ k, s k = b ^ ((V.l ^ d) ^ k)` from `⟨_, fun k => rfl⟩`. Establish `hq : 0 < V.l ^ d` using `pow_pos V.3.pos d`. Establish `hsA : ∀ k, s k ∈ A` using `fun k => by`. Rewrite using `[hs]`.

Conclude with `hpowA b hb _ (pow_pos hq k)`. Establish `hsS : ∀ k, s (k + 1) = s k ^ V.l ^ d` using `fun k => by`. Rewrite using `[hs, hs, pow_succ, pow_mul]`. Establish `hd1 : (1 : ℝ) ≤ d` using `by exact_mod_cast Nat.one_le_iff_ne_zero.2 hd`. Establish `hD : ∀ k : ℕ, ∀ i j, V.Ge ((k : ℝ) + 1) ((s (k + 1) - s k) i j)`.

Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`. Introduce `i j`. Rewrite using `[hsS 0]`.

Establish `hm` using `hint _ (hfrob (s 0) (hsA 0)) i j`. Establish `e : s 0 ^ V.l ^ d - s 0 = (V.l : C) • ((V.l : C)⁻¹ • (s 0 ^ V.l ^ d - s 0))`. Rewrite using `[smul_smul, mul_inv_cancel₀ (l_cast_ne_zero V), one_smul]`. Rewrite using `[e, Matrix.smul_apply, smul_eq_mul]`. Conclude with `((ge_one_l V).mul hm).mono (by norm_num)`.

Consider the case `succ k ih`. Introduce `i j`. Establish `e : s (k + 1 + 1) - s (k + 1) = s (k + 1) ^ V.l ^ d - s k ^ V.l ^ d`. Rewrite using `[← hsS, ← hsS]`. Rewrite using `[e]`.

Establish `hk0 : (0 : ℝ) ≤ k` using `Nat.cast_nonneg k`. Conclude with `(Rd d _ (hsA k) _ (hsA (k + 1)) ((k : ℝ) + 1) (by linarith) ih i j).mono (by push_cast; linarith)`. Establish `hcau : ∀ i j, ∃ x : C, ∀ k : ℕ, V.Ge (k : ℝ) (x - s k i j)` using `fun i j => hcomp (fun k => s k i j) (fun k => (hD k i j).mono (by linarith))`. Take `⟨T, hT⟩ : ∃ T : Matrix (Fin n) (Fin n) C, ∀ i j (k : ℕ), V.Ge (k : ℝ) (T i j - s k i j)` from `⟨Matrix.of fun i j => Classical.choose (hcau i j), fun i j k => Classical.choose_spec (hcau i j) k⟩`. Establish `hTt : ∀ i j, Tends V (fun k => s k i j) (T i j)`.

Introduce `i j`. Unfold `Tends`. Introduce `w`. Conclude with `⟨⌈w⌉₊, fun k hk => (hT i j k).mono (le_trans (Nat.le_ceil w) (by exact_mod_cast hk))⟩`. Establish `hTA : T ∈ A` using `hclos s T hsA hTt`.

Establish `hTq : T ^ V.l ^ d = T`. Use extensionality with `i j`. Establish `h1` using `tends_pow hTt (V.l ^ d) i j`. Simplify using `only [← hsS] at h1`. Conclude with `eq_of_tends_of_tends h1 (tends_shift (hTt i j))`.

Establish `hbs : ∀ k, (V.l : C)⁻¹ • (b - s k) ∈ A`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`. Rewrite using `[hs 0, pow_zero, pow_one, sub_self, smul_zero]`.

Conclude with `h0`. Consider the case `succ k ih`. Establish `e : (V.l : C)⁻¹ • (b - s (k + 1)) = (V.l : C)⁻¹ • (b - s k) - (V.l : C)⁻¹ • (s k ^ V.l ^ d - s k)`. Rewrite using `[hsS k, ← smul_sub]`. Use `congr 1`.

Normalize the expressions using the abelian group laws. Rewrite using `[e]`. Conclude with `hsub _ ih _ (hfrob _ (hsA k))`. Establish `hlim : ∀ i j, Tends V (fun k => ((V.l : C)⁻¹ • (b - s k)) i j) (((V.l : C)⁻¹ • (b - T)) i j)`. Introduce `i j`.

Establish `h1` using `hTt i j`. Unfold `Tends at h1 ⊢`. Introduce `w`. Take `⟨n0, hn0⟩` from `h1 (w + 1)`. Use `⟨n0, fun k hk => ?_⟩` and prove the remaining obligations.

Use `show V.Ge w (((V.l : C)⁻¹ • (b - T)) i j - ((V.l : C)⁻¹ • (b - s k)) i j)`. Simplify using `only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]`. Establish `e : (V.l : C)⁻¹ * (b i j - T i j) - (V.l : C)⁻¹ * (b i j - s k i j) = (V.l : C)⁻¹ * -(T i j - s k i j)` using `by ring`. Rewrite using `[e]`. Conclude with `ge_inv_l_mul_of_ge_add_one (hn0 k hk).neg`.

Conclude with `⟨T, hTA, hTq, hclos _ _ hbs hlim⟩`.
-/
theorem teich_holds : TeichSt := by
  unfold TeichSt
  intro C _ V hcomp n d hd A hadd hneg hmul hcomm hint hclos hfrob b hb
  have h0 : (0 : Matrix (Fin n) (Fin n) C) ∈ A := by
    simpa using hadd b hb (-b) (hneg b hb)
  have hsub : ∀ a ∈ A, ∀ c ∈ A, a - c ∈ A := fun a ha c hc => by
    rw [sub_eq_add_neg]
    exact hadd a ha _ (hneg c hc)
  have hpow : ∀ a ∈ A, ∀ k : ℕ, a ^ (k + 1) ∈ A := by
    intro a ha k
    induction k with
    | zero =>
      rw [zero_add, pow_one]
      exact ha
    | succ k ih =>
      rw [pow_succ]
      exact hmul _ ih _ ha
  have hpowA : ∀ a ∈ A, ∀ k : ℕ, 0 < k → a ^ k ∈ A := by
    intro a ha k hk
    obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.1 hk)
    exact hpow a ha k'

  have Rl : ∀ x ∈ A, ∀ y ∈ A, ∀ t : ℝ, 1 ≤ t → (∀ i j, V.Ge t ((y - x) i j)) →
      ∀ i j, V.Ge (t + 1) ((y ^ V.l - x ^ V.l) i j) := by
    intro x hx y hy t ht hδ
    have hc : Commute x (y - x) := by
      show x * (y - x) = (y - x) * x
      rw [mul_sub, sub_mul, hcomm x hx y hy]
    have hexp : y ^ V.l - x ^ V.l = ∑ m ∈ Finset.range V.l,
        x ^ m * (y - x) ^ (V.l - m) * ((V.l.choose m : ℕ) : Matrix (Fin n) (Fin n) C) := by
      have e : x + (y - x) = y := by abel
      have h1 := hc.add_pow V.l
      rw [e, Finset.sum_range_succ, Nat.sub_self, pow_zero, mul_one, Nat.choose_self, Nat.cast_one,
        mul_one] at h1
      rw [h1]
      abel
    have hl2 : 2 ≤ V.l := V.3.two_le
    have ht0 : (0 : ℝ) ≤ t := by linarith
    intro i j
    rw [hexp, Matrix.sum_apply]
    refine VF.Ge.sum fun m hm => ?_
    rw [Finset.mem_range] at hm
    rw [← nsmul_eq_mul', Matrix.smul_apply, nsmul_eq_mul]
    have hP := ge_add_matrix_mul_entry_of_ge (ge_zero_matrix_pow_entry_of_ge_zero (hint x hx) m) (ge_nsmul_matrix_pow_entry_of_ge hδ (V.l - m)) i j
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · have hL : (2 : ℝ) ≤ ((V.l - 0 : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ V.l - 0)
      refine ((ge_zero_natCast V (V.l.choose 0)).mul hP).mono ?_
      nlinarith [mul_le_mul_of_nonneg_right hL ht0]
    · have hdiv : V.l ∣ V.l.choose m := V.3.dvd_choose_self (by omega) hm
      have hL : (1 : ℝ) ≤ ((V.l - m : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ V.l - m)
      refine ((ge_one_natCast_of_l_dvd hdiv).mul hP).mono ?_
      nlinarith [mul_le_mul_of_nonneg_right hL ht0]
  have Rd : ∀ e : ℕ, ∀ x ∈ A, ∀ y ∈ A, ∀ t : ℝ, 1 ≤ t → (∀ i j, V.Ge t ((y - x) i j)) →
      ∀ i j, V.Ge (t + e) ((y ^ V.l ^ e - x ^ V.l ^ e) i j) := by
    intro e
    induction e with
    | zero =>
      intro x hx y hy t ht h i j
      simp only [pow_zero, pow_one, Nat.cast_zero, add_zero]
      exact h i j
    | succ e ih =>
      intro x hx y hy t ht h i j
      have hpos : 0 < V.l ^ e := pow_pos V.3.pos e
      have h1 := ih x hx y hy t ht h
      have he0 : (0 : ℝ) ≤ e := Nat.cast_nonneg e
      have h2 := Rl _ (hpowA x hx _ hpos) _ (hpowA y hy _ hpos) (t + e) (by linarith) h1 i j
      rw [pow_succ, pow_mul, pow_mul]
      exact h2.mono (le_of_eq (by push_cast; ring))

  obtain ⟨s, hs⟩ : ∃ s : ℕ → Matrix (Fin n) (Fin n) C, ∀ k, s k = b ^ ((V.l ^ d) ^ k) :=
    ⟨_, fun k => rfl⟩
  have hq : 0 < V.l ^ d := pow_pos V.3.pos d
  have hsA : ∀ k, s k ∈ A := fun k => by
    rw [hs]
    exact hpowA b hb _ (pow_pos hq k)
  have hsS : ∀ k, s (k + 1) = s k ^ V.l ^ d := fun k => by
    rw [hs, hs, pow_succ, pow_mul]
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hd
  have hD : ∀ k : ℕ, ∀ i j, V.Ge ((k : ℝ) + 1) ((s (k + 1) - s k) i j) := by
    intro k
    induction k with
    | zero =>
      intro i j
      rw [hsS 0]
      have hm := hint _ (hfrob (s 0) (hsA 0)) i j
      have e : s 0 ^ V.l ^ d - s 0 = (V.l : C) • ((V.l : C)⁻¹ • (s 0 ^ V.l ^ d - s 0)) := by
        rw [smul_smul, mul_inv_cancel₀ (l_cast_ne_zero V), one_smul]
      rw [e, Matrix.smul_apply, smul_eq_mul]
      exact ((ge_one_l V).mul hm).mono (by norm_num)
    | succ k ih =>
      intro i j
      have e : s (k + 1 + 1) - s (k + 1) = s (k + 1) ^ V.l ^ d - s k ^ V.l ^ d := by
        rw [← hsS, ← hsS]
      rw [e]
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      exact (Rd d _ (hsA k) _ (hsA (k + 1)) ((k : ℝ) + 1) (by linarith) ih i j).mono
        (by push_cast; linarith)
  have hcau : ∀ i j, ∃ x : C, ∀ k : ℕ, V.Ge (k : ℝ) (x - s k i j) := fun i j =>
    hcomp (fun k => s k i j) (fun k => (hD k i j).mono (by linarith))
  obtain ⟨T, hT⟩ : ∃ T : Matrix (Fin n) (Fin n) C, ∀ i j (k : ℕ), V.Ge (k : ℝ) (T i j - s k i j) :=
    ⟨Matrix.of fun i j => Classical.choose (hcau i j), fun i j k => Classical.choose_spec (hcau i j) k⟩
  have hTt : ∀ i j, Tends V (fun k => s k i j) (T i j) := by
    intro i j
    unfold Tends
    intro w
    exact ⟨⌈w⌉₊, fun k hk => (hT i j k).mono (le_trans (Nat.le_ceil w) (by exact_mod_cast hk))⟩
  have hTA : T ∈ A := hclos s T hsA hTt
  have hTq : T ^ V.l ^ d = T := by
    ext i j
    have h1 := tends_pow hTt (V.l ^ d) i j
    simp only [← hsS] at h1
    exact eq_of_tends_of_tends h1 (tends_shift (hTt i j))
  have hbs : ∀ k, (V.l : C)⁻¹ • (b - s k) ∈ A := by
    intro k
    induction k with
    | zero =>
      rw [hs 0, pow_zero, pow_one, sub_self, smul_zero]
      exact h0
    | succ k ih =>
      have e : (V.l : C)⁻¹ • (b - s (k + 1)) =
          (V.l : C)⁻¹ • (b - s k) - (V.l : C)⁻¹ • (s k ^ V.l ^ d - s k) := by
        rw [hsS k, ← smul_sub]
        congr 1
        abel
      rw [e]
      exact hsub _ ih _ (hfrob _ (hsA k))
  have hlim : ∀ i j, Tends V (fun k => ((V.l : C)⁻¹ • (b - s k)) i j) (((V.l : C)⁻¹ • (b - T)) i j) := by
    intro i j
    have h1 := hTt i j
    unfold Tends at h1 ⊢
    intro w
    obtain ⟨n0, hn0⟩ := h1 (w + 1)
    refine ⟨n0, fun k hk => ?_⟩
    show V.Ge w (((V.l : C)⁻¹ • (b - T)) i j - ((V.l : C)⁻¹ • (b - s k)) i j)
    simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
    have e : (V.l : C)⁻¹ * (b i j - T i j) - (V.l : C)⁻¹ * (b i j - s k i j) =
        (V.l : C)⁻¹ * -(T i j - s k i j) := by ring
    rw [e]
    exact ge_inv_l_mul_of_ge_add_one (hn0 k hk).neg
  exact ⟨T, hTA, hTq, hclos _ _ hbs hlim⟩

end RowTiePKeyTeich

end Formalism.L2.FormalSeriesBounds
