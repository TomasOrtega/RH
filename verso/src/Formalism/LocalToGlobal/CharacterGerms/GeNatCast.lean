import Mathlib

namespace Formalism.L2.FormalSeriesBounds

open Finset

noncomputable section

structure VF (C : Type*) [Field C] where
  v : AddValuation C (WithTop ℝ)
  l : ℕ
  l_prime : l.Prime
  v_l : v (l : C) = 1

variable {C : Type*} [Field C]

namespace VF

variable (V : VF C)

def Ge (w : ℝ) (a : C) : Prop := (w : WithTop ℝ) ≤ V.v a

variable {V}

/- English proof (translation)
The claim follows from `le_trans (WithTop.coe_le_coe.mpr hw) h`.
-/
theorem Ge.mono {w w' : ℝ} {a : C} (h : V.Ge w a) (hw : w' ≤ w) : V.Ge w' a := le_trans (WithTop.coe_le_coe.mpr hw) h

/- English proof (translation)
Use `show ((w : ℝ) : WithTop ℝ) ≤ V.v 0`. Rewrite using `[AddValuation.map_zero]`. Conclude with `le_top`.
-/
theorem Ge.zero (w : ℝ) : V.Ge w (0 : C) := by
  show ((w : ℝ) : WithTop ℝ) ≤ V.v 0
  rw [AddValuation.map_zero]
  exact le_top

/- English proof (translation)
The claim follows from `le_trans (le_min ha hb) (V.v.map_add a b)`.
-/
theorem Ge.add {w : ℝ} {a b : C} (ha : V.Ge w a) (hb : V.Ge w b) : V.Ge w (a + b) := le_trans (le_min ha hb) (V.v.map_add a b)

/- English proof (translation)
Use `show ((w : ℝ) : WithTop ℝ) ≤ V.v (-a)`. Rewrite using `[AddValuation.map_neg]`. Conclude with `ha`.
-/
theorem Ge.neg {w : ℝ} {a : C} (ha : V.Ge w a) : V.Ge w (-a) := by
  show ((w : ℝ) : WithTop ℝ) ≤ V.v (-a)
  rw [AddValuation.map_neg]
  exact ha

/- English proof (translation)
Rewrite using `[sub_eq_add_neg]`. Conclude with `Ge.add ha (Ge.neg hb)`.
-/
theorem Ge.sub {w : ℝ} {a b : C} (ha : V.Ge w a) (hb : V.Ge w b) : V.Ge w (a - b) := by
  rw [sub_eq_add_neg]
  exact Ge.add ha (Ge.neg hb)

/- English proof (translation)
The claim follows from `Finset.sum_induction f (fun x => V.Ge w x) (fun _ _ ha hb => Ge.add ha hb) (Ge.zero w) h`.
-/
theorem Ge.sum {ι : Type*} {s : Finset ι} {f : ι → C} {w : ℝ} (h : ∀ i ∈ s, V.Ge w (f i)) :
    V.Ge w (∑ i ∈ s, f i) := Finset.sum_induction f (fun x => V.Ge w x) (fun _ _ ha hb => Ge.add ha hb) (Ge.zero w) h

/- English proof (translation)
Use `show ((w + w' : ℝ) : WithTop ℝ) ≤ V.v (a * b)`. Rewrite using `[AddValuation.map_mul, WithTop.coe_add]`. Conclude with `add_le_add ha hb`.
-/
theorem Ge.mul {w w' : ℝ} {a b : C} (ha : V.Ge w a) (hb : V.Ge w' b) : V.Ge (w + w') (a * b) := by
  show ((w + w' : ℝ) : WithTop ℝ) ≤ V.v (a * b)
  rw [AddValuation.map_mul, WithTop.coe_add]
  exact add_le_add ha hb

/- English proof (translation)
Use `show ((0 : ℝ) : WithTop ℝ) ≤ V.v 1`. Rewrite using `[AddValuation.map_one]`. Conclude with `le_of_eq WithTop.coe_zero`.
-/
theorem Ge.one : V.Ge 0 (1 : C) := by
  show ((0 : ℝ) : WithTop ℝ) ≤ V.v 1
  rw [AddValuation.map_one]
  exact le_of_eq WithTop.coe_zero

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simpa using (Ge.one (V := V))`. Consider the case `succ n ih`. Rewrite using `[pow_succ]`. Simplify using `using Ge.mul ih ha`.
-/
theorem Ge.pow {a : C} (ha : V.Ge 0 a) (n : ℕ) : V.Ge 0 (a ^ n) := by
  induction n with
  | zero => simpa using (Ge.one (V := V))
  | succ n ih =>
    rw [pow_succ]
    simpa using Ge.mul ih ha

/- English proof (translation)
Simplify using `using Ge.mul ha hb`.
-/
theorem Ge.mul_int {w : ℝ} {a b : C} (ha : V.Ge 0 a) (hb : V.Ge w b) : V.Ge w (a * b) := by
  simpa using Ge.mul ha hb

/- English proof (translation)
The claim follows from `(le_of_eq WithTop.coe_one).trans V.v_l.symm.le`.
-/
theorem ge_l : V.Ge 1 (V.l : C) := (le_of_eq WithTop.coe_one).trans V.v_l.symm.le

/- English proof (translation)
Introduce `h`. Establish `h1` using `V.v_l`. Rewrite `h1` using `[h, AddValuation.map_zero]`. Simplify using `at h1`.
-/
theorem l_ne_zero : (V.l : C) ≠ 0 := by
  intro h
  have h1 := V.v_l
  rw [h, AddValuation.map_zero] at h1
  simp at h1

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => rw [Nat.cast_zero]`. Conclude with `Ge.zero 0`. Consider the case `succ n ih => rw [Nat.cast_succ]`. Conclude with `Ge.add ih Ge.one`.
-/
theorem ge_natCast (n : ℕ) : V.Ge 0 (n : C) := by
  induction n with
  | zero => rw [Nat.cast_zero]; exact Ge.zero 0
  | succ n ih => rw [Nat.cast_succ]; exact Ge.add ih Ge.one

/- English proof (translation)
Establish `h0 : ((w : ℝ) : WithTop ℝ) ≤ 1 + V.v a`. Establish `h2 : ((w : ℝ) : WithTop ℝ) ≤ V.v ((V.l : C) * a)` using `h`. Rewrite `h2` using `[AddValuation.map_mul, V.v_l]`. Then use the resulting hypothesis. Use `show (((w - 1) : ℝ) : WithTop ℝ) ≤ V.v a`. Distinguish the cases in `hva : V.v a = ⊤`.

Rewrite using `[hva]`. Conclude with `le_top`. Take `⟨x, hx⟩` from `WithTop.ne_top_iff_exists.mp hva`. Rewrite `h0`, the goal using `[← hx]`. Establish `h' : w ≤ 1 + x` using `by exact_mod_cast h0`.

Conclude with `WithTop.coe_le_coe.mpr (by linarith)`.
-/
theorem Ge.of_l_mul {w : ℝ} {a : C} (h : V.Ge w ((V.l : C) * a)) : V.Ge (w - 1) a := by
  have h0 : ((w : ℝ) : WithTop ℝ) ≤ 1 + V.v a := by
    have h2 : ((w : ℝ) : WithTop ℝ) ≤ V.v ((V.l : C) * a) := h
    rwa [AddValuation.map_mul, V.v_l] at h2
  show (((w - 1) : ℝ) : WithTop ℝ) ≤ V.v a
  by_cases hva : V.v a = ⊤
  · rw [hva]; exact le_top
  · obtain ⟨x, hx⟩ := WithTop.ne_top_iff_exists.mp hva
    rw [← hx] at h0 ⊢
    have h' : w ≤ 1 + x := by exact_mod_cast h0
    exact WithTop.coe_le_coe.mpr (by linarith)

/- English proof (translation)
Use `show ((1 + w : ℝ) : WithTop ℝ) ≤ V.v ((V.l : C) * a)`. Rewrite using `[AddValuation.map_mul, V.v_l, WithTop.coe_add, WithTop.coe_one]`. Conclude with `add_le_add le_rfl h`.
-/
theorem Ge.l_mul {w : ℝ} {a : C} (h : V.Ge w a) : V.Ge (1 + w) ((V.l : C) * a) := by
  show ((1 + w : ℝ) : WithTop ℝ) ≤ V.v ((V.l : C) * a)
  rw [AddValuation.map_mul, V.v_l, WithTop.coe_add, WithTop.coe_one]
  exact add_le_add le_rfl h

/- English proof (translation)
Apply `Ge.of_l_mul` to reduce the goal to its premises. Rewrite using `[← mul_assoc, mul_inv_cancel₀ l_ne_zero, one_mul]` and apply the resulting hypothesis.
-/
theorem Ge.l_inv_mul {w : ℝ} {a : C} (h : V.Ge w a) : V.Ge (w - 1) ((V.l : C)⁻¹ * a) := by
  apply Ge.of_l_mul
  rwa [← mul_assoc, mul_inv_cancel₀ l_ne_zero, one_mul]

end VF

section Ops

variable {N : Type*}

def teich (l : ℕ) (c : C) (x : ℕ → N → C) : ℕ → N → C := fun i n => c ^ (l ^ i) * x i n

def Vpow (s : ℕ) (x : ℕ → N → C) : ℕ → N → C := fun i n => if i < s then 0 else x (i - s) n

def Fs (l : ℕ) (x : ℕ → N → C) : ℕ → N → C := fun i n => (l : C) * x (i + 1) n

def sumV (y : ℕ → ℕ → N → C) : ℕ → N → C := fun i n => ∑ s ∈ range (i + 1), y s (i - s) n

def const0 (h : N → C) : ℕ → N → C := fun i n => if i = 0 then h n else 0

end Ops

structure Cart (V : VF C) (d : ℕ) (I J : Type*) where

  ty : I ⊕ J → ZMod d
  Ty : AddSubgroup (ℕ → I ⊕ J → C)
  teich_mem : ∀ c, V.Ge 0 c → ∀ x ∈ Ty, teich V.l c x ∈ Ty
  V_mem : ∀ x ∈ Ty, Vpow 1 x ∈ Ty
  F_mem : ∀ x ∈ Ty, Fs V.l x ∈ Ty
  sumV_mem : ∀ y : ℕ → ℕ → I ⊕ J → C, (∀ s, y s ∈ Ty) → sumV y ∈ Ty

  t2 : ∀ x ∈ Ty, ∀ s, (∀ i < s, x i = 0) → ∀ n, V.Ge 0 (x s n)

  t3 : ∀ ζ : J → C, (∀ j, V.Ge 0 (ζ j)) → const0 (Sum.elim 0 ζ) ∈ Ty

  t4 : ∀ (a : ZMod d) (u : I → C), (∀ c, V.Ge 0 (u c)) → (∀ c, ty (Sum.inl c) ≠ a → u c = 0) →
    ∃ x ∈ Ty, x 0 = Sum.elim u 0 ∧ ∀ (i : ℕ) n, ty n ≠ a + i → x i n = 0

end

end Formalism.L2.FormalSeriesBounds
