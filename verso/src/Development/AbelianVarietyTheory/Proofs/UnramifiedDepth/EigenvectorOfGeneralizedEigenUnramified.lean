import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.GeNatCast

open scoped BigOperators TensorProduct
open Formalism.L2.FormalSeriesBounds

namespace GlobalTheory.GenEigen

/- English proof (translation)
Establish `hpow : ∀ (j : ℕ) b, u ^ j * b ∈ J → b ∈ J`. Introduce `j`. Proceed by induction on `j with`. Consider the case `zero => intro b hb`. Simplify using `using hb`.

Consider the case `succ j ih`. Introduce `b hb`. Apply `hu` to reduce the goal to its premises. Apply `ih` to reduce the goal to its premises. Rewrite using `[← mul_assoc, ← pow_succ]` and apply the resulting hypothesis.

Take `⟨c, hc⟩` from `sub_dvd_pow_sub_pow u (-N) k`. Apply `hpow k` to reduce the goal to its premises. Establish `e : u ^ k * y = c * ((u + N) * y) + ((-1) ^ k * y) * N ^ k`. Establish `: u ^ k = (u - -N) * c + (-N) ^ k` using `by rw [← hc]; ring`. Rewrite using `[this, neg_pow N]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `J.add_mem (J.mul_mem_left _ h) (J.mul_mem_left _ hN)`.
-/
theorem mem_of_add_nil {B : Type*} [CommRing B] (J : Ideal B) (u N y : B)
    (hu : ∀ b, u * b ∈ J → b ∈ J) (k : ℕ) (hN : N ^ k ∈ J) (h : (u + N) * y ∈ J) : y ∈ J := by
  have hpow : ∀ (j : ℕ) b, u ^ j * b ∈ J → b ∈ J := by
    intro j
    induction j with
    | zero => intro b hb; simpa using hb
    | succ j ih =>
      intro b hb
      apply hu
      apply ih
      rwa [← mul_assoc, ← pow_succ]
  obtain ⟨c, hc⟩ := sub_dvd_pow_sub_pow u (-N) k
  apply hpow k
  have e : u ^ k * y = c * ((u + N) * y) + ((-1) ^ k * y) * N ^ k := by
    have : u ^ k = (u - -N) * c + (-N) ^ k := by rw [← hc]; ring
    rw [this, neg_pow N]; ring
  rw [e]
  exact J.add_mem (J.mul_mem_left _ h) (J.mul_mem_left _ hN)

/- English proof (translation)
Establish `hε : a ε - p ε ∈ J`. Take `⟨y, hy⟩` from `h1`. Take `⟨k, hk⟩` from `hnil ε`. Establish `ha : a ε * a ε - a ε = l * a y` using `by simpa using congrArg a hy`. Establish `hp : p ε * p ε - p ε = l * p y` using `by simpa using congrArg p hy`.

Use `mem_of_add_nil J (2 * p ε - 1) (a ε - p ε) _ ?_ k hk ?_` and prove the remaining obligations. Introduce `b hb`. Apply `hreg (4 * y)` to reduce the goal to its premises. Establish `: p (1 + l * (4 * y)) * b = (2 * p ε - 1) * ((2 * p ε - 1) * b)`. Simplify using `only [map_add, map_mul, map_one, map_natCast, map_ofNat]`.

Take the linear combination `(-4 * b) * hp`. Rewrite using `[this]`. Conclude with `J.mul_mem_left _ hb`. Establish `: (2 * p ε - 1 + (a ε - p ε)) * (a ε - p ε) = l * (a y - p y)`. Take the linear combination `ha - hp`.

Rewrite using `[this]`. Conclude with `hS y`. Establish `ht : (a x ^ (l ^ d) - a x) - (p x ^ (l ^ d) - p x) ∈ J`. Take `⟨y, hy⟩` from `h2 x`. Take `⟨n, hn⟩` from `hlim`.

Establish `ha : a ε * (a x ^ (l ^ d) - a x) = l * a y` using `by simpa using congrArg a hy`. Establish `hp : p ε * (p x ^ (l ^ d) - p x) = l * p y` using `by simpa using congrArg p hy`. Use `set s := a x ^ (l ^ d) - a x`. Use `set t := p x ^ (l ^ d) - p x`. Establish `h3 : a ε * (s - t) ∈ J`.

Establish `: a ε * (s - t) = l * (a y - p y) - t * (a ε - p ε)`. Take the linear combination `ha - hp`. Rewrite using `[this]`. Conclude with `J.sub_mem (hS y) (J.mul_mem_left _ hε)`. Take `⟨j, hj⟩ : ∃ j, l ^ n = j + 1` from `⟨l ^ n - 1, by have := pow_pos hl n; omega⟩`.

Rewrite `hn` using `[hj, map_pow]`. Establish `: s - t = (s - t) * (1 - a ε ^ (j + 1)) + a ε ^ j * (a ε * (s - t))` using `by ring`. Rewrite using `[this]`. Conclude with `J.add_mem (J.mul_mem_left _ hn) (J.mul_mem_left _ h3)`. Take `⟨H, hH⟩` from `Polynomial.powAddExpansion (p x) (a x - p x) (l ^ d)`.

Take `⟨k, hk⟩` from `hnil x`. Take `⟨d', rfl⟩ : ∃ d', d = d' + 1` from `⟨d - 1, by omega⟩`. Use `mem_of_add_nil J (((l ^ (d' + 1) : ℕ) : B) * p x ^ (l ^ (d' + 1) - 1) - 1) (H * (a x - p x)) _ ?_ k ?_ ?_` and prove the remaining obligations. Introduce `b hb`. Apply `hreg (-((l : O) ^ d' * x ^ (l ^ (d' + 1) - 1)))` to reduce the goal to its premises.

Establish `: p (1 + l * (-((l : O) ^ d' * x ^ (l ^ (d' + 1) - 1)))) * b = -((((l ^ (d' + 1) : ℕ) : B) * p x ^ (l ^ (d' + 1) - 1) - 1) * b)`. Simplify using `only [map_add, map_mul, map_one, map_natCast, map_neg, map_pow, Nat.cast_pow]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `J.neg_mem hb`.

Rewrite using `[mul_pow]`. Conclude with `J.mul_mem_left _ hk`. Establish `e : p x + (a x - p x) = a x` using `by ring`. Rewrite `hH` using `[e]`. Establish `: (((l ^ (d' + 1) : ℕ) : B) * p x ^ (l ^ (d' + 1) - 1) - 1 + H * (a x - p x)) * (a x - p x) = (a x ^ (l ^ (d' + 1)) - a x) - (p x ^ (l ^ (d' + 1)) - p x)`.

Rewrite using `[hH]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `ht`.
-/
theorem step {O B : Type*} [CommRing O] [CommRing B] (a p : O →+* B) (J : Ideal B)
    (l d : ℕ) (hl : 0 < l) (hd : 0 < d) (ε : O)
    (h1 : ∃ y, ε * ε - ε = (l : O) * y)
    (h2 : ∀ x : O, ∃ y, ε * (x ^ (l ^ d) - x) = (l : O) * y)
    (hS : ∀ y, (l : B) * (a y - p y) ∈ J)
    (hreg : ∀ (e : O) b, p (1 + l * e) * b ∈ J → b ∈ J)
    (hnil : ∀ x, ∃ k : ℕ, (a x - p x) ^ k ∈ J)
    (hlim : ∃ n : ℕ, 1 - a (ε ^ (l ^ n)) ∈ J) (x : O) : a x - p x ∈ J := by
  have hε : a ε - p ε ∈ J := by
    obtain ⟨y, hy⟩ := h1
    obtain ⟨k, hk⟩ := hnil ε
    have ha : a ε * a ε - a ε = l * a y := by simpa using congrArg a hy
    have hp : p ε * p ε - p ε = l * p y := by simpa using congrArg p hy
    refine mem_of_add_nil J (2 * p ε - 1) (a ε - p ε) _ ?_ k hk ?_
    · intro b hb
      apply hreg (4 * y)
      have : p (1 + l * (4 * y)) * b = (2 * p ε - 1) * ((2 * p ε - 1) * b) := by
        simp only [map_add, map_mul, map_one, map_natCast, map_ofNat]
        linear_combination (-4 * b) * hp
      rw [this]
      exact J.mul_mem_left _ hb
    · have : (2 * p ε - 1 + (a ε - p ε)) * (a ε - p ε) = l * (a y - p y) := by
        linear_combination ha - hp
      rw [this]
      exact hS y
  have ht : (a x ^ (l ^ d) - a x) - (p x ^ (l ^ d) - p x) ∈ J := by
    obtain ⟨y, hy⟩ := h2 x
    obtain ⟨n, hn⟩ := hlim
    have ha : a ε * (a x ^ (l ^ d) - a x) = l * a y := by simpa using congrArg a hy
    have hp : p ε * (p x ^ (l ^ d) - p x) = l * p y := by simpa using congrArg p hy
    set s := a x ^ (l ^ d) - a x
    set t := p x ^ (l ^ d) - p x
    have h3 : a ε * (s - t) ∈ J := by
      have : a ε * (s - t) = l * (a y - p y) - t * (a ε - p ε) := by
        linear_combination ha - hp
      rw [this]
      exact J.sub_mem (hS y) (J.mul_mem_left _ hε)
    obtain ⟨j, hj⟩ : ∃ j, l ^ n = j + 1 := ⟨l ^ n - 1, by have := pow_pos hl n; omega⟩
    rw [hj, map_pow] at hn
    have : s - t = (s - t) * (1 - a ε ^ (j + 1)) + a ε ^ j * (a ε * (s - t)) := by ring
    rw [this]
    exact J.add_mem (J.mul_mem_left _ hn) (J.mul_mem_left _ h3)
  obtain ⟨H, hH⟩ := Polynomial.powAddExpansion (p x) (a x - p x) (l ^ d)
  obtain ⟨k, hk⟩ := hnil x
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  refine mem_of_add_nil J (((l ^ (d' + 1) : ℕ) : B) * p x ^ (l ^ (d' + 1) - 1) - 1)
    (H * (a x - p x)) _ ?_ k ?_ ?_
  · intro b hb
    apply hreg (-((l : O) ^ d' * x ^ (l ^ (d' + 1) - 1)))
    have : p (1 + l * (-((l : O) ^ d' * x ^ (l ^ (d' + 1) - 1)))) * b =
        -((((l ^ (d' + 1) : ℕ) : B) * p x ^ (l ^ (d' + 1) - 1) - 1) * b) := by
      simp only [map_add, map_mul, map_one, map_natCast, map_neg, map_pow, Nat.cast_pow]
      ring
    rw [this]
    exact J.neg_mem hb
  · rw [mul_pow]; exact J.mul_mem_left _ hk
  · have e : p x + (a x - p x) = a x := by ring
    rw [e] at hH
    have : (((l ^ (d' + 1) : ℕ) : B) * p x ^ (l ^ (d' + 1) - 1) - 1 + H * (a x - p x)) * (a x - p x)
        = (a x ^ (l ^ (d' + 1)) - a x) - (p x ^ (l ^ (d' + 1)) - p x) := by
      rw [hH]; ring
    rw [this]
    exact ht

variable {C : Type} [Field C] {V : VF C}

/- English proof (translation)
Establish `h0 : V.v (1 + e) = 0`. Establish `: V.v 1 < V.v e`. Rewrite using `[V.v.map_one]`. Conclude with `lt_of_lt_of_le (by exact_mod_cast (zero_lt_one : (0 : ℝ) < 1)) he`. Rewrite using `[V.v.map_add_eq_of_lt_left this, V.v.map_one]`.

Unfold `VF.Ge at h ⊢`. Rewrite `h` using `[V.v.map_mul, h0, zero_add]`. Then use the resulting hypothesis.
-/
theorem ge_of_one_add_mul {e z : C} {m : ℝ} (he : V.Ge 1 e) (h : V.Ge m ((1 + e) * z)) :
    V.Ge m z := by
  have h0 : V.v (1 + e) = 0 := by
    have : V.v 1 < V.v e := by
      rw [V.v.map_one]
      exact lt_of_lt_of_le (by exact_mod_cast (zero_lt_one : (0 : ℝ) < 1)) he
    rw [V.v.map_add_eq_of_lt_left this, V.v.map_one]
  unfold VF.Ge at h ⊢
  rwa [V.v.map_mul, h0, zero_add] at h

/- English proof (translation)
Unfold `VF.Ge`. Proceed by induction on `V.v z using WithTop.recTopCoe with`. Consider the case `top => exact ⟨0, le_top⟩`. Consider the case `coe t => exact ⟨t, le_rfl⟩`.
-/
theorem exists_ge (z : C) : ∃ m : ℝ, V.Ge m z := by
  unfold VF.Ge
  induction V.v z using WithTop.recTopCoe with
  | top => exact ⟨0, le_top⟩
  | coe t => exact ⟨t, le_rfl⟩

/- English proof (translation)
Assume the negation of the conclusion as `hz`. Establish `hne : V.v z ≠ ⊤`. Introduce `ht`. Establish `h1 : V.v (z * z⁻¹) = ⊤` using `by rw [V.v.map_mul, ht, top_add]`. Rewrite `h1` using `[mul_inv_cancel₀ hz, V.v.map_one]`.

Conclude with `WithTop.zero_ne_top h1`. Take `⟨t, ht⟩` from `WithTop.ne_top_iff_exists.mp hne`. Take `⟨k, hk⟩` from `exists_nat_gt (t - m)`. Use `h k` as an intermediate fact. Unfold `VF.Ge at this`.

Rewrite `this` using `[← ht]`. Establish `: m + k ≤ t` using `by exact_mod_cast this`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem eq_zero_of_forall_ge {z : C} (m : ℝ) (h : ∀ k : ℕ, V.Ge (m + k) z) : z = 0 := by
  by_contra hz
  have hne : V.v z ≠ ⊤ := by
    intro ht
    have h1 : V.v (z * z⁻¹) = ⊤ := by rw [V.v.map_mul, ht, top_add]
    rw [mul_inv_cancel₀ hz, V.v.map_one] at h1
    exact WithTop.zero_ne_top h1
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp hne
  obtain ⟨k, hk⟩ := exists_nat_gt (t - m)
  have := h k
  unfold VF.Ge at this
  rw [← ht] at this
  have : m + k ≤ t := by exact_mod_cast this
  linarith

/- English proof (translation)
The claim follows from `VF.Ge.sum fun j _ => (hM i j).mul_int (hz j)`.
-/
theorem ge_mulVec {κ : Type} [Fintype κ] {M : Matrix κ κ C} (hM : ∀ i j, V.Ge 0 (M i j))
    {z : κ → C} {m : ℝ} (hz : ∀ i, V.Ge m (z i)) (i : κ) : V.Ge m (M.mulVec z i) :=
  VF.Ge.sum fun j _ => (hM i j).mul_int (hz j)

def levelIdeal {κ : Type} [Fintype κ] [DecidableEq κ] {B : Type} [CommRing B]
    (Φ : B →+* Matrix κ κ C) (hΦ : ∀ b i j, V.Ge 0 (Φ b i j)) (w : κ → C) (m : ℝ) : Ideal B where
  carrier := {b | ∀ i, V.Ge m ((Φ b).mulVec w i)}
  add_mem' := by
    intro a b ha hb i
    rw [map_add, Matrix.add_mulVec]
    exact (ha i).add (hb i)
  zero_mem' := by
    intro i
    rw [map_zero, Matrix.zero_mulVec]
    exact VF.Ge.zero m
  smul_mem' := by
    intro c b hb i
    rw [smul_eq_mul, map_mul, ← Matrix.mulVec_mulVec]
    exact ge_mulVec (hΦ c) hb i

/- English proof (translation)
Set `P : O →+* Matrix κ κ C` to `(algebraMap C (Matrix κ κ C)).comp ψ`. Establish `hP : ∀ x, P x = ψ x • (1 : Matrix κ κ C)` using `fun x => Algebra.algebraMap_eq_smul_one (ψ x)`. Set `Φ : O ⊗[ℤ] O →+* Matrix κ κ C` to `(Algebra.TensorProduct.lift L.toIntAlgHom P.toIntAlgHom (fun x y => (Algebra.commutes (ψ y) (L x)).symm)).toRingHom`. Establish `hΦt : ∀ x y, Φ (x ⊗ₜ y) = ψ y • L x`. Introduce `x y`.

Express the relevant statement in the definitionally equal form `L x * P y = _`. Rewrite using `[hP, Matrix.mul_smul, mul_one]`. Establish `hΦ : ∀ b i j, V.Ge 0 (Φ b i j)`. Introduce `b`. Proceed by induction on `b using TensorProduct.induction_on with`.

Consider the case `zero => intro i j`. Rewrite using `[map_zero]`. Conclude with `VF.Ge.zero 0`. Consider the case `tmul x y => intro i j`. Rewrite using `[hΦt]`.

Conclude with `(hψ y).mul_int (hL x i j)`. Consider the case `add a b ha hb => intro i j`. Rewrite using `[map_add]`. Conclude with `(ha i j).add (hb i j)`. Set `a : O →+* O ⊗[ℤ] O` to `Algebra.TensorProduct.includeLeftRingHom`.

Set `p : O →+* O ⊗[ℤ] O` to `(Algebra.TensorProduct.includeRight : O →ₐ[ℤ] O ⊗[ℤ] O).toRingHom`. Establish `ha : ∀ x, Φ (a x) = L x` using `fun x => by`. Express the relevant statement in the definitionally equal form `Φ (x ⊗ₜ 1) = _`. Rewrite using `[hΦt, map_one, one_smul]`. Establish `hp : ∀ x, Φ (p x) = ψ x • (1 : Matrix κ κ C)` using `fun x => by`.

Express the relevant statement in the definitionally equal form `Φ (1 ⊗ₜ x) = _`. Rewrite using `[hΦt, map_one]`. Establish `mem : ∀ m b, b ∈ levelIdeal Φ hΦ w m ↔ ∀ i, V.Ge m ((Φ b).mulVec w i)` using `fun _ _ => Iff.rfl`. Take `⟨m0, hm0⟩ : ∃ m0 : ℝ, ∀ i, V.Ge m0 (w i)` from `by choose f hf using fun i => exists_ge (V := V) (w i)`. Take `⟨m0, hm0⟩` from `(Set.finite_range f).bddBelow`.

Conclude with `⟨m0, fun i => (hf i).mono (hm0 ⟨i, rfl⟩)⟩`. Establish `key : ∀ (k : ℕ) y, a y - p y ∈ levelIdeal Φ hΦ w (m0 + k)`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`.

Introduce `y`. Rewrite using `[mem]`. Rewrite using `[Nat.cast_zero, add_zero]`. Conclude with `ge_mulVec (hΦ _) hm0`. Consider the case `succ k ih`.

Use `step a p _ V.l d V.l_prime.pos hd ε h1 h2 ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `y`. Rewrite using `[mem]`. Introduce `i`. Use `((mem _ _).1 (ih y) i).l_mul` as an intermediate fact.

Rewrite using `[map_mul, map_natCast, ← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul C, Matrix.smul_mulVec]`. Conclude with `this.mono (by push_cast; linarith)`. Introduce `e b hb`. Rewrite `hb`, the goal using `[mem]`. Introduce `i`.

Use `hb i` as an intermediate fact. Rewrite `this` using `[map_mul, hp, Matrix.smul_mul, one_mul, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul, map_add, map_one, map_mul, map_natCast]`. Conclude with `ge_of_one_add_mul (by simpa using (hψ e).l_mul) this`. Introduce `y`. Take `⟨j, hj⟩` from `hnil y`.

Use `⟨j, (mem _ _).2 fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[map_pow, map_sub, ha, hp, hj]`. Conclude with `VF.Ge.zero _`. Take `⟨N, hN⟩` from `exists_nat_ge (m0 + (k + 1 : ℕ)) choose f hf using hlim N`. Take `⟨n, hn⟩` from `(Set.finite_range f).bddAbove`.

Use `⟨n, (mem _ _).2 fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[map_sub, map_one, ha, Matrix.sub_mulVec, Matrix.one_mulVec]`. Conclude with `(hf i n (hn ⟨i, rfl⟩)).mono hN`. Use function extensionality and compare the values at `i`. Use `eq_zero_of_forall_ge (V := V) m0 fun k => (mem _ _).1 (key k x) i` as an intermediate fact.

Rewrite `this` using `[map_sub, ha, hp, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Pi.sub_apply]`. Conclude with `sub_eq_zero.mp this`.
-/
theorem eigen_of_gen_eigen (C : Type) [Field C] (V : VF C) (O : Type) [CommRing O] (κ : Type)
    [Fintype κ] [DecidableEq κ] (L : O →+* Matrix κ κ C) (hL : ∀ x i j, V.Ge 0 (L x i j))
    (d : ℕ) (hd : 0 < d) (ε : O) (h1 : ∃ y, ε * ε - ε = (V.l : O) * y)
    (h2 : ∀ x : O, ∃ y, ε * (x ^ (V.l ^ d) - x) = (V.l : O) * y) (ψ : O →+* C) (w : κ → C)
    (hψ : ∀ x, V.Ge 0 (ψ x))
    (hnil : ∀ x, ∃ k : ℕ, ((L x - ψ x • (1 : Matrix κ κ C)) ^ k).mulVec w = 0)
    (hlim : ∀ (N : ℕ) i, ∃ n0 : ℕ, ∀ n ≥ n0, V.Ge N (w i - (L (ε ^ (V.l ^ n))).mulVec w i))
    (x : O) : (L x).mulVec w = ψ x • w := by
  let P : O →+* Matrix κ κ C := (algebraMap C (Matrix κ κ C)).comp ψ
  have hP : ∀ x, P x = ψ x • (1 : Matrix κ κ C) := fun x => Algebra.algebraMap_eq_smul_one (ψ x)
  let Φ : O ⊗[ℤ] O →+* Matrix κ κ C :=
    (Algebra.TensorProduct.lift L.toIntAlgHom P.toIntAlgHom
      (fun x y => (Algebra.commutes (ψ y) (L x)).symm)).toRingHom
  have hΦt : ∀ x y, Φ (x ⊗ₜ y) = ψ y • L x := by
    intro x y
    change L x * P y = _
    rw [hP, Matrix.mul_smul, mul_one]
  have hΦ : ∀ b i j, V.Ge 0 (Φ b i j) := by
    intro b
    induction b using TensorProduct.induction_on with
    | zero => intro i j; rw [map_zero]; exact VF.Ge.zero 0
    | tmul x y => intro i j; rw [hΦt]; exact (hψ y).mul_int (hL x i j)
    | add a b ha hb => intro i j; rw [map_add]; exact (ha i j).add (hb i j)
  let a : O →+* O ⊗[ℤ] O := Algebra.TensorProduct.includeLeftRingHom
  let p : O →+* O ⊗[ℤ] O := (Algebra.TensorProduct.includeRight : O →ₐ[ℤ] O ⊗[ℤ] O).toRingHom
  have ha : ∀ x, Φ (a x) = L x := fun x => by
    change Φ (x ⊗ₜ 1) = _
    rw [hΦt, map_one, one_smul]
  have hp : ∀ x, Φ (p x) = ψ x • (1 : Matrix κ κ C) := fun x => by
    change Φ (1 ⊗ₜ x) = _
    rw [hΦt, map_one]
  have mem : ∀ m b, b ∈ levelIdeal Φ hΦ w m ↔ ∀ i, V.Ge m ((Φ b).mulVec w i) :=
    fun _ _ => Iff.rfl
  obtain ⟨m0, hm0⟩ : ∃ m0 : ℝ, ∀ i, V.Ge m0 (w i) := by
    choose f hf using fun i => exists_ge (V := V) (w i)
    obtain ⟨m0, hm0⟩ := (Set.finite_range f).bddBelow
    exact ⟨m0, fun i => (hf i).mono (hm0 ⟨i, rfl⟩)⟩
  have key : ∀ (k : ℕ) y, a y - p y ∈ levelIdeal Φ hΦ w (m0 + k) := by
    intro k
    induction k with
    | zero =>
      intro y
      rw [mem]
      rw [Nat.cast_zero, add_zero]
      exact ge_mulVec (hΦ _) hm0
    | succ k ih =>
      refine step a p _ V.l d V.l_prime.pos hd ε h1 h2 ?_ ?_ ?_ ?_
      · intro y
        rw [mem]
        intro i
        have := ((mem _ _).1 (ih y) i).l_mul
        rw [map_mul, map_natCast, ← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul C, Matrix.smul_mulVec]
        exact this.mono (by push_cast; linarith)
      · intro e b hb
        rw [mem] at hb ⊢
        intro i
        have := hb i
        rw [map_mul, hp, Matrix.smul_mul, one_mul, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul,
          map_add, map_one, map_mul, map_natCast] at this
        exact ge_of_one_add_mul (by simpa using (hψ e).l_mul) this
      · intro y
        obtain ⟨j, hj⟩ := hnil y
        refine ⟨j, (mem _ _).2 fun i => ?_⟩
        rw [map_pow, map_sub, ha, hp, hj]
        exact VF.Ge.zero _
      · obtain ⟨N, hN⟩ := exists_nat_ge (m0 + (k + 1 : ℕ))
        choose f hf using hlim N
        obtain ⟨n, hn⟩ := (Set.finite_range f).bddAbove
        refine ⟨n, (mem _ _).2 fun i => ?_⟩
        rw [map_sub, map_one, ha, Matrix.sub_mulVec, Matrix.one_mulVec]
        exact (hf i n (hn ⟨i, rfl⟩)).mono hN
  funext i
  have := eq_zero_of_forall_ge (V := V) m0 fun k => (mem _ _).1 (key k x) i
  rw [map_sub, ha, hp, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    Pi.sub_apply] at this
  exact sub_eq_zero.mp this

end GlobalTheory.GenEigen
