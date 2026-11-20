import Mathlib

namespace GlobalTheory.MultiplierOrders

/- English proof (translation)
Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy => exact ⟨1, one_pos, by rw [one_smul]; exact Submodule.subset_span hy⟩`. Consider the case `zero => exact ⟨1, one_pos, by rw [smul_zero]; exact Submodule.zero_mem _⟩`. Consider the case `add y z _ _ hy hz`. Take `⟨m, hm, hy⟩` from `hy`.

Take `⟨n, hn, hz⟩` from `hz`. Use `⟨m * n, Nat.mul_pos hm hn, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_add]`. Use `Submodule.add_mem _ ?_ ?_` and prove the remaining obligations. Rewrite using `[mul_comm, mul_smul]`.

Conclude with `nsmul_mem hy n`. Rewrite using `[mul_smul]`. Conclude with `nsmul_mem hz m`. Consider the case `smul q y _ hy`. Take `⟨m, hm, hy⟩` from `hy`.

Use `⟨m * q.den, Nat.mul_pos hm q.den_pos, ?_⟩` and prove the remaining obligations. Establish `h : (m * q.den) • q • y = q.num • m • y`. Rewrite using `[← Nat.cast_smul_eq_nsmul ℚ, ← Nat.cast_smul_eq_nsmul ℚ m, ← Int.cast_smul_eq_zsmul ℚ, smul_smul, smul_smul]`. Use `congr 1`. Use `push_cast`.

Rewrite using `[mul_assoc, Rat.den_mul_eq_num, mul_comm]`. Rewrite using `[h]`. Conclude with `Submodule.smul_mem _ _ hy`.
-/
theorem exists_nsmul_mem_span {C : Type} [AddCommGroup C] [Module ℚ C] (S : Set C) (x : C)
    (hx : x ∈ Submodule.span ℚ S) : ∃ m : ℕ, 0 < m ∧ m • x ∈ Submodule.span ℤ S := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_pos, by rw [one_smul]; exact Submodule.subset_span hy⟩
  | zero => exact ⟨1, one_pos, by rw [smul_zero]; exact Submodule.zero_mem _⟩
  | add y z _ _ hy hz =>
    obtain ⟨m, hm, hy⟩ := hy
    obtain ⟨n, hn, hz⟩ := hz
    refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
    rw [smul_add]
    refine Submodule.add_mem _ ?_ ?_
    · rw [mul_comm, mul_smul]
      exact nsmul_mem hy n
    · rw [mul_smul]
      exact nsmul_mem hz m
  | smul q y _ hy =>
    obtain ⟨m, hm, hy⟩ := hy
    refine ⟨m * q.den, Nat.mul_pos hm q.den_pos, ?_⟩
    have h : (m * q.den) • q • y = q.num • m • y := by
      rw [← Nat.cast_smul_eq_nsmul ℚ, ← Nat.cast_smul_eq_nsmul ℚ m, ← Int.cast_smul_eq_zsmul ℚ,
        smul_smul, smul_smul]
      congr 1
      push_cast
      rw [mul_assoc, Rat.den_mul_eq_num, mul_comm]
    rw [h]
    exact Submodule.smul_mem _ _ hy

def multipliers {C : Type} [Ring C] (L : Submodule ℤ C) : Subring C where
  carrier := {x | ∀ y ∈ L, x * y ∈ L}
  mul_mem' := fun {a b} ha hb y hy => by
    rw [mul_assoc]; exact ha _ (hb y hy)
  one_mem' := fun y hy => by rw [one_mul]; exact hy
  add_mem' := fun {a b} ha hb y hy => by
    rw [add_mul]; exact L.add_mem (ha y hy) (hb y hy)
  zero_mem' := fun y _ => by rw [zero_mul]; exact L.zero_mem
  neg_mem' := fun {a} ha y hy => by
    rw [neg_mul]; exact L.neg_mem (ha y hy)

/- English proof (translation)
Take `⟨S, hS⟩` from `Module.Finite.fg_top (R := ℚ) (M := C)`. Establish `key : ∀ x : C, ∃ m : ℕ, 0 < m ∧ m • x ∈ Submodule.span ℤ (S : Set C)` using `fun x => exists_nsmul_mem_span _ x (by rw [hS]; exact Submodule.mem_top)`. Use `set L : Submodule ℤ C := Submodule.span ℤ (S : Set C) with hL`. Use `haveI : Module.Finite ℤ L := Module.Finite.iff_fg.mpr ⟨S, rfl⟩`. Use `⟨multipliers L, ?_, ?_⟩` and prove the remaining obligations.

Take `⟨m, hm, h1⟩` from `key 1`. Set `f : multipliers L →+ L` to `{ toFun := fun x => ⟨x.1 * (m • (1 : C)), x.2 _ h1⟩ map_zero' := Subtype.ext (by simp) map_add' := fun a b => Subtype.ext (by simp [add_mul]) }`. Use `Module.Finite.of_injective f.toIntLinearMap ?_` and prove the remaining obligations. Introduce `a b hab`. Establish `h : a.1 * (m • (1 : C)) = b.1 * (m • (1 : C))` using `congrArg Subtype.val hab`.

Rewrite `h` using `[mul_smul_comm, mul_smul_comm, mul_one, mul_one, ← Nat.cast_smul_eq_nsmul ℚ, ← Nat.cast_smul_eq_nsmul ℚ]`. Establish `hm' : (m : ℚ) ≠ 0` using `Nat.cast_ne_zero.mpr hm.ne'`. Conclude with `Subtype.ext (smul_right_injective C hm' h)`. Introduce `b choose n hn hmem using fun s : C => key (b * s)`. Use `⟨∏ s ∈ S, n s, Finset.prod_pos fun s _ => hn s, ?_⟩` and prove the remaining obligations.

Introduce `y hy`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem s hs`. Establish `hs' : s ∈ S` using `hs`. Rewrite using `[mul_assoc, ← nsmul_eq_mul, ← Finset.prod_erase_mul S n hs', mul_smul]`.

Conclude with `nsmul_mem (hmem s) _`. Consider the case `zero => rw [mul_zero]`. Conclude with `L.zero_mem`. Consider the case `add y z _ _ hy hz => rw [mul_add]`. Conclude with `L.add_mem hy hz`.

Consider the case `smul k y _ hy => rw [mul_smul_comm]`. Conclude with `L.smul_mem k hy`.
-/
theorem exists_order (C : Type) [Ring C] [Algebra ℚ C] [FiniteDimensional ℚ C] :
    ∃ OB : Subring C, Module.Finite ℤ OB ∧ ∀ b : C, ∃ m : ℕ, 0 < m ∧ (m : C) * b ∈ OB := by
  classical
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := ℚ) (M := C)
  have key : ∀ x : C, ∃ m : ℕ, 0 < m ∧ m • x ∈ Submodule.span ℤ (S : Set C) := fun x =>
    exists_nsmul_mem_span _ x (by rw [hS]; exact Submodule.mem_top)
  set L : Submodule ℤ C := Submodule.span ℤ (S : Set C) with hL
  haveI : Module.Finite ℤ L := Module.Finite.iff_fg.mpr ⟨S, rfl⟩
  refine ⟨multipliers L, ?_, ?_⟩
  · obtain ⟨m, hm, h1⟩ := key 1
    let f : multipliers L →+ L :=
      { toFun := fun x => ⟨x.1 * (m • (1 : C)), x.2 _ h1⟩
        map_zero' := Subtype.ext (by simp)
        map_add' := fun a b => Subtype.ext (by simp [add_mul]) }
    refine Module.Finite.of_injective f.toIntLinearMap ?_
    intro a b hab
    have h : a.1 * (m • (1 : C)) = b.1 * (m • (1 : C)) := congrArg Subtype.val hab
    rw [mul_smul_comm, mul_smul_comm, mul_one, mul_one, ← Nat.cast_smul_eq_nsmul ℚ,
      ← Nat.cast_smul_eq_nsmul ℚ] at h
    have hm' : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
    exact Subtype.ext (smul_right_injective C hm' h)
  · intro b
    choose n hn hmem using fun s : C => key (b * s)
    refine ⟨∏ s ∈ S, n s, Finset.prod_pos fun s _ => hn s, ?_⟩
    intro y hy
    induction hy using Submodule.span_induction with
    | mem s hs =>
      have hs' : s ∈ S := hs
      rw [mul_assoc, ← nsmul_eq_mul, ← Finset.prod_erase_mul S n hs', mul_smul]
      exact nsmul_mem (hmem s) _
    | zero => rw [mul_zero]; exact L.zero_mem
    | add y z _ _ hy hz => rw [mul_add]; exact L.add_mem hy hz
    | smul k y _ hy => rw [mul_smul_comm]; exact L.smul_mem k hy

end GlobalTheory.MultiplierOrders
