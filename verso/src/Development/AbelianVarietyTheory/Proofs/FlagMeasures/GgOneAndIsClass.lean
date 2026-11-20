import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsMirClass

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory.GLq.GGDeg

variable {g : ℕ} [Fact g.Prime]

/- English proof (translation)
Rewrite using `[Matrix.isUnit_iff_isUnit_det, Matrix.det_of_upperTriangular (fun a b hab => (h a b).1 hab), Finset.prod_eq_one fun a _ => (h a a).2 rfl]`. Conclude with `isUnit_one`.
-/
theorem isUnit_of_isUniUp {n : ℕ} {M : Mt g n} (h : IsUniUp M) : IsUnit M := by
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_of_upperTriangular (fun a b hab => (h a b).1 hab),
    Finset.prod_eq_one fun a _ => (h a a).2 rfl]
  exact isUnit_one

/- English proof (translation)
Establish `h : (Finset.univ.filter fun M : Mt g n => IsUniUp M) = (Fintype.piFinset fun a : Fin n => Fintype.piFinset fun b : Fin n => (if a < b then Finset.univ else if a = b then {1} else {0} : Finset (ZMod g)) : Finset (Fin n → Fin n → ZMod g))`. Use extensionality with `M`. Rewrite using `[Finset.mem_filter, and_iff_right (Finset.mem_univ _)]`. Use `Iff.trans ?_ Fintype.mem_piFinset.symm` and prove the remaining obligations. Use `forall_congr' fun a => Iff.trans (forall_congr' fun b => ?_) Fintype.mem_piFinset.symm` and prove the remaining obligations.

Break down `lt_trichotomy a b with hab | hab | hab` into its components or cases. Simplify using `[hab, hab.ne, hab.not_gt]`. Substitute `hab` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hab, hab.ne', hab.not_gt]`.

Rewrite using `[h]`. Use `erw [Fintype.card_piFinset]`. Simplify using `only [Fintype.card_piFinset]`. Rewrite using `[Finset.prod_comm]`. Use `Finset.prod_congr rfl fun b _ => ?_` and prove the remaining obligations.

Establish `h2 : ∀ a : Fin n, (if a < b then Finset.univ else if a = b then {1} else {0} : Finset (ZMod g)).card = if a < b then g else 1`. Introduce `a`. Apply the tactic sequence `split_ifs <;> simp [ZMod.card]`. Simplify using `only [h2]`. Rewrite using `[Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]`.

Use `congr 1`. Rewrite using `[show (Finset.univ.filter fun a : Fin n => a < b) = Finset.Iio b by ext; simp]`. Simplify using the standard rewrite rules.
-/
theorem card_uniUp_mat (n : ℕ) :
    (Finset.univ.filter fun M : Mt g n => IsUniUp M).card = ∏ i : Fin n, g ^ (i : ℕ) := by
  have h : (Finset.univ.filter fun M : Mt g n => IsUniUp M) =
      (Fintype.piFinset fun a : Fin n => Fintype.piFinset fun b : Fin n =>
        (if a < b then Finset.univ else if a = b then {1} else {0} : Finset (ZMod g)) :
          Finset (Fin n → Fin n → ZMod g)) := by
    ext M
    rw [Finset.mem_filter, and_iff_right (Finset.mem_univ _)]
    refine Iff.trans ?_ Fintype.mem_piFinset.symm
    refine forall_congr' fun a => Iff.trans (forall_congr' fun b => ?_) Fintype.mem_piFinset.symm
    rcases lt_trichotomy a b with hab | hab | hab
    · simp [hab, hab.ne, hab.not_gt]
    · subst hab; simp
    · simp [hab, hab.ne', hab.not_gt]
  rw [h]
  erw [Fintype.card_piFinset]
  simp only [Fintype.card_piFinset]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun b _ => ?_
  have h2 : ∀ a : Fin n, (if a < b then Finset.univ else if a = b then {1} else {0} : Finset (ZMod g)).card =
      if a < b then g else 1 := by
    intro a
    split_ifs <;> simp [ZMod.card]
  simp only [h2]
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
  congr 1
  rw [show (Finset.univ.filter fun a : Fin n => a < b) = Finset.Iio b by ext; simp]
  simp

/- English proof (translation)
Rewrite using `[← card_uniUp_mat]`. Use `Finset.card_bij (fun u _ => (u : Mt g n)) ?_ ?_ ?_` and prove the remaining obligations. Introduce `u hu`. Simplify using `using hu`. Introduce `u _ v _ h`.

Conclude with `Units.ext h`. Introduce `M hM`. Establish `hM' : IsUniUp M` using `by simpa using hM`. Conclude with `⟨(isUnit_of_isUniUp hM').unit, by simpa using hM', rfl⟩`.
-/
theorem card_uniUp (n : ℕ) :
    (Finset.univ.filter fun u : Gn g n => IsUniUp (u : Mt g n)).card = ∏ i : Fin n, g ^ (i : ℕ) := by
  rw [← card_uniUp_mat]
  refine Finset.card_bij (fun u _ => (u : Mt g n)) ?_ ?_ ?_
  · intro u hu
    simpa using hu
  · intro u _ v _ h
    exact Units.ext h
  · intro M hM
    have hM' : IsUniUp M := by simpa using hM
    exact ⟨(isUnit_of_isUniUp hM').unit, by simpa using hM', rfl⟩

/- English proof (translation)
Establish `hg : 0 < g` using `(Fact.out : g.Prime).pos`. Rewrite using `[← Nat.card_eq_fintype_card, Matrix.card_GL_field, ZMod.card, Nat.cast_prod]`. Establish `h1 : ∏ i ∈ Finset.Icc 1 n, ((g : ℂ) ^ i - 1) = ∏ i : Fin n, ((g : ℂ) ^ (n - i) - 1)`. Rewrite using `[Fin.prod_univ_eq_prod_range (fun i => ((g : ℂ) ^ (n - i) - 1)) n]`. Apply the tactic sequence `refine Finset.prod_bij' (fun i _ => n - i) (fun i _ => n - i) ?_ ?_ ?_ ?_ ?_ <;>`.

Apply the tactic sequence `simp only [Finset.mem_Icc, Finset.mem_range] <;> intro i hi`. Use linear arithmetic over natural numbers and integers. Use linear arithmetic over natural numbers and integers. Use linear arithmetic over natural numbers and integers. Use linear arithmetic over natural numbers and integers.

Rewrite using `[show n - (n - i) = i by omega]`. Rewrite using `[h1, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Nat.cast_sub (Nat.pow_le_pow_right hg i.2.le), mul_sub, ← pow_add, show (i : ℕ) + (n - i) = n by have := i.2; omega]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem card_Gn (n : ℕ) : (Fintype.card (Gn g n) : ℂ) =
    (∏ i : Fin n, (g : ℂ) ^ (i : ℕ)) * ∏ i ∈ Finset.Icc 1 n, ((g : ℂ) ^ i - 1) := by
  have hg : 0 < g := (Fact.out : g.Prime).pos
  rw [← Nat.card_eq_fintype_card, Matrix.card_GL_field, ZMod.card, Nat.cast_prod]
  have h1 : ∏ i ∈ Finset.Icc 1 n, ((g : ℂ) ^ i - 1) = ∏ i : Fin n, ((g : ℂ) ^ (n - i) - 1) := by
    rw [Fin.prod_univ_eq_prod_range (fun i => ((g : ℂ) ^ (n - i) - 1)) n]
    refine Finset.prod_bij' (fun i _ => n - i) (fun i _ => n - i) ?_ ?_ ?_ ?_ ?_ <;>
      simp only [Finset.mem_Icc, Finset.mem_range] <;> intro i hi
    · omega
    · omega
    · omega
    · omega
    · rw [show n - (n - i) = i by omega]
  rw [h1, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Nat.cast_sub (Nat.pow_le_pow_right hg i.2.le), mul_sub, ← pow_add,
    show (i : ℕ) + (n - i) = n by have := i.2; omega]
  push_cast
  ring

/- English proof (translation)
Introduce `g _ ψ n`. Establish `hg : (g : ℂ) ≠ 0` using `Nat.cast_ne_zero.mpr (Fact.out : g.Prime).ne_zero`. Prove the components needed by the constructor for the conclusion. Establish `h1 : IsUniUp (1 : Mt g n)` using `fun a b => ⟨fun h => Matrix.one_apply_ne h.ne', fun h => h ▸ Matrix.one_apply_eq a⟩`. Establish `h2 : ∀ i, entN (1 : Mt g n) i (i + 1) = 0`.

Introduce `i`. Unfold `entN`. Use `split_ifs with h`. Conclude with `Matrix.one_apply_ne (by simp)`. Both sides reduce to the same expression.

Unfold `gg`. Simplify using `only [mul_one, inv_mul_cancel, Units.val_one, h1, if_true, h2, Finset.sum_const_zero, AddChar.map_zero_eq_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]`. Rewrite using `[card_uniUp, card_Gn]`. Use `push_cast`. Rewrite using `[inv_mul_cancel_left₀ (Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ hg)]`.

Introduce `x z`. Unfold `gg`. Use `congr 1`. Use `(Fintype.sum_equiv (Equiv.mulLeft z) _ _ fun y => ?_).symm` and prove the remaining obligations. Establish `: (Equiv.mulLeft z y)⁻¹ * (z * x * z⁻¹) * (Equiv.mulLeft z y) = y⁻¹ * x * y`.

Simplify using `[mul_assoc]`. Rewrite using `[this]`.
-/
theorem gg_one_and_isClass : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) (n : ℕ),
    gg ψ n 1 = ∏ i ∈ Finset.Icc 1 n, ((g : ℂ) ^ i - 1) ∧ IsClass (gg ψ n) := by
  intro g _ ψ n
  have hg : (g : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : g.Prime).ne_zero
  constructor
  · have h1 : IsUniUp (1 : Mt g n) := fun a b =>
      ⟨fun h => Matrix.one_apply_ne h.ne', fun h => h ▸ Matrix.one_apply_eq a⟩
    have h2 : ∀ i, entN (1 : Mt g n) i (i + 1) = 0 := by
      intro i
      unfold entN
      split_ifs with h
      · exact Matrix.one_apply_ne (by simp)
      · rfl
    unfold gg
    simp only [mul_one, inv_mul_cancel, Units.val_one, h1, if_true, h2, Finset.sum_const_zero,
      AddChar.map_zero_eq_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [card_uniUp, card_Gn]
    push_cast
    rw [inv_mul_cancel_left₀ (Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ hg)]
  · intro x z
    unfold gg
    congr 1
    refine (Fintype.sum_equiv (Equiv.mulLeft z) _ _ fun y => ?_).symm
    have : (Equiv.mulLeft z y)⁻¹ * (z * x * z⁻¹) * (Equiv.mulLeft z y) = y⁻¹ * x * y := by
      simp [mul_assoc]
    rw [this]

end GlobalTheory.GLq.GGDeg
