import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StrongApproximation.DedekindLFunctions

noncomputable section

open IsDedekindDomain

namespace Formalism.L2.SG.Pf.ProdEApprox

section DedekindLFunctions

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  {n : ℕ}

end DedekindLFunctions

section Ent

variable {A : Type*} [CommRing A] {n : ℕ}

def EntIn (J : AddSubgroup A) (X : Matrix (Fin n) (Fin n) A) : Prop := ∀ i j, X i j ∈ J

/- English proof (translation)
Introduce `i j`. Rewrite using `[Matrix.mul_apply]`. Conclude with `sum_mem fun k _ => h _ (hX i k) _ (hY k j)`.
-/
theorem entIn_mul {J1 J2 J3 : AddSubgroup A} (h : ∀ x ∈ J1, ∀ y ∈ J2, x * y ∈ J3)
    {X Y : Matrix (Fin n) (Fin n) A} (hX : EntIn J1 X) (hY : EntIn J2 Y) : EntIn J3 (X * Y) := by
  intro i j
  rw [Matrix.mul_apply]
  exact sum_mem fun k _ => h _ (hX i k) _ (hY k j)

/- English proof (translation)
Introduce `i j` and use `J.add_mem (hX i j) (hY i j)`.
-/
theorem entIn_add {J : AddSubgroup A} {X Y : Matrix (Fin n) (Fin n) A} (hX : EntIn J X) (hY : EntIn J Y) :
    EntIn J (X + Y) :=
  fun i j => J.add_mem (hX i j) (hY i j)

/- English proof (translation)
Introduce `i j` and use `J.neg_mem (hX i j)`.
-/
theorem entIn_neg {J : AddSubgroup A} {X : Matrix (Fin n) (Fin n) A} (hX : EntIn J X) : EntIn J (-X) :=
  fun i j => J.neg_mem (hX i j)

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero`. Introduce `i j h`. Rewrite using `[pow_zero, Matrix.one_apply_ne]`. Introduce and unpack `rfl`.

Use linear arithmetic over natural numbers and integers. Consider the case `succ m ih`. Introduce `i j h`. Rewrite using `[pow_succ, Matrix.mul_apply]`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations.

Distinguish the cases in `hk : f i < f k + m`. Rewrite using `[ih i k hk, zero_mul]`. Rewrite using `[hX k j (by omega), mul_zero]`.
-/
theorem pow_apply_eq_zero (f : Fin n → ℕ) {X : Matrix (Fin n) (Fin n) A} (hX : ∀ i j, f i ≤ f j → X i j = 0)
    (m : ℕ) : ∀ i j, f i < f j + m → (X ^ m) i j = 0 := by
  induction m with
  | zero =>
    intro i j h
    rw [pow_zero, Matrix.one_apply_ne]
    rintro rfl
    omega
  | succ m ih =>
    intro i j h
    rw [pow_succ, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : f i < f k + m
    · rw [ih i k hk, zero_mul]
    · rw [hX k j (by omega), mul_zero]

/- English proof (translation)
Use extensionality with `i j`. Use `hf i` as an intermediate fact. Conclude with `pow_apply_eq_zero f hX n i j (by omega)`.
-/
theorem pow_eq_zero_of (f : Fin n → ℕ) (hf : ∀ i, f i < n) {X : Matrix (Fin n) (Fin n) A}
    (hX : ∀ i j, f i ≤ f j → X i j = 0) : X ^ n = 0 := by
  ext i j
  have := hf i
  exact pow_apply_eq_zero f hX n i j (by omega)

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => rw [zero_add, pow_one]`. Conclude with `entIn_neg hX`. Consider the case `succ m ih => rw [pow_succ]`. Conclude with `entIn_mul hJ ih (entIn_neg hX)`.
-/
theorem entIn_negpow {J : AddSubgroup A} (hJ : ∀ x ∈ J, ∀ y ∈ J, x * y ∈ J) {X : Matrix (Fin n) (Fin n) A}
    (hX : EntIn J X) (m : ℕ) : EntIn J ((-X) ^ (m + 1)) := by
  induction m with
  | zero => rw [zero_add, pow_one]; exact entIn_neg hX
  | succ m ih => rw [pow_succ]; exact entIn_mul hJ ih (entIn_neg hX)

/- English proof (translation)
Use `set X := (x : Matrix (Fin n) (Fin n) A) - 1 with hXdef`. Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases. Conclude with `⟨fun i => i.elim0, fun i => i.elim0⟩`. Establish `hnX : ∀ i j, f i ≤ f j → (-X) i j = 0` using `fun i j h => by rw [Matrix.neg_apply, hlow i j h, neg_zero]`. Establish `hpow : (-X) ^ n = 0` using `pow_eq_zero_of f hf hnX`.

Establish `hxS : (x : Matrix (Fin n) (Fin n) A) * ∑ i ∈ Finset.range n, (-X) ^ i = 1`. Establish `e : (x : Matrix (Fin n) (Fin n) A) = 1 - (-X)` using `by rw [sub_neg_eq_add, hXdef, add_sub_cancel]`. Rewrite using `[e, mul_neg_geom_sum, hpow, sub_zero]`. Establish `hinv : ((x⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) = ∑ i ∈ Finset.range n, (-X) ^ i`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]`. Take `⟨k, rfl⟩ : ∃ k, n = k + 1` from `⟨n - 1, by omega⟩`. Establish `hY : ((x⁻¹ : GL (Fin (k + 1)) A) : Matrix (Fin (k + 1)) (Fin (k + 1)) A) - 1 = ∑ i ∈ Finset.range k, (-X) ^ (i + 1)`. Rewrite using `[hinv, Finset.sum_range_succ', pow_zero, add_sub_cancel_right]`. Rewrite using `[hY]`.

Use `⟨fun i j => ?_, fun i j h => ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.sum_apply]`. Conclude with `sum_mem fun m _ => entIn_negpow hJ hx m i j`. Rewrite using `[Matrix.sum_apply]`. Conclude with `Finset.sum_eq_zero fun m _ => pow_apply_eq_zero f hnX (m + 1) i j (by omega)`.
-/
theorem inv_sub_one (f : Fin n → ℕ) (hf : ∀ i, f i < n) {J : AddSubgroup A} (hJ : ∀ x ∈ J, ∀ y ∈ J, x * y ∈ J)
    (x : GL (Fin n) A) (hlow : ∀ i j, f i ≤ f j → ((x : Matrix (Fin n) (Fin n) A) - 1) i j = 0)
    (hx : EntIn J ((x : Matrix (Fin n) (Fin n) A) - 1)) :
    EntIn J (((x⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) - 1) ∧
      ∀ i j, f i ≤ f j → (((x⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) - 1) i j = 0 := by
  set X := (x : Matrix (Fin n) (Fin n) A) - 1 with hXdef
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨fun i => i.elim0, fun i => i.elim0⟩
  have hnX : ∀ i j, f i ≤ f j → (-X) i j = 0 := fun i j h => by rw [Matrix.neg_apply, hlow i j h, neg_zero]
  have hpow : (-X) ^ n = 0 := pow_eq_zero_of f hf hnX

  have hxS : (x : Matrix (Fin n) (Fin n) A) * ∑ i ∈ Finset.range n, (-X) ^ i = 1 := by
    have e : (x : Matrix (Fin n) (Fin n) A) = 1 - (-X) := by rw [sub_neg_eq_add, hXdef, add_sub_cancel]
    rw [e, mul_neg_geom_sum, hpow, sub_zero]
  have hinv : ((x⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) = ∑ i ∈ Finset.range n, (-X) ^ i := by
    calc ((x⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A)
        = ((x⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) *
          ((x : Matrix (Fin n) (Fin n) A) * ∑ i ∈ Finset.range n, (-X) ^ i) := by rw [hxS, mul_one]
      _ = ∑ i ∈ Finset.range n, (-X) ^ i := by
          rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hY : ((x⁻¹ : GL (Fin (k + 1)) A) : Matrix (Fin (k + 1)) (Fin (k + 1)) A) - 1 =
      ∑ i ∈ Finset.range k, (-X) ^ (i + 1) := by
    rw [hinv, Finset.sum_range_succ', pow_zero, add_sub_cancel_right]
  rw [hY]
  refine ⟨fun i j => ?_, fun i j h => ?_⟩
  · rw [Matrix.sum_apply]
    exact sum_mem fun m _ => entIn_negpow hJ hx m i j
  · rw [Matrix.sum_apply]
    exact Finset.sum_eq_zero fun m _ => pow_apply_eq_zero f hnX (m + 1) i j (by omega)

end Ent

end Formalism.L2.SG.Pf.ProdEApprox
