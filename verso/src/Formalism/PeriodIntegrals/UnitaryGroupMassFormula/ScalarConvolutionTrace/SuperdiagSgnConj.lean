import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GGMirabolic

open Finset Matrix

noncomputable section

open Classical

namespace PI.GGConvScalarW

open Formalism.L2.SG.GGMirabolic

variable {F : Type} [Field F] [Fintype F] {k : ℕ}

def IsUTm (A : Matrix (Fin k) (Fin k) F) : Prop :=
  (∀ i, A i i = 1) ∧ ∀ i j, j < i → A i j = 0

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem isUni_iff (x : GL (Fin k) F) : IsUni k x ↔ IsUTm (x : Matrix (Fin k) (Fin k) F) := Iff.rfl

/- English proof (translation)
Use `⟨fun i => ?_, fun i j hij => ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single i]`. Rewrite using `[hA.1, hB.1, one_mul]`. Introduce `l _ hl`. Break down `lt_or_gt_of_ne hl with h | h` into its components or cases.

Rewrite using `[hA.2 i l h, zero_mul]`. Rewrite using `[hB.2 l i h, mul_zero]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ i) h`. Rewrite using `[Matrix.mul_apply]`.

Use `Finset.sum_eq_zero fun l _ => ?_` and prove the remaining obligations. Break down `lt_or_ge l i with h | h` into its components or cases. Rewrite using `[hA.2 i l h, zero_mul]`. Rewrite using `[hB.2 l j (lt_of_lt_of_le hij h), mul_zero]`.
-/
theorem IsUTm.mul {A B : Matrix (Fin k) (Fin k) F} (hA : IsUTm A) (hB : IsUTm B) : IsUTm (A * B) := by
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [hA.1, hB.1, one_mul]
    · intro l _ hl
      rcases lt_or_gt_of_ne hl with h | h
      · rw [hA.2 i l h, zero_mul]
      · rw [hB.2 l i h, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    rcases lt_or_ge l i with h | h
    · rw [hA.2 i l h, zero_mul]
    · rw [hB.2 l j (lt_of_lt_of_le hij h), mul_zero]

/- English proof (translation)
Establish `key : ∀ i j : Fin k, (j : ℕ) = (i : ℕ) + 1 → (A * B) i j = A i j + B i j`. Introduce `i j hj`. Establish `hij : i ≠ j` using `fun h => by rw [h] at hj; omega`. Rewrite using `[Matrix.mul_apply, Finset.sum_eq_add i j hij]`. Rewrite using `[hA.1, hB.1, one_mul, mul_one, add_comm]`.

Introduce `c _ hc`. Establish `h1 : (c : ℕ) ≠ i` using `fun h => hc.1 (Fin.ext h)`. Establish `h2 : (c : ℕ) ≠ j` using `fun h => hc.2 (Fin.ext h)`. Break down `Nat.lt_or_gt_of_ne h1 with h | h` into its components or cases. Rewrite using `[hA.2 i c (Fin.lt_iff_val_lt_val.2 h), zero_mul]`.

Rewrite using `[hB.2 c j (Fin.lt_iff_val_lt_val.2 (by omega)), mul_zero]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.

Unfold `superdiag`. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Use `split_ifs with hj`. Conclude with `key i j hj`. Simplify using the standard rewrite rules.
-/
theorem superdiag_mul {A B : Matrix (Fin k) (Fin k) F} (hA : IsUTm A) (hB : IsUTm B) :
    superdiag k (A * B) = superdiag k A + superdiag k B := by
  have key : ∀ i j : Fin k, (j : ℕ) = (i : ℕ) + 1 → (A * B) i j = A i j + B i j := by
    intro i j hj
    have hij : i ≠ j := fun h => by rw [h] at hj; omega
    rw [Matrix.mul_apply, Finset.sum_eq_add i j hij]
    · rw [hA.1, hB.1, one_mul, mul_one, add_comm]
    · intro c _ hc
      have h1 : (c : ℕ) ≠ i := fun h => hc.1 (Fin.ext h)
      have h2 : (c : ℕ) ≠ j := fun h => hc.2 (Fin.ext h)
      rcases Nat.lt_or_gt_of_ne h1 with h | h
      · rw [hA.2 i c (Fin.lt_iff_val_lt_val.2 h), zero_mul]
      · rw [hB.2 c j (Fin.lt_iff_val_lt_val.2 (by omega)), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
    · intro h
      exact absurd (Finset.mem_univ _) h
  unfold superdiag
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs with hj
  · exact key i j hj
  · simp

/- English proof (translation)
Establish `h2 : ∀ i j, j < i → ((u⁻¹ : GL (Fin k) F) : Matrix (Fin k) (Fin k) F) i j = 0`. Introduce `i j hij`. Rewrite using `[Matrix.coe_units_inv]`. Conclude with `Matrix.blockTriangular_inv_of_blockTriangular (b := id) (fun a b hab => h.2 a b hab) hij`. Use `⟨fun i => ?_, h2⟩` and prove the remaining obligations.

Establish `hm : ((u⁻¹ : GL (Fin k) F) : Matrix (Fin k) (Fin k) F) * (u : Matrix (Fin k) (Fin k) F) = 1`. Rewrite using `[← Units.val_mul, inv_mul_cancel, Units.val_one]`. Establish `he` using `congrFun (congrFun hm i) i`. Rewrite `he` using `[Matrix.mul_apply, Finset.sum_eq_single i, h.1, mul_one, Matrix.one_apply_eq]`. Conclude with `he`.

Introduce `l _ hl`. Break down `lt_or_gt_of_ne hl with hh | hh` into its components or cases. Rewrite using `[h2 i l hh, zero_mul]`. Rewrite using `[h.2 l i hh, mul_zero]`. Introduce `hh`.

Conclude with `absurd (Finset.mem_univ i) hh`.
-/
theorem IsUTm.inv_val (u : GL (Fin k) F) (h : IsUTm (u : Matrix (Fin k) (Fin k) F)) :
    IsUTm ((u⁻¹ : GL (Fin k) F) : Matrix (Fin k) (Fin k) F) := by
  have h2 : ∀ i j, j < i → ((u⁻¹ : GL (Fin k) F) : Matrix (Fin k) (Fin k) F) i j = 0 := by
    intro i j hij
    rw [Matrix.coe_units_inv]
    exact Matrix.blockTriangular_inv_of_blockTriangular (b := id)
      (fun a b hab => h.2 a b hab) hij
  refine ⟨fun i => ?_, h2⟩
  have hm : ((u⁻¹ : GL (Fin k) F) : Matrix (Fin k) (Fin k) F) * (u : Matrix (Fin k) (Fin k) F) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have he := congrFun (congrFun hm i) i
  rw [Matrix.mul_apply, Finset.sum_eq_single i, h.1, mul_one, Matrix.one_apply_eq] at he
  · exact he
  · intro l _ hl
    rcases lt_or_gt_of_ne hl with hh | hh
    · rw [h2 i l hh, zero_mul]
    · rw [h.2 l i hh, mul_zero]
  · intro hh
    exact absurd (Finset.mem_univ i) hh

/- English proof (translation)
Use `show IsUTm ((x : Matrix (Fin k) (Fin k) F) * (y : Matrix (Fin k) (Fin k) F))`. Conclude with `IsUTm.mul hx hy`.
-/
theorem isUni_mul {x y : GL (Fin k) F} (hx : IsUni k x) (hy : IsUni k y) : IsUni k (x * y) := by
  show IsUTm ((x : Matrix (Fin k) (Fin k) F) * (y : Matrix (Fin k) (Fin k) F))
  exact IsUTm.mul hx hy

/- English proof (translation)
The claim follows from `IsUTm.inv_val x hx`.
-/
theorem isUni_inv {x : GL (Fin k) F} (hx : IsUni k x) : IsUni k x⁻¹ := IsUTm.inv_val x hx

/- English proof (translation)
Unfold `psiU`. Rewrite using `[Units.val_mul, superdiag_mul hx hy, AddChar.map_add_eq_mul]`.
-/
theorem psiU_mul (ψ₀ : AddChar F ℂ) {x y : GL (Fin k) F} (hx : IsUni k x) (hy : IsUni k y) :
    psiU ψ₀ (x * y) = psiU ψ₀ x * psiU ψ₀ y := by
  unfold psiU
  rw [Units.val_mul, superdiag_mul hx hy, AddChar.map_add_eq_mul]

/- English proof (translation)
Unfold `psiU`. Establish `h0 : superdiag k (1 : Matrix (Fin k) (Fin k) F) = 0`. Unfold `superdiag`. Use `Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations. Use `split_ifs with h`.

Rewrite using `[Matrix.one_apply_ne]`. Introduce `e`. Rewrite `h` using `[e]`. Use linear arithmetic over natural numbers and integers. Both sides reduce to the same expression.

Rewrite using `[Units.val_one, h0, AddChar.map_zero_eq_one]`.
-/
theorem psiU_one (ψ₀ : AddChar F ℂ) : psiU ψ₀ (1 : GL (Fin k) F) = 1 := by
  unfold psiU
  have h0 : superdiag k (1 : Matrix (Fin k) (Fin k) F) = 0 := by
    unfold superdiag
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    split_ifs with h
    · rw [Matrix.one_apply_ne]
      intro e
      rw [e] at h
      omega
    · rfl
  rw [Units.val_one, h0, AddChar.map_zero_eq_one]

/- English proof (translation)
Rewrite using `[← psiU_mul ψ₀ (isUni_inv hx) hx, inv_mul_cancel, psiU_one]`.
-/
theorem psiU_inv_mul (ψ₀ : AddChar F ℂ) {x : GL (Fin k) F} (hx : IsUni k x) :
    psiU ψ₀ x⁻¹ * psiU ψ₀ x = 1 := by
  rw [← psiU_mul ψ₀ (isUni_inv hx) hx, inv_mul_cancel, psiU_one]

/- English proof (translation)
Unfold `psiU`. Introduce `h`. Establish `h1` using `AddChar.map_add_eq_mul ψ₀ (superdiag k (x : Matrix (Fin k) (Fin k) F)) (-(superdiag k (x : Matrix (Fin k) (Fin k) F)))`. Rewrite `h1` using `[add_neg_cancel, AddChar.map_zero_eq_one, h, zero_mul]`. Conclude with `one_ne_zero h1`.
-/
theorem psiU_ne_zero (ψ₀ : AddChar F ℂ) (x : GL (Fin k) F) : psiU ψ₀ x ≠ 0 := by
  unfold psiU
  intro h
  have h1 := AddChar.map_add_eq_mul ψ₀ (superdiag k (x : Matrix (Fin k) (Fin k) F)) (-(superdiag k (x : Matrix (Fin k) (Fin k) F)))
  rw [add_neg_cancel, AddChar.map_zero_eq_one, h, zero_mul] at h1
  exact one_ne_zero h1

def sgnM (k : ℕ) : Matrix (Fin k) (Fin k) F := Matrix.diagonal fun i => (-1 : F) ^ (i : ℕ)

/- English proof (translation)
Unfold `sgnM`. Rewrite using `[Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Rewrite using `[← mul_pow, neg_one_mul, neg_neg, one_pow]`.
-/
theorem sgnM_mul_self : sgnM (F := F) k * sgnM k = 1 := by
  unfold sgnM
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  rw [← mul_pow, neg_one_mul, neg_neg, one_pow]

def sgn (k : ℕ) : GL (Fin k) F := ⟨sgnM k, sgnM k, sgnM_mul_self, sgnM_mul_self⟩

/- English proof (translation)
Conclude with `Units.ext sgnM_mul_self`.
-/
theorem sgn_mul_self : sgn (F := F) k * sgn k = 1 := by
  exact Units.ext sgnM_mul_self

/- English proof (translation)
Unfold `sgnM`. Rewrite using `[Matrix.mul_diagonal, Matrix.diagonal_mul]`.
-/
theorem sgn_conj_apply (A : Matrix (Fin k) (Fin k) F) (i j : Fin k) :
    (sgnM (F := F) k * A * sgnM (F := F) k) i j = (-1 : F) ^ (i : ℕ) * A i j * (-1 : F) ^ (j : ℕ) := by
  unfold sgnM
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]

/- English proof (translation)
Use `⟨fun i => ?_, fun i j hij => ?_⟩` and prove the remaining obligations. Rewrite using `[sgn_conj_apply, h.1, mul_one, ← mul_pow, neg_one_mul, neg_neg, one_pow]`. Rewrite using `[sgn_conj_apply, h.2 i j hij, mul_zero, zero_mul]`.
-/
theorem isUTm_sgn_conj {A : Matrix (Fin k) (Fin k) F} (h : IsUTm A) : IsUTm (sgnM (F := F) k * A * sgnM (F := F) k) := by
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · rw [sgn_conj_apply, h.1, mul_one, ← mul_pow, neg_one_mul, neg_neg, one_pow]
  · rw [sgn_conj_apply, h.2 i j hij, mul_zero, zero_mul]

/- English proof (translation)
Unfold `superdiag`. Rewrite using `[← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Use `split_ifs with h`. Establish `hs : (-1 : F) ^ (i : ℕ) * (-1) ^ (i : ℕ) = 1`. Rewrite using `[← mul_pow, neg_one_mul, neg_neg, one_pow]`. Rewrite using `[sgn_conj_apply, h, pow_succ]`. Take the linear combination `(-(A i j)) * hs`.

Rewrite using `[neg_zero]`.
-/
theorem superdiag_sgn_conj (A : Matrix (Fin k) (Fin k) F) :
    superdiag k (sgnM (F := F) k * A * sgnM (F := F) k) = - superdiag k A := by
  unfold superdiag
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs with h
  · have hs : (-1 : F) ^ (i : ℕ) * (-1) ^ (i : ℕ) = 1 := by
      rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
    rw [sgn_conj_apply, h, pow_succ]
    linear_combination (-(A i j)) * hs
  · rw [neg_zero]

/- English proof (translation)
Use `show IsUTm (sgnM (F := F) k * (u : Matrix (Fin k) (Fin k) F) * sgnM k)`. Conclude with `isUTm_sgn_conj h`.
-/
theorem isUni_sgn_conj {u : GL (Fin k) F} (h : IsUni k u) : IsUni k (sgn k * u * sgn k) := by
  show IsUTm (sgnM (F := F) k * (u : Matrix (Fin k) (Fin k) F) * sgnM k)
  exact isUTm_sgn_conj h

/- English proof (translation)
Unfold `psiU`. Rewrite using `[show ((sgn k * u * sgn k : GL (Fin k) F) : Matrix (Fin k) (Fin k) F) = sgnM k * (u : Matrix (Fin k) (Fin k) F) * sgnM k from rfl, superdiag_sgn_conj, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]`.
-/
theorem psiU_sgn_conj (ψ₀ : AddChar F ℂ) (u : GL (Fin k) F) :
    psiU ψ₀ (sgn k * u * sgn k) * psiU ψ₀ u = 1 := by
  unfold psiU
  rw [show ((sgn k * u * sgn k : GL (Fin k) F) : Matrix (Fin k) (Fin k) F) = sgnM k * (u : Matrix (Fin k) (Fin k) F) * sgnM k from rfl,
    superdiag_sgn_conj, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]

end PI.GGConvScalarW
