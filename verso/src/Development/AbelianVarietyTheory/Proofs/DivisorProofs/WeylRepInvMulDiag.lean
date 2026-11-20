import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GindikinKarpelevich

open GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.WeylCell

namespace GlobalTheory.GKFactor

variable {k : Type} [Field k] {n : ℕ}

local notation "M" x:max => ((x : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)

/- English proof (translation)
Establish `h : (M (x⁻¹ * x)) p p = (M (1 : GL (Fin n) k)) p p` using `by rw [inv_mul_cancel]`. Rewrite `h` using `[Units.val_mul, Matrix.mul_apply, Units.val_one, Matrix.one_apply_eq]`. Rewrite `h` using `[Finset.sum_eq_single (w p) (fun b _ hb => by rw [hx b p hb, mul_zero]) (by simp)]`. Then use the resulting hypothesis.
-/
theorem weylRep_inv_mul_diag {w : Equiv.Perm (Fin n)} {x : GL (Fin n) k} (hx : IsWeylRep w x) (p : Fin n) :
    (M x⁻¹) p (w p) * (M x) (w p) p = 1 := by
  have h : (M (x⁻¹ * x)) p p = (M (1 : GL (Fin n) k)) p p := by rw [inv_mul_cancel]
  rw [Units.val_mul, Matrix.mul_apply, Units.val_one, Matrix.one_apply_eq] at h
  rwa [Finset.sum_eq_single (w p) (fun b _ hb => by rw [hx b p hb, mul_zero]) (by simp)] at h

/- English proof (translation)
Establish `h : (M (x * x⁻¹)) (w p) (w p) = (M (1 : GL (Fin n) k)) (w p) (w p)` using `by rw [mul_inv_cancel]`. Rewrite `h` using `[Units.val_mul, Matrix.mul_apply, Units.val_one, Matrix.one_apply_eq]`. Rewrite using `[Finset.sum_eq_single p (fun b _ hb => by` and apply the resulting hypothesis. Rewrite `h` using `[hx (w p) b (fun e => hb (w.injective e).symm), zero_mul]) (by simp)]`.
-/
theorem weylRep_mul_inv_diag {w : Equiv.Perm (Fin n)} {x : GL (Fin n) k} (hx : IsWeylRep w x) (p : Fin n) :
    (M x) (w p) p * (M x⁻¹) p (w p) = 1 := by
  have h : (M (x * x⁻¹)) (w p) (w p) = (M (1 : GL (Fin n) k)) (w p) (w p) := by rw [mul_inv_cancel]
  rw [Units.val_mul, Matrix.mul_apply, Units.val_one, Matrix.one_apply_eq] at h
  rwa [Finset.sum_eq_single p (fun b _ hb => by
      rw [hx (w p) b (fun e => hb (w.injective e).symm), zero_mul]) (by simp)] at h

/- English proof (translation)
Introduce `p a hpa`. Establish `hne : (M x) a (w⁻¹ a) ≠ 0`. Introduce `h0`. Use `weylRep_mul_inv_diag hx (w⁻¹ a)` as an intermediate fact. Rewrite `this` using `[show w (w⁻¹ a) = a by simp]`.

Rewrite `this` using `[h0, zero_mul]`. Conclude with `zero_ne_one this`. Establish `h : (M (x⁻¹ * x)) p (w⁻¹ a) = (M (1 : GL (Fin n) k)) p (w⁻¹ a)` using `by rw [inv_mul_cancel]`. Rewrite `h` using `[Units.val_mul, Matrix.mul_apply, Units.val_one, Matrix.one_apply_ne hpa]`. Rewrite using `[Finset.sum_eq_single a (fun b _ hb => by`.

Rewrite `h` using `[hx b (w⁻¹ a) (by simpa using hb), mul_zero]) (by simp)]`. Conclude with `(mul_eq_zero.1 h).resolve_right hne`.
-/
theorem weylRep_inv {w : Equiv.Perm (Fin n)} {x : GL (Fin n) k} (hx : IsWeylRep w x) : IsWeylRep w⁻¹ x⁻¹ := by
  intro p a hpa
  have hne : (M x) a (w⁻¹ a) ≠ 0 := by
    intro h0
    have := weylRep_mul_inv_diag hx (w⁻¹ a)
    rw [show w (w⁻¹ a) = a by simp] at this
    rw [h0, zero_mul] at this
    exact zero_ne_one this
  have h : (M (x⁻¹ * x)) p (w⁻¹ a) = (M (1 : GL (Fin n) k)) p (w⁻¹ a) := by rw [inv_mul_cancel]
  rw [Units.val_mul, Matrix.mul_apply, Units.val_one, Matrix.one_apply_ne hpa] at h
  rw [Finset.sum_eq_single a (fun b _ hb => by
      rw [hx b (w⁻¹ a) (by simpa using hb), mul_zero]) (by simp)] at h
  exact (mul_eq_zero.1 h).resolve_right hne

/- English proof (translation)
Establish `hi` using `weylRep_inv hx`. Rewrite using `[Units.val_mul, Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single (w q) (fun b _ hb => by rw [hx b q hb, mul_zero]) (by simp), Matrix.mul_apply, Finset.sum_eq_single (w p) (fun b _ hb => by rw [hi p b (fun e => hb (by rw [e]; simp)), zero_mul]) (by simp)]`.
-/
theorem weylRep_conj_apply {w : Equiv.Perm (Fin n)} {x : GL (Fin n) k} (hx : IsWeylRep w x) (u : GL (Fin n) k)
    (p q : Fin n) : (M (x⁻¹ * u * x)) p q = (M x⁻¹) p (w p) * (M u) (w p) (w q) * (M x) (w q) q := by
  have hi := weylRep_inv hx
  rw [Units.val_mul, Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single (w q)
    (fun b _ hb => by rw [hx b q hb, mul_zero]) (by simp), Matrix.mul_apply,
    Finset.sum_eq_single (w p) (fun b _ hb => by rw [hi p b (fun e => hb (by rw [e]; simp)), zero_mul]) (by simp)]

/- English proof (translation)
Rewrite using `[mem_cell, mem_unipBLower]`. Use `and_congr_right fun hu => ?_` and prove the remaining obligations. Rewrite `hu` using `[mem_unipB]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hl, -⟩ a b hab hw`.

Establish `h` using `hl _ _ hw`. Rewrite `h` using `[weylRep_conj_apply hx, show w (w⁻¹ a) = a by simp, show w (w⁻¹ b) = b by simp]`. Establish `h1` using `weylRep_inv_mul_diag hx (w⁻¹ a)`. Establish `h2` using `weylRep_mul_inv_diag hx (w⁻¹ b)`. Rewrite `h1` using `[show w (w⁻¹ a) = a by simp]`.

Rewrite `h2` using `[show w (w⁻¹ b) = b by simp]`. Break down `mul_eq_zero.1 h with h | h` into its components or cases. Break down `mul_eq_zero.1 h with h | h` into its components or cases. Rewrite `h1` using `[h, zero_mul]`. Conclude with `absurd h1 zero_ne_one`.

Conclude with `h`. Rewrite `h2` using `[h, zero_mul]`. Conclude with `absurd h2 zero_ne_one`. Introduce `h`. Use `⟨fun p q hpq => ?_, fun p => ?_⟩` and prove the remaining obligations.

Rewrite using `[weylRep_conj_apply hx]`. Break down `lt_or_gt_of_ne (fun e : w p = w q => hpq.ne (w.injective e)) with hl | hl` into its components or cases. Rewrite using `[h _ _ hl (by simpa using hpq), mul_zero, zero_mul]`. Rewrite using `[hu.1 _ _ hl, mul_zero, zero_mul]`. Rewrite using `[weylRep_conj_apply hx, hu.2, mul_one, weylRep_inv_mul_diag hx]`.
-/
theorem mem_cell_iff {w : Equiv.Perm (Fin n)} {x : GL (Fin n) k} (hx : IsWeylRep w x) (u : GL (Fin n) k) :
    u ∈ cell x ↔ u ∈ unipB k (Fin n) ∧ ∀ a b, a < b → w⁻¹ a < w⁻¹ b → (M u) a b = 0 := by
  rw [mem_cell, mem_unipBLower]
  refine and_congr_right fun hu => ?_
  rw [mem_unipB] at hu
  constructor
  · rintro ⟨hl, -⟩ a b hab hw
    have h := hl _ _ hw
    rw [weylRep_conj_apply hx, show w (w⁻¹ a) = a by simp, show w (w⁻¹ b) = b by simp] at h
    have h1 := weylRep_inv_mul_diag hx (w⁻¹ a)
    have h2 := weylRep_mul_inv_diag hx (w⁻¹ b)
    rw [show w (w⁻¹ a) = a by simp] at h1
    rw [show w (w⁻¹ b) = b by simp] at h2
    rcases mul_eq_zero.1 h with h | h
    · rcases mul_eq_zero.1 h with h | h
      · rw [h, zero_mul] at h1; exact absurd h1 zero_ne_one
      · exact h
    · rw [h, zero_mul] at h2; exact absurd h2 zero_ne_one
  · intro h
    refine ⟨fun p q hpq => ?_, fun p => ?_⟩
    · rw [weylRep_conj_apply hx]
      rcases lt_or_gt_of_ne (fun e : w p = w q => hpq.ne (w.injective e)) with hl | hl
      · rw [h _ _ hl (by simpa using hpq), mul_zero, zero_mul]
      · rw [hu.1 _ _ hl, mul_zero, zero_mul]
    · rw [weylRep_conj_apply hx, hu.2, mul_one, weylRep_inv_mul_diag hx]

end GlobalTheory.GKFactor
