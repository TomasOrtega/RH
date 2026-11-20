import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.LConvKirB

noncomputable section
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false
open Matrix GlobalTheory.SmGL GlobalTheory.Whittaker GlobalTheory.LocLanglands ValuativeRel Filter Topology

namespace DiscreteGroups.sglob.LConvKir

variable {k : Type} [Field k] {m : ℕ}

def Kmat (jj : Fin (m + 1)) (a : Fin (m + 1) → k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k :=
  Matrix.of fun p q => if p = jj then a q else (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) p q

def Kinv2 (jj : Fin (m + 1)) (z : (Fin (m + 1) → k) × k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k :=
  Matrix.of fun p q => if p = jj then (if q = jj then z.2 else -(z.1 q) * z.2)
    else (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) p q

def Kinv (jj : Fin (m + 1)) (a : Fin (m + 1) → k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k :=
  Kinv2 jj (a, (a jj)⁻¹)

/- English proof (translation)
Use extensionality with `p q`. Rewrite using `[Matrix.mul_apply]`. Distinguish the cases in `hp : p = jj`. Substitute `hp` using the available equality. Establish `hs : ∀ r, Kmat p a p r * Kinv p a r q = a r * (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r q + (if r = p then a p * (Kinv p a p q - (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) p q) else 0)`.

Introduce `r`. Distinguish the cases in `hr : r = p`. Rewrite using `[hr, if_pos rfl]`. Simplify using `only [Kmat, Matrix.of_apply, ↓reduceIte]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[if_neg hr, add_zero]`. Simplify using `only [Kmat, Kinv, Kinv2, Matrix.of_apply, ↓reduceIte, if_neg hr]`. Rewrite using `[Finset.sum_congr rfl (fun r _ => hs r), Finset.sum_add_distrib, Finset.sum_ite_eq']`. Simplify using `only [Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Distinguish the cases in `hq : q = p`.

Substitute `hq` using the available equality. Simplify using `only [Kinv, Kinv2, Matrix.of_apply, ↓reduceIte]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [Kinv, Kinv2, Matrix.of_apply, ↓reduceIte, if_neg hq, if_neg (Ne.symm hq)]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Finset.sum_eq_single p]`. Simplify using `only [Kmat, Kinv, Kinv2, Matrix.of_apply, if_neg hp, Matrix.one_apply_eq, one_mul]`. Introduce `r _ hr`.

Simplify using `only [Kmat, Matrix.of_apply, if_neg hp, Matrix.one_apply_ne (Ne.symm hr), zero_mul]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ p) h`.
-/
theorem Kmat_mul_Kinv (jj : Fin (m + 1)) (a : Fin (m + 1) → k) (ha : a jj ≠ 0) :
    Kmat jj a * Kinv jj a = 1 := by
  ext p q
  rw [Matrix.mul_apply]
  by_cases hp : p = jj
  · subst hp
    have hs : ∀ r, Kmat p a p r * Kinv p a r q = a r * (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r q +
        (if r = p then a p * (Kinv p a p q - (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) p q) else 0) := by
      intro r
      by_cases hr : r = p
      · rw [hr, if_pos rfl]; simp only [Kmat, Matrix.of_apply, ↓reduceIte]; ring
      · rw [if_neg hr, add_zero]
        simp only [Kmat, Kinv, Kinv2, Matrix.of_apply, ↓reduceIte, if_neg hr]
    rw [Finset.sum_congr rfl (fun r _ => hs r), Finset.sum_add_distrib, Finset.sum_ite_eq']
    simp only [Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    by_cases hq : q = p
    · subst hq
      simp only [Kinv, Kinv2, Matrix.of_apply, ↓reduceIte]
      field_simp
      ring
    · simp only [Kinv, Kinv2, Matrix.of_apply, ↓reduceIte, if_neg hq, if_neg (Ne.symm hq)]
      field_simp
      ring
  · rw [Finset.sum_eq_single p]
    · simp only [Kmat, Kinv, Kinv2, Matrix.of_apply, if_neg hp, Matrix.one_apply_eq, one_mul]
    · intro r _ hr
      simp only [Kmat, Matrix.of_apply, if_neg hp, Matrix.one_apply_ne (Ne.symm hr), zero_mul]
    · intro h; exact absurd (Finset.mem_univ p) h

/- English proof (translation)
The claim follows from `mul_eq_one_comm.1 (Kmat_mul_Kinv jj a ha)`.
-/
theorem Kinv_mul_Kmat (jj : Fin (m + 1)) (a : Fin (m + 1) → k) (ha : a jj ≠ 0) :
    Kinv jj a * Kmat jj a = 1 :=
  mul_eq_one_comm.1 (Kmat_mul_Kinv jj a ha)

/- English proof (translation)
Use extensionality with `p q`. Distinguish the cases in `hp : p = jj`. Substitute `hp` using the available equality. Simplify using `[Kmat, Matrix.one_apply, Pi.single_apply, eq_comm]`. Simplify using `[Kmat, hp]`.
-/
theorem Kmat_single (jj : Fin (m + 1)) : Kmat jj (Pi.single jj (1 : k)) = 1 := by
  ext p q
  by_cases hp : p = jj
  · subst hp; simp [Kmat, Matrix.one_apply, Pi.single_apply, eq_comm]
  · simp [Kmat, hp]

/- English proof (translation)
Use extensionality with `p q`. Distinguish the cases in `hp : p = jj`. Substitute `hp` using the available equality. Distinguish the cases in `hq : q = p`. Substitute `hq` using the available equality.

Simplify using `[Kinv, Kinv2]`. Simplify using `[Kinv, Kinv2, hq, Matrix.one_apply, Pi.single_apply, Ne.symm hq]`. Simplify using `[Kinv, Kinv2, hp]`.
-/
theorem Kinv_single (jj : Fin (m + 1)) : Kinv jj (Pi.single jj (1 : k)) = 1 := by
  ext p q
  by_cases hp : p = jj
  · subst hp
    by_cases hq : q = p
    · subst hq; simp [Kinv, Kinv2]
    · simp [Kinv, Kinv2, hq, Matrix.one_apply, Pi.single_apply, Ne.symm hq]
  · simp [Kinv, Kinv2, hp]

end DiscreteGroups.sglob.LConvKir
