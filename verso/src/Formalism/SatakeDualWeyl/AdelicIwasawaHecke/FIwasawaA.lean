import Formalism.SatakeDualWeyl.StatementF
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.SphericalA
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.GlintPrincRelIndexNeZero

open Formalism.UG Matrix

namespace Formalism.UG.P

section FIwasawaGen

variable {L : Type} [Field L] (σ : L →+* L) {n : ℕ}

def fIwasawaH (x y : Fin n → L) : L := ∑ j, σ (x (Fin.rev j)) * y j

def fIwasawaUn (M : Matrix (Fin n) (Fin n) L) : Prop := cT σ M * antiJ L n * M = antiJ L n

/- English proof (translation)
Unfold `antiJ`. Apply the tactic sequence `try simp only [Matrix.of_apply]`. Establish `hi` using `i.isLt`. Establish `hj` using `j.isLt`. Establish `hiff : ((i : ℕ) + (j : ℕ) + 1 = n) ↔ (j = Fin.rev i)`.

Rewrite using `[Fin.ext_iff, Fin.val_rev]`. Use linear arithmetic over natural numbers and integers. Distinguish the cases in `h : j = Fin.rev i`. Rewrite using `[if_pos h, if_pos (hiff.mpr h)]`. Rewrite using `[if_neg h, if_neg (fun h' => h (hiff.mp h'))]`.
-/
theorem fIwasawa_antiJ (i j : Fin n) : antiJ L n i j = if j = Fin.rev i then 1 else 0 := by
  unfold antiJ
  try simp only [Matrix.of_apply]
  have hi := i.isLt
  have hj := j.isLt
  have hiff : ((i : ℕ) + (j : ℕ) + 1 = n) ↔ (j = Fin.rev i) := by
    rw [Fin.ext_iff, Fin.val_rev]; omega
  by_cases h : j = Fin.rev i
  · rw [if_pos h, if_pos (hiff.mpr h)]
  · rw [if_neg h, if_neg (fun h' => h (hiff.mp h'))]

/- English proof (translation)
Apply the tactic sequence `first | rfl | simp [cT] | (unfold cT; simp)`.
-/
private theorem cT_apply' (M : Matrix (Fin n) (Fin n) L) (i j : Fin n) : cT σ M i j = σ (M j i) := by
  first | rfl | simp [cT] | (unfold cT; simp)

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [cT_apply', Matrix.mul_apply, map_sum, map_mul]`. Conclude with `Finset.sum_congr rfl (fun k _ => mul_comm _ _)`.
-/
private theorem cT_mul_adelic_iwasawa_hecke (A B : Matrix (Fin n) (Fin n) L) : cT σ (A * B) = cT σ B * cT σ A := by
  ext i j
  simp only [cT_apply', Matrix.mul_apply, map_sum, map_mul]
  exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)

/- English proof (translation)
Unfold `fIwasawaH`. Rewrite using `[Matrix.mul_apply]`. Use `Finset.sum_congr rfl (fun k _ => ?_)` and prove the remaining obligations. Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single (Fin.rev k)]`. Simplify using `[fIwasawa_antiJ, cT_apply']`.

Introduce `l _ hl`. Establish `: k ≠ Fin.rev l` using `fun h => hl (by rw [h, Fin.rev_rev])`. Simplify using `[fIwasawa_antiJ, this]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem fIwasawa_gram (M : Matrix (Fin n) (Fin n) L) (a b : Fin n) :
    (cT σ M * antiJ L n * M) a b = fIwasawaH σ (fun i => M i a) (fun i => M i b) := by
  unfold fIwasawaH
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.rev k)]
  · simp [fIwasawa_antiJ, cT_apply']
  · intro l _ hl
    have : k ≠ Fin.rev l := fun h => hl (by rw [h, Fin.rev_rev])
    simp [fIwasawa_antiJ, this]
  · intro h; exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Unfold `fIwasawaH`. Rewrite using `[Finset.sum_eq_single (Fin.rev p)]`. Simplify using the standard rewrite rules. Introduce `j _ hj`. Establish `: Fin.rev j ≠ p` using `fun h => hj (by rw [← h, Fin.rev_rev])`.

Simplify using `[Pi.single_apply, this]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem fIwasawa_H_single_left (p : Fin n) (w : Fin n → L) :
    fIwasawaH σ (Pi.single p 1) w = w (Fin.rev p) := by
  unfold fIwasawaH
  rw [Finset.sum_eq_single (Fin.rev p)]
  · simp
  · intro j _ hj
    have : Fin.rev j ≠ p := fun h => hj (by rw [← h, Fin.rev_rev])
    simp [Pi.single_apply, this]
  · intro h; exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Establish `hc : ∀ a : Fin n, (fun i => M i a) = M *ᵥ Pi.single a 1`. Introduce `a`. Use extensionality with `i`. Simplify using `[Matrix.mulVec, dotProduct, Pi.single_apply]`. Unfold `fIwasawaUn`.

Use extensionality with `a b`. Rewrite using `[fIwasawa_gram, hc a, hc b, h, fIwasawa_H_single_left, fIwasawa_antiJ]`. Distinguish the cases in `hb : b = Fin.rev a`. Substitute `hb` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[Pi.single_apply, hb, Ne.symm hb]`.
-/
theorem fIwasawa_un_of_isometry (M : Matrix (Fin n) (Fin n) L)
    (h : ∀ x y, fIwasawaH σ (M *ᵥ x) (M *ᵥ y) = fIwasawaH σ x y) : fIwasawaUn σ M := by
  have hc : ∀ a : Fin n, (fun i => M i a) = M *ᵥ Pi.single a 1 := by
    intro a; ext i; simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  unfold fIwasawaUn
  ext a b
  rw [fIwasawa_gram, hc a, hc b, h, fIwasawa_H_single_left, fIwasawa_antiJ]
  by_cases hb : b = Fin.rev a
  · subst hb; simp
  · simp [Pi.single_apply, hb, Ne.symm hb]

/- English proof (translation)
Unfold `fIwasawaUn at *`. Rewrite using `[cT_mul_adelic_iwasawa_hecke, show cT σ B * cT σ A * antiJ L n * (A * B) = cT σ B * (cT σ A * antiJ L n * A) * B by`. Simplify using `only [Matrix.mul_assoc], hA, hB]`.
-/
theorem fIwasawa_un_mul (A B : Matrix (Fin n) (Fin n) L) (hA : fIwasawaUn σ A) (hB : fIwasawaUn σ B) :
    fIwasawaUn σ (A * B) := by
  unfold fIwasawaUn at *
  rw [cT_mul_adelic_iwasawa_hecke, show cT σ B * cT σ A * antiJ L n * (A * B) = cT σ B * (cT σ A * antiJ L n * A) * B by
    simp only [Matrix.mul_assoc], hA, hB]

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single (Fin.rev i)]`. Rewrite using `[fIwasawa_antiJ, fIwasawa_antiJ, Fin.rev_rev]`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[Matrix.one_apply, h, Ne.symm h]`. Introduce `k _ hk`. Simplify using `[fIwasawa_antiJ, hk]`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem fIwasawa_antiJ_mul_antiJ : antiJ L n * antiJ L n = 1 := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.rev i)]
  · rw [fIwasawa_antiJ, fIwasawa_antiJ, Fin.rev_rev]
    by_cases h : i = j
    · subst h; simp
    · simp [Matrix.one_apply, h, Ne.symm h]
  · intro k _ hk
    simp [fIwasawa_antiJ, hk]
  · intro h; exact absurd (Finset.mem_univ _) h

def fIwasawaInv (M : Matrix (Fin n) (Fin n) L) : Matrix (Fin n) (Fin n) L :=
  antiJ L n * cT σ M * antiJ L n

/- English proof (translation)
Unfold `fIwasawaInv`. Unfold `fIwasawaUn at hM`. Rewrite using `[show antiJ L n * cT σ M * antiJ L n * M = antiJ L n * (cT σ M * antiJ L n * M) by`. Simplify using `only [Matrix.mul_assoc], hM, fIwasawa_antiJ_mul_antiJ]`.
-/
theorem fIwasawa_inv_mul (M : Matrix (Fin n) (Fin n) L) (hM : fIwasawaUn σ M) :
    fIwasawaInv σ M * M = 1 := by
  unfold fIwasawaInv
  unfold fIwasawaUn at hM
  rw [show antiJ L n * cT σ M * antiJ L n * M = antiJ L n * (cT σ M * antiJ L n * M) by
    simp only [Matrix.mul_assoc], hM, fIwasawa_antiJ_mul_antiJ]

/- English proof (translation)
Establish `h` using `fIwasawa_inv_mul σ M hM`. Use `first`. Consider the case `exact mul_eq_one_comm.mp h`. Consider the case `(rw [← Matrix.inv_eq_left_inv h]; exact Matrix.mul_nonsing_inv _ (Matrix.isUnit_det_of_left_inverse h))`.
-/
theorem fIwasawa_mul_inv (M : Matrix (Fin n) (Fin n) L) (hM : fIwasawaUn σ M) :
    M * fIwasawaInv σ M = 1 := by
  have h := fIwasawa_inv_mul σ M hM
  first
  | exact mul_eq_one_comm.mp h
  | (rw [← Matrix.inv_eq_left_inv h]; exact Matrix.mul_nonsing_inv _ (Matrix.isUnit_det_of_left_inverse h))

def fIwasawaMk (M : Matrix (Fin n) (Fin n) L) (hM : fIwasawaUn σ M) : GU σ n :=
  ⟨⟨M, fIwasawaInv σ M, fIwasawa_mul_inv σ M hM, fIwasawa_inv_mul σ M hM⟩, hM⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem fIwasawa_mk_val (M : Matrix (Fin n) (Fin n) L) (hM : fIwasawaUn σ M) :
    (((fIwasawaMk σ M hM : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = M := rfl

/- English proof (translation)
The claim follows from `g.2`.
-/
theorem fIwasawa_mem_un (g : GU σ n) :
    fIwasawaUn σ (((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) := g.2

end FIwasawaGen

end Formalism.UG.P
