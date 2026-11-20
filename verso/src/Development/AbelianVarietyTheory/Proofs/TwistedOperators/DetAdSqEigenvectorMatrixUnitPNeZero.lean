import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousExptPY

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

namespace GlobalTheory.PolarU

open scoped ComplexOrder in

/- English proof (translation)
Introduce `hdet`. Take `⟨v, hv0, hv⟩` from `Matrix.exists_mulVec_eq_zero_iff.mpr hdet`. Apply `hv0` to reduce the goal to its premises. Establish `hquad : star v ⬝ᵥ ((P + Pᴴ) *ᵥ v) = 2 * (star v ⬝ᵥ v)`. Rewrite using `[h]`.

Use `first`. Consider the case `simp [smul_mulVec, dotProduct_smul, smul_eq_mul]`. Consider the case `simp [Matrix.smul_mulVec_assoc, dotProduct_smul, smul_eq_mul]`. Consider the case `simp [dotProduct_smul, smul_eq_mul]`. Establish `hzero : star v ⬝ᵥ ((P + Pᴴ) *ᵥ v) = 0`.

Establish `hstar : star v ᵥ* Pᴴ = star (P *ᵥ v)` using `(star_mulVec P v).symm`. Rewrite using `[add_mulVec, dotProduct_add, dotProduct_mulVec (star v) Pᴴ v, hstar, hv]`. Simplify using the standard rewrite rules. Establish `hnorm : star v ⬝ᵥ v = 0`. Establish `h2 : (2 : ℂ) * (star v ⬝ᵥ v) = 0` using `hquad.symm.trans hzero`.

Break down `mul_eq_zero.mp h2 with h2 | h2` into its components or cases. Evaluate the numerical expressions using `at h2`. Conclude with `h2`. Conclude with `dotProduct_star_self_eq_zero.mp hnorm`.
-/
theorem det_ne_zero_of_add_conjTranspose {n : Type} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℂ) (h : P + Pᴴ = (2 : ℂ) • (1 : Matrix n n ℂ)) : P.det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  apply hv0

  have hquad : star v ⬝ᵥ ((P + Pᴴ) *ᵥ v) = 2 * (star v ⬝ᵥ v) := by
    rw [h]
    first
      | simp [smul_mulVec, dotProduct_smul, smul_eq_mul]
      | simp [Matrix.smul_mulVec_assoc, dotProduct_smul, smul_eq_mul]
      | simp [dotProduct_smul, smul_eq_mul]

  have hzero : star v ⬝ᵥ ((P + Pᴴ) *ᵥ v) = 0 := by
    have hstar : star v ᵥ* Pᴴ = star (P *ᵥ v) := (star_mulVec P v).symm
    rw [add_mulVec, dotProduct_add, dotProduct_mulVec (star v) Pᴴ v, hstar, hv]
    simp
  have hnorm : star v ⬝ᵥ v = 0 := by
    have h2 : (2 : ℂ) * (star v ⬝ᵥ v) = 0 := hquad.symm.trans hzero
    rcases mul_eq_zero.mp h2 with h2 | h2
    · norm_num at h2
    · exact h2
  exact dotProduct_star_self_eq_zero.mp hnorm

/- English proof (translation)
Take `⟨x1, x2⟩` from `x`. Take `⟨y1, y2⟩` from `y`. Apply the tactic sequence `rcases x1 with i | i <;> rcases x2 with j | j <;> rcases y1 with k | k <;> rcases y2 with l | l <;>`. Simplify using `[sameBlock, posIx, Fin.ext_iff]`.
-/
private lemma isLeft_ne_of_posIx_eq {p q : ℕ} (x y : Ix p q × Ix p q) (hx : ¬ sameBlock x.1 x.2)
    (hy : ¬ sameBlock y.1 y.2) (hne : y ≠ x) (h1 : posIx y.1 = posIx x.1)
    (h2 : posIx y.2 = posIx x.2) : x.1.isLeft ≠ y.1.isLeft := by
  obtain ⟨x1, x2⟩ := x
  obtain ⟨y1, y2⟩ := y
  rcases x1 with i | i <;> rcases x2 with j | j <;> rcases y1 with k | k <;> rcases y2 with l | l <;>
    simp_all [sameBlock, posIx, Fin.ext_iff]

/- English proof (translation)
Unfold `eigP`. Rewrite using `[if_neg hne, if_neg (Ne.symm hne)]`. Distinguish the cases in `h : posIx y.1 = posIx x.1 ∧ posIx y.2 = posIx x.2`. Establish `c1 : ¬ sameBlock y.1 y.2 ∧ posIx y.1 = posIx x.1 ∧ posIx y.2 = posIx x.2` using `⟨hy, h⟩`. Establish `c2 : ¬ sameBlock x.1 x.2 ∧ posIx x.1 = posIx y.1 ∧ posIx x.2 = posIx y.2` using `⟨hx, h.1.symm, h.2.symm⟩`.

Rewrite using `[if_pos c1, if_pos c2]`. Establish `hL` using `isLeft_ne_of_posIx_eq x y hx hy hne h.1 h.2`. Generalize the expression as in `x.1.isLeft = s at hL ⊢`. Generalize the expression as in `y.1.isLeft = t at hL ⊢`. Apply the tactic sequence `cases s <;> cases t <;> simp at hL ⊢`.

Establish `c1 : ¬ (¬ sameBlock y.1 y.2 ∧ posIx y.1 = posIx x.1 ∧ posIx y.2 = posIx x.2)` using `fun h' => h ⟨h'.2.1, h'.2.2⟩`. Establish `c2 : ¬ (¬ sameBlock x.1 x.2 ∧ posIx x.1 = posIx y.1 ∧ posIx x.2 = posIx y.2)` using `fun h' => h ⟨h'.2.1.symm, h'.2.2.symm⟩`. Rewrite using `[if_neg c1, if_neg c2]`. Simplify using the standard rewrite rules.
-/
private lemma eigP_add_star_eigP_eq_zero {p q : ℕ} (x y : Ix p q × Ix p q) (hx : ¬ sameBlock x.1 x.2)
    (hy : ¬ sameBlock y.1 y.2) (hne : y ≠ x) : eigP x y + star (eigP y x) = 0 := by
  unfold eigP
  rw [if_neg hne, if_neg (Ne.symm hne)]
  by_cases h : posIx y.1 = posIx x.1 ∧ posIx y.2 = posIx x.2
  · have c1 : ¬ sameBlock y.1 y.2 ∧ posIx y.1 = posIx x.1 ∧ posIx y.2 = posIx x.2 := ⟨hy, h⟩
    have c2 : ¬ sameBlock x.1 x.2 ∧ posIx x.1 = posIx y.1 ∧ posIx x.2 = posIx y.2 :=
      ⟨hx, h.1.symm, h.2.symm⟩
    rw [if_pos c1, if_pos c2]
    have hL := isLeft_ne_of_posIx_eq x y hx hy hne h.1 h.2
    generalize x.1.isLeft = s at hL ⊢
    generalize y.1.isLeft = t at hL ⊢
    cases s <;> cases t <;> simp at hL ⊢
  · have c1 : ¬ (¬ sameBlock y.1 y.2 ∧ posIx y.1 = posIx x.1 ∧ posIx y.2 = posIx x.2) :=
      fun h' => h ⟨h'.2.1, h'.2.2⟩
    have c2 : ¬ (¬ sameBlock x.1 x.2 ∧ posIx x.1 = posIx y.1 ∧ posIx x.2 = posIx y.2) :=
      fun h' => h ⟨h'.2.1.symm, h'.2.2.symm⟩
    rw [if_neg c1, if_neg c2]
    simp

/- English proof (translation)
Distinguish the cases in `hc : cd = ab`. Substitute `hc` using the available equality. Rewrite using `[if_pos rfl]`. Evaluate the numerical expressions using `[eigP]`. Rewrite using `[if_neg hc]`.

Conclude with `eigP_add_star_eigP_eq_zero ab.1 cd.1 ab.2 cd.2 (fun h => hc (Subtype.ext h))`.
-/
theorem eigenvectorMatrix_add_star {p q : ℕ} (ab cd : PIx p q) :
    eigP ab.1 cd.1 + star (eigP cd.1 ab.1) = if cd = ab then 2 else 0 := by
  by_cases hc : cd = ab
  · subst hc
    rw [if_pos rfl]
    norm_num [eigP]
  · rw [if_neg hc]
    exact eigP_add_star_eigP_eq_zero ab.1 cd.1 ab.2 cd.2 (fun h => hc (Subtype.ext h))

/- English proof (translation)
Introduce `p q`. Apply `det_ne_zero_of_add_conjTranspose` to reduce the goal to its premises. Use extensionality with `cd ab`. Simplify using `only [Matrix.add_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]`. Rewrite using `[eigenvectorMatrix_add_star]`.

Apply the tactic sequence `split_ifs <;> norm_num`.
-/
theorem det_eigenvectorMatrix_ne_zero :
    ∀ (p q : ℕ), (Matrix.of fun (cd ab : PIx p q) => eigP ab.1 cd.1).det ≠ 0 := by
  intro p q
  apply det_ne_zero_of_add_conjTranspose
  ext cd ab
  simp only [Matrix.add_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul]
  rw [eigenvectorMatrix_add_star]
  split_ifs <;> norm_num

end GlobalTheory.PolarU
