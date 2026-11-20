import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
import Formalism.FormalDegreeBessel.FinalG
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationContinuousOnInvertible
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed

open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal

noncomputable section

namespace Formalism.FourierDecayAlt.P.B2x4

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

section form
variable {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ)

/- English proof (translation)
Simplify using `only [herm, dotProduct, mulVec, bvec, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_mul, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `i _`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises.

Introduce `j _`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma herm_sum (u v : Fin m → ℂ) : ∑ j, herm H (bvec j) v * u j = herm H u v := by
  simp only [herm, dotProduct, mulVec, bvec, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  ring

/- English proof (translation)
Simplify using `only [herm, mulVec_add, dotProduct_add]`.
-/
lemma herm_add_left (u u' w : Fin m → ℂ) : herm H (u + u') w = herm H u w + herm H u' w := by
  simp only [herm, mulVec_add, dotProduct_add]

/- English proof (translation)
Simplify using `only [herm, mulVec_sub, dotProduct_sub]`.
-/
lemma herm_sub_left (u u' w : Fin m → ℂ) : herm H (u - u') w = herm H u w - herm H u' w := by
  simp only [herm, mulVec_sub, dotProduct_sub]

/- English proof (translation)
Simplify using `only [herm, mulVec_smul, dotProduct_smul, smul_eq_mul]`.
-/
lemma herm_smul_left (c : ℂ) (u w : Fin m → ℂ) : herm H (c • u) w = c * herm H u w := by
  simp only [herm, mulVec_smul, dotProduct_smul, smul_eq_mul]

/- English proof (translation)
Simplify using `only [herm, star_add, add_dotProduct]`.
-/
lemma herm_add_right (u w w' : Fin m → ℂ) : herm H u (w + w') = herm H u w + herm H u w' := by
  simp only [herm, star_add, add_dotProduct]

/- English proof (translation)
Simplify using `only [herm, star_sub, sub_dotProduct]`.
-/
lemma herm_sub_right (u w w' : Fin m → ℂ) : herm H u (w - w') = herm H u w - herm H u w' := by
  simp only [herm, star_sub, sub_dotProduct]

/- English proof (translation)
Simplify using `only [herm, star_smul, smul_dotProduct, smul_eq_mul]`.
-/
lemma herm_smul_right (c : ℂ) (u w : Fin m → ℂ) : herm H u (c • w) = star c * herm H u w := by
  simp only [herm, star_smul, smul_dotProduct, smul_eq_mul]

/- English proof (translation)
Unfold `herm`. Rewrite using `[← Matrix.star_dotProduct_star, star_star, star_mulVec, hH, ← dotProduct_mulVec]`.
-/
lemma herm_symm (hH : Hᴴ = H) (u w : Fin m → ℂ) : star (herm H u w) = herm H w u := by
  unfold herm
  rw [← Matrix.star_dotProduct_star, star_star, star_mulVec, hH, ← dotProduct_mulVec]

/- English proof (translation)
Simplify using `[herm, bvec, dotProduct, mulVec, Pi.single_apply]`.
-/
lemma herm_bvec (i j : Fin m) : herm H (bvec j) (bvec i) = H i j := by
  simp [herm, bvec, dotProduct, mulVec, Pi.single_apply]

/- English proof (translation)
Unfold `herm`. Rewrite using `[star_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec (star w) gᴴ]`.
-/
lemma herm_mulVec (g : Matrix (Fin m) (Fin m) ℂ) (u w : Fin m → ℂ) :
    herm H (g *ᵥ u) (g *ᵥ w) = herm (gᴴ * H * g) u w := by
  unfold herm
  rw [star_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec (star w) gᴴ]

/- English proof (translation)
Use `show gᴴ * H * g = H`. Use extensionality with `i j`. Rewrite using `[← herm_bvec (gᴴ * H * g), ← herm_mulVec, h, herm_bvec]`.
-/
lemma mem_UH_of_herm (g : Matrix (Fin m) (Fin m) ℂ)
    (h : ∀ u w, herm H (g *ᵥ u) (g *ᵥ w) = herm H u w) : g ∈ UH H := by
  show gᴴ * H * g = H
  ext i j
  rw [← herm_bvec (gᴴ * H * g), ← herm_mulVec, h, herm_bvec]

/- English proof (translation)
Establish `hev : herm H e v = 0` using `by rw [← herm_symm H hH v e, hve, star_zero]`. Simplify using `only [herm_add_left, herm_sub_left, herm_smul_left, herm_add_right, herm_sub_right, herm_smul_right, herm_symm H hH, hee, hve, hev]`. Take the linear combination `(herm H u e * herm H e w) * hb`.
-/
lemma heis_isom (hH : Hᴴ = H) (e v : Fin m → ℂ) (b : ℂ) (hee : herm H e e = 0) (hve : herm H v e = 0)
    (hb : b + star b + herm H v v = 0) (u w : Fin m → ℂ) :
    herm H (u - herm H u v • e + herm H u e • (v + b • e)) (w - herm H w v • e + herm H w e • (v + b • e)) =
      herm H u w := by
  have hev : herm H e v = 0 := by rw [← herm_symm H hH v e, hve, star_zero]
  simp only [herm_add_left, herm_sub_left, herm_smul_left, herm_add_right, herm_sub_right, herm_smul_right,
    herm_symm H hH, hee, hve, hev]
  linear_combination (herm H u e * herm H e w) * hb

end form

def lastI (k r' : ℕ) : Fin (2 * (1 + r') + k + 1) := ⟨2 * (1 + r') + k, by omega⟩

/- English proof (translation)
The claim follows from `(hpkFacts k r).1`.
-/
lemma Hpk_herm (k r : ℕ) : (Hpk k r)ᴴ = Hpk k r := (hpkFacts k r).1

/- English proof (translation)
Establish `hv : (eI k (1 + r') (a0 r')).val = 0` using `rfl`. Unfold `Hpk`. Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; omega)`.
-/
lemma Hpk_zero_row (k r' : ℕ) (j : Fin (2 * (1 + r') + k + 1)) :
    Hpk k (1 + r') (eI k (1 + r') (a0 r')) j = if j.val = 2 * (1 + r') + k then 1 else 0 := by
  have hv : (eI k (1 + r') (a0 r')).val = 0 := rfl
  unfold Hpk
  split_ifs <;> first | rfl | (exfalso; omega)

/- English proof (translation)
Rewrite using `[← herm_sum]`. Rewrite using `[Finset.sum_eq_single (lastI k r')]`. Rewrite using `[e0, herm_bvec, Hpk_zero_row, if_pos (show (lastI k r').val = 2 * (1 + r') + k from rfl), one_mul]`. Introduce `j _ hj`. Establish `: j.val ≠ 2 * (1 + r') + k` using `fun h => hj (Fin.ext h)`.

Rewrite using `[e0, herm_bvec, Hpk_zero_row, if_neg this, zero_mul]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
lemma hermitian_first_basis_right (k r' : ℕ) (u : Fin (2 * (1 + r') + k + 1) → ℂ) :
    herm (Hpk k (1 + r')) u (e0 k r') = u (lastI k r') := by
  rw [← herm_sum]
  rw [Finset.sum_eq_single (lastI k r')]
  · rw [e0, herm_bvec, Hpk_zero_row, if_pos (show (lastI k r').val = 2 * (1 + r') + k from rfl), one_mul]
  · intro j _ hj
    have : j.val ≠ 2 * (1 + r') + k := fun h => hj (Fin.ext h)
    rw [e0, herm_bvec, Hpk_zero_row, if_neg this, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Rewrite using `[← herm_symm _ (Hpk_herm k (1 + r')), hermitian_first_basis_right]`.
-/
lemma hermitian_form_base_vector_left (k r' : ℕ) (w : Fin (2 * (1 + r') + k + 1) → ℂ) :
    herm (Hpk k (1 + r')) (e0 k r') w = star (w (lastI k r')) := by
  rw [← herm_symm _ (Hpk_herm k (1 + r')), hermitian_first_basis_right]

/- English proof (translation)
Simplify using `only [e0, bvec, eI, a0, Pi.single_apply, Fin.ext_iff]`.
-/
lemma goodRowsProjector_apply_eq_sum (k r' : ℕ) (i : Fin (2 * (1 + r') + k + 1)) : e0 k r' i = if i.val = 0 then 1 else 0 := by
  simp only [e0, bvec, eI, a0, Pi.single_apply, Fin.ext_iff]

/- English proof (translation)
Unfold `liftVec lastI`. Rewrite using `[dif_neg (by simp only []; omega)]`.
-/
lemma liftVec_last (k r' : ℕ) (y : Fin (2 * r' + k + 1) → ℂ) : liftVec k 1 r' y (lastI k r') = 0 := by
  unfold liftVec lastI
  rw [dif_neg (by simp only []; omega)]

/- English proof (translation)
Use `symm`. Apply `Finset.sum_of_injOn (levPos k 1 r')` to reduce the goal to its premises. Introduce `a _ b _ hab`. Use `congrArg Fin.val hab` as an intermediate fact. Simplify using `only [levPos] at this`.

Conclude with `Fin.ext (by omega)`. Introduce `a _`. Conclude with `Finset.mem_coe.2 (Finset.mem_univ _)`. Introduce `p _ hp`. Apply `h` to reduce the goal to its premises.

Introduce `hc`. Apply `hp` to reduce the goal to its premises. Use `⟨⟨p.val - 1, by omega⟩, Finset.mem_coe.2 (Finset.mem_univ _), ?_⟩` and prove the remaining obligations. Apply `Fin.ext` to reduce the goal to its premises. Simplify using `only [levPos]`.

Use linear arithmetic over natural numbers and integers. Introduce `_ _`. Both sides reduce to the same expression.
-/
lemma sum_lift (k r' : ℕ) (F : Fin (2 * (1 + r') + k + 1) → ℂ)
    (h : ∀ p, ¬ (1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1) → F p = 0) :
    ∑ p, F p = ∑ j, F (levPos k 1 r' j) := by
  symm
  apply Finset.sum_of_injOn (levPos k 1 r')
  · intro a _ b _ hab
    have := congrArg Fin.val hab
    simp only [levPos] at this
    exact Fin.ext (by omega)
  · intro a _; exact Finset.mem_coe.2 (Finset.mem_univ _)
  · intro p _ hp
    apply h
    intro hc
    apply hp
    refine ⟨⟨p.val - 1, by omega⟩, Finset.mem_coe.2 (Finset.mem_univ _), ?_⟩
    apply Fin.ext
    simp only [levPos]
    omega
  · intro _ _; rfl

/- English proof (translation)
Use `j.isLt` as an intermediate fact. Unfold `liftVec levPos`. Rewrite using `[dif_pos (by simp only []; omega)]`. Use `congr 1`.
-/
lemma liftVec_levPos (k r' : ℕ) (y : Fin (2 * r' + k + 1) → ℂ) (j : Fin (2 * r' + k + 1)) :
    liftVec k 1 r' y (levPos k 1 r' j) = y j := by
  have := j.isLt
  unfold liftVec levPos
  rw [dif_pos (by simp only []; omega)]
  congr 1

/- English proof (translation)
Unfold `liftVec`. Rewrite using `[dif_neg hp]`.
-/
lemma liftVec_out (k r' : ℕ) (y : Fin (2 * r' + k + 1) → ℂ) (p : Fin (2 * (1 + r') + k + 1))
    (hp : ¬ (1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1)) : liftVec k 1 r' y p = 0 := by
  unfold liftVec
  rw [dif_neg hp]

/- English proof (translation)
Establish `e1 : (levPos k 1 r' i = levPos k 1 r' j) ↔ i.val = j.val`. Simplify using `only [levPos, Fin.ext_iff]`. Use linear arithmetic over natural numbers and integers. Establish `e2 : (i = j) ↔ i.val = j.val` using `Fin.ext_iff`. Establish `hi : (levPos k 1 r' i).val = i.val + 1` using `rfl`.

Establish `hj : (levPos k 1 r' j).val = j.val + 1` using `rfl`. Unfold `Hpk`. Simplify using `only [e1, e2]`. Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; omega)`.
-/
lemma Hpk_levPos (k r' : ℕ) (i j : Fin (2 * r' + k + 1)) :
    Hpk k (1 + r') (levPos k 1 r' i) (levPos k 1 r' j) = Hpk k r' i j := by
  have e1 : (levPos k 1 r' i = levPos k 1 r' j) ↔ i.val = j.val := by
    simp only [levPos, Fin.ext_iff]; omega
  have e2 : (i = j) ↔ i.val = j.val := Fin.ext_iff
  have hi : (levPos k 1 r' i).val = i.val + 1 := rfl
  have hj : (levPos k 1 r' j).val = j.val + 1 := rfl
  unfold Hpk
  simp only [e1, e2]
  split_ifs <;> first | rfl | (exfalso; omega)

/- English proof (translation)
Simplify using `only [herm, dotProduct, mulVec, Pi.star_apply]`. Rewrite using `[sum_lift]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `i _`. Rewrite using `[liftVec_levPos, sum_lift]`.

Use `congr 1`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `j _`. Rewrite using `[liftVec_levPos, Hpk_levPos]`. Introduce `p hp`.

Rewrite using `[liftVec_out k r' y p hp, mul_zero]`. Introduce `p hp`. Rewrite using `[liftVec_out k r' y' p hp, star_zero, zero_mul]`.
-/
lemma herm_lift (k r' : ℕ) (y y' : Fin (2 * r' + k + 1) → ℂ) :
    herm (Hpk k (1 + r')) (liftVec k 1 r' y) (liftVec k 1 r' y') = herm (Hpk k r') y y' := by
  simp only [herm, dotProduct, mulVec, Pi.star_apply]
  rw [sum_lift]
  · apply Finset.sum_congr rfl; intro i _
    rw [liftVec_levPos, sum_lift]
    · congr 1
      apply Finset.sum_congr rfl; intro j _
      rw [liftVec_levPos, Hpk_levPos]
    · intro p hp; rw [liftVec_out k r' y p hp, mul_zero]
  · intro p hp; rw [liftVec_out k r' y' p hp, star_zero, zero_mul]

/- English proof (translation)
Establish `h` using `herm_symm _ (Hpk_herm k r') y y`. Establish `him : (herm (Hpk k r') y y).im = 0`. Use `congrArg Complex.im h` as an intermediate fact. Simplify using `only [Complex.star_def, Complex.conj_im] at this`. Combine the linear equalities and inequalities to obtain the conclusion.

Apply `Complex.ext` to reduce the goal to its premises. Simplify using `[hb]`. Simplify using `[hb, him]`.
-/
lemma hb_rel (k r' : ℕ) (y : Fin (2 * r' + k + 1) → ℂ) (s : ℝ) :
    hb k r' y s + star (hb k r' y s) + herm (Hpk k r') y y = 0 := by
  have h := herm_symm _ (Hpk_herm k r') y y
  have him : (herm (Hpk k r') y y).im = 0 := by
    have := congrArg Complex.im h
    simp only [Complex.star_def, Complex.conj_im] at this
    linarith
  apply Complex.ext
  · simp [hb]
  · simp [hb, him]

/- English proof (translation)
Introduce `k r' v u b`. Use extensionality with `i`. Simplify using `only [heisG, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]`. Establish `h1 : ∀ (w φ : Fin (2 * (1 + r') + k + 1) → ℂ), (Matrix.vecMulVec w φ *ᵥ u) i = (∑ j, φ j * u j) * w i`. Introduce `w φ`.

Simplify using `only [mulVec, dotProduct, vecMulVec_apply, Finset.sum_mul]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `j _`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h1, h1, herm_sum, herm_sum]`.

Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]`.
-/
theorem heisAct : HeisAct := by
  intro k r' v u b
  ext i
  simp only [heisG, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul]
  have h1 : ∀ (w φ : Fin (2 * (1 + r') + k + 1) → ℂ), (Matrix.vecMulVec w φ *ᵥ u) i = (∑ j, φ j * u j) * w i := by
    intro w φ
    simp only [mulVec, dotProduct, vecMulVec_apply, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro j _; ring
  rw [h1, h1, herm_sum, herm_sum]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]

/- English proof (translation)
Simplify using `only [heisG, Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply, vecMulVec_apply, hermitian_first_basis_right, Pi.add_apply, Pi.smul_apply, smul_eq_mul, bvec, Pi.single_apply, lastI, Fin.ext_iff]`. Use `congr 2`. Simplify using `only [eq_comm]`.
-/
lemma heisG_apply (k r' : ℕ) (v : Fin (2 * (1 + r') + k + 1) → ℂ) (b : ℂ) (i j : Fin (2 * (1 + r') + k + 1)) :
    heisG k r' v b i j = (if i = j then 1 else 0) - e0 k r' i * herm (Hpk k (1 + r')) (bvec j) v +
      (v i + b * e0 k r' i) * (if j.val = 2 * (1 + r') + k then 1 else 0) := by
  simp only [heisG, Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply, vecMulVec_apply, hermitian_first_basis_right,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, bvec, Pi.single_apply, lastI, Fin.ext_iff]
  congr 2
  simp only [eq_comm]

/- English proof (translation)
Introduce `k r' x`. Take `⟨y, s⟩` from `x`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Apply `mem_UH_of_herm` to reduce the goal to its premises. Introduce `u w`.

Simplify using `only [heis0]`. Rewrite using `[heisAct, heisAct]`. Apply `heis_isom _ (Hpk_herm k (1 + r'))` to reduce the goal to its premises. Rewrite using `[hermitian_first_basis_right, goodRowsProjector_apply_eq_sum]`. Simplify using `[lastI]`.

Rewrite using `[hermitian_first_basis_right, liftVec_last]`. Rewrite using `[herm_lift]`. Conclude with `hb_rel k r' y s`. Introduce `a i hai`. Establish `ha` using `a.isLt`.

Simplify using `only [heis0]`. Establish `hv : (eI k (1 + r') a).val = a.val` using `rfl`. Establish `hz : (if (eI k (1 + r') a).val = 2 * (1 + r') + k then (1 : ℂ) else 0) = 0` using `if_neg (by omega)`. Rewrite using `[heisG_apply, hz, mul_zero, add_zero, goodRowsProjector_apply_eq_sum]`. Distinguish the cases in `hi : i.val = 0`.

Establish `: bvec (eI k (1 + r') a) = e0 k r'`. Unfold `e0`. Use `congr 1`. Apply `Fin.ext` to reduce the goal to its premises. Simplify using `only [eI, a0]`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[this, hermitian_form_base_vector_left, liftVec_last]`. Simplify using the standard rewrite rules. Rewrite using `[if_neg hi]`. Simplify using the standard rewrite rules.

Introduce `i j h1 h2 h3`. Simplify using `only [heis0]`. Establish `hz : (if j.val = 2 * (1 + r') + k then (1 : ℂ) else 0) = 0` using `if_neg (by omega)`. Establish `hz2 : (if i.val = 0 then (1 : ℂ) else 0) = 0` using `if_neg (by omega)`. Rewrite using `[heisG_apply, hz, mul_zero, add_zero, goodRowsProjector_apply_eq_sum, hz2]`.

Simplify using the standard rewrite rules.
-/
theorem heisMem : HeisMem := by
  intro k r' x
  obtain ⟨y, s⟩ := x
  refine ⟨?_, ?_, ?_⟩
  · apply mem_UH_of_herm
    intro u w
    simp only [heis0]
    rw [heisAct, heisAct]
    apply heis_isom _ (Hpk_herm k (1 + r'))
    · rw [hermitian_first_basis_right, goodRowsProjector_apply_eq_sum]; simp [lastI]
    · rw [hermitian_first_basis_right, liftVec_last]
    · rw [herm_lift]; exact hb_rel k r' y s
  · intro a i hai
    have ha := a.isLt
    simp only [heis0]
    have hv : (eI k (1 + r') a).val = a.val := rfl
    have hz : (if (eI k (1 + r') a).val = 2 * (1 + r') + k then (1 : ℂ) else 0) = 0 := if_neg (by omega)
    rw [heisG_apply, hz, mul_zero, add_zero, goodRowsProjector_apply_eq_sum]
    by_cases hi : i.val = 0
    · have : bvec (eI k (1 + r') a) = e0 k r' := by
        unfold e0; congr 1; apply Fin.ext; simp only [eI, a0]; omega
      rw [this, hermitian_form_base_vector_left, liftVec_last]; simp
    · rw [if_neg hi]; simp
  · intro i j h1 h2 h3
    simp only [heis0]
    have hz : (if j.val = 2 * (1 + r') + k then (1 : ℂ) else 0) = 0 := if_neg (by omega)
    have hz2 : (if i.val = 0 then (1 : ℂ) else 0) = 0 := if_neg (by omega)
    rw [heisG_apply, hz, mul_zero, add_zero, goodRowsProjector_apply_eq_sum, hz2]; simp

end Formalism.FourierDecayAlt.P.B2x4

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

/- English proof (translation)
Introduce `h1 h2 h3 k r z hz hT`. Conclude with `h1 k r _ (h2 k r z) (h3 k r z hz hT)`.
-/
theorem weyl_haar_from_compact : Formalism.FourierDecayAlt.B2.HaarWFromCompact := by
  intro h1 h2 h3 k r z hz hT
  exact h1 k r _ (h2 k r z) (h3 k r z hz hT)

/- English proof (translation)
Introduce `hCC hN hW hK hU`. Establish `raw : ConjInvRaw`. Introduce `k r z μN hz hT hμ h hh`. Conclude with `hCC k r (Nset k r) (UWset k r z) μN (hN k r) (hW k r z) (hK k r z hz hT) (fun a ha u hu => (hU k r z hz a ha u hu).1) hμ h hh`. Use `⟨raw, ?_⟩` and prove the remaining obligations.

Introduce `k r Wp Wq _ _ _ _ D h₀ hh`. Break down `hh with hh | hh` into its components or cases. Conclude with `raw k r D.z D.μN D.z_mem D.T_pos D.haarN h₀ hh`. Conclude with `raw k r D.z' D.μN D.z'_mem D.T'_pos D.haarN h₀ hh`.
-/
theorem conjugation_invariance_of_parts : Formalism.FourierDecayAlt.B2.AssembleConjInv := by
  intro hCC hN hW hK hU
  have raw : ConjInvRaw := by
    intro k r z μN hz hT hμ h hh
    exact hCC k r (Nset k r) (UWset k r z) μN (hN k r) (hW k r z) (hK k r z hz hT)
      (fun a ha u hu => (hU k r z hz a ha u hu).1) hμ h hh
  refine ⟨raw, ?_⟩
  intro k r Wp Wq _ _ _ _ D h₀ hh
  rcases hh with hh | hh
  · exact raw k r D.z D.μN D.z_mem D.T_pos D.haarN h₀ hh
  · exact raw k r D.z' D.μN D.z'_mem D.T'_pos D.haarN h₀ hh

/- English proof (translation)
The claim follows from `conjugation_invariance_of_parts compact_subgroup_conjugation hN hW hK uWNormal`.
-/
theorem B2x4.conjInv_of (hN : ClosedN) (hW : ClosedW) (hK : CompactW) : ConjInvRaw ∧ ConjInvAll :=
  conjugation_invariance_of_parts compact_subgroup_conjugation hN hW hK uWNormal

/- English proof (translation)
The claim follows from `(B2x4.conjInv_of unipotent_radical_closed weyl_subgroup_closed weyl_subgroup_compact).1`.
-/
theorem b2_conjInvRaw_proof : Formalism.FourierDecayAlt.B2.ConjInvRaw :=
  (B2x4.conjInv_of unipotent_radical_closed weyl_subgroup_closed weyl_subgroup_compact).1

/- English proof (translation)
The claim follows from `(B2x4.conjInv_of unipotent_radical_closed weyl_subgroup_closed weyl_subgroup_compact).2`.
-/
theorem conjugation_invariance_every_setting : Formalism.FourierDecayAlt.B2.ConjInvAll :=
  (B2x4.conjInv_of unipotent_radical_closed weyl_subgroup_closed weyl_subgroup_compact).2

/- English proof (translation)
The claim follows from `B2x4.heisAct`.
-/
theorem heisenberg_action_formula : Formalism.FourierDecayAlt.B2.HeisAct := B2x4.heisAct

/- English proof (translation)
The claim follows from `B2x4.heisMem`.
-/
theorem heisenberg_mem_unipotent : Formalism.FourierDecayAlt.B2.HeisMem := B2x4.heisMem

end Formalism.FourierDecayAlt.P
