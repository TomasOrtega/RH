import Formalism.HermitianCurvature.StatementWd
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PositionInsertionDiagonalCompat
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TransferMatrixFactorization
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DiagScalarCommuteOfEntries

namespace Formalism.FourierDecayAlt.P.Wd10

open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd

section Kap

variable {K S : Type} [Field K]

def gq (l : Letter K S) (y : K) : K :=
  if l.plus then (y - l.pt + 1) / (y - l.pt) else (l.pt - y) / (l.pt - y - 1)

def hp (l : Letter K S) (Y : K) : K :=
  if l.plus then (Y - l.pt) / (Y - l.pt - 1) else (Y - l.pt) / (Y - l.pt + 1)

def fac (l l' : Letter K S) : K :=
  if l.plus = l'.plus then 1 else 1 - ((l.pt - l'.pt + (if l.plus then 1 else -1)) ^ 2)⁻¹

/- English proof (translation)
Simplify using `only [qw, gq]`. Apply the tactic sequence `split_ifs <;> rfl`.
-/
theorem qw_cons (q : K → K) (l : Letter K S) (w : List (Letter K S)) (y : K) :
    qw q (l :: w) y = qw q w y * gq l y := by
  simp only [qw, gq]
  split_ifs <;> rfl

/- English proof (translation)
Simplify using `only [ph, hp]`. Apply the tactic sequence `split_ifs <;> rfl`.
-/
theorem ph_cons (l : Letter K S) (L : List (Letter K S)) (Y : K) :
    ph (l :: L) Y = ph L Y * hp l Y := by
  simp only [ph, hp]
  split_ifs <;> rfl

/- English proof (translation)
Take `⟨p, s, a⟩` from `l`. Take `⟨p', s', b⟩` from `l'`. Apply the tactic sequence `cases p <;> cases p' <;>`. Apply the tactic sequence `simp only [gq, hp, fac, ypt, dl, RegL, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte] at hr hg ⊢ <;>`. Apply the tactic sequence `rw [div_ne_zero_iff] at hg <;> obtain ⟨h1, h2⟩ := hg`.

Establish `e1 : a - 1 - b ≠ 0` using `fun h => h1 (by linear_combination -h)`. Establish `e2 : a - 1 - b + 1 ≠ 0` using `fun h => h2 (by linear_combination -h)`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `e1 : a - 1 - b - 1 ≠ 0` using `fun h => hr (by linear_combination h)`.

Establish `e3 : a - b + -1 ≠ 0` using `fun h => h2 (by linear_combination h)`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `e1 : a + 1 - b ≠ 0` using `fun h => h2 (by linear_combination -h)`. Establish `e2 : a + 1 - b + 1 ≠ 0` using `fun h => hr (by linear_combination -h)`.

Establish `e3 : a - b + 1 ≠ 0` using `fun h => h2 (by linear_combination -h)`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `e1 : a + 1 - b - 1 ≠ 0` using `fun h => h2 (by linear_combination h)`. Establish `e2 : a + 1 - b ≠ 0` using `fun h => h1 (by linear_combination h)`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fac_eq (l l' : Letter K S) (hr : RegL l' (dl l).pt) (hg : gq l' (ypt l) ≠ 0) :
    gq l' (ypt l) / hp l' (dl l).pt = fac l l' := by
  obtain ⟨p, s, a⟩ := l
  obtain ⟨p', s', b⟩ := l'
  cases p <;> cases p' <;>
    simp only [gq, hp, fac, ypt, dl, RegL, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte] at hr hg ⊢ <;>
    rw [div_ne_zero_iff] at hg <;> obtain ⟨h1, h2⟩ := hg
  ·
    have e1 : a - 1 - b ≠ 0 := fun h => h1 (by linear_combination -h)
    have e2 : a - 1 - b + 1 ≠ 0 := fun h => h2 (by linear_combination -h)
    field_simp
    ring
  ·
    have e1 : a - 1 - b - 1 ≠ 0 := fun h => hr (by linear_combination h)
    have e3 : a - b + -1 ≠ 0 := fun h => h2 (by linear_combination h)
    field_simp
    ring
  ·
    have e1 : a + 1 - b ≠ 0 := fun h => h2 (by linear_combination -h)
    have e2 : a + 1 - b + 1 ≠ 0 := fun h => hr (by linear_combination -h)
    have e3 : a - b + 1 ≠ 0 := fun h => h2 (by linear_combination -h)
    field_simp
    ring
  ·
    have e1 : a + 1 - b - 1 ≠ 0 := fun h => h2 (by linear_combination h)
    have e2 : a + 1 - b ≠ 0 := fun h => h1 (by linear_combination h)
    field_simp
    ring

/- English proof (translation)
The claim follows from `| [], _, _ => by simp [ph] | l' :: L, hr, hq => by have hr1 : RegL l' (dl l).pt := hr l' (by simp) have hr2 : Reg L (dl l).pt := fun x hx => hr x (by simp [hx]) rw [List.cons_append, qw_cons] at hq have hq1 := left_ne_zero_of_mul hq have hq2 := right_ne_zero_of_mul hq rw [List.co …`.
-/
theorem kap_step (q : K → K) (w : List (Letter K S)) (l : Letter K S) :
    ∀ L : List (Letter K S), Reg L (dl l).pt → qw q (L ++ w) (ypt l) ≠ 0 →
      qw q (L ++ w) (ypt l) / ph L (dl l).pt = qw q w (ypt l) * (L.map fun l' => fac l l').prod
  | [], _, _ => by simp [ph]
  | l' :: L, hr, hq => by
    have hr1 : RegL l' (dl l).pt := hr l' (by simp)
    have hr2 : Reg L (dl l).pt := fun x hx => hr x (by simp [hx])
    rw [List.cons_append, qw_cons] at hq
    have hq1 := left_ne_zero_of_mul hq
    have hq2 := right_ne_zero_of_mul hq
    rw [List.cons_append, qw_cons, ph_cons, mul_div_mul_comm, kap_step q w l L hr2 hq1,
      fac_eq l l' hr1 hq2, List.map_cons, List.prod_cons]
    ring

/- English proof (translation)
Introduce `l hl` and use `h l (List.mem_append.2 (Or.inl hl))`.
-/
theorem reg_left {L w : List (Letter K S)} {Y : K} (h : Reg (L ++ w) Y) : Reg L Y :=
  fun l hl => h l (List.mem_append.2 (Or.inl hl))

/- English proof (translation)
The claim follows from `| [], _ => rfl | l :: L, h => by obtain ⟨h1, h2, h3⟩ := h rw [kap, kapF, mul_div_assoc, kap_step q w l L (reg_left h1) h2, kap_eq q w L h3, mul_assoc] rfl`.
-/
theorem kap_eq (q : K → K) (w : List (Letter K S)) :
    ∀ L : List (Letter K S), DualOK q w L → kap q w L = kapF q w L
  | [], _ => rfl
  | l :: L, h => by
    obtain ⟨h1, h2, h3⟩ := h
    rw [kap, kapF, mul_div_assoc, kap_step q w l L (reg_left h1) h2, kap_eq q w L h3, mul_assoc]
    rfl

end Kap

section Dual

variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]

/- English proof (translation)
Introduce `_ _` and use `Commute.one_right _`.
-/
theorem free_one (a : S) : FreeOf a (1 : SlopeTestRemainingChoices S A) := fun _ _ => Commute.one_right _

/- English proof (translation)
Introduce `_ _` and use `Commute.zero_right _`.
-/
theorem free_zero (a : S) : FreeOf a (0 : SlopeTestRemainingChoices S A) := fun _ _ => Commute.zero_right _

/- English proof (translation)
Introduce `i j` and use `(hx i j).mul_right (hy i j)`.
-/
theorem free_mul {a : S} {x y : SlopeTestRemainingChoices S A} (hx : FreeOf a x) (hy : FreeOf a y) : FreeOf a (x * y) :=
  fun i j => (hx i j).mul_right (hy i j)

/- English proof (translation)
Introduce `i j` and use `(hx i j).neg_right`.
-/
theorem free_neg {a : S} {x : SlopeTestRemainingChoices S A} (hx : FreeOf a x) : FreeOf a (-x) :=
  fun i j => (hx i j).neg_right

/- English proof (translation)
Introduce `i j` and use `(hx i j).add_right (hy i j)`.
-/
theorem free_add {a : S} {x y : SlopeTestRemainingChoices S A} (hx : FreeOf a x) (hy : FreeOf a y) : FreeOf a (x + y) :=
  fun i j => (hx i j).add_right (hy i j)

/- English proof (translation)
Introduce `i j` and use `(hx i j).smul_right c`.
-/
theorem free_smul {a : S} {x : SlopeTestRemainingChoices S A} (c : K) (hx : FreeOf a x) : FreeOf a (c • x) :=
  fun i j => (hx i j).smul_right c

/- English proof (translation)
Introduce `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j`. Conclude with `free_zero a`. Conclude with `free_one a`. Conclude with `free_neg (free_one a)`.

Conclude with `free_zero a`.
-/
theorem freeOf_J_matrix (a : S) : FreeOf2 a (YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A)) := by
  intro i j
  fin_cases i <;> fin_cases j
  · exact free_zero a
  · exact free_one a
  · exact free_neg (free_one a)
  · exact free_zero a

/- English proof (translation)
Introduce `i j`. Rewrite using `[Matrix.mul_apply]`. Conclude with `Finset.sum_induction _ (FreeOf a) (fun _ _ => free_add) (free_zero a) (fun k _ => free_mul (hM i k) (hN k j))`.
-/
theorem freeOf2_mul {a : S} {M N : M2 (SlopeTestRemainingChoices S A)} (hM : FreeOf2 a M) (hN : FreeOf2 a N) :
    FreeOf2 a (M * N) := by
  intro i j
  rw [Matrix.mul_apply]
  exact Finset.sum_induction _ (FreeOf a) (fun _ _ => free_add) (free_zero a)
    (fun k _ => free_mul (hM i k) (hN k j))

/- English proof (translation)
Introduce `i j` and use `hM j i`.
-/
theorem freeOf_matrix_transpose {a : S} {M : M2 (SlopeTestRemainingChoices S A)} (hM : FreeOf2 a M) : FreeOf2 a Mᵀ :=
  fun i j => hM j i

/- English proof (translation)
Introduce `i j` and use `free_smul c (hM i j)`.
-/
theorem freeOf_matrix_smul {a : S} {M : M2 (SlopeTestRemainingChoices S A)} (c : K) (hM : FreeOf2 a M) : FreeOf2 a (c • M) :=
  fun i j => free_smul c (hM i j)

/- English proof (translation)
Introduce `i j` and use `free_neg (hM i j)`.
-/
theorem freeOf_matrix_neg {a : S} {M : M2 (SlopeTestRemainingChoices S A)} (hM : FreeOf2 a M) : FreeOf2 a (-M) :=
  fun i j => free_neg (hM i j)

/- English proof (translation)
Simplify using `only [d0, Matrix.diagonal_mul_diagonal]`.
-/
theorem diagScalar_mul (x y : SlopeTestRemainingChoices S A) : d0 (x * y) = d0 x * d0 y := by
  simp only [d0, Matrix.diagonal_mul_diagonal]

/- English proof (translation)
Simplify using `only [d0, Matrix.diagonal_mul]`.
-/
theorem diagScalar_mul_apply (x : SlopeTestRemainingChoices S A) (M : M2 (SlopeTestRemainingChoices S A)) (i j : Fin 2) : (d0 x * M) i j = x * M i j := by
  simp only [d0, Matrix.diagonal_mul]

/- English proof (translation)
Simplify using `only [d0, Matrix.mul_diagonal]`.
-/
theorem mul_diagScalar_apply (x : SlopeTestRemainingChoices S A) (M : M2 (SlopeTestRemainingChoices S A)) (i j : Fin 2) : (M * d0 x) i j = M i j * x := by
  simp only [d0, Matrix.mul_diagonal]

/- English proof (translation)
Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Rewrite using `[mul_diagScalar_apply, diagScalar_mul_apply]`. Conclude with `(hx i j).eq`.
-/
theorem partial_flip_commute_diagScalar_of_free {a : S} {x : SlopeTestRemainingChoices S A} (hx : FreeOf a x) : Q0 a * d0 x = d0 x * Q0 a := by
  refine Matrix.ext fun i j => ?_
  rw [mul_diagScalar_apply, diagScalar_mul_apply]
  exact (hx i j).eq

/- English proof (translation)
Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Rewrite using `[mul_diagScalar_apply, diagScalar_mul_apply]`. Conclude with `(hx j i).eq`.
-/
theorem flip_commute_diagScalar_of_free {a : S} {x : SlopeTestRemainingChoices S A} (hx : FreeOf a x) : P0 a * d0 x = d0 x * P0 a := by
  refine Matrix.ext fun i j => ?_
  rw [mul_diagScalar_apply, diagScalar_mul_apply]
  exact (hx j i).eq

/- English proof (translation)
Simplify using `only [Rht0, smul_mul_assoc, mul_smul_comm, sub_mul, mul_sub, one_mul, mul_one, partial_flip_commute_diagScalar_of_free hx]`.
-/
theorem Rht0_comm {a : S} {x : SlopeTestRemainingChoices S A} (hx : FreeOf a x) (d : K) :
    Rht0 a d * d0 x = d0 x * Rht0 a d := by
  simp only [Rht0, smul_mul_assoc, mul_smul_comm, sub_mul, mul_sub, one_mul, mul_one, partial_flip_commute_diagScalar_of_free hx]

/- English proof (translation)
Simplify using `only [Rh0, smul_mul_assoc, mul_smul_comm, sub_mul, mul_sub, one_mul, mul_one, flip_commute_diagScalar_of_free hx]`.
-/
theorem Rh0_comm {a : S} {x : SlopeTestRemainingChoices S A} (hx : FreeOf a x) (d : K) :
    Rh0 a d * d0 x = d0 x * Rh0 a d := by
  simp only [Rh0, smul_mul_assoc, mul_smul_comm, sub_mul, mul_sub, one_mul, mul_one, flip_commute_diagScalar_of_free hx]

/- English proof (translation)
Simplify using `only [ins, Finset.sum_mul, Finset.mul_sum, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[mul_assoc, h i j, mul_smul_comm, ← mul_assoc, ← mul_assoc, (hx i j).eq]`.
-/
theorem ins_twine {a : S} {M M' : M2 (SlopeTestRemainingChoices S A)} {x : SlopeTestRemainingChoices S A} {c : K} (hx : FreeOf a x)
    (h : ∀ i j, M i j * x = c • (x * M' i j)) : ins a M * x = c • (x * ins a M') := by
  simp only [ins, Finset.sum_mul, Finset.mul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [mul_assoc, h i j, mul_smul_comm, ← mul_assoc, ← mul_assoc, (hx i j).eq]

/- English proof (translation)
Establish `e` using `congrFun (congrFun h i) j`. Rewrite `e` using `[mul_diagScalar_apply, Matrix.smul_apply, diagScalar_mul_apply]`. Then use the resulting hypothesis.
-/
theorem twine_entries {M M' : M2 (SlopeTestRemainingChoices S A)} {x : SlopeTestRemainingChoices S A} {c : K}
    (h : M * d0 x = c • (d0 x * M')) (i j : Fin 2) : M i j * x = c • (x * M' i j) := by
  have e := congrFun (congrFun h i) j
  rwa [mul_diagScalar_apply, Matrix.smul_apply, diagScalar_mul_apply] at e

/- English proof (translation)
Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [YangianSpanCharacter.T.J]`.
-/
theorem J_conj : (YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A))ᴴ = (YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A))ᵀ := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [YangianSpanCharacter.T.J]

/- English proof (translation)
Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [YangianSpanCharacter.T.J]`.
-/
theorem Jt_conj : ((YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A))ᵀ)ᴴ = YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A) := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [YangianSpanCharacter.T.J]

/- English proof (translation)
Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [YangianSpanCharacter.T.J]`.
-/
theorem J_entry_comm (x : SlopeTestRemainingChoices S A) (i j : Fin 2) : Commute x (YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A) i j) := by
  fin_cases i <;> fin_cases j <;> simp [YangianSpanCharacter.T.J]

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `h`. Rewrite `h1` using `[List.map_cons, List.nodup_cons]`. Rewrite `h3` using `[List.pairwise_cons]`. Conclude with `⟨⟨h1.2, fun l' hl' => h2 l' (List.mem_cons_of_mem _ hl'), h3.2⟩, h1.1, h2 l List.mem_cons_self, h3.1⟩`.
-/
theorem good_cons {l : Letter K S} {W : List (Letter K S)} (h : Good (l :: W)) :
    Good W ∧ l.intersection_update_fsHerm_neg_one ∉ W.map Letter.intersection_update_fsHerm_neg_one ∧ star l.pt = l.pt ∧ Reg W l.pt := by
  obtain ⟨h1, h2, h3⟩ := h
  rw [List.map_cons, List.nodup_cons] at h1
  rw [List.pairwise_cons] at h3
  exact ⟨⟨h1.2, fun l' hl' => h2 l' (List.mem_cons_of_mem _ hl'), h3.2⟩, h1.1,
    h2 l List.mem_cons_self, h3.1⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨h l List.mem_cons_self, fun x hx => h x (List.mem_cons_of_mem _ hx)⟩`.
-/
theorem reg_cons {l : Letter K S} {W : List (Letter K S)} {Y : K} (h : Reg (l :: W) Y) :
    RegL l Y ∧ Reg W Y :=
  ⟨h l List.mem_cons_self, fun x hx => h x (List.mem_cons_of_mem _ hx)⟩

/- English proof (translation)
Take `⟨p, s, a⟩` from `l`. Apply the tactic sequence `cases p <;> simp only [hp, dl, RegL, Bool.false_eq_true, ↓reduceIte] at h1 h2 ⊢`. Conclude with `div_ne_zero (fun h => h2 (by linear_combination h)) (fun h => h1 (by linear_combination -h))`. Conclude with `div_ne_zero (fun h => h2 (by linear_combination -h)) (fun h => h1 (by linear_combination h))`.
-/
theorem hp_ne {l : Letter K S} {Y : K} (h1 : RegL l Y) (h2 : RegL (dl l) Y) : hp l Y ≠ 0 := by
  obtain ⟨p, s, a⟩ := l
  cases p <;> simp only [hp, dl, RegL, Bool.false_eq_true, ↓reduceIte] at h1 h2 ⊢
  · exact div_ne_zero (fun h => h2 (by linear_combination h)) (fun h => h1 (by linear_combination -h))
  · exact div_ne_zero (fun h => h2 (by linear_combination -h)) (fun h => h1 (by linear_combination h))

/- English proof (translation)
The claim follows from `| [], _, _, _ => by simp [ph] | l :: L, Y, h1, h2 => by rw [ph_cons] rw [List.map_cons] at h2 exact mul_ne_zero (ph_ne L Y (reg_cons h1).2 (reg_cons h2).2) (hp_ne (reg_cons h1).1 (reg_cons h2).1)`.
-/
theorem ph_ne : ∀ (L : List (Letter K S)) (Y : K), Reg L Y → Reg (L.map dl) Y → ph L Y ≠ 0
  | [], _, _, _ => by simp [ph]
  | l :: L, Y, h1, h2 => by
    rw [ph_cons]
    rw [List.map_cons] at h2
    exact mul_ne_zero (ph_ne L Y (reg_cons h1).2 (reg_cons h2).2) (hp_ne (reg_cons h1).1 (reg_cons h2).1)

/- English proof (translation)
The claim follows from `| [], _ => free_one c | l :: L, h => by rw [List.cons_append, List.map_cons, List.mem_cons, not_or] at h have hT := (hWF K A S QQ (L ++ w) c h.2).2 rw [Ps] refine free_mul ?_ (Ps_free hIF hWF QQ q w c L h.2) split · exact (hIF K A S l.intersection_update_fsHerm_neg_one _).1 c h.1 …`.
-/
theorem Ps_free (hIF : InsFree) (hWF : WordFree) (QQ : K → M2 A) (q : K → K) (w : List (Letter K S))
    (c : S) : ∀ L : List (Letter K S), c ∉ (L ++ w).map Letter.intersection_update_fsHerm_neg_one → FreeOf c (Ps QQ q w L)
  | [], _ => free_one c
  | l :: L, h => by
    rw [List.cons_append, List.map_cons, List.mem_cons, not_or] at h
    have hT := (hWF K A S QQ (L ++ w) c h.2).2
    rw [Ps]
    refine free_mul ?_ (Ps_free hIF hWF QQ q w c L h.2)
    split
    · exact (hIF K A S l.intersection_update_fsHerm_neg_one _).1 c h.1
        (freeOf_matrix_neg (freeOf_matrix_smul _ (freeOf2_mul (freeOf_J_matrix c) (freeOf_matrix_transpose (hT _)))))
    · exact (hIF K A S l.intersection_update_fsHerm_neg_one _).1 c h.1 (freeOf_matrix_smul _ (freeOf2_mul (freeOf_J_matrix c) (hT _)))

end Dual

section Main

/- English proof (translation)
Introduce `K A S _ _ _ _ _ _ _ _ QQ q w L hSt`. Proceed by induction on `L with`. Consider the case `nil`. Introduce `_ _ _`. Use `⟨isUnit_one, one_ne_zero, ?_, ?_, ?_⟩` and prove the remaining obligations.

Simplify using `[Ps, JL]`. Simplify using `[Ps, kap]`. Introduce `Y _ _`. Simplify using `[Ps, ph, d0]`. Consider the case `cons l L ih`.

Introduce `hG hGd hOK`. Take `⟨hG', hnot, hstar, hregY⟩` from `good_cons hG`. Take `⟨hGd', -, -, hregd⟩` from `good_cons hGd`. Take `⟨hR1, hq, hOK'⟩` from `hOK`. Take `⟨hU', hk', h3', h4', h5'⟩` from `ih hG' hGd' hOK'`.

Establish `hM` using `hWM K A S QQ q (L ++ w) hSt hG'`. Take `⟨hfR, hfT⟩` from `hWF K A S QQ (L ++ w) l.intersection_update_fsHerm_neg_one hnot`. Establish `hfP : FreeOf l.intersection_update_fsHerm_neg_one (Ps QQ q w L)` using `Ps_free hIF hWF QQ q w l.intersection_update_fsHerm_neg_one L hnot`. Establish `hph : ph L (dl l).pt ≠ 0` using `ph_ne L _ (reg_left hR1) (reg_left hregd)`. Establish `hkap : kap q w (l :: L) ≠ 0` using `div_ne_zero (mul_ne_zero hk' hq) hph`.

Take `⟨p, a, Y⟩` from `l`. Consider the cases of `p`. Express the relevant statement in the definitionally equal form `Reg (L ++ w) (Y - 1) at hR1`. Express the relevant statement in the definitionally equal form `qw q (L ++ w) (Y - 1) ≠ 0 at hq`. Express the relevant statement in the definitionally equal form `Reg (L.map dl ++ w) (Y - 1) at hregd`.

Take `⟨m1, m2, m3, m4⟩` from `hDM K A S {Y | Reg (L ++ w) Y} (RRw QQ (L ++ w)) (TTw QQ (L ++ w)) (qw q (L ++ w)) a Y hM hfR hfT hregY hR1 hstar hq`. Establish `ePs : Ps QQ q w (⟨false, a, Y⟩ :: L) = PsiM (TTw QQ (L ++ w)) (qw q (L ++ w)) a Y * Ps QQ q w L` using `rfl`. Establish `eRR : RRw QQ ((⟨false, a, Y⟩ :: L) ++ w) = RRw QQ (L ++ w) * ins a (TTw QQ (L ++ w) Y)ᵀ` using `rfl`. Establish `eRRd : RRw QQ ((⟨false, a, Y⟩ :: L).map dl ++ w) = RRw QQ (L.map dl ++ w) * ins a (TTw QQ (L.map dl ++ w) (Y - 1))` using `rfl`. Establish `eJL : (JL (⟨false, a, Y⟩ :: L) : SlopeTestRemainingChoices S A) = ins a (YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A))ᵀ * JL L` using `rfl`.

Establish `ekap : kap q w (⟨false, a, Y⟩ :: L) = kap q w L * qw q (L ++ w) (Y - 1) / ph L (Y - 1)`. Both sides reduce to the same expression. Establish `hcomm : Commute (star (Ps QQ q w L)) (ins a (YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A))ᵀ)`. Establish `c0 : Commute (Ps QQ q w L) (ins a (YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A)))` using `(hIF K A S a _).2 _ hfP (fun i j => J_entry_comm _ i j)`. Establish `c1 : Commute (Ps QQ q w L) (star (ins a (YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A))ᵀ))`.

Rewrite using `[hIS K A S a _ (freeOf_matrix_transpose (freeOf_J_matrix a)), Jt_conj]`. Conclude with `c0`. Simplify using `using c1.star_star`. Use `⟨?_, hkap, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[ePs]`.

Conclude with `m1.mul hU'`. Rewrite using `[ePs, eRR, eJL, star_mul]`. Simplify using `only [mul_assoc]`. Rewrite using `[m2, hcomm.left_comm, h3']`. Rewrite using `[ePs, eRR, eRRd, ekap, star_mul]`.

Establish `tw : ins a (TTw QQ (L ++ w) (Y - 1)) * Ps QQ q w L = ph L (Y - 1) • (Ps QQ q w L * ins a (TTw QQ (L.map dl ++ w) (Y - 1)))` using `ins_twine hfP (twine_entries (h5' (Y - 1) hR1 hregd))`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [mul_assoc]`. Use `_ = (qw q (L ++ w) (Y - 1))⁻¹ • (star (Ps QQ q w L) * RRw QQ (L ++ w) * (ins a (TTw QQ (L ++ w) (Y - 1)) * Ps QQ q w L)) := by`. Rewrite using `[m3]`.

Simplify using `only [mul_smul_comm, smul_mul_assoc, mul_assoc]`. Use `_ = ((qw q (L ++ w) (Y - 1))⁻¹ * ph L (Y - 1)) • (star (Ps QQ q w L) * RRw QQ (L ++ w) * Ps QQ q w L * ins a (TTw QQ (L.map dl ++ w) (Y - 1))) := by`. Rewrite using `[tw, mul_smul_comm, smul_smul]`. Simplify using `only [mul_assoc]`. Use `_ = (kap q w L * qw q (L ++ w) (Y - 1) / ph L (Y - 1))⁻¹ • (RRw QQ (L.map dl ++ w) * ins a (TTw QQ (L.map dl ++ w) (Y - 1))) := by`.

Rewrite using `[h4', smul_mul_assoc, smul_smul]`. Use `congr 1`. Rewrite using `[inv_div]`. Expand and normalize the polynomial expressions, which then agree. Introduce `Y0 hr1 hr2`.

Take `⟨hl1, hr1'⟩` from `reg_cons hr1`. Take `⟨hl2, hr2'⟩` from `reg_cons hr2`. Establish `n1 : Y - Y0 ≠ 1` using `hl1`. Establish `n2 : Y0 - Y ≠ 0`. Introduce `h`.

Conclude with `hl2 (by change Y0 - (Y - 1) = 1; linear_combination h)`. Establish `e1 : Y0 - (Y - 1) = Y0 - Y + 1` using `by ring`. Establish `eTT : TTw QQ ((⟨false, a, Y⟩ :: L) ++ w) Y0 = Rht0 a (Y - Y0) * TTw QQ (L ++ w) Y0`. Both sides reduce to the same expression. Establish `eTTd : TTw QQ ((⟨false, a, Y⟩ :: L).map dl ++ w) Y0 = TTw QQ (L.map dl ++ w) Y0 * Rh0 a (Y0 - (Y - 1))` using `rfl`.

Establish `eph : ph (⟨false, a, Y⟩ :: L) Y0 = ph L Y0 * ((Y0 - Y) / (Y0 - Y + 1))` using `rfl`. Rewrite using `[ePs, eTT, eTTd, eph, diagScalar_mul, e1]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[m4 Y0 hr1' n1 n2, smul_mul_assoc]`. Simplify using `only [mul_assoc]`.

Use `_ = ((Y0 - Y) / (Y0 - Y + 1)) • (d0 (PsiM (TTw QQ (L ++ w)) (qw q (L ++ w)) a Y) * ((TTw QQ (L ++ w) Y0 * d0 (Ps QQ q w L)) * Rh0 a (Y0 - Y + 1))) := by`. Rewrite using `[Rh0_comm hfP]`. Simplify using `only [mul_assoc]`. Use `_ = (ph L Y0 * ((Y0 - Y) / (Y0 - Y + 1))) • (d0 (PsiM (TTw QQ (L ++ w)) (qw q (L ++ w)) a Y) * d0 (Ps QQ q w L) * (TTw QQ (L.map dl ++ w) Y0 * Rh0 a (Y0 - Y + 1))) := by`. Rewrite using `[h5' Y0 hr1' hr2', smul_mul_assoc, mul_smul_comm, smul_smul, mul_comm (ph L Y0)]`.

Simplify using `only [mul_assoc]`. Express the relevant statement in the definitionally equal form `Reg (L ++ w) (Y + 1) at hR1`. Express the relevant statement in the definitionally equal form `qw q (L ++ w) Y ≠ 0 at hq`. Express the relevant statement in the definitionally equal form `Reg (L.map dl ++ w) (Y + 1) at hregd`. Take `⟨d1, d2, d3, d4, d5, d6⟩` from `hDP K A S {Y | Reg (L ++ w) Y} (RRw QQ (L ++ w)) (TTw QQ (L ++ w)) (qw q (L ++ w)) a Y hM hfR hfT hregY hR1 hstar hq`.

Establish `ePs : Ps QQ q w (⟨true, a, Y⟩ :: L) = PsiP (TTw QQ (L ++ w)) (qw q (L ++ w)) a Y * Ps QQ q w L` using `rfl`. Establish `eRR : RRw QQ ((⟨true, a, Y⟩ :: L) ++ w) = RRw QQ (L ++ w) * ins a (TTw QQ (L ++ w) Y)` using `rfl`. Establish `eRRd : RRw QQ ((⟨true, a, Y⟩ :: L).map dl ++ w) = RRw QQ (L.map dl ++ w) * ins a (TTw QQ (L.map dl ++ w) (Y + 1))ᵀ` using `rfl`. Establish `eJL : (JL (⟨true, a, Y⟩ :: L) : SlopeTestRemainingChoices S A) = ins a (YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A)) * JL L` using `rfl`. Establish `ekap : kap q w (⟨true, a, Y⟩ :: L) = kap q w L * qw q (L ++ w) Y / ph L (Y + 1)` using `rfl`.

Establish `hcomm : Commute (star (Ps QQ q w L)) (ins a (YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A)))`. Establish `c0 : Commute (Ps QQ q w L) (ins a (YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A))ᵀ)` using `(hIF K A S a _).2 _ hfP (fun i j => J_entry_comm _ j i)`. Establish `c1 : Commute (Ps QQ q w L) (star (ins a (YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A))))`. Rewrite using `[hIS K A S a _ (freeOf_J_matrix a), J_conj]`. Conclude with `c0`.

Simplify using `using c1.star_star`. Use `⟨?_, hkap, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[ePs]`. Conclude with `(show IsUnit (PsiP (TTw QQ (L ++ w)) (qw q (L ++ w)) a Y) from ⟨⟨_, _, d2, d3⟩, rfl⟩).mul hU'`. Rewrite using `[ePs, eRR, eJL, star_mul]`.

Simplify using `only [mul_assoc]`. Rewrite using `[d4, hcomm.left_comm, h3']`. Rewrite using `[ePs, eRR, eRRd, ekap, star_mul]`. Establish `tw : ins a (TTw QQ (L ++ w) (Y + 1))ᵀ * Ps QQ q w L = ph L (Y + 1) • (Ps QQ q w L * ins a (TTw QQ (L.map dl ++ w) (Y + 1))ᵀ)` using `ins_twine hfP (fun i j => twine_entries (h5' (Y + 1) hR1 hregd) j i)`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [mul_assoc]`. Use `_ = (qw q (L ++ w) Y)⁻¹ • (star (Ps QQ q w L) * RRw QQ (L ++ w) * (ins a (TTw QQ (L ++ w) (Y + 1))ᵀ * Ps QQ q w L)) := by`. Rewrite using `[d5]`. Simplify using `only [mul_smul_comm, smul_mul_assoc, mul_assoc]`. Use `_ = ((qw q (L ++ w) Y)⁻¹ * ph L (Y + 1)) • (star (Ps QQ q w L) * RRw QQ (L ++ w) * Ps QQ q w L * ins a (TTw QQ (L.map dl ++ w) (Y + 1))ᵀ) := by`.

Rewrite using `[tw, mul_smul_comm, smul_smul]`. Simplify using `only [mul_assoc]`. Use `_ = (kap q w L * qw q (L ++ w) Y / ph L (Y + 1))⁻¹ • (RRw QQ (L.map dl ++ w) * ins a (TTw QQ (L.map dl ++ w) (Y + 1))ᵀ) := by`. Rewrite using `[h4', smul_mul_assoc, smul_smul]`. Use `congr 1`.

Rewrite using `[inv_div]`. Expand and normalize the polynomial expressions, which then agree. Introduce `Y0 hr1 hr2`. Take `⟨hl1, hr1'⟩` from `reg_cons hr1`. Take `⟨hl2, hr2'⟩` from `reg_cons hr2`.

Establish `n1 : Y0 - Y ≠ 1` using `hl1`. Establish `n2 : Y0 - Y ≠ 0`. Introduce `h`. Conclude with `hl2 (by change Y + 1 - Y0 = 1; linear_combination -h)`. Establish `eTT : TTw QQ ((⟨true, a, Y⟩ :: L) ++ w) Y0 = TTw QQ (L ++ w) Y0 * Rh0 a (Y0 - Y)` using `rfl`.

Establish `eTTd : TTw QQ ((⟨true, a, Y⟩ :: L).map dl ++ w) Y0 = Rht0 a (Y + 1 - Y0) * TTw QQ (L.map dl ++ w) Y0` using `rfl`. Establish `eph : ph (⟨true, a, Y⟩ :: L) Y0 = ph L Y0 * ((Y0 - Y) / (Y0 - Y - 1))` using `rfl`. Rewrite using `[ePs, eTT, eTTd, eph, diagScalar_mul]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[d6 Y0 hr1' n1 n2, smul_mul_assoc]`.

Simplify using `only [mul_assoc]`. Use `_ = (ph L Y0 * ((Y0 - Y) / (Y0 - Y - 1))) • (d0 (PsiP (TTw QQ (L ++ w)) (qw q (L ++ w)) a Y) * d0 (Ps QQ q w L) * (Rht0 a (Y + 1 - Y0) * TTw QQ (L.map dl ++ w) Y0)) := by`. Rewrite using `[h5' Y0 hr1' hr2', mul_smul_comm, mul_smul_comm, smul_smul, mul_comm (ph L Y0)]`. Rewrite using `[← mul_assoc (Rht0 a (Y + 1 - Y0)), Rht0_comm hfP]`. Simplify using `only [mul_assoc]`.
-/
theorem dualityList_of (hIF : InsFree) (hIS : InsStar) (hWF : WordFree) (hWM : WordModule)
    (hDP : DualPlus) (hDM : DualMinus) : DualityList := by
  intro K A S _ _ _ _ _ _ _ _ QQ q w L hSt
  induction L with
  | nil =>
    intro _ _ _
    refine ⟨isUnit_one, one_ne_zero, ?_, ?_, ?_⟩
    · simp [Ps, JL]
    · simp [Ps, kap]
    · intro Y _ _
      simp [Ps, ph, d0]
  | cons l L ih =>
    intro hG hGd hOK
    obtain ⟨hG', hnot, hstar, hregY⟩ := good_cons hG
    obtain ⟨hGd', -, -, hregd⟩ := good_cons hGd
    obtain ⟨hR1, hq, hOK'⟩ := hOK
    obtain ⟨hU', hk', h3', h4', h5'⟩ := ih hG' hGd' hOK'
    have hM := hWM K A S QQ q (L ++ w) hSt hG'
    obtain ⟨hfR, hfT⟩ := hWF K A S QQ (L ++ w) l.intersection_update_fsHerm_neg_one hnot
    have hfP : FreeOf l.intersection_update_fsHerm_neg_one (Ps QQ q w L) := Ps_free hIF hWF QQ q w l.intersection_update_fsHerm_neg_one L hnot
    have hph : ph L (dl l).pt ≠ 0 := ph_ne L _ (reg_left hR1) (reg_left hregd)
    have hkap : kap q w (l :: L) ≠ 0 := div_ne_zero (mul_ne_zero hk' hq) hph
    obtain ⟨p, a, Y⟩ := l
    cases p
    ·
      change Reg (L ++ w) (Y - 1) at hR1
      change qw q (L ++ w) (Y - 1) ≠ 0 at hq
      change Reg (L.map dl ++ w) (Y - 1) at hregd
      obtain ⟨m1, m2, m3, m4⟩ := hDM K A S {Y | Reg (L ++ w) Y} (RRw QQ (L ++ w)) (TTw QQ (L ++ w))
        (qw q (L ++ w)) a Y hM hfR hfT hregY hR1 hstar hq
      have ePs : Ps QQ q w (⟨false, a, Y⟩ :: L) =
          PsiM (TTw QQ (L ++ w)) (qw q (L ++ w)) a Y * Ps QQ q w L := rfl
      have eRR : RRw QQ ((⟨false, a, Y⟩ :: L) ++ w) =
          RRw QQ (L ++ w) * ins a (TTw QQ (L ++ w) Y)ᵀ := rfl
      have eRRd : RRw QQ ((⟨false, a, Y⟩ :: L).map dl ++ w) =
          RRw QQ (L.map dl ++ w) * ins a (TTw QQ (L.map dl ++ w) (Y - 1)) := rfl
      have eJL : (JL (⟨false, a, Y⟩ :: L) : SlopeTestRemainingChoices S A) = ins a (YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A))ᵀ * JL L := rfl
      have ekap : kap q w (⟨false, a, Y⟩ :: L) = kap q w L * qw q (L ++ w) (Y - 1) / ph L (Y - 1) :=
        rfl
      have hcomm : Commute (star (Ps QQ q w L)) (ins a (YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A))ᵀ) := by
        have c0 : Commute (Ps QQ q w L) (ins a (YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A))) :=
          (hIF K A S a _).2 _ hfP (fun i j => J_entry_comm _ i j)
        have c1 : Commute (Ps QQ q w L) (star (ins a (YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A))ᵀ)) := by
          rw [hIS K A S a _ (freeOf_matrix_transpose (freeOf_J_matrix a)), Jt_conj]
          exact c0
        simpa using c1.star_star
      refine ⟨?_, hkap, ?_, ?_, ?_⟩
      · rw [ePs]
        exact m1.mul hU'
      · rw [ePs, eRR, eJL, star_mul]
        simp only [mul_assoc]
        rw [m2, hcomm.left_comm, h3']
      · rw [ePs, eRR, eRRd, ekap, star_mul]
        have tw : ins a (TTw QQ (L ++ w) (Y - 1)) * Ps QQ q w L =
            ph L (Y - 1) • (Ps QQ q w L * ins a (TTw QQ (L.map dl ++ w) (Y - 1))) :=
          ins_twine hfP (twine_entries (h5' (Y - 1) hR1 hregd))
        calc star (Ps QQ q w L) * star (PsiM (TTw QQ (L ++ w)) (qw q (L ++ w)) a Y) *
              (RRw QQ (L ++ w) * ins a (TTw QQ (L ++ w) Y)ᵀ) *
              (PsiM (TTw QQ (L ++ w)) (qw q (L ++ w)) a Y * Ps QQ q w L)
            = star (Ps QQ q w L) * (star (PsiM (TTw QQ (L ++ w)) (qw q (L ++ w)) a Y) *
              (RRw QQ (L ++ w) * ins a (TTw QQ (L ++ w) Y)ᵀ) *
              PsiM (TTw QQ (L ++ w)) (qw q (L ++ w)) a Y) * Ps QQ q w L := by
              simp only [mul_assoc]
          _ = (qw q (L ++ w) (Y - 1))⁻¹ • (star (Ps QQ q w L) * RRw QQ (L ++ w) *
              (ins a (TTw QQ (L ++ w) (Y - 1)) * Ps QQ q w L)) := by
              rw [m3]
              simp only [mul_smul_comm, smul_mul_assoc, mul_assoc]
          _ = ((qw q (L ++ w) (Y - 1))⁻¹ * ph L (Y - 1)) • (star (Ps QQ q w L) * RRw QQ (L ++ w) *
              Ps QQ q w L * ins a (TTw QQ (L.map dl ++ w) (Y - 1))) := by
              rw [tw, mul_smul_comm, smul_smul]
              simp only [mul_assoc]
          _ = (kap q w L * qw q (L ++ w) (Y - 1) / ph L (Y - 1))⁻¹ •
              (RRw QQ (L.map dl ++ w) * ins a (TTw QQ (L.map dl ++ w) (Y - 1))) := by
              rw [h4', smul_mul_assoc, smul_smul]
              congr 1
              rw [inv_div]
              ring
      · intro Y0 hr1 hr2
        obtain ⟨hl1, hr1'⟩ := reg_cons hr1
        obtain ⟨hl2, hr2'⟩ := reg_cons hr2
        have n1 : Y - Y0 ≠ 1 := hl1
        have n2 : Y0 - Y ≠ 0 := by
          intro h
          exact hl2 (by change Y0 - (Y - 1) = 1; linear_combination h)
        have e1 : Y0 - (Y - 1) = Y0 - Y + 1 := by ring
        have eTT : TTw QQ ((⟨false, a, Y⟩ :: L) ++ w) Y0 = Rht0 a (Y - Y0) * TTw QQ (L ++ w) Y0 :=
          rfl
        have eTTd : TTw QQ ((⟨false, a, Y⟩ :: L).map dl ++ w) Y0 =
            TTw QQ (L.map dl ++ w) Y0 * Rh0 a (Y0 - (Y - 1)) := rfl
        have eph : ph (⟨false, a, Y⟩ :: L) Y0 = ph L Y0 * ((Y0 - Y) / (Y0 - Y + 1)) := rfl
        rw [ePs, eTT, eTTd, eph, diagScalar_mul, e1]
        calc Rht0 a (Y - Y0) * TTw QQ (L ++ w) Y0 *
              (d0 (PsiM (TTw QQ (L ++ w)) (qw q (L ++ w)) a Y) * d0 (Ps QQ q w L))
            = (Rht0 a (Y - Y0) * TTw QQ (L ++ w) Y0 *
              d0 (PsiM (TTw QQ (L ++ w)) (qw q (L ++ w)) a Y)) * d0 (Ps QQ q w L) :=
              (mul_assoc _ _ _).symm
          _ = ((Y0 - Y) / (Y0 - Y + 1)) • (d0 (PsiM (TTw QQ (L ++ w)) (qw q (L ++ w)) a Y) *
              (TTw QQ (L ++ w) Y0 * (Rh0 a (Y0 - Y + 1) * d0 (Ps QQ q w L)))) := by
              rw [m4 Y0 hr1' n1 n2, smul_mul_assoc]
              simp only [mul_assoc]
          _ = ((Y0 - Y) / (Y0 - Y + 1)) • (d0 (PsiM (TTw QQ (L ++ w)) (qw q (L ++ w)) a Y) *
              ((TTw QQ (L ++ w) Y0 * d0 (Ps QQ q w L)) * Rh0 a (Y0 - Y + 1))) := by
              rw [Rh0_comm hfP]
              simp only [mul_assoc]
          _ = (ph L Y0 * ((Y0 - Y) / (Y0 - Y + 1))) •
              (d0 (PsiM (TTw QQ (L ++ w)) (qw q (L ++ w)) a Y) * d0 (Ps QQ q w L) *
              (TTw QQ (L.map dl ++ w) Y0 * Rh0 a (Y0 - Y + 1))) := by
              rw [h5' Y0 hr1' hr2', smul_mul_assoc, mul_smul_comm, smul_smul, mul_comm (ph L Y0)]
              simp only [mul_assoc]
    ·
      change Reg (L ++ w) (Y + 1) at hR1
      change qw q (L ++ w) Y ≠ 0 at hq
      change Reg (L.map dl ++ w) (Y + 1) at hregd
      obtain ⟨d1, d2, d3, d4, d5, d6⟩ := hDP K A S {Y | Reg (L ++ w) Y} (RRw QQ (L ++ w))
        (TTw QQ (L ++ w)) (qw q (L ++ w)) a Y hM hfR hfT hregY hR1 hstar hq
      have ePs : Ps QQ q w (⟨true, a, Y⟩ :: L) =
          PsiP (TTw QQ (L ++ w)) (qw q (L ++ w)) a Y * Ps QQ q w L := rfl
      have eRR : RRw QQ ((⟨true, a, Y⟩ :: L) ++ w) =
          RRw QQ (L ++ w) * ins a (TTw QQ (L ++ w) Y) := rfl
      have eRRd : RRw QQ ((⟨true, a, Y⟩ :: L).map dl ++ w) =
          RRw QQ (L.map dl ++ w) * ins a (TTw QQ (L.map dl ++ w) (Y + 1))ᵀ := rfl
      have eJL : (JL (⟨true, a, Y⟩ :: L) : SlopeTestRemainingChoices S A) = ins a (YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A)) * JL L := rfl
      have ekap : kap q w (⟨true, a, Y⟩ :: L) = kap q w L * qw q (L ++ w) Y / ph L (Y + 1) := rfl
      have hcomm : Commute (star (Ps QQ q w L)) (ins a (YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A))) := by
        have c0 : Commute (Ps QQ q w L) (ins a (YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A))ᵀ) :=
          (hIF K A S a _).2 _ hfP (fun i j => J_entry_comm _ j i)
        have c1 : Commute (Ps QQ q w L) (star (ins a (YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A)))) := by
          rw [hIS K A S a _ (freeOf_J_matrix a), J_conj]
          exact c0
        simpa using c1.star_star
      refine ⟨?_, hkap, ?_, ?_, ?_⟩
      · rw [ePs]
        exact (show IsUnit (PsiP (TTw QQ (L ++ w)) (qw q (L ++ w)) a Y) from
          ⟨⟨_, _, d2, d3⟩, rfl⟩).mul hU'
      · rw [ePs, eRR, eJL, star_mul]
        simp only [mul_assoc]
        rw [d4, hcomm.left_comm, h3']
      · rw [ePs, eRR, eRRd, ekap, star_mul]
        have tw : ins a (TTw QQ (L ++ w) (Y + 1))ᵀ * Ps QQ q w L =
            ph L (Y + 1) • (Ps QQ q w L * ins a (TTw QQ (L.map dl ++ w) (Y + 1))ᵀ) :=
          ins_twine hfP (fun i j => twine_entries (h5' (Y + 1) hR1 hregd) j i)
        calc star (Ps QQ q w L) * star (PsiP (TTw QQ (L ++ w)) (qw q (L ++ w)) a Y) *
              (RRw QQ (L ++ w) * ins a (TTw QQ (L ++ w) Y)) *
              (PsiP (TTw QQ (L ++ w)) (qw q (L ++ w)) a Y * Ps QQ q w L)
            = star (Ps QQ q w L) * (star (PsiP (TTw QQ (L ++ w)) (qw q (L ++ w)) a Y) *
              (RRw QQ (L ++ w) * ins a (TTw QQ (L ++ w) Y)) *
              PsiP (TTw QQ (L ++ w)) (qw q (L ++ w)) a Y) * Ps QQ q w L := by
              simp only [mul_assoc]
          _ = (qw q (L ++ w) Y)⁻¹ • (star (Ps QQ q w L) * RRw QQ (L ++ w) *
              (ins a (TTw QQ (L ++ w) (Y + 1))ᵀ * Ps QQ q w L)) := by
              rw [d5]
              simp only [mul_smul_comm, smul_mul_assoc, mul_assoc]
          _ = ((qw q (L ++ w) Y)⁻¹ * ph L (Y + 1)) • (star (Ps QQ q w L) * RRw QQ (L ++ w) *
              Ps QQ q w L * ins a (TTw QQ (L.map dl ++ w) (Y + 1))ᵀ) := by
              rw [tw, mul_smul_comm, smul_smul]
              simp only [mul_assoc]
          _ = (kap q w L * qw q (L ++ w) Y / ph L (Y + 1))⁻¹ •
              (RRw QQ (L.map dl ++ w) * ins a (TTw QQ (L.map dl ++ w) (Y + 1))ᵀ) := by
              rw [h4', smul_mul_assoc, smul_smul]
              congr 1
              rw [inv_div]
              ring
      · intro Y0 hr1 hr2
        obtain ⟨hl1, hr1'⟩ := reg_cons hr1
        obtain ⟨hl2, hr2'⟩ := reg_cons hr2
        have n1 : Y0 - Y ≠ 1 := hl1
        have n2 : Y0 - Y ≠ 0 := by
          intro h
          exact hl2 (by change Y + 1 - Y0 = 1; linear_combination -h)
        have eTT : TTw QQ ((⟨true, a, Y⟩ :: L) ++ w) Y0 = TTw QQ (L ++ w) Y0 * Rh0 a (Y0 - Y) := rfl
        have eTTd : TTw QQ ((⟨true, a, Y⟩ :: L).map dl ++ w) Y0 =
            Rht0 a (Y + 1 - Y0) * TTw QQ (L.map dl ++ w) Y0 := rfl
        have eph : ph (⟨true, a, Y⟩ :: L) Y0 = ph L Y0 * ((Y0 - Y) / (Y0 - Y - 1)) := rfl
        rw [ePs, eTT, eTTd, eph, diagScalar_mul]
        calc TTw QQ (L ++ w) Y0 * Rh0 a (Y0 - Y) *
              (d0 (PsiP (TTw QQ (L ++ w)) (qw q (L ++ w)) a Y) * d0 (Ps QQ q w L))
            = (TTw QQ (L ++ w) Y0 * Rh0 a (Y0 - Y) *
              d0 (PsiP (TTw QQ (L ++ w)) (qw q (L ++ w)) a Y)) * d0 (Ps QQ q w L) :=
              (mul_assoc _ _ _).symm
          _ = ((Y0 - Y) / (Y0 - Y - 1)) • (d0 (PsiP (TTw QQ (L ++ w)) (qw q (L ++ w)) a Y) *
              (Rht0 a (Y + 1 - Y0) * (TTw QQ (L ++ w) Y0 * d0 (Ps QQ q w L)))) := by
              rw [d6 Y0 hr1' n1 n2, smul_mul_assoc]
              simp only [mul_assoc]
          _ = (ph L Y0 * ((Y0 - Y) / (Y0 - Y - 1))) •
              (d0 (PsiP (TTw QQ (L ++ w)) (qw q (L ++ w)) a Y) * d0 (Ps QQ q w L) *
              (Rht0 a (Y + 1 - Y0) * TTw QQ (L.map dl ++ w) Y0)) := by
              rw [h5' Y0 hr1' hr2', mul_smul_comm, mul_smul_comm, smul_smul, mul_comm (ph L Y0)]
              rw [← mul_assoc (Rht0 a (Y + 1 - Y0)), Rht0_comm hfP]
              simp only [mul_assoc]

end Main

end Formalism.FourierDecayAlt.P.Wd10

/- English proof (translation)
Introduce `K S _ _ q w L _ _ h`. Conclude with `Formalism.FourierDecayAlt.P.Wd10.kap_eq q w L h`.
-/
theorem Formalism.FourierDecayAlt.P.kappa_formula_holds : Formalism.FourierDecayAlt.Wd.KapFormula := by
  intro K S _ _ q w L _ _ h
  exact Formalism.FourierDecayAlt.P.Wd10.kap_eq q w L h

/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.Wd10.dualityList_of Formalism.FourierDecayAlt.P.position_insertion_free_compat Formalism.FourierDecayAlt.P.position_insertion_star_compat Formalism.FourierDecayAlt.P.word_free_of_unused_positions Formalism.FourierDecayAlt.P.word_module_structure Formal …`.
-/
theorem Formalism.FourierDecayAlt.P.duality_list_holds : Formalism.FourierDecayAlt.Wd.DualityList :=
  Formalism.FourierDecayAlt.P.Wd10.dualityList_of Formalism.FourierDecayAlt.P.position_insertion_free_compat Formalism.FourierDecayAlt.P.position_insertion_star_compat
    Formalism.FourierDecayAlt.P.word_free_of_unused_positions Formalism.FourierDecayAlt.P.word_module_structure Formalism.FourierDecayAlt.P.duality_plus
    Formalism.FourierDecayAlt.P.duality_minus
