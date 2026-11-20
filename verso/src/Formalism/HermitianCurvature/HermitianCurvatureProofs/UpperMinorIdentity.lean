import Formalism.HermitianCurvature.HermitianCurvatureProofs.CardInsertEmbedding

open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants

namespace Formalism.FourierDecayAlt.P

open C2x2 CardInsertEmbedding

/- English proof (translation)
Introduce `m w d hd a b hab`. Use `⟨1, Or.inl rfl, fun l hl u' hu => ?_⟩` and prove the remaining obligations. Establish `ham : a.val + 1 ≤ m` using `a.isLt`. Establish `hRc : (C2.wSet w (a.val + 1)).card = a.val + 1` using `c2x3_wSet_card w ham`. Establish `hIc : (C2.iSet m (a.val + 1)).card = a.val + 1` using `c2x3_iSet_card ham`.

Establish `hCc : (insert b (C2.iSet m a.val)).card = a.val + 1` using `card_ins b hab (by omega)`. Unfold `C2.minorS`. Rewrite using `[dif_pos (hRc.trans hIc.symm), dif_pos (hRc.trans hCc.symm)]`. Use `set eR := (C2.wSet w (a.val + 1)).orderEmbOfFin rfl with heR`. Use `set eI := (C2.iSet m (a.val + 1)).orderEmbOfFin (hRc.trans hIc.symm).symm with heI`.

Use `set eC := (insert b (C2.iSet m a.val)).orderEmbOfFin (hRc.trans hCc.symm).symm with heC`. Establish `hI : ∀ t, (eI t).val = t.val` using `fun t => iemb ham _ t`. Establish `hC : ∀ t, eC t = if ht : t.val < a.val then ⟨t.val, by omega⟩ else b` using `fun t => cemb b hab _ t`. Establish `hR : ∀ t, ∃ j0 : Fin m, j0.val < a.val + 1 ∧ w j0 = eR t`. Introduce `t`.

Use `Finset.orderEmbOfFin_mem (C2.wSet w (a.val + 1)) rfl t` as an intermediate fact. Take `⟨j0, hj0, hw⟩` from `Finset.mem_image.mp this`. Conclude with `⟨j0, by simpa [C2.iSet] using hj0, hw⟩`. Establish `hPu` using `isUnit_det_monomialMatrix w d hd`. Use `set P := C2.monoP w d with hP`.

Establish `hPl : l * P = P * (P⁻¹ * l * P)`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hPu, Matrix.one_mul]`. Establish `hlt` using `hl.2`. Rewrite using `[hPl, Matrix.mul_assoc, submatrix_monomialMatrix_mul hRc (by omega) w d _ eR eI eC hI hR, L_mul_sub (by omega) _ _ (fun i j h => hlt.1 i j h) eI eC hI, Matrix.det_mul, Matrix.det_mul, det_lt_sub _ hlt eI hI]`. Establish `hdu : (u'.submatrix eI eC).det = u' a b`.

Rewrite using `[Matrix.det_of_upperTriangular]`. Establish `ht0 : a.val < (C2.wSet w (a.val + 1)).card` using `by omega`. Rewrite using `[Finset.prod_eq_single ⟨a.val, ht0⟩]`. Simplify using `only [Matrix.submatrix_apply]`. Rewrite using `[hC, dif_neg (lt_irrefl _)]`.

Use `congr 1`. Conclude with `Fin.ext (hI _)`. Introduce `t _ ht`. Establish `htv : t.val < a.val`. Use `t.isLt` as an intermediate fact.

Establish `: t.val ≠ a.val` using `fun e => ht (Fin.ext e)`. Use linear arithmetic over natural numbers and integers. Simplify using `only [Matrix.submatrix_apply]`. Rewrite using `[hC, dif_pos htv]`. Establish `: eI t = ⟨t.val, by omega⟩` using `Fin.ext (hI t)`.

Rewrite using `[this]`. Conclude with `hu.2 _`. Simplify using the standard rewrite rules. Introduce `t s hst`. Simplify using `only [id] at hst`.

Simplify using `only [Matrix.submatrix_apply]`. Establish `hsv : s.val < a.val` using `by have := t.isLt; rw [Fin.lt_def] at hst; omega`. Rewrite using `[hC, dif_pos hsv]`. Apply `hu.1` to reduce the goal to its premises. Rewrite using `[Fin.lt_def, hI]`.

Simplify using `only`. Rewrite `hst` using `[Fin.lt_def]`. Conclude with `hst`. Rewrite using `[hdu]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem upper_minor_identity : C2.MinorU := by
  intro m w d hd a b hab
  refine ⟨1, Or.inl rfl, fun l hl u' hu => ?_⟩
  have ham : a.val + 1 ≤ m := a.isLt
  have hRc : (C2.wSet w (a.val + 1)).card = a.val + 1 := c2x3_wSet_card w ham
  have hIc : (C2.iSet m (a.val + 1)).card = a.val + 1 := c2x3_iSet_card ham
  have hCc : (insert b (C2.iSet m a.val)).card = a.val + 1 := card_ins b hab (by omega)
  unfold C2.minorS
  rw [dif_pos (hRc.trans hIc.symm), dif_pos (hRc.trans hCc.symm)]
  set eR := (C2.wSet w (a.val + 1)).orderEmbOfFin rfl with heR
  set eI := (C2.iSet m (a.val + 1)).orderEmbOfFin (hRc.trans hIc.symm).symm with heI
  set eC := (insert b (C2.iSet m a.val)).orderEmbOfFin (hRc.trans hCc.symm).symm with heC
  have hI : ∀ t, (eI t).val = t.val := fun t => iemb ham _ t
  have hC : ∀ t, eC t = if ht : t.val < a.val then ⟨t.val, by omega⟩ else b := fun t => cemb b hab _ t
  have hR : ∀ t, ∃ j0 : Fin m, j0.val < a.val + 1 ∧ w j0 = eR t := by
    intro t
    have := Finset.orderEmbOfFin_mem (C2.wSet w (a.val + 1)) rfl t
    obtain ⟨j0, hj0, hw⟩ := Finset.mem_image.mp this
    exact ⟨j0, by simpa [C2.iSet] using hj0, hw⟩
  have hPu := isUnit_det_monomialMatrix w d hd
  set P := C2.monoP w d with hP
  have hPl : l * P = P * (P⁻¹ * l * P) := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hPu, Matrix.one_mul]
  have hlt := hl.2
  rw [hPl, Matrix.mul_assoc,
    submatrix_monomialMatrix_mul hRc (by omega) w d _ eR eI eC hI hR,
    L_mul_sub (by omega) _ _ (fun i j h => hlt.1 i j h) eI eC hI,
    Matrix.det_mul, Matrix.det_mul, det_lt_sub _ hlt eI hI]
  have hdu : (u'.submatrix eI eC).det = u' a b := by
    rw [Matrix.det_of_upperTriangular]
    · have ht0 : a.val < (C2.wSet w (a.val + 1)).card := by omega
      rw [Finset.prod_eq_single ⟨a.val, ht0⟩]
      · simp only [Matrix.submatrix_apply]
        rw [hC, dif_neg (lt_irrefl _)]
        congr 1
        exact Fin.ext (hI _)
      · intro t _ ht
        have htv : t.val < a.val := by
          have := t.isLt; have : t.val ≠ a.val := fun e => ht (Fin.ext e); omega
        simp only [Matrix.submatrix_apply]
        rw [hC, dif_pos htv]
        have : eI t = ⟨t.val, by omega⟩ := Fin.ext (hI t)
        rw [this]; exact hu.2 _
      · simp
    · intro t s hst
      simp only [id] at hst
      simp only [Matrix.submatrix_apply]
      have hsv : s.val < a.val := by have := t.isLt; rw [Fin.lt_def] at hst; omega
      rw [hC, dif_pos hsv]
      apply hu.1
      rw [Fin.lt_def, hI]; simp only; rw [Fin.lt_def] at hst; exact hst
  rw [hdu]
  ring

end Formalism.FourierDecayAlt.P
