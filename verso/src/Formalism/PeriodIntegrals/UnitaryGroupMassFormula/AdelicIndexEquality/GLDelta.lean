import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.LocSplitChiOf

noncomputable section

namespace PI.UnitaryGroupMassFormula.AdIndexEq

namespace GLChiPf

open Matrix

variable {k : Type} [Field k] {n : ℕ}

def glOf (M : Matrix (Fin n) (Fin n) k) (h : M.det ≠ 0) : GL (Fin n) k :=
  ⟨M, M⁻¹, Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.mpr h),
    Matrix.nonsing_inv_mul M (isUnit_iff_ne_zero.mpr h)⟩

/- English proof (translation)
Rewrite using `[map_mul, map_mul, mul_comm (χ s), mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]`.
-/
theorem chi_conj (χ : GL (Fin n) k →* ℚ) (s x : GL (Fin n) k) : χ (s * x * s⁻¹) = χ x := by
  rw [map_mul, map_mul, mul_comm (χ s), mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [mul_diagonal, diagonal_mul, transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, Function.update_apply, Pi.one_apply, eq_comm (a := i) (b := a), eq_comm (a := j) (b := b)]`. Establish `h2 : (2 : k) ≠ 0` using `two_ne_zero`. Apply the tactic sequence `by_cases ha : a = i <;> by_cases hb : b = i <;> by_cases hab : a = b <;>`. Apply the tactic sequence `by_cases hjb : b = j <;> simp_all`.
-/
theorem diag_transvection [CharZero k] (i j : Fin n) (hij : i ≠ j) (c : k) :
    diagonal (Function.update (1 : Fin n → k) i 2) * transvection i j c *
      diagonal (Function.update (1 : Fin n → k) i 2⁻¹) = transvection i j (2 * c) := by
  ext a b
  simp only [mul_diagonal, diagonal_mul, transvection, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply, Function.update_apply, Pi.one_apply, eq_comm (a := i) (b := a),
    eq_comm (a := j) (b := b)]
  have h2 : (2 : k) ≠ 0 := two_ne_zero
  by_cases ha : a = i <;> by_cases hb : b = i <;> by_cases hab : a = b <;>
    by_cases hjb : b = j <;> simp_all

/- English proof (translation)
Take `⟨i, j, hij, c⟩` from `t`. Establish `h2 : (2 : k) ≠ 0` using `two_ne_zero`. Establish `key : ∀ a : k, a ≠ 0 → diagonal (Function.update (1 : Fin n → k) i a) * diagonal (Function.update (1 : Fin n → k) i a⁻¹) = 1`. Introduce `a ha`. Rewrite using `[diagonal_mul_diagonal, ← diagonal_one]`.

Use `congr 1`. Use function extensionality and compare the values at `x`. Distinguish the cases in `hx : x = i`. Substitute `hx` using the available equality. Simplify using `[ha]`.

Simplify using `[Function.update_apply, hx]`. Establish `key' : diagonal (Function.update (1 : Fin n → k) i 2⁻¹) * diagonal (Function.update (1 : Fin n → k) i 2) = 1`. Simplify using `using key 2⁻¹ (inv_ne_zero h2)`. Set `s : GL (Fin n) k` to `⟨diagonal (Function.update (1 : Fin n → k) i 2), diagonal (Function.update (1 : Fin n → k) i 2⁻¹), key 2 h2, key'⟩`. Establish `hsq : s * glOf _ h * s⁻¹ = glOf _ h * glOf _ h`.

Apply `Units.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `diagonal (Function.update (1 : Fin n → k) i 2) * transvection i j c * diagonal (Function.update (1 : Fin n → k) i 2⁻¹) = transvection i j c * transvection i j c`. Rewrite using `[diag_transvection i j hij c, two_mul]`. Use `symm`. Apply `transvection_mul_transvection_same` to reduce the goal to its premises.

Apply the tactic sequence `all_goals exact hij`. Establish `e` using `chi_conj χ s (glOf _ h)`. Rewrite `e` using `[hsq, map_mul]`. Conclude with `mul_left_cancel₀ (ne_of_gt (hpos _)) (e.trans (mul_one _).symm)`.
-/
theorem chi_transvection [CharZero k] (χ : GL (Fin n) k →* ℚ) (hpos : ∀ g, 0 < χ g)
    (t : TransvectionStruct (Fin n) k) (h : t.toMatrix.det ≠ 0) : χ (glOf t.toMatrix h) = 1 := by
  obtain ⟨i, j, hij, c⟩ := t
  have h2 : (2 : k) ≠ 0 := two_ne_zero
  have key : ∀ a : k, a ≠ 0 → diagonal (Function.update (1 : Fin n → k) i a) *
      diagonal (Function.update (1 : Fin n → k) i a⁻¹) = 1 := by
    intro a ha
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext x
    by_cases hx : x = i
    · subst hx; simp [ha]
    · simp [Function.update_apply, hx]
  have key' : diagonal (Function.update (1 : Fin n → k) i 2⁻¹) *
      diagonal (Function.update (1 : Fin n → k) i 2) = 1 := by
    simpa using key 2⁻¹ (inv_ne_zero h2)
  let s : GL (Fin n) k := ⟨diagonal (Function.update (1 : Fin n → k) i 2),
    diagonal (Function.update (1 : Fin n → k) i 2⁻¹), key 2 h2, key'⟩
  have hsq : s * glOf _ h * s⁻¹ = glOf _ h * glOf _ h := by
    apply Units.ext
    change diagonal (Function.update (1 : Fin n → k) i 2) * transvection i j c *
      diagonal (Function.update (1 : Fin n → k) i 2⁻¹) = transvection i j c * transvection i j c
    rw [diag_transvection i j hij c, two_mul]
    symm
    apply transvection_mul_transvection_same
    all_goals exact hij
  have e := chi_conj χ s (glOf _ h)
  rw [hsq, map_mul] at e
  exact mul_left_cancel₀ (ne_of_gt (hpos _)) (e.trans (mul_one _).symm)

def dU : (Fin n → kˣ) →* GL (Fin n) k :=
  (Units.map (Matrix.diagonalRingHom (Fin n) k).toMonoidHom).comp MulEquiv.piUnits.symm.toMonoidHom

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem dU_val (D : Fin n → kˣ) :
    ((dU D : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = diagonal (fun i => (D i : k)) := rfl

/- English proof (translation)
Rewrite using `[PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv, hσ]`. Both sides reduce to the same expression.
-/
theorem perm_conj (σ : Equiv.Perm (Fin n)) (hσ : σ.symm = σ) (M : Matrix (Fin n) (Fin n) k) :
    σ.toPEquiv.toMatrix * M * σ.toPEquiv.toMatrix = M.submatrix σ σ := by
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv, hσ]
  rfl

/- English proof (translation)
Establish `e` using `perm_conj σ hσ (1 : Matrix (Fin n) (Fin n) k)`. Rewrite `e` using `[Matrix.mul_one, Matrix.submatrix_one_equiv]`. Then use the resulting hypothesis.
-/
theorem perm_sq (σ : Equiv.Perm (Fin n)) (hσ : σ.symm = σ) :
    σ.toPEquiv.toMatrix * σ.toPEquiv.toMatrix = (1 : Matrix (Fin n) (Fin n) k) := by
  have e := perm_conj σ hσ (1 : Matrix (Fin n) (Fin n) k)
  rwa [Matrix.mul_one, Matrix.submatrix_one_equiv] at e

def sU (σ : Equiv.Perm (Fin n)) (hσ : σ.symm = σ) : GL (Fin n) k :=
  ⟨σ.toPEquiv.toMatrix, σ.toPEquiv.toMatrix, perm_sq σ hσ, perm_sq σ hσ⟩

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Use `show σ.toPEquiv.toMatrix * ((dU D : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * σ.toPEquiv.toMatrix = ((dU (D ∘ σ) : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)`. Rewrite using `[dU_val, dU_val, perm_conj σ hσ, Matrix.submatrix_diagonal_equiv]`. Both sides reduce to the same expression.
-/
theorem sU_conj_dU (σ : Equiv.Perm (Fin n)) (hσ : σ.symm = σ) (D : Fin n → kˣ) :
    sU σ hσ * dU D * (sU σ hσ)⁻¹ = dU (D ∘ σ) := by
  apply Units.ext
  show σ.toPEquiv.toMatrix * ((dU D : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * σ.toPEquiv.toMatrix =
    ((dU (D ∘ σ) : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)
  rw [dU_val, dU_val, perm_conj σ hσ, Matrix.submatrix_diagonal_equiv]
  rfl

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `only [Function.comp_apply]`. Distinguish the cases in `hxj : x = j`. Substitute `hxj` using the available equality. Simplify using the standard rewrite rules.

Distinguish the cases in `hxi : x = i`. Substitute `hxi` using the available equality. Rewrite using `[Equiv.swap_apply_left, Pi.mulSingle_eq_of_ne (Ne.symm hxj), Pi.mulSingle_eq_of_ne hxj]`. Rewrite using `[Equiv.swap_apply_of_ne_of_ne hxi hxj, Pi.mulSingle_eq_of_ne hxi, Pi.mulSingle_eq_of_ne hxj]`.
-/
theorem mulSingle_comp_swap (i j : Fin n) (d : kˣ) :
    (Pi.mulSingle i d : Fin n → kˣ) ∘ (Equiv.swap i j) = Pi.mulSingle j d := by
  funext x
  simp only [Function.comp_apply]
  by_cases hxj : x = j
  · subst hxj; simp
  · by_cases hxi : x = i
    · subst hxi
      rw [Equiv.swap_apply_left, Pi.mulSingle_eq_of_ne (Ne.symm hxj), Pi.mulSingle_eq_of_ne hxj]
    · rw [Equiv.swap_apply_of_ne_of_ne hxi hxj, Pi.mulSingle_eq_of_ne hxi, Pi.mulSingle_eq_of_ne hxj]

/- English proof (translation)
Establish `h` using `chi_conj χ (sU (Equiv.swap i j) (Equiv.symm_swap i j)) (dU (Pi.mulSingle i d))`. Rewrite `h` using `[sU_conj_dU, mulSingle_comp_swap]`. Conclude with `h.symm`.
-/
theorem chi_single_eq (χ : GL (Fin n) k →* ℚ) (i j : Fin n) (d : kˣ) :
    χ (dU (Pi.mulSingle i d)) = χ (dU (Pi.mulSingle j d)) := by
  have h := chi_conj χ (sU (Equiv.swap i j) (Equiv.symm_swap i j)) (dU (Pi.mulSingle i d))
  rw [sU_conj_dU, mulSingle_comp_swap] at h
  exact h.symm

/- English proof (translation)
Establish `hn : n ≠ 0` using `by rintro rfl; exact i.elim0`. Establish `hsc : Units.map (algebraMap k (Matrix (Fin n) (Fin n) k)).toMonoidHom d = dU (fun _ => d)`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[dU_val]`. Use extensionality with `a b`.

Simplify using `[Matrix.algebraMap_matrix_apply, Matrix.diagonal_apply]`. Establish `hprod : (fun _ : Fin n => d) = ∏ l, Pi.mulSingle l d` using `(Finset.univ_prod_mulSingle (fun _ => d)).symm`. Establish `h1 : (χ.comp dU) (fun _ => d) = 1` using `by rw [MonoidHom.comp_apply, ← hsc]; exact hz d`. Rewrite `h1` using `[hprod, map_prod]`. Simplify using `only [MonoidHom.comp_apply] at h1`.

Establish `h2 : ∏ l : Fin n, χ (dU (Pi.mulSingle l d)) = ∏ _l : Fin n, χ (dU (Pi.mulSingle i d))` using `Finset.prod_congr rfl (fun l _ => chi_single_eq χ l i d)`. Rewrite `h1` using `[h2, Finset.prod_const, Finset.card_univ, Fintype.card_fin]`. Conclude with `(pow_eq_one_iff_of_nonneg (hpos _).le hn).mp h1`.
-/
theorem chi_single (χ : GL (Fin n) k →* ℚ) (hpos : ∀ g, 0 < χ g)
    (hz : ∀ d : kˣ, χ (Units.map (algebraMap k (Matrix (Fin n) (Fin n) k)).toMonoidHom d) = 1)
    (i : Fin n) (d : kˣ) : χ (dU (Pi.mulSingle i d)) = 1 := by
  have hn : n ≠ 0 := by rintro rfl; exact i.elim0
  have hsc : Units.map (algebraMap k (Matrix (Fin n) (Fin n) k)).toMonoidHom d = dU (fun _ => d) := by
    apply Units.ext
    rw [dU_val]
    ext a b
    simp [Matrix.algebraMap_matrix_apply, Matrix.diagonal_apply]
  have hprod : (fun _ : Fin n => d) = ∏ l, Pi.mulSingle l d := (Finset.univ_prod_mulSingle (fun _ => d)).symm
  have h1 : (χ.comp dU) (fun _ => d) = 1 := by rw [MonoidHom.comp_apply, ← hsc]; exact hz d
  rw [hprod, map_prod] at h1
  simp only [MonoidHom.comp_apply] at h1
  have h2 : ∏ l : Fin n, χ (dU (Pi.mulSingle l d)) = ∏ _l : Fin n, χ (dU (Pi.mulSingle i d)) :=
    Finset.prod_congr rfl (fun l _ => chi_single_eq χ l i d)
  rw [h2, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h1
  exact (pow_eq_one_iff_of_nonneg (hpos _).le hn).mp h1

/- English proof (translation)
Establish `e : χ (dU D) = (χ.comp dU) (∏ i, Pi.mulSingle i (D i))`. Rewrite using `[Finset.univ_prod_mulSingle]`. Both sides reduce to the same expression. Rewrite using `[e, map_prod]`. Conclude with `Finset.prod_eq_one (fun i _ => chi_single χ hpos hz i (D i))`.
-/
theorem chi_diag (χ : GL (Fin n) k →* ℚ) (hpos : ∀ g, 0 < χ g)
    (hz : ∀ d : kˣ, χ (Units.map (algebraMap k (Matrix (Fin n) (Fin n) k)).toMonoidHom d) = 1)
    (D : Fin n → kˣ) : χ (dU D) = 1 := by
  have e : χ (dU D) = (χ.comp dU) (∏ i, Pi.mulSingle i (D i)) := by
    rw [Finset.univ_prod_mulSingle]; rfl
  rw [e, map_prod]
  exact Finset.prod_eq_one (fun i _ => chi_single χ hpos hz i (D i))

end GLChiPf

open GLChiPf in
/- English proof (translation)
Introduce `k _ _ n χ hpos hz g`. Take `⟨L, L', D, hM⟩` from `Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec (g : Matrix (Fin n) (Fin n) k)`. Establish `htd : ∀ t : Matrix.TransvectionStruct (Fin n) k, t.toMatrix.det ≠ 0` using `fun t => by`. Rewrite using `[t.det]`. Conclude with `one_ne_zero`.

Establish `lu_val : ∀ l : List (Matrix.TransvectionStruct (Fin n) k), (((l.map fun t => glOf t.toMatrix (htd t)).prod : Matrix.GeneralLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) = (l.map Matrix.TransvectionStruct.toMatrix).prod`. Introduce `l`. Proceed by induction on `l with`. Consider the case `nil => rfl`. Consider the case `cons t l ih`.

Simplify using `only [List.map_cons, List.prod_cons, Units.val_mul, ih]`. Apply the tactic sequence `try rfl`. Establish `lu_chi : ∀ l : List (Matrix.TransvectionStruct (Fin n) k), χ ((l.map fun t => glOf t.toMatrix (htd t)).prod) = 1`. Introduce `l`. Proceed by induction on `l with`.

Consider the case `nil => simp`. Consider the case `cons t l ih`. Rewrite using `[List.map_cons, List.prod_cons, map_mul, ih, chi_transvection χ hpos t (htd t), one_mul]`. Establish `det_l : ∀ l : List (Matrix.TransvectionStruct (Fin n) k), (l.map Matrix.TransvectionStruct.toMatrix).prod.det = 1`. Introduce `l`.

Proceed by induction on `l with`. Consider the case `nil => simp`. Consider the case `cons t l ih => rw [List.map_cons, List.prod_cons, Matrix.det_mul, t.det, ih, one_mul]`. Establish `hg0 : (g : Matrix (Fin n) (Fin n) k).det ≠ 0` using `((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit g)).ne_zero`. Establish `hdet : (g : Matrix (Fin n) (Fin n) k).det = ∏ j, D j`.

Rewrite using `[hM, Matrix.det_mul, Matrix.det_mul, det_l, det_l, Matrix.det_diagonal, one_mul, mul_one]`. Establish `hD : ∀ i, D i ≠ 0`. Introduce `i`. Rewrite `hg0` using `[hdet]`. Conclude with `Finset.prod_ne_zero_iff.mp hg0 i (Finset.mem_univ i)`.

Establish `hg : g = (L.map fun t => glOf t.toMatrix (htd t)).prod * dU (fun i => Units.mk0 (D i) (hD i)) * (L'.map fun t => glOf t.toMatrix (htd t)).prod`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Units.val_mul, Units.val_mul, lu_val, lu_val, dU_val]`. Conclude with `hM`. Rewrite using `[hg, map_mul, map_mul, lu_chi, lu_chi, chi_diag χ hpos hz, one_mul, one_mul]`.
-/
theorem gl_character : GLChi := by
  intro k _ _ n χ hpos hz g
  obtain ⟨L, L', D, hM⟩ :=
    Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec (g : Matrix (Fin n) (Fin n) k)
  have htd : ∀ t : Matrix.TransvectionStruct (Fin n) k, t.toMatrix.det ≠ 0 := fun t => by
    rw [t.det]; exact one_ne_zero
  have lu_val : ∀ l : List (Matrix.TransvectionStruct (Fin n) k),
      (((l.map fun t => glOf t.toMatrix (htd t)).prod : Matrix.GeneralLinearGroup (Fin n) k) :
        Matrix (Fin n) (Fin n) k) = (l.map Matrix.TransvectionStruct.toMatrix).prod := by
    intro l
    induction l with
    | nil => rfl
    | cons t l ih =>
      simp only [List.map_cons, List.prod_cons, Units.val_mul, ih]
      try rfl
  have lu_chi : ∀ l : List (Matrix.TransvectionStruct (Fin n) k),
      χ ((l.map fun t => glOf t.toMatrix (htd t)).prod) = 1 := by
    intro l
    induction l with
    | nil => simp
    | cons t l ih =>
      rw [List.map_cons, List.prod_cons, map_mul, ih, chi_transvection χ hpos t (htd t), one_mul]
  have det_l : ∀ l : List (Matrix.TransvectionStruct (Fin n) k),
      (l.map Matrix.TransvectionStruct.toMatrix).prod.det = 1 := by
    intro l
    induction l with
    | nil => simp
    | cons t l ih => rw [List.map_cons, List.prod_cons, Matrix.det_mul, t.det, ih, one_mul]
  have hg0 : (g : Matrix (Fin n) (Fin n) k).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit g)).ne_zero
  have hdet : (g : Matrix (Fin n) (Fin n) k).det = ∏ j, D j := by
    rw [hM, Matrix.det_mul, Matrix.det_mul, det_l, det_l, Matrix.det_diagonal, one_mul, mul_one]
  have hD : ∀ i, D i ≠ 0 := by
    intro i
    rw [hdet] at hg0
    exact Finset.prod_ne_zero_iff.mp hg0 i (Finset.mem_univ i)
  have hg : g = (L.map fun t => glOf t.toMatrix (htd t)).prod * dU (fun i => Units.mk0 (D i) (hD i)) *
      (L'.map fun t => glOf t.toMatrix (htd t)).prod := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, lu_val, lu_val, dU_val]
    exact hM
  rw [hg, map_mul, map_mul, lu_chi, lu_chi, chi_diag χ hpos hz, one_mul, one_mul]

end PI.UnitaryGroupMassFormula.AdIndexEq
