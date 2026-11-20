import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock

open MeasureTheory Matrix

namespace GlobalTheory.DetFactor

variable {k : Type} [Field k] {m : ℕ}

noncomputable def diagGL (n : ℕ) : (Fin n → kˣ) →* GL (Fin n) k :=
  (Units.map (diagonalRingHom (Fin n) k).toMonoidHom).comp MulEquiv.piUnits.symm.toMonoidHom

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem diagGL_val {n : ℕ} (d : Fin n → kˣ) : ((diagGL n d : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = diagonal (fun i => (d i : k)) := rfl

noncomputable def toGL {n : ℕ} (M : Matrix (Fin n) (Fin n) k) (h : M.det ≠ 0) : GL (Fin n) k :=
  nonsingInvUnit M (isUnit_iff_ne_zero.mpr h)

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem toGL_val {n : ℕ} (M : Matrix (Fin n) (Fin n) k) (h : M.det ≠ 0) :
    ((toGL M h : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = M := rfl

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [transvection, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, diagonal_mul, mul_diagonal]`. Apply the tactic sequence `by_cases ha : a = i <;> by_cases hb : b = j <;> by_cases hbi : b = i <;> by_cases hab : a = b <;>`. Apply the tactic sequence `simp_all [single, one_apply, eq_comm] <;> ring`.
-/
theorem conj_transvection {n : ℕ} {i j : Fin n} (hij : i ≠ j) (t : k) :
    diagonal (fun l => if l = i then (2 : k) else 1) * transvection i j t
      = transvection i j (2 * t) * diagonal (fun l => if l = i then (2 : k) else 1) := by
  ext a b
  simp only [transvection, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, diagonal_mul, mul_diagonal]
  by_cases ha : a = i <;> by_cases hb : b = j <;> by_cases hbi : b = i <;> by_cases hab : a = b <;>
    simp_all [single, one_apply, eq_comm] <;> ring

/- English proof (translation)
Rewrite using `[det_diagonal, Finset.prod_ne_zero_iff]`. Introduce `l _`. Apply the tactic sequence `split_ifs <;> simp [h2]`.
-/
theorem det_diag2_ne {n : ℕ} (h2 : (2 : k) ≠ 0) (i : Fin n) :
    (diagonal (fun l => if l = i then (2 : k) else 1)).det ≠ 0 := by
  rw [det_diagonal, Finset.prod_ne_zero_iff]
  intro l _
  split_ifs <;> simp [h2]

/- English proof (translation)
Rewrite using `[det_transvection_of_ne _ _ hij]`. Conclude with `one_ne_zero`.
-/
theorem det_transvection_ne {n : ℕ} {i j : Fin n} (hij : i ≠ j) (t : k) :
    (transvection i j t).det ≠ 0 := by
  rw [det_transvection_of_ne _ _ hij]; exact one_ne_zero

/- English proof (translation)
Use `set D := toGL _ (det_diag2_ne h2 i)`. Establish `h1 : D * toGL (transvection i j t) (det_transvection_ne hij t) = toGL (transvection i j (2 * t)) (det_transvection_ne hij _) * D`. Apply `Units.ext` to reduce the goal to its premises. Simplify using `only [Units.val_mul, toGL_val, D]`. Conclude with `conj_transvection hij t`.

Establish `h3 : toGL (transvection i j t) (det_transvection_ne hij t) * toGL (transvection i j t) (det_transvection_ne hij t) = toGL (transvection i j (2 * t)) (det_transvection_ne hij _)`. Apply `Units.ext` to reduce the goal to its premises. Simplify using `only [Units.val_mul, toGL_val]`. Rewrite using `[transvection_mul_transvection_same (h := hij), two_mul]`. Establish `e1` using `congrArg c h1`.

Establish `e3` using `congrArg c h3`. Rewrite `e1` using `[map_mul, map_mul, mul_comm (c D)]`. Establish `e1'` using `mul_right_cancel e1`. Rewrite `e3` using `[map_mul, ← e1']`. Conclude with `(mul_eq_left.mp e3)`.
-/
theorem map_transvection_eq_one (h2 : (2 : k) ≠ 0) {n : ℕ} (c : GL (Fin n) k →* ℂˣ) {i j : Fin n}
    (hij : i ≠ j) (t : k) : c (toGL (transvection i j t) (det_transvection_ne hij t)) = 1 := by
  set D := toGL _ (det_diag2_ne h2 i)
  have h1 : D * toGL (transvection i j t) (det_transvection_ne hij t)
      = toGL (transvection i j (2 * t)) (det_transvection_ne hij _) * D := by
    apply Units.ext; simp only [Units.val_mul, toGL_val, D]; exact conj_transvection hij t
  have h3 : toGL (transvection i j t) (det_transvection_ne hij t) * toGL (transvection i j t) (det_transvection_ne hij t)
      = toGL (transvection i j (2 * t)) (det_transvection_ne hij _) := by
    apply Units.ext; simp only [Units.val_mul, toGL_val]; rw [transvection_mul_transvection_same (h := hij), two_mul]
  have e1 := congrArg c h1
  have e3 := congrArg c h3
  rw [map_mul, map_mul, mul_comm (c D)] at e1
  have e1' := mul_right_cancel e1
  rw [map_mul, ← e1'] at e3
  exact (mul_eq_left.mp e3)

/- English proof (translation)
Use `det_permutation (R := k) σ` as an intermediate fact. Simplify using `only [Equiv.Perm.permMatrix] at this`. Rewrite using `[this]`. Apply the tactic sequence `rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]`.
-/
theorem det_perm_ne {n : ℕ} (σ : Equiv.Perm (Fin n)) : (σ.toPEquiv.toMatrix : Matrix (Fin n) (Fin n) k).det ≠ 0 := by
  have := det_permutation (R := k) σ
  simp only [Equiv.Perm.permMatrix] at this
  rw [this]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]

/- English proof (translation)
Use `set P := toGL _ (det_perm_ne (k := k) σ)`. Establish `h1 : P * diagGL n d = diagGL n (d ∘ σ) * P`. Apply `Units.ext` to reduce the goal to its premises. Simplify using `only [Units.val_mul, toGL_val, P, diagGL_val]`. Rewrite using `[PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]`.

Use extensionality with `a b`. Simplify using `[diagonal_apply, Equiv.eq_symm_apply]`. Establish `e` using `congrArg c h1`. Rewrite `e` using `[map_mul, map_mul, mul_comm (c P)]`. Conclude with `(mul_right_cancel e).symm`.
-/
theorem map_diagGL_perm {n : ℕ} (c : GL (Fin n) k →* ℂˣ) (σ : Equiv.Perm (Fin n)) (d : Fin n → kˣ) :
    c (diagGL n (d ∘ σ)) = c (diagGL n d) := by
  set P := toGL _ (det_perm_ne (k := k) σ)
  have h1 : P * diagGL n d = diagGL n (d ∘ σ) * P := by
    apply Units.ext
    simp only [Units.val_mul, toGL_val, P, diagGL_val]
    rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
    ext a b
    simp [diagonal_apply, Equiv.eq_symm_apply]
  have e := congrArg c h1
  rw [map_mul, map_mul, mul_comm (c P)] at e
  exact (mul_right_cancel e).symm

/- English proof (translation)
Establish `hs : ∀ i (x : kˣ), c (diagGL (m + 1) (Pi.mulSingle i x)) = c (diagGL (m + 1) (Pi.mulSingle 0 x))`. Introduce `i x`. Rewrite using `[← map_diagGL_perm c (Equiv.swap 0 i) (Pi.mulSingle i x)]`. Use `congr 2`. Use function extensionality and compare the values at `a`.

Simplify using `only [Function.comp_apply, Pi.mulSingle_apply, Equiv.swap_apply_eq_iff, Equiv.swap_apply_right]`. Establish `e : c (diagGL (m + 1) d) = (c.comp (diagGL (m + 1))) (∏ i, Pi.mulSingle i (d i))`. Rewrite using `[Finset.univ_prod_mulSingle]`. Both sides reduce to the same expression. Rewrite using `[e, map_prod, map_prod]`.

Simplify using `only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.mulSingle_apply]`. Conclude with `Finset.prod_congr rfl (fun i _ => hs i (d i))`.
-/
theorem map_diagGL_eq (c : GL (Fin (m + 1)) k →* ℂˣ) (d : Fin (m + 1) → kˣ) :
    c (diagGL (m + 1) d) = (c.comp (diagGL (m + 1))).comp (MonoidHom.mulSingle (fun _ => kˣ) 0) (∏ i, d i) := by
  have hs : ∀ i (x : kˣ), c (diagGL (m + 1) (Pi.mulSingle i x)) = c (diagGL (m + 1) (Pi.mulSingle 0 x)) := by
    intro i x
    rw [← map_diagGL_perm c (Equiv.swap 0 i) (Pi.mulSingle i x)]
    congr 2
    funext a
    simp only [Function.comp_apply, Pi.mulSingle_apply, Equiv.swap_apply_eq_iff, Equiv.swap_apply_right]
  have e : c (diagGL (m + 1) d) = (c.comp (diagGL (m + 1))) (∏ i, Pi.mulSingle i (d i)) := by
    rw [Finset.univ_prod_mulSingle]; rfl
  rw [e, map_prod, map_prod]
  simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.mulSingle_apply]
  exact Finset.prod_congr rfl (fun i _ => hs i (d i))

/- English proof (translation)
Consider the cases of `n with`. Consider the case `zero`. Use `⟨1, fun g => ?_⟩` and prove the remaining obligations. Establish `: g = 1` using `Units.ext (Matrix.ext fun i _ => i.elim0)`. Simplify using `[this]`.

Consider the case `succ m`. Use `⟨(c.comp (diagGL (m + 1))).comp (MonoidHom.mulSingle (fun _ => kˣ) 0), fun g => ?_⟩` and prove the remaining obligations. Use `set χ := (c.comp (diagGL (m + 1))).comp (MonoidHom.mulSingle (fun _ => kˣ) 0)`. Set `P : Matrix (Fin (m + 1)) (Fin (m + 1)) k → Prop` to `fun M => ∀ u : GL (Fin (m + 1)) k, (u : Matrix _ _ k) = M → c u = χ (Matrix.GeneralLinearGroup.det u)`. Establish `hg : Matrix.det (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) ≠ 0` using `(Matrix.isUnits_det_units g).ne_zero`.

Use `diagonal_transvection_induction_of_det_ne_zero P (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) hg ?_ ?_ ?_ g rfl` and prove the remaining obligations. Introduce `D hD u hu`. Establish `hD' : ∀ i, D i ≠ 0`. Introduce `i`. Rewrite `hD` using `[det_diagonal]`.

Conclude with `Finset.prod_ne_zero_iff.mp hD i (Finset.mem_univ i)`. Establish `hu' : u = diagGL (m + 1) (fun i => Units.mk0 (D i) (hD' i))`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[hu, diagGL_val]`. Both sides reduce to the same expression.

Establish `hdet : Matrix.GeneralLinearGroup.det u = ∏ i, Units.mk0 (D i) (hD' i)`. Apply `Units.ext` to reduce the goal to its premises. Simplify using `[hu, det_diagonal]`. Rewrite using `[hdet, hu', map_diagGL_eq]`. Introduce `t u hu`.

Establish `hu' : u = toGL (transvection t.i t.j t.c) (det_transvection_ne t.hij t.c)` using `Units.ext hu`. Establish `hdet : Matrix.GeneralLinearGroup.det u = 1`. Apply `Units.ext` to reduce the goal to its premises. Simplify using `[hu, TransvectionStruct.toMatrix, det_transvection_of_ne _ _ t.hij]`. Rewrite using `[hdet, map_one, hu']`.

Conclude with `map_transvection_eq_one h2 c t.hij t.c`. Introduce `A B hA hB PA PB u hu`. Establish `hu' : u = toGL A hA * toGL B hB` using `Units.ext (by simp [hu])`. Rewrite using `[hu', map_mul, map_mul, PA _ rfl, PB _ rfl, ← map_mul]`.
-/
theorem factors_through_det (h2 : (2 : k) ≠ 0) {n : ℕ} (c : GL (Fin n) k →* ℂˣ) :
    ∃ χ : kˣ →* ℂˣ, ∀ g, c g = χ (Matrix.GeneralLinearGroup.det g) := by
  cases n with
  | zero =>
    refine ⟨1, fun g => ?_⟩
    have : g = 1 := Units.ext (Matrix.ext fun i _ => i.elim0)
    simp [this]
  | succ m =>
    refine ⟨(c.comp (diagGL (m + 1))).comp (MonoidHom.mulSingle (fun _ => kˣ) 0), fun g => ?_⟩
    set χ := (c.comp (diagGL (m + 1))).comp (MonoidHom.mulSingle (fun _ => kˣ) 0)
    let P : Matrix (Fin (m + 1)) (Fin (m + 1)) k → Prop := fun M =>
      ∀ u : GL (Fin (m + 1)) k, (u : Matrix _ _ k) = M → c u = χ (Matrix.GeneralLinearGroup.det u)
    have hg : Matrix.det (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) ≠ 0 := (Matrix.isUnits_det_units g).ne_zero
    refine diagonal_transvection_induction_of_det_ne_zero P (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) hg ?_ ?_ ?_ g rfl
    · intro D hD u hu
      have hD' : ∀ i, D i ≠ 0 := by
        intro i; rw [det_diagonal] at hD; exact Finset.prod_ne_zero_iff.mp hD i (Finset.mem_univ i)
      have hu' : u = diagGL (m + 1) (fun i => Units.mk0 (D i) (hD' i)) := by
        apply Units.ext; rw [hu, diagGL_val]; rfl
      have hdet : Matrix.GeneralLinearGroup.det u = ∏ i, Units.mk0 (D i) (hD' i) := by
        apply Units.ext; simp [hu, det_diagonal]
      rw [hdet, hu', map_diagGL_eq]
    · intro t u hu
      have hu' : u = toGL (transvection t.i t.j t.c) (det_transvection_ne t.hij t.c) := Units.ext hu
      have hdet : Matrix.GeneralLinearGroup.det u = 1 := by
        apply Units.ext; simp [hu, TransvectionStruct.toMatrix, det_transvection_of_ne _ _ t.hij]
      rw [hdet, map_one, hu']
      exact map_transvection_eq_one h2 c t.hij t.c
    · intro A B hA hB PA PB u hu
      have hu' : u = toGL A hA * toGL B hB := Units.ext (by simp [hu])
      rw [hu', map_mul, map_mul, PA _ rfl, PB _ rfl, ← map_mul]

end GlobalTheory.DetFactor

/- English proof (translation)
Introduce `k _ h2 n c`. Conclude with `GlobalTheory.DetFactor.factors_through_det h2 c`.
-/
theorem GlobalTheory.ghom_factors_through_det : ∀ {k : Type} [Field k], (2 : k) ≠ 0 → ∀ {n : ℕ} (c : GL (Fin n) k →* ℂˣ),
    ∃ χ : kˣ →* ℂˣ, ∀ g, c g = χ (Matrix.GeneralLinearGroup.det g) :=
  by intro k _ h2 n c; exact GlobalTheory.DetFactor.factors_through_det h2 c
