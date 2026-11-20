import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.InductiveHeisenbergInputs

noncomputable section

open Matrix MeasureTheory
open scoped ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

namespace FormulaFAux

def sg (k r : ℕ) (i : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) :=
  if r ≤ i.val ∧ i.val ≤ r + k then i else ⟨2 * r + k - i.val, by omega⟩

/- English proof (translation)
Apply the tactic sequence `unfold sg; split_ifs <;> rfl`.
-/
theorem sg_val (k r : ℕ) (i : Fin (2 * r + k + 1)) :
    (sg k r i).val = if r ≤ i.val ∧ i.val ≤ r + k then i.val else 2 * r + k - i.val := by
  unfold sg; split_ifs <;> rfl

/- English proof (translation)
Apply the tactic sequence `apply Fin.ext; rw [sg_val, sg_val]; split_ifs <;> omega`.
-/
theorem sg_sg (k r : ℕ) (i : Fin (2 * r + k + 1)) : sg k r (sg k r i) = i := by
  apply Fin.ext; rw [sg_val, sg_val]; split_ifs <;> omega

/- English proof (translation)
Establish `key : j = sg k r i ↔ j.val = (if r ≤ i.val ∧ i.val ≤ r + k then i.val else 2 * r + k - i.val)`. Rewrite using `[← sg_val, Fin.ext_iff]`. Unfold `Hpk`. Simplify using `only [key, Fin.ext_iff]`. Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; omega)`.
-/
theorem hpk_apply (k r : ℕ) (i j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j = sg k r i then (if i.val = r + k then -1 else 1) else 0 := by
  have key : j = sg k r i ↔ j.val = (if r ≤ i.val ∧ i.val ≤ r + k then i.val else 2 * r + k - i.val) := by
    rw [← sg_val, Fin.ext_iff]
  unfold Hpk
  simp only [key, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

/- English proof (translation)
Simplify using `[mulVec, dotProduct, hpk_apply]`.
-/
theorem hpk_mulVec (k r : ℕ) (w : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) :
    (Hpk k r *ᵥ w) i = (if i.val = r + k then -1 else 1) * w (sg k r i) := by
  simp [mulVec, dotProduct, hpk_apply]

/- English proof (translation)
Simplify using `only [dotProduct, Pi.star_apply, hpk_mulVec]`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> simp`. Use `_ = ∑ i, star (u i) * w i := Fintype.sum_equiv (Function.Involutive.toPerm _ (sg_sg k r)) _ _ (fun i => rfl)`.
-/
theorem star_hpk_dot (k r : ℕ) (u w : Fin (2 * r + k + 1) → ℂ) :
    star (Hpk k r *ᵥ u) ⬝ᵥ (Hpk k r *ᵥ w) = star u ⬝ᵥ w := by
  simp only [dotProduct, Pi.star_apply, hpk_mulVec]
  calc ∑ i, star ((if i.val = r + k then -1 else 1 : ℂ) * u (sg k r i)) * ((if i.val = r + k then -1 else 1) * w (sg k r i))
      = ∑ i, star (u (sg k r i)) * w (sg k r i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        split_ifs <;> simp
    _ = ∑ i, star (u i) * w i :=
        Fintype.sum_equiv (Function.Involutive.toPerm _ (sg_sg k r)) _ _ (fun i => rfl)

abbrev cc : ℂ := ((Real.sqrt 2)⁻¹ : ℂ)

/- English proof (translation)
Establish `h : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2`. Rewrite using `[← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num`. Establish `h0 : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0`. Introduce `h'`. Rewrite `h` using `[h', zero_pow two_ne_zero]`.

Evaluate the numerical expressions using `at h`. Simplify using `only [cc]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[h]`.
-/
theorem cc_sq : cc * cc = 1 / 2 := by
  have h : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have h0 : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    intro h'; rw [h', zero_pow two_ne_zero] at h; norm_num at h
  simp only [cc]; field_simp; rw [h]

def aF (k r : ℕ) (y : Fin (2 * r + k + 1) → ℂ) (t : Fin (r + 1)) : ℂ :=
  if h : t.val < r then y (eI k r ⟨t.val, h⟩) else cc * (y (wI k r 0) - y (wI k r (Fin.last k)))

def aF' (k r : ℕ) (y : Fin (2 * r + k + 1) → ℂ) (t : Fin (r + 1)) : ℂ :=
  if h : t.val < r then y (esI k r ⟨t.val, h⟩) else cc * (y (wI k r 0) + y (wI k r (Fin.last k)))

/- English proof (translation)
Introduce `i j h; simp only [levPos, Fin.ext_iff] at h; exact Fin.ext (by omega)`.
-/
theorem levPos_inj (k r' : ℕ) : Function.Injective (levPos k 1 r') := by
  intro i j h; simp only [levPos, Fin.ext_iff] at h; exact Fin.ext (by omega)

/- English proof (translation)
Unfold `liftVec; rw [dif_pos (by simp only [levPos]; omega)]; congr 1`.
-/
theorem lift_levPos (k r' : ℕ) (v : Fin (2 * r' + k + 1) → ℂ) (i : Fin (2 * r' + k + 1)) :
    liftVec k 1 r' v (levPos k 1 r' i) = v i := by
  unfold liftVec; rw [dif_pos (by simp only [levPos]; omega)]; congr 1

/- English proof (translation)
Simplify using `only [liftVec]`. Rewrite using `[dif_neg]`. Introduce and unpack `⟨h1, h2⟩`. Conclude with `hp ⟨⟨p.val - 1, by omega⟩, Fin.ext (by simp [levPos]; omega)⟩`.
-/
theorem lift_zero (k r' : ℕ) (v : Fin (2 * r' + k + 1) → ℂ) (p : Fin (2 * (1 + r') + k + 1))
    (hp : p ∉ Set.range (levPos k 1 r')) : liftVec k 1 r' v p = 0 := by
  simp only [liftVec]; rw [dif_neg]; rintro ⟨h1, h2⟩
  exact hp ⟨⟨p.val - 1, by omega⟩, Fin.ext (by simp [levPos]; omega)⟩

/- English proof (translation)
Simplify using `only [dotProduct, Pi.star_apply]`. Use `symm`. Use `Fintype.sum_of_injective _ (levPos_inj k r') _ _ (fun p hp => ?_) (fun i => ?_)` and prove the remaining obligations. Rewrite using `[lift_zero _ _ v _ hp, mul_zero]`. Rewrite using `[lift_levPos, lift_levPos]`.
-/
theorem lift_dot (k r' : ℕ) (u v : Fin (2 * r' + k + 1) → ℂ) :
    star (liftVec k 1 r' u) ⬝ᵥ liftVec k 1 r' v = star u ⬝ᵥ v := by
  simp only [dotProduct, Pi.star_apply]
  symm
  refine Fintype.sum_of_injective _ (levPos_inj k r') _ _ (fun p hp => ?_) (fun i => ?_)
  · rw [lift_zero _ _ v _ hp, mul_zero]
  · rw [lift_levPos, lift_levPos]

/- English proof (translation)
Set `al : Fin (m + 1) → ℂ` to `Fin.cases 1 (fun _ => 0)`. Set `xh : Fin (m + 1) → ℂ` to `Fin.cases 0 (fun j => x j)`. Set `ah : Fin (m + 1) → ℂ` to `Fin.cases 0 (fun j => a j)`. Set `U : Matrix (Fin (m + 1)) (Fin 3) ℂ` to `Matrix.of fun i q => ![al i, xh i, ah i] q`. Set `V : Matrix (Fin 3) (Fin (m + 1)) ℂ` to `Matrix.of fun q j => ![c * al j + star (xh j), al j, star (ah j)] q`.

Establish `hM : Mx = 1 + U * V`. Use extensionality with `i j`. Apply the tactic sequence `refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j`. Simplify using `[h00, U, V, al, xh, ah, Matrix.mul_apply, Fin.sum_univ_three]`. Simplify using `[h0j, U, V, al, xh, ah, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply, (Fin.succ_ne_zero j).symm]`.

Simplify using `[hj0, U, V, al, xh, ah, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply]`. Simplify using `[hij, U, V, al, xh, ah, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply, Fin.succ_inj]`. Rewrite using `[hM, det_one_add_mul_comm, det_fin_three]`. Simplify using `only [← Fin.sum_univ_eq_sum_range]`. Simplify using `[U, V, al, xh, ah, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem gram_det (m : ℕ) (Mx : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (c : ℂ) (x a : ℕ → ℂ)
    (h00 : Mx 0 0 = 1 + c) (h0j : ∀ j : Fin m, Mx 0 j.succ = star (x j))
    (hj0 : ∀ j : Fin m, Mx j.succ 0 = x j)
    (hij : ∀ i j : Fin m, Mx i.succ j.succ = (if i = j then 1 else 0) + a i * star (a j)) :
    Mx.det = (1 + c - ∑ j ∈ Finset.range m, star (x j) * x j) * (1 + ∑ j ∈ Finset.range m, star (a j) * a j) +
      (∑ j ∈ Finset.range m, star (x j) * a j) * (∑ j ∈ Finset.range m, star (a j) * x j) := by
  let al : Fin (m + 1) → ℂ := Fin.cases 1 (fun _ => 0)
  let xh : Fin (m + 1) → ℂ := Fin.cases 0 (fun j => x j)
  let ah : Fin (m + 1) → ℂ := Fin.cases 0 (fun j => a j)
  let U : Matrix (Fin (m + 1)) (Fin 3) ℂ := Matrix.of fun i q => ![al i, xh i, ah i] q
  let V : Matrix (Fin 3) (Fin (m + 1)) ℂ := Matrix.of fun q j => ![c * al j + star (xh j), al j, star (ah j)] q
  have hM : Mx = 1 + U * V := by
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · simp [h00, U, V, al, xh, ah, Matrix.mul_apply, Fin.sum_univ_three]
    · simp [h0j, U, V, al, xh, ah, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply, (Fin.succ_ne_zero j).symm]
    · simp [hj0, U, V, al, xh, ah, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply]
    · simp [hij, U, V, al, xh, ah, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply, Fin.succ_inj]
  rw [hM, det_one_add_mul_comm, det_fin_three]
  simp only [← Fin.sum_univ_eq_sum_range]
  simp [U, V, al, xh, ah, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
  ring

end FormulaFAux

end ReciprocityTheory.ChartRestriction.DS.Xi
