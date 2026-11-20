import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.FramesTor

noncomputable section

namespace Formalism.MainNotions.S.Pv.Frames

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S

/- English proof (translation)
Use `congrFun hc p` as an intermediate fact. Simplify using `only [bvec, Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this`. Conclude with `this`.
-/
theorem col_of_fix {m : ℕ} {h : Matrix (Fin m) (Fin m) ℂ} {c : Fin m} (hc : h *ᵥ bvec c = bvec c) (p : Fin m) :
    h p c = if p = c then 1 else 0 := by
  have := congrFun hc p
  simp only [bvec, Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
  exact this

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem eI_val {k r : ℕ} (a : Fin r) : (eI k r a).val = a.val := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem esI_val {k r : ℕ} (a : Fin r) : (esI k r a).val = 2 * r + k - a.val := rfl

/- English proof (translation)
Establish `ha` using `a.isLt`. Establish `e1 : (esI k r a).val = 2 * r + k - a.val` using `rfl`. Unfold `Hpk`. Distinguish the cases in `hq : q = eI k r a`. Establish `hqv : q.val = a.val` using `by rw [hq]; rfl`.

Apply the tactic sequence `rw [if_pos hq, if_neg (fun h => by have := h.1; omega), if_pos (by constructor <;> omega)]`. Establish `hqv : q.val ≠ a.val` using `fun e => hq (Fin.ext e)`. Rewrite using `[if_neg hq, if_neg (fun h => by have := h.1; omega), if_neg (fun h => by have := h.2; omega), if_neg (fun h => by have := h.1; have := h.2.1; omega)]`.
-/
theorem Hpk_esI_row {k r : ℕ} (a : Fin r) (q : Fin (2 * r + k + 1)) :
    Hpk k r (esI k r a) q = if q = eI k r a then 1 else 0 := by
  have ha := a.isLt
  have e1 : (esI k r a).val = 2 * r + k - a.val := rfl
  unfold Hpk
  by_cases hq : q = eI k r a
  · have hqv : q.val = a.val := by rw [hq]; rfl
    rw [if_pos hq, if_neg (fun h => by have := h.1; omega), if_pos (by constructor <;> omega)]
  · have hqv : q.val ≠ a.val := fun e => hq (Fin.ext e)
    rw [if_neg hq, if_neg (fun h => by have := h.1; omega), if_neg (fun h => by have := h.2; omega),
      if_neg (fun h => by have := h.1; have := h.2.1; omega)]

/- English proof (translation)
Establish `ha` using `a.isLt`. Establish `e1 : (eI k r a).val = a.val` using `rfl`. Unfold `Hpk`. Distinguish the cases in `hq : q = esI k r a`. Establish `hqv : q.val = 2 * r + k - a.val` using `by rw [hq]; rfl`.

Apply the tactic sequence `rw [if_pos hq, if_pos (by constructor <;> omega)]`. Establish `hqv : q.val ≠ 2 * r + k - a.val` using `fun e => hq (Fin.ext e)`. Rewrite using `[if_neg hq, if_neg (fun h => by have := h.2; omega), if_neg (fun h => by have := h.2; omega), if_neg (fun h => by have := h.1; omega)]`.
-/
theorem Hpk_eI_row {k r : ℕ} (a : Fin r) (q : Fin (2 * r + k + 1)) :
    Hpk k r (eI k r a) q = if q = esI k r a then 1 else 0 := by
  have ha := a.isLt
  have e1 : (eI k r a).val = a.val := rfl
  unfold Hpk
  by_cases hq : q = esI k r a
  · have hqv : q.val = 2 * r + k - a.val := by rw [hq]; rfl
    rw [if_pos hq, if_pos (by constructor <;> omega)]
  · have hqv : q.val ≠ 2 * r + k - a.val := fun e => hq (Fin.ext e)
    rw [if_neg hq, if_neg (fun h => by have := h.2; omega), if_neg (fun h => by have := h.2; omega),
      if_neg (fun h => by have := h.1; omega)]

/- English proof (translation)
Unfold `Hpk`. Rewrite using `[if_neg (fun h => by have := h.1; have := h.2; omega), if_neg (fun h => by have := h.1; omega), if_neg (fun h => by have := h.1; have := h.2.1; omega)]`.
-/
theorem Hpk_mid_col {k r : ℕ} (i j : Fin (2 * r + k + 1)) (hj1 : r ≤ j.val) (hj2 : j.val ≤ r + k)
    (hi : i.val < r ∨ r + k < i.val) : Hpk k r i j = 0 := by
  unfold Hpk
  rw [if_neg (fun h => by have := h.1; have := h.2; omega), if_neg (fun h => by have := h.1; omega),
    if_neg (fun h => by have := h.1; have := h.2.1; omega)]

/- English proof (translation)
Establish `key` using `congrArg (fun M : Matrix (Fin m) (Fin m) ℂ => M c j) hUH`. Simplify using `only [Matrix.mul_apply, Matrix.conjTranspose_apply, hc] at key`. Simplify `key` using `[apply_ite star, star_one, star_zero, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ]`.
-/
theorem UH_entry {m : ℕ} {H h : Matrix (Fin m) (Fin m) ℂ} (hUH : hᴴ * H * h = H) {c : Fin m}
    (hc : ∀ p, h p c = if p = c then 1 else 0) (j : Fin m) : ∑ q, H c q * h q j = H c j := by
  have key := congrArg (fun M : Matrix (Fin m) (Fin m) ℂ => M c j) hUH
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hc] at key
  simpa [apply_ite star, star_one, star_zero, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ] using key

/- English proof (translation)
Establish `hU' : hᴴ * Hpk k r * h = Hpk k r` using `hU`. Distinguish the cases in `hjl : j.val < r`. Use `col_of_fix (hfix ⟨j.val, hjl⟩).1 i` as an intermediate fact. Establish `hj : eI k r ⟨j.val, hjl⟩ = j` using `Fin.ext rfl`. Rewrite `this` using `[hj]`.

Rewrite `hne` using `[this]`. Use `split_ifs at hne with e`. Rewrite using `[e]`. Conclude with `absurd rfl hne`. Distinguish the cases in `hjh : r + k < j.val`.

Establish `ha : 2 * r + k - j.val < r` using `by omega`. Use `col_of_fix (hfix ⟨2 * r + k - j.val, ha⟩).2 i` as an intermediate fact. Establish `hj : esI k r ⟨2 * r + k - j.val, ha⟩ = j` using `Fin.ext (by show 2 * r + k - (2 * r + k - j.val) = j.val; omega)`. Rewrite `this` using `[hj]`. Rewrite `hne` using `[this]`.

Use `split_ifs at hne with e`. Rewrite using `[e]`. Conclude with `absurd rfl hne`. Use `push Not at hjl hjh`. Rewrite using `[dT_mid j hjl hjh]`.

Distinguish the cases in `hil : i.val < r`. Use `exfalso set a : Fin r := ⟨i.val, hil⟩`. Establish `hcol` using `col_of_fix (hfix a).2`. Apply the tactic sequence `have e := UH_entry hU' hcol j`. Establish `s1 : ∑ q, Hpk k r (esI k r a) q * h q j = h (eI k r a) j`.

Simplify using `only [Hpk_esI_row, ite_mul, one_mul, zero_mul]`. Simplify using `[Finset.sum_ite_eq']`. Rewrite `e` using `[s1, Hpk_mid_col _ j hjl hjh (Or.inr (by show r + k < 2 * r + k - i.val; omega))]`. Establish `hi : eI k r a = i` using `Fin.ext rfl`. Rewrite `e` using `[hi]`.

Conclude with `hne e`. Distinguish the cases in `hih : r + k < i.val`. It suffices to derive a contradiction. Establish `ha : 2 * r + k - i.val < r` using `by omega`. Use `set a : Fin r := ⟨2 * r + k - i.val, ha⟩`.

Establish `hcol` using `col_of_fix (hfix a).1`. Apply the tactic sequence `have e := UH_entry hU' hcol j`. Establish `s1 : ∑ q, Hpk k r (eI k r a) q * h q j = h (esI k r a) j`. Simplify using `only [Hpk_eI_row, ite_mul, one_mul, zero_mul]`. Simplify using `[Finset.sum_ite_eq']`.

Rewrite `e` using `[s1, Hpk_mid_col _ j hjl hjh (Or.inl (by show (2 * r + k - i.val) < r; omega))]`. Establish `hi : esI k r a = i` using `Fin.ext (by show 2 * r + k - (2 * r + k - i.val) = i.val; omega)`. Rewrite `e` using `[hi]`. Conclude with `hne e`. Use `push Not at hil hih`.

Conclude with `dT_mid i hil hih`.
-/
theorem fix_dT {k r : ℕ} {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hU : h ∈ UH (Hpk k r))
    (hfix : ∀ a : Fin r, h *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ h *ᵥ bvec (esI k r a) = bvec (esI k r a))
    (i j : Fin (2 * r + k + 1)) (hne : h i j ≠ 0) : dT k r i = dT k r j := by
  have hU' : hᴴ * Hpk k r * h = Hpk k r := hU
  by_cases hjl : j.val < r
  · have := col_of_fix (hfix ⟨j.val, hjl⟩).1 i
    have hj : eI k r ⟨j.val, hjl⟩ = j := Fin.ext rfl
    rw [hj] at this
    rw [this] at hne
    split_ifs at hne with e
    · rw [e]
    · exact absurd rfl hne
  by_cases hjh : r + k < j.val
  · have ha : 2 * r + k - j.val < r := by omega
    have := col_of_fix (hfix ⟨2 * r + k - j.val, ha⟩).2 i
    have hj : esI k r ⟨2 * r + k - j.val, ha⟩ = j := Fin.ext (by show 2 * r + k - (2 * r + k - j.val) = j.val; omega)
    rw [hj] at this
    rw [this] at hne
    split_ifs at hne with e
    · rw [e]
    · exact absurd rfl hne
  push Not at hjl hjh
  rw [dT_mid j hjl hjh]
  by_cases hil : i.val < r
  · exfalso
    set a : Fin r := ⟨i.val, hil⟩
    have hcol := col_of_fix (hfix a).2
    have e := UH_entry hU' hcol j
    have s1 : ∑ q, Hpk k r (esI k r a) q * h q j = h (eI k r a) j := by
      simp only [Hpk_esI_row, ite_mul, one_mul, zero_mul]
      simp [Finset.sum_ite_eq']
    rw [s1, Hpk_mid_col _ j hjl hjh (Or.inr (by show r + k < 2 * r + k - i.val; omega))] at e
    have hi : eI k r a = i := Fin.ext rfl
    rw [hi] at e
    exact hne e
  by_cases hih : r + k < i.val
  · exfalso
    have ha : 2 * r + k - i.val < r := by omega
    set a : Fin r := ⟨2 * r + k - i.val, ha⟩
    have hcol := col_of_fix (hfix a).1
    have e := UH_entry hU' hcol j
    have s1 : ∑ q, Hpk k r (eI k r a) q * h q j = h (esI k r a) j := by
      simp only [Hpk_eI_row, ite_mul, one_mul, zero_mul]
      simp [Finset.sum_ite_eq']
    rw [s1, Hpk_mid_col _ j hjl hjh (Or.inl (by show (2 * r + k - i.val) < r; omega))] at e
    have hi : esI k r a = i := Fin.ext (by show 2 * r + k - (2 * r + k - i.val) = i.val; omega)
    rw [hi] at e
    exact hne e
  push Not at hil hih
  exact dT_mid i hil hih

/- English proof (translation)
The claim follows from `fix_dT hh.1 hh.2.1 i j hne`.
-/
theorem UW_dT {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hh : h ∈ UWset k r z) (i j : Fin (2 * r + k + 1)) (hne : h i j ≠ 0) : dT k r i = dT k r j :=
  fix_dT hh.1 hh.2.1 i j hne

/- English proof (translation)
The claim follows from `conjI_eq_self (UW_dT hh)`.
-/
theorem UW_conjI {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hh : h ∈ UWset k r z) : tTi k r * h * tT k r = h := conjI_eq_self (UW_dT hh)

/- English proof (translation)
The claim follows from `conj_eq_self (UW_dT hh)`.
-/
theorem UW_conj {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hh : h ∈ UWset k r z) : tT k r * h * tTi k r = h := conj_eq_self (UW_dT hh)

/- English proof (translation)
Rewrite using `[Matrix.mul_inv_rev, Matrix.mul_inv_rev, tTi_inv, tT_inv, Matrix.mul_assoc]`.
-/
theorem conj_inv {k r : ℕ} (M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    tT k r * M⁻¹ * tTi k r = (tT k r * M * tTi k r)⁻¹ := by
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, tTi_inv, tT_inv, Matrix.mul_assoc]

/- English proof (translation)
Rewrite using `[Matrix.mul_inv_rev, Matrix.mul_inv_rev, tTi_inv, tT_inv, Matrix.mul_assoc]`.
-/
theorem conjI_inv {k r : ℕ} (M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    tTi k r * M⁻¹ * tT k r = (tTi k r * M * tT k r)⁻¹ := by
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, tTi_inv, tT_inv, Matrix.mul_assoc]

/- English proof (translation)
Unfold `bigCell at hne`. Use `split_ifs at hne with h1 h2 h3 h4 h5`. Rewrite using `[h2, dT_esI]`. Unfold `dT`. Simplify using `[h1]`.

Conclude with `absurd rfl hne`. Rewrite using `[dT_mid i h4.1 h4.2, dT_mid j (by omega) h3]`. Conclude with `absurd rfl hne`. Establish `hi : i.val < r` using `by omega`. Conclude with `(dT_pair i j hi (by omega)).symm`.

Conclude with `absurd rfl hne`.
-/
theorem bigCell_dT {k r : ℕ} (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (i j : Fin (2 * r + k + 1))
    (hne : bigCell k r c μ i j ≠ 0) : dT k r i = dT k r j := by
  unfold bigCell at hne
  split_ifs at hne with h1 h2 h3 h4 h5
  · rw [h2, dT_esI]
    unfold dT; simp [h1]
  · exact absurd rfl hne
  · rw [dT_mid i h4.1 h4.2, dT_mid j (by omega) h3]
  · exact absurd rfl hne
  · have hi : i.val < r := by omega
    exact (dT_pair i j hi (by omega)).symm
  · exact absurd rfl hne

/- English proof (translation)
The claim follows from `conjI_eq_self (bigCell_dT c μ)`.
-/
theorem bigCell_conjI {k r : ℕ} (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    tTi k r * bigCell k r c μ * tT k r = bigCell k r c μ := conjI_eq_self (bigCell_dT c μ)

end Formalism.MainNotions.S.Pv.Frames

end
