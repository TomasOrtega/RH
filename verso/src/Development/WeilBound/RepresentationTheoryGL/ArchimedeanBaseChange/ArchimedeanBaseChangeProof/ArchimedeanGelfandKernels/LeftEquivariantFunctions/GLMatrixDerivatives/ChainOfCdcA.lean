import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.ChainOfSt

noncomputable section

open Matrix Finset

namespace PositivityTheory.RgBcC.LfSt.ChainPf.Cdc

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat hb)

variable {n : ℕ}

/- English proof (translation)
The claim follows from `isOpen_ne_fun (continuous_id.matrix_det) continuous_const`.
-/
theorem isOpen_GLs : IsOpen (GLs n) :=
  isOpen_ne_fun (continuous_id.matrix_det) continuous_const

/- English proof (translation)
Take `⟨a, b⟩` from `p`. Unfold `hb`. Use `split_ifs with h1 h2`. Simplify using `[Matrix.IsHermitian, Matrix.conjTranspose_single]`. Simplify using `only [Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_single]`.

Simplify using `[add_comm]`. Simplify using `only [Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_single]`. Simplify using `[star_mul', Complex.conj_I]`. Rewrite using `[← smul_neg, neg_sub]`.
-/
theorem hb_herm (p : Fin n × Fin n) : (hb p : Mat n).IsHermitian := by
  obtain ⟨a, b⟩ := p
  unfold hb
  split_ifs with h1 h2
  · simp [Matrix.IsHermitian, Matrix.conjTranspose_single]
  · simp only [Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_single]
    simp [add_comm]
  · simp only [Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_single]
    simp [star_mul', Complex.conj_I]
    rw [← smul_neg, neg_sub]

/- English proof (translation)
Take `⟨a, b⟩` from `p`. Unfold `hb`. Simplify using `only`. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality.

Simplify using `only [if_true, Matrix.single_apply]`. Rewrite using `[if_neg hab, if_neg hab]`. Distinguish the cases in `hlt : a < b`. Rewrite using `[if_pos hlt, if_pos hlt]`. Simplify using `only [Matrix.smul_apply, Matrix.add_apply, Matrix.single_apply, smul_eq_mul]`.

Rewrite using `[if_neg hlt, if_neg hlt]`. Simplify using `only [Matrix.smul_apply, Matrix.sub_apply, Matrix.single_apply, smul_eq_mul]`.
-/
theorem hb_apply (p : Fin n × Fin n) (i j : Fin n) : (hb p : Mat n) i j =
    if p.1 = p.2 then (if p.1 = i ∧ p.1 = j then 1 else 0)
    else if p.1 < p.2 then ((Real.sqrt 2)⁻¹ : ℂ) * ((if p.1 = i ∧ p.2 = j then 1 else 0) + (if p.2 = i ∧ p.1 = j then 1 else 0))
    else (((Real.sqrt 2)⁻¹ : ℂ) * Complex.I) * ((if p.1 = i ∧ p.2 = j then 1 else 0) - (if p.2 = i ∧ p.1 = j then 1 else 0)) := by
  obtain ⟨a, b⟩ := p
  unfold hb
  dsimp only
  by_cases hab : a = b
  · subst hab
    simp only [if_true, Matrix.single_apply]
  · rw [if_neg hab, if_neg hab]
    by_cases hlt : a < b
    · rw [if_pos hlt, if_pos hlt]
      simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.single_apply, smul_eq_mul]
    · rw [if_neg hlt, if_neg hlt]
      simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.single_apply, smul_eq_mul]

/- English proof (translation)
Take `⟨a, b⟩` from `p`. Unfold `hb`. Simplify using `only`. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality.

Simplify using `[Matrix.trace_mul_single]`. Rewrite using `[if_neg hab, if_neg hab]`. Distinguish the cases in `hlt : a < b`. Rewrite using `[if_pos hlt, if_pos hlt]`. Simplify using `[Matrix.mul_add, Matrix.trace_add, Matrix.trace_mul_single]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[if_neg hlt, if_neg hlt]`. Simplify using `[Matrix.mul_sub, Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_mul_single]`.
-/
theorem hb_tr (H : Mat n) (p : Fin n × Fin n) : (H * hb p).trace =
    if p.1 = p.2 then H p.1 p.1
    else if p.1 < p.2 then ((Real.sqrt 2)⁻¹ : ℂ) * (H p.2 p.1 + H p.1 p.2)
    else (((Real.sqrt 2)⁻¹ : ℂ) * Complex.I) * (H p.2 p.1 - H p.1 p.2) := by
  obtain ⟨a, b⟩ := p
  unfold hb
  dsimp only
  by_cases hab : a = b
  · subst hab
    simp [Matrix.trace_mul_single]
  · rw [if_neg hab, if_neg hab]
    by_cases hlt : a < b
    · rw [if_pos hlt, if_pos hlt]
      simp [Matrix.mul_add, Matrix.trace_add, Matrix.trace_mul_single]
      ring
    · rw [if_neg hlt, if_neg hlt]
      simp [Matrix.mul_sub, Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_mul_single]

/- English proof (translation)
Rewrite using `[← Complex.ofReal_inv]`. Establish `hc2 : s⁻¹ * s⁻¹ = 1 / 2` using `by rw [← mul_inv, hs]; norm_num`. Apply `Complex.ext` to reduce the goal to its premises. Simplify using `[Complex.mul_re, Complex.mul_im]`. Take the linear combination `(2 * h.re) * hc2`.

Simplify using `[Complex.mul_re, Complex.mul_im]`. Take the linear combination `(2 * h.im) * hc2`.
-/
theorem key_pair (h : ℂ) (s : ℝ) (hs : s * s = 2) :
    (((((s : ℂ))⁻¹ * (star h + h)).re : ℝ) : ℂ) * ((s : ℂ))⁻¹ +
      (((((s : ℂ))⁻¹ * Complex.I * (h - star h)).re : ℝ) : ℂ) * (-((s : ℂ))⁻¹ * Complex.I) = h := by
  rw [← Complex.ofReal_inv]
  have hc2 : s⁻¹ * s⁻¹ = 1 / 2 := by rw [← mul_inv, hs]; norm_num
  apply Complex.ext
  · simp [Complex.mul_re, Complex.mul_im]
    linear_combination (2 * h.re) * hc2
  · simp [Complex.mul_re, Complex.mul_im]
    linear_combination (2 * h.im) * hc2

/- English proof (translation)
Rewrite using `[← Complex.ofReal_inv]`. Establish `hc2 : s⁻¹ * s⁻¹ = 1 / 2` using `by rw [← mul_inv, hs]; norm_num`. Apply `Complex.ext` to reduce the goal to its premises. Simplify using `[Complex.mul_re, Complex.mul_im]`. Take the linear combination `(2 * h.re) * hc2`.

Simplify using `[Complex.mul_re, Complex.mul_im]`. Take the linear combination `(2 * h.im) * hc2`.
-/
theorem key_pair2 (h : ℂ) (s : ℝ) (hs : s * s = 2) :
    (((((s : ℂ))⁻¹ * Complex.I * (star h - h)).re : ℝ) : ℂ) * (((s : ℂ))⁻¹ * Complex.I) +
      (((((s : ℂ))⁻¹ * (h + star h)).re : ℝ) : ℂ) * ((s : ℂ))⁻¹ = h := by
  rw [← Complex.ofReal_inv]
  have hc2 : s⁻¹ * s⁻¹ = 1 / 2 := by rw [← mul_inv, hs]; norm_num
  apply Complex.ext
  · simp [Complex.mul_re, Complex.mul_im]
    linear_combination (2 * h.re) * hc2
  · simp [Complex.mul_re, Complex.mul_im]
    linear_combination (2 * h.im) * hc2

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Matrix.sum_apply, Matrix.smul_apply]`. Establish `hji : H j i = star (H i j)` using `(hH.apply j i).symm`. Establish `hs : Real.sqrt 2 * Real.sqrt 2 = 2` using `Real.mul_self_sqrt (by norm_num)`. Distinguish the cases in `hij : i = j`.

Substitute `hij` using the available equality. Establish `him : (H i i).im = 0`. Use `congrArg Complex.im (hH.apply i i)` as an intermediate fact. Simplify using `only [Complex.star_def, Complex.conj_im] at this`. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite using `[Finset.sum_eq_single (i, i)]`. Rewrite using `[hb_tr, hb_apply]`. Simplify using `only [if_true, and_self, Complex.real_smul, mul_one]`. Apply the tactic sequence `apply Complex.ext <;> simp [him]`. Introduce `p _ hp`.

Take `⟨a, b⟩` from `p`. Establish `hne : ¬(a = i ∧ b = i)` using `fun h => hp (by rw [h.1, h.2])`. Establish `hne' : ¬(b = i ∧ a = i)` using `fun h => hne ⟨h.2, h.1⟩`. Rewrite using `[hb_apply]`. Simplify using `only`.

Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality. Rewrite using `[if_pos rfl, if_neg hne, smul_zero]`. Apply the tactic sequence `rw [if_neg hab, if_neg hne, if_neg hne'] split_ifs <;> simp`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ _) h`. Establish `hne : (i, j) ≠ (j, i)` using `fun h => hij (Prod.mk.inj h).1`. Rewrite using `[Finset.sum_eq_add (i, j) (j, i) hne]`. Rewrite using `[hb_tr, hb_tr, hb_apply, hb_apply] dsimp only`. Rewrite using `[if_neg hij, if_neg (Ne.symm hij)]`.

Simplify using `only [hji, Complex.real_smul]`. Break down `lt_or_gt_of_ne hij with hlt | hlt` into its components or cases. Rewrite using `[if_pos hlt, if_pos hlt, if_neg (not_lt.mpr hlt.le), if_neg (not_lt.mpr hlt.le)]`. Simplify using `only [and_self, if_true, hij, Ne.symm hij, false_and, if_false, add_zero, zero_sub, mul_one, mul_neg]`. Use `key_pair (H i j) (Real.sqrt 2) hs` as an intermediate fact.

Use `this using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [hlt, not_lt.mpr hlt.le, if_true, if_false]`. Simplify using `only [and_self, if_true, hij, Ne.symm hij, false_and, and_false, if_false, add_zero, zero_add, sub_zero, zero_sub, mul_one, mul_neg]`. Use `key_pair2 (H i j) (Real.sqrt 2) hs` as an intermediate fact.

Use `this using 1` and compare the differences between its conclusion and the goal. Introduce `p _ hp`. Take `⟨a, b⟩` from `p`. Establish `h1 : ¬(a = i ∧ b = j)` using `fun h => hp.1 (by rw [h.1, h.2])`. Establish `h2 : ¬(b = i ∧ a = j)` using `fun h => hp.2 (by rw [h.1, h.2])`.

Rewrite using `[hb_apply]`. Simplify using `only`. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality. Establish `h3 : ¬(a = i ∧ a = j)` using `fun h => hij (h.1.symm.trans h.2)`.

Rewrite using `[if_pos rfl, if_neg h3, smul_zero]`. Apply the tactic sequence `rw [if_neg hab, if_neg h1, if_neg h2] split_ifs <;> simp`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem hb_expand (H : Mat n) (hH : H.IsHermitian) : ∑ p, ((H * hb p).trace.re : ℝ) • (hb p : Mat n) = H := by
  ext i j
  simp only [Matrix.sum_apply, Matrix.smul_apply]
  have hji : H j i = star (H i j) := (hH.apply j i).symm
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  by_cases hij : i = j
  · subst hij
    have him : (H i i).im = 0 := by
      have := congrArg Complex.im (hH.apply i i)
      simp only [Complex.star_def, Complex.conj_im] at this
      linarith
    rw [Finset.sum_eq_single (i, i)]
    · rw [hb_tr, hb_apply]
      simp only [if_true, and_self, Complex.real_smul, mul_one]
      apply Complex.ext <;> simp [him]
    · intro p _ hp
      obtain ⟨a, b⟩ := p
      have hne : ¬(a = i ∧ b = i) := fun h => hp (by rw [h.1, h.2])
      have hne' : ¬(b = i ∧ a = i) := fun h => hne ⟨h.2, h.1⟩
      rw [hb_apply]
      dsimp only
      by_cases hab : a = b
      · subst hab
        rw [if_pos rfl, if_neg hne, smul_zero]
      · rw [if_neg hab, if_neg hne, if_neg hne']
        split_ifs <;> simp
    · intro h; exact absurd (Finset.mem_univ _) h
  · have hne : (i, j) ≠ (j, i) := fun h => hij (Prod.mk.inj h).1
    rw [Finset.sum_eq_add (i, j) (j, i) hne]
    · rw [hb_tr, hb_tr, hb_apply, hb_apply]
      dsimp only
      rw [if_neg hij, if_neg (Ne.symm hij)]
      simp only [hji, Complex.real_smul]
      rcases lt_or_gt_of_ne hij with hlt | hlt
      · rw [if_pos hlt, if_pos hlt, if_neg (not_lt.mpr hlt.le), if_neg (not_lt.mpr hlt.le)]
        simp only [and_self, if_true, hij, Ne.symm hij, false_and, if_false, add_zero, zero_sub, mul_one, mul_neg]
        have := key_pair (H i j) (Real.sqrt 2) hs
        convert this using 1
        ring
      · simp only [hlt, not_lt.mpr hlt.le, if_true, if_false]
        simp only [and_self, if_true, hij, Ne.symm hij, false_and, and_false, if_false, add_zero, zero_add, sub_zero,
          zero_sub, mul_one, mul_neg]
        have := key_pair2 (H i j) (Real.sqrt 2) hs
        convert this using 1
    · intro p _ hp
      obtain ⟨a, b⟩ := p
      have h1 : ¬(a = i ∧ b = j) := fun h => hp.1 (by rw [h.1, h.2])
      have h2 : ¬(b = i ∧ a = j) := fun h => hp.2 (by rw [h.1, h.2])
      rw [hb_apply]
      dsimp only
      by_cases hab : a = b
      · subst hab
        have h3 : ¬(a = i ∧ a = j) := fun h => hij (h.1.symm.trans h.2)
        rw [if_pos rfl, if_neg h3, smul_zero]
      · rw [if_neg hab, if_neg h1, if_neg h2]
        split_ifs <;> simp
    · intro h; exact absurd (Finset.mem_univ _) h
    · intro h; exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Use `Matrix.mem_unitaryGroup_iff.mp k.2` as an intermediate fact. Rewrite `this` using `[Matrix.star_eq_conjTranspose]`. Then use the resulting hypothesis.
-/
theorem unit_mul_star (k : Matrix.unitaryGroup (Fin n) ℂ) : k.1 * (k.1)ᴴ = 1 := by
  have := Matrix.mem_unitaryGroup_iff.mp k.2
  rwa [Matrix.star_eq_conjTranspose] at this

/- English proof (translation)
Use `Matrix.mem_unitaryGroup_iff'.mp k.2` as an intermediate fact. Rewrite `this` using `[Matrix.star_eq_conjTranspose]`. Then use the resulting hypothesis.
-/
theorem unit_star_mul (k : Matrix.unitaryGroup (Fin n) ℂ) : (k.1)ᴴ * k.1 = 1 := by
  have := Matrix.mem_unitaryGroup_iff'.mp k.2
  rwa [Matrix.star_eq_conjTranspose] at this

/- English proof (translation)
Unfold `Matrix.IsHermitian`. Rewrite using `[Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hH.eq, Matrix.mul_assoc]`.
-/
theorem conj_herm (k : Mat n) (H : Mat n) (hH : H.IsHermitian) : (k * H * kᴴ).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hH.eq, Matrix.mul_assoc]

/- English proof (translation)
Establish `h1` using `hb_expand ((k.1)ᴴ * H * k.1) (by`. Use `conj_herm (k.1)ᴴ H hH` as an intermediate fact. Rewrite using `[Matrix.conjTranspose_conjTranspose] at this)` and apply the resulting hypothesis. Establish `h2 : ∀ p, ((k.1)ᴴ * H * k.1 * hb p).trace = (H * (k.1 * hb p * (k.1)ᴴ)).trace`. Introduce `p`.

Rewrite using `[show (k.1)ᴴ * H * k.1 * hb p = (k.1)ᴴ * (H * k.1 * hb p) by simp only [Matrix.mul_assoc], Matrix.trace_mul_comm, show H * k.1 * hb p * (k.1)ᴴ = H * (k.1 * hb p * (k.1)ᴴ) by simp only [Matrix.mul_assoc]]`. Simplify using `only [h2] at h1`. Establish `h3` using `congrArg (fun M => k.1 * M * (k.1)ᴴ) h1`. Simplify using `only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul] at h3`. Rewrite using `[h3, ← Matrix.mul_assoc, ← Matrix.mul_assoc, unit_mul_star, Matrix.one_mul, Matrix.mul_assoc, unit_mul_star, Matrix.mul_one]`.
-/
theorem expand_conj (k : Matrix.unitaryGroup (Fin n) ℂ) (H : Mat n) (hH : H.IsHermitian) :
    ∑ p, ((H * (k.1 * hb p * (k.1)ᴴ)).trace.re : ℝ) • (k.1 * hb p * (k.1)ᴴ) = H := by
  have h1 := hb_expand ((k.1)ᴴ * H * k.1) (by
    have := conj_herm (k.1)ᴴ H hH
    rwa [Matrix.conjTranspose_conjTranspose] at this)
  have h2 : ∀ p, ((k.1)ᴴ * H * k.1 * hb p).trace = (H * (k.1 * hb p * (k.1)ᴴ)).trace := by
    intro p
    rw [show (k.1)ᴴ * H * k.1 * hb p = (k.1)ᴴ * (H * k.1 * hb p) by simp only [Matrix.mul_assoc],
      Matrix.trace_mul_comm, show H * k.1 * hb p * (k.1)ᴴ = H * (k.1 * hb p * (k.1)ᴴ) by simp only [Matrix.mul_assoc]]
  simp only [h2] at h1
  have h3 := congrArg (fun M => k.1 * M * (k.1)ᴴ) h1
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul] at h3
  rw [h3, ← Matrix.mul_assoc, ← Matrix.mul_assoc, unit_mul_star, Matrix.one_mul, Matrix.mul_assoc, unit_mul_star,
    Matrix.mul_one]

/- English proof (translation)
Use `set Y : Fin n × Fin n → Mat n := fun p => k.1 * hb p * (k.1)ᴴ with hYdef`. Establish `hY : ∀ p, (Y p).IsHermitian` using `fun p => conj_herm k.1 (hb p) (hb_herm p)`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Rewrite using `[hb_expand _ (hY p)]`.

Use `_ = ∑ p, ∑ q, ((Y p * hb q).trace.re : ℝ) • B (Y p) (hb q) := by`. Simplify using `only [map_sum, map_smul]`. Use `_ = ∑ q, ∑ p, ((hb q * Y p).trace.re : ℝ) • B (Y p) (hb q) := by`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations.

Rewrite using `[Matrix.trace_mul_comm]`. Use `_ = ∑ q, B (∑ p, ((hb q * Y p).trace.re : ℝ) • Y p) (hb q) := by`. Simplify using `only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]`. Use `_ = ∑ q, B (hb q) (hb q) := by`. Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations.

Rewrite using `[expand_conj k (hb q) (hb_herm q)]`.
-/
theorem basis_inv {W : Type} [AddCommGroup W] [Module ℝ W] (B : Mat n →ₗ[ℝ] Mat n →ₗ[ℝ] W)
    (k : Matrix.unitaryGroup (Fin n) ℂ) :
    ∑ p, B (k.1 * hb p * (k.1)ᴴ) (k.1 * hb p * (k.1)ᴴ) = ∑ p, B (hb p) (hb p) := by
  set Y : Fin n × Fin n → Mat n := fun p => k.1 * hb p * (k.1)ᴴ with hYdef
  have hY : ∀ p, (Y p).IsHermitian := fun p => conj_herm k.1 (hb p) (hb_herm p)
  calc ∑ p, B (Y p) (Y p) = ∑ p, B (Y p) (∑ q, ((Y p * hb q).trace.re : ℝ) • (hb q : Mat n)) := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [hb_expand _ (hY p)]
    _ = ∑ p, ∑ q, ((Y p * hb q).trace.re : ℝ) • B (Y p) (hb q) := by
        simp only [map_sum, map_smul]
    _ = ∑ q, ∑ p, ((hb q * Y p).trace.re : ℝ) • B (Y p) (hb q) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun p _ => ?_
        rw [Matrix.trace_mul_comm]
    _ = ∑ q, B (∑ p, ((hb q * Y p).trace.re : ℝ) • Y p) (hb q) := by
        simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
    _ = ∑ q, B (hb q) (hb q) := by
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [expand_conj k (hb q) (hb_herm q)]

end PositivityTheory.RgBcC.LfSt.ChainPf.Cdc
