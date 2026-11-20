import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameInduction.Counts
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameInduction.NegativeBound

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2

noncomputable section

namespace PI.FrameInd

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[Matrix.mul_apply, Matrix.submatrix_apply, Matrix.conjTranspose_apply]`.
-/
lemma submatrix_conj {ι κ : Type*} [Fintype ι] [Fintype κ] (W M : Matrix ι ι ℂ) (e : κ ≃ ι) :
    (W.submatrix id e)ᴴ * M * W.submatrix id e = (Wᴴ * M * W).submatrix e e := by
  ext i j
  simp [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.conjTranspose_apply]

/- English proof (translation)
Introduce `k r z z' γ hs hp hdet`. Use `set hA := isHerm k r z z' γ with hhA`. Use `set ev := hA.eigenvalues with hev`. Establish `h1 : Fintype.card {i // 0 < ev i} ≤ r + 1` using `hP k r z z' γ hs hp hdet`. Establish `h2 : Fintype.card {i // ¬ 0 < ev i} ≤ r + 1` using `hN k r z z' γ hs hp hdet`.

Establish `h3` using `Fintype.card_subtype_compl (fun i : Fin (r + 1) ⊕ Fin (r + 1) => 0 < ev i)`. Establish `h4 : Fintype.card {i : Fin (r + 1) ⊕ Fin (r + 1) // 0 < ev i} ≤ Fintype.card (Fin (r + 1) ⊕ Fin (r + 1))` using `Fintype.card_subtype_le _`. Simplify using `only [Fintype.card_sum, Fintype.card_fin] at h3 h4`. Establish `hcP : Fintype.card {i // 0 < ev i} = r + 1` using `by omega`. Establish `hcN : Fintype.card {i // ¬ 0 < ev i} = r + 1` using `by omega`.

Establish `hne : ∀ i, ev i ≠ 0`. Introduce `i h0`. Apply `hdet` to reduce the goal to its premises. Rewrite using `[hA.det_eq_prod_eigenvalues]`. Conclude with `Finset.prod_eq_zero (Finset.mem_univ i) (by rw [← hev, h0]; simp)`.

Set `eP : {i // 0 < ev i} ≃ Fin (r + 1)` to `Fintype.equivFinOfCardEq hcP`. Set `eN : {i // ¬ 0 < ev i} ≃ Fin (r + 1)` to `Fintype.equivFinOfCardEq hcN`. Set `e : Fin (r + 1) ⊕ Fin (r + 1) ≃ Fin (r + 1) ⊕ Fin (r + 1)` to `(Equiv.sumCongr eP.symm eN.symm).trans (Equiv.sumCompl fun i => 0 < ev i)`. Set `U : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) ℂ` to `hA.eigenvectorUnitary`. Set `s : Fin (r + 1) ⊕ Fin (r + 1) → ℂ` to `fun i => (((Real.sqrt |ev i|)⁻¹ : ℝ) : ℂ)`.

Set `f : Fin (r + 1) ⊕ Fin (r + 1) → ℂ` to `fun i => if 0 < ev i then 1 else -1`. Establish `hW : (U * diagonal s)ᴴ * gramM k r z z' γ * (U * diagonal s) = diagonal f`. Establish `hd : Uᴴ * gramM k r z z' γ * U = diagonal (fun i => ((ev i : ℝ) : ℂ))` using `CountsW.diag_eq hA`. Rewrite using `[conjTranspose_mul, diagonal_conjTranspose]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hd, diagonal_mul_diagonal, diagonal_mul_diagonal]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Establish `hpos : 0 < |ev i|` using `abs_pos.2 (hne i)`. Establish `hsq : Real.sqrt |ev i| * Real.sqrt |ev i| = |ev i|` using `Real.mul_self_sqrt hpos.le`.

Establish `hsq0 : Real.sqrt |ev i| ≠ 0` using `by positivity`. Simplify using `only [s, f, Pi.star_apply, Complex.star_def, Complex.conj_ofReal]`. Rewrite using `[← Complex.ofReal_mul, ← Complex.ofReal_mul]`. Establish `: (Real.sqrt |ev i|)⁻¹ * ev i * (Real.sqrt |ev i|)⁻¹ = if 0 < ev i then 1 else -1`. Rewrite using `[mul_comm, ← mul_assoc, ← mul_inv, hsq]`.

Use `split_ifs with h`. Rewrite using `[abs_of_pos h, inv_mul_cancel₀ (hne i)]`. Rewrite using `[abs_of_neg (lt_of_le_of_ne (not_lt.1 h) (hne i)), inv_neg, neg_mul, inv_mul_cancel₀ (hne i)]`. Apply the tactic sequence `rw [this]; split_ifs <;> simp`. Establish `hfe : f ∘ e = Sum.elim (fun _ => 1) (fun _ => -1)`.

Use function extensionality and compare the values at `i`. Break down `i with a | a` into its components or cases. Simplify using `[f, e, Equiv.sumCompl_apply_inl, (eP.symm a).2]`. Simplify using `[f, e, Equiv.sumCompl_apply_inr, (eN.symm a).2]`. Establish `hD : ((U * diagonal s).submatrix id e)ᴴ * gramM k r z z' γ * (U * diagonal s).submatrix id e = diagonal (Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1))`.

Rewrite using `[submatrix_conj, hW, submatrix_diagonal_equiv, hfe]`. Use `⟨(U * diagonal s).submatrix id e, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[isUnit_iff_ne_zero]`. Introduce `h0`. Use `congrArg Matrix.det hD` as an intermediate fact.

Rewrite `this` using `[det_mul, det_mul, h0, mul_zero, det_diagonal]`. Use `(Finset.prod_ne_zero_iff.2 fun i _ => ?_) this.symm` and prove the remaining obligations. Apply the tactic sequence `rcases i with a | a <;> simp`. Rewrite using `[hD]`. Use extensionality with `i j`.

Apply the tactic sequence `rcases i with a | a <;> rcases j with b | b <;> simp [diagonal_apply, one_apply] <;> split_ifs <;> simp`.
-/
theorem signStep_of (hP : PosCount) (hN : NonposCount) : SignStep := by
  intro k r z z' γ hs hp hdet
  set hA := isHerm k r z z' γ with hhA
  set ev := hA.eigenvalues with hev
  have h1 : Fintype.card {i // 0 < ev i} ≤ r + 1 := hP k r z z' γ hs hp hdet
  have h2 : Fintype.card {i // ¬ 0 < ev i} ≤ r + 1 := hN k r z z' γ hs hp hdet
  have h3 := Fintype.card_subtype_compl (fun i : Fin (r + 1) ⊕ Fin (r + 1) => 0 < ev i)
  have h4 : Fintype.card {i : Fin (r + 1) ⊕ Fin (r + 1) // 0 < ev i} ≤
      Fintype.card (Fin (r + 1) ⊕ Fin (r + 1)) := Fintype.card_subtype_le _
  simp only [Fintype.card_sum, Fintype.card_fin] at h3 h4
  have hcP : Fintype.card {i // 0 < ev i} = r + 1 := by omega
  have hcN : Fintype.card {i // ¬ 0 < ev i} = r + 1 := by omega
  have hne : ∀ i, ev i ≠ 0 := by
    intro i h0
    apply hdet
    rw [hA.det_eq_prod_eigenvalues]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [← hev, h0]; simp)
  let eP : {i // 0 < ev i} ≃ Fin (r + 1) := Fintype.equivFinOfCardEq hcP
  let eN : {i // ¬ 0 < ev i} ≃ Fin (r + 1) := Fintype.equivFinOfCardEq hcN
  let e : Fin (r + 1) ⊕ Fin (r + 1) ≃ Fin (r + 1) ⊕ Fin (r + 1) :=
    (Equiv.sumCongr eP.symm eN.symm).trans (Equiv.sumCompl fun i => 0 < ev i)
  let U : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) ℂ := hA.eigenvectorUnitary
  let s : Fin (r + 1) ⊕ Fin (r + 1) → ℂ := fun i => (((Real.sqrt |ev i|)⁻¹ : ℝ) : ℂ)
  let f : Fin (r + 1) ⊕ Fin (r + 1) → ℂ := fun i => if 0 < ev i then 1 else -1
  have hW : (U * diagonal s)ᴴ * gramM k r z z' γ * (U * diagonal s) = diagonal f := by
    have hd : Uᴴ * gramM k r z z' γ * U = diagonal (fun i => ((ev i : ℝ) : ℂ)) := CountsW.diag_eq hA
    rw [conjTranspose_mul, diagonal_conjTranspose]
    calc (star s |> diagonal) * Uᴴ * gramM k r z z' γ * (U * diagonal s)
        = diagonal (star s) * (Uᴴ * gramM k r z z' γ * U) * diagonal s := by simp only [Matrix.mul_assoc]
      _ = diagonal f := by
        rw [hd, diagonal_mul_diagonal, diagonal_mul_diagonal]
        congr 1
        funext i
        have hpos : 0 < |ev i| := abs_pos.2 (hne i)
        have hsq : Real.sqrt |ev i| * Real.sqrt |ev i| = |ev i| := Real.mul_self_sqrt hpos.le
        have hsq0 : Real.sqrt |ev i| ≠ 0 := by positivity
        simp only [s, f, Pi.star_apply, Complex.star_def, Complex.conj_ofReal]
        rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
        have : (Real.sqrt |ev i|)⁻¹ * ev i * (Real.sqrt |ev i|)⁻¹ = if 0 < ev i then 1 else -1 := by
          rw [mul_comm, ← mul_assoc, ← mul_inv, hsq]
          split_ifs with h
          · rw [abs_of_pos h, inv_mul_cancel₀ (hne i)]
          · rw [abs_of_neg (lt_of_le_of_ne (not_lt.1 h) (hne i)), inv_neg, neg_mul,
              inv_mul_cancel₀ (hne i)]
        rw [this]; split_ifs <;> simp
  have hfe : f ∘ e = Sum.elim (fun _ => 1) (fun _ => -1) := by
    funext i
    rcases i with a | a
    · simp [f, e, Equiv.sumCompl_apply_inl, (eP.symm a).2]
    · simp [f, e, Equiv.sumCompl_apply_inr, (eN.symm a).2]
  have hD : ((U * diagonal s).submatrix id e)ᴴ * gramM k r z z' γ * (U * diagonal s).submatrix id e =
      diagonal (Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1)) := by
    rw [submatrix_conj, hW, submatrix_diagonal_equiv, hfe]
  refine ⟨(U * diagonal s).submatrix id e, ?_, ?_⟩
  · rw [isUnit_iff_ne_zero]
    intro h0
    have := congrArg Matrix.det hD
    rw [det_mul, det_mul, h0, mul_zero, det_diagonal] at this
    refine (Finset.prod_ne_zero_iff.2 fun i _ => ?_) this.symm
    rcases i with a | a <;> simp
  · rw [hD]
    ext i j
    rcases i with a | a <;> rcases j with b | b <;> simp [diagonal_apply, one_apply] <;> split_ifs <;> simp

/- English proof (translation)
The claim follows from `signStep_of PI.FrameInd.CountsW.positive_count (PI.FrameInd.CountsW.nonposCount_of negative_bound)`.
-/
theorem signStep : SignStep :=
  signStep_of PI.FrameInd.CountsW.positive_count (PI.FrameInd.CountsW.nonposCount_of negative_bound)

end PI.FrameInd
