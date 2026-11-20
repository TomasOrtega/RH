import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.FourierZeroN

noncomputable section

open scoped Matrix ComplexOrder
open Matrix Formalism.IndefR.Datum

namespace PositivityTheory.Rg.Sw.Glob

/- English proof (translation)
Use `⟨(hT.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℂ), hT.eigenvalues, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← star_eq_conjTranspose]`. Conclude with `Unitary.coe_star_mul_self _`. Rewrite using `[← star_eq_conjTranspose]`. Conclude with `Unitary.coe_mul_star_self _`.

Use `hT.conjStarAlgAut_star_eigenvectorUnitary` as an intermediate fact. Rewrite `this` using `[Unitary.conjStarAlgAut_apply]`. Simplify `this` using `[star_eq_conjTranspose, Function.comp_def]`.
-/
theorem exists_unitary_diag {k : ℕ} {T : Matrix (Fin k) (Fin k) ℂ} (hT : T.IsHermitian) :
    ∃ (W : Matrix (Fin k) (Fin k) ℂ) (lam : Fin k → ℝ), Wᴴ * W = 1 ∧ W * Wᴴ = 1 ∧
      Wᴴ * T * W = diagonal (fun i => (lam i : ℂ)) := by
  refine ⟨(hT.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℂ), hT.eigenvalues, ?_, ?_, ?_⟩
  · rw [← star_eq_conjTranspose]; exact Unitary.coe_star_mul_self _
  · rw [← star_eq_conjTranspose]; exact Unitary.coe_mul_star_self _
  · have := hT.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_apply] at this
    simpa [star_eq_conjTranspose, Function.comp_def] using this

/- English proof (translation)
Establish `hpos` using `hM.eigenvalues_pos`. Establish `hUU : (hM.1.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℂ)ᴴ * (hM.1.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℂ) = 1`. Rewrite using `[← star_eq_conjTranspose]`. Conclude with `Unitary.coe_star_mul_self _`. Establish `hd : (hM.1.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℂ)ᴴ * M * (hM.1.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℂ) = diagonal (fun i => (hM.1.eigenvalues i : ℂ))`.

Use `hM.1.conjStarAlgAut_star_eigenvectorUnitary` as an intermediate fact. Rewrite `this` using `[Unitary.conjStarAlgAut_apply]`. Simplify `this` using `[star_eq_conjTranspose, Function.comp_def]`. Generalize the expression as in `(hM.1.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℂ) = U at hUU hd`. Generalize the expression as in `hM.1.eigenvalues = μ at hpos hd`.

Use `⟨U * diagonal (fun i => ((Real.sqrt (μ i))⁻¹ : ℂ)), ?_⟩` and prove the remaining obligations. Establish `hCd : (diagonal (fun i => ((Real.sqrt (μ i))⁻¹ : ℂ)))ᴴ = diagonal (fun i => ((Real.sqrt (μ i))⁻¹ : ℂ))`. Rewrite using `[diagonal_conjTranspose]`. Use `congr 1`. Use function extensionality and compare the values at `i`.

Simplify using `[Complex.conj_ofReal]`. Rewrite using `[conjTranspose_mul, hCd]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = 1 := by`.

Rewrite using `[hd, diagonal_mul_diagonal, diagonal_mul_diagonal, ← diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Establish `hp` using `hpos i`. Establish `hs : (Real.sqrt (μ i)) ^ 2 = μ i` using `Real.sq_sqrt hp.le`.

Establish `hs0 : Real.sqrt (μ i) ≠ 0` using `(Real.sqrt_pos.mpr hp).ne'`. Establish `hc : ((Real.sqrt (μ i) : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast hs0`. Clear the denominators using the available nonvanishing facts. Rewrite using `[← Complex.ofReal_pow, hs]`.
-/
theorem exists_normal {k : ℕ} {M : Matrix (Fin k) (Fin k) ℂ} (hM : M.PosDef) : ∃ C : Matrix (Fin k) (Fin k) ℂ,
    Cᴴ * M * C = 1 := by
  have hpos := hM.eigenvalues_pos
  have hUU : (hM.1.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℂ)ᴴ * (hM.1.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℂ) = 1 := by
    rw [← star_eq_conjTranspose]; exact Unitary.coe_star_mul_self _
  have hd : (hM.1.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℂ)ᴴ * M * (hM.1.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℂ) =
      diagonal (fun i => (hM.1.eigenvalues i : ℂ)) := by
    have := hM.1.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_apply] at this
    simpa [star_eq_conjTranspose, Function.comp_def] using this
  generalize (hM.1.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℂ) = U at hUU hd
  generalize hM.1.eigenvalues = μ at hpos hd
  refine ⟨U * diagonal (fun i => ((Real.sqrt (μ i))⁻¹ : ℂ)), ?_⟩
  have hCd : (diagonal (fun i => ((Real.sqrt (μ i))⁻¹ : ℂ)))ᴴ = diagonal (fun i => ((Real.sqrt (μ i))⁻¹ : ℂ)) := by
    rw [diagonal_conjTranspose]; congr 1; funext i; simp [Complex.conj_ofReal]
  rw [conjTranspose_mul, hCd]
  calc diagonal (fun i => ((Real.sqrt (μ i))⁻¹ : ℂ)) * Uᴴ * M * (U * diagonal (fun i => ((Real.sqrt (μ i))⁻¹ : ℂ)))
      = diagonal (fun i => ((Real.sqrt (μ i))⁻¹ : ℂ)) * (Uᴴ * M * U) * diagonal (fun i => ((Real.sqrt (μ i))⁻¹ : ℂ)) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by
        rw [hd, diagonal_mul_diagonal, diagonal_mul_diagonal, ← diagonal_one]
        congr 1; funext i
        have hp := hpos i
        have hs : (Real.sqrt (μ i)) ^ 2 = μ i := Real.sq_sqrt hp.le
        have hs0 : Real.sqrt (μ i) ≠ 0 := (Real.sqrt_pos.mpr hp).ne'
        have hc : ((Real.sqrt (μ i) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs0
        field_simp
        rw [← Complex.ofReal_pow, hs]

/- English proof (translation)
Take `⟨hSS, hSG, hM⟩` from `h`. Establish `hMh : (G * S)ᴴ = G * S` using `hM.1`. Establish `hGh : Gᴴ = G`. Establish `h1 : Sᴴ * Sᴴ = 1` using `by rw [← conjTranspose_mul, hSS, conjTranspose_one]`. Establish `h2 : Sᴴ * Gᴴ = G * S` using `by rw [← conjTranspose_mul]; exact hMh`.

Combine the equalities or inequalities in the displayed calculation. Take `⟨C, hCMC⟩` from `exists_normal hM`. Establish `hCCM : C * (Cᴴ * (G * S)) = 1` using `(Matrix.mul_eq_one_comm_of_equiv (Equiv.refl (Fin k))).mp hCMC`. Establish `hTh : (Cᴴ * G * C).IsHermitian` using `by show (Cᴴ * G * C)ᴴ = Cᴴ * G * C`. Rewrite using `[conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hGh, Matrix.mul_assoc]`.

Establish `hTT : (Cᴴ * G * C) * (Cᴴ * G * C) = 1`. Establish `e1 : C * Cᴴ * G = S`. Establish `: G = G * S * S` using `by rw [Matrix.mul_assoc, hSS, Matrix.mul_one]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`.

Use `_ = S := by rw [hCCM, Matrix.one_mul]`. Combine the equalities or inequalities in the displayed calculation. Take `⟨W, lam, hWW, hWW', hTd⟩` from `exists_unitary_diag hTh`. Establish `hsq : ∀ i, lam i = 1 ∨ lam i = -1`. Establish `hD : diagonal (fun i => (lam i : ℂ)) * diagonal (fun i => (lam i : ℂ)) = 1`.

Rewrite using `[← hTd]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hWW', Matrix.mul_one, Matrix.mul_assoc Wᴴ (Cᴴ * G * C) (Cᴴ * G * C), hTT, Matrix.mul_one, hWW]`. Introduce `i`. Use `congrFun (congrFun hD i) i` as an intermediate fact.

Rewrite `this` using `[diagonal_mul_diagonal, diagonal_apply_eq, one_apply_eq]`. Establish `h2 : (lam i) * (lam i) = 1` using `by exact_mod_cast this`. Establish `h3 : (lam i - 1) * (lam i + 1) = 0` using `by ring_nf; linarith`. Break down `mul_eq_zero.mp h3 with h | h` into its components or cases. Use `left`.

Combine the linear equalities and inequalities to obtain the conclusion. Use `right`. Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨fun i => decide (lam i = 1), C * W, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `hinv : ((C * W)ᴴ * (G * S)) * (C * W) = 1`.

Rewrite using `[conjTranspose_mul]`. Combine the equalities or inequalities in the displayed calculation. Conclude with `isUnit_det_of_left_inverse hinv`. Rewrite using `[conjTranspose_mul]`. Combine the equalities or inequalities in the displayed calculation.

Use `congr 1`. Use function extensionality and compare the values at `i`. Simplify using `only [sgn]`. Break down `hsq i with h | h` into its components or cases. Simplify using `[h]`.

Apply the tactic sequence `simp [h] <;> norm_num`. Rewrite using `[conjTranspose_mul]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem frame_of_cartan {k : ℕ} (G S : Matrix (Fin k) (Fin k) ℂ) (h : IsCartanInv G S) :
    ∃ (ε : Fin k → Bool) (fr : Matrix (Fin k) (Fin k) ℂ), IsUnit fr.det ∧ frᴴ * G * fr = diagonal (sgn ε) ∧
      frᴴ * (G * S) * fr = 1 := by
  obtain ⟨hSS, hSG, hM⟩ := h
  have hMh : (G * S)ᴴ = G * S := hM.1
  have hGh : Gᴴ = G := by
    have h1 : Sᴴ * Sᴴ = 1 := by rw [← conjTranspose_mul, hSS, conjTranspose_one]
    have h2 : Sᴴ * Gᴴ = G * S := by rw [← conjTranspose_mul]; exact hMh
    calc Gᴴ = Sᴴ * Sᴴ * Gᴴ := by rw [h1, Matrix.one_mul]
      _ = Sᴴ * (Sᴴ * Gᴴ) := by rw [Matrix.mul_assoc]
      _ = Sᴴ * (G * S) := by rw [h2]
      _ = Sᴴ * G * S := by rw [Matrix.mul_assoc]
      _ = G := hSG
  obtain ⟨C, hCMC⟩ := exists_normal hM
  have hCCM : C * (Cᴴ * (G * S)) = 1 :=
    (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl (Fin k))).mp hCMC
  have hTh : (Cᴴ * G * C).IsHermitian := by
    show (Cᴴ * G * C)ᴴ = Cᴴ * G * C
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hGh, Matrix.mul_assoc]
  have hTT : (Cᴴ * G * C) * (Cᴴ * G * C) = 1 := by
    have e1 : C * Cᴴ * G = S := by
      have : G = G * S * S := by rw [Matrix.mul_assoc, hSS, Matrix.mul_one]
      calc C * Cᴴ * G = C * (Cᴴ * (G * S)) * S := by
            conv_lhs => rw [this]
            simp only [Matrix.mul_assoc]
        _ = S := by rw [hCCM, Matrix.one_mul]
    calc (Cᴴ * G * C) * (Cᴴ * G * C) = Cᴴ * G * (C * Cᴴ * G) * C := by simp only [Matrix.mul_assoc]
      _ = Cᴴ * (G * S) * C := by rw [e1]; simp only [Matrix.mul_assoc]
      _ = 1 := hCMC
  obtain ⟨W, lam, hWW, hWW', hTd⟩ := exists_unitary_diag hTh
  have hsq : ∀ i, lam i = 1 ∨ lam i = -1 := by
    have hD : diagonal (fun i => (lam i : ℂ)) * diagonal (fun i => (lam i : ℂ)) = 1 := by
      rw [← hTd]
      calc Wᴴ * (Cᴴ * G * C) * W * (Wᴴ * (Cᴴ * G * C) * W)
          = Wᴴ * (Cᴴ * G * C) * (W * Wᴴ) * (Cᴴ * G * C) * W := by simp only [Matrix.mul_assoc]
        _ = 1 := by
          rw [hWW', Matrix.mul_one, Matrix.mul_assoc Wᴴ (Cᴴ * G * C) (Cᴴ * G * C), hTT, Matrix.mul_one, hWW]
    intro i
    have := congrFun (congrFun hD i) i
    rw [diagonal_mul_diagonal, diagonal_apply_eq, one_apply_eq] at this
    have h2 : (lam i) * (lam i) = 1 := by exact_mod_cast this
    have h3 : (lam i - 1) * (lam i + 1) = 0 := by ring_nf; linarith
    rcases mul_eq_zero.mp h3 with h | h
    · left; linarith
    · right; linarith
  refine ⟨fun i => decide (lam i = 1), C * W, ?_, ?_, ?_⟩
  · have hinv : ((C * W)ᴴ * (G * S)) * (C * W) = 1 := by
      rw [conjTranspose_mul]
      calc Wᴴ * Cᴴ * (G * S) * (C * W) = Wᴴ * (Cᴴ * (G * S) * C) * W := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hCMC, Matrix.mul_one, hWW]
    exact isUnit_det_of_left_inverse hinv
  · rw [conjTranspose_mul]
    calc Wᴴ * Cᴴ * G * (C * W) = Wᴴ * (Cᴴ * G * C) * W := by simp only [Matrix.mul_assoc]
      _ = diagonal (fun i => (lam i : ℂ)) := hTd
      _ = diagonal (sgn fun i => decide (lam i = 1)) := by
          congr 1; funext i
          simp only [sgn]
          rcases hsq i with h | h
          · simp [h]
          · simp [h] <;> norm_num
  · rw [conjTranspose_mul]
    calc Wᴴ * Cᴴ * (G * S) * (C * W) = Wᴴ * (Cᴴ * (G * S) * C) * W := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hCMC, Matrix.mul_one, hWW]

/- English proof (translation)
Introduce `D V τ s h`. Conclude with `frame_of_cartan _ _ h`.
-/
theorem sFrame : SFrame := by
  intro D V τ s h
  exact frame_of_cartan _ _ h

end PositivityTheory.Rg.Sw.Glob
