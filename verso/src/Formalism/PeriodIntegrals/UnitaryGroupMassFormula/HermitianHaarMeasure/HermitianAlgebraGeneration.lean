import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianHaarMeasure.GeneralSecondMinorExpansion

open Matrix Finset

noncomputable section

namespace PI.QnHermHaar

open Formalism.REAL Formalism.FourierDecayAlt.Q

/- English proof (translation)
Unfold `HermAlgFrom HermAlg`. Introduce `hSM hCC hMV hMC A _ _ _ _ m E Y Yb Hm x xb hGl hHm hHm2 hstarE hYY hYbYb hYYb hLY hLYb hYbH hxbH u p q`. Choose the witnesses or unpack the hypotheses as in `⟨P, Q, ε, hQP, hPQ, hPs, hQs, hHmP, hQHm⟩ : ∃ (P Q : Matrix (Fin m) (Fin m) ℂ) (ε : Fin m → ℤˣ), Q * P = 1 ∧ P * Q = 1 ∧ (∀ i j, star (P i j) = Q j i) ∧ (∀ i j, star (Q i j) = P j i) ∧ (∀ k b, ∑ j, Hm k j * P j b = P k b * ((ε b : ℤ) : ℂ)) ∧ (∀ a l, ∑ i, Q a i * Hm i l = ((ε a : …`. Establish `hH : Hm.IsHermitian` using `hHm`. Use `set P : Matrix (Fin m) (Fin m) ℂ := (hH.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ) with hPdef`.

Establish `hQP : star P * P = 1` using `by first`. Consider the case `exact Matrix.mem_unitaryGroup_iff'.mp hH.eigenvectorUnitary.2`. Consider the case `exact unitary.star_mul_self_of_mem hH.eigenvectorUnitary.2`. Consider the case `exact Unitary.star_mul_self_of_mem hH.eigenvectorUnitary.2`. Establish `hPQ : P * star P = 1` using `by first`.

Consider the case `exact Matrix.mem_unitaryGroup_iff.mp hH.eigenvectorUnitary.2`. Consider the case `exact unitary.mul_star_self_of_mem hH.eigenvectorUnitary.2`. Consider the case `exact Unitary.mul_star_self_of_mem hH.eigenvectorUnitary.2`. Use `set d : Fin m → ℂ := fun b => ((hH.eigenvalues b : ℝ) : ℂ) with hd`. Establish `hspec : Hm = P * Matrix.diagonal d * star P` using `by first`.

Consider the case `exact hH.spectral_theorem`. Consider the case `exact Matrix.IsHermitian.spectral_theorem hH`. Establish `hHP : Hm * P = P * Matrix.diagonal d`. Rewrite using `[hspec]`. Simplify using `only [Matrix.mul_assoc, hQP, Matrix.mul_one]`.

Establish `hQH : star P * Hm = Matrix.diagonal d * star P`. Rewrite using `[hspec]`. Simplify using `only [← Matrix.mul_assoc, hQP, Matrix.one_mul]`. Establish `hPHP : star P * Hm * P = Matrix.diagonal d`. Rewrite using `[hQH, Matrix.mul_assoc, hQP, Matrix.mul_one]`.

Establish `hD2 : Matrix.diagonal d * Matrix.diagonal d = 1`. Rewrite using `[← hPHP]`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc P (star P), hPQ, Matrix.one_mul, ← Matrix.mul_assoc Hm Hm, hHm2, Matrix.one_mul, hQP]`. Establish `hdd : ∀ b, hH.eigenvalues b * hH.eigenvalues b = 1` using `fun b => by`.

Establish `h1` using `congrFun (congrFun hD2 b) b`. Rewrite `h1` using `[Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq, Matrix.one_apply_eq]`. Establish `h2 : ((hH.eigenvalues b : ℝ) : ℂ) * ((hH.eigenvalues b : ℝ) : ℂ) = 1` using `h1`. Conclude with `h2` after adjusting the coercions. Establish `hεd : ∀ b, (((if hH.eigenvalues b = 1 then (1 : ℤˣ) else -1 : ℤˣ) : ℤ) : ℂ) = d b` using `fun b => by`.

Break down `mul_self_eq_one_iff.mp (hdd b) with h | h` into its components or cases. Simplify using `[hd, h]`. Establish `hne : hH.eigenvalues b ≠ 1` using `by rw [h]; norm_num`. Rewrite using `[if_neg hne]`. Simplify using `[hd, h]`.

Use `⟨P, star P, fun b => if hH.eigenvalues b = 1 then 1 else -1, hQP, hPQ, fun i j => by rw [Matrix.star_apply], fun i j => by rw [Matrix.star_apply, star_star], fun k b => ?_, fun a l => ?_⟩` and prove the remaining obligations. Establish `h1` using `congrFun (congrFun hHP k) b`. Rewrite `h1` using `[Matrix.mul_apply, Matrix.mul_diagonal]`. Rewrite using `[h1]`. Use `congr 1`.

Conclude with `(hεd b).symm`. Establish `h1` using `congrFun (congrFun hQH a) l`. Rewrite `h1` using `[Matrix.mul_apply, Matrix.diagonal_mul]`. Rewrite using `[h1]`. Use `congr 1`.

Conclude with `(hεd a).symm`. Establish `hGl'` using `glConj E P Q hGl hQP`. Establish `hE'` using `starConj E Hm P Q ε hstarE hPs hQs hHmP hQHm`. Establish `hYY'` using `commVec Y Q hYY`. Establish `hYbYb'` using `commCov Yb P hYbYb`.

Establish `hLY'` using `leibVec E Y P Q hQP hLY`. Establish `hLYb'` using `leibCov E Yb P Q hQP hLYb`. Establish `hYb' : ∀ c, covC P Yb c = ((ε c : ℤ) : ℂ) • star (vecC Q Y c)`. Introduce `c`. Simplify using `only [covC, vecC, hYbH, star_sum, star_smul, hQs, Finset.smul_sum, smul_smul]`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun l' _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_smul]`. Use `congr 1`. Combine the equalities or inequalities in the displayed calculation.

Establish `hxb' : ∀ c, (xb ᵥ* P) c = ((ε c : ℤ) : ℂ) * star ((Q *ᵥ x) c)`. Introduce `c`. Use `show ∑ l, xb l * P l c = ((ε c : ℤ) : ℂ) * star (∑ k, Q c k * x k)`. Simplify using `only [hxbH, star_sum, star_mul', hQs, Finset.sum_mul, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun l' _ => ?_` and prove the remaining obligations. Establish `e1 : ∑ l, Hm l' l * star (x l') * P l c = star (x l') * ∑ l, Hm l' l * P l c`. Rewrite using `[Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun _ _ => by ring`. Rewrite using `[e1, hHmP l' c]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[tATrans hCC E Y Yb x xb P Q hGl hQP hPQ u p q, tATrans hCC E Y Yb x xb P Q hGl hQP hPQ (star u) q p]`. Apply the tactic sequence `fin_cases p <;> fin_cases q`. Conclude with `star_transfer_diagonal_zero hSM _ _ _ _ _ ε hGl' hE' u`. Conclude with `star_transfer_zero_one hSM hMV _ _ _ _ _ ε hGl' hE' hYY' hLY' hYb' hxb' u`.

Establish `h` using `congrArg star (star_transfer_zero_one hSM hMV _ _ _ _ _ ε hGl' hE' hYY' hLY' hYb' hxb' (star u))`. Rewrite `h` using `[star_star, star_star]`. Conclude with `h.symm`. Conclude with `lower_right_ne_zero_of_upper_right_zero hSM hMV hMC _ _ _ _ _ ε hGl' hE' hYY' hYbYb' hLY' hLYb' hYb' hxb' u`.
-/
theorem hermitian_algebra_generation : HermAlgFrom := by
  unfold HermAlgFrom HermAlg
  intro hSM hCC hMV hMC A _ _ _ _ m E Y Yb Hm x xb hGl hHm hHm2 hstarE hYY hYbYb hYYb hLY hLYb hYbH hxbH u p q

  obtain ⟨P, Q, ε, hQP, hPQ, hPs, hQs, hHmP, hQHm⟩ : ∃ (P Q : Matrix (Fin m) (Fin m) ℂ) (ε : Fin m → ℤˣ),
      Q * P = 1 ∧ P * Q = 1 ∧ (∀ i j, star (P i j) = Q j i) ∧ (∀ i j, star (Q i j) = P j i) ∧
      (∀ k b, ∑ j, Hm k j * P j b = P k b * ((ε b : ℤ) : ℂ)) ∧
      (∀ a l, ∑ i, Q a i * Hm i l = ((ε a : ℤ) : ℂ) * Q a l) := by
    have hH : Hm.IsHermitian := hHm
    set P : Matrix (Fin m) (Fin m) ℂ := (hH.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ) with hPdef
    have hQP : star P * P = 1 := by
      first
        | exact Matrix.mem_unitaryGroup_iff'.mp hH.eigenvectorUnitary.2
        | exact unitary.star_mul_self_of_mem hH.eigenvectorUnitary.2
        | exact Unitary.star_mul_self_of_mem hH.eigenvectorUnitary.2
    have hPQ : P * star P = 1 := by
      first
        | exact Matrix.mem_unitaryGroup_iff.mp hH.eigenvectorUnitary.2
        | exact unitary.mul_star_self_of_mem hH.eigenvectorUnitary.2
        | exact Unitary.mul_star_self_of_mem hH.eigenvectorUnitary.2
    set d : Fin m → ℂ := fun b => ((hH.eigenvalues b : ℝ) : ℂ) with hd
    have hspec : Hm = P * Matrix.diagonal d * star P := by
      first
        | exact hH.spectral_theorem
        | exact Matrix.IsHermitian.spectral_theorem hH
    have hHP : Hm * P = P * Matrix.diagonal d := by
      rw [hspec]
      simp only [Matrix.mul_assoc, hQP, Matrix.mul_one]
    have hQH : star P * Hm = Matrix.diagonal d * star P := by
      rw [hspec]
      simp only [← Matrix.mul_assoc, hQP, Matrix.one_mul]
    have hPHP : star P * Hm * P = Matrix.diagonal d := by
      rw [hQH, Matrix.mul_assoc, hQP, Matrix.mul_one]
    have hD2 : Matrix.diagonal d * Matrix.diagonal d = 1 := by
      rw [← hPHP]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc P (star P), hPQ, Matrix.one_mul, ← Matrix.mul_assoc Hm Hm, hHm2, Matrix.one_mul, hQP]
    have hdd : ∀ b, hH.eigenvalues b * hH.eigenvalues b = 1 := fun b => by
      have h1 := congrFun (congrFun hD2 b) b
      rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at h1
      have h2 : ((hH.eigenvalues b : ℝ) : ℂ) * ((hH.eigenvalues b : ℝ) : ℂ) = 1 := h1
      exact_mod_cast h2
    have hεd : ∀ b, (((if hH.eigenvalues b = 1 then (1 : ℤˣ) else -1 : ℤˣ) : ℤ) : ℂ) = d b := fun b => by
      rcases mul_self_eq_one_iff.mp (hdd b) with h | h
      · simp [hd, h]
      · have hne : hH.eigenvalues b ≠ 1 := by rw [h]; norm_num
        rw [if_neg hne]
        simp [hd, h]
    refine ⟨P, star P, fun b => if hH.eigenvalues b = 1 then 1 else -1, hQP, hPQ,
      fun i j => by rw [Matrix.star_apply], fun i j => by rw [Matrix.star_apply, star_star], fun k b => ?_,
      fun a l => ?_⟩
    · have h1 := congrFun (congrFun hHP k) b
      rw [Matrix.mul_apply, Matrix.mul_diagonal] at h1
      rw [h1]
      congr 1
      exact (hεd b).symm
    · have h1 := congrFun (congrFun hQH a) l
      rw [Matrix.mul_apply, Matrix.diagonal_mul] at h1
      rw [h1]
      congr 1
      exact (hεd a).symm

  have hGl' := glConj E P Q hGl hQP
  have hE' := starConj E Hm P Q ε hstarE hPs hQs hHmP hQHm
  have hYY' := commVec Y Q hYY
  have hYbYb' := commCov Yb P hYbYb
  have hLY' := leibVec E Y P Q hQP hLY
  have hLYb' := leibCov E Yb P Q hQP hLYb
  have hYb' : ∀ c, covC P Yb c = ((ε c : ℤ) : ℂ) • star (vecC Q Y c) := by
    intro c
    simp only [covC, vecC, hYbH, star_sum, star_smul, hQs, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l' _ => ?_
    rw [← Finset.sum_smul]
    congr 1
    calc ∑ l, P l c * Hm l' l = ∑ l, Hm l' l * P l c := Finset.sum_congr rfl fun _ _ => mul_comm _ _
      _ = P l' c * ((ε c : ℤ) : ℂ) := hHmP l' c
      _ = ((ε c : ℤ) : ℂ) * P l' c := mul_comm _ _
  have hxb' : ∀ c, (xb ᵥ* P) c = ((ε c : ℤ) : ℂ) * star ((Q *ᵥ x) c) := by
    intro c
    show ∑ l, xb l * P l c = ((ε c : ℤ) : ℂ) * star (∑ k, Q c k * x k)
    simp only [hxbH, star_sum, star_mul', hQs, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l' _ => ?_
    have e1 : ∑ l, Hm l' l * star (x l') * P l c = star (x l') * ∑ l, Hm l' l * P l c := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [e1, hHmP l' c]
    ring
  rw [tATrans hCC E Y Yb x xb P Q hGl hQP hPQ u p q, tATrans hCC E Y Yb x xb P Q hGl hQP hPQ (star u) q p]
  fin_cases p <;> fin_cases q
  · exact star_transfer_diagonal_zero hSM _ _ _ _ _ ε hGl' hE' u
  · exact star_transfer_zero_one hSM hMV _ _ _ _ _ ε hGl' hE' hYY' hLY' hYb' hxb' u
  · have h := congrArg star (star_transfer_zero_one hSM hMV _ _ _ _ _ ε hGl' hE' hYY' hLY' hYb' hxb' (star u))
    rw [star_star, star_star] at h
    exact h.symm
  · exact lower_right_ne_zero_of_upper_right_zero hSM hMV hMC _ _ _ _ _ ε hGl' hE' hYY' hYbYb' hLY' hLYb' hYb' hxb' u

end PI.QnHermHaar
