import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BlochKatoSelmerVanishes

open Matrix UpperTheory.V

/- English proof (translation)
Establish `hd : Matrix.det !![a, b; c, d] ≠ 0` using `by rwa [Matrix.det_fin_two_of]`. Take `⟨P, hP⟩ : ∃ P : GL (Fin 2) k, (P : Matrix (Fin 2) (Fin 2) k) = !![a, b; c, d]` from `⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hd, rfl⟩`. Use `⟨P, fun t ht => ?_⟩` and prove the remaining obligations. Establish `hPW : !![a, b; c, d] * (W t : Matrix (Fin 2) (Fin 2) k) = Matrix.diagonal (fun i => ((![Ψ, Ψ⁻¹] i t : kˣ) : k)) * !![a, b; c, d]`. Take `⟨h1, h2, h3, h4⟩` from `h t ht`.

Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j`. Simplify using `[Matrix.mul_apply, Fin.sum_univ_two]`. Take the linear combination `h1`. Simplify using `[Matrix.mul_apply, Fin.sum_univ_two]`.

Take the linear combination `h2`. Simplify using `[Matrix.mul_apply, Fin.sum_univ_two]`. Take the linear combination `h3`. Simplify using `[Matrix.mul_apply, Fin.sum_univ_two]`. Take the linear combination `h4`.

Rewrite using `[Units.val_mul, Units.val_mul, hP, hPW, Matrix.mul_assoc, ← hP, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]`.
-/
private theorem diagonal_on_subgroup_from_equations {Γ k : Type} [Group Γ] [Field k] (H : Subgroup Γ) (W : Γ →* GL (Fin 2) k)
    (Ψ : Γ →* kˣ) (a b c d : k) (hdet : a * d - b * c ≠ 0)
    (h : ∀ g ∈ H, a * W g 0 0 + b * W g 1 0 = (Ψ g : k) * a ∧ a * W g 0 1 + b * W g 1 1 = (Ψ g : k) * b ∧
      c * W g 0 0 + d * W g 1 0 = (Ψ g : k)⁻¹ * c ∧ c * W g 0 1 + d * W g 1 1 = (Ψ g : k)⁻¹ * d) :
    Af.IsDiagOn W H ![Ψ, Ψ⁻¹] := by
  have hd : Matrix.det !![a, b; c, d] ≠ 0 := by rwa [Matrix.det_fin_two_of]
  obtain ⟨P, hP⟩ : ∃ P : GL (Fin 2) k, (P : Matrix (Fin 2) (Fin 2) k) = !![a, b; c, d] :=
    ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hd, rfl⟩
  refine ⟨P, fun t ht => ?_⟩
  have hPW : !![a, b; c, d] * (W t : Matrix (Fin 2) (Fin 2) k) =
      Matrix.diagonal (fun i => ((![Ψ, Ψ⁻¹] i t : kˣ) : k)) * !![a, b; c, d] := by
    obtain ⟨h1, h2, h3, h4⟩ := h t ht
    ext i j
    fin_cases i <;> fin_cases j
    · simp [Matrix.mul_apply, Fin.sum_univ_two]
      linear_combination h1
    · simp [Matrix.mul_apply, Fin.sum_univ_two]
      linear_combination h2
    · simp [Matrix.mul_apply, Fin.sum_univ_two]
      linear_combination h3
    · simp [Matrix.mul_apply, Fin.sum_univ_two]
      linear_combination h4
  rw [Units.val_mul, Units.val_mul, hP, hPW, Matrix.mul_assoc, ← hP, ← Units.val_mul, mul_inv_cancel,
    Units.val_one, Matrix.mul_one]

/- English proof (translation)
Introduce `Γ k _ _ H W Ψ M hM`. Establish `hMi : ((M⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) * (M : Matrix (Fin 3) (Fin 3) k) = 1`. Rewrite using `[← Units.val_mul, inv_mul_cancel, Units.val_one]`. Distinguish the cases in `htriv : ∀ g ∈ H, Ψ g = 1`. Use `⟨1, fun t ht => ?_⟩` and prove the remaining obligations.

Establish `e` using `hM t ht`. Establish `hD : Matrix.diagonal ![(Ψ t : k), 1, (((Ψ t)⁻¹ : kˣ) : k)] = 1`. Rewrite using `[htriv t ht]`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp`.

Rewrite `e` using `[hD, Matrix.one_mul]`. Establish `hB : !![W t 0 0, 0, W t 0 1; 0, 1, 0; W t 1 0, 0, W t 1 1] = (1 : Matrix (Fin 3) (Fin 3) k)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Matrix.mul_assoc, hMi, Matrix.one_mul]`. Use `_ = 1 := by rw [e, hMi]`.

Establish `b00` using `congrFun (congrFun hB 0) 0`. Establish `b02` using `congrFun (congrFun hB 0) 2`. Establish `b20` using `congrFun (congrFun hB 2) 0`. Establish `b22` using `congrFun (congrFun hB 2) 2`. Simplify using `at b00 b02 b20 b22`.

Rewrite using `[one_mul, inv_one, mul_one]`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [htriv t ht, b00, b02, b20, b22]`. Use `push_neg at htriv`. Take `⟨g0, hg0, hne⟩` from `htriv`.

Establish `e0` using `hM g0 hg0`. Establish `x01 : (M : Matrix (Fin 3) (Fin 3) k) 0 1 = (Ψ g0 : k) * (M : Matrix (Fin 3) (Fin 3) k) 0 1`. Use `congrFun (congrFun e0 0) 1` as an intermediate fact. Simplify `this` using `[Matrix.mul_apply, Fin.sum_univ_three]`. Establish `x21 : (M : Matrix (Fin 3) (Fin 3) k) 2 1 = (((Ψ g0)⁻¹ : kˣ) : k) * (M : Matrix (Fin 3) (Fin 3) k) 2 1`.

Use `congrFun (congrFun e0 2) 1` as an intermediate fact. Simplify `this` using `[Matrix.mul_apply, Fin.sum_univ_three]`. Establish `m01 : (M : Matrix (Fin 3) (Fin 3) k) 0 1 = 0`. Establish `: (M : Matrix (Fin 3) (Fin 3) k) 0 1 * (1 - (Ψ g0 : k)) = 0` using `by linear_combination x01`. Break down `mul_eq_zero.mp this with h | h` into its components or cases.

Conclude with `h`. Conclude with `absurd (Units.val_eq_one.mp (sub_eq_zero.mp h).symm) hne`. Establish `m21 : (M : Matrix (Fin 3) (Fin 3) k) 2 1 = 0`. Establish `: (M : Matrix (Fin 3) (Fin 3) k) 2 1 * (1 - (((Ψ g0)⁻¹ : kˣ) : k)) = 0`. Take the linear combination `x21`.

Break down `mul_eq_zero.mp this with h | h` into its components or cases. Conclude with `h`. Conclude with `absurd (inv_eq_one.mp (Units.val_eq_one.mp (sub_eq_zero.mp h).symm)) hne`. Establish `hdetM : (M : Matrix (Fin 3) (Fin 3) k).det ≠ 0`. Introduce `h0`.

Use `congrArg Matrix.det hMi` as an intermediate fact. Rewrite `this` using `[Matrix.det_mul, h0, mul_zero, Matrix.det_one]`. Conclude with `zero_ne_one this`. Establish `hdet : (M : Matrix (Fin 3) (Fin 3) k) 0 0 * (M : Matrix (Fin 3) (Fin 3) k) 2 2 - (M : Matrix (Fin 3) (Fin 3) k) 0 2 * (M : Matrix (Fin 3) (Fin 3) k) 2 0 ≠ 0`. Introduce `h0`.

Apply `hdetM` to reduce the goal to its premises. Rewrite using `[Matrix.det_fin_three, m01, m21]`. Take the linear combination `(M : Matrix (Fin 3) (Fin 3) k) 1 1 * h0`. Use `diagonal_on_subgroup_from_equations H W Ψ _ _ _ _ hdet fun g hg => ⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `congrFun (congrFun (hM g hg) 0) 0` as an intermediate fact.

Simplify `this` using `[Matrix.mul_apply, Fin.sum_univ_three]`. Use `congrFun (congrFun (hM g hg) 0) 2` as an intermediate fact. Simplify `this` using `[Matrix.mul_apply, Fin.sum_univ_three]`. Use `congrFun (congrFun (hM g hg) 2) 0` as an intermediate fact. Simplify `this` using `[Matrix.mul_apply, Fin.sum_univ_three]`.

Use `congrFun (congrFun (hM g hg) 2) 2` as an intermediate fact. Simplify `this` using `[Matrix.mul_apply, Fin.sum_univ_three]`.
-/
theorem UpperTheory.diagonal_on_subgroup_of_conjugate :
    ∀ {Γ k : Type} [Group Γ] [Field k] (H : Subgroup Γ) (W : Γ →* GL (Fin 2) k) (Ψ : Γ →* kˣ) (M : GL (Fin 3) k), (∀ g ∈ H, (M : Matrix (Fin 3) (Fin 3) k) * !![W g 0 0, 0, W g 0 1; 0, 1, 0; W g 1 0, 0, W g 1 1] = Matrix.diagonal ![(Ψ g : k), 1, (((Ψ g)⁻¹ : kˣ) : k)] * (M : Matrix (Fin 3) (Fin 3) k)) → Af.IsDiagOn W H ![Ψ, Ψ⁻¹] := by
  intro Γ k _ _ H W Ψ M hM
  have hMi : ((M⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) * (M : Matrix (Fin 3) (Fin 3) k) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  by_cases htriv : ∀ g ∈ H, Ψ g = 1
  · refine ⟨1, fun t ht => ?_⟩
    have e := hM t ht
    have hD : Matrix.diagonal ![(Ψ t : k), 1, (((Ψ t)⁻¹ : kˣ) : k)] = 1 := by
      rw [htriv t ht]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    rw [hD, Matrix.one_mul] at e
    have hB : !![W t 0 0, 0, W t 0 1; 0, 1, 0; W t 1 0, 0, W t 1 1] = (1 : Matrix (Fin 3) (Fin 3) k) := by
      calc _ = ((M⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) *
            ((M : Matrix (Fin 3) (Fin 3) k) * !![W t 0 0, 0, W t 0 1; 0, 1, 0; W t 1 0, 0, W t 1 1]) := by
            rw [← Matrix.mul_assoc, hMi, Matrix.one_mul]
        _ = 1 := by rw [e, hMi]
    have b00 := congrFun (congrFun hB 0) 0
    have b02 := congrFun (congrFun hB 0) 2
    have b20 := congrFun (congrFun hB 2) 0
    have b22 := congrFun (congrFun hB 2) 2
    simp at b00 b02 b20 b22
    rw [one_mul, inv_one, mul_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [htriv t ht, b00, b02, b20, b22]
  · push_neg at htriv
    obtain ⟨g0, hg0, hne⟩ := htriv
    have e0 := hM g0 hg0
    have x01 : (M : Matrix (Fin 3) (Fin 3) k) 0 1 = (Ψ g0 : k) * (M : Matrix (Fin 3) (Fin 3) k) 0 1 := by
      have := congrFun (congrFun e0 0) 1
      simpa [Matrix.mul_apply, Fin.sum_univ_three] using this
    have x21 : (M : Matrix (Fin 3) (Fin 3) k) 2 1 =
        (((Ψ g0)⁻¹ : kˣ) : k) * (M : Matrix (Fin 3) (Fin 3) k) 2 1 := by
      have := congrFun (congrFun e0 2) 1
      simpa [Matrix.mul_apply, Fin.sum_univ_three] using this
    have m01 : (M : Matrix (Fin 3) (Fin 3) k) 0 1 = 0 := by
      have : (M : Matrix (Fin 3) (Fin 3) k) 0 1 * (1 - (Ψ g0 : k)) = 0 := by linear_combination x01
      rcases mul_eq_zero.mp this with h | h
      · exact h
      · exact absurd (Units.val_eq_one.mp (sub_eq_zero.mp h).symm) hne
    have m21 : (M : Matrix (Fin 3) (Fin 3) k) 2 1 = 0 := by
      have : (M : Matrix (Fin 3) (Fin 3) k) 2 1 * (1 - (((Ψ g0)⁻¹ : kˣ) : k)) = 0 := by
        linear_combination x21
      rcases mul_eq_zero.mp this with h | h
      · exact h
      · exact absurd (inv_eq_one.mp (Units.val_eq_one.mp (sub_eq_zero.mp h).symm)) hne
    have hdetM : (M : Matrix (Fin 3) (Fin 3) k).det ≠ 0 := by
      intro h0
      have := congrArg Matrix.det hMi
      rw [Matrix.det_mul, h0, mul_zero, Matrix.det_one] at this
      exact zero_ne_one this
    have hdet : (M : Matrix (Fin 3) (Fin 3) k) 0 0 * (M : Matrix (Fin 3) (Fin 3) k) 2 2 -
        (M : Matrix (Fin 3) (Fin 3) k) 0 2 * (M : Matrix (Fin 3) (Fin 3) k) 2 0 ≠ 0 := by
      intro h0
      apply hdetM
      rw [Matrix.det_fin_three, m01, m21]
      linear_combination (M : Matrix (Fin 3) (Fin 3) k) 1 1 * h0
    refine diagonal_on_subgroup_from_equations H W Ψ _ _ _ _ hdet fun g hg => ⟨?_, ?_, ?_, ?_⟩
    · have := congrFun (congrFun (hM g hg) 0) 0
      simpa [Matrix.mul_apply, Fin.sum_univ_three] using this
    · have := congrFun (congrFun (hM g hg) 0) 2
      simpa [Matrix.mul_apply, Fin.sum_univ_three] using this
    · have := congrFun (congrFun (hM g hg) 2) 0
      simpa [Matrix.mul_apply, Fin.sum_univ_three] using this
    · have := congrFun (congrFun (hM g hg) 2) 2
      simpa [Matrix.mul_apply, Fin.sum_univ_three] using this
