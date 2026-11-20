import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.StripInt

open scoped MatrixGroups

/- English proof (translation)
Introduce `x`. Use `set g := (x 0).gcd (x 1) with hg`. Break down `Nat.eq_zero_or_pos g with h0 | hpos` into its components or cases. Take `⟨h0', h1'⟩` from `Int.gcd_eq_zero_iff.mp h0`. Use `⟨0, 1, ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `i`. Apply the tactic sequence `fin_cases i <;> simp [h0', h1']`. Establish `hc : IsCoprime (x 0 / (g : ℤ)) (x 1 / (g : ℤ))` using `Int.isCoprime_iff_gcd_eq_one.mpr (Int.gcd_div_gcd_div_gcd hpos)`. Take `⟨γ, -, hγ⟩` from `ModularGroup.bottom_row_surj (R := ℤ) (show ![x 0 / (g : ℤ), x 1 / (g : ℤ)] ∈ {cd : Fin 2 → ℤ | IsCoprime (cd 0) (cd 1)} by simpa using hc)`. Use `⟨g, γ, ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `i`. Establish `hi` using `congrFun hγ i`. Simplify using `only [UpperTheory.V.Af.Rs.row, Pi.smul_apply, smul_eq_mul] at hi ⊢`. Rewrite using `[hi]`. Use `fin_cases i`.

Simplify using `only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]`. Conclude with `(Int.mul_ediv_cancel' (Int.gcd_dvd_left (x 0) (x 1))).symm`. Simplify using `only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]`. Conclude with `(Int.mul_ediv_cancel' (Int.gcd_dvd_right (x 0) (x 1))).symm`.
-/
theorem UpperTheory.V.Af.Rs.rowRep :
    UpperTheory.V.Af.Rs.RowRep := by
  intro x
  set g := (x 0).gcd (x 1) with hg
  rcases Nat.eq_zero_or_pos g with h0 | hpos
  · obtain ⟨h0', h1'⟩ := Int.gcd_eq_zero_iff.mp h0
    refine ⟨0, 1, ?_⟩
    funext i
    fin_cases i <;> simp [h0', h1']
  · have hc : IsCoprime (x 0 / (g : ℤ)) (x 1 / (g : ℤ)) :=
      Int.isCoprime_iff_gcd_eq_one.mpr (Int.gcd_div_gcd_div_gcd hpos)
    obtain ⟨γ, -, hγ⟩ := ModularGroup.bottom_row_surj (R := ℤ)
      (show ![x 0 / (g : ℤ), x 1 / (g : ℤ)] ∈ {cd : Fin 2 → ℤ | IsCoprime (cd 0) (cd 1)} by simpa using hc)
    refine ⟨g, γ, ?_⟩
    funext i
    have hi := congrFun hγ i
    simp only [UpperTheory.V.Af.Rs.row, Pi.smul_apply, smul_eq_mul] at hi ⊢
    rw [hi]
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      exact (Int.mul_ediv_cancel' (Int.gcd_dvd_left (x 0) (x 1))).symm
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      exact (Int.mul_ediv_cancel' (Int.gcd_dvd_right (x 0) (x 1))).symm
