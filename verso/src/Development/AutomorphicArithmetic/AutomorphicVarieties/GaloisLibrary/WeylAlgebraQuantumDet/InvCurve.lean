import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.IsTop

open Matrix UpperTheory.V.Weyl

/- English proof (translation)
Introduce `n a b`. Distinguish the cases in `hab : a = b`. Substitute `hab set E : Matrix (Fin n) (Fin n) ℂ := Matrix.single a a 1 with hEdef` using the available equality. Establish `hE : E * E = E`. Rewrite using `[hEdef, Matrix.single_mul_single_same, one_mul]`.

Use `⟨fun t => 1 + (Complex.exp t - 1) • E, fun t => 1 + (Complex.exp (-t) - 1) • E, by simp, by simp, ?_, ?_⟩` and prove the remaining obligations. Introduce `t`. Establish `key : (Complex.exp (-t) - 1) + ((Complex.exp t - 1) + (Complex.exp (-t) - 1) * (Complex.exp t - 1)) = 0`. Establish `h1 : Complex.exp (-t) * Complex.exp t = 1`. Rewrite using `[← Complex.exp_add]`.

Simplify using the standard rewrite rules. Take the linear combination `h1`. Simplify using `only [add_mul, mul_add, one_mul, mul_one, smul_mul_smul_comm, hE]`. Rewrite using `[add_assoc, ← add_smul, ← add_smul, key, zero_smul, add_zero]`. Introduce `i j`.

Prove the components needed by the constructor for the conclusion. Establish `h` using `(((Complex.hasDerivAt_exp 0).sub_const 1).mul_const (E i j)).const_add ((1 : Matrix (Fin n) (Fin n) ℂ) i j)`. Simplify `h` using `[Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]`. Establish `h0 : HasDerivAt (fun t : ℂ => Complex.exp (-t)) (-1) 0`. Simplify using `using (hasDerivAt_neg (0 : ℂ)).cexp`.

Establish `h` using `((h0.sub_const 1).mul_const (E i j)).const_add ((1 : Matrix (Fin n) (Fin n) ℂ) i j)`. Simplify `h` using `[Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]`. Use `set E : Matrix (Fin n) (Fin n) ℂ := Matrix.single a b 1 with hEdef`. Establish `hE : E * E = 0`. Rewrite using `[hEdef]`.

Simplify using `[Ne.symm hab]`. Use `⟨fun t => 1 + t • E, fun t => 1 - t • E, by simp, by simp, ?_, ?_⟩` and prove the remaining obligations. Introduce `t`. Simplify using `only [sub_mul, mul_add, one_mul, mul_one, smul_mul_smul_comm, hE, smul_zero]`. Normalize the expressions using the abelian group laws.

Introduce `i j`. Prove the components needed by the constructor for the conclusion. Establish `h` using `((hasDerivAt_id (0 : ℂ)).mul_const (E i j)).const_add ((1 : Matrix (Fin n) (Fin n) ℂ) i j)`. Simplify `h` using `[Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]`. Establish `h` using `((hasDerivAt_id (0 : ℂ)).mul_const (E i j)).const_sub ((1 : Matrix (Fin n) (Fin n) ℂ) i j)`.

Simplify `h` using `[Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]`.
-/
theorem UpperTheory.V.Weyl.invCurve :
    ∀ (n : ℕ) (a b : Fin n), ∃ P Q : ℂ → Matrix (Fin n) (Fin n) ℂ, P 0 = 1 ∧ Q 0 = 1 ∧ (∀ t, Q t * P t = 1) ∧
      ∀ i j, HasDerivAt (fun t => P t i j) (Matrix.single a b (1 : ℂ) i j) 0 ∧ HasDerivAt (fun t => Q t i j) (-Matrix.single a b (1 : ℂ) i j) 0 := by
  intro n a b
  by_cases hab : a = b
  · subst hab
    set E : Matrix (Fin n) (Fin n) ℂ := Matrix.single a a 1 with hEdef
    have hE : E * E = E := by
      rw [hEdef, Matrix.single_mul_single_same, one_mul]
    refine ⟨fun t => 1 + (Complex.exp t - 1) • E, fun t => 1 + (Complex.exp (-t) - 1) • E,
      by simp, by simp, ?_, ?_⟩
    · intro t
      have key : (Complex.exp (-t) - 1) + ((Complex.exp t - 1)
          + (Complex.exp (-t) - 1) * (Complex.exp t - 1)) = 0 := by
        have h1 : Complex.exp (-t) * Complex.exp t = 1 := by
          rw [← Complex.exp_add]; simp
        linear_combination h1
      simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_smul_comm, hE]
      rw [add_assoc, ← add_smul, ← add_smul, key, zero_smul, add_zero]
    · intro i j
      constructor
      · have h := (((Complex.hasDerivAt_exp 0).sub_const 1).mul_const (E i j)).const_add ((1 : Matrix (Fin n) (Fin n) ℂ) i j)
        simpa [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] using h
      · have h0 : HasDerivAt (fun t : ℂ => Complex.exp (-t)) (-1) 0 := by
          simpa using (hasDerivAt_neg (0 : ℂ)).cexp
        have h := ((h0.sub_const 1).mul_const (E i j)).const_add ((1 : Matrix (Fin n) (Fin n) ℂ) i j)
        simpa [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] using h
  · set E : Matrix (Fin n) (Fin n) ℂ := Matrix.single a b 1 with hEdef
    have hE : E * E = 0 := by
      rw [hEdef]
      simp [Ne.symm hab]
    refine ⟨fun t => 1 + t • E, fun t => 1 - t • E, by simp, by simp, ?_, ?_⟩
    · intro t
      simp only [sub_mul, mul_add, one_mul, mul_one, smul_mul_smul_comm, hE, smul_zero]
      abel
    · intro i j
      constructor
      · have h := ((hasDerivAt_id (0 : ℂ)).mul_const (E i j)).const_add ((1 : Matrix (Fin n) (Fin n) ℂ) i j)
        simpa [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] using h
      · have h := ((hasDerivAt_id (0 : ℂ)).mul_const (E i j)).const_sub ((1 : Matrix (Fin n) (Fin n) ℂ) i j)
        simpa [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] using h
