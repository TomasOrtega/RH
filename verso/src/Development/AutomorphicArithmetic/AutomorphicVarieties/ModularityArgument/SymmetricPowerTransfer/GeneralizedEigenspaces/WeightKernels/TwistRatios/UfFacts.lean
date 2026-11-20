import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.GoodSet

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
open UpperTheory.V.W (Plc Lp)
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
The claim follows from `(Matrix.isUnits_det_units g).ne_zero`.
-/
private theorem UpperTheory.V.Z.Sym.Ga.det_ne {k : Type} [Field k] (g : GL (Fin 2) k) :
    (g : Matrix (Fin 2) (Fin 2) k).det ≠ 0 :=
  (Matrix.isUnits_det_units g).ne_zero

/- English proof (translation)
Establish `h : ((g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) * (g : Matrix (Fin 2) (Fin 2) k) = 1`. Rewrite using `[← Units.val_mul, inv_mul_cancel, Units.val_one]`. Establish `h2` using `congrArg Matrix.det h`. Rewrite `h2` using `[Matrix.det_mul, Matrix.det_one]`. Conclude with `eq_inv_of_mul_eq_one_left h2`.
-/
private theorem UpperTheory.V.Z.Sym.Ga.det_inv {k : Type} [Field k] (g : GL (Fin 2) k) :
    ((g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k).det = ((g : Matrix (Fin 2) (Fin 2) k).det)⁻¹ := by
  have h : ((g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) * (g : Matrix (Fin 2) (Fin 2) k) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h2 := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_one] at h2
  exact eq_inv_of_mul_eq_one_left h2

/- English proof (translation)
Rewrite using `[Matrix.coe_units_inv, Matrix.inv_def, Matrix.adjugate_fin_two, Ring.inverse_eq_inv', Matrix.trace_smul, Matrix.trace_fin_two, Matrix.trace_fin_two]`. Simplify using `only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, smul_eq_mul]`. Rewrite using `[div_eq_inv_mul, add_comm]`.
-/
private theorem UpperTheory.V.Z.Sym.Ga.trace_inv {k : Type} [Field k] (g : GL (Fin 2) k) :
    ((g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k).trace =
      (g : Matrix (Fin 2) (Fin 2) k).trace / (g : Matrix (Fin 2) (Fin 2) k).det := by
  rw [Matrix.coe_units_inv, Matrix.inv_def, Matrix.adjugate_fin_two, Ring.inverse_eq_inv', Matrix.trace_smul,
    Matrix.trace_fin_two, Matrix.trace_fin_two]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    smul_eq_mul]
  rw [div_eq_inv_mul, add_comm]

/- English proof (translation)
Introduce `k _ g`. Establish `hd` using `Ga.det_ne g`. Use `⟨?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `a b h`. Establish `h'` using `h`.

Rewrite `h'` using `[Matrix.charpoly_fin_two]`. Establish `e0` using `congrArg (Polynomial.eval 0) h'`. Establish `e1` using `congrArg (Polynomial.eval 1) h'`. Simplify using `only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C] at e0 e1`. Establish `hdet : (g : Matrix (Fin 2) (Fin 2) k).det = a * b` using `by linear_combination e0`.

Establish `htr : (g : Matrix (Fin 2) (Fin 2) k).trace = a + b` using `by linear_combination e0 - e1`. Establish `ha : (a : k) ≠ 0` using `a.ne_zero`. Establish `hb : (b : k) ≠ 0` using `b.ne_zero`. Simplify using `only [Ga.uf, Ga.tr]`. Rewrite using `[htr, hdet, Units.val_inv_eq_inv_val, Units.val_div_eq_div_val]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [Ga.uf, Ga.tr]`. Rewrite using `[Ga.trace_inv, Ga.det_inv]`. Clear the denominators using the available nonvanishing facts.

Introduce `x`. Establish `hx : ((x⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) * (x : Matrix (Fin 2) (Fin 2) k) = 1`. Rewrite using `[← Units.val_mul, inv_mul_cancel, Units.val_one]`. Establish `ht : ((x * g * x⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k).trace = (g : Matrix (Fin 2) (Fin 2) k).trace`. Rewrite using `[Units.val_mul, Units.val_mul, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hx, Matrix.one_mul]`.

Establish `hdt : ((x * g * x⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k).det = (g : Matrix (Fin 2) (Fin 2) k).det`. Rewrite using `[Units.val_mul, Units.val_mul, Matrix.det_mul, mul_comm, Matrix.det_mul, ← mul_assoc, ← Matrix.det_mul, hx, Matrix.det_one, one_mul]`. Simplify using `only [Ga.uf, Ga.tr]`. Rewrite using `[ht, hdt]`. Introduce `g' P μ h`.

Establish `hμ : (μ : k) ≠ 0` using `μ.ne_zero`. Establish `hP` using `Ga.det_ne P`. Establish `hPi : (P : Matrix (Fin 2) (Fin 2) k) * ((P⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) = 1`. Rewrite using `[← Units.val_mul, mul_inv_cancel, Units.val_one]`. Establish `hPi' : ((P⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) * (P : Matrix (Fin 2) (Fin 2) k) = 1`.

Rewrite using `[← Units.val_mul, inv_mul_cancel, Units.val_one]`. Establish `hg : ((g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k)ᵀ * (g : Matrix (Fin 2) (Fin 2) k)ᵀ = 1`. Rewrite using `[← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.transpose_one]`. Establish `hform : (g' : Matrix (Fin 2) (Fin 2) k) = (μ : k) • (((P⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) * ((g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k)ᵀ * (P : Matrix (Fin 2) (Fin 2) k))`. Establish `e` using `congrArg (fun M => ((P⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) * ((g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k)ᵀ * M) h`.

Rewrite `e` using `[Matrix.mul_smul]`. Rewrite using `[← e]`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc (((g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k)ᵀ) ((g : Matrix (Fin 2) (Fin 2) k)ᵀ), hg, Matrix.one_mul, ← Matrix.mul_assoc, hPi', Matrix.one_mul]`. Establish `htr : (g' : Matrix (Fin 2) (Fin 2) k).trace = μ * ((g : Matrix (Fin 2) (Fin 2) k).trace / (g : Matrix (Fin 2) (Fin 2) k).det)`.

Rewrite using `[hform, Matrix.trace_smul, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hPi, Matrix.one_mul, Matrix.trace_transpose, Ga.trace_inv, smul_eq_mul]`. Establish `hdt : (g' : Matrix (Fin 2) (Fin 2) k).det = μ ^ 2 / (g : Matrix (Fin 2) (Fin 2) k).det`. Establish `e` using `congrArg Matrix.det h`. Rewrite `e` using `[Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_smul, Fintype.card_fin]`. Clear the denominators using the available nonvanishing facts.

Establish `: (P : Matrix (Fin 2) (Fin 2) k).det * ((g' : Matrix (Fin 2) (Fin 2) k).det * (g : Matrix (Fin 2) (Fin 2) k).det) = (P : Matrix (Fin 2) (Fin 2) k).det * (μ : k) ^ 2` using `by linear_combination e`. Conclude with `mul_left_cancel₀ hP this`. Simplify using `only [Ga.uf, Ga.tr]`. Rewrite using `[htr, hdt]`. Clear the denominators using the available nonvanishing facts.

Introduce `Γ _ ρ s`. Establish `hd'` using `Ga.det_ne (ρ s)`. Establish `e : (ad0 ρ s : Matrix (Fin 3) (Fin 3) k) = (((ρ s : Matrix (Fin 2) (Fin 2) k).det)⁻¹) • symSquareMatrixHom k (ρ s : Matrix (Fin 2) (Fin 2) k)`. Rewrite using `[ad0, tw_val]`. Simplify using `[Matrix.GeneralLinearGroup.det]`.

Simplify using `only [Ga.tr, Ga.uf]`. Rewrite using `[e, Matrix.trace_smul, Matrix.trace_fin_two, Matrix.trace_fin_three]`. Establish `hd2` using `hd'`. Rewrite `hd2`, the goal using `[Matrix.det_fin_two]`. Simplify using `[symSquareMatrixHom]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.V.Z.Sym.Ga.ufFacts :
    ∀ (k : Type) [Field k] (g : GL (Fin 2) k), (∀ a b : kˣ, (g : Matrix (Fin 2) (Fin 2) k).charpoly = (X - C (a : k)) * (X - C (b : k)) → Ga.uf g = (a / b : kˣ) + ((a / b : kˣ)⁻¹ : kˣ)) ∧ Ga.uf g⁻¹ = Ga.uf g ∧ (∀ x : GL (Fin 2) k, Ga.uf (x * g * x⁻¹) = Ga.uf g) ∧ (∀ (g' P : GL (Fin 2) k) (μ : kˣ), (g : Matrix (Fin 2) (Fin 2) k)ᵀ * (P : Matrix (Fin 2) (Fin 2) k) * (g' : Matrix (Fin 2) (Fin 2) k) = (μ : k) • (P : Matrix (Fin 2) (Fin 2) k) → Ga.uf g' = Ga.uf g) ∧ ∀ (Γ : Type) [Group Γ] (ρ : Γ →* GL (Fin 2) k) (s : Γ), Ga.tr (ad0 ρ s) = Ga.uf (ρ s) + 1 := by
  intro k _ g
  have hd := Ga.det_ne g
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a b h
    have h' := h
    rw [Matrix.charpoly_fin_two] at h'
    have e0 := congrArg (Polynomial.eval 0) h'
    have e1 := congrArg (Polynomial.eval 1) h'
    simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C] at e0 e1
    have hdet : (g : Matrix (Fin 2) (Fin 2) k).det = a * b := by linear_combination e0
    have htr : (g : Matrix (Fin 2) (Fin 2) k).trace = a + b := by linear_combination e0 - e1
    have ha : (a : k) ≠ 0 := a.ne_zero
    have hb : (b : k) ≠ 0 := b.ne_zero
    simp only [Ga.uf, Ga.tr]
    rw [htr, hdet, Units.val_inv_eq_inv_val, Units.val_div_eq_div_val]
    field_simp
    ring
  · simp only [Ga.uf, Ga.tr]
    rw [Ga.trace_inv, Ga.det_inv]
    field_simp
  · intro x
    have hx : ((x⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) * (x : Matrix (Fin 2) (Fin 2) k) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have ht : ((x * g * x⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k).trace = (g : Matrix (Fin 2) (Fin 2) k).trace := by
      rw [Units.val_mul, Units.val_mul, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hx, Matrix.one_mul]
    have hdt : ((x * g * x⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k).det = (g : Matrix (Fin 2) (Fin 2) k).det := by
      rw [Units.val_mul, Units.val_mul, Matrix.det_mul, mul_comm, Matrix.det_mul, ← mul_assoc, ← Matrix.det_mul, hx,
        Matrix.det_one, one_mul]
    simp only [Ga.uf, Ga.tr]
    rw [ht, hdt]
  · intro g' P μ h
    have hμ : (μ : k) ≠ 0 := μ.ne_zero
    have hP := Ga.det_ne P
    have hPi : (P : Matrix (Fin 2) (Fin 2) k) * ((P⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hPi' : ((P⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) * (P : Matrix (Fin 2) (Fin 2) k) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hg : ((g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k)ᵀ * (g : Matrix (Fin 2) (Fin 2) k)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.transpose_one]
    have hform : (g' : Matrix (Fin 2) (Fin 2) k) = (μ : k) • (((P⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) *
        ((g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k)ᵀ * (P : Matrix (Fin 2) (Fin 2) k)) := by
      have e := congrArg (fun M => ((P⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) *
        ((g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k)ᵀ * M) h
      rw [Matrix.mul_smul] at e
      rw [← e]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (((g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k)ᵀ) ((g : Matrix (Fin 2) (Fin 2) k)ᵀ), hg,
        Matrix.one_mul, ← Matrix.mul_assoc, hPi', Matrix.one_mul]
    have htr : (g' : Matrix (Fin 2) (Fin 2) k).trace =
        μ * ((g : Matrix (Fin 2) (Fin 2) k).trace / (g : Matrix (Fin 2) (Fin 2) k).det) := by
      rw [hform, Matrix.trace_smul, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hPi, Matrix.one_mul,
        Matrix.trace_transpose, Ga.trace_inv, smul_eq_mul]
    have hdt : (g' : Matrix (Fin 2) (Fin 2) k).det = μ ^ 2 / (g : Matrix (Fin 2) (Fin 2) k).det := by
      have e := congrArg Matrix.det h
      rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_smul, Fintype.card_fin] at e
      field_simp
      have : (P : Matrix (Fin 2) (Fin 2) k).det * ((g' : Matrix (Fin 2) (Fin 2) k).det * (g : Matrix (Fin 2) (Fin 2) k).det) =
          (P : Matrix (Fin 2) (Fin 2) k).det * (μ : k) ^ 2 := by linear_combination e
      exact mul_left_cancel₀ hP this
    simp only [Ga.uf, Ga.tr]
    rw [htr, hdt]
    field_simp
  · intro Γ _ ρ s
    have hd' := Ga.det_ne (ρ s)
    have e : (ad0 ρ s : Matrix (Fin 3) (Fin 3) k) =
        (((ρ s : Matrix (Fin 2) (Fin 2) k).det)⁻¹) • symSquareMatrixHom k (ρ s : Matrix (Fin 2) (Fin 2) k) := by
      rw [ad0, tw_val]
      simp [Matrix.GeneralLinearGroup.det]
    simp only [Ga.tr, Ga.uf]
    rw [e, Matrix.trace_smul, Matrix.trace_fin_two, Matrix.trace_fin_three]
    have hd2 := hd'
    rw [Matrix.det_fin_two] at hd2 ⊢
    simp [symSquareMatrixHom]
    field_simp
    ring
