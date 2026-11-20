import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.LdExOfLeaves

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ldexb

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable {n : ℕ} {Y : Spc F E n}

omit [NumberField E] in
/- English proof (translation)
The claim follows from `Matrix.map_mul`.
-/
theorem incM_mul' {α β γ : Type} [Fintype β] (X : Matrix α β E) (Z : Matrix β γ E) :
    incM F (X * Z) = incM F X * incM F Z := Matrix.map_mul

omit [NumberField E] in
/- English proof (translation)
The claim follows from `Matrix.map_one _ (map_zero _) (map_one _)`.
-/
theorem incM_one' {ι : Type} [Fintype ι] [DecidableEq ι] : incM F (1 : Matrix ι ι E) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

omit [NumberField E] in
/- English proof (translation)
Rewrite using `[← incM_mul', Units.mul_inv, incM_one']`.
-/
theorem incM_mul_inv' {ι : Type} [Fintype ι] [DecidableEq ι] (b : GL ι E) : incM F b.1 * incM F (b⁻¹).1 = 1 := by
  rw [← incM_mul', Units.mul_inv, incM_one']

omit [NumberField E] in
/- English proof (translation)
Rewrite using `[← incM_mul', Units.inv_mul, incM_one']`.
-/
theorem incM_inv_mul' {ι : Type} [Fintype ι] [DecidableEq ι] (b : GL ι E) : incM F (b⁻¹).1 * incM F b.1 = 1 := by
  rw [← incM_mul', Units.inv_mul, incM_one']

omit [NumberField E] in
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem matrixRep_one : mat2 (1 : G2 σ Y) = 1 := rfl

omit [NumberField E] in
/- English proof (translation)
Use `show incM F (b⁻¹).1 * (mat2 x * mat2 z) * incM F b.1 = (incM F (b⁻¹).1 * mat2 x * incM F b.1) * (incM F (b⁻¹).1 * mat2 z * incM F b.1)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[incM_mul_inv', Matrix.mul_one]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = _ := by simp only [Matrix.mul_assoc]`.
-/
theorem inFrame_mul (b : GL (Fin n ⊕ Fin n) E) (x z : G2 σ Y) : inFrame b (x * z) = inFrame b x * inFrame b z := by
  show incM F (b⁻¹).1 * (mat2 x * mat2 z) * incM F b.1 =
    (incM F (b⁻¹).1 * mat2 x * incM F b.1) * (incM F (b⁻¹).1 * mat2 z * incM F b.1)
  calc incM F (b⁻¹).1 * (mat2 x * mat2 z) * incM F b.1 =
      incM F (b⁻¹).1 * mat2 x * (incM F b.1 * incM F (b⁻¹).1) * mat2 z * incM F b.1 := by
        rw [incM_mul_inv', Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

omit [NumberField E] in
/- English proof (translation)
Use `show incM F (b⁻¹).1 * mat2 (1 : G2 σ Y) * incM F b.1 = 1`. Rewrite using `[matrixRep_one, Matrix.mul_one, incM_inv_mul']`.
-/
theorem inFrame_one (b : GL (Fin n ⊕ Fin n) E) : inFrame b (1 : G2 σ Y) = 1 := by
  show incM F (b⁻¹).1 * mat2 (1 : G2 σ Y) * incM F b.1 = 1
  rw [matrixRep_one, Matrix.mul_one, incM_inv_mul']

omit [NumberField E] in
/- English proof (translation)
Use `show mat2 x = incM F b.1 * (incM F (b⁻¹).1 * mat2 x * incM F b.1) * incM F (b⁻¹).1`. Simplify using `only [← Matrix.mul_assoc, incM_mul_inv', Matrix.one_mul]`. Rewrite using `[Matrix.mul_assoc, incM_mul_inv', Matrix.mul_one]`.
-/
theorem matrix_eq_frame_conjugate (b : GL (Fin n ⊕ Fin n) E) (x : G2 σ Y) : mat2 x = incM F b.1 * inFrame b x * incM F (b⁻¹).1 := by
  show mat2 x = incM F b.1 * (incM F (b⁻¹).1 * mat2 x * incM F b.1) * incM F (b⁻¹).1
  simp only [← Matrix.mul_assoc, incM_mul_inv', Matrix.one_mul]
  rw [Matrix.mul_assoc, incM_mul_inv', Matrix.mul_one]

def ParF (b : GL (Fin n ⊕ Fin n) E) (x : G2 σ Y) : Prop := (inFrame b x).toBlocks₂₁ = 0

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, Matrix.toCols₁]`.
-/
theorem mul_fromRows_one_zero {R m k : Type} [Semiring R] [Fintype k] [DecidableEq k] (M : Matrix m (k ⊕ k) R) :
    M * Matrix.fromRows (1 : Matrix k k R) (0 : Matrix k k R) = M.toCols₁ := by
  ext i j
  simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, Matrix.toCols₁]

/- English proof (translation)
Apply the tactic sequence `ext (i | i) j <;> rfl`.
-/
theorem toCols₁_eq_fromRows {R m k : Type} (M : Matrix (m ⊕ m) (k ⊕ k) R) :
    M.toCols₁ = Matrix.fromRows M.toBlocks₁₁ M.toBlocks₂₁ := by
  ext (i | i) j <;> rfl

/- English proof (translation)
Apply the tactic sequence `ext (i | i) j <;> simp [Matrix.mul_apply, Matrix.one_apply]`.
-/
theorem fromRows_one_zero_mul {R k l : Type} [Semiring R] [Fintype k] [DecidableEq k] (S : Matrix k l R) :
    Matrix.fromRows (1 : Matrix k k R) (0 : Matrix k k R) * S = Matrix.fromRows S (0 : Matrix k l R) := by
  ext (i | i) j <;> simp [Matrix.mul_apply, Matrix.one_apply]

omit [NumberField E] in
/- English proof (translation)
Apply the tactic sequence `ext (i | i) j <;> by_cases h : i = j <;> simp [incM, Matrix.one_apply, h]`.
-/
theorem inclusion_from_rows_identity_zero :
    incM F (Matrix.fromRows (1 : Matrix (Fin n) (Fin n) E) (0 : Matrix (Fin n) (Fin n) E)) =
      Matrix.fromRows (1 : Matrix (Fin n) (Fin n) (AE F E)) (0 : Matrix (Fin n) (Fin n) (AE F E)) := by
  ext (i | i) j <;> by_cases h : i = j <;> simp [incM, Matrix.one_apply, h]

omit [NumberField E] in
/- English proof (translation)
Apply the tactic sequence `ext (i | i) j <;> by_cases h : i = j <;> simp [incM, diagCols, Matrix.one_apply, h]`.
-/
theorem incM_diagCols : incM F (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) E) = diagCols (Fin n) := by
  ext (i | i) j <;> by_cases h : i = j <;> simp [incM, diagCols, Matrix.one_apply, h]

/- English proof (translation)
Take `⟨-, t, ht⟩` from `hb`. Establish `ht' : b.1.toCols₁ = (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) E) * t.1` using `ht`. Use `⟨t, ?_⟩` and prove the remaining obligations. Rewrite using `[← inclusion_from_rows_identity_zero, ← incM_mul', mul_fromRows_one_zero, ht', incM_mul', incM_diagCols]`.
-/
theorem frame_cols {b : GL (Fin n ⊕ Fin n) E} (hb : IsFrame2 σ Y b) : ∃ t₀ : GL (Fin n) E,
    incM F b.1 * Matrix.fromRows (1 : Matrix (Fin n) (Fin n) (AE F E)) (0 : Matrix (Fin n) (Fin n) (AE F E)) = (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) * incM F t₀.1 := by
  obtain ⟨-, t, ht⟩ := hb
  have ht' : b.1.toCols₁ = (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) E) * t.1 := ht
  refine ⟨t, ?_⟩
  rw [← inclusion_from_rows_identity_zero, ← incM_mul', mul_fromRows_one_zero, ht', incM_mul', incM_diagCols]

omit [NumberField E] in
/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.det_mul, Matrix.det_mul, Matrix.det_mul]`. Expand and normalize the polynomial expressions, which then agree. Use `_ = S.det := by rw [incM_mul_inv', Matrix.det_one, mul_one]`.
-/
theorem det_conj {ι : Type} [Fintype ι] [DecidableEq ι] (t₀ : GL ι E) (S : Matrix ι ι (AE F E)) :
    (incM F (t₀⁻¹).1 * S * incM F t₀.1).det = S.det := by
  calc (incM F (t₀⁻¹).1 * S * incM F t₀.1).det = S.det * (incM F t₀.1 * incM F (t₀⁻¹).1).det := by
        rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_mul]; ring
    _ = S.det := by rw [incM_mul_inv', Matrix.det_one, mul_one]

/- English proof (translation)
Take `⟨t₀, h0⟩` from `frame_cols hb`. Use `set EsymmMapInvMulProd : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E) := Matrix.fromRows (1 : Matrix (Fin n) (Fin n) (AE F E)) (0 : Matrix (Fin n) (Fin n) (AE F E)) with hR`. Establish `hd : (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) = incM F b.1 * EsymmMapInvMulProd * incM F (t₀⁻¹).1`. Rewrite using `[h0, Matrix.mul_assoc, incM_mul_inv', Matrix.mul_one]`. Establish `hp : mat2 p * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) = (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) * (t : Matrix (Fin n) (Fin n) (AE F E))` using `h`.

Establish `key : inFrame b p * EsymmMapInvMulProd = EsymmMapInvMulProd * (incM F (t₀⁻¹).1 * t.1 * incM F t₀.1)` using `by show incM F (b⁻¹).1 * mat2 p * incM F b.1 * EsymmMapInvMulProd = _`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.mul_assoc _ (incM F b.1), h0]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = incM F (b⁻¹).1 * (incM F b.1 * EsymmMapInvMulProd * incM F (t₀⁻¹).1) * t.1 * incM F t₀.1 := by`.

Rewrite using `[hp, ← hd]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = (incM F (b⁻¹).1 * incM F b.1) * EsymmMapInvMulProd * (incM F (t₀⁻¹).1 * t.1 * incM F t₀.1) := by`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = _ := by rw [incM_inv_mul', Matrix.one_mul]`.

Rewrite `key` using `[hR, mul_fromRows_one_zero, toCols₁_eq_fromRows, fromRows_one_zero_mul]`. Take `⟨k1, k2⟩` from `Matrix.fromRows_inj key`. Conclude with `⟨k2, by rw [k1, det_conj]⟩`.
-/
theorem par_to {b : GL (Fin n ⊕ Fin n) E} (hb : IsFrame2 σ Y b) {p : G2 σ Y} {t : GL (Fin n) (AE F E)} (h : IsPar p t) :
    ParF b p ∧ (inFrame b p).toBlocks₁₁.det = t.1.det := by
  obtain ⟨t₀, h0⟩ := frame_cols hb
  set EsymmMapInvMulProd : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E) :=
    Matrix.fromRows (1 : Matrix (Fin n) (Fin n) (AE F E)) (0 : Matrix (Fin n) (Fin n) (AE F E)) with hR
  have hd : (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) = incM F b.1 * EsymmMapInvMulProd * incM F (t₀⁻¹).1 := by
    rw [h0, Matrix.mul_assoc, incM_mul_inv', Matrix.mul_one]
  have hp : mat2 p * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) = (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) * (t : Matrix (Fin n) (Fin n) (AE F E)) := h
  have key : inFrame b p * EsymmMapInvMulProd = EsymmMapInvMulProd * (incM F (t₀⁻¹).1 * t.1 * incM F t₀.1) := by
    show incM F (b⁻¹).1 * mat2 p * incM F b.1 * EsymmMapInvMulProd = _
    calc incM F (b⁻¹).1 * mat2 p * incM F b.1 * EsymmMapInvMulProd = incM F (b⁻¹).1 * (mat2 p * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E))) * incM F t₀.1 := by
          rw [Matrix.mul_assoc _ (incM F b.1), h0]; simp only [Matrix.mul_assoc]
      _ = incM F (b⁻¹).1 * (incM F b.1 * EsymmMapInvMulProd * incM F (t₀⁻¹).1) * t.1 * incM F t₀.1 := by
          rw [hp, ← hd]; simp only [Matrix.mul_assoc]
      _ = (incM F (b⁻¹).1 * incM F b.1) * EsymmMapInvMulProd * (incM F (t₀⁻¹).1 * t.1 * incM F t₀.1) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [incM_inv_mul', Matrix.one_mul]
  rw [hR, mul_fromRows_one_zero, toCols₁_eq_fromRows, fromRows_one_zero_mul] at key
  obtain ⟨k1, k2⟩ := Matrix.fromRows_inj key
  exact ⟨k2, by rw [k1, det_conj]⟩

/- English proof (translation)
Take `⟨t₀, h0⟩` from `frame_cols hb`. Use `set X := inFrame b p with hXdef`. Use `set S := X.toBlocks₁₁ with hS`. Use `set EsymmMapInvMulProd : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E) := Matrix.fromRows (1 : Matrix (Fin n) (Fin n) (AE F E)) (0 : Matrix (Fin n) (Fin n) (AE F E)) with hR`. Establish `hX : X = Matrix.fromBlocks S X.toBlocks₁₂ 0 X.toBlocks₂₂`.

Rewrite using `[← h]`. Conclude with `(Matrix.fromBlocks_toBlocks X).symm`. Establish `hXu : IsUnit X.det`. Use `Matrix.isUnit_det_of_right_inverse (B := inFrame b p⁻¹) ?_` and prove the remaining obligations. Rewrite using `[hXdef, ← inFrame_mul, mul_inv_cancel, inFrame_one]`.

Establish `hSu : IsUnit S.det`. Rewrite `hXu` using `[hX, Matrix.det_fromBlocks_zero₂₁]`. Conclude with `isUnit_of_mul_isUnit_left hXu`. Establish `hSS : S * S⁻¹ = 1` using `Matrix.mul_nonsing_inv S hSu`. Establish `hSS' : S⁻¹ * S = 1` using `Matrix.nonsing_inv_mul S hSu`.

Establish `h1 : incM F t₀.1 * incM F (t₀⁻¹).1 = 1` using `incM_mul_inv' t₀`. Establish `h2 : incM F (t₀⁻¹).1 * incM F t₀.1 = 1` using `incM_inv_mul' t₀`. Set `t : GL (Fin n) (AE F E)` to `⟨incM F t₀.1 * S * incM F (t₀⁻¹).1, incM F t₀.1 * S⁻¹ * incM F (t₀⁻¹).1, by`. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation.

Establish `hd : (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) = incM F b.1 * EsymmMapInvMulProd * incM F (t₀⁻¹).1`. Rewrite using `[h0, Matrix.mul_assoc, incM_mul_inv', Matrix.mul_one]`. Establish `hXR : X * EsymmMapInvMulProd = EsymmMapInvMulProd * S`. Rewrite using `[hR, mul_fromRows_one_zero, toCols₁_eq_fromRows, fromRows_one_zero_mul, ← hS]`. Rewrite using `[show X.toBlocks₂₁ = 0 from h]`.

Use `⟨t, ?_, ?_⟩` and prove the remaining obligations. Use `show mat2 p * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) = (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) * (incM F t₀.1 * S * incM F (t₀⁻¹).1)`. Rewrite using `[matrix_eq_frame_conjugate b p, ← hXdef, hd]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[incM_inv_mul', Matrix.mul_one]`.

Simplify using `only [Matrix.mul_assoc]`. Use `_ = incM F b.1 * EsymmMapInvMulProd * (incM F (t₀⁻¹).1 * incM F t₀.1) * S * incM F (t₀⁻¹).1 := by`. Rewrite using `[hXR, h2, Matrix.mul_one]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = _ := by simp only [Matrix.mul_assoc]`.

Use `show (incM F t₀.1 * S * incM F (t₀⁻¹).1).det = S.det`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.det_mul, Matrix.det_mul, Matrix.det_mul]`. Expand and normalize the polynomial expressions, which then agree. Use `_ = S.det := by rw [h1, Matrix.det_one, mul_one]`.
-/
theorem par_of {b : GL (Fin n ⊕ Fin n) E} (hb : IsFrame2 σ Y b) {p : G2 σ Y} (h : ParF b p) :
    ∃ t : GL (Fin n) (AE F E), IsPar p t ∧ t.1.det = (inFrame b p).toBlocks₁₁.det := by
  obtain ⟨t₀, h0⟩ := frame_cols hb
  set X := inFrame b p with hXdef
  set S := X.toBlocks₁₁ with hS
  set EsymmMapInvMulProd : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E) :=
    Matrix.fromRows (1 : Matrix (Fin n) (Fin n) (AE F E)) (0 : Matrix (Fin n) (Fin n) (AE F E)) with hR
  have hX : X = Matrix.fromBlocks S X.toBlocks₁₂ 0 X.toBlocks₂₂ := by
    rw [← h]; exact (Matrix.fromBlocks_toBlocks X).symm
  have hXu : IsUnit X.det := by
    refine Matrix.isUnit_det_of_right_inverse (B := inFrame b p⁻¹) ?_
    rw [hXdef, ← inFrame_mul, mul_inv_cancel, inFrame_one]
  have hSu : IsUnit S.det := by
    rw [hX, Matrix.det_fromBlocks_zero₂₁] at hXu
    exact isUnit_of_mul_isUnit_left hXu
  have hSS : S * S⁻¹ = 1 := Matrix.mul_nonsing_inv S hSu
  have hSS' : S⁻¹ * S = 1 := Matrix.nonsing_inv_mul S hSu
  have h1 : incM F t₀.1 * incM F (t₀⁻¹).1 = 1 := incM_mul_inv' t₀
  have h2 : incM F (t₀⁻¹).1 * incM F t₀.1 = 1 := incM_inv_mul' t₀
  let t : GL (Fin n) (AE F E) :=
    ⟨incM F t₀.1 * S * incM F (t₀⁻¹).1, incM F t₀.1 * S⁻¹ * incM F (t₀⁻¹).1, by
      calc incM F t₀.1 * S * incM F (t₀⁻¹).1 * (incM F t₀.1 * S⁻¹ * incM F (t₀⁻¹).1) =
          incM F t₀.1 * S * (incM F (t₀⁻¹).1 * incM F t₀.1) * S⁻¹ * incM F (t₀⁻¹).1 := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [h2, Matrix.mul_one, Matrix.mul_assoc (incM F t₀.1) S, hSS, Matrix.mul_one, h1], by
      calc incM F t₀.1 * S⁻¹ * incM F (t₀⁻¹).1 * (incM F t₀.1 * S * incM F (t₀⁻¹).1) =
          incM F t₀.1 * S⁻¹ * (incM F (t₀⁻¹).1 * incM F t₀.1) * S * incM F (t₀⁻¹).1 := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [h2, Matrix.mul_one, Matrix.mul_assoc (incM F t₀.1) S⁻¹, hSS', Matrix.mul_one, h1]⟩
  have hd : (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) = incM F b.1 * EsymmMapInvMulProd * incM F (t₀⁻¹).1 := by
    rw [h0, Matrix.mul_assoc, incM_mul_inv', Matrix.mul_one]
  have hXR : X * EsymmMapInvMulProd = EsymmMapInvMulProd * S := by
    rw [hR, mul_fromRows_one_zero, toCols₁_eq_fromRows, fromRows_one_zero_mul, ← hS]
    rw [show X.toBlocks₂₁ = 0 from h]
  refine ⟨t, ?_, ?_⟩
  · show mat2 p * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) = (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) * (incM F t₀.1 * S * incM F (t₀⁻¹).1)
    rw [matrix_eq_frame_conjugate b p, ← hXdef, hd]
    calc incM F b.1 * X * incM F (b⁻¹).1 * (incM F b.1 * EsymmMapInvMulProd * incM F (t₀⁻¹).1) =
        incM F b.1 * X * (incM F (b⁻¹).1 * incM F b.1) * EsymmMapInvMulProd * incM F (t₀⁻¹).1 := by simp only [Matrix.mul_assoc]
      _ = incM F b.1 * (X * EsymmMapInvMulProd) * incM F (t₀⁻¹).1 := by
          rw [incM_inv_mul', Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = incM F b.1 * EsymmMapInvMulProd * (incM F (t₀⁻¹).1 * incM F t₀.1) * S * incM F (t₀⁻¹).1 := by
          rw [hXR, h2, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]
  · show (incM F t₀.1 * S * incM F (t₀⁻¹).1).det = S.det
    calc (incM F t₀.1 * S * incM F (t₀⁻¹).1).det = S.det * (incM F t₀.1 * incM F (t₀⁻¹).1).det := by
          rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_mul]; ring
      _ = S.det := by rw [h1, Matrix.det_one, mul_one]

end PositivityTheory.SiegelWeilFormula.Ldexb

end
