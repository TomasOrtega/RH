import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.MultiDiagonalTraces.TraceGamDiag

noncomputable section

open Matrix
open scoped ComplexConjugate

namespace PositivityTheory.RgBcC.Cxi

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat hb)

variable {n : ℕ}

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hbM_herm (m : Md n) : (hbM m).IsHermitian := (hbOrtho n).2 m

/- English proof (translation)
Consider separately whether the proposition holds or fails. Substitute using the available equality. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Substitute using the available equality.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
private theorem trace_single_mul_single_eq_ite (a b c d : Fin n) :
    (single a b (1 : ℂ) * single c d (1 : ℂ)).trace = if b = c ∧ a = d then 1 else 0 := by
  by_cases h : b = c
  · subst h
    rw [single_mul_single_same, one_mul]
    by_cases h' : a = d
    · subst h'
      simp [trace_single_eq_same]
    · simp [Matrix.trace_single_eq_of_ne, h']
  · rw [single_mul_single_of_ne (h := h)]
    simp [h]

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Evaluate the numerical expressions.

Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation. Treat this case separately. Treat this case separately. Treat this case separately.

Treat this case separately.
-/
private theorem trace_hb_mul_hb_eq_ite (p q : Fin n × Fin n) : (hb p * hb q).trace = if p = q then 1 else 0 := by
  obtain ⟨a, b⟩ := p
  obtain ⟨c, d⟩ := q
  have hs : ((↑√2 : ℂ))⁻¹ * (↑√2 : ℂ)⁻¹ = (1 / 2 : ℂ) := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    norm_num
  simp only [hb, Prod.mk.injEq]
  split_ifs <;>
    (try simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul, trace_single_mul_single_eq_ite, smul_eq_mul]) <;>
    (try split_ifs) <;>
    (try simp only [Fin.ext_iff, Fin.lt_def, not_and, not_lt] at *) <;>
    first
    | omega
    | ring1
    | linear_combination 2 * hs
    | linear_combination 2 * hs - 2 * (↑√2 : ℂ)⁻¹ * (↑√2 : ℂ)⁻¹ * Complex.I_sq

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
private theorem trace_hbM_mul_hbM_eq_ite (p q : Md n) : (hbM p * hbM q).trace = if p = q then 1 else 0 := by
  simp only [hbM, trace_hb_mul_hb_eq_ite, EmbeddingLike.apply_eq_iff_eq]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities.

Simplify to obtain the desired conclusion from the available facts.
-/
theorem hbM_li : LinearIndependent ℂ (hbM (n := n)) := by
  rw [linearIndependent_iff']
  intro s g hg i hi
  have h := congrArg (fun X => (X * hbM i).trace) hg
  simp only [Finset.sum_mul, Matrix.smul_mul, Matrix.trace_sum, Matrix.trace_smul, Matrix.zero_mul,
    Matrix.trace_zero, smul_eq_mul, trace_hbM_mul_hbM_eq_ite, mul_ite, mul_one, mul_zero] at h
  rw [Finset.sum_ite_eq'] at h
  simpa [hi] using h

def hbB (n : ℕ) [Nonempty (Md n)] : Module.Basis (Md n) ℂ (Mat n) :=
  basisOfLinearIndependentOfCardEqFinrank hbM_li (by simp [Module.finrank_matrix])

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem hbB_apply [Nonempty (Md n)] (m : Md n) : hbB n m = hbM m := by
  rw [hbB, coe_basisOfLinearIndependentOfCardEqFinrank]

/- English proof (translation)
Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem hbB_repr [Nonempty (Md n)] (X : Mat n) (m : Md n) : (hbB n).repr X m = (X * hbM m).trace := by
  conv_rhs => rw [← (hbB n).sum_repr X]
  simp only [Finset.sum_mul, Matrix.smul_mul, Matrix.trace_sum, Matrix.trace_smul, hbB_apply, trace_hbM_mul_hbM_eq_ite,
    smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

def phiL (y : Mat n) : Mat n →ₗ[ℂ] Mat n where
  toFun X := y * X * yᴴ
  map_add' X X' := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by rw [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]

/- English proof (translation)
By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem Mt_eq_toMatrix [Nonempty (Md n)] (y : Mat n) : Mt y = LinearMap.toMatrix (hbB n) (hbB n) (phiL y) := by
  ext p q
  rw [LinearMap.toMatrix_apply]
  have hH : (y * hbM q * yᴴ).IsHermitian := by
    simp only [IsHermitian, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, (hbM_herm q).eq,
      Matrix.mul_assoc]
  have hr : star (y * hbM q * yᴴ * hbM p).trace = (y * hbM q * yᴴ * hbM p).trace := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hH.eq, (hbM_herm p).eq, Matrix.trace_mul_comm]
  show (((y * hbM q * yᴴ * hbM p).trace.re : ℂ)) = (hbB n).repr (phiL y (hbB n q)) p
  rw [hbB_apply, hbB_repr]
  exact Complex.conj_eq_iff_re.1 hr

def stdB (n : ℕ) : Module.Basis (Md n) ℂ (Mat n) := (Matrix.stdBasis ℂ (Fin n) (Fin n)).reindex finProdFinEquiv

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem stdB_apply (m : Md n) : stdB n m = single (finProdFinEquiv.symm m).1 (finProdFinEquiv.symm m).2 1 := by
  simp [stdB, Matrix.stdBasis_eq_single]

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules. Both sides reduce to the same expression.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem phiL_single (w : Fin n → ℂ) (i j : Fin n) :
    phiL (diagonal w) (single i j (1 : ℂ)) = (w i * conj (w j)) • single i j (1 : ℂ) := by
  ext a b
  simp only [phiL, LinearMap.coe_mk, AddHom.coe_mk, Matrix.diagonal_conjTranspose, Matrix.mul_diagonal,
    Matrix.diagonal_mul, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul, Pi.star_apply]
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    simp only [mul_one]
    rfl
  · simp

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem phiL_stdB (w : Fin n → ℂ) (m : Md n) :
    phiL (diagonal w) (stdB n m) = (w (finProdFinEquiv.symm m).1 * conj (w (finProdFinEquiv.symm m).2)) • stdB n m := by
  rw [stdB_apply, phiL_single]

/- English proof (translation)
By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules.
-/
theorem toMatrix_stdB (w : Fin n → ℂ) : LinearMap.toMatrix (stdB n) (stdB n) (phiL (diagonal w)) =
    diagonal fun m => w (finProdFinEquiv.symm m).1 * conj (w (finProdFinEquiv.symm m).2) := by
  ext p q
  rw [LinearMap.toMatrix_apply, phiL_stdB, map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply,
    diagonal_apply]
  by_cases h : q = p
  · subst h; simp
  · simp [h, Ne.symm h]

end PositivityTheory.RgBcC.Cxi
