import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SiegelSmall
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.UnitaryConjIff
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SiegelA

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

set_option linter.unusedSectionVars false

namespace PositivityTheory.SiegelWeilFormula.Ald

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
Simplify using `only [incM]`. Conclude with `Matrix.map_mul (f := (inclR (F := F) (E := E) (AF F)))`.
-/
theorem incM_mul {ι κ ν : Type} [Fintype κ] (M : Matrix ι κ E) (N : Matrix κ ν E) :
    incM F (M * N) = incM F M * incM F N := by
  simp only [incM]
  exact Matrix.map_mul (f := (inclR (F := F) (E := E) (AF F)))

/- English proof (translation)
Use extensionality with `u k`. Apply the tactic sequence `rcases u with u | u <;> simp [incM, diagCols, Matrix.one_apply, apply_ite] <;> split_ifs <;> simp_all`.
-/
theorem incM_diagCols (n : ℕ) :
    incM F (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) E) = (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) := by
  ext u k
  rcases u with u | u <;> simp [incM, diagCols, Matrix.one_apply, apply_ite] <;> split_ifs <;> simp_all

/- English proof (translation)
Use extensionality with `u k`. Simplify using `[Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, Matrix.toCols₁]`.
-/
theorem mul_fromRows_one_zero {R : Type*} [CommRing R] {n : ℕ} (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) :
    M * Matrix.fromRows (1 : Matrix (Fin n) (Fin n) R) (0 : Matrix (Fin n) (Fin n) R) = M.toCols₁ := by
  ext u k
  simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, Matrix.toCols₁]

/- English proof (translation)
Take `⟨-, tb, htb0⟩` from `hb`. Establish `htb : b.1.toCols₁ = (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) E) * tb.1` using `htb0`. Use `⟨tb, ?_⟩` and prove the remaining obligations. Establish `e : (incM F b.1).toCols₁ = incM F b.1.toCols₁` using `rfl`. Rewrite using `[mul_fromRows_one_zero, e, htb, incM_mul]`.

Use `congr 1`. Use extensionality with `u k`. Apply the tactic sequence `rcases u with u | u <;> simp [incM, diagCols, Matrix.one_apply, apply_ite] <;> split_ifs <;> simp_all`.
-/
theorem frame_fromRows {n : ℕ} {Y : Spc F E n} {b : GL (Fin n ⊕ Fin n) E} (hb : IsFrame2 σ Y b) :
    ∃ tb : GL (Fin n) E, incM F b.1 * Matrix.fromRows (1 : Matrix (Fin n) (Fin n) (AE F E)) (0 : Matrix (Fin n) (Fin n) (AE F E)) =
      (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) * incM F tb.1 := by
  obtain ⟨-, tb, htb0⟩ := hb
  have htb : b.1.toCols₁ = (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) E) * tb.1 := htb0
  refine ⟨tb, ?_⟩
  have e : (incM F b.1).toCols₁ = incM F b.1.toCols₁ := rfl
  rw [mul_fromRows_one_zero, e, htb, incM_mul]
  congr 1
  ext u k
  rcases u with u | u <;> simp [incM, diagCols, Matrix.one_apply, apply_ite] <;> split_ifs <;> simp_all

/- English proof (translation)
Establish `e1 : frQ b w * (incM F b.1)ᵀ = w`. Rewrite using `[frQ, Matrix.mul_assoc, ← Matrix.transpose_mul, incM_mul_inv, Matrix.transpose_one, Matrix.mul_one]`. Establish `e2 : incM F b.1 = Matrix.fromCols (incM F b.1.toCols₁) (incM F b.1.toCols₂)`. Use extensionality with `u v`. Apply the tactic sequence `rcases v with v | v <;> rfl`.

Use `conv_lhs => rw [← e1, e2, Matrix.transpose_fromCols, ← Matrix.fromCols_toCols (frQ b w), Matrix.fromCols_mul_fromRows]`.
-/
theorem frame_decomp {m n : ℕ} (b : GL (Fin n ⊕ Fin n) E) (w : Matrix (Fin m) (Fin n ⊕ Fin n) (AE F E)) :
    w = (frQ b w).toCols₁ * (incM F b.1.toCols₁)ᵀ + (frQ b w).toCols₂ * (incM F b.1.toCols₂)ᵀ := by
  have e1 : frQ b w * (incM F b.1)ᵀ = w := by
    rw [frQ, Matrix.mul_assoc, ← Matrix.transpose_mul, incM_mul_inv, Matrix.transpose_one, Matrix.mul_one]
  have e2 : incM F b.1 = Matrix.fromCols (incM F b.1.toCols₁) (incM F b.1.toCols₂) := by
    ext u v
    rcases v with v | v <;> rfl
  conv_lhs => rw [← e1, e2, Matrix.transpose_fromCols, ← Matrix.fromCols_toCols (frQ b w), Matrix.fromCols_mul_fromRows]

end PositivityTheory.SiegelWeilFormula.Ald

end
