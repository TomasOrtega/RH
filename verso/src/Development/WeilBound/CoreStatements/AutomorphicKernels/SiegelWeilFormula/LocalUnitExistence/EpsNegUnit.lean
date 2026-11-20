import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalUnitExistence.ExistsEigenvalueGLOneEqCuspidalLabelGen
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalUnitExistence.ExistsSkewUnit
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalUnitExistence.IwaTransport
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalUnitExistence.DetLast
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.FinOneOneMem

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ldexb

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

omit [NumberField F] [NumberField E] in

/- English proof (translation)
Establish an intermediate fact. Apply the first step, then apply the next step to every resulting obligation. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts.

A detailed English derivation is pending.
-/
theorem eps_neg {n : ℕ} (hn : 1 ≤ n) (hc : ∀ z : E, σ (σ z) = z) {J : Matrix (Fin n) (Fin n) E}
    (hJ : ∀ i j, σ (J j i) = -J i j) {b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E} {ε : ℤˣ}
    (hb : bᵀ * dbl J * b.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) : ((ε : ℤ) : E) = -1 := by
  have hD : ((dbl J).map σ)ᵀ = -dbl J := by
    ext (i | i) (j | j) <;> simp [dbl, Matrix.fromBlocks, hJ]
  set G := bᵀ * dbl J * b.map σ with hG
  have hs : (G.map σ)ᵀ = -G := by
    rw [hG, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.map_map]
    have e : (⇑σ ∘ ⇑σ) = id := funext hc
    rw [e, Matrix.map_id, hD, show (bᵀ.map σ)ᵀ = b.map σ by rw [Matrix.transpose_map, Matrix.transpose_transpose]]
    simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
  have := congrFun (congrFun hs (Sum.inl ⟨0, hn⟩)) (Sum.inr ⟨0, hn⟩)
  rw [hb] at this
  simpa [Matrix.fromBlocks] using this

/- English proof (translation)
Separate the alternatives or extract the components of the hypothesis. It suffices to derive a contradiction. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Move the embeddings inside the algebraic operations. Take a linear combination of the given relations to obtain the conclusion. A detailed English derivation is pending.
-/
theorem eps_neg_unit {ε : ℤˣ} (h : ((ε : ℤ) : E) = -1) : ε = -1 := by
  rcases Int.units_eq_one_or ε with e | e
  · exfalso
    rw [e] at h
    have : (2 : E) = 0 := by
      have h' : ((1 : ℤ) : E) = -1 := by exact_mod_cast h
      push_cast at h'
      linear_combination h'
    exact two_ne_zero this
  · exact e

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Substitute using the available equality.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree.

Establish an intermediate fact. Substitute using the available equality. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Supply the required witnesses or components. Simplify using the standard rewrite rules.
-/
theorem hgtPull : Ald.HgtPull := by
  intro F E _ _ _ _ _ σ d n h Y b j hn hs hb hJ
  have hB := d.ok.good
  have hσ : ∀ z, σ (σ z) = z := UnitA.sig_sig hB.cm
  refine ⟨fun x => ?_, val_pull h hJ hb⟩
  obtain ⟨Y₀, b₀, K₀, a₀, hb₀, he₀, hK₀, ha₀⟩ := exists_eigenvalueGLOne_eq_cuspidalLabel_gen hB hn
  obtain ⟨ε, he⟩ := hb.1
  have hK : IsStdK (σ := σ) (Y := Y) d.B b (d.K.comap j) := Ald.kStd F E σ d n h Y b j hb hJ
  rcases hs with ⟨-, hY⟩ | ⟨-, hY⟩
  ·
    have hε : ε = -1 := eps_neg_unit (eps_neg hn hσ hY he)
    subst hε
    obtain ⟨r, hr, hrf, hri⟩ := exists_skewUnit hB
    refine iwa_transport (B := d.B) hσ hb hb₀ he he₀ r ?_ hrf hri hK₀ ha₀.iwa hK x
    rw [hr]; push_cast; ring
  ·
    have hε : ε = 1 := eps_unit (eps_one hn hσ hY he)
    subst hε
    refine iwa_transport (B := d.B) hσ hb hb₀ he he₀ 1 ?_ (fun v => ?_) (fun w => ?_) hK₀ ha₀.iwa hK x
    · simp
    · simp only [Units.val_one, inv_one, map_one]; exact ⟨one_mem _, one_mem _⟩
    · simp

end PositivityTheory.SiegelWeilFormula.Ldexb

end
