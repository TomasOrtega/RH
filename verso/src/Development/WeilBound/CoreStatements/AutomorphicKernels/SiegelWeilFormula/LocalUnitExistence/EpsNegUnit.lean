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
Establish `hD : ((dbl J).map σ)ᵀ = -dbl J`. Apply the tactic sequence `ext (i | i) (j | j) <;> simp [dbl, Matrix.fromBlocks, hJ]`. Use `set G := bᵀ * dbl J * b.map σ with hG`. Establish `hs : (G.map σ)ᵀ = -G`. Rewrite using `[hG, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.map_map]`.

Establish `e : (⇑σ ∘ ⇑σ) = id` using `funext hc`. Rewrite using `[e, Matrix.map_id, hD, show (bᵀ.map σ)ᵀ = b.map σ by rw [Matrix.transpose_map, Matrix.transpose_transpose]]`. Simplify using `only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]`. Use `congrFun (congrFun hs (Sum.inl ⟨0, hn⟩)) (Sum.inr ⟨0, hn⟩)` as an intermediate fact. Rewrite `this` using `[hb]`.

Simplify `this` using `[Matrix.fromBlocks]`.
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
Break down `Int.units_eq_one_or ε with e | e` into its components or cases. It suffices to derive a contradiction. Rewrite `h` using `[e]`. Establish `: (2 : E) = 0`. Establish `h' : ((1 : ℤ) : E) = -1` using `by exact_mod_cast h`.

Move the coercions through the operations in `at h'`. Take the linear combination `h'`. Conclude with `two_ne_zero this`. Conclude with `e`.
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
Introduce `F E _ _ _ _ _ σ d n h Y b j hn hs hb hJ`. Establish `hB` using `d.ok.good`. Establish `hσ : ∀ z, σ (σ z) = z` using `UnitA.sig_sig hB.cm`. Use `⟨fun x => ?_, val_pull h hJ hb⟩` and prove the remaining obligations. Take `⟨Y₀, b₀, K₀, a₀, hb₀, he₀, hK₀, ha₀⟩` from `exists_eigenvalueGLOne_eq_cuspidalLabel_gen hB hn`.

Take `⟨ε, he⟩` from `hb.1`. Establish `hK : IsStdK (σ` using `σ) (Y := Y) d.B b (d.K.comap j) := Ald.kStd F E σ d n h Y b j hb hJ`. Break down `hs with ⟨-, hY⟩ | ⟨-, hY⟩` into its components or cases. Establish `hε : ε = -1` using `eps_neg_unit (eps_neg hn hσ hY he)`. Substitute `hε` using the available equality.

Take `⟨r, hr, hrf, hri⟩` from `exists_skewUnit hB`. Use `iwa_transport (B := d.B) hσ hb hb₀ he he₀ r ?_ hrf hri hK₀ ha₀.iwa hK x` and prove the remaining obligations. Rewrite using `[hr]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `hε : ε = 1` using `eps_unit (eps_one hn hσ hY he)`. Substitute `hε` using the available equality. Use `iwa_transport (B := d.B) hσ hb hb₀ he he₀ 1 ?_ (fun v => ?_) (fun w => ?_) hK₀ ha₀.iwa hK x` and prove the remaining obligations. Simplify using the standard rewrite rules. Simplify using `only [Units.val_one, inv_one, map_one]`.

Conclude with `⟨one_mem _, one_mem _⟩`. Simplify using the standard rewrite rules.
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
