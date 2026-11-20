import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.LdExOfLeaves
import Development.WeilBound.ThetaLifts.LatticeBasics.StdExOf
import Development.WeilBound.ThetaLifts.LatticeBasics.FrameConj
import Development.WeilBound.ThetaLifts.LatticeBasics.HgtInt
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalUnitExistence.UnitHermitianSpace

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ldexb

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

omit [NumberField F] [NumberField E] in

/- English proof (translation)
Establish `hD : ((dbl J).map σ)ᵀ = dbl J`. Apply the tactic sequence `ext (i | i) (j | j) <;> simp [dbl, Matrix.fromBlocks, hJ]`. Use `set G := bᵀ * dbl J * b.map σ with hG`. Establish `hs : (G.map σ)ᵀ = G`. Rewrite using `[hG, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.map_map]`.

Establish `e : (⇑σ ∘ ⇑σ) = id` using `funext hc`. Rewrite using `[e, Matrix.map_id, hD, show (bᵀ.map σ)ᵀ = b.map σ by rw [Matrix.transpose_map, Matrix.transpose_transpose], Matrix.mul_assoc]`. Use `congrFun (congrFun hs (Sum.inl ⟨0, hn⟩)) (Sum.inr ⟨0, hn⟩)` as an intermediate fact. Rewrite `this` using `[hb]`. Simplify `this` using `[Matrix.fromBlocks]`.
-/
theorem eps_one {n : ℕ} (hn : 1 ≤ n) (hc : ∀ z : E, σ (σ z) = z) {J : Matrix (Fin n) (Fin n) E}
    (hJ : ∀ i j, σ (J j i) = J i j) {b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E} {ε : ℤˣ}
    (hb : bᵀ * dbl J * b.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) : ((ε : ℤ) : E) = 1 := by
  have hD : ((dbl J).map σ)ᵀ = dbl J := by
    ext (i | i) (j | j) <;> simp [dbl, Matrix.fromBlocks, hJ]
  set G := bᵀ * dbl J * b.map σ with hG
  have hs : (G.map σ)ᵀ = G := by
    rw [hG, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.map_map]
    have e : (⇑σ ∘ ⇑σ) = id := funext hc
    rw [e, Matrix.map_id, hD, show (bᵀ.map σ)ᵀ = b.map σ by rw [Matrix.transpose_map, Matrix.transpose_transpose], Matrix.mul_assoc]
  have := congrFun (congrFun hs (Sum.inl ⟨0, hn⟩)) (Sum.inr ⟨0, hn⟩)
  rw [hb] at this
  simpa [Matrix.fromBlocks] using this

/- English proof (translation)
Break down `Int.units_eq_one_or ε with e | e` into its components or cases. Conclude with `e`. It suffices to derive a contradiction. Rewrite `h` using `[e]`. Establish `: (2 : E) = 0`.

Establish `h' : ((-1 : ℤ) : E) = 1` using `by exact_mod_cast h`. Move the coercions through the operations in `at h'`. Take the linear combination `-h'`. Conclude with `two_ne_zero this`.
-/
theorem eps_unit {ε : ℤˣ} (h : ((ε : ℤ) : E) = 1) : ε = 1 := by
  rcases Int.units_eq_one_or ε with e | e
  · exact e
  · exfalso
    rw [e] at h
    have : (2 : E) = 0 := by
      have h' : ((-1 : ℤ) : E) = 1 := by exact_mod_cast h
      push_cast at h'
      linear_combination -h'
    exact two_ne_zero this

/- English proof (translation)
Take `⟨b, K, a, hb, hK, ha, -, -⟩` from `stdEx_of frameConj hgtEx F E σ B n (UnitHermitianSpace.unitSpc F E n) n 0 hB (Or.inl (UnitHermitianSpace.isHerm_unitSpc hB n))`. Use `⟨UnitHermitianSpace.unitSpc F E n, b, K, a, hb, ?_, hK, ha⟩` and prove the remaining obligations. Take `⟨ε, hε⟩` from `hb.1`. Establish `hc : ∀ z : E, σ (σ z) = z` using `(UnitHermitianSpace.isHerm_unitSpc hB n).herm |> fun _ => by`. Introduce `z`.

Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Conclude with `τ.injective (by rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star])`. Establish `h1` using `eps_one hn hc (UnitHermitianSpace.isHerm_unitSpc hB n).herm hε`. Rewrite using `[hε, eps_unit h1]`. Simplify using `[Ald.jeps]`.
-/
theorem exists_eigenvalueGLOne_eq_cuspidalLabel_gen {B : Base F E} (hB : B.IsGood σ) {n : ℕ} (hn : 1 ≤ n) :
    ∃ (Y₀ : Spc F E n) (b₀ : GL (Fin n ⊕ Fin n) E) (K₀ : Subgroup (G2 σ Y₀)) (a₀ : G2 σ Y₀ → ℝ),
      IsFrame2 σ Y₀ b₀ ∧ b₀.1ᵀ * dbl Y₀.J * b₀.1.map σ = Ald.jeps n 1 ∧
      IsStdK (σ := σ) (Y := Y₀) B b₀ K₀ ∧ IsHgt K₀ a₀ := by
  obtain ⟨b, K, a, hb, hK, ha, -, -⟩ :=
    stdEx_of frameConj hgtEx F E σ B n (UnitHermitianSpace.unitSpc F E n) n 0 hB (Or.inl (UnitHermitianSpace.isHerm_unitSpc hB n))
  refine ⟨UnitHermitianSpace.unitSpc F E n, b, K, a, hb, ?_, hK, ha⟩
  obtain ⟨ε, hε⟩ := hb.1
  have hc : ∀ z : E, σ (σ z) = z := (UnitHermitianSpace.isHerm_unitSpc hB n).herm |> fun _ => by
    intro z
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    exact τ.injective (by rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star])
  have h1 := eps_one hn hc (UnitHermitianSpace.isHerm_unitSpc hB n).herm hε
  rw [hε, eps_unit h1]
  simp [Ald.jeps]

end PositivityTheory.SiegelWeilFormula.Ldexb

end
