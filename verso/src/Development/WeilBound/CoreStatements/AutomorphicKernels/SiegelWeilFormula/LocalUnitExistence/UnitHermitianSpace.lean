import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.LdExOfLeaves
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyAlgebraMapMemIntegers
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ldexb.UnitHermitianSpace

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable (F E) in

def unitSpc (n : ℕ) : Spc F E n := ⟨1, stdLattice E n, fun _ => 1, fun _ => 1⟩

omit [NumberField F] [NumberField E] in
/- English proof (translation)
Simplify using `only [stdLattice, Formalism.UG.stdLat, Submodule.mem_pi, Set.mem_univ, true_imp_iff, LinearMap.mem_range, Algebra.linearMap_apply]`. Use `forall_congr' fun i => ⟨?_, fun h => ⟨⟨x i, h⟩, rfl⟩⟩` and prove the remaining obligations. Introduce and unpack `⟨o, ho⟩`. Rewrite using `[← ho]`. Conclude with `o.2`.
-/
theorem mem_std {n : ℕ} (x : Fin n → E) : x ∈ stdLattice E n ↔ ∀ i, IsIntegral ℤ (x i) := by
  simp only [stdLattice, Formalism.UG.stdLat, Submodule.mem_pi, Set.mem_univ, true_imp_iff, LinearMap.mem_range,
    Algebra.linearMap_apply]
  refine forall_congr' fun i => ⟨?_, fun h => ⟨⟨x i, h⟩, rfl⟩⟩
  rintro ⟨o, ho⟩
  rw [← ho]
  exact o.2

omit [NumberField F] [NumberField E] in
/- English proof (translation)
Simplify using `[form, dotProduct]`.
-/
theorem form_one {n : ℕ} (x y : Fin n → E) : form σ (1 : Matrix (Fin n) (Fin n) E) y x = ∑ i, y i * σ (x i) := by
  simp [form, dotProduct]

/- English proof (translation)
Use `⟨by omega, Matrix.fromCols 1 0, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.transpose_fromCols, Matrix.mul_one]`. Establish `hm : (Matrix.fromCols (1 : Matrix (Fin n) (Fin n) ℂ) (0 : Matrix (Fin n) (Fin 0) ℂ)).map star = Matrix.fromCols 1 0`. Use extensionality with `i (j | j)`. Simplify using `[Matrix.one_apply]`.

Conclude with `j.elim0`. Rewrite using `[hm, Matrix.fromRows_mul_fromCols]`. Use extensionality with `(i | i) (j | j)`. Simplify using the standard rewrite rules. Conclude with `j.elim0`.

Conclude with `i.elim0`. Conclude with `i.elim0`.
-/
theorem hasSig_one {n : ℕ} : HasSig (1 : Matrix (Fin n) (Fin n) ℂ) n 0 := by
  refine ⟨by omega, Matrix.fromCols 1 0, ?_⟩
  rw [Matrix.transpose_fromCols, Matrix.mul_one]
  have hm : (Matrix.fromCols (1 : Matrix (Fin n) (Fin n) ℂ) (0 : Matrix (Fin n) (Fin 0) ℂ)).map star =
      Matrix.fromCols 1 0 := by
    ext i (j | j)
    · simp [Matrix.one_apply]
    · exact j.elim0
  rw [hm, Matrix.fromRows_mul_fromCols]
  ext (i | i) (j | j)
  · simp
  · exact j.elim0
  · exact i.elim0
  · exact i.elim0

open scoped ComplexOrder in
/- English proof (translation)
Use `⟨Matrix.one_mul 1, ?_, fun x hx => ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.transpose_one, Matrix.one_mul, Matrix.one_mul, Matrix.map_one _ (star_zero ℂ) (star_one ℂ)]`. Rewrite using `[Matrix.one_mulVec, Matrix.one_mulVec, dotProduct_comm]`. Establish `h` using `(Matrix.dotProduct_star_self_pos_iff (v := x)).2 hx`. Conclude with `(Complex.pos_iff.1 h).1`.
-/
theorem isCartan_one {n : ℕ} : IsCartan (1 : Matrix (Fin n) (Fin n) ℂ) 1 := by
  refine ⟨Matrix.one_mul 1, ?_, fun x hx => ?_⟩
  · rw [Matrix.transpose_one, Matrix.one_mul, Matrix.one_mul, Matrix.map_one _ (star_zero ℂ) (star_one ℂ)]
  · rw [Matrix.one_mulVec, Matrix.one_mulVec, dotProduct_comm]
    have h := (Matrix.dotProduct_star_self_pos_iff (v := x)).2 hx
    exact (Complex.pos_iff.1 h).1

/- English proof (translation)
Use `⟨fun i j => ?_, fun w => ?_, isLattice_stdLattice, fun y => ?_, fun w => ?_, fun v => ?_⟩` and prove the remaining obligations. Simplify using `only [unitSpc, Matrix.one_apply] split_ifs with h1 h2 h2`. Conclude with `map_one σ`. Conclude with `absurd h1.symm h2`. Conclude with `absurd h2.symm h1`.

Conclude with `map_zero σ`. Simplify using `only [unitSpc, Matrix.map_one _ (map_zero _) (map_one _)]`. Conclude with `hasSig_one`. Simplify using `only [unitSpc]`. Rewrite using `[mem_std]`.

Prove the components needed by the constructor for the conclusion. Introduce `hy x hx`. Rewrite `hx` using `[mem_std]`. Rewrite using `[form_one]`. Conclude with `IsIntegral.sum _ fun i _ => (hy i).mul (map_isIntegral_int σ (hx i))`.

Introduce `h i`. Establish `hx : (Pi.single i (1 : E) : Fin n → E) ∈ stdLattice E n`. Rewrite using `[mem_std]`. Introduce `j`. Distinguish the cases in `e : j = i`.

Substitute `e` using the available equality. Simplify using `using isIntegral_one`. Simplify `isIntegral_zero` using `[Pi.single_apply, e]`. Use `h _ hx` as an intermediate fact. Rewrite `this` using `[form_one]`.

Simplify `this` using `[Pi.single_apply]`. Simplify using `only [unitSpc, Matrix.map_one _ (map_zero _) (map_one _)]`. Conclude with `isCartan_one`. Conclude with `isSplitBasis_stdLattice (B.τ v) hB.cm`.
-/
theorem isHerm_unitSpc {B : Base F E} (hB : B.IsGood σ) (n : ℕ) : (unitSpc F E n).IsHerm σ B n 0 := by
  refine ⟨fun i j => ?_, fun w => ?_, isLattice_stdLattice, fun y => ?_, fun w => ?_, fun v => ?_⟩
  · simp only [unitSpc, Matrix.one_apply]
    split_ifs with h1 h2 h2
    · exact map_one σ
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · exact map_zero σ
  · simp only [unitSpc, Matrix.map_one _ (map_zero _) (map_one _)]
    exact hasSig_one
  · simp only [unitSpc]
    rw [mem_std]
    constructor
    · intro hy x hx
      rw [mem_std] at hx
      rw [form_one]
      exact IsIntegral.sum _ fun i _ => (hy i).mul (map_isIntegral_int σ (hx i))
    · intro h i
      have hx : (Pi.single i (1 : E) : Fin n → E) ∈ stdLattice E n := by
        rw [mem_std]
        intro j
        by_cases e : j = i
        · subst e; simpa using isIntegral_one
        · simpa [Pi.single_apply, e] using isIntegral_zero
      have := h _ hx
      rw [form_one] at this
      simpa [Pi.single_apply] using this
  · simp only [unitSpc, Matrix.map_one _ (map_zero _) (map_one _)]
    exact isCartan_one
  · exact isSplitBasis_stdLattice (B.τ v) hB.cm

end PositivityTheory.SiegelWeilFormula.Ldexb.UnitHermitianSpace

end
