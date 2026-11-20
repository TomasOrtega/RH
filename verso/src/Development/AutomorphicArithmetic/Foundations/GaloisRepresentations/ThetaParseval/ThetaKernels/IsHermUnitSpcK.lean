import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalUnitExistence.UnitHermitianSpace
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Ldexb.UnitHermitianSpace
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
/- English proof (translation)
Use `⟨fun i j => ?_, fun w => ?_, isLattice_stdLattice, fun y => ?_, fun w => ?_, fun v => ?_⟩` and prove the remaining obligations. Simplify using `only [unitSpc, Matrix.one_apply] split_ifs with h1 h2 h2`. Conclude with `map_one σ`. Conclude with `absurd h1.symm h2`. Conclude with `absurd h2.symm h1`.

Conclude with `map_zero σ`. Simplify using `only [unitSpc, Matrix.map_one _ (map_zero _) (map_one _)]`. Conclude with `hasSig_one`. Simplify using `only [unitSpc]`. Rewrite using `[mem_std]`.

Prove the components needed by the constructor for the conclusion. Introduce `hy x hx`. Rewrite `hx` using `[mem_std]`. Rewrite using `[form_one]`. Conclude with `IsIntegral.sum _ fun i _ => (hy i).mul (map_isIntegral_int σ (hx i))`.

Introduce `h i`. Establish `hx : (Pi.single i (1 : E) : Fin n → E) ∈ stdLattice E n`. Rewrite using `[mem_std]`. Introduce `j`. Distinguish the cases in `e : j = i`.

Substitute `e` using the available equality. Simplify using `using isIntegral_one`. Simplify `isIntegral_zero` using `[Pi.single_apply, e]`. Use `h _ hx` as an intermediate fact. Rewrite `this` using `[form_one]`.

Simplify `this` using `[Pi.single_apply]`. Simplify using `only [unitSpc, Matrix.map_one _ (map_zero _) (map_one _)]`. Conclude with `isCartan_one`. Conclude with `isSplitBasis_stdLattice (B.τ v) hB.cm`.
-/
theorem isHerm_unitSpc_k {B : Base F E} (hB : _root_.UpperTheory.TP.W.GoodK σ B) (n : ℕ) : (unitSpc F E n).IsHerm σ B n 0 := by
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
end
