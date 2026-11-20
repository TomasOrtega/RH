import Mathlib
import Formalism.RealPlaceAnalysis.SmoothOnGVIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OffDiagonalBlockSumSqNormBlockUnitaryInvariantStatement
open MeasureTheory Matrix
open Formalism.REAL (UJ KG toM toMK muK expG inG Jm Kset)

namespace GlobalTheory

/- English proof (translation)
Introduce `n ε`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `hM : Continuous fun g : UJ ε => toM g` using `Units.continuous_val.comp continuous_subtype_val`. Use `continuous_finset_sum _ fun z _ => ?_` and prove the remaining obligations. Conclude with `((continuous_apply z.1.2).comp ((continuous_apply z.1.1).comp hM)).norm.pow 2`.

Introduce `k k' g`. Establish `hk : toM (k : UJ ε) ∈ Kset ε` using `k.2`. Establish `hk' : toM (k' : UJ ε) ∈ Kset ε` using `k'.2`. Establish `hmul : toM ((k : UJ ε) * g * (k' : UJ ε)) = toM (k : UJ ε) * toM g * toM (k' : UJ ε)` using `rfl`. Rewrite using `[hmul]`.

Use `GlobalTheory.T.offDiagonalBlock_sum_sq_norm_blockUnitary_invariant n ε _ _ _ ?_ hk.2 ?_ hk'.2` and prove the remaining obligations. Conclude with `Matrix.mem_unitaryGroup_iff'.mp hk.1`. Conclude with `Matrix.mem_unitaryGroup_iff'.mp hk'.1`.
-/
theorem offDiagBlockNorm_cont_inv : ∀ (n : ℕ) (ε : Fin n → Bool), (Continuous fun g : UJ ε => ∑ z : {z : Fin n × Fin n // ε z.1 = true ∧ ε z.2 = false}, ‖(toM g) z.1.1 z.1.2‖ ^ 2) ∧ ∀ (k k' : KG ε) (g : UJ ε), ∑ z : {z : Fin n × Fin n // ε z.1 = true ∧ ε z.2 = false}, ‖(toM ((k : UJ ε) * g * (k' : UJ ε))) z.1.1 z.1.2‖ ^ 2 = ∑ z : {z : Fin n × Fin n // ε z.1 = true ∧ ε z.2 = false}, ‖(toM g) z.1.1 z.1.2‖ ^ 2 := by
  intro n ε
  refine ⟨?_, ?_⟩
  · have hM : Continuous fun g : UJ ε => toM g :=
      Units.continuous_val.comp continuous_subtype_val
    refine continuous_finset_sum _ fun z _ => ?_
    exact ((continuous_apply z.1.2).comp ((continuous_apply z.1.1).comp hM)).norm.pow 2
  · intro k k' g
    have hk : toM (k : UJ ε) ∈ Kset ε := k.2
    have hk' : toM (k' : UJ ε) ∈ Kset ε := k'.2
    have hmul : toM ((k : UJ ε) * g * (k' : UJ ε)) = toM (k : UJ ε) * toM g * toM (k' : UJ ε) := rfl
    rw [hmul]
    refine GlobalTheory.T.offDiagonalBlock_sum_sq_norm_blockUnitary_invariant n ε _ _ _ ?_ hk.2 ?_ hk'.2
    · exact Matrix.mem_unitaryGroup_iff'.mp hk.1
    · exact Matrix.mem_unitaryGroup_iff'.mp hk'.1

end GlobalTheory
