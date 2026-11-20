import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.AdicComplExists

variable {L : Type} [CommRing L] {J : Ideal L}

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem evalₐ_algebraMap' (n : ℕ) (r : L) :
    AdicCompletion.evalₐ J n (algebraMap L (AdicCompletion J L) r) = Ideal.Quotient.mk _ r := by
  rw [AlgHom.commutes]; rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem mem_map_pow_iff (hfg : J.FG) (n : ℕ) (y : AdicCompletion J L) :
    y ∈ (J ^ n).map (algebraMap L (AdicCompletion J L)) ↔ AdicCompletion.evalₐ J n y = 0 := by
  rw [← Submodule.restrictScalars_mem L, ← Ideal.smul_top_eq_map,
    AdicCompletion.pow_smul_top_eq_ker_eval hfg, LinearMap.mem_ker]
  have h' : (J ^ n • ⊤ : Ideal L) = J ^ n := by ext x; simp
  exact (map_eq_zero_iff _ (Ideal.quotientEquivAlgOfEq L h').injective).symm

end GlobalTheory.BSP.AdicComplExists

open GlobalTheory.BSP.AdicComplExists in

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Supply the required witnesses or components. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem GlobalTheory.BSP.isCompl_exists : ∀ (L : Type) [CommRing L] (J : Ideal L), J.FG →
    ∃ (Q : Type) (_ : CommRing Q) (i : L →+* Q), IsCompl i J := by
  intro L _ J hfg
  refine ⟨AdicCompletion J L, inferInstance, algebraMap L (AdicCompletion J L), ⟨?_, ?_, ?_⟩⟩
  · rw [IsAdicComplete.map_algebraMap_iff]
    exact AdicCompletion.isAdicComplete hfg
  · intro x n
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ J n x)
    exact ⟨r, by rw [mem_map_pow_iff hfg, map_sub, evalₐ_algebraMap', hr, sub_self]⟩
  · intro a n ha
    rw [mem_map_pow_iff hfg, evalₐ_algebraMap'] at ha
    exact Ideal.Quotient.eq_zero_iff_mem.mp ha
