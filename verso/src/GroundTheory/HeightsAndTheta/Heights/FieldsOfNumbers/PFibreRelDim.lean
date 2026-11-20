import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsFibreRelDim
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PContractRelDimLe
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR PFContracted

noncomputable section

universe u

/- English proof (translation)
Introduce `F _ K K' _ _ _ _ j ι' _ P' hP' n hP'n hPn W _ hWn _ W' hW'`. Take `⟨hW'm, hPW', hcW'⟩` from `hW'`. Use `hP'.isPrime` as an intermediate fact. Use `hW'm.isPrime` as an intermediate fact. Establish `hge : ((n : ℕ) : WithBot (WithTop ℤ)) ≤ relDim W'`.

Rewrite using `[← hWn, ← hcW']`. Conclude with `ContractRelDimLe.proof F K K' j ι' W' hW'm`. Establish `hne : ¬ W' ≤ P'`. Introduce `hle`. Establish `heq : W' = P'` using `le_antisymm hle hPW'`.

Rewrite `hcW'` using `[heq]`. Rewrite `hPn` using `[hcW', hWn]`. Use `congrArg (fun x : WithBot (WithTop ℤ) => x) hPn` as an intermediate fact. Rewrite `this` using `[natCast_withBot_withTop, natCast_withBot_withTop]`. Establish `h2` using `WithTop.coe_injective (WithBot.coe_injective this)`.

Use linear arithmetic over natural numbers and integers. Take `⟨f, hfW', hfP'⟩` from `Set.not_subset.mp hne`. Establish `hstab : ∀ {Q : Ideal (MRing ι' F)}, IsMultiProjPrime Q → ∀ (T : Finset K') (q : MRing ι' F), q ∈ Q → killBlocks T q ∈ Q` using `fun hQ T _ hq => killBlocks_mem_of_isMultiHomogIdeal hQ.multiHomog T hq`. Take `⟨D', -, hD'⟩` from `exists_ringKrullDim_eq (hstab hP') hP'.relevant`. Take `⟨D, -, hD⟩` from `exists_ringKrullDim_eq (hstab hW'm) hW'm.relevant`.

Establish `hstep` using `ringKrullDim_add_one_le hPW' hfP' hfW'`. Rewrite `hstep` using `[hD, hD']`. Establish `hlt : D + 1 ≤ D'` using `by exact_mod_cast hstep`. Rewrite `hP'n` using `[relDim_eq_int hD', natCast_withBot_withTop]`. Establish `hP'z` using `WithTop.coe_injective (WithBot.coe_injective hP'n)`.

Rewrite `hge`, the goal using `[relDim_eq_int hD, natCast_withBot_withTop]`. Establish `hgez : (n : ℤ) ≤ (D : ℤ) - Fintype.card K'` using `WithTop.coe_le_coe.mp (WithBot.coe_le_coe.mp hge)`. Use `congr 2`. Move the coercions through the operations in `at hP'z`. Use linear arithmetic over natural numbers and integers.
-/
theorem FibreRelDim.proof : FibreRelDim.Statement.{u} := by
  intro F _ K K' _ _ _ _ j ι' _ P' hP' n hP'n hPn W _ hWn _ W' hW'
  obtain ⟨hW'm, hPW', hcW'⟩ := hW'
  have := hP'.isPrime
  have := hW'm.isPrime

  have hge : ((n : ℕ) : WithBot (WithTop ℤ)) ≤ relDim W' := by
    rw [← hWn, ← hcW']
    exact ContractRelDimLe.proof F K K' j ι' W' hW'm

  have hne : ¬ W' ≤ P' := by
    intro hle
    have heq : W' = P' := le_antisymm hle hPW'
    rw [heq] at hcW'
    rw [hcW', hWn] at hPn
    have := congrArg (fun x : WithBot (WithTop ℤ) => x) hPn
    rw [natCast_withBot_withTop, natCast_withBot_withTop] at this
    have h2 := WithTop.coe_injective (WithBot.coe_injective this)
    omega
  obtain ⟨f, hfW', hfP'⟩ := Set.not_subset.mp hne
  have hstab : ∀ {Q : Ideal (MRing ι' F)}, IsMultiProjPrime Q →
      ∀ (T : Finset K') (q : MRing ι' F), q ∈ Q → killBlocks T q ∈ Q :=
    fun hQ T _ hq => killBlocks_mem_of_isMultiHomogIdeal hQ.multiHomog T hq
  obtain ⟨D', -, hD'⟩ := exists_ringKrullDim_eq (hstab hP') hP'.relevant
  obtain ⟨D, -, hD⟩ := exists_ringKrullDim_eq (hstab hW'm) hW'm.relevant
  have hstep := ringKrullDim_add_one_le hPW' hfP' hfW'
  rw [hD, hD'] at hstep
  have hlt : D + 1 ≤ D' := by exact_mod_cast hstep
  rw [relDim_eq_int hD', natCast_withBot_withTop] at hP'n
  have hP'z := WithTop.coe_injective (WithBot.coe_injective hP'n)
  rw [relDim_eq_int hD, natCast_withBot_withTop] at hge ⊢
  have hgez : (n : ℤ) ≤ (D : ℤ) - Fintype.card K' :=
    WithTop.coe_le_coe.mp (WithBot.coe_le_coe.mp hge)
  congr 2
  push_cast at hP'z
  omega

end

end GroundTheory.Heights₂.Heights.FieldNumbers
