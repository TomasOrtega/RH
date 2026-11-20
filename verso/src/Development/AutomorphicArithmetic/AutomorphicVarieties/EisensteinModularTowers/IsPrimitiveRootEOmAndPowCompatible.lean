import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.IsThBIff
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLamOfLSmulIff
import Development.AbelianVarietyTheory.Definitions.Foundations.IsPrimitiveRootTopZeta
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsAlgClosureOfTower
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.isPrimitiveRoot_eOm_and_pow_compatible :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (l : ℕ) [Fact l.Prime] (N : ℕ) [NeZero N], (∀ L : ℕ, IsPrimitiveRoot (eOm ε (1 / ((N * l ^ L : ℕ) : ℚ))) (N * l ^ L)) ∧ (∀ L : ℕ, eOm ε (1 / ((N * l ^ L : ℕ) : ℚ)) ^ N = zt ε l L) ∧ (∀ m n : ℕ, eOm ε (1 / ((N * l ^ (m + n) : ℕ) : ℚ)) ^ (l ^ n) = eOm ε (1 / ((N : ℚ) * (l : ℚ) ^ m))) := by
  intro Ω _ _ _ ε l hl N _
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hl0 : l ≠ 0 := hl.out.ne_zero
  have hN0 : N ≠ 0 := NeZero.ne N
  have hl1 : (l : ℚ) ≠ 0 := by exact_mod_cast hl0
  have hN1 : (N : ℚ) ≠ 0 := by exact_mod_cast hN0
  refine ⟨fun L => GlobalTheory.K4.isPrimitiveRoot_eOm ε (mul_ne_zero hN0 (pow_ne_zero L hl0)), fun L => ?_, fun m n => ?_⟩
  · rw [← GlobalTheory.UlCusp.eOm_nsmul]
    have h : (N : ℚ) * (1 / ((N * l ^ L : ℕ) : ℚ)) = 1 / (l : ℚ) ^ L := by
      push_cast; field_simp
    rw [h]; rfl
  · rw [← GlobalTheory.UlCusp.eOm_nsmul]
    have h : ((l ^ n : ℕ) : ℚ) * (1 / ((N * l ^ (m + n) : ℕ) : ℚ)) = 1 / ((N : ℚ) * (l : ℚ) ^ m) := by
      push_cast; rw [pow_add]; field_simp
    rw [h]
