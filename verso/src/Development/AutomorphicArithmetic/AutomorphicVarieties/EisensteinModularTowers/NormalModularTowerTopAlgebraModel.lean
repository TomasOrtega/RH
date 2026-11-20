import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.IsThBIff
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLamOfLSmulIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsAlgebraicOfJKMem
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

/- English proof (translation)
Introduce `Ω _ _ _ ε X M hM`. Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ`. Use `haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic`. Establish `hζ` using `isPrimitiveRoot_eOm ε hM`. Establish `hS : fixMu Ω M = (IntermediateField.adjoin ℚ {eOm ε (1 / (M : ℚ))}).fixingSubgroup`.

Unfold `fixMu`. Use `congr 1`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[IntermediateField.adjoin_le_iff]`. Introduce `z hz`.

Use `haveI : NeZero M := ⟨hM⟩`. Take `⟨i, -, rfl⟩` from `hζ.eq_pow_of_pow_eq_one hz`. Conclude with `pow_mem (IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton _)) i`. Rewrite using `[IntermediateField.adjoin_simple_le_iff]`. Conclude with `IntermediateField.subset_adjoin ℚ _ hζ.pow_eq_one`.

Establish `h` using `GlobalTheory.K4.LevNormal.normal Ω ε X (CongruenceSubgroup.Gamma M) M _ (Nat.pos_of_ne_zero hM) hζ le_rfl`. Rewrite `h` using `[← hS]`. Conclude with `h`.
-/
theorem UpperTheory.normal_modularTowerTop_algebraModel :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (M : ℕ), M ≠ 0 → @Normal (topF X M) (topL X M) _ _ (algMdl X _ _) := by
  intro Ω _ _ _ ε X M hM
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  have hζ := isPrimitiveRoot_eOm ε hM
  have hS : fixMu Ω M = (IntermediateField.adjoin ℚ {eOm ε (1 / (M : ℚ))}).fixingSubgroup := by
    unfold fixMu
    congr 1
    apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff]
      intro z hz
      haveI : NeZero M := ⟨hM⟩
      obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hz
      exact pow_mem (IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton _)) i
    · rw [IntermediateField.adjoin_simple_le_iff]
      exact IntermediateField.subset_adjoin ℚ _ hζ.pow_eq_one
  have h := GlobalTheory.K4.LevNormal.normal Ω ε X (CongruenceSubgroup.Gamma M) M _ (Nat.pos_of_ne_zero hM) hζ le_rfl
  rw [← hS] at h
  exact h
