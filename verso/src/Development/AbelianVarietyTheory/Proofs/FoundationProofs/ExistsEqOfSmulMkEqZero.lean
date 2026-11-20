import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsTrDataGaussianIntOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDerivationOnExtensionCubeDefectStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KaehlerRelationOfDerivationOnLargeSubalgebraStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTowerUnionZetaDerivationModIntegralClosureStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTowerUnionQDerivationModIntegralClosureStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAlmostDualTraceDataTowerUnionAdjoinStatement

open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

namespace GlobalTheory.AlmostEt

/- English proof (translation)
Rewrite `h` using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]`. Take `⟨t, ht⟩` from `h`. Conclude with `⟨t, by simpa [Algebra.smul_def] using ht⟩`.
-/
theorem exists_eq_of_smul_mk_eq_zero {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]
    (s : integralClosure (O0 p) Ω) (ω : Ω)
    (h : s • (Submodule.Quotient.mk ω : Frac p Ω) = 0) :
    ∃ t : integralClosure (O0 p) Ω, (t : Ω) = (s : Ω) * ω := by
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h
  obtain ⟨t, ht⟩ := h
  exact ⟨t, by simpa [Algebra.smul_def] using ht⟩

/- English proof (translation)
Introduce `p _ Ω _ _ hp2 hclo T n hn x y zi qi hz hq hrel`. Establish `hpΩ : (p : Ω) ≠ 0` using `by haveI := GlobalTheory.K5.Basic.charZero_of_isClo hclo`. Conclude with `(Fact.out : p.Prime).ne_zero` after adjusting the coercions. Establish `hrel' : ∑ i, (![x * zi, y * qi] : Fin 2 → integralClosure (O0 p) Ω) i • KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) ((![zS T n, qS T n] : Fin 2 → integralClosure (O0 p) Ω) i) = 0`. Simplify `hrel` using `[Fin.sum_univ_two]`.

Take `⟨F, hF⟩` from `GlobalTheory.T.kaehler_relation_of_derivation_on_large_subalgebra (O0 p) (integralClosure (O0 p) Ω) 2 _ _ hrel'`. Take `⟨C, tr, m, a, b, hFC, htr⟩` from `GlobalTheory.T.exists_almostDualTraceData_towerUnionAdjoin p Ω hp2 hclo T F`. Establish `hzT : zS T n ∈ towerAlg T` using `Algebra.subset_adjoin (Or.inl ⟨n, rfl⟩)`. Establish `hqT : qS T n ∈ towerAlg T` using `Algebra.subset_adjoin (Or.inr ⟨n, rfl⟩)`. Establish `hyC : ∀ i, (![zS T n, qS T n] : Fin 2 → integralClosure (O0 p) Ω) i ∈ C`.

Introduce `i`. Use `fin_cases i`. Conclude with `htr.le hzT`. Conclude with `htr.le hqT`. Establish `hzΩ : T.ζ n * (zi : Ω) = 1`.

Use `congrArg Subtype.val hz` as an intermediate fact. Simplify `this` using `[zS]`. Establish `hqΩ : T.qq n * (qi : Ω) = 1`. Use `congrArg Subtype.val hq` as an intermediate fact. Simplify `this` using `[qS]`.

Take `⟨k, rfl⟩ : ∃ k, n = k + 1` from `⟨n - 1, by omega⟩`. Prove the components needed by the constructor for the conclusion. Take `⟨Dz, hDz, hDzv⟩` from `GlobalTheory.T.exists_towerUnion_zetaDerivation_modIntegralClosure p Ω hclo T`. Take `⟨D', hD', hD'v⟩` from `GlobalTheory.T.exists_derivationOn_extension_cube_defect (O0 p) (integralClosure (O0 p) Ω) (Frac p Ω) (towerAlg T) C tr m a b _ htr Dz hDz`. Establish `h` using `hF C hFC hyC (Frac p Ω) D' hD'`.

Simplify using `only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h`. Rewrite `h` using `[hD'v _ hzT, hD'v _ hqT, (hDzv (k + 1)).1, (hDzv (k + 1)).2, smul_zero, smul_zero, add_zero, smul_smul]`. Take `⟨t, ht⟩` from `exists_eq_of_smul_mk_eq_zero _ _ h`. Use `⟨t, Subtype.ext ?_⟩` and prove the remaining obligations. Move the coercions through the operations in `at ht ⊢`.

Rewrite using `[ht]`. Clear the denominators using the available nonvanishing facts. Take the linear combination `(-((x : Ω) * (p : Ω) ^ (k + 1))) * hzΩ`. Take `⟨Dq, hDq, hDqv⟩` from `GlobalTheory.T.exists_towerUnion_qDerivation_modIntegralClosure p Ω hclo T`. Take `⟨D', hD', hD'v⟩` from `GlobalTheory.T.exists_derivationOn_extension_cube_defect (O0 p) (integralClosure (O0 p) Ω) (Frac p Ω) (towerAlg T) C tr m a b _ htr Dq hDq`.

Establish `h` using `hF C hFC hyC (Frac p Ω) D' hD'`. Simplify using `only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h`. Rewrite `h` using `[hD'v _ hzT, hD'v _ hqT, (hDqv (k + 1)).1, (hDqv (k + 1)).2, smul_zero, smul_zero, zero_add, smul_smul]`. Take `⟨t, ht⟩` from `exists_eq_of_smul_mk_eq_zero _ _ h`. Use `⟨t, Subtype.ext ?_⟩` and prove the remaining obligations.

Move the coercions through the operations in `at ht ⊢`. Rewrite using `[ht]`. Clear the denominators using the available nonvanishing facts. Take the linear combination `(-(y : Ω)) * hqΩ`.
-/
theorem dlog_indep_pow_three : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω],
    p ≠ 2 → IsClo p Ω → ∀ (T : Tower p Ω) (n : ℕ), 1 ≤ n →
    ∀ x y zi qi : (integralClosure (O0 p) Ω), zS T n * zi = 1 → qS T n * qi = 1 →
    (x * zi) • KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) (zS T n) +
      (y * qi) • KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) (qS T n) = 0 →
    (∃ t, (p : (integralClosure (O0 p) Ω)) ^ 3 * x = (p : (integralClosure (O0 p) Ω)) ^ (n - 1) * t) ∧
    (∃ t, (p : (integralClosure (O0 p) Ω)) ^ 3 * y = (p : (integralClosure (O0 p) Ω)) ^ n * t) := by
  intro p _ Ω _ _ hp2 hclo T n hn x y zi qi hz hq hrel
  have hpΩ : (p : Ω) ≠ 0 := by
    haveI := GlobalTheory.K5.Basic.charZero_of_isClo hclo
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hrel' : ∑ i, (![x * zi, y * qi] : Fin 2 → integralClosure (O0 p) Ω) i •
      KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω)
        ((![zS T n, qS T n] : Fin 2 → integralClosure (O0 p) Ω) i) = 0 := by
    simpa [Fin.sum_univ_two] using hrel
  obtain ⟨F, hF⟩ := GlobalTheory.T.kaehler_relation_of_derivation_on_large_subalgebra (O0 p) (integralClosure (O0 p) Ω) 2 _ _ hrel'
  obtain ⟨C, tr, m, a, b, hFC, htr⟩ := GlobalTheory.T.exists_almostDualTraceData_towerUnionAdjoin p Ω hp2 hclo T F
  have hzT : zS T n ∈ towerAlg T := Algebra.subset_adjoin (Or.inl ⟨n, rfl⟩)
  have hqT : qS T n ∈ towerAlg T := Algebra.subset_adjoin (Or.inr ⟨n, rfl⟩)
  have hyC : ∀ i, (![zS T n, qS T n] : Fin 2 → integralClosure (O0 p) Ω) i ∈ C := by
    intro i; fin_cases i
    · exact htr.le hzT
    · exact htr.le hqT
  have hzΩ : T.ζ n * (zi : Ω) = 1 := by
    have := congrArg Subtype.val hz; simpa [zS] using this
  have hqΩ : T.qq n * (qi : Ω) = 1 := by
    have := congrArg Subtype.val hq; simpa [qS] using this
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  constructor
  · obtain ⟨Dz, hDz, hDzv⟩ := GlobalTheory.T.exists_towerUnion_zetaDerivation_modIntegralClosure p Ω hclo T
    obtain ⟨D', hD', hD'v⟩ := GlobalTheory.T.exists_derivationOn_extension_cube_defect (O0 p) (integralClosure (O0 p) Ω) (Frac p Ω)
      (towerAlg T) C tr m a b _ htr Dz hDz
    have h := hF C hFC hyC (Frac p Ω) D' hD'
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h
    rw [hD'v _ hzT, hD'v _ hqT, (hDzv (k + 1)).1, (hDzv (k + 1)).2, smul_zero, smul_zero,
      add_zero, smul_smul] at h
    obtain ⟨t, ht⟩ := exists_eq_of_smul_mk_eq_zero _ _ h
    refine ⟨t, Subtype.ext ?_⟩
    push_cast at ht ⊢
    rw [ht]
    field_simp
    linear_combination (-((x : Ω) * (p : Ω) ^ (k + 1))) * hzΩ
  · obtain ⟨Dq, hDq, hDqv⟩ := GlobalTheory.T.exists_towerUnion_qDerivation_modIntegralClosure p Ω hclo T
    obtain ⟨D', hD', hD'v⟩ := GlobalTheory.T.exists_derivationOn_extension_cube_defect (O0 p) (integralClosure (O0 p) Ω) (Frac p Ω)
      (towerAlg T) C tr m a b _ htr Dq hDq
    have h := hF C hFC hyC (Frac p Ω) D' hD'
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h
    rw [hD'v _ hzT, hD'v _ hqT, (hDqv (k + 1)).1, (hDqv (k + 1)).2, smul_zero, smul_zero,
      zero_add, smul_smul] at h
    obtain ⟨t, ht⟩ := exists_eq_of_smul_mk_eq_zero _ _ h
    refine ⟨t, Subtype.ext ?_⟩
    push_cast at ht ⊢
    rw [ht]
    field_simp
    linear_combination (-(y : Ω)) * hqΩ

end GlobalTheory.AlmostEt
