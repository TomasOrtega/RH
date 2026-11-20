import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmAOneApply
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer

namespace GlobalTheory.RankFibreKer

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Separate the alternatives or extract the components of the hypothesis. A detailed English derivation is pending.
-/
theorem eq_of_isFirstMax_of_isFirstMax {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {a d : ℕ} {Y : Matrix (Fin a) (Fin d) k} {J J' : Fin a ↪ Fin d} (h : IsFirstMax Y J) (h' : IsFirstMax Y J') :
    J = J' := by
  apply idx.injective
  rcases lt_trichotomy (idx J) (idx J') with hl | he | hl
  · exact absurd ((h'.2 J).2 hl) (not_lt.2 (h.2 J').1)
  · exact he
  · exact absurd ((h.2 J').2 hl) (not_lt.2 (h'.2 J).1)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Replace the relevant objects with their definitions.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Prove the components needed by the constructor for the conclusion. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem sec_inv_mul_mem_slice : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a d : ℕ) (Y : Matrix (Fin a) (Fin d) k) (J : Fin a ↪ Fin d), IsFirstMax Y J →
    ((sec Y)⁻¹).val * Y ∈ slice k a d := by
  intro k _ _ _ _ a d Y J hJ
  have hex : ∃ J, IsFirstMax Y J := ⟨J, hJ⟩
  have hc : hex.choose = J := eq_of_isFirstMax_of_isFirstMax hex.choose_spec hJ
  have hs : (sec Y).val = Y.submatrix id J := by
    unfold sec
    rw [dif_pos hex]
    show Y.submatrix id hex.choose = _
    rw [hc]
  have hsub : (((sec Y)⁻¹).val * Y).submatrix id J = ((sec Y)⁻¹).val * Y.submatrix id J := by
    ext i j; simp [Matrix.mul_apply]
  have hdet : (((sec Y)⁻¹).val).det = (minor Y J)⁻¹ := by
    have e := congrArg Matrix.det (sec Y).inv_mul
    rw [Matrix.det_mul, Matrix.det_one, hs] at e
    exact eq_inv_of_mul_eq_one_left e
  refine ⟨J, ?_, fun J' => ?_⟩
  · rw [hsub, ← hs]; exact (sec Y).inv_mul
  · rw [minor_mul, hdet, map_mul, map_inv₀]
    have h0 : valuation k (minor Y J) ≠ 0 := by simpa using hJ.1
    constructor
    · rw [inv_mul_le_iff₀ (zero_lt_iff.2 h0), mul_one]; exact (hJ.2 J').1
    · intro hl
      rw [inv_mul_lt_iff₀ (zero_lt_iff.2 h0), mul_one]; exact (hJ.2 J').2 hl

end GlobalTheory.RankFibreKer
