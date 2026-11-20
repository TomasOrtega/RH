import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPinnedOfIsUnf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryLatticeStabilizerDetRoot
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke.LatticeBasisLifts GlobalTheory.GeoLevel
open GlobalTheory.Member (FinCong IotaOK)
open GlobalTheory.LevelCusp (IsMatch)
open GlobalTheory.Dict (castFr)
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

namespace GlobalTheory.GeoLevel

/- English proof (translation)
Establish an intermediate fact. By extensionality, compare the relevant components. Establish an intermediate fact. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression.
-/
theorem det_mul_cc_det_of_isMatch {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (δ : GL (Fin r) E) (h : IsMatch X X δ) :
    (δ : Matrix (Fin r) (Fin r) E).det * IsCMField.complexConj E (δ : Matrix (Fin r) (Fin r) E).det = 1 := by
  have hm : (δ : Matrix (Fin r) (Fin r) E)ᵀ * X.Gm *
      ((IsCMField.complexConj E : E →+* E).mapMatrix (δ : Matrix (Fin r) (Fin r) E)) = X.Gm := by
    ext i j
    have := h.iso (Pi.single i 1) (Pi.single j 1)
    simp only [herm, cc, Matrix.mulVec_single_one, Matrix.col_apply] at this
    simp only [Pi.single_apply, apply_ite, map_one, map_zero, mul_ite, ite_mul, mul_one, one_mul, mul_zero,
      zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
    rw [← this]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    rfl
  have hd := congrArg Matrix.det hm
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, ← RingHom.map_det] at hd
  apply mul_left_cancel₀ X.Gm_det
  rw [mul_one]
  refine Eq.trans ?_ hd
  rw [← mul_assoc, mul_comm X.Gm.det]
  rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Replace the relevant objects with their definitions. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree. Supply the required witnesses or components. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem four_dvd_finrank_and_det_eq_pm_one : ∀ (D : D7), 4 ∣ Module.finrank ℚ D.host.E ∧ ∀ (r : ℕ) (X : Data D.host.E r) (δ : GL (Fin r) D.host.E), IsMatch X X δ → (δ : Matrix (Fin r) (Fin r) D.host.E).det = 1 ∨ ∃ m : ℕ, 0 < m ∧ (δ : Matrix (Fin r) (Fin r) D.host.E).det ^ m = 1 := by
  intro D
  refine ⟨?_, fun r X δ h => ?_⟩
  · have hE : Module.finrank ℚ D.host.E = 4 * D.R.n := by
      have h : (Module.finrank ℚ D.host.E : ℝ) = 4 * (D.R.n : ℝ) := by
        rw [D.host.finrank_cmField]
        unfold Ranks.n
        push_cast
        ring
      exact_mod_cast h
    exact ⟨_, hE⟩
  · have h1 := det_mul_cc_det_of_isMatch X δ h
    refine Or.inr (GlobalTheory.Mem.StabDet.eq_pm_one_of_unitary D.host _ ⟨?_, h1⟩
      (GlobalTheory.Mem.StabDet.isIntegral_det X.Λ X.Λ_fg X.Λ_span _ fun v hv => (h.lat v).1 hv))
    rw [mul_comm]
    exact h1

end GlobalTheory.GeoLevel
