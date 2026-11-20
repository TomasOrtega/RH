import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetGNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryGroupFamilyZariskiDenseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPairingLinearSubstitutionAdjointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CauchyBinetColumnFrameProdDetPowEqSumStatement
open Classical MvPolynomial

noncomputable section

namespace GlobalTheory.MinorFrame

variable {ι : Type} [Fintype ι]

/- English proof (translation)
Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses.

Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem eval_rsub_frameMat {a d : ℕ} (x₀ : Var ι d a → ℂ) (g : ι → Matrix (Fin a) (Fin a) ℂ) (P : Pol ι d a) :
    eval (fun v : ι × Fin a × Fin a => g v.1 v.2.1 v.2.2) (rsub (frameMat x₀) P) = eval x₀ (colSub g P) := by
  have h : (eval (fun v : ι × Fin a × Fin a => g v.1 v.2.1 v.2.2)).comp
        (rsub (frameMat x₀) : Pol ι d a →ₐ[ℂ] _).toRingHom
      = (eval x₀).comp (colSub g : Pol ι d a →ₐ[ℂ] Pol ι d a).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c; simp
    · intro v
      obtain ⟨τ, r, j⟩ := v
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, rsub_X, colSub, aeval_X,
        map_sum, map_mul, eval_C, eval_X]
      rw [Fintype.sum_prod_type, Finset.sum_eq_single τ]
      · rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_eq_single j]
        · simp [frameMat, mul_comm]
        · intro b _ hb; simp [frameMat, hb]
        · simp
      · intro b _ hb; simp [frameMat, hb]
      · simp
  exact congrArg (fun φ : Pol ι d a →+* ℂ => φ P) h

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
theorem rsub_frameMat_of_mem_inv {a d : ℕ} {n : ι → ℕ} (x₀ : Var ι d a → ℂ) {P : Pol ι d a}
    (hP : P ∈ inv a d n) : rsub (frameMat x₀) P = eval x₀ P • detG a n := by
  rw [← sub_eq_zero]
  apply GlobalTheory.T.unitaryGroup_family_zariski_dense
  intro g
  rw [map_sub, eval_rsub_frameMat x₀ (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) P, hP g, smul_eval, smul_eval,
    eval_detG a n (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ))]
  ring

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules.

Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem inv_le_span_prodMinors : ∀ {ι : Type} [Fintype ι] (a d : ℕ) (n : ι → ℕ), GlobalTheory.MinorFrame.inv a d n ≤ Submodule.span ℂ (Set.range (GlobalTheory.MinorFrame.prodMinors (ι := ι) (a := a) (d := d) (n := n))) := by
  intro ι _ a d n P hP
  set c := Formalism.L2.DIV.fockS (detG (ι := ι) a n) (detG a n) with hc
  have hc0 : c ≠ 0 := fun h => by
    have := fockS_self_re_pos (detG_ne_zero (ι := ι) a n)
    rw [← hc, h] at this
    simp at this
  have key : c • P = ∑ T : Tup ι a d n, Formalism.L2.DIV.fockS (prodMinors T) P • prodMinors T := by
    apply MvPolynomial.funext
    intro x₀
    have h1 := GlobalTheory.T.fockPairing_linearSubstitution_adjoint (frameMat x₀).conjTranspose (detG a n) P
    rw [Matrix.conjTranspose_conjTranspose, rsub_frameMat_of_mem_inv x₀ hP, GlobalTheory.T.cauchyBinet_columnFrame_prodDetPow_eq_sum] at h1
    rw [← Formalism.L2.DIV.fockL_apply, ← Formalism.L2.DIV.fockL_apply, map_sum, map_smul, LinearMap.sum_apply] at h1
    simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, Formalism.L2.DIV.fockL_apply, smul_eq_mul,
      starRingEnd_apply, star_star] at h1
    rw [smul_eval, map_sum]
    simp only [smul_eval]
    rw [mul_comm, ← h1]
    refine Finset.sum_congr rfl fun T _ => ?_
    ring
  have hP' : P = c⁻¹ • ∑ T : Tup ι a d n, Formalism.L2.DIV.fockS (prodMinors T) P • prodMinors T := by
    rw [← key, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  rw [hP']
  exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun T _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨T, rfl⟩))

end GlobalTheory.MinorFrame
