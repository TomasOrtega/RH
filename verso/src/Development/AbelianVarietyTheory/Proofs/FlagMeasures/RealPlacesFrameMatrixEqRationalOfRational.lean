import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnWittFrameBasisBlockGramStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryStabiliserOrthogonalSummand
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.InclusionInjective
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianFrameExistence.Transfer
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.St

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `D X u wt hW s γ₀ y₀ hs hy`. Take `⟨Q, Qi, G', hQQi, hQiQ, hQq, -, -, -, hG', hblk⟩` from `GlobalTheory.T.columnWittFrame_basis_blockGram D X u wt hW`. Use function extensionality and compare the values at `τ`. Use `set v := X.pl.symm τ with hv`. Use `set φ := X.B.I.φ v with hφ`.

Use `set G := (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm with hGdef`. Establish `hgram : gramQ X wt v = G.map φ`. Use extensionality with `a b`. Establish `h1` using `congrFun (congrFun hblk (Sum.inl a)) (Sum.inl b)`. Rewrite `h1` using `[Matrix.fromBlocks_apply₁₁]`.

Rewrite using `[Matrix.map_apply, ← h1]`. Simplify using `only [gramQ, Matrix.of_apply, rvV]`. Use `PI.ScPiFrameW.hJ_rv X.B.I v (X.crd (qFr wt a)) (X.crd (qFr wt b))` as an intermediate fact. Use `this.trans ?_` and prove the remaining obligations. Use `congr 1`.

Simplify using `only [Formalism.UG.hform, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, hQq, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Establish `hdetG : G.det ≠ 0`. Establish `hJu : IsUnit X.B.I.J.det` using `isUnit_iff_ne_zero.mpr X.B.I.J_det`. Establish `hJinv : X.B.I.J * X.B.I.J⁻¹ = 1` using `Matrix.mul_nonsing_inv _ hJu`.

Establish `hR : Matrix.fromBlocks G 0 0 G' * (Qi * X.B.I.J⁻¹ * (Qi.map (starRingEnd X.B.I.E))ᵀ) = 1`. Rewrite using `[← hblk]`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc Q Qi, hQQi, Matrix.one_mul, ← Matrix.mul_assoc X.B.I.J, hJinv, Matrix.one_mul, ← Matrix.transpose_mul, ← Matrix.map_mul, hQiQ, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]`. Establish `hd` using `congrArg Matrix.det hR`.

Rewrite `hd` using `[Matrix.det_mul, Matrix.det_one, Matrix.det_fromBlocks_zero₂₁]`. Conclude with `left_ne_zero_of_mul (left_ne_zero_of_mul_eq_one hd)`. Establish `hdetQ : IsUnit (gramQ X wt v).det`. Establish `hm : (G.map φ).det = φ G.det` using `(RingHom.map_det φ G).symm`. Rewrite using `[hgram, hm, isUnit_iff_ne_zero, map_ne_zero]`.

Conclude with `hdetG`. Establish `hvec : ∀ x, uMat (s v) *ᵥ rv X.B.I v x = rv X.B.I v (γ₀ *ᵥ x)`. Introduce `x`. Establish `hu : IsUnit (X.B.I.P v).det` using `(Matrix.isUnit_iff_isUnit_det _).mp (X.B.I.P_unit v)`. Establish `hinv : X.B.I.P v * (X.B.I.P v)⁻¹ = 1` using `Matrix.mul_nonsing_inv _ hu`.

Rewrite using `[hs v]`. Simplify using `only [rv]`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.mul_assoc _ (X.B.I.P v), hinv, Matrix.mul_one, ← Matrix.mulVec_mulVec]`. Use `congr 1`. Use function extensionality and compare the values at `k`.

Simplify using `[Matrix.mulVec, dotProduct, map_sum, map_mul, φ]`. Establish `hlin : ∀ b, rv X.B.I v (γ₀ *ᵥ X.crd (qFr wt b)) = ∑ i, φ (y₀ i b) • rvV X v (qFr wt i)`. Introduce `b`. Rewrite using `[hy b]`. Simplify using `only [rvV, rv]`.

Repeatedly rewrite using `[← Matrix.mulVec_smul]`. Rewrite using `[← Matrix.mulVec_sum]`. Use `congr 1`. Use function extensionality and compare the values at `k`. Simplify using `[Finset.sum_apply, map_sum, map_mul, φ]`.

Establish `hM : (Matrix.of fun a b => hJ (X.B.I.ε v) (rvV X v (qFr wt a)) (uMat (s v) *ᵥ rvV X v (qFr wt b))) = gramQ X wt v * y₀.map φ`. Use extensionality with `a b`. Rewrite using `[Matrix.of_apply, show rvV X v (qFr wt b) = rv X.B.I v (X.crd (qFr wt b)) from rfl, hvec, hlin, Matrix.mul_apply]`. Simplify using `only [hJ, Matrix.mulVec_sum, Matrix.mulVec_smul, dotProduct_sum, dotProduct_smul, gramQ, Matrix.of_apply, Matrix.map_apply, smul_eq_mul, rvV]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree. Establish `hfin : y₀.map φ = Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) (y₀.map X.ιE) τ`. Use extensionality with `a b`. Simplify using `only [Formalism.L2.Forms.atInf, Matrix.map_apply, φ, X.φ_eq, hv, Equiv.apply_symm_apply]`. Both sides reduce to the same expression.

Use `show (gramQ X wt v)⁻¹ * _ = _`. Rewrite using `[hM, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdetQ, Matrix.one_mul, hfin]`.
-/
theorem sTil_eq_atInf_of_rational : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V), WittX X u wt → ∀ (s : X.B.I.Ginf) (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) (y₀ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) X.B.I.E), (∀ v, uMat (s v) = (X.B.I.P v)⁻¹ * γ₀.map (X.B.I.φ v) * X.B.I.P v) → (∀ j, γ₀ *ᵥ X.crd (qFr wt j) = ∑ i, y₀ i j • X.crd (qFr wt i)) → sTil X wt s = Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) (y₀.map X.ιE) := by
  intro D X u wt hW s γ₀ y₀ hs hy
  obtain ⟨Q, Qi, G', hQQi, hQiQ, hQq, -, -, -, hG', hblk⟩ := GlobalTheory.T.columnWittFrame_basis_blockGram D X u wt hW
  funext τ
  set v := X.pl.symm τ with hv
  set φ := X.B.I.φ v with hφ
  set G := (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm with hGdef

  have hgram : gramQ X wt v = G.map φ := by
    ext a b
    have h1 := congrFun (congrFun hblk (Sum.inl a)) (Sum.inl b)
    rw [Matrix.fromBlocks_apply₁₁] at h1
    rw [Matrix.map_apply, ← h1]
    simp only [gramQ, Matrix.of_apply, rvV]
    have := PI.ScPiFrameW.hJ_rv X.B.I v (X.crd (qFr wt a)) (X.crd (qFr wt b))
    refine this.trans ?_
    congr 1
    simp only [Formalism.UG.hform, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, hQq, Finset.sum_mul]
    rw [Finset.sum_comm]

  have hdetG : G.det ≠ 0 := by
    have hJu : IsUnit X.B.I.J.det := isUnit_iff_ne_zero.mpr X.B.I.J_det
    have hJinv : X.B.I.J * X.B.I.J⁻¹ = 1 := Matrix.mul_nonsing_inv _ hJu
    have hR : Matrix.fromBlocks G 0 0 G' *
        (Qi * X.B.I.J⁻¹ * (Qi.map (starRingEnd X.B.I.E))ᵀ) = 1 := by
      rw [← hblk]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Q Qi, hQQi, Matrix.one_mul, ← Matrix.mul_assoc X.B.I.J, hJinv, Matrix.one_mul,
        ← Matrix.transpose_mul, ← Matrix.map_mul, hQiQ, Matrix.map_one _ (map_zero _) (map_one _),
        Matrix.transpose_one]
    have hd := congrArg Matrix.det hR
    rw [Matrix.det_mul, Matrix.det_one, Matrix.det_fromBlocks_zero₂₁] at hd
    exact left_ne_zero_of_mul (left_ne_zero_of_mul_eq_one hd)
  have hdetQ : IsUnit (gramQ X wt v).det := by
    have hm : (G.map φ).det = φ G.det := (RingHom.map_det φ G).symm
    rw [hgram, hm, isUnit_iff_ne_zero, map_ne_zero]; exact hdetG

  have hvec : ∀ x, uMat (s v) *ᵥ rv X.B.I v x = rv X.B.I v (γ₀ *ᵥ x) := by
    intro x
    have hu : IsUnit (X.B.I.P v).det := (Matrix.isUnit_iff_isUnit_det _).mp (X.B.I.P_unit v)
    have hinv : X.B.I.P v * (X.B.I.P v)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
    rw [hs v]
    simp only [rv]
    rw [Matrix.mulVec_mulVec, Matrix.mul_assoc _ (X.B.I.P v), hinv, Matrix.mul_one, ← Matrix.mulVec_mulVec]
    congr 1
    funext k
    simp [Matrix.mulVec, dotProduct, map_sum, map_mul, φ]
  have hlin : ∀ b, rv X.B.I v (γ₀ *ᵥ X.crd (qFr wt b)) = ∑ i, φ (y₀ i b) • rvV X v (qFr wt i) := by
    intro b
    rw [hy b]
    simp only [rvV, rv]
    simp_rw [← Matrix.mulVec_smul]
    rw [← Matrix.mulVec_sum]
    congr 1
    funext k
    simp [Finset.sum_apply, map_sum, map_mul, φ]
  have hM : (Matrix.of fun a b => hJ (X.B.I.ε v) (rvV X v (qFr wt a))
      (uMat (s v) *ᵥ rvV X v (qFr wt b))) = gramQ X wt v * y₀.map φ := by
    ext a b
    rw [Matrix.of_apply, show rvV X v (qFr wt b) = rv X.B.I v (X.crd (qFr wt b)) from rfl, hvec, hlin,
      Matrix.mul_apply]
    simp only [hJ, Matrix.mulVec_sum, Matrix.mulVec_smul, dotProduct_sum, dotProduct_smul, gramQ,
      Matrix.of_apply, Matrix.map_apply, smul_eq_mul, rvV]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hfin : y₀.map φ = Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) (y₀.map X.ιE) τ := by
    ext a b
    simp only [Formalism.L2.Forms.atInf, Matrix.map_apply, φ, X.φ_eq, hv, Equiv.apply_symm_apply]
    rfl
  show (gramQ X wt v)⁻¹ * _ = _
  rw [hM, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdetQ, Matrix.one_mul, hfin]

end GlobalTheory.St
