import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicCoefficientSplitting
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthonormalFlagTranslateHolds

namespace ReciprocityTheory.ChartRestriction.G.FD.OrthonormalPerpBasis

open NumberField Complex Matrix
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

variable {r : ℕ} (X : Data E r)

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem ortho_h {x : Frame X.Ψ r} (ho : X.IsOrtho x) (τ : X.Ψ) (a b : Fin r) :
    hermC τ.1 X.Gm (col (mat x τ) a) (col (mat x τ) b) =
      if a = b then ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) else 0 := by
  have h := congrFun (congrFun (ho τ) a) b
  rw [Matrix.diagonal_apply] at h
  exact h

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation.

Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem span_cols {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (w : Fin r → ℂ) :
    ∃ c : Fin r → ℂ, w = ∑ a, c a • col (mat x τ) a := by
  have hdet : IsUnit (mat x τ).det := isUnit_iff_ne_zero.mpr (hx τ).1
  refine ⟨(mat x τ)⁻¹ *ᵥ w, ?_⟩
  have hBB : mat x τ *ᵥ ((mat x τ)⁻¹ *ᵥ w) = w := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  calc w = mat x τ *ᵥ ((mat x τ)⁻¹ *ᵥ w) := hBB.symm
    _ = _ := by
      funext k
      simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, col]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/- English proof (translation)
Replace the relevant objects with their definitions. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem sgn_mul_self (a : ℕ) : ((sgn X.p0 a : ℝ) : ℂ) * ((sgn X.p0 a : ℝ) : ℂ) = 1 := by
  unfold sgn
  split_ifs <;> simp

/- English proof (translation)
Replace the relevant objects with their definitions. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem hermC_sum_smul_left' {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (c : Fin r → ℂ)
    (w : Fin r → Fin r → ℂ) (u : Fin r → ℂ) :
    hermC τ G (∑ i, c i • w i) u = ∑ i, c i * hermC τ G (w i) u := by
  unfold hermC
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun b _ => by ring

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem expand {x : Frame X.Ψ r} (hx : x ∈ X.dom) (ho : X.IsOrtho x) (τ : X.Ψ) (v : Fin r → ℂ) :
    v = ∑ a : Fin r, (((sgn X.p0 (a : ℕ) : ℝ) : ℂ) * hermC τ.1 X.Gm v (col (mat x τ) a)) • col (mat x τ) a := by
  obtain ⟨c, hc⟩ := span_cols X hx τ v
  have hcoef : ∀ a, hermC τ.1 X.Gm v (col (mat x τ) a) = c a * ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) := by
    intro a
    conv_lhs => rw [hc]
    rw [hermC_sum_smul_left']
    simp only [ortho_h X ho τ, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  conv_lhs => rw [hc]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [hcoef, ← mul_assoc, mul_comm _ (c a), mul_assoc, sgn_mul_self, mul_one]

/- English proof (translation)
Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Both sides reduce to the same expression.

Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Reduce the equality to equality of the corresponding arguments. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem ppos_ortho {x : Frame X.Ψ r} (hx : x ∈ X.dom) (ho : X.IsOrtho x) (τ : X.Ψ) (v : Fin r → ℂ) :
    X.ppos x τ v = ∑ a : Fin X.p0, hermC τ.1 X.Gm v (col (mat x τ) (Fin.castLE X.p0_le a)) •
      col (mat x τ) (Fin.castLE X.p0_le a) := by
  have hg : X.gramPos x τ = 1 := by
    ext a b
    simp only [Data.gramPos, Matrix.submatrix_apply, ho τ, Matrix.diagonal_apply, Fin.castLE_inj,
      Matrix.one_apply]
    split_ifs with h
    · simp [sgn, Fin.coe_castLE, a.isLt]
    · rfl
  unfold Data.ppos
  rw [hg, Matrix.inv_eq_left_inv (mul_one (1 : Matrix (Fin X.p0) (Fin X.p0) ℂ))]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  simp [Matrix.one_apply]

end ReciprocityTheory.ChartRestriction.G.FD.OrthonormalPerpBasis
