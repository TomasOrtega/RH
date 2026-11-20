import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsReading

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DarbouxSymp

variable {D : D7}

/- English proof (translation)
Simplify using `only [cA, sigR, incA, inclR]`. Simplify using the standard rewrite rules. Both sides reduce to the same expression.
-/
theorem cA_incA_eq (a : D.host.E) : cA D (incA D a) = incA D (star a) := by
  simp only [cA, sigR, incA, inclR]
  simp
  rfl

/- English proof (translation)
The claim follows from `V.herm.eq (V.frame i) (V.frame j)`.
-/
theorem gram_star_eq (V : HSp D) (i j) : star (V.gram i j) = V.gram j i :=
  V.herm.eq (V.frame i) (V.frame j)

/- English proof (translation)
Introduce `h`. Take `⟨v, hv, h0⟩` from `Matrix.exists_mulVec_eq_zero_iff.2 h`. Apply `hv` to reduce the goal to its premises. Establish `: V.frame.equivFun.symm v = 0`. Apply `V.nondeg.2` to reduce the goal to its premises.

Introduce `x`. Establish `hx : x = ∑ i, V.frame.repr x i • V.frame i` using `(V.frame.sum_repr x).symm`. Rewrite using `[hx, map_sum, LinearMap.sum_apply]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Establish `h1 : ∑ j, V.gram i j * v j = 0` using `congr_fun h0 i`.

Establish `h2 : V.hT (V.frame i) (V.frame.equivFun.symm v) = ∑ j, V.gram i j * v j`. Rewrite using `[Module.Basis.equivFun_symm_apply, map_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, smul_eq_mul, mul_comm]`. Both sides reduce to the same expression.

Rewrite using `[LinearMap.map_smulₛₗ, LinearMap.smul_apply, h2, h1, smul_zero]`. Conclude with `V.frame.equivFun.symm.injective (this.trans (map_zero _).symm)`.
-/
theorem gram_det_ne_zero (V : HSp D) : V.gram.det ≠ 0 := by
  intro h
  obtain ⟨v, hv, h0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  apply hv
  have : V.frame.equivFun.symm v = 0 := by
    apply V.nondeg.2
    intro x
    have hx : x = ∑ i, V.frame.repr x i • V.frame i := (V.frame.sum_repr x).symm
    rw [hx, map_sum, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    have h1 : ∑ j, V.gram i j * v j = 0 := congr_fun h0 i
    have h2 : V.hT (V.frame i) (V.frame.equivFun.symm v) = ∑ j, V.gram i j * v j := by
      rw [Module.Basis.equivFun_symm_apply, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, smul_eq_mul, mul_comm]; rfl
    rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, h2, h1, smul_zero]
  exact V.frame.equivFun.symm.injective (this.trans (map_zero _).symm)

/- English proof (translation)
Rewrite using `[← Matrix.map_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (gram_det_ne_zero V))]`. Conclude with `Matrix.map_one _ (map_zero _) (map_one _)`.
-/
theorem gram_map_mul_inv (V : HSp D) :
    HMul.hMul (V.gram.map (incA D) : Matrix (Fin V.rank) (Fin V.rank) (AE D)) (V.gram⁻¹.map (incA D) : Matrix (Fin V.rank) (Fin V.rank) (AE D)) = 1 := by
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (gram_det_ne_zero V))]
  exact Matrix.map_one _ (map_zero _) (map_one _)

/- English proof (translation)
Unfold `hO`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun d _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hO_rearr (S T : HSp D) (X Y : WO S T) : hO S T X Y =
    ∑ b, ∑ c, ∑ d, cA D (Y c b) * incA D (T.gram c d) * ∑ a, X d a * incA D (S.gram⁻¹ a b) := by
  unfold hO
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

/- English proof (translation)
Establish `L1 : ∀ d b, ∑ a, (HMul.hMul (xᵀ.submatrix e₂.symm e₁.symm) (S.gram.map (incA D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D)) d a * incA D (S.gram⁻¹ a b) = x (e₁.symm b) (e₂.symm d)`. Introduce `d b`. Establish `h` using `congrFun (congrFun (show HMul.hMul (HMul.hMul (xᵀ.submatrix e₂.symm e₁.symm : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (S.gram.map (incA D) : Matrix (Fin S.rank) (Fin S.rank) (AE D))) (S.gram⁻¹.map (incA D) : Matrix (Fin S.rank) (Fin S.rank) (AE D)) = (xᵀ.submatrix e₂.symm e₁.sym …`. Rewrite using `[Matrix.mul_assoc, gram_map_mul_inv, Matrix.mul_one]) d) b`. Rewrite `h` using `[Matrix.mul_apply]`.

Simplify using `using h`. Establish `L2 : ∀ c b, cA D ((HMul.hMul (yᵀ.submatrix e₂.symm e₁.symm) (S.gram.map (incA D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D)) c b) = ∑ k, cA D (y (e₁.symm k) (e₂.symm c)) * incA D (S.gram b k)`. Introduce `c b`. Rewrite using `[Matrix.mul_apply, map_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[map_mul, Matrix.map_apply, cA_incA_eq, gram_star_eq]`. Both sides reduce to the same expression. Establish `E1 : ∀ a b, S'.gram⁻¹ a b = -T.gram (e₂ b) (e₂ a)` using `fun a b => by`. Rewrite using `[hS']`. Both sides reduce to the same expression.

Establish `E2 : ∀ c d, T'.gram c d = -S.gram (e₁ d) (e₁ c)` using `fun c d => by`. Use `congrFun (congrFun hT' d) c` as an intermediate fact. Simplify using `using this`. Rewrite using `[hO_rearr]`. Repeatedly rewrite using `[L1, L2]`.

Unfold `hO`. Repeatedly rewrite using `[E1, E2]`. Establish `hR : ∀ F : Fin S.rank → Fin T.rank → Fin T.rank → Fin S.rank → AE D, (∀ a b c d, incA D (-T.gram (e₂ b) (e₂ a)) * cA D (y c b) * incA D (-S.gram (e₁ d) (e₁ c)) * x d a = F (e₁ d) (e₂ b) (e₂ a) (e₁ c)) → ∑ a, ∑ b, ∑ c, ∑ d, incA D (-T.gram (e₂ b) (e₂ a)) * cA D (y c b) * incA D (- …`. Introduce `F hF`. Use `Fintype.sum_equiv e₂ _ _ fun a => ?_` and prove the remaining obligations.

Use `Fintype.sum_equiv e₂ _ _ fun b => ?_` and prove the remaining obligations. Use `Fintype.sum_equiv e₁ _ _ fun c => ?_` and prove the remaining obligations. Use `Fintype.sum_equiv e₁ _ _ fun d => ?_` and prove the remaining obligations. Conclude with `hF a b c d`. Rewrite using `[hR (fun b c d k => cA D (y (e₁.symm k) (e₂.symm c)) * incA D (S.gram b k) * incA D (T.gram c d) * x (e₁.symm b) (e₂.symm d)) (fun a b c d => by simp only [Equiv.symm_apply_apply, map_neg]; ring)]`.

Simplify using `only [Finset.sum_mul]`. Use `conv_lhs => rw [Finset.sum_comm]`. Use `conv_lhs => enter [2, c]`. Rewrite using `[Finset.sum_comm]`. Use `conv_lhs => enter [2, c, 2, d]`.

Rewrite using `[Finset.sum_comm]`. Use `conv_lhs => rw [Finset.sum_comm]`.
-/
theorem hO_darboux (S T S' T' : HSp D) (e₁ : Fin T'.rank ≃ Fin S.rank) (e₂ : Fin S'.rank ≃ Fin T.rank)
    (hT' : T'.gramᵀ = -(S.gram.submatrix e₁ e₁)) (hS' : S'.gram⁻¹ = -(T.gramᵀ.submatrix e₂ e₂)) (x y : WO S' T') :
    hO S T (HMul.hMul (xᵀ.submatrix e₂.symm e₁.symm) (S.gram.map (incA D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D))
      (HMul.hMul (yᵀ.submatrix e₂.symm e₁.symm) (S.gram.map (incA D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D)) =
    hO S' T' x y := by
  have L1 : ∀ d b, ∑ a, (HMul.hMul (xᵀ.submatrix e₂.symm e₁.symm) (S.gram.map (incA D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D)) d a
      * incA D (S.gram⁻¹ a b) = x (e₁.symm b) (e₂.symm d) := by
    intro d b
    have h := congrFun (congrFun (show HMul.hMul (HMul.hMul (xᵀ.submatrix e₂.symm e₁.symm : Matrix (Fin T.rank) (Fin S.rank) (AE D))
      (S.gram.map (incA D) : Matrix (Fin S.rank) (Fin S.rank) (AE D))) (S.gram⁻¹.map (incA D) : Matrix (Fin S.rank) (Fin S.rank) (AE D))
      = (xᵀ.submatrix e₂.symm e₁.symm : Matrix (Fin T.rank) (Fin S.rank) (AE D)) by
        rw [Matrix.mul_assoc, gram_map_mul_inv, Matrix.mul_one]) d) b
    rw [Matrix.mul_apply] at h
    simpa using h
  have L2 : ∀ c b, cA D ((HMul.hMul (yᵀ.submatrix e₂.symm e₁.symm) (S.gram.map (incA D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D)) c b)
      = ∑ k, cA D (y (e₁.symm k) (e₂.symm c)) * incA D (S.gram b k) := by
    intro c b
    rw [Matrix.mul_apply, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, Matrix.map_apply, cA_incA_eq, gram_star_eq]
    rfl
  have E1 : ∀ a b, S'.gram⁻¹ a b = -T.gram (e₂ b) (e₂ a) := fun a b => by
    rw [hS']; rfl
  have E2 : ∀ c d, T'.gram c d = -S.gram (e₁ d) (e₁ c) := fun c d => by
    have := congrFun (congrFun hT' d) c
    simpa using this
  rw [hO_rearr]
  simp_rw [L1, L2]
  unfold hO
  simp_rw [E1, E2]
  have hR : ∀ F : Fin S.rank → Fin T.rank → Fin T.rank → Fin S.rank → AE D,
      (∀ a b c d, incA D (-T.gram (e₂ b) (e₂ a)) * cA D (y c b) * incA D (-S.gram (e₁ d) (e₁ c)) * x d a
        = F (e₁ d) (e₂ b) (e₂ a) (e₁ c)) →
      ∑ a, ∑ b, ∑ c, ∑ d, incA D (-T.gram (e₂ b) (e₂ a)) * cA D (y c b) * incA D (-S.gram (e₁ d) (e₁ c)) * x d a
        = ∑ d, ∑ c, ∑ k, ∑ b, F b c d k := by
    intro F hF
    refine Fintype.sum_equiv e₂ _ _ fun a => ?_
    refine Fintype.sum_equiv e₂ _ _ fun b => ?_
    refine Fintype.sum_equiv e₁ _ _ fun c => ?_
    refine Fintype.sum_equiv e₁ _ _ fun d => ?_
    exact hF a b c d
  rw [hR (fun b c d k => cA D (y (e₁.symm k) (e₂.symm c)) * incA D (S.gram b k) * incA D (T.gram c d) * x (e₁.symm b) (e₂.symm d))
    (fun a b c d => by simp only [Equiv.symm_apply_apply, map_neg]; ring)]
  simp only [Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => enter [2, c]; rw [Finset.sum_comm]
  conv_lhs => enter [2, c, 2, d]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]

/- English proof (translation)
Introduce `D S T S' T' e₁ e₂ hT' hS' x y`. Unfold `symplO`. Rewrite using `[hO_darboux S T S' T' e₁ e₂ hT' hS' x y]`.
-/
theorem symplO_darboux : ∀ (D : D7) (S T S' T' : HSp D) (e₁ : Fin T'.rank ≃ Fin S.rank) (e₂ : Fin S'.rank ≃ Fin T.rank),
    T'.gramᵀ = -(S.gram.submatrix e₁ e₁) → S'.gram⁻¹ = -(T.gramᵀ.submatrix e₂ e₂) → ∀ x y : WO S' T',
      symplO S T (HMul.hMul (xᵀ.submatrix e₂.symm e₁.symm) (S.gram.map (incA D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D))
        (HMul.hMul (yᵀ.submatrix e₂.symm e₁.symm) (S.gram.map (incA D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D)) =
      symplO S' T' x y := by
  intro D S T S' T' e₁ e₂ hT' hS' x y
  unfold symplO
  rw [hO_darboux S T S' T' e₁ e₂ hT' hS' x y]

end GlobalTheory.DarbouxSymp
