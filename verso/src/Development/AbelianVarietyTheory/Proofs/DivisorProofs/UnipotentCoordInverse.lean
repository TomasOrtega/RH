import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoC
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentCoordinateAdditive
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.UnipDom
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThK.UnipDom.PlaneInv

open GlobalTheory.ThK.UnipDom.Additive

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
Proceed by induction on `a using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul x y => simp [cA, hσ]`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy]`.
-/
theorem cA_cA (hσ : ∀ x, σ (σ x) = x) (a : AE F E) : cA σ (cA σ a) = a := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [cA, hσ]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/- English proof (translation)
Establish `hu : (mat u)ᵀ * incM F J * (mat u).map (cA σ) = incM F J` using `u.2`. Establish `h1 : (fun i => cA σ ((mat u *ᵥ w) i)) = (mat u).map (cA σ) *ᵥ fun i => cA σ (w i)`. Use function extensionality and compare the values at `i`. Simplify using `[Matrix.mulVec, dotProduct, map_sum, map_mul]`. Unfold `fA`.

Rewrite using `[h1, Matrix.mulVec_mulVec, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hu]`.
-/
theorem fA_mat {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (u : UA σ J) (v w : Fin n → AE F E) :
    fA σ J (mat u *ᵥ v) (mat u *ᵥ w) = fA σ J v w := by
  have hu : (mat u)ᵀ * incM F J * (mat u).map (cA σ) = incM F J := u.2
  have h1 : (fun i => cA σ ((mat u *ᵥ w) i)) = (mat u).map (cA σ) *ᵥ fun i => cA σ (w i) := by
    funext i
    simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
  unfold fA
  rw [h1, Matrix.mulVec_mulVec, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    ← Matrix.mul_assoc, hu]

/- English proof (translation)
Simplify using `only [fA, dotProduct, Matrix.mulVec, incM, Matrix.map_apply, map_sum, map_mul, cA_cA hσ, cA_inclR, hJ, map_neg, Finset.mul_sum, ← Finset.sum_neg_distrib]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fA_skew (hσ : ∀ x, σ (σ x) = x) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : ∀ i j, σ (J j i) = -J i j)
    (v w : Fin n → AE F E) : fA σ J v w = -cA σ (fA σ J w v) := by
  simp only [fA, dotProduct, Matrix.mulVec, incM, Matrix.map_apply, map_sum, map_mul, cA_cA hσ, cA_inclR, hJ, map_neg,
    Finset.mul_sum, ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n n₁ Y Y₁ H hCM hJ hP u hu`. Take `⟨-, -, -, hxy, horth, -⟩` from `hP`. Establish `hσ : ∀ x, σ (σ x) = x` using `fun x => by`. Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Apply `τ.injective` to reduce the goal to its premises.

Rewrite using `[hCM.2.2.2, hCM.2.2.2, star_star]`. Establish `h1 : ∀ w, mat u⁻¹ *ᵥ (mat u *ᵥ w) = w` using `fun w => by`. Rewrite using `[Matrix.mulVec_mulVec, mat_inv_mul', Matrix.one_mulVec]`. Prove the components needed by the constructor for the conclusion. Use function extensionality and compare the values at `j set e : Fin n → AE F E := incM F H.ι *ᵥ Pi.single j 1 with he`.

Establish `hval : ∀ c : AE F E, fA σ Y.J (e + c • incV F H.x) (incV F H.y) = c`. Introduce `c`. Rewrite using `[fA_add_left, fA_smul_left, fA_incV, hxy, map_one, mul_one, he, single_eq_incV, incM_mulVec_incV, fA_incV, (horth _).2, map_zero, zero_add]`. Take `⟨a, ha⟩` from `(unip_spec hu).2 (Pi.single j 1)`. Establish `hx1` using `(unip_spec (inv_mem hu)).1`.

Establish `h2` using `h1 e`. Rewrite `h2` using `[he, ha, Matrix.mulVec_add, Matrix.mulVec_smul, hx1, ← he]`. Establish `h3 : mat u⁻¹ *ᵥ e = e + (-a) • incV F H.x`. Rewrite using `[neg_smul]`. Conclude with `eq_add_neg_of_add_eq h2`.

Simplify using `only [Pi.neg_apply, coA]`. Rewrite using `[ha, ← he, h3, hval, hval]`. Unfold `coC`. Rewrite using `[← fA_skew hσ hJ, ← fA_mat u⁻¹ (incV F H.y) (mat u *ᵥ incV F H.y), h1]`.
-/
theorem coA_coC_inv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n n₁ : ℕ) (Y : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁), IsCMExt F E σ → (∀ i j, σ (Y.J j i) = -Y.J i j) → IsIsoPlane σ B H Y Y₁ → ∀ u ∈ unip σ Y H, coA σ Y.J H u⁻¹ = -coA σ Y.J H u ∧ coC σ Y.J H u⁻¹ = -cA σ (coC σ Y.J H u) := by
  intro F E _ _ _ _ _ σ B n n₁ Y Y₁ H hCM hJ hP u hu
  obtain ⟨-, -, -, hxy, horth, -⟩ := hP
  have hσ : ∀ x, σ (σ x) = x := fun x => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hCM.2.2.2, hCM.2.2.2, star_star]
  have h1 : ∀ w, mat u⁻¹ *ᵥ (mat u *ᵥ w) = w := fun w => by
    rw [Matrix.mulVec_mulVec, mat_inv_mul', Matrix.one_mulVec]
  constructor
  · funext j
    set e : Fin n → AE F E := incM F H.ι *ᵥ Pi.single j 1 with he
    have hval : ∀ c : AE F E, fA σ Y.J (e + c • incV F H.x) (incV F H.y) = c := by
      intro c
      rw [fA_add_left, fA_smul_left, fA_incV, hxy, map_one, mul_one, he, single_eq_incV,
        incM_mulVec_incV, fA_incV, (horth _).2, map_zero, zero_add]
    obtain ⟨a, ha⟩ := (unip_spec hu).2 (Pi.single j 1)
    have hx1 := (unip_spec (inv_mem hu)).1
    have h2 := h1 e
    rw [he, ha, Matrix.mulVec_add, Matrix.mulVec_smul, hx1, ← he] at h2
    have h3 : mat u⁻¹ *ᵥ e = e + (-a) • incV F H.x := by
      rw [neg_smul]; exact eq_add_neg_of_add_eq h2
    simp only [Pi.neg_apply, coA]
    rw [ha, ← he, h3, hval, hval]
  · unfold coC
    rw [← fA_skew hσ hJ, ← fA_mat u⁻¹ (incV F H.y) (mat u *ᵥ incV F H.y), h1]

end GlobalTheory.ThK.UnipDom.PlaneInv

end
