import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicLeviEmbeddingHomomorphismProperties
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicStabilizerRadicalStructure
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MajorantFlagLengthsInvarianceTorusPositivity
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GramSchmidtLengths
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalFormFlagZeroMiddleInverseMinorOrthogonal
import Formalism.FlagUnipotentLattices.CardSubgroupsOfIndexLe
import Formalism.FormalDegreeBessel.FinalG

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.RadBound

open GlobalTheory.Amp.GramFlag (eucl_eq)

/- English proof (translation)
Unfold `eucl`. Apply `Real.sqrt_le_sqrt` to reduce the goal to its premises. Rewrite using `[← Finset.sum_image (f := fun i => Complex.normSq (v i)) (fun a _ b _ h => hf h)]`. Conclude with `Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => Complex.normSq_nonneg _)`.
-/
theorem eucl_comp_le {n N : ℕ} (f : Fin n → Fin N) (hf : Function.Injective f) (v : Fin N → ℂ) :
    eucl (fun j => v (f j)) ≤ eucl v := by
  unfold eucl
  apply Real.sqrt_le_sqrt
  rw [← Finset.sum_image (f := fun i => Complex.normSq (v i)) (fun a _ b _ h => hf h)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun i _ _ => Complex.normSq_nonneg _)

/- English proof (translation)
Unfold `eucl`. Simplify using `[Complex.normSq_neg]`.
-/
theorem eucl_neg {N : ℕ} (v : Fin N → ℂ) : eucl (-v) = eucl v := by
  unfold eucl
  simp [Complex.normSq_neg]

/- English proof (translation)
Establish `key : eucl (∑ a, c a • v a) ≤ ∑ a, ‖c a‖ * eucl (v a)`. Rewrite using `[eucl_eq]`. Establish `e : (WithLp.toLp 2 (∑ a, c a • v a) : EuclideanSpace ℂ (Fin N)) = ∑ a, c a • (WithLp.toLp 2 (v a) : EuclideanSpace ℂ (Fin N))`. Use extensionality with `i`. Simplify using `[Finset.sum_apply]`.

Rewrite using `[e]`. Use `(norm_sum_le _ _).trans (le_of_eq ?_)` and prove the remaining obligations. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[norm_smul, eucl_eq]`. Use `key.trans ?_` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem eucl_sum_le {n N : ℕ} (c : Fin n → ℂ) (v : Fin n → Fin N → ℂ) (C R : ℝ) (hc : ∀ a, ‖c a‖ ≤ C)
    (hv : ∀ a, eucl (v a) ≤ R) : eucl (∑ a, c a • v a) ≤ n * (C * R) := by
  have key : eucl (∑ a, c a • v a) ≤ ∑ a, ‖c a‖ * eucl (v a) := by
    rw [eucl_eq]
    have e : (WithLp.toLp 2 (∑ a, c a • v a) : EuclideanSpace ℂ (Fin N)) =
        ∑ a, c a • (WithLp.toLp 2 (v a) : EuclideanSpace ℂ (Fin N)) := by
      ext i
      simp [Finset.sum_apply]
    rw [e]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [norm_smul, eucl_eq]
  refine key.trans ?_
  calc ∑ a, ‖c a‖ * eucl (v a) ≤ ∑ _a : Fin n, C * R :=
        Finset.sum_le_sum fun a _ =>
          mul_le_mul (hc a) (hv a) (Real.sqrt_nonneg _) ((norm_nonneg _).trans (hc a))
    _ = n * (C * R) := by simp

/- English proof (translation)
Set `f : Fin j → EuclideanSpace ℂ (Fin j)` to `fun i => WithLp.toLp 2 (fun d => A d i)`. Establish `h : Module.finrank ℂ (EuclideanSpace ℂ (Fin j)) = Fintype.card (Fin j)` using `by simp`. Set `B` to `InnerProductSpace.gramSchmidtOrthonormalBasis h f`. Set `S` to `EuclideanSpace.basisFun (Fin j) ℂ`. Establish `hS : S.toBasis.det f = A.det`.

Rewrite using `[Module.Basis.det_apply]`. Use `congr 1`. Establish `hmul : S.toBasis.det f = S.toBasis.det B * B.toBasis.det f`. Establish `e` using `AlternatingMap.eq_smul_basis_det B.toBasis S.toBasis.det`. Use `congrArg (fun F : EuclideanSpace ℂ (Fin j) [⋀^Fin j]→ₗ[ℂ] ℂ => F f) e` as an intermediate fact.

Simplify `this` using `[OrthonormalBasis.coe_toBasis]`. Rewrite using `[← hS, hmul, norm_mul, S.det_to_matrix_orthonormalBasis B, one_mul, InnerProductSpace.gramSchmidtOrthonormalBasis_det, norm_prod]`. Use `Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem hadamard_lemma' {j : ℕ} (A : Matrix (Fin j) (Fin j) ℂ) :
    ‖A.det‖ ≤ ∏ i, eucl (fun d => A d i) := by
  classical
  let f : Fin j → EuclideanSpace ℂ (Fin j) := fun i => WithLp.toLp 2 (fun d => A d i)
  have h : Module.finrank ℂ (EuclideanSpace ℂ (Fin j)) = Fintype.card (Fin j) := by simp
  let B := InnerProductSpace.gramSchmidtOrthonormalBasis h f
  let S := EuclideanSpace.basisFun (Fin j) ℂ
  have hS : S.toBasis.det f = A.det := by
    rw [Module.Basis.det_apply]
    congr 1
  have hmul : S.toBasis.det f = S.toBasis.det B * B.toBasis.det f := by
    have e := AlternatingMap.eq_smul_basis_det B.toBasis S.toBasis.det
    have := congrArg (fun F : EuclideanSpace ℂ (Fin j) [⋀^Fin j]→ₗ[ℂ] ℂ => F f) e
    simpa [OrthonormalBasis.coe_toBasis] using this
  rw [← hS, hmul, norm_mul, S.det_to_matrix_orthonormalBasis B, one_mul,
    InnerProductSpace.gramSchmidtOrthonormalBasis_det, norm_prod]
  refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => ?_
  calc ‖inner ℂ (B i) (f i)‖ ≤ ‖B i‖ * ‖f i‖ := norm_inner_le_norm _ _
    _ = ‖f i‖ := by rw [B.orthonormal.1 i, one_mul]
    _ = eucl (fun d => A d i) := (eucl_eq _).symm

/- English proof (translation)
Distinguish the cases in `hf : Function.Injective f`. Establish `hA : (N.submatrix f g).det * ∏ i, ((a (f i) : ℂ)) = (Matrix.of fun i' i => (a (f i') : ℂ) * N (f i') (g i)).det`. Establish `e : (Matrix.of fun i' i => (a (f i') : ℂ) * N (f i') (g i)) = Matrix.diagonal (fun i => (a (f i) : ℂ)) * N.submatrix f g`. Use extensionality with `i' i`. Simplify using `[Matrix.diagonal_mul]`.

Rewrite using `[e, Matrix.det_mul, Matrix.det_diagonal, mul_comm]`. Establish `h1` using `hadamard_lemma' (Matrix.of fun i' i => (a (f i') : ℂ) * N (f i') (g i))`. Rewrite `h1` using `[← hA, norm_mul, norm_prod]`. Establish `h2 : ∏ i, eucl (fun d => (Matrix.of fun i' i => (a (f i') : ℂ) * N (f i') (g i)) d i) ≤ ∏ i, eucl (fun d => (a d : ℂ) * N d (g i))` using `Finset.prod_le_prod (fun i _ => Real.sqrt_nonneg _) (fun i _ => eucl_comp_le f hf (fun d => (a d : ℂ) * N d (g i)))`. Establish `hprod : ∏ i, ‖((a (f i) : ℂ))‖ = ∏ i, a (f i)` using `Finset.prod_congr rfl fun i _ => by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (ha _)]`.

Establish `hpos : 0 < ∏ i, a (f i)` using `Finset.prod_pos fun i _ => ha (f i)`. Rewrite `h1` using `[hprod]`. Rewrite using `[Finset.prod_inv_distrib, ← div_eq_mul_inv, le_div_iff₀ hpos]`. Conclude with `h1.trans h2`. Choose the witnesses or unpack the hypotheses as in `⟨i, i', hne, heq⟩ : ∃ i i', i ≠ i' ∧ f i = f i' := by`.

Simplify using `only [Function.Injective, not_forall] at hf`. Take `⟨i, i', h, hne⟩` from `hf`. Conclude with `⟨i, i', hne, h⟩`. Rewrite using `[Matrix.det_zero_of_row_eq hne (by funext c; simp [heq]), norm_zero]`. Conclude with `mul_nonneg (Finset.prod_nonneg fun _ _ => Real.sqrt_nonneg _) (Finset.prod_nonneg fun i _ => (inv_pos.2 (ha _)).le)`.
-/
theorem minor_le {r j : ℕ} (N : Matrix (Fin r) (Fin r) ℂ) (a : Fin r → ℝ) (ha : ∀ b, 0 < a b)
    (f g : Fin j → Fin r) :
    ‖(N.submatrix f g).det‖ ≤ (∏ i, eucl (fun d => (a d : ℂ) * N d (g i))) * ∏ i, (a (f i))⁻¹ := by
  classical
  by_cases hf : Function.Injective f
  · have hA : (N.submatrix f g).det * ∏ i, ((a (f i) : ℂ)) =
        (Matrix.of fun i' i => (a (f i') : ℂ) * N (f i') (g i)).det := by
      have e : (Matrix.of fun i' i => (a (f i') : ℂ) * N (f i') (g i)) =
          Matrix.diagonal (fun i => (a (f i) : ℂ)) * N.submatrix f g := by
        ext i' i
        simp [Matrix.diagonal_mul]
      rw [e, Matrix.det_mul, Matrix.det_diagonal, mul_comm]
    have h1 := hadamard_lemma' (Matrix.of fun i' i => (a (f i') : ℂ) * N (f i') (g i))
    rw [← hA, norm_mul, norm_prod] at h1
    have h2 : ∏ i, eucl (fun d => (Matrix.of fun i' i => (a (f i') : ℂ) * N (f i') (g i)) d i) ≤
        ∏ i, eucl (fun d => (a d : ℂ) * N d (g i)) :=
      Finset.prod_le_prod (fun i _ => Real.sqrt_nonneg _)
        (fun i _ => eucl_comp_le f hf (fun d => (a d : ℂ) * N d (g i)))
    have hprod : ∏ i, ‖((a (f i) : ℂ))‖ = ∏ i, a (f i) :=
      Finset.prod_congr rfl fun i _ => by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (ha _)]
    have hpos : 0 < ∏ i, a (f i) := Finset.prod_pos fun i _ => ha (f i)
    rw [hprod] at h1
    rw [Finset.prod_inv_distrib, ← div_eq_mul_inv, le_div_iff₀ hpos]
    exact h1.trans h2
  · obtain ⟨i, i', hne, heq⟩ : ∃ i i', i ≠ i' ∧ f i = f i' := by
      simp only [Function.Injective, not_forall] at hf
      obtain ⟨i, i', h, hne⟩ := hf
      exact ⟨i, i', hne, h⟩
    rw [Matrix.det_zero_of_row_eq hne (by funext c; simp [heq]), norm_zero]
    exact mul_nonneg (Finset.prod_nonneg fun _ _ => Real.sqrt_nonneg _)
      (Finset.prod_nonneg fun i _ => (inv_pos.2 (ha _)).le)

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation.
-/
theorem prod_le_pow' {n : ℕ} (f : Fin n → ℝ) (R : ℝ) (h0 : ∀ i, 0 ≤ f i) (h : ∀ i, f i ≤ R) :
    ∏ i, f i ≤ R ^ n := by
  calc ∏ i, f i ≤ ∏ _i : Fin n, R := Finset.prod_le_prod (fun i _ => h0 i) (fun i _ => h i)
    _ = R ^ n := by simp

/- English proof (translation)
Consider the cases of `r with`. Consider the case `zero => exact ⟨fun i => i.elim0, fun c => c.elim0⟩`. Consider the case `succ n`. Establish `hdet0 : 0 < ‖N.det‖` using `norm_pos_iff.2 hdet`. Establish `hR0 : 0 ≤ R` using `by linarith`.

Establish `hcol : ∀ b, 0 ≤ eucl (fun d => (a d : ℂ) * N d b)` using `fun b => Real.sqrt_nonneg _`. Establish `hainv0 : ∀ b, 0 ≤ (a b)⁻¹` using `fun b => (inv_pos.2 (ha b)).le`. Prove the components needed by the constructor for the conclusion. Introduce `i j`. Establish `hadj : ‖N.adjugate i j‖ ≤ R ^ (2 * (n + 1) - 2)`.

Rewrite using `[Matrix.adjugate_fin_succ_eq_det_submatrix, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]`. Use `(minor_le N a ha j.succAbove i.succAbove).trans ?_` and prove the remaining obligations. Establish `e : 2 * (n + 1) - 2 = n + n` using `by omega`. Rewrite using `[e, pow_add]`. Conclude with `mul_le_mul (prod_le_pow' _ R (fun _ => hcol _) (fun _ => hN _)) (prod_le_pow' _ R (fun _ => hainv0 _) (fun _ => hal _)) (Finset.prod_nonneg fun _ _ => hainv0 _) (pow_nonneg hR0 _)`.

Rewrite using `[Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, norm_mul, Ring.inverse_eq_inv, norm_inv, mul_comm]`. Conclude with `mul_le_mul hadj hDe (inv_nonneg.2 (norm_nonneg _)) (pow_nonneg hR0 _)`. Introduce `c`. Establish `h1` using `minor_le N a ha (id : Fin (n + 1) → Fin (n + 1)) id`. Rewrite `h1` using `[Matrix.submatrix_id_id]`.

Establish `hprodcol : (∏ i, eucl (fun d => (a d : ℂ) * N d (id i))) ≤ R ^ (n + 1)` using `prod_le_pow' _ R (fun _ => hcol _) (fun _ => hN _)`. Rewrite `h1` using `[← Finset.mul_prod_erase Finset.univ (fun i => (a (id i))⁻¹) (Finset.mem_univ c)]`. Establish `hrest : ∏ i ∈ Finset.univ.erase c, (a (id i))⁻¹ ≤ R ^ n`. Combine the equalities or inequalities in the displayed calculation. Establish `hrest0 : 0 ≤ ∏ i ∈ Finset.univ.erase c, (a (id i))⁻¹` using `Finset.prod_nonneg fun _ _ => hainv0 _`.

Establish `h2 : ‖N.det‖ ≤ R ^ (n + 1) * ((a c)⁻¹ * R ^ n)` using `h1.trans (mul_le_mul hprodcol (mul_le_mul_of_nonneg_left hrest (hainv0 c)) (mul_nonneg (hainv0 c) hrest0) (pow_nonneg hR0 _))`. Establish `hac` using `ha c`. Establish `e : 2 * (n + 1) - 1 = (n + 1) + n` using `by omega`. Rewrite using `[e, pow_add]`. Establish `h3 : a c * ‖N.det‖ ≤ R ^ (n + 1) * R ^ n`.

Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation.
-/
theorem inv_bound {r : ℕ} (N : Matrix (Fin r) (Fin r) ℂ) (a : Fin r → ℝ) (ha : ∀ b, 0 < a b) (R De : ℝ)
    (hR : 1 ≤ R) (hal : ∀ b, (a b)⁻¹ ≤ R) (hN : ∀ b, eucl (fun d => (a d : ℂ) * N d b) ≤ R)
    (hdet : N.det ≠ 0) (hDe : ‖N.det‖⁻¹ ≤ De) :
    (∀ i j, ‖N⁻¹ i j‖ ≤ R ^ (2 * r - 2) * De) ∧ ∀ c, a c ≤ R ^ (2 * r - 1) * De := by
  cases r with
  | zero => exact ⟨fun i => i.elim0, fun c => c.elim0⟩
  | succ n =>
  have hdet0 : 0 < ‖N.det‖ := norm_pos_iff.2 hdet
  have hR0 : 0 ≤ R := by linarith
  have hcol : ∀ b, 0 ≤ eucl (fun d => (a d : ℂ) * N d b) := fun b => Real.sqrt_nonneg _
  have hainv0 : ∀ b, 0 ≤ (a b)⁻¹ := fun b => (inv_pos.2 (ha b)).le
  constructor
  · intro i j
    have hadj : ‖N.adjugate i j‖ ≤ R ^ (2 * (n + 1) - 2) := by
      rw [Matrix.adjugate_fin_succ_eq_det_submatrix, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
        one_mul]
      refine (minor_le N a ha j.succAbove i.succAbove).trans ?_
      have e : 2 * (n + 1) - 2 = n + n := by omega
      rw [e, pow_add]
      exact mul_le_mul (prod_le_pow' _ R (fun _ => hcol _) (fun _ => hN _))
        (prod_le_pow' _ R (fun _ => hainv0 _) (fun _ => hal _))
        (Finset.prod_nonneg fun _ _ => hainv0 _) (pow_nonneg hR0 _)
    rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, norm_mul, Ring.inverse_eq_inv, norm_inv, mul_comm]
    exact mul_le_mul hadj hDe (inv_nonneg.2 (norm_nonneg _)) (pow_nonneg hR0 _)
  · intro c
    have h1 := minor_le N a ha (id : Fin (n + 1) → Fin (n + 1)) id
    rw [Matrix.submatrix_id_id] at h1
    have hprodcol : (∏ i, eucl (fun d => (a d : ℂ) * N d (id i))) ≤ R ^ (n + 1) :=
      prod_le_pow' _ R (fun _ => hcol _) (fun _ => hN _)
    rw [← Finset.mul_prod_erase Finset.univ (fun i => (a (id i))⁻¹) (Finset.mem_univ c)] at h1
    have hrest : ∏ i ∈ Finset.univ.erase c, (a (id i))⁻¹ ≤ R ^ n := by
      calc ∏ i ∈ Finset.univ.erase c, (a (id i))⁻¹ ≤ ∏ _i ∈ Finset.univ.erase c, R :=
            Finset.prod_le_prod (fun _ _ => hainv0 _) (fun _ _ => hal _)
        _ = R ^ n := by rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _)]; simp
    have hrest0 : 0 ≤ ∏ i ∈ Finset.univ.erase c, (a (id i))⁻¹ :=
      Finset.prod_nonneg fun _ _ => hainv0 _
    have h2 : ‖N.det‖ ≤ R ^ (n + 1) * ((a c)⁻¹ * R ^ n) :=
      h1.trans (mul_le_mul hprodcol (mul_le_mul_of_nonneg_left hrest (hainv0 c))
        (mul_nonneg (hainv0 c) hrest0) (pow_nonneg hR0 _))
    have hac := ha c
    have e : 2 * (n + 1) - 1 = (n + 1) + n := by omega
    rw [e, pow_add]
    have h3 : a c * ‖N.det‖ ≤ R ^ (n + 1) * R ^ n := by
      calc a c * ‖N.det‖ ≤ a c * (R ^ (n + 1) * ((a c)⁻¹ * R ^ n)) :=
            mul_le_mul_of_nonneg_left h2 hac.le
        _ = R ^ (n + 1) * R ^ n := by field_simp
    calc a c = a c * ‖N.det‖ * ‖N.det‖⁻¹ := by field_simp
      _ ≤ R ^ (n + 1) * R ^ n * De :=
          mul_le_mul h3 hDe (inv_nonneg.2 (norm_nonneg _)) (by positivity)

variable {k r : ℕ}

/- English proof (translation)
Use `Matrix.inv_eq_left_inv ?_` and prove the remaining obligations. Rewrite using `[Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`. Use extensionality with `b`. Conclude with `inv_mul_cancel₀ (ha b)`.
-/
theorem diag_inv (a : Fin r → ℂ) (ha : ∀ b, a b ≠ 0) :
    (Matrix.diagonal a)⁻¹ = Matrix.diagonal fun b => (a b)⁻¹ := by
  refine Matrix.inv_eq_left_inv ?_
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  ext b
  exact inv_mul_cancel₀ (ha b)

section
open GlobalTheory.Amp.Rad

/- English proof (translation)
Simplify using `only [Matrix.mulVec, dotProduct, m_e]`. Simplify using the standard rewrite rules.
-/
theorem mE_e (m : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (v : Fin (2 * r + k + 1) → ℂ) (c : Fin r) :
    (mEmb k r m *ᵥ v) (eI k r c) = v (eI k r c) := by
  simp only [Matrix.mulVec, dotProduct, m_e]
  simp

/- English proof (translation)
Simplify using `only [Matrix.mulVec, dotProduct, middleSpaceLeviEmbedding_apply_es_row]`. Simplify using the standard rewrite rules.
-/
theorem middleSpaceLeviEmbedding_mulVec_dual_isotropic_coord (m : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (v : Fin (2 * r + k + 1) → ℂ) (c : Fin r) :
    (mEmb k r m *ᵥ v) (esI k r c) = v (esI k r c) := by
  simp only [Matrix.mulVec, dotProduct, middleSpaceLeviEmbedding_apply_es_row]
  simp

/- English proof (translation)
Simplify using `only [Matrix.mulVec, dotProduct]`. Rewrite using `[sum3 (k := k) (r := r)]`. Simplify using `[m_we, m_ws, m_ww]`.
-/
theorem mE_w (m : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (v : Fin (2 * r + k + 1) → ℂ) (j : Fin (k + 1)) :
    (mEmb k r m *ᵥ v) (wI k r j) = (m *ᵥ fun i => v (wI k r i)) j := by
  simp only [Matrix.mulVec, dotProduct]
  rw [sum3 (k := k) (r := r)]
  simp [m_we, m_ws, m_ww]

/- English proof (translation)
Simplify using `only [Matrix.mulVec, dotProduct]`. Rewrite using `[UEmb.sum_idx (k := k) (r := r)]`. Simplify using `[UEmb.u_ee, UEmb.u_em, UEmb.u_es]`.
-/
theorem uE_e (u : Matrix (Fin r) (Fin r) ℂ) (v : Fin (2 * r + k + 1) → ℂ) (c : Fin r) :
    (uEmb k r u *ᵥ v) (eI k r c) = ∑ b, u c b * v (eI k r b) := by
  simp only [Matrix.mulVec, dotProduct]
  rw [UEmb.sum_idx (k := k) (r := r)]
  simp [UEmb.u_ee, UEmb.u_em, UEmb.u_es]

/- English proof (translation)
Simplify using `only [Matrix.mulVec, dotProduct]`. Rewrite using `[UEmb.sum_idx (k := k) (r := r)]`. Simplify using `[UEmb.u_se, UEmb.u_sm, UEmb.u_ss]`.
-/
theorem isotropicLeviEmbedding_mulVec_dual_isotropic_coord (u : Matrix (Fin r) (Fin r) ℂ) (v : Fin (2 * r + k + 1) → ℂ) (c : Fin r) :
    (uEmb k r u *ᵥ v) (esI k r c) = ∑ b, star (u⁻¹ b c) * v (esI k r b) := by
  simp only [Matrix.mulVec, dotProduct]
  rw [UEmb.sum_idx (k := k) (r := r)]
  simp [UEmb.u_se, UEmb.u_sm, UEmb.u_ss]

/- English proof (translation)
Establish `hw : wI k r j = UEmb.mI k r j` using `Fin.ext rfl`. Simplify using `only [Matrix.mulVec, dotProduct]`. Rewrite using `[UEmb.sum_idx (k := k) (r := r), hw]`. Simplify using `[UEmb.u_me, UEmb.u_mm, UEmb.u_ms]`.
-/
theorem uE_w (u : Matrix (Fin r) (Fin r) ℂ) (v : Fin (2 * r + k + 1) → ℂ) (j : Fin (k + 1)) :
    (uEmb k r u *ᵥ v) (wI k r j) = v (wI k r j) := by
  have hw : wI k r j = UEmb.mI k r j := Fin.ext rfl
  simp only [Matrix.mulVec, dotProduct]
  rw [UEmb.sum_idx (k := k) (r := r), hw]
  simp [UEmb.u_me, UEmb.u_mm, UEmb.u_ms]

/- English proof (translation)
Establish `ha0 : ∀ b, (a b : ℂ) ≠ 0` using `fun b => by exact_mod_cast (ha b).ne'`. Establish `hD : IsUnit (Matrix.diagonal fun b => (a b : ℂ)).det`. Rewrite using `[Matrix.det_diagonal]`. Conclude with `isUnit_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun b _ => ha0 b)`. Establish `hinv : (pEl k r B S * uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m)⁻¹ = mEmb k r m⁻¹ * (uEmb k r (Matrix.diagonal fun b => (a b : ℂ)⁻¹) * pEl k r (-B) (-S))`.

Rewrite using `[Matrix.mul_inv_rev, Matrix.mul_inv_rev, mEmb_inv m hm, UEmb.uEmb_inv _ hD, pEl_inv, diag_inv _ ha0]`. Establish `hv : ∀ x, (pEl k r (-B) (-S) *ᵥ bvec (esI k r d)) x = pEl k r (-B) (-S) x (esI k r d)` using `fun x => mulVec_bvec _ _ _`. Establish `hDi : (Matrix.diagonal fun b => (a b : ℂ)⁻¹)⁻¹ = Matrix.diagonal fun b => (a b : ℂ)`. Rewrite using `[diag_inv _ (fun b => inv_ne_zero (ha0 b))]`. Simplify using the standard rewrite rules.

Rewrite using `[hinv, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]`. Use `⟨fun c => ?_, fun j => ?_, fun c => ?_⟩` and prove the remaining obligations. Rewrite using `[middleSpaceLeviEmbedding_mulVec_dual_isotropic_coord, isotropicLeviEmbedding_mulVec_dual_isotropic_coord, hDi]`. Simplify using `[Matrix.diagonal_apply, hv, pEl_ss]`. Distinguish the cases in `h : c = d`.

Substitute `h` using the available equality. Simplify using `[Complex.conj_ofReal]`. Simplify using `[h, Ne.symm h]`. Rewrite using `[mE_w]`. Establish `e : (fun i => (uEmb k r (Matrix.diagonal fun b => (a b : ℂ)⁻¹) *ᵥ (pEl k r (-B) (-S) *ᵥ bvec (esI k r d))) (wI k r i)) = -B d`.

Use function extensionality and compare the values at `i`. Rewrite using `[uE_w, hv, pEl_ws]`. Both sides reduce to the same expression. Rewrite using `[e, Matrix.mulVec_neg]`. Both sides reduce to the same expression.

Rewrite using `[mE_e, uE_e]`. Simplify using `[Matrix.diagonal_apply, hv, pEl_es, herm_neg_left, herm_neg_right]`.
-/
theorem col_comp (B : Fin r → Fin (k + 1) → ℂ) (S : Matrix (Fin r) (Fin r) ℂ) (a : Fin r → ℝ) (ha : ∀ b, 0 < a b)
    (m : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (hm : m ∈ UH (Hb k)) (d : Fin r) :
    (∀ c, ((pEl k r B S * uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m)⁻¹ *ᵥ bvec (esI k r d))
      (esI k r c) = if c = d then (a c : ℂ) else 0) ∧
    (∀ j, ((pEl k r B S * uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m)⁻¹ *ᵥ bvec (esI k r d))
      (wI k r j) = -(m⁻¹ *ᵥ B d) j) ∧
    (∀ c, ((pEl k r B S * uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m)⁻¹ *ᵥ bvec (esI k r d))
      (eI k r c) = (a c : ℂ)⁻¹ * (-S c d - herm (Hb k) (B d) (B c) / 2)) := by
  have ha0 : ∀ b, (a b : ℂ) ≠ 0 := fun b => by exact_mod_cast (ha b).ne'
  have hD : IsUnit (Matrix.diagonal fun b => (a b : ℂ)).det := by
    rw [Matrix.det_diagonal]
    exact isUnit_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun b _ => ha0 b)
  have hinv : (pEl k r B S * uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m)⁻¹ =
      mEmb k r m⁻¹ * (uEmb k r (Matrix.diagonal fun b => (a b : ℂ)⁻¹) * pEl k r (-B) (-S)) := by
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, mEmb_inv m hm, UEmb.uEmb_inv _ hD, pEl_inv,
      diag_inv _ ha0]
  have hv : ∀ x, (pEl k r (-B) (-S) *ᵥ bvec (esI k r d)) x = pEl k r (-B) (-S) x (esI k r d) :=
    fun x => mulVec_bvec _ _ _
  have hDi : (Matrix.diagonal fun b => (a b : ℂ)⁻¹)⁻¹ = Matrix.diagonal fun b => (a b : ℂ) := by
    rw [diag_inv _ (fun b => inv_ne_zero (ha0 b))]
    simp
  rw [hinv, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  refine ⟨fun c => ?_, fun j => ?_, fun c => ?_⟩
  · rw [middleSpaceLeviEmbedding_mulVec_dual_isotropic_coord, isotropicLeviEmbedding_mulVec_dual_isotropic_coord, hDi]
    simp [Matrix.diagonal_apply, hv, pEl_ss]
    by_cases h : c = d
    · subst h
      simp [Complex.conj_ofReal]
    · simp [h, Ne.symm h]
  · rw [mE_w]
    have e : (fun i => (uEmb k r (Matrix.diagonal fun b => (a b : ℂ)⁻¹) *ᵥ
        (pEl k r (-B) (-S) *ᵥ bvec (esI k r d))) (wI k r i)) = -B d := by
      funext i
      rw [uE_w, hv, pEl_ws]
      rfl
    rw [e, Matrix.mulVec_neg]
    rfl
  · rw [mE_e, uE_e]
    simp [Matrix.diagonal_apply, hv, pEl_es, herm_neg_left, herm_neg_right]

/- English proof (translation)
Unfold `Xst at hv`. Take `⟨w, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun ℂ).1 hv`. Establish `hw : ∀ c, (∑ i, w i • bvec (esI k r i)) (esI k r c) = w c`. Introduce `c`. Simplify using `[Finset.sum_apply, bvec_apply, esI_inj]`.

Repeatedly rewrite using `[hw]`.
-/
theorem Xst_eq {v : Fin (2 * r + k + 1) → ℂ} (hv : v ∈ Xst k r) :
    v = ∑ c, v (esI k r c) • bvec (esI k r c) := by
  unfold Xst at hv
  obtain ⟨w, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hv
  have hw : ∀ c, (∑ i, w i • bvec (esI k r i)) (esI k r c) = w c := by
    intro c
    simp [Finset.sum_apply, bvec_apply, esI_inj]
  simp_rw [hw]

/- English proof (translation)
Unfold `Dmin`. Use `congr 1`. Use extensionality with `a b`. Simplify using `[Zhat, Zr, fvec, NfMid.herm_e, mulVec_bvec]`.
-/
theorem dr_eq (z z' : Fin (2 * r + k + 1) → ℂ) (g : Mat k r) :
    Dmin k r z z' g ⟨r, by omega⟩ = (Zr k r g).det := by
  unfold Dmin
  congr 1
  ext a b
  simp [Zhat, Zr, fvec, NfMid.herm_e, mulVec_bvec]

end

/- English proof (translation)
Introduce `k r z z' g₀ β De R₀ hTF hNorm hDeOK hR₀ m hm y q a ha hSz' hSz`. Establish `UH_mul : ∀ {g h : Mat k r}, g ∈ UH (Hpk k r) → h ∈ UH (Hpk k r) → g * h ∈ UH (Hpk k r)`. Introduce `g h hg hh`. Simplify using `only [UH, Set.mem_setOf_eq] at hg hh ⊢`. Rewrite using `[Matrix.conjTranspose_mul, show hᴴ * gᴴ * Hpk k r * (g * h) = hᴴ * (gᴴ * Hpk k r * g) * h by simp only [Matrix.mul_assoc], hg, hh]`.

Establish `uEmb_Xst : ∀ (V : Matrix (Fin r) (Fin r) ℂ) {w : Fin (2 * r + k + 1) → ℂ}, w ∈ Xst k r → uEmb k r V *ᵥ w ∈ Xst k r`. Introduce `V w hw`. Rewrite using `[Xst_eq hw, Matrix.mulVec_sum]`. Use `Submodule.sum_mem _ fun c _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.mulVec_smul, UEmb.uEmb_esI]`.

Use `Submodule.smul_mem _ _ (Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ ?_)` and prove the remaining obligations. Conclude with `Submodule.subset_span ⟨a, rfl⟩`. Establish `skew_le : ∀ (S K : Matrix (Fin r) (Fin r) ℂ), (∀ c d, star (S d c) = -S c d) → (∀ c d, star (K d c) = K c d) → ∀ T : ℝ, (∀ c d, ‖S c d + K c d‖ ≤ T) → ∀ c d, ‖S c d‖ ≤ T`. Introduce `S K hS hK T h c d`. Establish `e : S c d = ((S c d + K c d) - star (S d c + K d c)) / 2`.

Rewrite using `[star_add, hS, hK]`. Expand and normalize the polynomial expressions, which then agree. Establish `h1` using `norm_sub_le (S c d + K c d) (star (S d c + K d c))`. Rewrite `h1` using `[norm_star]`. Rewrite using `[e, norm_div, Complex.norm_two, div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]`.

Combine the linear relations using `[h c d, h d c]`. Take `⟨hzW, hz'W, -, -, hg₀, -, hDr⟩` from `hTF`. Take `⟨x, hxdef⟩ : ∃ x, x = uEmb k r (upperOff β y) * pOf k r q * uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m` from `⟨_, rfl⟩`. Take `⟨Q, hQ⟩ : ∃ Q, Q = pEl k r q.1 (skewM q.2.1 q.2.2) * uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m` from `⟨_, rfl⟩`. Rewrite `hSz'`, `hSz` using `[← hxdef]`.

Establish `hR0 : 0 ≤ R₀` using `by linarith`. Establish `hDe0 : 0 ≤ De` using `by linarith [hDeOK.1]`. Establish `ha0 : ∀ b, (a b : ℂ) ≠ 0` using `fun b => by exact_mod_cast (ha b).ne'`. Establish `hDu : IsUnit (Matrix.diagonal fun b => (a b : ℂ)).det`. Rewrite using `[Matrix.det_diagonal]`.

Conclude with `isUnit_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun b _ => ha0 b)`. Establish `hUdet : (upperOff β y).det = 1` using `UEmb.det_upper _`. Establish `hUu : IsUnit (upperOff β y).det` using `by rw [hUdet]; exact isUnit_one`. Establish `hSskew : (skewM q.2.1 q.2.2)ᴴ = -skewM q.2.1 q.2.2` using `Rad.skewM_skew _ _`. Establish `hUN : uEmb k r (upperOff β y) ∈ Nset k r` using `UEmb.upper_mem _`.

Establish `hPN : pEl k r q.1 (skewM q.2.1 q.2.2) ∈ Nset k r` using `(((Rad.radical k r).1 q.1 (skewM q.2.1 q.2.2)).2.2.2 hSskew).1`. Establish `hDG : uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) ∈ GG k r` using `UEmb.uEmb_mem _ hDu`. Establish `hMG : mEmb k r m ∈ GG k r` using `Rad.mEmb_mem m hm`. Establish `hDMG` using `UH_mul hDG hMG`. Establish `hQG : Q ∈ GG k r` using `by rw [hQ]; exact UH_mul (UH_mul hPN.1 hDG) hMG`.

Establish `hxQ : x = uEmb k r (upperOff β y) * Q`. Rewrite using `[hxdef, hQ, pOf]`. Simplify using `only [Matrix.mul_assoc]`. Establish `hxG : x ∈ GG k r` using `by rw [hxQ]; exact UH_mul hUN.1 hQG`. Establish `hx'G : g₀ * x ∈ GG k r` using `UH_mul hg₀ hxG`.

Establish `h1UW : ∀ w : Fin (2 * r + k + 1) → ℂ, (1 : Mat k r) ∈ UWset k r w`. Introduce `w`. Simplify using `[UWset, UH]`. Establish `hSset : ∀ w, ∀ n ∈ Nset k r, n ∈ Sset k r w` using `fun w n hn => ⟨1, h1UW w, n, hn, (one_mul n).symm⟩`. Establish `h1K : (1 : Mat k r) ∈ (GG k r ∩ (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set (Mat k r)))` using `⟨by simp [UH], Submonoid.one_mem _⟩`.

Establish `LB'` using `LInv.lengths_basic k r z' hz'W`. Establish `LB` using `LInv.lengths_basic k r z hzW`. Establish `hal : ∀ b, (a b)⁻¹ ≤ R₀`. Introduce `b`. Establish `e1` using `(LB'.1 Q hQG _ (hSset z' _ hUN) 1 h1K).1 b.castSucc`.

Establish `e2` using `(LB'.1 _ hDMG _ (hSset z' _ hPN) 1 h1K).1 b.castSucc`. Establish `e3` using `LB'.2.1 a ha m hm b`. Establish `hQ' : Q = pEl k r q.1 (skewM q.2.1 q.2.2) * (uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m) * 1`. Rewrite using `[hQ, Matrix.mul_one, Matrix.mul_assoc]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hxQ, ← Matrix.mul_one (uEmb k r (upperOff β y) * Q), e1, hQ', e2, e3]`. Use `_ ≤ Sg k r z' x := ((LB'.2.2 x).2.1 _).2`. Use `_ ≤ R₀ := hSz'`. Take `⟨u', hu'len, -⟩` from `GramFlag.gramSchmidt_lengths k r z (g₀ * x) hx'G`. Establish `hWb : ∀ a', eucl (∑ b, upper u' b a' • ((g₀ * x)⁻¹ *ᵥ bvec (eI k r b))) ≤ R₀`.

Introduce `a'`. Rewrite using `[(hu'len a').1]`. Conclude with `((LB.2.2 (g₀ * x)).2.1 _).2.trans hSz`. Take `⟨Mm, hMm⟩ : ∃ Mm : Matrix (Fin r) (Fin r) ℂ, Mm = (upperOff β y)ᴴ * Zr k r g₀⁻¹` from `⟨_, rfl⟩`. Establish `hM : ∀ b, (g₀ * x)⁻¹ *ᵥ bvec (eI k r b) = ∑ d, Mm d b • (Q⁻¹ *ᵥ bvec (esI k r d))`.

Introduce `b`. Establish `hyX : uEmb k r (upperOff β y)⁻¹ *ᵥ (g₀⁻¹ *ᵥ bvec (eI k r b)) ∈ Xst k r` using `uEmb_Xst _ (hNorm.2.1 b).1`. Rewrite using `[hxQ, Matrix.mul_inv_rev, Matrix.mul_inv_rev, UEmb.uEmb_inv _ hUu, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Xst_eq hyX, Matrix.mulVec_sum]`. Use `Finset.sum_congr rfl fun d _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.mulVec_smul]`.

Use `congr 1`. Rewrite using `[isotropicLeviEmbedding_mulVec_dual_isotropic_coord, Matrix.nonsing_inv_nonsing_inv _ hUu, hMm, Matrix.mul_apply]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.conjTranspose_apply, Rad.mulVec_bvec]`. Both sides reduce to the same expression.

Take `⟨Nm, hNm⟩ : ∃ Nm : Matrix (Fin r) (Fin r) ℂ, Nm = Mm * upper u'` from `⟨_, rfl⟩`. Establish `hW' : ∀ a', (∑ b, upper u' b a' • ((g₀ * x)⁻¹ *ᵥ bvec (eI k r b))) = ∑ d, Nm d a' • (Q⁻¹ *ᵥ bvec (esI k r d))`. Introduce `a'`. Repeatedly rewrite using `[hM, Finset.smul_sum, smul_smul]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun d _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_smul, hNm, Matrix.mul_apply]`. Use `congr 1`. Conclude with `Finset.sum_congr rfl fun b _ => mul_comm _ _`. Establish `hWb' : ∀ a', eucl (∑ d, Nm d a' • (Q⁻¹ *ᵥ bvec (esI k r d))) ≤ R₀`.

Introduce `a'`. Rewrite using `[← hW' a']`. Conclude with `hWb a'`. Establish `hcol` using `fun d => col_comp q.1 (skewM q.2.1 q.2.2) a ha m hm d`. Simplify using `only [← hQ] at hcol`.

Establish `hcol1 : ∀ d c, (Q⁻¹ *ᵥ bvec (esI k r d)) (esI k r c) = if c = d then (a c : ℂ) else 0` using `fun d => (hcol d).1`. Establish `hNcol : ∀ a', eucl (fun c => (a c : ℂ) * Nm c a') ≤ R₀`. Introduce `a'`. Establish `e : (fun c => (a c : ℂ) * Nm c a') = fun c => (∑ d, Nm d a' • (Q⁻¹ *ᵥ bvec (esI k r d))) (esI k r c)`. Use function extensionality and compare the values at `c`.

Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hcol1]`. Simplify using `[mul_comm]`. Rewrite using `[e]`. Conclude with `(eucl_comp_le (esI k r) (fun c c' h => (Rad.esI_inj c c').1 h) _).trans (hWb' a')`. Establish `hZr : Zr k r g₀⁻¹ = (Zr k r g₀)ᴴ` using `NfMid.zr_inv hg₀`.

Establish `hdr` using `dr_eq z z' g₀`. Establish `hZne : ‖(Zr k r g₀).det‖ ≠ 0` using `by rw [← hdr]; exact hDr`. Establish `hZDe : ‖(Zr k r g₀).det‖⁻¹ ≤ De`. Rewrite using `[← hdr]`. Conclude with `hDeOK.2 ⟨r, by omega⟩ le_rfl (by rw [hdr]; exact norm_ne_zero_iff.1 hZne)`.

Establish `hdetN : ‖Nm.det‖ = ‖(Zr k r g₀).det‖`. Rewrite using `[hNm, Matrix.det_mul, hMm, Matrix.det_mul, hZr, Matrix.det_conjTranspose, Matrix.det_conjTranspose, hUdet, UEmb.det_upper]`. Simplify using the standard rewrite rules. Establish `hNdet : Nm.det ≠ 0`. Introduce `h`.

Apply `hZne` to reduce the goal to its premises. Rewrite using `[← hdetN, h, norm_zero]`. Establish `hNDe : ‖Nm.det‖⁻¹ ≤ De` using `by rw [hdetN]; exact hZDe`. Take `⟨hinvE, hac⟩` from `inv_bound Nm a ha R₀ De hR₀ hal hNcol hNdet hNDe`. Establish `hNu : Nm * Nm⁻¹ = 1` using `Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hNdet)`.

Establish `hErep : ∀ d, Q⁻¹ *ᵥ bvec (esI k r d) = ∑ a', Nm⁻¹ a' d • ∑ d', Nm d' a' • (Q⁻¹ *ᵥ bvec (esI k r d'))`. Introduce `d`. Use function extensionality and compare the values at `i`. Establish `hone` using `fun d' => congrFun (congrFun hNu d') d`. Simplify using `only [Matrix.mul_apply] at hone`.

Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `[Matrix.one_apply]`. Use `_ = _ := by`.

Use `Finset.sum_congr rfl fun d' _ => ?_` and prove the remaining obligations. Rewrite using `[← hone d', Finset.sum_mul]`. Conclude with `Finset.sum_congr rfl fun a' _ => by ring`. Establish `hEbd : ∀ d, eucl (Q⁻¹ *ᵥ bvec (esI k r d)) ≤ r * R₀ ^ (2 * r - 1) * De`. Introduce `d`.

Establish `hr : 1 ≤ r` using `by have := d.isLt; omega`. Rewrite using `[hErep d]`. Use `(eucl_sum_le (fun a' => Nm⁻¹ a' d) _ (R₀ ^ (2 * r - 2) * De) R₀ (fun a' => hinvE a' d) hWb').trans (le_of_eq ?_)` and prove the remaining obligations. Establish `e : 2 * r - 1 = (2 * r - 2) + 1` using `by omega`. Rewrite using `[e, pow_succ]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hSK : ∀ c d, ‖skewM q.2.1 q.2.2 c d + herm (Hb k) (q.1 d) (q.1 c) / 2‖ ≤ r * R₀ ^ (4 * r - 2) * De ^ 2`. Introduce `c d`. Establish `hr : 1 ≤ r` using `by have := d.isLt; omega`. Establish `e1` using `(hcol d).2.2 c`.

Establish `e2 : skewM q.2.1 q.2.2 c d + herm (Hb k) (q.1 d) (q.1 c) / 2 = -((a c : ℂ) * (Q⁻¹ *ᵥ bvec (esI k r d)) (eI k r c))`. Rewrite using `[e1, ← mul_assoc, mul_inv_cancel₀ (ha0 c), one_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e2, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (ha c)]`. Combine the equalities or inequalities in the displayed calculation.

Establish `e : 4 * r - 2 = (2 * r - 1) + (2 * r - 1)` using `by omega`. Rewrite using `[e, pow_add]`. Expand and normalize the polynomial expressions, which then agree. Establish `hskew : ∀ c d : Fin r, ‖skewM q.2.1 q.2.2 c d‖ ≤ r * R₀ ^ (4 * r - 2) * De ^ 2`. Introduce `c d`.

Use `skew_le (skewM q.2.1 q.2.2) (Matrix.of fun c d => herm (Hb k) (q.1 d) (q.1 c) / 2) (fun c d => ?_) (fun c d => ?_) _ (fun c d => ?_) c d` and prove the remaining obligations. Use `congrFun (congrFun hSskew c) d` as an intermediate fact. Simplify `this` using `[Matrix.conjTranspose_apply]`. Simplify using `only [Matrix.of_apply]`. Rewrite using `[div_eq_mul_inv, div_eq_mul_inv, star_mul', Rad.herm_star]`.

Simplify using the standard rewrite rules. Simplify `hSK c d` using `only [Matrix.of_apply]`. Use `⟨fun b => ?_, fun p => ?_, fun b => ?_⟩` and prove the remaining obligations. Establish `e : m⁻¹ *ᵥ q.1 b = -(fun j => (Q⁻¹ *ᵥ bvec (esI k r b)) (wI k r j))`. Use function extensionality and compare the values at `j`.

Simplify using `only [Pi.neg_apply, (hcol b).2.1 j, neg_neg]`. Rewrite using `[e, eucl_neg]`. Conclude with `(eucl_comp_le (wI k r) (fun j j' h => (Rad.wI_inj j j').1 h) _).trans (hEbd b)`. Establish `e : q.2.1 p = skewM q.2.1 q.2.2 p.1.1 p.1.2`. Simplify using `only [skewM, dif_pos p.2]`.

Rewrite using `[e]`. Conclude with `hskew _ _`. Establish `e : skewM q.2.1 q.2.2 b b = (q.2.2 b : ℂ) * Complex.I`. Simplify using `[skewM]`. Use `hskew b b` as an intermediate fact.

Rewrite `this` using `[e, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]`. Conclude with `this`.
-/
theorem radical_coords_le : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (g₀ : Mat k r) (β : Fin r → ℕ) (De R₀ : ℝ), TwoFl k r z z' g₀ → IsNormal k r β g₀ → DeOK k r z z' g₀ De → 1 ≤ R₀ → ∀ m ∈ UH (Hb k), ∀ (y : UToff β → ℂ) (q : PPar k r) (a : Fin r → ℝ), (∀ b, 0 < a b) → Sg k r z' (uEmb k r (upperOff β y) * pOf k r q * uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m) ≤ R₀ → Sg k r z (g₀ * (uEmb k r (upperOff β y) * pOf k r q * uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m)) ≤ R₀ → (∀ b, eucl (m⁻¹ *ᵥ q.1 b) ≤ r * R₀ ^ (2 * r - 1) * De) ∧ (∀ p, ‖q.2.1 p‖ ≤ r * R₀ ^ (4 * r - 2) * De ^ 2) ∧ ∀ b, |q.2.2 b| ≤ r * R₀ ^ (4 * r - 2) * De ^ 2 := by
  intro k r z z' g₀ β De R₀ hTF hNorm hDeOK hR₀ m hm y q a ha hSz' hSz
  classical
  have UH_mul : ∀ {g h : Mat k r}, g ∈ UH (Hpk k r) → h ∈ UH (Hpk k r) → g * h ∈ UH (Hpk k r) := by
    intro g h hg hh
    simp only [UH, Set.mem_setOf_eq] at hg hh ⊢
    rw [Matrix.conjTranspose_mul,
      show hᴴ * gᴴ * Hpk k r * (g * h) = hᴴ * (gᴴ * Hpk k r * g) * h by simp only [Matrix.mul_assoc],
      hg, hh]
  have uEmb_Xst : ∀ (V : Matrix (Fin r) (Fin r) ℂ) {w : Fin (2 * r + k + 1) → ℂ},
      w ∈ Xst k r → uEmb k r V *ᵥ w ∈ Xst k r := by
    intro V w hw
    rw [Xst_eq hw, Matrix.mulVec_sum]
    refine Submodule.sum_mem _ fun c _ => ?_
    rw [Matrix.mulVec_smul, UEmb.uEmb_esI]
    refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ ?_)
    exact Submodule.subset_span ⟨a, rfl⟩
  have skew_le : ∀ (S K : Matrix (Fin r) (Fin r) ℂ), (∀ c d, star (S d c) = -S c d) →
      (∀ c d, star (K d c) = K c d) → ∀ T : ℝ, (∀ c d, ‖S c d + K c d‖ ≤ T) →
      ∀ c d, ‖S c d‖ ≤ T := by
    intro S K hS hK T h c d
    have e : S c d = ((S c d + K c d) - star (S d c + K d c)) / 2 := by
      rw [star_add, hS, hK]
      ring
    have h1 := norm_sub_le (S c d + K c d) (star (S d c + K d c))
    rw [norm_star] at h1
    rw [e, norm_div, Complex.norm_two, div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
    linarith [h c d, h d c]
  obtain ⟨hzW, hz'W, -, -, hg₀, -, hDr⟩ := hTF
  obtain ⟨x, hxdef⟩ : ∃ x, x = uEmb k r (upperOff β y) * pOf k r q *
      uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = pEl k r q.1 (skewM q.2.1 q.2.2) *
      uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m := ⟨_, rfl⟩
  rw [← hxdef] at hSz' hSz
  have hR0 : 0 ≤ R₀ := by linarith
  have hDe0 : 0 ≤ De := by linarith [hDeOK.1]
  have ha0 : ∀ b, (a b : ℂ) ≠ 0 := fun b => by exact_mod_cast (ha b).ne'
  have hDu : IsUnit (Matrix.diagonal fun b => (a b : ℂ)).det := by
    rw [Matrix.det_diagonal]
    exact isUnit_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun b _ => ha0 b)
  have hUdet : (upperOff β y).det = 1 := UEmb.det_upper _
  have hUu : IsUnit (upperOff β y).det := by rw [hUdet]; exact isUnit_one
  have hSskew : (skewM q.2.1 q.2.2)ᴴ = -skewM q.2.1 q.2.2 := Rad.skewM_skew _ _
  have hUN : uEmb k r (upperOff β y) ∈ Nset k r := UEmb.upper_mem _
  have hPN : pEl k r q.1 (skewM q.2.1 q.2.2) ∈ Nset k r :=
    (((Rad.radical k r).1 q.1 (skewM q.2.1 q.2.2)).2.2.2 hSskew).1
  have hDG : uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) ∈ GG k r := UEmb.uEmb_mem _ hDu
  have hMG : mEmb k r m ∈ GG k r := Rad.mEmb_mem m hm
  have hDMG := UH_mul hDG hMG
  have hQG : Q ∈ GG k r := by rw [hQ]; exact UH_mul (UH_mul hPN.1 hDG) hMG
  have hxQ : x = uEmb k r (upperOff β y) * Q := by
    rw [hxdef, hQ, pOf]
    simp only [Matrix.mul_assoc]
  have hxG : x ∈ GG k r := by rw [hxQ]; exact UH_mul hUN.1 hQG
  have hx'G : g₀ * x ∈ GG k r := UH_mul hg₀ hxG
  have h1UW : ∀ w : Fin (2 * r + k + 1) → ℂ, (1 : Mat k r) ∈ UWset k r w := by
    intro w
    simp [UWset, UH]
  have hSset : ∀ w, ∀ n ∈ Nset k r, n ∈ Sset k r w :=
    fun w n hn => ⟨1, h1UW w, n, hn, (one_mul n).symm⟩
  have h1K : (1 : Mat k r) ∈
      (GG k r ∩ (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set (Mat k r))) :=
    ⟨by simp [UH], Submonoid.one_mem _⟩
  have LB' := LInv.lengths_basic k r z' hz'W
  have LB := LInv.lengths_basic k r z hzW
  have hal : ∀ b, (a b)⁻¹ ≤ R₀ := by
    intro b
    have e1 := (LB'.1 Q hQG _ (hSset z' _ hUN) 1 h1K).1 b.castSucc
    have e2 := (LB'.1 _ hDMG _ (hSset z' _ hPN) 1 h1K).1 b.castSucc
    have e3 := LB'.2.1 a ha m hm b
    have hQ' : Q = pEl k r q.1 (skewM q.2.1 q.2.2) *
        (uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m) * 1 := by
      rw [hQ, Matrix.mul_one, Matrix.mul_assoc]
    calc (a b)⁻¹ = lA k r z' x b.castSucc := by
          rw [hxQ, ← Matrix.mul_one (uEmb k r (upperOff β y) * Q), e1, hQ', e2, e3]
      _ ≤ Sg k r z' x := ((LB'.2.2 x).2.1 _).2
      _ ≤ R₀ := hSz'
  obtain ⟨u', hu'len, -⟩ := GramFlag.gramSchmidt_lengths k r z (g₀ * x) hx'G
  have hWb : ∀ a', eucl (∑ b, upper u' b a' • ((g₀ * x)⁻¹ *ᵥ bvec (eI k r b))) ≤ R₀ := by
    intro a'
    rw [(hu'len a').1]
    exact ((LB.2.2 (g₀ * x)).2.1 _).2.trans hSz
  obtain ⟨Mm, hMm⟩ : ∃ Mm : Matrix (Fin r) (Fin r) ℂ, Mm = (upperOff β y)ᴴ * Zr k r g₀⁻¹ :=
    ⟨_, rfl⟩
  have hM : ∀ b, (g₀ * x)⁻¹ *ᵥ bvec (eI k r b) = ∑ d, Mm d b • (Q⁻¹ *ᵥ bvec (esI k r d)) := by
    intro b
    have hyX : uEmb k r (upperOff β y)⁻¹ *ᵥ (g₀⁻¹ *ᵥ bvec (eI k r b)) ∈ Xst k r :=
      uEmb_Xst _ (hNorm.2.1 b).1
    rw [hxQ, Matrix.mul_inv_rev, Matrix.mul_inv_rev, UEmb.uEmb_inv _ hUu, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, Xst_eq hyX, Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Matrix.mulVec_smul]
    congr 1
    rw [isotropicLeviEmbedding_mulVec_dual_isotropic_coord, Matrix.nonsing_inv_nonsing_inv _ hUu, hMm, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Matrix.conjTranspose_apply, Rad.mulVec_bvec]
    rfl
  obtain ⟨Nm, hNm⟩ : ∃ Nm : Matrix (Fin r) (Fin r) ℂ, Nm = Mm * upper u' := ⟨_, rfl⟩
  have hW' : ∀ a', (∑ b, upper u' b a' • ((g₀ * x)⁻¹ *ᵥ bvec (eI k r b))) =
      ∑ d, Nm d a' • (Q⁻¹ *ᵥ bvec (esI k r d)) := by
    intro a'
    simp_rw [hM, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [← Finset.sum_smul, hNm, Matrix.mul_apply]
    congr 1
    exact Finset.sum_congr rfl fun b _ => mul_comm _ _
  have hWb' : ∀ a', eucl (∑ d, Nm d a' • (Q⁻¹ *ᵥ bvec (esI k r d))) ≤ R₀ := by
    intro a'
    rw [← hW' a']
    exact hWb a'
  have hcol := fun d => col_comp q.1 (skewM q.2.1 q.2.2) a ha m hm d
  simp only [← hQ] at hcol
  have hcol1 : ∀ d c, (Q⁻¹ *ᵥ bvec (esI k r d)) (esI k r c) = if c = d then (a c : ℂ) else 0 :=
    fun d => (hcol d).1
  have hNcol : ∀ a', eucl (fun c => (a c : ℂ) * Nm c a') ≤ R₀ := by
    intro a'
    have e : (fun c => (a c : ℂ) * Nm c a') =
        fun c => (∑ d, Nm d a' • (Q⁻¹ *ᵥ bvec (esI k r d))) (esI k r c) := by
      funext c
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hcol1]
      simp [mul_comm]
    rw [e]
    exact (eucl_comp_le (esI k r) (fun c c' h => (Rad.esI_inj c c').1 h) _).trans (hWb' a')
  have hZr : Zr k r g₀⁻¹ = (Zr k r g₀)ᴴ := NfMid.zr_inv hg₀
  have hdr := dr_eq z z' g₀
  have hZne : ‖(Zr k r g₀).det‖ ≠ 0 := by rw [← hdr]; exact hDr
  have hZDe : ‖(Zr k r g₀).det‖⁻¹ ≤ De := by
    rw [← hdr]
    exact hDeOK.2 ⟨r, by omega⟩ le_rfl (by rw [hdr]; exact norm_ne_zero_iff.1 hZne)
  have hdetN : ‖Nm.det‖ = ‖(Zr k r g₀).det‖ := by
    rw [hNm, Matrix.det_mul, hMm, Matrix.det_mul, hZr, Matrix.det_conjTranspose,
      Matrix.det_conjTranspose, hUdet, UEmb.det_upper]
    simp
  have hNdet : Nm.det ≠ 0 := by
    intro h
    apply hZne
    rw [← hdetN, h, norm_zero]
  have hNDe : ‖Nm.det‖⁻¹ ≤ De := by rw [hdetN]; exact hZDe
  obtain ⟨hinvE, hac⟩ := inv_bound Nm a ha R₀ De hR₀ hal hNcol hNdet hNDe
  have hNu : Nm * Nm⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hNdet)
  have hErep : ∀ d, Q⁻¹ *ᵥ bvec (esI k r d) =
      ∑ a', Nm⁻¹ a' d • ∑ d', Nm d' a' • (Q⁻¹ *ᵥ bvec (esI k r d')) := by
    intro d
    funext i
    have hone := fun d' => congrFun (congrFun hNu d') d
    simp only [Matrix.mul_apply] at hone
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    calc (Q⁻¹ *ᵥ bvec (esI k r d)) i
        = ∑ d', (1 : Matrix (Fin r) (Fin r) ℂ) d' d * (Q⁻¹ *ᵥ bvec (esI k r d')) i := by
          simp [Matrix.one_apply]
      _ = _ := by
          refine Finset.sum_congr rfl fun d' _ => ?_
          rw [← hone d', Finset.sum_mul]
          exact Finset.sum_congr rfl fun a' _ => by ring
  have hEbd : ∀ d, eucl (Q⁻¹ *ᵥ bvec (esI k r d)) ≤ r * R₀ ^ (2 * r - 1) * De := by
    intro d
    have hr : 1 ≤ r := by have := d.isLt; omega
    rw [hErep d]
    refine (eucl_sum_le (fun a' => Nm⁻¹ a' d) _ (R₀ ^ (2 * r - 2) * De) R₀
      (fun a' => hinvE a' d) hWb').trans (le_of_eq ?_)
    have e : 2 * r - 1 = (2 * r - 2) + 1 := by omega
    rw [e, pow_succ]
    ring
  have hSK : ∀ c d, ‖skewM q.2.1 q.2.2 c d + herm (Hb k) (q.1 d) (q.1 c) / 2‖ ≤
      r * R₀ ^ (4 * r - 2) * De ^ 2 := by
    intro c d
    have hr : 1 ≤ r := by have := d.isLt; omega
    have e1 := (hcol d).2.2 c
    have e2 : skewM q.2.1 q.2.2 c d + herm (Hb k) (q.1 d) (q.1 c) / 2 =
        -((a c : ℂ) * (Q⁻¹ *ᵥ bvec (esI k r d)) (eI k r c)) := by
      rw [e1, ← mul_assoc, mul_inv_cancel₀ (ha0 c), one_mul]
      ring
    rw [e2, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (ha c)]
    calc a c * ‖(Q⁻¹ *ᵥ bvec (esI k r d)) (eI k r c)‖
        ≤ (R₀ ^ (2 * r - 1) * De) * (r * R₀ ^ (2 * r - 1) * De) :=
          mul_le_mul (hac c) ((LInv.norm_le_eucl _ _).trans (hEbd d)) (norm_nonneg _)
            (mul_nonneg (pow_nonneg hR0 _) hDe0)
      _ = r * R₀ ^ (4 * r - 2) * De ^ 2 := by
          have e : 4 * r - 2 = (2 * r - 1) + (2 * r - 1) := by omega
          rw [e, pow_add]
          ring
  have hskew : ∀ c d : Fin r, ‖skewM q.2.1 q.2.2 c d‖ ≤ r * R₀ ^ (4 * r - 2) * De ^ 2 := by
    intro c d
    refine skew_le (skewM q.2.1 q.2.2) (Matrix.of fun c d => herm (Hb k) (q.1 d) (q.1 c) / 2)
      (fun c d => ?_) (fun c d => ?_) _ (fun c d => ?_) c d
    · have := congrFun (congrFun hSskew c) d
      simpa [Matrix.conjTranspose_apply] using this
    · simp only [Matrix.of_apply]
      rw [div_eq_mul_inv, div_eq_mul_inv, star_mul', Rad.herm_star]
      simp
    · simpa only [Matrix.of_apply] using hSK c d
  refine ⟨fun b => ?_, fun p => ?_, fun b => ?_⟩
  · have e : m⁻¹ *ᵥ q.1 b = -(fun j => (Q⁻¹ *ᵥ bvec (esI k r b)) (wI k r j)) := by
      funext j
      simp only [Pi.neg_apply, (hcol b).2.1 j, neg_neg]
    rw [e, eucl_neg]
    exact (eucl_comp_le (wI k r) (fun j j' h => (Rad.wI_inj j j').1 h) _).trans (hEbd b)
  · have e : q.2.1 p = skewM q.2.1 q.2.2 p.1.1 p.1.2 := by
      simp only [skewM, dif_pos p.2]
    rw [e]
    exact hskew _ _
  · have e : skewM q.2.1 q.2.2 b b = (q.2.2 b : ℂ) * Complex.I := by
      simp [skewM]
    have := hskew b b
    rw [e, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs] at this
    exact this

end GlobalTheory.Amp.RadBound
