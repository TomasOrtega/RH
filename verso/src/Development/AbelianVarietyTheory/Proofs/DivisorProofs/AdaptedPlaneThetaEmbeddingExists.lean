import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.RealFreq

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem evI_mul (a b : AF F) : evI F (a * b) = evI F a * evI F b := by
  unfold evI; exact map_mul _ a.1 b.1

/- English proof (translation)
Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem evI_add (a b : AF F) : evI F (a + b) = evI F a + evI F b := by
  unfold evI; exact map_add _ a.1 b.1

/- English proof (translation)
Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem evI_realAd (t : ℝ) : evI F (realAd F t) = algebraMap ℝ _ t := by
  unfold evI realAd
  exact RingEquiv.apply_symm_apply _ _

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Replace the relevant objects with their definitions. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem realAd_mul_at (t : ℝ) (b : AF F) : At (evI F) (realAd F t * b) := by
  intro u hu
  have h1 : u.1 = 0 := by
    unfold evI at hu
    exact (map_eq_zero_iff _ (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective).1 hu
  have h2 : u * realAd F t = 0 := by
    refine Prod.ext ?_ ?_
    · change u.1 * _ = 0
      rw [h1, zero_mul]
    · change u.2 * 0 = 0
      rw [mul_zero]
  rw [smul_eq_mul, ← mul_assoc, h2, zero_mul]

/- English proof (translation)
Replace the relevant objects with their definitions. Simplify using the standard rewrite rules.
-/
theorem cA_inclR (σ : E →ₐ[F] E) (e : E) : cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := by
  unfold cA inclR
  simp

end GlobalTheory.RealFreq

namespace GlobalTheory.RealFreq
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
open Matrix

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem hTens_add_right (σ : E →ₐ[F] E) {n d : ℕ} (JA : Matrix (Fin n) (Fin n) (AE F E)) (JB : Matrix (Fin d) (Fin d) (AE F E))
    (x y y' : Matrix (Fin n) (Fin d) (AE F E)) :
    hTens (cA σ) JA JB x (y + y') = hTens (cA σ) JA JB x y + hTens (cA σ) JA JB x y' := by
  simp only [hTens, Matrix.add_apply, map_add, mul_add, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem hTens_smul_right (σ : E →ₐ[F] E) {n d : ℕ} (JA : Matrix (Fin n) (Fin n) (AE F E)) (JB : Matrix (Fin d) (Fin d) (AE F E))
    (x y : Matrix (Fin n) (Fin d) (AE F E)) (r : AF F) :
    hTens (cA σ) JA JB x (r • y) = r • hTens (cA σ) JA JB x y := by
  simp only [hTens, Matrix.smul_apply, map_smul, mul_smul_comm, Finset.smul_sum]

def hTensR (σ : E →ₐ[F] E) {n d : ℕ} (JA : Matrix (Fin n) (Fin n) (AE F E)) (JB : Matrix (Fin d) (Fin d) (AE F E))
    (x : Matrix (Fin n) (Fin d) (AE F E)) : Matrix (Fin n) (Fin d) (AE F E) →ₗ[AF F] AE F E where
  toFun := hTens (cA σ) JA JB x
  map_add' := hTens_add_right σ JA JB x
  map_smul' := fun r y => hTens_smul_right σ JA JB x y r

/- English proof (translation)
Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Reduce the equality to equality of the corresponding arguments. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.

A detailed English derivation is pending.
-/
theorem hTens_rat (σ : E →ₐ[F] E) {n d : ℕ} (JX : Matrix (Fin n) (Fin n) E) (JW : Matrix (Fin d) (Fin d) E)
    (ξ q : Fin n → E) (y x : Fin d → E) :
    hTens (cA σ) (incM F JX) (incM F JW) (vecMulVec (incV F ξ) (incV F y)) (vecMulVec (incV F q) (incV F x)) =
      inclR (F := F) (AF F) (form σ JX ξ q * form σ JW y x) := by
  simp only [hTens, vecMulVec_apply, incV, incM, Matrix.map_apply, ← map_mul, cA_inclR, form, dotProduct, mulVec,
    Finset.sum_mul, Finset.mul_sum, map_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  congr 1; rw [map_mul]; ring

end GlobalTheory.RealFreq

namespace GlobalTheory.RealFreq
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
open Matrix

/- English proof (translation)
Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem symp_freq (σ : E →ₐ[F] E) {n d : ℕ} (JX : Matrix (Fin n) (Fin n) E) (JW : Matrix (Fin d) (Fin d) E)
    (ξ : Fin n → E) (y x : Fin d → E) (hyx : form σ JW y x = -1) {N : ℕ} (q : Fin N → Fin n → E) (t : Fin N → ℝ) :
    symp (R := AF F) (cA σ) (-1) (incM F JX) (incM F JW) (vecMulVec (incV F ξ) (incV F y))
      (vecMulVec (∑ j, realAd F (t j) • incV F (q j)) (incV F x)) =
      ∑ j, realAd F (t j) * Algebra.trace (AF F) (AE F E) (inclR (F := F) (AF F) (form σ JX ξ (q j))) := by
  have hv : vecMulVec (∑ j, realAd F (t j) • incV F (q j)) (incV F x) =
      ∑ j, realAd F (t j) • vecMulVec (incV F (q j)) (incV F x) := by
    ext i l
    simp [vecMulVec_apply, Matrix.sum_apply, Finset.sum_mul, smul_mul_assoc]
  unfold symp
  rw [hv]
  change Algebra.trace (AF F) (AE F E) (-1 * hTensR σ (incM F JX) (incM F JW) _ (∑ j, _)) = _
  rw [map_sum]
  simp only [map_smul]
  simp only [hTensR, LinearMap.coe_mk, AddHom.coe_mk, hTens_rat, hyx, mul_neg_one, map_neg, smul_neg,
    Finset.sum_neg_distrib, neg_mul, one_mul, neg_neg, map_sum, map_smul, smul_eq_mul]

end GlobalTheory.RealFreq

namespace GlobalTheory.RealFreq
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
open Matrix

def evIHom : AF F →+ mixedEmbedding.mixedSpace F where
  toFun := evI F
  map_zero' := by unfold evI; exact map_zero _
  map_add' := evI_add

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem psi_freq (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) {N : ℕ} (c : Fin N → AF F) (t : Fin N → ℝ) :
    ψ (∑ j, realAd F (t j) * c j) = Complex.exp (-(2 * Real.pi * Complex.I) *
      ((∑ j, t j * Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (c j)) : ℝ) : ℂ)) := by
  have hat : At (evI F) (∑ j, realAd F (t j) * c j) := by
    intro u hu
    rw [Finset.smul_sum]
    exact Finset.sum_eq_zero fun j _ => realAd_mul_at _ _ u hu
  rw [hψ.2.2 _ hat]
  congr 3
  have h1 : evI F (∑ j, realAd F (t j) * c j) = ∑ j, t j • evI F (c j) := by
    change evIHom (∑ j, realAd F (t j) * c j) = _
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    change evI F _ = _
    rw [evI_mul, evI_realAd, Algebra.smul_def]
  rw [h1, map_sum]
  simp only [map_smul, smul_eq_mul]

end GlobalTheory.RealFreq

namespace GlobalTheory.RealFreq
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
open Matrix

variable (F) in

def realTr : E →+ ℝ :=
  (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)).toAddMonoidHom.comp (evIHom.comp
    ((Algebra.trace (AF F) (AE F E)).toAddMonoidHom.comp (inclR (F := F) (AF F)).toAddMonoidHom))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem realTr_apply (e : E) : realTr F e = Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
    (evI F (Algebra.trace (AF F) (AE F E) (inclR (F := F) (AF F) e))) := rfl

omit [NumberField F] [NumberField E] in
/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.
-/
theorem trace_baseChange_tmul' [FiniteDimensional F E] (R : Type) [CommRing R] [Algebra F R] (a : R) (e : E) :
    Algebra.trace R (R ⊗[F] E) (a ⊗ₜ[F] e) = a * algebraMap F R (Algebra.trace F E e) := by
  have h1 : a ⊗ₜ[F] e = a • ((1 : R) ⊗ₜ[F] e) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [h1, map_smul, Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul,
    LinearMap.trace_baseChange, smul_eq_mul]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Evaluate the numerical expressions.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules. Check the signs of the components of the expression.

A detailed English derivation is pending.
-/
theorem realTr_one_ne (h : Module.finrank F E = 2) : realTr F (1 : E) ≠ 0 := by
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [h]; norm_num)
  rw [realTr_apply]
  have h1 : inclR (F := F) (AF F) (1 : E) = (1 : AF F) ⊗ₜ[F] (1 : E) := rfl
  have h2 : Algebra.trace F E (1 : E) = 1 + 1 := by
    rw [← map_one (algebraMap F E), Algebra.trace_algebraMap, h]; norm_num
  have h3 : evI F (1 : AF F) = 1 := by unfold evI; exact map_one _
  rw [h1, trace_baseChange_tmul', h2, map_add, map_one, one_mul, evI_add, h3, map_add,
    ← map_one (algebraMap ℝ (mixedEmbedding.mixedSpace F)), Algebra.trace_algebraMap, mixedEmbedding.finrank]
  have : 0 < Module.finrank ℚ F := Module.finrank_pos
  simp only [nsmul_eq_mul, mul_one]
  positivity

end GlobalTheory.RealFreq

namespace GlobalTheory.RealFreq
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
open Matrix

/- English proof (translation)
Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem det_ne_zero_of_sig {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (r s : ℕ) (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hrs)
  have hD : (A.submatrix id e.symm)ᵀ * M * (A.map star).submatrix id e.symm =
      (Aᵀ * M * A.map star).submatrix e.symm e.symm := by
    rw [Matrix.transpose_submatrix]
    calc _ = Aᵀ.submatrix e.symm id * M.submatrix id id * (A.map star).submatrix id e.symm := by
          rw [Matrix.submatrix_id_id]
      _ = _ := by
          rw [Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id]
  rw [hA] at hD
  intro h0
  have := congrArg Matrix.det hD
  rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero, zero_mul, Matrix.det_submatrix_equiv_self,
    Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul, Matrix.det_neg, Matrix.det_one, mul_one] at this
  exact pow_ne_zero _ (by norm_num) this.symm

/- English proof (translation)
Replace the relevant objects with their definitions. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem form_swap (σ : E →ₐ[F] E) (hσ : ∀ z, σ (σ z) = z) {d : ℕ} (J : Matrix (Fin d) (Fin d) E)
    (hskew : ∀ i j, σ (J j i) = -J i j) (x y : Fin d → E) : form σ J y x = -σ (form σ J x y) := by
  unfold form
  simp only [dotProduct, mulVec, map_sum, map_mul, hσ, hskew, Finset.mul_sum, neg_mul, mul_neg,
    Finset.sum_neg_distrib, neg_neg]
  exact Finset.sum_comm.trans (Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => by ring)

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. By extensionality, compare the relevant components. Consider separately whether the proposition holds or fails.

Substitute using the available equality. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem form_single (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ξ : Fin n → E) (k : Fin n) (c : E) :
    form σ J ξ (Pi.single k c) = (ξ ᵥ* J) k * σ c := by
  unfold form
  rw [Matrix.dotProduct_mulVec]
  have : (fun i => σ ((Pi.single k c : Fin n → E) i)) = Pi.single k (σ c) := by
    ext i; by_cases h : i = k
    · subst h; simp
    · simp [h]
  rw [this, dotProduct_single]

end GlobalTheory.RealFreq

namespace GlobalTheory.RealFreq
open Matrix

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions.

Rewrite the conclusion using the stated equalities. Introduce a local definition for the expression. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Express the relevant assertion in an equivalent form by its definition. Rewrite the indicated hypotheses using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Simplify using the standard rewrite rules. Move the embeddings inside the algebraic operations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Expand and normalize the polynomial expressions, which then agree.

A detailed English derivation is pending.
-/
theorem injective_real_frequencies : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (W₁ : Spc F E d₁) (M : Model σ X W) (H' : Plane E d d₁) (i₀ i₁ : ℕ),
    H'.IsAdapted σ B W W₁ i₀ i₁ → B.IsGood σ → M.IsGood B.ψ → (∃ r s r' s' : ℕ, X.IsHerm σ B r s ∧ W.IsSkew σ B r' s') →
    ∃ (N : ℕ) (emb : (Fin N → ℝ) → (Fin n → AE F E)) (lam : (Fin n → E) → Fin N → ℝ), Function.Injective lam ∧
      ∀ (ξ : Fin n → E) (t : Fin N → ℝ),
        B.ψ ((M.co.e (Matrix.vecMulVec (incV F ξ) (incV F H'.y))).1 ⬝ᵥ (M.co.e (Matrix.vecMulVec (emb t) (incV F H'.x))).2 -
          (M.co.e (Matrix.vecMulVec (emb t) (incV F H'.x))).1 ⬝ᵥ (M.co.e (Matrix.vecMulVec (incV F ξ) (incV F H'.y))).2) =
        Complex.exp (2 * Real.pi * Complex.I * ∑ j, (lam ξ j : ℂ) * (t j : ℂ)) := by
  intro F E _ _ _ _ _ σ B n d d₁ X W W₁ M H' i₀ i₁ hH hB _ hsig
  obtain ⟨r, s, r', s', hX, hW⟩ := hsig
  have hcm := hB.cm
  have hne : Nonempty (NumberField.InfinitePlace F) := inferInstance
  obtain ⟨w⟩ := hne
  have hσ : ∀ z : E, σ (σ z) = z := by
    intro z
    apply (B.emb w).1.injective
    rw [hcm.2.2.2, hcm.2.2.2, star_star]
  have hyx : form σ W.J H'.y H'.x = -1 := by
    rw [form_swap σ hσ W.J hW.skew, hH.xy, map_one]
  have hdet : X.J.det ≠ 0 := by
    intro h0
    apply det_ne_zero_of_sig _ r s (hX.sig w)
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
  let b := Module.finBasis ℚ (Fin n → E)
  refine ⟨Module.finrank ℚ (Fin n → E), fun t => ∑ j, realAd F (t j) • incV F (b j),
    fun ξ j => -(realTr F (form σ X.J ξ (b j))), ?_, ?_⟩
  · intro ξ ξ' hξ
    by_contra hne
    have hz : ∀ j, realTr F (form σ X.J (ξ - ξ') (b j)) = 0 := by
      intro j
      have := congrFun hξ j
      simp only [neg_inj] at this
      rw [form, sub_dotProduct, map_sub]
      unfold form at this
      rw [this, sub_self]
    let L : (Fin n → E) →+ ℝ := (realTr F).comp
      { toFun := form σ X.J (ξ - ξ')
        map_zero' := by
          unfold form
          rw [show (fun i => σ ((0 : Fin n → E) i)) = 0 from funext fun i => map_zero σ, Matrix.mulVec_zero,
            dotProduct_zero]
        map_add' := fun u v => by
          unfold form
          rw [show (fun i => σ ((u + v) i)) = (fun i => σ (u i)) + (fun i => σ (v i)) from funext fun i => map_add σ _ _,
            Matrix.mulVec_add, dotProduct_add] }
    have hL : L.toRatLinearMap = 0 := b.ext fun j => hz j
    have hw : (ξ - ξ') ᵥ* X.J ≠ 0 := by
      intro h0
      apply hne
      have := Matrix.vecMul_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).2 (Ne.isUnit hdet))
        (h0.trans (Matrix.zero_vecMul _).symm)
      exact sub_eq_zero.1 this
    obtain ⟨k, hk⟩ := Function.ne_iff.1 hw
    have h1 : form σ X.J (ξ - ξ') (Pi.single k (σ ((((ξ - ξ') ᵥ* X.J) k)⁻¹))) = 1 := by
      rw [form_single, hσ]
      exact mul_inv_cancel₀ hk
    have h2 := LinearMap.congr_fun hL (Pi.single k (σ ((((ξ - ξ') ᵥ* X.J) k)⁻¹)))
    change realTr F (form σ X.J (ξ - ξ') _) = 0 at h2
    rw [h1] at h2
    exact realTr_one_ne hcm.2.2.1 h2
  · intro ξ t
    rw [← M.co.form, symp_freq σ X.J W.J ξ H'.y H'.x hyx b t, psi_freq B.ψ hB.std]
    congr 1
    simp only [realTr_apply]
    push_cast
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring

end GlobalTheory.RealFreq
