import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LogGaussNormSupportFinite
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory NumberField

noncomputable section

def ChowHeightConst.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n k : ℕ) (H : ArchData K n) (c : K), c ≠ 0 →
    chowHt H k 0 (C c : MvPolynomial (Fin k × Fin n) K) = 0

section Ball

open Matrix

variable {n : ℕ}

def ballProd (h : HermNorm n) (k : ℕ) : Set (Fin k × Fin n → ℂ) :=
  {u | ∀ i, h.norm (fun j => u (i, j)) < 1}

/- English proof (translation)
Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem continuous_hermNorm_group (h : HermNorm n) {k : ℕ} (i : Fin k) :
    Continuous fun u : Fin k × Fin n → ℂ => h.norm (fun j => u (i, j)) := by
  simp only [HermNorm.norm, Matrix.mulVec, dotProduct]
  fun_prop

/- English proof (translation)
Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem isOpen_ballProd (h : HermNorm n) (k : ℕ) : IsOpen (ballProd h k) := by
  have e : ballProd h k = ⋂ i, {u | h.norm (fun j => u (i, j)) < 1} := by
    ext u
    simp [ballProd]
  rw [e]
  exact isOpen_iInter_of_finite fun i => isOpen_lt (continuous_hermNorm_group h i) continuous_const

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem zero_mem_ballProd (h : HermNorm n) (k : ℕ) : (0 : Fin k × Fin n → ℂ) ∈ ballProd h k := by
  intro i
  have e : (fun j : Fin n => (0 : Fin k × Fin n → ℂ) (i, j)) = 0 := rfl
  rw [e]
  simp [HermNorm.norm]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Combine the linear equalities and inequalities to obtain the conclusion. Chain the equalities or inequalities of the calculation.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem norm_le_of_hermNorm_lt (h : HermNorm n) {v : Fin n → ℂ} (hv : h.norm v < 1) (j : Fin n) :
    ‖v j‖ ≤ ∑ j', ∑ l, ‖h.mat⁻¹ j' l‖ := by
  have hinv : h.mat⁻¹ * h.mat = 1 := Matrix.nonsing_inv_mul _ h.isUnit_det
  have hv' : v = h.mat⁻¹ *ᵥ (h.mat *ᵥ v) := by
    rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  have hcoord : ∀ l, ‖(h.mat *ᵥ v) l‖ ≤ 1 := by
    intro l
    have h1 : ‖(h.mat *ᵥ v) l‖ ^ 2 ≤ ∑ m, ‖(h.mat *ᵥ v) m‖ ^ 2 :=
      Finset.single_le_sum (f := fun m => ‖(h.mat *ᵥ v) m‖ ^ 2) (fun m _ => sq_nonneg _)
        (Finset.mem_univ l)
    have h2 : √(‖(h.mat *ᵥ v) l‖ ^ 2) ≤ h.norm v := Real.sqrt_le_sqrt h1
    rw [Real.sqrt_sq (norm_nonneg _)] at h2
    linarith
  calc ‖v j‖ = ‖(h.mat⁻¹ *ᵥ (h.mat *ᵥ v)) j‖ := by rw [← hv']
    _ = ‖∑ l, h.mat⁻¹ j l * (h.mat *ᵥ v) l‖ := rfl
    _ ≤ ∑ l, ‖h.mat⁻¹ j l * (h.mat *ᵥ v) l‖ := norm_sum_le _ _
    _ ≤ ∑ l, ‖h.mat⁻¹ j l‖ := by
        refine Finset.sum_le_sum fun l _ => ?_
        rw [norm_mul]
        exact mul_le_of_le_one_right (norm_nonneg _) (hcoord l)
    _ ≤ ∑ j', ∑ l, ‖h.mat⁻¹ j' l‖ :=
        Finset.single_le_sum (f := fun j' => ∑ l, ‖h.mat⁻¹ j' l‖)
          (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ j)

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. A detailed English derivation is pending.
-/
theorem isBounded_ballProd (h : HermNorm n) (k : ℕ) : Bornology.IsBounded (ballProd h k) := by
  have hR : 0 ≤ ∑ j', ∑ l, ‖h.mat⁻¹ j' l‖ :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine (Metric.isBounded_closedBall (x := (0 : Fin k × Fin n → ℂ))
    (r := ∑ j', ∑ l, ‖h.mat⁻¹ j' l‖)).subset fun u hu => ?_
  rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg hR]
  rintro ⟨i, j⟩
  exact norm_le_of_hermNorm_lt h (hu i) j

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem volume_ballProd_pos (h : HermNorm n) (k : ℕ) : 0 < volume (ballProd h k) :=
  (isOpen_ballProd h k).measure_pos volume ⟨0, zero_mem_ballProd h k⟩

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem volume_ballProd_lt_top (h : HermNorm n) (k : ℕ) : volume (ballProd h k) < ⊤ :=
  (isBounded_ballProd h k).measure_lt_top

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem sphereMean_const (h : HermNorm n) (k : ℕ) (a : ℝ) : sphereMean h k (fun _ => a) = a :=
  setAverage_const (volume_ballProd_pos h k).ne' (volume_ballProd_lt_top h k).ne a

/- English proof (translation)
Replace the relevant objects with their definitions. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem mahler_C (h : HermNorm n) (k : ℕ) (z : ℂ) :
    mahler h k (C z : MvPolynomial (Fin k × Fin n) ℂ) = Real.log ‖z‖ := by
  unfold mahler
  simp only [eval_C]
  exact sphereMean_const h k _

end Ball

section ProductFormula

variable {K : Type*} [Field K] [NumberField K]

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.
-/
theorem prod_norm_embeddings (x : K) :
    ∏ σ : K →+* ℂ, ‖σ x‖ = ((|Algebra.norm ℚ x| : ℚ) : ℝ) := by
  have h : ‖algebraMap ℚ ℂ (Algebra.norm ℚ x)‖ = ∏ σ : K →+* ℂ, ‖σ x‖ := by
    rw [Algebra.norm_eq_prod_embeddings ℚ ℂ x, norm_prod, ← Fintype.prod_equiv
      (RingHom.equivRatAlgHom K ℂ) (fun f => ‖f x‖) (fun φ => ‖φ x‖)
      fun _ => by simp [RingHom.equivRatAlgHom_apply]]
  rw [← h, eq_ratCast, ← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs, Rat.cast_abs]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem sum_log_norm_embeddings {x : K} (hx : x ≠ 0) :
    ∑ σ : K →+* ℂ, Real.log ‖σ x‖ = Real.log ((|Algebra.norm ℚ x| : ℚ) : ℝ) := by
  rw [← prod_norm_embeddings, Real.log_prod]
  intro σ _
  exact norm_ne_zero_iff.mpr ((map_ne_zero σ).mpr hx)

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.
-/
theorem finsum_log_adicAbv {x : K} (hx : x ≠ 0) :
    ∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      Real.log (NumberField.HeightOneSpectrum.adicAbv K v x) =
        -Real.log ((|Algebra.norm ℚ x| : ℚ) : ℝ) := by
  have hpos : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      0 < NumberField.HeightOneSpectrum.adicAbv K v x := fun v =>
    (NumberField.HeightOneSpectrum.adicAbv K v).pos hx
  rw [← Real.log_finprod hpos]
  have e : ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      NumberField.HeightOneSpectrum.adicAbv K v x = ∏ᶠ w : FinitePlace K, w x := by
    rw [← finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm]
    refine finprod_congr fun v => ?_
    rw [FinitePlace.equivHeightOneSpectrum_symm_apply, FinitePlace.norm_embedding]
  rw [e, FinitePlace.prod_eq_inv_abs_norm hx, Rat.cast_inv, Real.log_inv]

end ProductFormula

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Establish an intermediate fact. Simplify using the standard rewrite rules.
-/
theorem chowHeightConst : ChowHeightConst.Statement := by
  intro K _ _ n k H c hc
  unfold chowHt
  have harch : ∀ σ : K →+* ℂ,
      mahler (H.normAt σ) k ((C c : MvPolynomial (Fin k × Fin n) K).map σ) = Real.log ‖σ c‖ :=
    fun σ => by rw [map_C, mahler_C]
  simp only [harch, gaussNorm_C, Nat.cast_zero, mul_zero, zero_mul, zero_div, add_zero,
    finsum_log_adicAbv hc, sum_log_norm_embeddings hc, neg_add_cancel]

end

end GroundTheory.Heights₂.Heights
