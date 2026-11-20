import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.EnergyAbs

noncomputable section

open MeasureTheory Measure
open scoped InnerProductSpace ComplexConjugate ENNReal

namespace Formalism.L2.S.Pv.EnergyAbs

open Formalism.L2.SG.Pf.EnergyAbs

section HS

variable {V V' : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']

/- English proof (translation)
Unfold `Formalism.L2.SG.Pf.EnergyAbs.hsA`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[ContinuousLinearMap.smul_apply, norm_smul, mul_pow]`.
-/
theorem hsA_smul (c : ℂ) (A : V' →L[ℂ] V) : hsA (c • A) = ‖c‖ ^ 2 * hsA A := by
  unfold Formalism.L2.SG.Pf.EnergyAbs.hsA
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ContinuousLinearMap.smul_apply, norm_smul, mul_pow]

/- English proof (translation)
Conclude with `(stdOrthonormalBasis ℂ E).sum_sq_norm_inner_right x`.
-/
private theorem sum_norm_inner_stdBasis_sq_eq_norm_sq {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (x : E) :
    ∑ i, ‖⟪stdOrthonormalBasis ℂ E i, x⟫_ℂ‖ ^ 2 = ‖x‖ ^ 2 := by
  exact (stdOrthonormalBasis ℂ E).sum_sq_norm_inner_right x

/- English proof (translation)
Unfold `Formalism.L2.SG.Pf.EnergyAbs.hsA`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[sum_norm_inner_stdBasis_sq_eq_norm_sq]`. Use `_ = ∑ j, ∑ i, ‖⟪stdOrthonormalBasis ℂ V' i, (ContinuousLinearMap.adjoint A) (stdOrthonormalBasis ℂ V j)⟫_ℂ‖ ^ 2 := by`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[ContinuousLinearMap.adjoint_inner_right, norm_inner_symm]`. Use `_ = ∑ j, ‖(ContinuousLinearMap.adjoint A) (stdOrthonormalBasis ℂ V j)‖ ^ 2 := by`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[sum_norm_inner_stdBasis_sq_eq_norm_sq]`.
-/
theorem hsA_eq_adjoint (A : V' →L[ℂ] V) :
    hsA A = ∑ i, ‖(ContinuousLinearMap.adjoint A) (stdOrthonormalBasis ℂ V i)‖ ^ 2 := by
  unfold Formalism.L2.SG.Pf.EnergyAbs.hsA
  calc ∑ i, ‖A (stdOrthonormalBasis ℂ V' i)‖ ^ 2
      = ∑ i, ∑ j, ‖⟪stdOrthonormalBasis ℂ V j, A (stdOrthonormalBasis ℂ V' i)⟫_ℂ‖ ^ 2 := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [sum_norm_inner_stdBasis_sq_eq_norm_sq]
    _ = ∑ j, ∑ i, ‖⟪stdOrthonormalBasis ℂ V' i,
          (ContinuousLinearMap.adjoint A) (stdOrthonormalBasis ℂ V j)⟫_ℂ‖ ^ 2 := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
        rw [ContinuousLinearMap.adjoint_inner_right, norm_inner_symm]
    _ = ∑ j, ‖(ContinuousLinearMap.adjoint A) (stdOrthonormalBasis ℂ V j)‖ ^ 2 := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [sum_norm_inner_stdBasis_sq_eq_norm_sq]

/- English proof (translation)
Establish `h` using `hU v v`. Rewrite `h` using `[inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]`. Conclude with `h` after adjusting the coercions.
-/
private theorem norm_sq_apply_of_inner_preserving {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (U : E →L[ℂ] E) (hU : ∀ a b, ⟪U a, U b⟫_ℂ = ⟪a, b⟫_ℂ) (v : E) : ‖U v‖ ^ 2 = ‖v‖ ^ 2 := by
  have h := hU v v
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  exact_mod_cast h

/- English proof (translation)
Establish `h1 : Formalism.L2.SG.Pf.EnergyAbs.hsA (U.comp (A.comp (ContinuousLinearMap.adjoint U'))) = Formalism.L2.SG.Pf.EnergyAbs.hsA (A.comp (ContinuousLinearMap.adjoint U'))`. Unfold `Formalism.L2.SG.Pf.EnergyAbs.hsA`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[ContinuousLinearMap.comp_apply]`. Conclude with `norm_sq_apply_of_inner_preserving U hU _`.

Rewrite using `[h1, hsA_eq_adjoint, hsA_eq_adjoint A]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.comp_apply]`. Conclude with `norm_sq_apply_of_inner_preserving U' hU' _`.
-/
theorem hsA_conj (U : V →L[ℂ] V) (U' : V' →L[ℂ] V') (hU : ∀ a b, ⟪U a, U b⟫_ℂ = ⟪a, b⟫_ℂ)
    (hU' : ∀ a b, ⟪U' a, U' b⟫_ℂ = ⟪a, b⟫_ℂ) (A : V' →L[ℂ] V) :
    hsA (U.comp (A.comp (ContinuousLinearMap.adjoint U'))) = hsA A := by
  have h1 : Formalism.L2.SG.Pf.EnergyAbs.hsA (U.comp (A.comp (ContinuousLinearMap.adjoint U'))) =
      Formalism.L2.SG.Pf.EnergyAbs.hsA (A.comp (ContinuousLinearMap.adjoint U')) := by
    unfold Formalism.L2.SG.Pf.EnergyAbs.hsA
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ContinuousLinearMap.comp_apply]
    exact norm_sq_apply_of_inner_preserving U hU _
  rw [h1, hsA_eq_adjoint, hsA_eq_adjoint A]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint,
    ContinuousLinearMap.comp_apply]
  exact norm_sq_apply_of_inner_preserving U' hU' _

def hsL : (V' →L[ℂ] V) →ₗ[ℂ] PiLp 2 (fun _ : Fin (Module.finrank ℂ V') => V) where
  toFun A := WithLp.toLp 2 (fun j => A (stdOrthonormalBasis ℂ V' j))
  map_add' A B := by
    ext j
    simp
  map_smul' c A := by
    ext j
    simp

def hsC : (V' →L[ℂ] V) →L[ℂ] PiLp 2 (fun _ : Fin (Module.finrank ℂ V') => V) :=
  LinearMap.toContinuousLinearMap hsL

/- English proof (translation)
Rewrite using `[PiLp.norm_eq_of_L2]`. Both sides reduce to the same expression.
-/
theorem norm_hsC (A : V' →L[ℂ] V) : ‖hsC A‖ = Real.sqrt (hsA A) := by
  rw [PiLp.norm_eq_of_L2]
  rfl

/- English proof (translation)
Repeatedly rewrite using `[← norm_hsC]`. Rewrite using `[← ContinuousLinearMap.integral_comp_comm _ hf]`. Conclude with `norm_integral_le_integral_norm _`.
-/
theorem sqrt_hsA_integral_le {α : Type*} [MeasurableSpace α] {μ : Measure α} (f : α → (V' →L[ℂ] V))
    (hf : Integrable f μ) :
    Real.sqrt (hsA (∫ x, f x ∂μ)) ≤ ∫ x, Real.sqrt (hsA (f x)) ∂μ := by
  simp_rw [← norm_hsC]
  rw [← ContinuousLinearMap.integral_comp_comm _ hf]
  exact norm_integral_le_integral_norm _

/- English proof (translation)
Repeatedly rewrite using `[← norm_hsC]`. Establish `h : hsC A = hsC B + hsC (A - B)`. Simplify using `[map_sub]`. Rewrite using `[h]`. Conclude with `norm_add_le _ _`.
-/
theorem sqrt_hsA_le_add_sub (A B : V' →L[ℂ] V) :
    Real.sqrt (hsA A) ≤ Real.sqrt (hsA B) + Real.sqrt (hsA (A - B)) := by
  simp_rw [← norm_hsC]
  have h : hsC A = hsC B + hsC (A - B) := by
    simp [map_sub]
  rw [h]
  exact norm_add_le _ _

end HS

section Rep

variable {G : Type} [Group G] [TopologicalSpace G]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH]

/- English proof (translation)
Take `⟨-, hmul, -, -⟩` from `hσ`. Rewrite using `[hmul, ContinuousLinearMap.mul_apply]`.
-/
theorem rep_mul_apply {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) (x y : G) (a : HH) :
    σ x (σ y a) = σ (x * y) a := by
  obtain ⟨-, hmul, -, -⟩ := hσ
  rw [hmul, ContinuousLinearMap.mul_apply]

end Rep

section Kernel

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsMulLeftInvariant]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH]
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

end Kernel

section Quot

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]

/- English proof (translation)
Establish `hm : Measurable (fun p : G × G => p.2⁻¹ * p.1)` using `measurable_snd.inv.mul measurable_fst`. Use extensionality with `s hs`. Rewrite using `[Measure.map_apply hm hs, Measure.prod_apply (hm hs)]`. Establish `h` using `hq (s.indicator 1) (measurable_one.indicator hs)`. Rewrite `h` using `[lintegral_indicator_one hs]`.

Rewrite using `[h]`. Use `lintegral_congr fun x => ?_` and prove the remaining obligations. Establish `hx : MeasurableSet ((fun t : G => t * x) ⁻¹' s)` using `measurable_mul_const x hs`. Establish `hx' : MeasurableSet ((fun t : G => t⁻¹ * x) ⁻¹' s)` using `(measurable_inv.mul_const x) hs`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Measure.map_apply measurable_inv hx']`. Use `congr 1`. Use extensionality with `t`. Simplify using the standard rewrite rules. Use `_ = μS ((fun t : G => t⁻¹ * x) ⁻¹' s) := by rw [hinv]`.

Use `_ = _ := rfl`.
-/
theorem quot_map_inv {μ μS ν : Measure G} [SFinite ν] [SFinite μS] (hq : IsQuot μ μS ν)
    (hinv : μS.map (fun x => x⁻¹) = μS) :
    μ = (ν.prod μS).map (fun p => p.2⁻¹ * p.1) := by
  have hm : Measurable (fun p : G × G => p.2⁻¹ * p.1) := measurable_snd.inv.mul measurable_fst
  ext s hs
  rw [Measure.map_apply hm hs, Measure.prod_apply (hm hs)]
  have h := hq (s.indicator 1) (measurable_one.indicator hs)
  rw [lintegral_indicator_one hs] at h
  rw [h]
  refine lintegral_congr fun x => ?_
  have hx : MeasurableSet ((fun t : G => t * x) ⁻¹' s) := measurable_mul_const x hs
  have hx' : MeasurableSet ((fun t : G => t⁻¹ * x) ⁻¹' s) := (measurable_inv.mul_const x) hs
  calc ∫⁻ t, s.indicator (1 : G → ℝ≥0∞) (t * x) ∂μS
      = ∫⁻ t, ((fun t : G => t * x) ⁻¹' s).indicator (1 : G → ℝ≥0∞) t ∂μS := rfl
    _ = μS ((fun t : G => t * x) ⁻¹' s) := lintegral_indicator_one hx
    _ = (μS.map (fun t => t⁻¹)) ((fun t : G => t⁻¹ * x) ⁻¹' s) := by
        rw [Measure.map_apply measurable_inv hx']
        congr 1
        ext t
        simp
    _ = μS ((fun t : G => t⁻¹ * x) ⁻¹' s) := by rw [hinv]
    _ = _ := rfl

end Quot

end Formalism.L2.S.Pv.EnergyAbs
