import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrderedCechToCatCochainsOneApplyValueAtSubset
open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.ModelS.L2InnerProduct

/- English proof (translation)
Establish `hK : IsCompact (Set.pi Set.univ (fun _ : Fin n => Set.pi Set.univ (fun _ : Fin n => Metric.closedBall (0 : ℂ) 1)) : Set (Matrix (Fin n) (Fin n) ℂ))` using `isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_closedBall _ _))`. Establish `hC : IsClosed ((Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)))` using `isClosed_unitary (R := Matrix (Fin n) (Fin n) ℂ)`. Use `hK.of_isClosed_subset hC ?_` and prove the remaining obligations. Introduce `x hx`. Simplify using `only [Set.mem_pi, Set.mem_univ, true_implies, Metric.mem_closedBall, dist_zero_right]`.

Introduce `i j`. Conclude with `entry_norm_bound_of_unitary hx i j`.
-/
theorem isCompact_unitary_set (n : ℕ) :
    IsCompact ((Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ))) := by
  have hK : IsCompact (Set.pi Set.univ
      (fun _ : Fin n => Set.pi Set.univ (fun _ : Fin n => Metric.closedBall (0 : ℂ) 1)) :
        Set (Matrix (Fin n) (Fin n) ℂ)) :=
    isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_closedBall _ _))
  have hC : IsClosed ((Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ))) :=
    isClosed_unitary (R := Matrix (Fin n) (Fin n) ℂ)
  refine hK.of_isClosed_subset hC ?_
  intro x hx
  simp only [Set.mem_pi, Set.mem_univ, true_implies, Metric.mem_closedBall, dist_zero_right]
  intro i j
  exact entry_norm_bound_of_unitary hx i j

/- English proof (translation)
The claim follows from `isCompact_iff_compactSpace.mp (isCompact_unitary_set n)`.
-/
theorem compactSpace_unitary (n : ℕ) : CompactSpace (Matrix.unitaryGroup (Fin n) ℂ) :=
  isCompact_iff_compactSpace.mp (isCompact_unitary_set n)

/- English proof (translation)
The claim follows from `x.2.1.continuousOn.comp_continuous continuous_subtype_val unit_mem`.
-/
theorem continuous_restrict {n : ℕ} (x : SmF n) :
    Continuous fun k : Matrix.unitaryGroup (Fin n) ℂ => x.1 k.1 :=
  x.2.1.continuousOn.comp_continuous continuous_subtype_val unit_mem

section

variable {n : ℕ} [MeasurableSpace (Matrix.unitaryGroup (Fin n) ℂ)]
  [BorelSpace (Matrix.unitaryGroup (Fin n) ℂ)]
  (κ : Measure (Matrix.unitaryGroup (Fin n) ℂ)) [IsFiniteMeasure κ]

/- English proof (translation)
Use `haveI := compactSpace_unitary n`. Conclude with `((Complex.continuous_conj.comp (continuous_restrict x)).mul (continuous_restrict y)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)`.
-/
theorem integrable_integrand (x y : SmF n) :
    Integrable (fun k : Matrix.unitaryGroup (Fin n) ℂ => conj (x.1 k.1) * y.1 k.1) κ := by
  haveI := compactSpace_unitary n
  exact ((Complex.continuous_conj.comp (continuous_restrict x)).mul
    (continuous_restrict y)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/- English proof (translation)
Use `haveI := compactSpace_unitary n`. Conclude with `((continuous_restrict x).norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)`.
-/
theorem integrable_normSq (x : SmF n) :
    Integrable (fun k : Matrix.unitaryGroup (Fin n) ℂ => ‖x.1 k.1‖ ^ 2) κ := by
  haveI := compactSpace_unitary n
  exact ((continuous_restrict x).norm.pow 2).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/- English proof (translation)
Rewrite using `[← integral_complex_ofReal]`. Unfold `ipK`. Use `integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)` and prove the remaining obligations. Simplify using `[Complex.conj_mul']`.
-/
theorem ipK_self (x : SmF n) :
    ipK κ x x = ((∫ k, ‖x.1 k.1‖ ^ 2 ∂κ : ℝ) : ℂ) := by
  rw [← integral_complex_ofReal]
  unfold ipK
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  simp [Complex.conj_mul']

/- English proof (translation)
Unfold `ipK`. Rewrite using `[← integral_conj]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)` and prove the remaining obligations. Simplify using `[mul_comm]`.
-/
theorem ipK_conj (x y : SmF n) : conj (ipK κ y x) = ipK κ x y := by
  unfold ipK
  rw [← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  simp [mul_comm]

/- English proof (translation)
Unfold `ipK`. Rewrite using `[← integral_add (integrable_integrand κ x z) (integrable_integrand κ y z)]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)` and prove the remaining obligations. Simplify using `[add_mul]`.
-/
theorem ipK_add_left (x y z : SmF n) : ipK κ (x + y) z = ipK κ x z + ipK κ y z := by
  unfold ipK
  rw [← integral_add (integrable_integrand κ x z) (integrable_integrand κ y z)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  simp [add_mul]

/- English proof (translation)
Unfold `ipK`. Rewrite using `[← integral_const_mul]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)` and prove the remaining obligations. Simplify using `[mul_assoc]`.
-/
theorem ipK_smul_left (c : ℂ) (x y : SmF n) : ipK κ (c • x) y = conj c * ipK κ x y := by
  unfold ipK
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  simp [mul_assoc]

/- English proof (translation)
Rewrite `h` using `[ipK_self, Complex.ofReal_eq_zero]`. Establish `hae` using `(integral_eq_zero_iff_of_nonneg (fun k => by positivity) (integrable_normSq κ x)).1 h`. Establish `hc : Continuous fun k : Matrix.unitaryGroup (Fin n) ℂ => ‖x.1 k.1‖ ^ 2` using `(continuous_restrict x).norm.pow 2`. Use `(hc.ae_eq_iff_eq κ continuous_zero).1 hae` as an intermediate fact. Simplify using `using congrFun this k`.
-/
theorem eq_zero_of_ipK_self [κ.IsOpenPosMeasure] (x : SmF n) (h : ipK κ x x = 0)
    (k : Matrix.unitaryGroup (Fin n) ℂ) : x.1 k.1 = 0 := by
  rw [ipK_self, Complex.ofReal_eq_zero] at h
  have hae := (integral_eq_zero_iff_of_nonneg (fun k => by positivity) (integrable_normSq κ x)).1 h
  have hc : Continuous fun k : Matrix.unitaryGroup (Fin n) ℂ => ‖x.1 k.1‖ ^ 2 :=
    (continuous_restrict x).norm.pow 2
  have := (hc.ae_eq_iff_eq κ continuous_zero).1 hae
  simpa using congrFun this k

end

/- English proof (translation)
Introduce `n _ _ κ _ _`. Use `⟨ipK_conj κ, fun x => ?_, ipK_add_left κ, ipK_smul_left κ, eq_zero_of_ipK_self κ⟩` and prove the remaining obligations. Rewrite using `[ipK_self, Complex.ofReal_re]`. Conclude with `integral_nonneg fun k => by positivity`.
-/
theorem ipK_form : ∀ (n : ℕ) [MeasurableSpace (Matrix.unitaryGroup (Fin n) ℂ)] [BorelSpace (Matrix.unitaryGroup (Fin n) ℂ)] (κ : Measure (Matrix.unitaryGroup (Fin n) ℂ)) [IsFiniteMeasure κ] [κ.IsOpenPosMeasure], (∀ x y : GlobalTheory.CompanionTheory.ModelS.SmF n, conj (GlobalTheory.CompanionTheory.ModelS.ipK κ y x) = GlobalTheory.CompanionTheory.ModelS.ipK κ x y) ∧ (∀ x : GlobalTheory.CompanionTheory.ModelS.SmF n, 0 ≤ (GlobalTheory.CompanionTheory.ModelS.ipK κ x x).re) ∧ (∀ x y z : GlobalTheory.CompanionTheory.ModelS.SmF n, GlobalTheory.CompanionTheory.ModelS.ipK κ (x + y) z = GlobalTheory.CompanionTheory.ModelS.ipK κ x z + GlobalTheory.CompanionTheory.ModelS.ipK κ y z) ∧ (∀ (c : ℂ) (x y : GlobalTheory.CompanionTheory.ModelS.SmF n), GlobalTheory.CompanionTheory.ModelS.ipK κ (c • x) y = conj c * GlobalTheory.CompanionTheory.ModelS.ipK κ x y) ∧ ∀ x : GlobalTheory.CompanionTheory.ModelS.SmF n, GlobalTheory.CompanionTheory.ModelS.ipK κ x x = 0 → ∀ k : Matrix.unitaryGroup (Fin n) ℂ, x.1 k.1 = 0 := by
  intro n _ _ κ _ _
  refine ⟨ipK_conj κ, fun x => ?_, ipK_add_left κ, ipK_smul_left κ, eq_zero_of_ipK_self κ⟩
  rw [ipK_self, Complex.ofReal_re]
  exact integral_nonneg fun k => by positivity

end GlobalTheory.CompanionTheory.ModelS.L2InnerProduct
