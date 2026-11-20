import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import GroundTheory.HeightsAndTheta.Heights.Regularisation.BoundedStatements
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PHermExtend

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Introduce `K _ J _ a`. Set `S : K → ((k : K) × J k → ℂ) → ℝ` to `fun k z => ∑ i, ‖z ⟨k, i⟩‖ ^ 2`. Establish `hS0 : ∀ k z, 0 ≤ S k z` using `fun k z => Finset.sum_nonneg fun i _ => by positivity`. Establish `hSpos : ∀ k (z : (k : K) × J k → ℂ), (∃ i, z ⟨k, i⟩ ≠ 0) → 0 < S k z`. Introduce and unpack `k z ⟨i, hi⟩`.

Conclude with `lt_of_lt_of_le (pow_pos (norm_pos_iff.mpr hi) 2) (Finset.single_le_sum (f := fun i => ‖z ⟨k, i⟩‖ ^ 2) (fun j _ => by positivity) (Finset.mem_univ i))`. Establish `hSmul : ∀ (c : K → ℂ) k (z : (k : K) × J k → ℂ), S k (fun p => c p.1 * z p) = ‖c k‖ ^ 2 * S k z`. Introduce `c k z`. Simplify using `only [S, norm_mul, mul_pow, Finset.mul_sum]`. Use `⟨⟨a, fun z => ∏ k, S k z ^ ((a k : ℝ) / 2), ?_, ?_⟩, rfl, ?_, ?_⟩` and prove the remaining obligations.

Introduce `z hz`. Conclude with `Finset.prod_pos fun k _ => Real.rpow_pos_of_pos (hSpos k z (hz k)) _`. Introduce `c z hc show ∏ k, S k (fun p => c p.1 * z p) ^ ((a k : ℝ) / 2) = _`. Simplify using `only [hSmul]`. Rewrite using `[← Finset.prod_mul_distrib]`.

Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Real.mul_rpow (by positivity) (hS0 k z)]`. Use `congr 1`. Rewrite using `[← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), ← Real.rpow_intCast]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `show ContDiffOn ℝ _ (fun z => ∏ k, S k z ^ ((a k : ℝ) / 2)) _`. Apply `contDiffOn_prod` to reduce the goal to its premises. Introduce `k _ z hz`.

Conclude with `((ContDiff.sum fun i _ => (contDiff_norm_sq ℝ).comp (contDiff_apply ℝ ℂ _)).contDiffAt.rpow_const_of_ne (hSpos k z (hz k)).ne').contDiffWithinAt`. Introduce `z`. Simplify using `[S]`.
-/
theorem _root_.GlobalTheory.CompanionTheory.Relay.exists_smooth_conj_invariant_metric : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (a : K → ℤ), ∃ A : HermLine J, A.a = a ∧ IsSmoothHerm A ∧ IsConjInvariantH A := by
  intro K _ J _ a
  let S : K → ((k : K) × J k → ℂ) → ℝ := fun k z => ∑ i, ‖z ⟨k, i⟩‖ ^ 2
  have hS0 : ∀ k z, 0 ≤ S k z := fun k z => Finset.sum_nonneg fun i _ => by positivity
  have hSpos : ∀ k (z : (k : K) × J k → ℂ), (∃ i, z ⟨k, i⟩ ≠ 0) → 0 < S k z := by
    rintro k z ⟨i, hi⟩
    exact lt_of_lt_of_le (pow_pos (norm_pos_iff.mpr hi) 2)
      (Finset.single_le_sum (f := fun i => ‖z ⟨k, i⟩‖ ^ 2) (fun j _ => by positivity) (Finset.mem_univ i))
  have hSmul : ∀ (c : K → ℂ) k (z : (k : K) × J k → ℂ), S k (fun p => c p.1 * z p) = ‖c k‖ ^ 2 * S k z := by
    intro c k z
    simp only [S, norm_mul, mul_pow, Finset.mul_sum]
  refine ⟨⟨a, fun z => ∏ k, S k z ^ ((a k : ℝ) / 2), ?_, ?_⟩, rfl, ?_, ?_⟩
  · intro z hz
    exact Finset.prod_pos fun k _ => Real.rpow_pos_of_pos (hSpos k z (hz k)) _
  · intro c z hc
    show ∏ k, S k (fun p => c p.1 * z p) ^ ((a k : ℝ) / 2) = _
    simp only [hSmul]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Real.mul_rpow (by positivity) (hS0 k z)]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), ← Real.rpow_intCast]
    congr 1
    push_cast
    ring
  · show ContDiffOn ℝ _ (fun z => ∏ k, S k z ^ ((a k : ℝ) / 2)) _
    apply contDiffOn_prod
    intro k _ z hz
    exact ((ContDiff.sum fun i _ => (contDiff_norm_sq ℝ).comp (contDiff_apply ℝ ℂ _)).contDiffAt.rpow_const_of_ne
      (hSpos k z (hz k)).ne').contDiffWithinAt
  · intro z
    simp [S]
