import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.KleimanSt
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootModelArithIntersectionFormulaStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootModelLogIntegralFormulaStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootModelPointHeightDegreeStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootModelCurveDegreeNefStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootModelSemipositiveConjStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RationalWeightIntegralCoeffsStatement

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

/- English proof (translation)
Introduce `hZ II hII Ψ _ N M t lam s e F hrat hsp hnef hF hpt`. Take `⟨q, n, hq, hn⟩` from `GlobalTheory.T.rational_weight_integral_coeffs Ψ N M lam s hrat`. Establish `hsemi` using `GlobalTheory.T.root_model_semipositive_conj Ψ N M t lam s q n hn hsp`. Establish `hnf` using `(GlobalTheory.T.root_model_curve_degree_nef Ψ N M t lam s q n hn).2 hnef`. Establish `hA` using `GlobalTheory.T.root_model_arith_intersection_formula II hII Ψ N M t lam s q n hn`.

Establish `hG` using `GlobalTheory.T.root_model_log_integral_formula II hII Ψ N M t (fun _ => lam) (fun _ => (s : ℝ)) q (fun _ => n) (fun _ j => hn j)`. Establish `hGeo : geomDeg M.P (combLine (M.line t) n) (dimFl Ψ N) = M.δ * (q : ℝ) ^ dimFl Ψ N * M.geoFun (linA lam s ^ dimFl Ψ N)`. Establish `hprod : (∏ _k : Fin (dimFl Ψ N), linA lam (s : ℝ)) = linA lam s ^ dimFl Ψ N`. Simplify using the standard rewrite rules. Rewrite `hG` using `[hprod]`.

Conclude with `hG`. Establish `key` using `hZ M.K M.ι M.P M.P (dimFl Ψ N) (combLine (M.line t) n) ((q : ℝ) * e) F II hII.1 M.arith le_rfl hsemi.1 hnf hsemi.2 (by`. Introduce `W hW`. Take `⟨hp, hle⟩` from `hpt W hW`. Take `⟨-, hI⟩` from `GlobalTheory.T.root_model_point_height_degree II hII Ψ N M t lam s q n W hn hp`.

Use `⟨hp.1, hp.2, ?_⟩` and prove the remaining obligations. Rewrite using `[hI]`. Conclude with `mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle (Nat.cast_nonneg q)) (Nat.cast_nonneg _))`. Use `hF`. Rewrite `key` using `[hA, hGeo]`.

Establish `hqR : (0 : ℝ) < q` using `Nat.cast_pos.mpr hq`. Establish `hδ : (0 : ℝ) < M.δ` using `Nat.cast_pos.mpr M.δ_pos`. Establish `hpos : (0 : ℝ) < M.δ * (q : ℝ) ^ (dimFl Ψ N + 1)` using `mul_pos hδ (pow_pos hqR _)`. Use `le_of_mul_le_mul_left ?_ hpos` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem zhang_upper_bound_root_model : SuccessiveMinimaUpperBound → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N) (t : ℝ) (lam : Wt Ψ N) (s : ℚ) (e : ℝ) (F : Set (Ideal (MRing M.ι))), IsRatWt lam → M.Semipos t lam s → M.NefFib lam s → IsZariskiDense M.P F → (∀ W ∈ F, M.IsPt W ∧ M.ht II t lam s W ≤ e) → M.arFun II t (linA lam s ^ (dimFl Ψ N + 1)) ≤ ((dimFl Ψ N : ℝ) + 1) * e * M.geoFun (linA lam s ^ dimFl Ψ N) := by
  intro hZ II hII Ψ _ N M t lam s e F hrat hsp hnef hF hpt
  obtain ⟨q, n, hq, hn⟩ := GlobalTheory.T.rational_weight_integral_coeffs Ψ N M lam s hrat
  have hsemi := GlobalTheory.T.root_model_semipositive_conj Ψ N M t lam s q n hn hsp
  have hnf := (GlobalTheory.T.root_model_curve_degree_nef Ψ N M t lam s q n hn).2 hnef
  have hA := GlobalTheory.T.root_model_arith_intersection_formula II hII Ψ N M t lam s q n hn
  have hG := GlobalTheory.T.root_model_log_integral_formula II hII Ψ N M t (fun _ => lam) (fun _ => (s : ℝ)) q (fun _ => n)
    (fun _ j => hn j)
  have hGeo : geomDeg M.P (combLine (M.line t) n) (dimFl Ψ N) =
      M.δ * (q : ℝ) ^ dimFl Ψ N * M.geoFun (linA lam s ^ dimFl Ψ N) := by
    have hprod : (∏ _k : Fin (dimFl Ψ N), linA lam (s : ℝ)) = linA lam s ^ dimFl Ψ N := by
      simp
    rw [hprod] at hG
    exact hG
  have key := hZ M.K M.ι M.P M.P (dimFl Ψ N) (combLine (M.line t) n) ((q : ℝ) * e) F II hII.1
    M.arith le_rfl hsemi.1 hnf hsemi.2
    (by
      intro W hW
      obtain ⟨hp, hle⟩ := hpt W hW
      obtain ⟨-, hI⟩ := GlobalTheory.T.root_model_point_height_degree II hII Ψ N M t lam s q n W hn hp
      refine ⟨hp.1, hp.2, ?_⟩
      rw [hI]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle (Nat.cast_nonneg q))
        (Nat.cast_nonneg _))
    hF
  rw [hA, hGeo] at key
  have hqR : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hδ : (0 : ℝ) < M.δ := Nat.cast_pos.mpr M.δ_pos
  have hpos : (0 : ℝ) < M.δ * (q : ℝ) ^ (dimFl Ψ N + 1) := mul_pos hδ (pow_pos hqR _)
  refine le_of_mul_le_mul_left ?_ hpos
  calc _ ≤ _ := key
    _ = _ := by push_cast; ring

end GlobalTheory.CompanionTheory.Ar.Top
