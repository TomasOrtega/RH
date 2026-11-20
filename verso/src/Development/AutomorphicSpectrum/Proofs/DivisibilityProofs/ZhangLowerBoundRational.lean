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
Introduce `hZ1 II hII Ψ _ N M t lam s e hrat hsemi hnef hpts`. Take `⟨q, n, hq, hn⟩` from `GlobalTheory.T.rational_weight_integral_coeffs Ψ N M lam s hrat`. Establish `hp` using `GlobalTheory.T.root_model_semipositive_conj Ψ N M t lam s q n hn hsemi`. Establish `hnf` using `(GlobalTheory.T.root_model_curve_degree_nef Ψ N M t lam s q n hn).2 hnef`. Establish `hW : ∀ W, IsArithVar W 1 → M.P ≤ W → ((q : ℝ) * e) * degC W ≤ II M.K M.ι W 1 ![combLine (M.line t) n]`.

Introduce `W h1 h2`. Establish `hpt : M.IsPt W` using `⟨h1, h2⟩`. Take `⟨hd, hI⟩` from `GlobalTheory.T.root_model_point_height_degree II hII Ψ N M t lam s q n W hn hpt`. Rewrite using `[hI]`. Establish `hq' : (0 : ℝ) ≤ q` using `Nat.cast_nonneg q`.

Establish `hd' : (0 : ℝ) ≤ degC W` using `Nat.cast_nonneg _`. Conclude with `mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hpts W hpt) hq') hd'`. Establish `key` using `hZ1 M.K M.ι M.P M.P (dimFl Ψ N) (combLine (M.line t) n) ((q : ℝ) * e) II hII.1 M.arith le_rfl hp.1 hnf hp.2 hW`. Establish `hgeo : geomDeg M.P (combLine (M.line t) n) (dimFl Ψ N) = (M.δ : ℝ) * (q : ℝ) ^ dimFl Ψ N * M.geoFun (linA lam s ^ dimFl Ψ N)`. Use `GlobalTheory.T.root_model_log_integral_formula II hII Ψ N M t (fun _ => lam) (fun _ => (s : ℝ)) q (fun _ => n) (fun _ j => hn j)` as an intermediate fact.

Simplify `this` using `[geomDeg, Finset.prod_const]`. Rewrite `key` using `[hgeo, GlobalTheory.T.root_model_arith_intersection_formula II hII Ψ N M t lam s q n hn]`. Establish `hδ : (0 : ℝ) < M.δ` using `by exact_mod_cast M.δ_pos`. Establish `hq0 : (0 : ℝ) < q` using `by exact_mod_cast hq`. Establish `hc : (0 : ℝ) < (M.δ : ℝ) * (q : ℝ) ^ (dimFl Ψ N + 1)` using `by positivity`.

Use `le_of_mul_le_mul_left ?_ hc` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem zhang_lower_bound_root_model : SuccessiveMinimaLowerBound → ∀ II : IntersectionSystem, IsFullIntersectionSystem II →
    ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N) (t : ℝ) (lam : Wt Ψ N) (s : ℚ) (e : ℝ), IsRatWt lam →
      M.Semipos t lam s → M.NefFib lam s → (∀ W, M.IsPt W → e ≤ M.ht II t lam s W) →
      ((dimFl Ψ N : ℝ) + 1) * e * M.geoFun (linA lam s ^ dimFl Ψ N) ≤
        M.arFun II t (linA lam s ^ (dimFl Ψ N + 1)) := by
  intro hZ1 II hII Ψ _ N M t lam s e hrat hsemi hnef hpts
  obtain ⟨q, n, hq, hn⟩ := GlobalTheory.T.rational_weight_integral_coeffs Ψ N M lam s hrat
  have hp := GlobalTheory.T.root_model_semipositive_conj Ψ N M t lam s q n hn hsemi
  have hnf := (GlobalTheory.T.root_model_curve_degree_nef Ψ N M t lam s q n hn).2 hnef
  have hW : ∀ W, IsArithVar W 1 → M.P ≤ W →
      ((q : ℝ) * e) * degC W ≤ II M.K M.ι W 1 ![combLine (M.line t) n] := by
    intro W h1 h2
    have hpt : M.IsPt W := ⟨h1, h2⟩
    obtain ⟨hd, hI⟩ := GlobalTheory.T.root_model_point_height_degree II hII Ψ N M t lam s q n W hn hpt
    rw [hI]
    have hq' : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    have hd' : (0 : ℝ) ≤ degC W := Nat.cast_nonneg _
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hpts W hpt) hq') hd'
  have key := hZ1 M.K M.ι M.P M.P (dimFl Ψ N) (combLine (M.line t) n) ((q : ℝ) * e) II hII.1 M.arith le_rfl
    hp.1 hnf hp.2 hW
  have hgeo : geomDeg M.P (combLine (M.line t) n) (dimFl Ψ N) =
      (M.δ : ℝ) * (q : ℝ) ^ dimFl Ψ N * M.geoFun (linA lam s ^ dimFl Ψ N) := by
    have := GlobalTheory.T.root_model_log_integral_formula II hII Ψ N M t (fun _ => lam) (fun _ => (s : ℝ)) q (fun _ => n) (fun _ j => hn j)
    simpa [geomDeg, Finset.prod_const] using this
  rw [hgeo, GlobalTheory.T.root_model_arith_intersection_formula II hII Ψ N M t lam s q n hn] at key
  have hδ : (0 : ℝ) < M.δ := by exact_mod_cast M.δ_pos
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hc : (0 : ℝ) < (M.δ : ℝ) * (q : ℝ) ^ (dimFl Ψ N + 1) := by positivity
  refine le_of_mul_le_mul_left ?_ hc
  calc (M.δ : ℝ) * (q : ℝ) ^ (dimFl Ψ N + 1) * (((dimFl Ψ N : ℝ) + 1) * e * M.geoFun (linA lam s ^ dimFl Ψ N))
      = ((dimFl Ψ N + 1 : ℕ) : ℝ) * ((q : ℝ) * e) *
          ((M.δ : ℝ) * (q : ℝ) ^ dimFl Ψ N * M.geoFun (linA lam s ^ dimFl Ψ N)) := by
        push_cast; ring
    _ ≤ _ := key

end GlobalTheory.CompanionTheory.Ar.Top
