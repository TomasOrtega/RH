import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.TsgPolyVolPolyCoeffEven
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreLocal
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagHeightPolynomialWeightForm
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagVarietyAnalyticSystemExistsStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagVarietyBoundaryDimensionDropStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.WeightMapAntisymmetricDeltaIdentityStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RealisationPotentialDegreeCompatibilityStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.UniformisedDegreePolynomialAntisymmetricStatement
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB

namespace TopProp

open FlLines

/- English proof (translation)
Use `formPoly_eq_toWt _ _ _ fun lam => ?_` and prove the remaining obligations. Use `set S : Set (Ideal (MRing (FlIdx Ψ N))) := divSupp (PFl Ψ N) (C (((2 : ℕ) : ℤ))) with hSdef`. Establish `hS : S.Finite` using `divSupp_finite _ _`. Use `set m : Ideal (MRing (FlIdx Ψ N)) → ℝ := fun V => (multAt (PFl Ψ N ⊔ Ideal.span {C (((2 : ℕ) : ℤ))}) V : ℝ) with hm`. Establish `hD : ∀ L : Fin (antisymDegree Ψ N) → HermLine (FlIdx Ψ N), (∀ j, IsSmoothHerm (L j)) → ptsIntegral (PFl Ψ N) (pot L) (fun _ => 1) = ∑ᶠ V ∈ S, m V * (geoNum _ V (fun j => (L j).a) : ℝ)` using `fun L hL => hIn.degree _ _ _ _ L 2 hP hL Nat.prime_two`.

Establish `hsm : ∀ a : FlBlock Ψ N → ℤ, IsSmoothHerm (fsHerm (FlIdx Ψ N) a)` using `FlagHeightMultilinear.isSmoothHerm_fsHerm`. Establish `h1` using `degSum_polar (antisymDegree Ψ N) S hS m lam (xDeg Ψ N)`. Establish `h2` using `degSum_polar (antisymDegree Ψ N) S hS m (gapZ lam) (yDeg Ψ N)`. Establish `hv : (fun (_ : Fin (antisymDegree Ψ N)) k => ∑ a, lam a * xDeg Ψ N a k) = fun _ k => ∑ a, gapZ lam a * yDeg Ψ N a k`. Use function extensionality and compare the values at `_ k`.

Conclude with `deg_abel lam k`. Rewrite `h1` using `[hv, ← h2]`. Establish `ex : ∀ w : Fin (antisymDegree Ψ N) → Ψ × Fin N, ptsIntegral (PFl Ψ N) (pot fun r => xLine Ψ N (w r)) (fun _ => 1) = ∑ᶠ V ∈ S, m V * (geoNum _ V (fun r => xDeg Ψ N (w r)) : ℝ)` using `fun w => hD _ fun _ => hsm _`. Establish `ey : ∀ w : Fin (antisymDegree Ψ N) → Ψ × Fin N, ptsIntegral (PFl Ψ N) (pot fun r => yLineFl Ψ N (w r)) (fun _ => 1) = ∑ᶠ V ∈ S, m V * (geoNum _ V (fun r => yDeg Ψ N (w r)) : ℝ)` using `fun w => hD _ fun _ => hsm _`. Simplify using `only [ex, ey]`.

Conclude with `h1`.
-/
theorem degFl_yLines (hIn : Inputs) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ)
    (hP : IsArithVar (PFl Ψ N) (antisymDegree Ψ N + 1)) :
    degFlPoly Ψ N = toWt (formPoly (antisymDegree Ψ N) fun w =>
      ptsIntegral (PFl Ψ N) (pot fun r => yLineFl Ψ N (w r)) fun _ => 1) := by
  refine formPoly_eq_toWt _ _ _ fun lam => ?_
  set S : Set (Ideal (MRing (FlIdx Ψ N))) := divSupp (PFl Ψ N) (C (((2 : ℕ) : ℤ))) with hSdef
  have hS : S.Finite := divSupp_finite _ _
  set m : Ideal (MRing (FlIdx Ψ N)) → ℝ :=
    fun V => (multAt (PFl Ψ N ⊔ Ideal.span {C (((2 : ℕ) : ℤ))}) V : ℝ) with hm
  have hD : ∀ L : Fin (antisymDegree Ψ N) → HermLine (FlIdx Ψ N), (∀ j, IsSmoothHerm (L j)) →
      ptsIntegral (PFl Ψ N) (pot L) (fun _ => 1) = ∑ᶠ V ∈ S, m V * (geoNum _ V (fun j => (L j).a) : ℝ) :=
    fun L hL => hIn.degree _ _ _ _ L 2 hP hL Nat.prime_two
  have hsm : ∀ a : FlBlock Ψ N → ℤ, IsSmoothHerm (fsHerm (FlIdx Ψ N) a) :=
    FlagHeightMultilinear.isSmoothHerm_fsHerm
  have h1 := degSum_polar (antisymDegree Ψ N) S hS m lam (xDeg Ψ N)
  have h2 := degSum_polar (antisymDegree Ψ N) S hS m (gapZ lam) (yDeg Ψ N)
  have hv : (fun (_ : Fin (antisymDegree Ψ N)) k => ∑ a, lam a * xDeg Ψ N a k) =
      fun _ k => ∑ a, gapZ lam a * yDeg Ψ N a k := by
    funext _ k
    exact deg_abel lam k
  rw [hv, ← h2] at h1
  have ex : ∀ w : Fin (antisymDegree Ψ N) → Ψ × Fin N,
      ptsIntegral (PFl Ψ N) (pot fun r => xLine Ψ N (w r)) (fun _ => 1) =
        ∑ᶠ V ∈ S, m V * (geoNum _ V (fun r => xDeg Ψ N (w r)) : ℝ) :=
    fun w => hD _ fun _ => hsm _
  have ey : ∀ w : Fin (antisymDegree Ψ N) → Ψ × Fin N,
      ptsIntegral (PFl Ψ N) (pot fun r => yLineFl Ψ N (w r)) (fun _ => 1) =
        ∑ᶠ V ∈ S, m V * (geoNum _ V (fun r => yDeg Ψ N (w r)) : ℝ) :=
    fun w => hD _ fun _ => hsm _
  simp only [ex, ey]
  exact h1

/- English proof (translation)
Take `⟨d, S₀, Re, hd, hdeg, href, -, ⟨F⟩⟩` from `GlobalTheory.T.flag_variety_analytic_system_exists hIn Ψ N hN`. Establish `hP` using `(GlobalTheory.T.flag_variety_boundary_dimension_drop Ψ N hN).1`. Establish `hR` using `GlobalTheory.T.realisation_potential_degree_compatibility hIn.2.1.1 _ _ _ _ S₀ _ Re`. Establish `hw : ∀ w : Fin (d + 1) → Ψ × Fin N, ptsIntegral (PFl Ψ N) (pot fun r => yLineFl Ψ N (w r)) (fun _ => 1) = S₀.degNum w`. Introduce `w`.

Use `hR.2.1 w` as an intermediate fact. Simplify using `only [href, hdeg] at this`. Simplify using `using this`. Use `⟨d, S₀, hd, F.unif, ?_⟩` and prove the remaining obligations. Rewrite using `[degFl_yLines hIn Ψ N hP, AnSys.degPoly]`.

Use `congr 1`. Rewrite using `[← hd]`. Use `congr 1`. Use function extensionality and compare the values at `w`. Conclude with `hw w`.
-/
theorem degFl_eq (hIn : Inputs) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] [Nonempty Ψ] (N : ℕ) (hN : 2 ≤ N) :
    ∃ (d : ℕ) (S₀ : AnSys (d + 1) (Ψ × Fin N)), d + 1 = antisymDegree Ψ N ∧
      IsUniformised S₀.A S₀.open' N S₀.potH ∧ degFlPoly Ψ N = toWt S₀.degPoly := by
  obtain ⟨d, S₀, Re, hd, hdeg, href, -, ⟨F⟩⟩ := GlobalTheory.T.flag_variety_analytic_system_exists hIn Ψ N hN
  have hP := (GlobalTheory.T.flag_variety_boundary_dimension_drop Ψ N hN).1
  have hR := GlobalTheory.T.realisation_potential_degree_compatibility hIn.2.1.1 _ _ _ _ S₀ _ Re
  have hw : ∀ w : Fin (d + 1) → Ψ × Fin N,
      ptsIntegral (PFl Ψ N) (pot fun r => yLineFl Ψ N (w r)) (fun _ => 1) = S₀.degNum w := by
    intro w
    have := hR.2.1 w
    simp only [href, hdeg] at this
    simpa using this
  refine ⟨d, S₀, hd, F.unif, ?_⟩
  rw [degFl_yLines hIn Ψ N hP, AnSys.degPoly]
  congr 1
  rw [← hd]
  congr 1
  funext w
  exact hw w

end TopProp

open TopProp

/- English proof (translation)
Introduce `hIn Ψ _ _ _ N j hN hj`. Take `⟨d, S₀, hd, hU₀, hfl⟩` from `degFl_eq hIn Ψ N hN`. Take `⟨c, hc, hc'⟩` from `GlobalTheory.T.uniformised_degree_polynomial_antisymmetric hIn Ψ N N (d + 1) S₀ le_rfl hd hU₀`. Establish `hΔ : 0 < eval (rhoWt Ψ N) (antisymDelta Ψ N)` using `(GlobalTheory.T.vandermonde_product_weight_positive Ψ N (∏ τ : Ψ, ∏ i : Fin N, ∏ l ∈ Finset.Ioi i, ∑ m ∈ Finset.Ico i l, X (τ, m)) 1 (fun c => by simp [map_prod, map_sum])).2`. Establish `hfl' : degFlPoly Ψ N = C c * antisymDelta Ψ N` using `hfl.trans hc'`.

Use `⟨⟨c, hc, hfl'⟩, fun D S hD hU => ?_⟩` and prove the remaining obligations. Take `⟨v, hv, hv'⟩` from `GlobalTheory.T.uniformised_degree_polynomial_antisymmetric hIn Ψ N j D S hj hD hU`. Establish `hvol : volOf S = v / c`. Unfold `volOf`. Rewrite using `[hv', hfl', eval_mul, eval_mul, eval_C, eval_C]`.

Clear the denominators using the available nonvanishing facts. Use `⟨hvol ▸ div_pos hv hc, ?_⟩` and prove the remaining obligations. Rewrite using `[hvol, hv', hfl', ← mul_assoc, ← C_mul, div_mul_cancel₀ _ hc.ne']`.
-/
theorem proportional : Proportional := by
  intro hIn Ψ _ _ _ N j hN hj
  obtain ⟨d, S₀, hd, hU₀, hfl⟩ := degFl_eq hIn Ψ N hN
  obtain ⟨c, hc, hc'⟩ := GlobalTheory.T.uniformised_degree_polynomial_antisymmetric hIn Ψ N N (d + 1) S₀ le_rfl hd hU₀
  have hΔ : 0 < eval (rhoWt Ψ N) (antisymDelta Ψ N) :=
    (GlobalTheory.T.vandermonde_product_weight_positive Ψ N (∏ τ : Ψ, ∏ i : Fin N, ∏ l ∈ Finset.Ioi i, ∑ m ∈ Finset.Ico i l, X (τ, m)) 1
      (fun c => by simp [map_prod, map_sum])).2
  have hfl' : degFlPoly Ψ N = C c * antisymDelta Ψ N := hfl.trans hc'
  refine ⟨⟨c, hc, hfl'⟩, fun D S hD hU => ?_⟩
  obtain ⟨v, hv, hv'⟩ := GlobalTheory.T.uniformised_degree_polynomial_antisymmetric hIn Ψ N j D S hj hD hU
  have hvol : volOf S = v / c := by
    unfold volOf
    rw [hv', hfl', eval_mul, eval_mul, eval_C, eval_C]
    field_simp
  refine ⟨hvol ▸ div_pos hv hc, ?_⟩
  rw [hvol, hv', hfl', ← mul_assoc, ← C_mul, div_mul_cancel₀ _ hc.ne']

end GlobalTheory.CompanionTheory.Ar.PB
