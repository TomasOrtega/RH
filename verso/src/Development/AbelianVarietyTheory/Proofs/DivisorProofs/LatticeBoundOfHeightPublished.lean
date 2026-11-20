import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValVwProdLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateInclusionRaynaudExtensionAlgebraicPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateLatticeSpanStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicDiscriminantDualBasisBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTatePointDualBasisStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.EigenSplit GlobalTheory.Frames GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovHt GlobalTheory.CovTop
attribute [local instance] Over.cartesianMonoidalCategory

attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.CovHt.HTLatB

/- English proof (translation)
Introduce `_ E _ _ _ _ H`. Use `letI := H.starRing`. Introduce `Dw l Xo c p _ _ T io y₀ hy k kO P ψ hP τ w hw hs a ha`. Establish `hp : p.Prime` using `Fact.out`. Establish `hp1 : (1 : ℝ) < p` using `by exact_mod_cast hp.one_lt`.

Establish `hHT : HTChar p (Valued.v : Valuation ℂ_[p] ℝ≥0) P.Gt` using `htChar_of_pointOver E H Dw l Xo c p ℂ_[p] _ 𝓞_ℂ_[p] T io y₀ hy k kO P ψ hP`. Use `set x : ℝ := (padicValNat p (discr E).natAbs : ℝ) / (Module.finrank ℚ E : ℝ) with hx`. Establish `hx0 : 0 ≤ x` using `by positivity`. Take `⟨d, hd, hdw⟩ : ∃ d : ℂ_[p], (p : ℝ) ^ (-x) ≤ ‖d‖ ∧ d • w ∈ P.latT` from `by classical`. Distinguish the cases in `hτ : τ (H.rt : E) = H.rt0`.

Take `⟨d, n, r, b, hd, hsum⟩` from `GlobalTheory.T.padic_discriminant_dual_basis_bound E p (embAt c ℂ_[p] τ)`. Use `⟨d, hd, GlobalTheory.T.hodge_tate_point_dual_basis P _ d r b hsum ?_⟩` and prove the remaining obligations. Unfold `htLat at hw`. Rewrite `hw` using `[if_pos hτ]`. Use `hw` and compare the differences between its conclusion and the goal.

Use `⟨1, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[norm_one]`. Conclude with `Real.rpow_le_one_of_one_le_of_nonpos hp1.le (neg_nonpos.2 hx0)`. Unfold `htLat at hw`. Rewrite `hw` using `[if_neg hτ]`.

Rewrite using `[one_smul]`. Conclude with `hw.1`. Take `⟨c0, hc0⟩` from `IsAlgClosed.exists_pow_nat_eq (p : ℂ_[p]) (n := p - 1) (by have := hp.two_le; omega)`. Establish `hpn : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1`. Rewrite using `[Nat.cast_sub hp.one_le, Nat.cast_one]`.

Establish `hc0n : ‖c0‖ = (p : ℝ) ^ (-(1 / ((p : ℝ) - 1)))`. Establish `h1 : ‖c0‖ ^ (p - 1) = (p : ℝ)⁻¹` using `by rw [← norm_pow, hc0, GlobalTheory.PadicComplexHost.norm_p]`. Establish `h2` using `Real.pow_rpow_inv_natCast (norm_nonneg c0) (n := p - 1) (by have := hp.two_le; omega)`. Rewrite `h2` using `[h1, hpn, Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity)]`. Rewrite using `[one_div]`.

Conclude with `h2.symm`. Establish `hc0le : ‖c0‖ ≤ 1`. Rewrite using `[hc0n]`. Use `Real.rpow_le_one_of_one_le_of_nonpos hp1.le (neg_nonpos.2 ?_)` and prove the remaining obligations. Establish `: (0 : ℝ) < (p : ℝ) - 1` using `by linarith`.

Check the signs of the components of the expression. Set `cO : 𝓞_ℂ_[p]` to `⟨c0, (GlobalTheory.PadicComplexHost.mem_iff_norm p c0).2 hc0le⟩`. Establish `hcO : (Valued.v : Valuation ℂ_[p] ℝ≥0) (algebraMap 𝓞_ℂ_[p] ℂ_[p] cO) ^ (p - 1) ≤ (Valued.v : Valuation ℂ_[p] ℝ≥0) (p : ℂ_[p])`. Rewrite using `[← map_pow]`. Conclude with `le_of_eq (congrArg _ hc0)`.

Establish `hA` using `GlobalTheory.T.hodge_tate_lattice_span P hHT (embInt c P.integers τ) hdw (Submodule.smul_mem _ d hs) hcO`. Establish `hcd : ‖a‖ ≤ ‖c0 * d‖`. Use `ha.trans ?_` and prove the remaining obligations. Rewrite using `[norm_mul, hc0n, htEx, neg_add, Real.rpow_add (by positivity)]`. Use `mul_le_mul_of_nonneg_left ?_ (by positivity)` and prove the remaining obligations.

Use `le_trans (Real.rpow_le_rpow_of_exponent_le hp1.le ?_) hd` and prove the remaining obligations. Rewrite using `[← hx]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hne : c0 * d ≠ 0`. Introduce `h0`.

Establish `: (p : ℝ) ^ (-x) ≤ 0`. Use `hd.trans (le_of_eq ?_)` and prove the remaining obligations. Establish `h1 : ‖c0 * d‖ = 0` using `by rw [h0, norm_zero]`. Rewrite `h1` using `[norm_mul]`. Break down `mul_eq_zero.1 h1 with h2 | h2` into its components or cases.

Rewrite `h2` using `[hc0n]`. Conclude with `absurd h2 (by positivity)`. Conclude with `h2`. Conclude with `absurd this (not_le.2 (by positivity))`. Establish `hs1 : ‖a / (c0 * d)‖ ≤ 1`.

Rewrite using `[norm_div]`. Conclude with `div_le_one_of_le₀ hcd (norm_nonneg _)`. Set `sO : 𝓞_ℂ_[p]` to `⟨a / (c0 * d), (GlobalTheory.PadicComplexHost.mem_iff_norm p _).2 hs1⟩`. Establish `key` using `(P.wRec (embInt c P.integers τ)).smul_mem sO hA`. Establish `e : a • w = sO • (algebraMap 𝓞_ℂ_[p] ℂ_[p] cO • d • w)`.

Rewrite using `[← algebraMap_smul ℂ_[p] sO, smul_smul, smul_smul]`. Use `congr 1`. Express the relevant statement in the definitionally equal form `a = a / (c0 * d) * c0 * d`. Rewrite using `[_root_.mul_assoc, div_mul_cancel₀ a hne]`. Rewrite using `[e]`.

Conclude with `key`.
-/
theorem latBound : Hypotheses2 → GlobalTheory.CovHt.HTDiag.LatBound := by
  intro _ E _ _ _ _ H
  letI := H.starRing
  intro Dw l Xo c p _ _ T io y₀ hy k kO P ψ hP τ w hw hs a ha
  have hp : p.Prime := Fact.out
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hHT : HTChar p (Valued.v : Valuation ℂ_[p] ℝ≥0) P.Gt :=
    htChar_of_pointOver E H Dw l Xo c p ℂ_[p] _ 𝓞_ℂ_[p] T io y₀ hy k kO P ψ hP
  set x : ℝ := (padicValNat p (discr E).natAbs : ℝ) / (Module.finrank ℚ E : ℝ) with hx
  have hx0 : 0 ≤ x := by positivity

  obtain ⟨d, hd, hdw⟩ : ∃ d : ℂ_[p], (p : ℝ) ^ (-x) ≤ ‖d‖ ∧ d • w ∈ P.latT := by
    classical
    by_cases hτ : τ (H.rt : E) = H.rt0
    · obtain ⟨d, n, r, b, hd, hsum⟩ := GlobalTheory.T.padic_discriminant_dual_basis_bound E p (embAt c ℂ_[p] τ)
      refine ⟨d, hd, GlobalTheory.T.hodge_tate_point_dual_basis P _ d r b hsum ?_⟩
      unfold htLat at hw
      rw [if_pos hτ] at hw
      convert hw
    · refine ⟨1, ?_, ?_⟩
      · rw [norm_one]
        exact Real.rpow_le_one_of_one_le_of_nonpos hp1.le (neg_nonpos.2 hx0)
      · unfold htLat at hw
        rw [if_neg hτ] at hw
        rw [one_smul]
        exact hw.1

  obtain ⟨c0, hc0⟩ := IsAlgClosed.exists_pow_nat_eq (p : ℂ_[p]) (n := p - 1) (by have := hp.two_le; omega)
  have hpn : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.cast_sub hp.one_le, Nat.cast_one]
  have hc0n : ‖c0‖ = (p : ℝ) ^ (-(1 / ((p : ℝ) - 1))) := by
    have h1 : ‖c0‖ ^ (p - 1) = (p : ℝ)⁻¹ := by rw [← norm_pow, hc0, GlobalTheory.PadicComplexHost.norm_p]
    have h2 := Real.pow_rpow_inv_natCast (norm_nonneg c0) (n := p - 1) (by have := hp.two_le; omega)
    rw [h1, hpn, Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity)] at h2
    rw [one_div]
    exact h2.symm
  have hc0le : ‖c0‖ ≤ 1 := by
    rw [hc0n]
    refine Real.rpow_le_one_of_one_le_of_nonpos hp1.le (neg_nonpos.2 ?_)
    have : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    positivity
  let cO : 𝓞_ℂ_[p] := ⟨c0, (GlobalTheory.PadicComplexHost.mem_iff_norm p c0).2 hc0le⟩
  have hcO : (Valued.v : Valuation ℂ_[p] ℝ≥0) (algebraMap 𝓞_ℂ_[p] ℂ_[p] cO) ^ (p - 1) ≤
      (Valued.v : Valuation ℂ_[p] ℝ≥0) (p : ℂ_[p]) := by
    rw [← map_pow]
    exact le_of_eq (congrArg _ hc0)
  have hA := GlobalTheory.T.hodge_tate_lattice_span P hHT (embInt c P.integers τ) hdw (Submodule.smul_mem _ d hs) hcO

  have hcd : ‖a‖ ≤ ‖c0 * d‖ := by
    refine ha.trans ?_
    rw [norm_mul, hc0n, htEx, neg_add, Real.rpow_add (by positivity)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine le_trans (Real.rpow_le_rpow_of_exponent_le hp1.le ?_) hd
    rw [← hx]
    linarith
  have hne : c0 * d ≠ 0 := by
    intro h0
    have : (p : ℝ) ^ (-x) ≤ 0 := by
      refine hd.trans (le_of_eq ?_)
      have h1 : ‖c0 * d‖ = 0 := by rw [h0, norm_zero]
      rw [norm_mul] at h1
      rcases mul_eq_zero.1 h1 with h2 | h2
      · rw [hc0n] at h2
        exact absurd h2 (by positivity)
      · exact h2
    exact absurd this (not_le.2 (by positivity))
  have hs1 : ‖a / (c0 * d)‖ ≤ 1 := by
    rw [norm_div]
    exact div_le_one_of_le₀ hcd (norm_nonneg _)
  let sO : 𝓞_ℂ_[p] := ⟨a / (c0 * d), (GlobalTheory.PadicComplexHost.mem_iff_norm p _).2 hs1⟩
  have key := (P.wRec (embInt c P.integers τ)).smul_mem sO hA
  have e : a • w = sO • (algebraMap 𝓞_ℂ_[p] ℂ_[p] cO • d • w) := by
    rw [← algebraMap_smul ℂ_[p] sO, smul_smul, smul_smul]
    congr 1
    change a = a / (c0 * d) * c0 * d
    rw [_root_.mul_assoc, div_mul_cancel₀ a hne]
  rw [e]
  exact key

end GlobalTheory.CovHt.HTLatB
