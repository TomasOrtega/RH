import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TcoMem
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAffCoverSpec
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ToPtIdPtBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardOpenCoordinateRingIsFractionRingIsNoetheStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAffineOpenRingPolynomialEquivStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LaurentConstantTermEqEvalOriginChartStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TraceFibreRingEqFinsumFibrePointsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TraceEvalOriginEqFibreTraceStatement

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechDR GlobalTheory.PD KaehlerDifferential

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PD

/- English proof (translation)
Introduce `k _ _ F K _ _ _ _ _ _ d x hc τ hτ ρ hρ hac hred h`. Establish `hloc : locCoch k K x (h : K) Finset.univ = (h : K) • vol0 k K x` using `if_pos rfl`. Establish `h1 : trF k τ ρ (locCoch k K x (h : K) Finset.univ) = ρ (Algebra.trace F K (h : K))`. Simplify using `only [trF, LinearMap.comp_apply, LinearMap.restrictScalars_apply, hloc, map_smul, hτ.1, smul_eq_mul, mul_one]`. Rewrite using `[h1]`.

Take `⟨e, -⟩` from `GlobalTheory.T.standardAffineOpen_ring_polynomialEquiv k F d x hc.pd 0`. Use `haveI : IsIntegrallyClosed (rA k x {0}) := IsIntegrallyClosed.of_equiv e.toRingEquiv`. Use `haveI : IsFractionRing (rA k x {0}) F := (GlobalTheory.T.standardOpenCoordinateRing_isFractionRing_isNoetherianRing k F d x hc.pd {0} (Finset.singleton_nonempty _)).1`. Use `haveI := hc.fin`. Establish `hint : IsIntegral (rA k x {0}) (h : K)` using `h.2`.

Take `⟨a, ha⟩` from `(IsIntegrallyClosed.isIntegral_iff (R := rA k x {0}) (K := F)).1 (Algebra.isIntegral_trace (L := F) hint)`. Take `⟨ev, hev, hker⟩` from `GlobalTheory.T.laurentConstantTerm_eq_eval_origin_chart k F d x hc.pd ρ hρ`. Establish `ha' : (a : F) = Algebra.trace F K (h : K)` using `ha`. Rewrite using `[← ha', hev, GlobalTheory.T.trace_eval_origin_eq_fibre_trace k F K d x hc ev hker h a ha', GlobalTheory.T.trace_fibreRing_eq_finsum_fibrePoints k F K d x hc hac hred h]`.
-/
theorem trF_locCoch_eq_finsum_fib : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → ∀ (τ : DR k K →ₗ[K] K), IsTop k K x τ → ∀ (ρ : F →ₗ[k] k), IsRes k x ρ → IsAlgClosed k → IsReduced ((rB k K x {0}) ⧸ (Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem k K x j⟩ : (rB k K x {0}))))) → ∀ h : (rB k K x {0}), trF k τ ρ (locCoch k K x h Finset.univ) = ∑ᶠ e : fib k K x, e.1 h := by
  intro k _ _ F K _ _ _ _ _ _ d x hc τ hτ ρ hρ hac hred h
  have hloc : locCoch k K x (h : K) Finset.univ = (h : K) • vol0 k K x := if_pos rfl
  have h1 : trF k τ ρ (locCoch k K x (h : K) Finset.univ) = ρ (Algebra.trace F K (h : K)) := by
    simp only [trF, LinearMap.comp_apply, LinearMap.restrictScalars_apply, hloc, map_smul, hτ.1, smul_eq_mul, mul_one]
  rw [h1]
  obtain ⟨e, -⟩ := GlobalTheory.T.standardAffineOpen_ring_polynomialEquiv k F d x hc.pd 0
  haveI : IsIntegrallyClosed (rA k x {0}) := IsIntegrallyClosed.of_equiv e.toRingEquiv
  haveI : IsFractionRing (rA k x {0}) F := (GlobalTheory.T.standardOpenCoordinateRing_isFractionRing_isNoetherianRing k F d x hc.pd {0} (Finset.singleton_nonempty _)).1
  haveI := hc.fin
  have hint : IsIntegral (rA k x {0}) (h : K) := h.2
  obtain ⟨a, ha⟩ := (IsIntegrallyClosed.isIntegral_iff (R := rA k x {0}) (K := F)).1 (Algebra.isIntegral_trace (L := F) hint)
  obtain ⟨ev, hev, hker⟩ := GlobalTheory.T.laurentConstantTerm_eq_eval_origin_chart k F d x hc.pd ρ hρ
  have ha' : (a : F) = Algebra.trace F K (h : K) := ha
  rw [← ha', hev, GlobalTheory.T.trace_eval_origin_eq_fibre_trace k F K d x hc ev hker h a ha', GlobalTheory.T.trace_fibreRing_eq_finsum_fibrePoints k F K d x hc hac hred h]

end GlobalTheory.PD
