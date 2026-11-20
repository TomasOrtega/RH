import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RingOfIntegersFiniteExtIsDVRFiniteUnitIffStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWittResidueFieldInRingOfIntegersStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniformiserEisensteinNotInXPowStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinQuotientEisensteinEquivStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinDistinguishedPowerSeriesAdicCompleteStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinEvalTeichmullerTiltStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanEqKerThetaOfDistinguishedAinfStatement

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Assume the negation of the conclusion as `h0`. Take `⟨n, u, rfl⟩` from `WittVector.exists_eq_pow_p_mul' x h0`. Rewrite `hx` using `[map_mul, map_pow, map_natCast]`.

Break down `mul_eq_zero.1 hx with h | h` into its components or cases. Conclude with `pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) h`. Conclude with `(u.isUnit.map w).ne_zero h`.
-/
theorem wq_map_injective {l : ℕ} [Fact l.Prime] {a : ℕ} [NeZero a] {O : Type} [CommRing O] [IsDomain O]
    [CharZero O] (w : Wq l a →+* O) : Function.Injective w := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra h0
  obtain ⟨n, u, rfl⟩ := WittVector.exists_eq_pow_p_mul' x h0
  rw [map_mul, map_pow, map_natCast] at hx
  rcases mul_eq_zero.1 hx with h | h
  · exact pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) h
  · exact (u.isUnit.map w).ne_zero h

/- English proof (translation)
Introduce `l hl K`. Take `⟨hdvr, hfin, hunit⟩` from `GlobalTheory.T.ringOfIntegers_finiteExt_isDVR_finite_unit_iff l K`. Take `⟨a, ha, w, hK, hw, hres⟩` from `GlobalTheory.T.exists_witt_residueField_in_ringOfIntegers l K`. Use `letI : Algebra (Wq l a) ↥(OL K) := w.toRingHom.toAlgebra`. Establish `halg : ∀ c, algebraMap (Wq l a) ↥(OL K) c = w c` using `fun _ => rfl`.

Use `haveI : IsScalarTower ℤ_[l] (Wq l a) ↥(OL K) := IsScalarTower.of_algebraMap_eq fun z => (w.commutes z).symm`. Use `haveI : Module.Finite (Wq l a) ↥(OL K) := Module.Finite.of_restrictScalars_finite ℤ_[l] _ _`. Take `⟨π, Ep, hπ, hE, hne, hmin⟩` from `GlobalTheory.T.exists_uniformiser_eisenstein_not_in_X_pow l a ↥(OL K) (wq_map_injective _) hres`. Take `⟨str, hstr⟩` from `GlobalTheory.T.breuilKisin_quotient_eisenstein_equiv l a ↥(OL K) π Ep hE hmin`. Take `⟨hδ, hc⟩` from `GlobalTheory.T.eisenstein_distinguished_powerSeries_adicComplete l a Ep hE`.

Take `⟨fl, ev, hfl, hX, hC, hφ⟩` from `GlobalTheory.T.exists_breuilKisin_eval_teichmuller_tilt l a (intToOC K π) (fun h => hπ.not_isUnit ((hunit π).2 h))`. Establish `hpoly : ∀ f : Polynomial (Wq l a), Per.θ l (ev (f : (Wq l a)⟦X⟧)) = intToOC K (Polynomial.aeval π f)`. Introduce `f`. Establish `: ((Per.θ l).comp ev).comp Polynomial.coeToPowerSeries.ringHom = (intToOC K).comp (Polynomial.aeval π : Polynomial (Wq l a) →ₐ[Wq l a] ↥(OL K)).toRingHom`. Use `Polynomial.ringHom_ext (fun c => ?_) ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `Per.θ l (ev ((Polynomial.C c : Polynomial (Wq l a)) : (Wq l a)⟦X⟧)) = intToOC K (Polynomial.aeval π (Polynomial.C c))`. Rewrite using `[Polynomial.coe_C, hC, Polynomial.aeval_C, halg, hw]`. Express the relevant statement in the definitionally equal form `Per.θ l (ev ((Polynomial.X : Polynomial (Wq l a)) : (Wq l a)⟦X⟧)) = intToOC K (Polynomial.aeval π (Polynomial.X : Polynomial (Wq l a)))`. Rewrite using `[Polynomial.coe_X, hX, Polynomial.aeval_X, hfl]`. Conclude with `congrArg (fun φ : Polynomial (Wq l a) →+* OC l => φ f) this`.

Establish `hE0 : Per.θ l (ev (Ep : (Wq l a)⟦X⟧)) = 0` using `by rw [hpoly, hmin.1, map_zero]`. Use `⟨{ a := a, Ep := Ep, monic := hE.1, deg_pos := hE.2.1, dvd_coeff := hE.2.2.1, coeff_zero := hE.2.2.2 not_expand := hne, str := str, isUnit_δ := hδ, complete := hc, flat := fl, ev := ev, ev_X := hX ev_C := hC, ev_frob := hφ span_ev := GlobalTheory.T.span_eq_ker_theta_of_distinguis …` and prove the remaining obligations. Rewrite using `[← (deltaS l a).map_δ_of_map_φ (ainfDelta l) ainf_torsionFree ev hφ]`. Conclude with `hδ.map ev`. Take `⟨f, rfl⟩` from `hmin.2.1 r`.

Rewrite `h` using `[hstr, Ideal.Quotient.eq, Ideal.mem_span_singleton']`. Take `⟨y, hy⟩` from `h`. Rewrite using `[← hpoly, ← sub_eq_zero, ← map_sub, ← map_sub, ← hy, map_mul, map_mul, hE0, mul_zero]`.
-/
theorem nonempty_bk_of_finExt : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l), Nonempty (BK K) := by
  intro l hl K
  obtain ⟨hdvr, hfin, hunit⟩ := GlobalTheory.T.ringOfIntegers_finiteExt_isDVR_finite_unit_iff l K
  obtain ⟨a, ha, w, hK, hw, hres⟩ := GlobalTheory.T.exists_witt_residueField_in_ringOfIntegers l K
  letI : Algebra (Wq l a) ↥(OL K) := w.toRingHom.toAlgebra
  have halg : ∀ c, algebraMap (Wq l a) ↥(OL K) c = w c := fun _ => rfl
  haveI : IsScalarTower ℤ_[l] (Wq l a) ↥(OL K) :=
    IsScalarTower.of_algebraMap_eq fun z => (w.commutes z).symm
  haveI : Module.Finite (Wq l a) ↥(OL K) := Module.Finite.of_restrictScalars_finite ℤ_[l] _ _
  obtain ⟨π, Ep, hπ, hE, hne, hmin⟩ :=
    GlobalTheory.T.exists_uniformiser_eisenstein_not_in_X_pow l a ↥(OL K) (wq_map_injective _) hres
  obtain ⟨str, hstr⟩ := GlobalTheory.T.breuilKisin_quotient_eisenstein_equiv l a ↥(OL K) π Ep hE hmin
  obtain ⟨hδ, hc⟩ := GlobalTheory.T.eisenstein_distinguished_powerSeries_adicComplete l a Ep hE
  obtain ⟨fl, ev, hfl, hX, hC, hφ⟩ :=
    GlobalTheory.T.exists_breuilKisin_eval_teichmuller_tilt l a (intToOC K π) (fun h => hπ.not_isUnit ((hunit π).2 h))
  have hpoly : ∀ f : Polynomial (Wq l a),
      Per.θ l (ev (f : (Wq l a)⟦X⟧)) = intToOC K (Polynomial.aeval π f) := by
    intro f
    have : ((Per.θ l).comp ev).comp Polynomial.coeToPowerSeries.ringHom =
        (intToOC K).comp (Polynomial.aeval π : Polynomial (Wq l a) →ₐ[Wq l a] ↥(OL K)).toRingHom := by
      refine Polynomial.ringHom_ext (fun c => ?_) ?_
      · change Per.θ l (ev ((Polynomial.C c : Polynomial (Wq l a)) : (Wq l a)⟦X⟧)) =
          intToOC K (Polynomial.aeval π (Polynomial.C c))
        rw [Polynomial.coe_C, hC, Polynomial.aeval_C, halg, hw]
      · change Per.θ l (ev ((Polynomial.X : Polynomial (Wq l a)) : (Wq l a)⟦X⟧)) =
          intToOC K (Polynomial.aeval π (Polynomial.X : Polynomial (Wq l a)))
        rw [Polynomial.coe_X, hX, Polynomial.aeval_X, hfl]
    exact congrArg (fun φ : Polynomial (Wq l a) →+* OC l => φ f) this
  have hE0 : Per.θ l (ev (Ep : (Wq l a)⟦X⟧)) = 0 := by rw [hpoly, hmin.1, map_zero]
  refine ⟨{
    a := a, Ep := Ep, monic := hE.1, deg_pos := hE.2.1, dvd_coeff := hE.2.2.1, coeff_zero := hE.2.2.2
    not_expand := hne, str := str, isUnit_δ := hδ, complete := hc, flat := fl, ev := ev, ev_X := hX
    ev_C := hC, ev_frob := hφ
    span_ev := GlobalTheory.T.span_eq_ker_theta_of_distinguished_ainf l _ hE0 ?_
    θ_ev := fun r x h => ?_
    gal_w := fun g c => gal_wA l a
      (fun x hx => (IntermediateField.mem_fixingSubgroup_iff _ _).1 g.2 x (hK hx)) c }⟩
  · rw [← (deltaS l a).map_δ_of_map_φ (ainfDelta l) ainf_torsionFree ev hφ]
    exact hδ.map ev
  · obtain ⟨f, rfl⟩ := hmin.2.1 r
    rw [hstr, Ideal.Quotient.eq, Ideal.mem_span_singleton'] at h
    obtain ⟨y, hy⟩ := h
    rw [← hpoly, ← sub_eq_zero, ← map_sub, ← map_sub, ← hy, map_mul, map_mul, hE0, mul_zero]

end GlobalTheory.BSP
