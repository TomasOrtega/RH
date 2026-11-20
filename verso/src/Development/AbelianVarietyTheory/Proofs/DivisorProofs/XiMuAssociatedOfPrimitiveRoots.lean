import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDetEltOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FontaineAinfLocalDomainXiAdicOrder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusTwistedDivisibility
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MuCoeffZeroNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TiltIsDomainValuationRing
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

/- English proof (translation)
Unfold `nu mu root`. Rewrite using `[map_sub, map_one, WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_apply_frobeniusEquiv_symm]`.
-/
theorem frobenius_nu {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (ε : PreTilt O p) :
    WittVector.frobenius (nu ε) = mu ε := by
  unfold nu mu root
  rw [map_sub, map_one, WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller,
    frobenius_apply_frobeniusEquiv_symm]

/- English proof (translation)
Introduce `p _ C _ _ _ v O _ _ _ _ hv ε hε ε' hε'`. Take `⟨hdom, -, hker, -⟩` from `GlobalTheory.AinfXi.ainf_local_xi_order p C v O hv ε hε`. Take `⟨-, -, hker', -⟩` from `GlobalTheory.AinfXi.ainf_local_xi_order p C v O hv ε' hε'`. Establish `hA : Associated (xi ε) (xi ε')`. Rewrite using `[← Ideal.span_singleton_eq_span_singleton, ← hker, ← hker']`.

Use `⟨hA, ?_⟩` and prove the remaining obligations. Take `⟨hS, hVR⟩` from `GlobalTheory.TiltValuation.tilt_isDomain_valuationRing p C v O hv`. Establish `key : ∀ e e' : PreTilt O p, IsPrimitiveRoot (root e).untilt p → Associated (xi e) (xi e') → mu e ∣ mu e'`. Introduce `e e' he hee'`. Take `⟨u, hu⟩` from `hee'`.

Establish `h0` using `(GlobalTheory.DetInv.mu_coeff_zero_ne_zero p C v O hv e he).1`. Establish `hrel : ∀ i : Fin 1, mu e * WittVector.frobenius ((fun _ : Fin 1 => mu e') i) = WittVector.frobenius (mu e) * ((fun _ _ => WittVector.frobenius (u : WittVector p (PreTilt O p))) *ᵥ (fun _ : Fin 1 => mu e')) i`. Introduce `i`. Simplify using `only [Matrix.mulVec, dotProduct, Fin.sum_univ_one]`. Establish `hφ : ∀ x : PreTilt O p, WittVector.frobenius (mu x) = WittVector.frobenius (xi x) * mu x` using `fun x => by conv_lhs => rw [← xi_mul_nu x, map_mul, frobenius_nu]`.

Rewrite using `[hφ e, hφ e', ← hu, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `GlobalTheory.LemY.dvd_of_frobenius_eq p (PreTilt O p) 1 (mu e) _ _ h0 hrel 0`. Conclude with `associated_of_dvd_dvd (key ε ε' hε hA) (key ε' ε hε' hA.symm)`.
-/
theorem xi_mu_associated : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p),
    IsPrimitiveRoot (root ε).untilt p → ∀ ε' : PreTilt O p, IsPrimitiveRoot (root ε').untilt p →
    Associated (xi ε) (xi ε') ∧ Associated (mu ε) (mu ε') := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε ε' hε'
  obtain ⟨hdom, -, hker, -⟩ := GlobalTheory.AinfXi.ainf_local_xi_order p C v O hv ε hε
  obtain ⟨-, -, hker', -⟩ := GlobalTheory.AinfXi.ainf_local_xi_order p C v O hv ε' hε'
  have hA : Associated (xi ε) (xi ε') := by
    rw [← Ideal.span_singleton_eq_span_singleton, ← hker, ← hker']
  refine ⟨hA, ?_⟩
  obtain ⟨hS, hVR⟩ := GlobalTheory.TiltValuation.tilt_isDomain_valuationRing p C v O hv

  have key : ∀ e e' : PreTilt O p, IsPrimitiveRoot (root e).untilt p →
      Associated (xi e) (xi e') → mu e ∣ mu e' := by
    intro e e' he hee'
    obtain ⟨u, hu⟩ := hee'
    have h0 := (GlobalTheory.DetInv.mu_coeff_zero_ne_zero p C v O hv e he).1
    have hrel : ∀ i : Fin 1, mu e * WittVector.frobenius ((fun _ : Fin 1 => mu e') i) =
        WittVector.frobenius (mu e) *
          ((fun _ _ => WittVector.frobenius (u : WittVector p (PreTilt O p))) *ᵥ
            (fun _ : Fin 1 => mu e')) i := by
      intro i
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_one]
      have hφ : ∀ x : PreTilt O p, WittVector.frobenius (mu x) =
          WittVector.frobenius (xi x) * mu x := fun x => by
        conv_lhs => rw [← xi_mul_nu x, map_mul, frobenius_nu]
      rw [hφ e, hφ e', ← hu, map_mul]
      ring
    exact GlobalTheory.LemY.dvd_of_frobenius_eq p (PreTilt O p) 1 (mu e) _ _ h0 hrel 0
  exact associated_of_dvd_dvd (key ε ε' hε hA) (key ε' ε hε' hA.symm)

end GlobalTheory.DetInv
