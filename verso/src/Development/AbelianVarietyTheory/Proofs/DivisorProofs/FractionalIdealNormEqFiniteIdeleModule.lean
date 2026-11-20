import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCmCurveTorsionTransportSecondPeriod
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open GlobalTheory.ToricTransport (coordIn)
open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.LatVal.InvIdealNorm

open scoped GlobalTheory.Idele

variable {K : Type} [Field K] [NumberField K]

/- English proof (translation)
Establish an intermediate fact. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities.
-/
theorem eq_inv_smul_one {t : (Af K)ˣ} {𝔞 : FractionalIdeal (𝓞 K)⁰ K} (h : IsInvIdealOf t 𝔞) :
    𝔞 = t⁻¹ • (1 : FractionalIdeal (𝓞 K)⁰ K) := by
  have h' := GlobalTheory.LatVal.CurveTransport.isInvIdealOf_inv_smul_one t
  ext x
  rw [h x, h' x]

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem finprod_absNorm_zpow_count {I : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0) :
    ∏ᶠ v : HeightOneSpectrum (𝓞 K), ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ FractionalIdeal.count K v I =
      ((FractionalIdeal.absNorm I : ℚ) : ℝ) := by
  let g : FractionalIdeal (𝓞 K)⁰ K →*₀ ℝ :=
    (Rat.castHom ℝ).toMonoidWithZeroHom.comp FractionalIdeal.absNorm
  have hg : ∀ J, g J = ((FractionalIdeal.absNorm J : ℚ) : ℝ) := fun _ => rfl
  conv_rhs => rw [← hg, ← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hI]
  rw [map_finprod g]
  · refine finprod_congr fun v => ?_
    rw [map_zpow₀, hg, FractionalIdeal.coeIdeal_absNorm]
    simp
  · refine (Filter.eventually_cofinite.1 (FractionalIdeal.finite_factors I)).subset fun v hv h0 => hv ?_
    simp only [h0, zpow_zero]

end GlobalTheory.LatVal.InvIdealNorm

open GlobalTheory.LatVal.InvIdealNorm in
open scoped GlobalTheory.Idele in

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Reduce the equality to equality of the corresponding arguments. Rewrite the conclusion using the stated equalities.
-/
theorem GlobalTheory.LatVal.nrm_eq_modF_of_isInvIdealOf : ∀ {K : Type} [Field K] [NumberField K] (t : (Af K)ˣ)
    (𝔞 : FractionalIdeal (𝓞 K)⁰ K) (h : IsInvIdealOf t 𝔞), nrm 𝔞 = modF t := by
  intro K _ _ t 𝔞 h
  have e := eq_inv_smul_one h
  rw [GlobalTheory.Idele.smul_one_eq] at e
  have h0 : 𝔞 ≠ 0 := e ▸ GlobalTheory.Idele.idealOf_ne_zero _
  rw [nrm, ← finprod_absNorm_zpow_count h0, modF]
  refine finprod_congr fun v => ?_
  congr 1
  rw [e, GlobalTheory.Idele.count_idealOf, GlobalTheory.Idele.ord_vw_inv, GlobalTheory.Idele.ord_vw, neg_neg]
