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
Establish `h'` using `GlobalTheory.LatVal.CurveTransport.isInvIdealOf_inv_smul_one t`. Use extensionality with `x`. Rewrite using `[h x, h' x]`.
-/
theorem eq_inv_smul_one {t : (Af K)ˣ} {𝔞 : FractionalIdeal (𝓞 K)⁰ K} (h : IsInvIdealOf t 𝔞) :
    𝔞 = t⁻¹ • (1 : FractionalIdeal (𝓞 K)⁰ K) := by
  have h' := GlobalTheory.LatVal.CurveTransport.isInvIdealOf_inv_smul_one t
  ext x
  rw [h x, h' x]

/- English proof (translation)
Set `g : FractionalIdeal (𝓞 K)⁰ K →*₀ ℝ` to `(Rat.castHom ℝ).toMonoidWithZeroHom.comp FractionalIdeal.absNorm`. Establish `hg : ∀ J, g J = ((FractionalIdeal.absNorm J : ℚ) : ℝ)` using `fun _ => rfl`. Use `conv_rhs => rw [← hg, ← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hI]`. Rewrite using `[map_finprod g]`. Use `finprod_congr fun v => ?_` and prove the remaining obligations.

Rewrite using `[map_zpow₀, hg, FractionalIdeal.coeIdeal_absNorm]`. Simplify using the standard rewrite rules. Use `(Filter.eventually_cofinite.1 (FractionalIdeal.finite_factors I)).subset fun v hv h0 => hv ?_` and prove the remaining obligations. Simplify using `only [h0, zpow_zero]`.
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
Introduce `K _ _ t 𝔞 h`. Establish `e` using `eq_inv_smul_one h`. Rewrite `e` using `[GlobalTheory.Idele.smul_one_eq]`. Establish `h0 : 𝔞 ≠ 0` using `e ▸ GlobalTheory.Idele.idealOf_ne_zero _`. Rewrite using `[nrm, ← finprod_absNorm_zpow_count h0, modF]`.

Use `finprod_congr fun v => ?_` and prove the remaining obligations. Use `congr 1`. Rewrite using `[e, GlobalTheory.Idele.count_idealOf, GlobalTheory.Idele.ord_vw_inv, GlobalTheory.Idele.ord_vw, neg_neg]`.
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
