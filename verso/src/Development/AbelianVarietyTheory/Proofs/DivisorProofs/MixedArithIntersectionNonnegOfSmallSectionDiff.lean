import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLBLeBySmallSectionIffExistsSmallSectionDiffeStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef

open MvPolynomial in

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Introduce a local definition for the expression. Introduce a local definition for the expression.

Introduce a local definition for the expression. Establish an intermediate fact. Assume the hypotheses and unpack their components. Reduce the claim to the hypotheses of an applicable result. Simplify using the standard rewrite rules.

Establish an intermediate fact. Introduce a local definition for the expression. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result.

Simplify using the standard rewrite rules. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Simplify using the standard rewrite rules.

Expand and normalize the polynomial expressions, which then agree. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Replace the relevant objects with their definitions.

Check the signs of the components of the expression. Establish an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Replace the relevant objects with their definitions. Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion. A detailed English derivation is pending.
-/
theorem mixed_diff_nonneg : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (A B : HermLB p) (Φ : MvPolynomial (Fin 2) ℝ →ₗ[ℝ] ℝ), IsArFun ![A, B] D Φ → Le B A → ∀ x y : ℕ, HtNef ((A.pow x).tens (B.pow y)) D → 0 ≤ Φ ((MvPolynomial.X 0 - MvPolynomial.X 1) * (MvPolynomial.C (x : ℝ) * MvPolynomial.X 0 + MvPolynomial.C (y : ℝ) * MvPolynomial.X 1) ^ D) := by
  intro hC k _ X _ p D hX A B Φ hΦ hle x y hN
  classical
  haveI := hX.isLocallyNoetherian
  obtain ⟨s, hs, hs0⟩ := (GlobalTheory.T.hermLBLeBySmallSection_iff_exists_smallSection_difference k X p A B).1 hle
  have hg :=  (sec_ne_zero_iff s).1 hs0
  let L : Fin 2 → HermLB p := ![A, B]
  let F : Option (Fin 2) → HermLB p := fun o => o.elim (A.tens B.dual) L
  let E : Option (Fin 2) → Fin 2 → ℤ := fun o => o.elim ![1, -1] (fun i => Pi.single i 1)
  have hiso : ∀ j, (comb L (E j)).Isometric (F j) := by
    rintro (_ | i)
    · apply HermLB.icls_eq_iff.1
      simp [icls_comb, Fin.sum_univ_two, L, E, F, HermLB.icls_tens, HermLB.icls_dual, sub_eq_add_neg]
    · exact isometric_comb_single L i
  have hΦ' := ((hC.arIso k X p D hX).2 (Fin 2) L Φ hΦ).2.2 (Option (Fin 2)) F E hiso
  let n : Fin 2 → ℤ := ![(x : ℤ), (y : ℤ)]
  obtain ⟨h, hh⟩ := (hC.arExists k X p D hX).1 (comb L n)
  have hNiso : (comb L n).Isometric ((A.pow x).tens (B.pow y)) := by
    apply HermLB.icls_eq_iff.1
    simp [icls_comb, Fin.sum_univ_two, L, n, HermLB.icls_tens, HermLB.icls_pow]
  have hr := isRatSec_ratOfSec s hg
  obtain ⟨-, hmix⟩ := hC.arMix k X p D hX (Fin 2) (A.tens B.dual) L _ hΦ' n h hh (ratOfSec s hg) hr
  have hpoly : aeval (fun j => lin fun i => ((E j i : ℤ) : ℝ))
      (MvPolynomial.X none * rename some (lin fun i => ((n i : ℤ) : ℝ)) ^ D) =
      (MvPolynomial.X 0 - MvPolynomial.X 1) * (C (x : ℝ) * MvPolynomial.X 0 + C (y : ℝ) * MvPolynomial.X 1) ^ D := by
    simp [aeval_rename, lin, Fin.sum_univ_two, E, n, Function.comp_def, Pi.single_apply]
    left
    ring
  rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply, hpoly] at hmix
  rw [hmix]
  have h1 : 0 ≤ ∑ᶠ z, (((A.tens B.dual).div hr).mult z : ℝ) * h z :=
    finsum_nonneg fun z => mul_nonneg (Int.cast_nonneg (mult_divOfSec_nonneg (hL := (A.tens B.dual).isLB) z))
      (hN.2 h (hNiso.isArithHeight hX hh) z)
  have h2 : ∀ σ, ((comb L n).φ σ).chernInt D (offSupp p σ ((A.tens B.dual).div hr))
      (logNorm ((A.tens B.dual).φ σ) (ratOfSec s hg)) ≤ 0 := by
    intro σ
    have hneg : ((comb L n).φ σ).chernPart D (-1) = 0 := by
      rw [hNiso.chernPart_eq]
      exact Weight.chernPart_neg_eq_zero (((A.pow x).tens (B.pow y)).cInf σ) (hN.1 σ)
    rw [Weight.chernInt, hneg, MeasureTheory.Measure.restrict_zero, MeasureTheory.integral_zero_measure, sub_zero]
    refine MeasureTheory.setIntegral_nonpos (isOpen_offSupp _).measurableSet fun z hz => ?_
    have hz' : z ∈ ptsIn p σ (Out.nonzeroLocus s) := by
      rw [← offSupp_divOfSec (hL := (A.tens B.dual).isLB)]
      exact hz
    rw [logNorm_ratOfSec _ hz']
    have h0 : 0 ≤ ((A.tens B.dual).φ σ).nsq (secVal p σ s) z := by
      unfold Weight.nsq
      positivity
    have := Real.log_nonpos h0 (hs σ z)
    linarith
  have h3 : (comb L n).archInt (A.tens B.dual) D hr ≤ 0 := by
    have := finsum_nonneg fun σ => neg_nonneg.2 (h2 σ)
    rw [finsum_neg_distrib] at this
    unfold HermLB.archInt
    linarith
  linarith

end GlobalTheory.HSNef
