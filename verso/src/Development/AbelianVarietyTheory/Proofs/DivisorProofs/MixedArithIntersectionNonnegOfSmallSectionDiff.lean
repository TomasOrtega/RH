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
Introduce `hC k _ X _ p D hX A B Φ hΦ hle x y hN`. Use `haveI := hX.isLocallyNoetherian`. Take `⟨s, hs, hs0⟩` from `(GlobalTheory.T.hermLBLeBySmallSection_iff_exists_smallSection_difference k X p A B).1 hle`. Establish `hg` using `(sec_ne_zero_iff s).1 hs0`. Set `L : Fin 2 → HermLB p` to `![A, B]`.

Set `F : Option (Fin 2) → HermLB p` to `fun o => o.elim (A.tens B.dual) L`. Set `E : Option (Fin 2) → Fin 2 → ℤ` to `fun o => o.elim ![1, -1] (fun i => Pi.single i 1)`. Establish `hiso : ∀ j, (comb L (E j)).Isometric (F j)`. Introduce and unpack `(_ | i)`. Apply `HermLB.icls_eq_iff.1` to reduce the goal to its premises.

Simplify using `[icls_comb, Fin.sum_univ_two, L, E, F, HermLB.icls_tens, HermLB.icls_dual, sub_eq_add_neg]`. Conclude with `isometric_comb_single L i`. Establish `hΦ'` using `((hC.arIso k X p D hX).2 (Fin 2) L Φ hΦ).2.2 (Option (Fin 2)) F E hiso`. Set `n : Fin 2 → ℤ` to `![(x : ℤ), (y : ℤ)]`. Take `⟨h, hh⟩` from `(hC.arExists k X p D hX).1 (comb L n)`.

Establish `hNiso : (comb L n).Isometric ((A.pow x).tens (B.pow y))`. Apply `HermLB.icls_eq_iff.1` to reduce the goal to its premises. Simplify using `[icls_comb, Fin.sum_univ_two, L, n, HermLB.icls_tens, HermLB.icls_pow]`. Establish `hr` using `isRatSec_ratOfSec s hg`. Take `⟨-, hmix⟩` from `hC.arMix k X p D hX (Fin 2) (A.tens B.dual) L _ hΦ' n h hh (ratOfSec s hg) hr`.

Establish `hpoly : aeval (fun j => lin fun i => ((E j i : ℤ) : ℝ)) (MvPolynomial.X none * rename some (lin fun i => ((n i : ℤ) : ℝ)) ^ D) = (MvPolynomial.X 0 - MvPolynomial.X 1) * (C (x : ℝ) * MvPolynomial.X 0 + C (y : ℝ) * MvPolynomial.X 1) ^ D`. Simplify using `[aeval_rename, lin, Fin.sum_univ_two, E, n, Function.comp_def, Pi.single_apply]`. Use `left`. Expand and normalize the polynomial expressions, which then agree. Rewrite `hmix` using `[LinearMap.comp_apply, AlgHom.toLinearMap_apply, hpoly]`.

Rewrite using `[hmix]`. Establish `h1 : 0 ≤ ∑ᶠ z, (((A.tens B.dual).div hr).mult z : ℝ) * h z` using `finsum_nonneg fun z => mul_nonneg (Int.cast_nonneg (mult_divOfSec_nonneg (hL := (A.tens B.dual).isLB) z)) (hN.2 h (hNiso.isArithHeight hX hh) z)`. Establish `h2 : ∀ σ, ((comb L n).φ σ).chernInt D (offSupp p σ ((A.tens B.dual).div hr)) (logNorm ((A.tens B.dual).φ σ) (ratOfSec s hg)) ≤ 0`. Introduce `σ`. Establish `hneg : ((comb L n).φ σ).chernPart D (-1) = 0`.

Rewrite using `[hNiso.chernPart_eq]`. Conclude with `Weight.chernPart_neg_eq_zero (((A.pow x).tens (B.pow y)).cInf σ) (hN.1 σ)`. Rewrite using `[Weight.chernInt, hneg, MeasureTheory.Measure.restrict_zero, MeasureTheory.integral_zero_measure, sub_zero]`. Use `MeasureTheory.setIntegral_nonpos (isOpen_offSupp _).measurableSet fun z hz => ?_` and prove the remaining obligations. Establish `hz' : z ∈ ptsIn p σ (Out.nonzeroLocus s)`.

Rewrite using `[← offSupp_divOfSec (hL := (A.tens B.dual).isLB)]`. Conclude with `hz`. Rewrite using `[logNorm_ratOfSec _ hz']`. Establish `h0 : 0 ≤ ((A.tens B.dual).φ σ).nsq (secVal p σ s) z`. Unfold `Weight.nsq`.

Check the signs of the components of the expression. Use `Real.log_nonpos h0 (hs σ z)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h3 : (comb L n).archInt (A.tens B.dual) D hr ≤ 0`. Use `finsum_nonneg fun σ => neg_nonneg.2 (h2 σ)` as an intermediate fact.

Rewrite `this` using `[finsum_neg_distrib]`. Unfold `HermLB.archInt`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion.
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
