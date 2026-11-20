import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TraceDualDifferent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivLatticeClassesFibreSummandStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivFourierClassesPosConeSummandStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeSumEqConeSum
open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.EisNonConst
open NumberField GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.SlopeTestRemainingChoices.EisFibre

/- English proof (translation)
Establish `hr : (0 : ℝ) ≤ (|(Algebra.norm ℚ p.1 : ℝ)| / nrm 𝔞) ^ (k - 1)`. Apply `pow_nonneg` to reduce the goal to its premises. Apply `div_nonneg (abs_nonneg _)` to reduce the goal to its premises. Unfold `nrm`. Conclude with `FractionalIdeal.absNorm_nonneg _` after adjusting the coercions.

Unfold `qTerm qPow`. Rewrite using `[norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_of_nonneg hr]`. Use `push_cast`. Use `congr 1`. Use `congr 1`.

Apply the tactic sequence `apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, Complex.re_sum, Complex.im_sum, Finset.mul_sum]`.
-/
theorem qTerm_norm {F : Type} [Field F] [NumberField F] (𝔞 : Frac F) (k : ℕ) (z : Emb F → ℂ) (p : F × F) :
    ((‖qTerm 𝔞 k z p‖ : ℝ) : ℂ) = qTerm 𝔞 k (fun τ => Complex.I * ((z τ).im : ℂ)) p := by
  have hr : (0 : ℝ) ≤ (|(Algebra.norm ℚ p.1 : ℝ)| / nrm 𝔞) ^ (k - 1) := by
    apply pow_nonneg; apply div_nonneg (abs_nonneg _)
    unfold nrm; exact_mod_cast FractionalIdeal.absNorm_nonneg _
  unfold qTerm qPow
  rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_of_nonneg hr]
  push_cast
  congr 1
  congr 1
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, Complex.re_sum, Complex.im_sum, Finset.mul_sum]

/- English proof (translation)
Introduce `F _ _ _ hL 𝔞 𝔟 k hk2 hke hsum z hz`. Take `⟨e1, he1⟩` from `GlobalTheory.T.exists_equiv_latticeClasses_fibre_summand F 𝔞 𝔟`. Take `⟨e2, he2⟩` from `GlobalTheory.T.exists_equiv_fourierClasses_posCone_summand F 𝔞 𝔟`. Use `set C : ℂ := (omegaFactor 𝔞 : ℂ) ^ k / (cK F k : ℂ) with hC`. Use `set y : Emb F → ℂ := fun τ => Complex.I * ((z τ).im : ℂ) with hy_def`.

Establish `hdF : 0 < dF F` using `abs_pos.2 (by exact_mod_cast discr_ne_zero F)`. Establish `hN : 0 < nrm 𝔞`. Unfold `nrm`. Establish `h2 : FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0`. Rewrite using `[Ne, FractionalIdeal.absNorm_eq_zero_iff]`.

Conclude with `𝔞.ne_zero`. Conclude with `lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg _) h2.symm` after adjusting the coercions. Establish `hCne : C ≠ 0`. Establish `h1 : 0 < omegaFactor 𝔞` using `mul_pos (Real.rpow_pos_of_pos hdF _) hN`. Establish `h2 : 0 < cK F k` using `mul_pos (pow_pos (by exact_mod_cast Nat.factorial_pos _) _) (Real.rpow_pos_of_pos hdF _)`.

Rewrite using `[hC]`. Conclude with `div_ne_zero (pow_ne_zero _ (by exact_mod_cast h1.ne')) (by exact_mod_cast h2.ne')`. Establish `hy : y ∈ upperHalf F` using `fun τ => by simpa [hy_def] using hz τ`. Establish `hlat : ∀ w ∈ upperHalf F, Summable (fun x : (Σ _β : NzCls 𝔟, (latM 𝔞 : Set F)) => eisTerm k 0 w ((x.2 : F), rep x.1))`. Introduce `w hw`.

Establish `h1 : Summable (fun c : {c : Quotient (latRel 𝔞 𝔟) // c.out.1.2 ≠ 0} => eisClass 𝔞 𝔟 k 0 w c)` using `(hsum w hw).subtype _`. Establish `h2` using `(e1.summable_iff (f := fun c : {c : Quotient (latRel 𝔞 𝔟) // c.out.1.2 ≠ 0} => eisClass 𝔞 𝔟 k 0 w c)).2 h1`. Use `h2.congr fun x => ?_` and prove the remaining obligations. Simplify using `only [Function.comp_apply]`. Conclude with `he1 k hke 0 w x`.

Establish `hqfib : ∀ β : NzCls 𝔟, Summable (fun ν : posCone 𝔞 (rep β) => ‖qTerm 𝔞 k z (ν.1, rep β)‖)`. Introduce `β`. Use `(GlobalTheory.EisPerB.lattice_sum_eq_cone_sum F hL 𝔞 k hk2 hke (rep β) (rep_ne_zero β) y hy).1` as an intermediate fact. Rewrite using `[← Complex.summable_ofReal]`. Use `this.congr fun ν => ?_` and prove the remaining obligations.

Conclude with `(qTerm_norm 𝔞 k z _).symm`. Establish `hqsig : Summable (fun x : (Σ β : NzCls 𝔟, posCone 𝔞 (rep β)) => qTerm 𝔞 k z (x.2.1, rep x.1))`. Use `Summable.of_norm ?_` and prove the remaining obligations. Rewrite using `[summable_sigma_of_nonneg (fun _ => norm_nonneg _)]`. Use `⟨hqfib, ?_⟩` and prove the remaining obligations.

Establish `hmarg : Summable (fun β : NzCls 𝔟 => ∑' a : (latM 𝔞 : Set F), ‖eisTerm k 0 y ((a : F), rep β)‖)` using `(summable_norm_iff.2 (hlat y hy)).sigma`. Use `Summable.of_nonneg_of_le (fun _ => tsum_nonneg fun _ => norm_nonneg _) (fun β => ?_) (hmarg.mul_left ‖C‖⁻¹)` and prove the remaining obligations. Take `⟨-, hP⟩` from `GlobalTheory.EisPerB.lattice_sum_eq_cone_sum F hL 𝔞 k hk2 hke (rep β) (rep_ne_zero β) y hy`. Establish `hfib` using `hqfib β`. Establish `hT : ((∑' ν : posCone 𝔞 (rep β), ‖qTerm 𝔞 k z (ν.1, rep β)‖ : ℝ) : ℂ) = ∑' ν : posCone 𝔞 (rep β), qTerm 𝔞 k y (ν.1, rep β)`.

Rewrite using `[Complex.ofReal_tsum]`. Conclude with `tsum_congr fun ν => qTerm_norm 𝔞 k z _`. Establish `hE : ∑' ν : posCone 𝔞 (rep β), qTerm 𝔞 k y (ν.1, rep β) = C⁻¹ * ∑' a : (latM 𝔞 : Set F), eisTerm k 0 y ((a : F), rep β)`. Rewrite using `[hP.tsum_eq, ← mul_assoc, inv_mul_cancel₀ hCne, one_mul]`. Establish `hnn : 0 ≤ ∑' ν : posCone 𝔞 (rep β), ‖qTerm 𝔞 k z (ν.1, rep β)‖` using `tsum_nonneg fun _ => norm_nonneg _`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Complex.norm_real, Real.norm_of_nonneg hnn]`. Use `_ = ‖C‖⁻¹ * ‖∑' a : (latM 𝔞 : Set F), eisTerm k 0 y ((a : F), rep β)‖ := by`. Rewrite using `[hT, hE, norm_mul, norm_inv]`. Use `_ ≤ ‖C‖⁻¹ * ∑' a : (latM 𝔞 : Set F), ‖eisTerm k 0 y ((a : F), rep β)‖ := by gcongr`.

Conclude with `norm_tsum_le_tsum_norm ((summable_norm_iff.2 (hlat y hy)).sigma_factor β)`. Establish `hq : Summable (qClass 𝔞 𝔟 k z)`. Establish `: Summable (qClass 𝔞 𝔟 k z ∘ e2)` using `hqsig.congr fun x => (he2 k z x).symm`. Conclude with `(e2.summable_iff).1 this`. Use `⟨hq, ?_⟩` and prove the remaining obligations.

Establish `hQ : HasSum (fun β : NzCls 𝔟 => ∑' ν : posCone 𝔞 (rep β), qTerm 𝔞 k z (ν.1, rep β)) (∑' c, qClass 𝔞 𝔟 k z c)`. Establish `h1 : HasSum (fun x => qTerm 𝔞 k z (x.2.1, rep x.1) : (Σ β : NzCls 𝔟, posCone 𝔞 (rep β)) → ℂ) (∑' c, qClass 𝔞 𝔟 k z c)`. Use `(e2.hasSum_iff (f := qClass 𝔞 𝔟 k z)).2 hq.hasSum` as an intermediate fact. Conclude with `this.congr_fun fun x => (he2 k z x).symm`. Conclude with `h1.sigma fun β => (hqsig.sigma_factor β).hasSum`.

Establish `hL1 : HasSum (fun x : (Σ _β : NzCls 𝔟, (latM 𝔞 : Set F)) => eisTerm k 0 z ((x.2 : F), rep x.1)) (C * ∑' c, qClass 𝔞 𝔟 k z c)`. Establish `hs` using `(hlat z hz).hasSum`. Establish `hg` using `hs.sigma fun β => (GlobalTheory.EisPerB.lattice_sum_eq_cone_sum F hL 𝔞 k hk2 hke (rep β) (rep_ne_zero β) z hz).2`. Rewrite using `[(hQ.mul_left C).unique hg]`. Conclude with `hs`.

Establish `: HasSum (fun x => eisClass 𝔞 𝔟 k 0 z (e1 x).1) (C * ∑' c, qClass 𝔞 𝔟 k z c)` using `hL1.congr_fun fun x => he1 k hke 0 z x`. Conclude with `(e1.hasSum_iff (f := fun c : {c : Quotient (latRel 𝔞 𝔟) // c.out.1.2 ≠ 0} => eisClass 𝔞 𝔟 k 0 z c)).1 this`.
-/
theorem nonconst_terms : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F], GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.Lipschitz →
  ∀ (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (k : ℕ), 2 ≤ k → Even k →
  (∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F, Summable (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisClass 𝔞 𝔟 k 0 z)) →
  ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F, Summable (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.qClass 𝔞 𝔟 k z) ∧
    HasSum (fun c : {c : Quotient (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latRel 𝔞 𝔟) // c.out.1.2 ≠ 0} => GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisClass 𝔞 𝔟 k 0 z c)
      ((GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.omegaFactor 𝔞 : ℂ) ^ k / (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.cK F k : ℂ) * ∑' c, GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.qClass 𝔞 𝔟 k z c) := by
  intro F _ _ _ hL 𝔞 𝔟 k hk2 hke hsum z hz
  obtain ⟨e1, he1⟩ := GlobalTheory.T.exists_equiv_latticeClasses_fibre_summand F 𝔞 𝔟
  obtain ⟨e2, he2⟩ := GlobalTheory.T.exists_equiv_fourierClasses_posCone_summand F 𝔞 𝔟
  set C : ℂ := (omegaFactor 𝔞 : ℂ) ^ k / (cK F k : ℂ) with hC
  set y : Emb F → ℂ := fun τ => Complex.I * ((z τ).im : ℂ) with hy_def
  have hdF : 0 < dF F := abs_pos.2 (by exact_mod_cast discr_ne_zero F)
  have hN : 0 < nrm 𝔞 := by
    unfold nrm
    have h2 : FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := by
      rw [Ne, FractionalIdeal.absNorm_eq_zero_iff]; exact 𝔞.ne_zero
    exact_mod_cast lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg _) h2.symm
  have hCne : C ≠ 0 := by
    have h1 : 0 < omegaFactor 𝔞 := mul_pos (Real.rpow_pos_of_pos hdF _) hN
    have h2 : 0 < cK F k := mul_pos (pow_pos (by exact_mod_cast Nat.factorial_pos _) _) (Real.rpow_pos_of_pos hdF _)
    rw [hC]
    exact div_ne_zero (pow_ne_zero _ (by exact_mod_cast h1.ne')) (by exact_mod_cast h2.ne')
  have hy : y ∈ upperHalf F := fun τ => by simpa [hy_def] using hz τ

  have hlat : ∀ w ∈ upperHalf F, Summable (fun x : (Σ _β : NzCls 𝔟, (latM 𝔞 : Set F)) =>
      eisTerm k 0 w ((x.2 : F), rep x.1)) := by
    intro w hw
    have h1 : Summable (fun c : {c : Quotient (latRel 𝔞 𝔟) // c.out.1.2 ≠ 0} => eisClass 𝔞 𝔟 k 0 w c) :=
      (hsum w hw).subtype _
    have h2 := (e1.summable_iff (f := fun c : {c : Quotient (latRel 𝔞 𝔟) // c.out.1.2 ≠ 0} => eisClass 𝔞 𝔟 k 0 w c)).2 h1
    refine h2.congr fun x => ?_
    simp only [Function.comp_apply]
    exact he1 k hke 0 w x

  have hqfib : ∀ β : NzCls 𝔟, Summable (fun ν : posCone 𝔞 (rep β) => ‖qTerm 𝔞 k z (ν.1, rep β)‖) := by
    intro β
    have := (GlobalTheory.EisPerB.lattice_sum_eq_cone_sum F hL 𝔞 k hk2 hke (rep β) (rep_ne_zero β) y hy).1
    rw [← Complex.summable_ofReal]
    refine this.congr fun ν => ?_
    exact (qTerm_norm 𝔞 k z _).symm
  have hqsig : Summable (fun x : (Σ β : NzCls 𝔟, posCone 𝔞 (rep β)) => qTerm 𝔞 k z (x.2.1, rep x.1)) := by
    refine Summable.of_norm ?_
    rw [summable_sigma_of_nonneg (fun _ => norm_nonneg _)]
    refine ⟨hqfib, ?_⟩
    have hmarg : Summable (fun β : NzCls 𝔟 => ∑' a : (latM 𝔞 : Set F), ‖eisTerm k 0 y ((a : F), rep β)‖) :=
      (summable_norm_iff.2 (hlat y hy)).sigma
    refine Summable.of_nonneg_of_le (fun _ => tsum_nonneg fun _ => norm_nonneg _) (fun β => ?_) (hmarg.mul_left ‖C‖⁻¹)
    obtain ⟨-, hP⟩ := GlobalTheory.EisPerB.lattice_sum_eq_cone_sum F hL 𝔞 k hk2 hke (rep β) (rep_ne_zero β) y hy
    have hfib := hqfib β
    have hT : ((∑' ν : posCone 𝔞 (rep β), ‖qTerm 𝔞 k z (ν.1, rep β)‖ : ℝ) : ℂ) =
        ∑' ν : posCone 𝔞 (rep β), qTerm 𝔞 k y (ν.1, rep β) := by
      rw [Complex.ofReal_tsum]
      exact tsum_congr fun ν => qTerm_norm 𝔞 k z _
    have hE : ∑' ν : posCone 𝔞 (rep β), qTerm 𝔞 k y (ν.1, rep β) =
        C⁻¹ * ∑' a : (latM 𝔞 : Set F), eisTerm k 0 y ((a : F), rep β) := by
      rw [hP.tsum_eq, ← mul_assoc, inv_mul_cancel₀ hCne, one_mul]
    have hnn : 0 ≤ ∑' ν : posCone 𝔞 (rep β), ‖qTerm 𝔞 k z (ν.1, rep β)‖ := tsum_nonneg fun _ => norm_nonneg _
    calc ∑' ν : posCone 𝔞 (rep β), ‖qTerm 𝔞 k z (ν.1, rep β)‖
        = ‖((∑' ν : posCone 𝔞 (rep β), ‖qTerm 𝔞 k z (ν.1, rep β)‖ : ℝ) : ℂ)‖ := by
          rw [Complex.norm_real, Real.norm_of_nonneg hnn]
      _ = ‖C‖⁻¹ * ‖∑' a : (latM 𝔞 : Set F), eisTerm k 0 y ((a : F), rep β)‖ := by
          rw [hT, hE, norm_mul, norm_inv]
      _ ≤ ‖C‖⁻¹ * ∑' a : (latM 𝔞 : Set F), ‖eisTerm k 0 y ((a : F), rep β)‖ := by
          gcongr
          exact norm_tsum_le_tsum_norm ((summable_norm_iff.2 (hlat y hy)).sigma_factor β)
  have hq : Summable (qClass 𝔞 𝔟 k z) := by
    have : Summable (qClass 𝔞 𝔟 k z ∘ e2) := hqsig.congr fun x => (he2 k z x).symm
    exact (e2.summable_iff).1 this
  refine ⟨hq, ?_⟩

  have hQ : HasSum (fun β : NzCls 𝔟 => ∑' ν : posCone 𝔞 (rep β), qTerm 𝔞 k z (ν.1, rep β)) (∑' c, qClass 𝔞 𝔟 k z c) := by
    have h1 : HasSum (fun x => qTerm 𝔞 k z (x.2.1, rep x.1) : (Σ β : NzCls 𝔟, posCone 𝔞 (rep β)) → ℂ) (∑' c, qClass 𝔞 𝔟 k z c) := by
      have := (e2.hasSum_iff (f := qClass 𝔞 𝔟 k z)).2 hq.hasSum
      exact this.congr_fun fun x => (he2 k z x).symm
    exact h1.sigma fun β => (hqsig.sigma_factor β).hasSum
  have hL1 : HasSum (fun x : (Σ _β : NzCls 𝔟, (latM 𝔞 : Set F)) => eisTerm k 0 z ((x.2 : F), rep x.1))
      (C * ∑' c, qClass 𝔞 𝔟 k z c) := by
    have hs := (hlat z hz).hasSum
    have hg := hs.sigma fun β => (GlobalTheory.EisPerB.lattice_sum_eq_cone_sum F hL 𝔞 k hk2 hke (rep β) (rep_ne_zero β) z hz).2
    rw [(hQ.mul_left C).unique hg]
    exact hs
  have : HasSum (fun x => eisClass 𝔞 𝔟 k 0 z (e1 x).1) (C * ∑' c, qClass 𝔞 𝔟 k z c) :=
    hL1.congr_fun fun x => he1 k hke 0 z x
  exact (e1.hasSum_iff (f := fun c : {c : Quotient (latRel 𝔞 𝔟) // c.out.1.2 ≠ 0} => eisClass 𝔞 𝔟 k 0 z c)).1 this

end GlobalTheory.EisNonConst
