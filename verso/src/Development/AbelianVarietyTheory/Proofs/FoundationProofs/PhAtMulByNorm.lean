import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealPeriodLatticeOfCurveDatum
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralJAndAlgebraicData
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaTaylorCoeffAlgebraicAndConjugate
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TaylorSeriesInParameterRescaleOfAlgebraic
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SigmaStarSquareQuotientInModelParameter
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntSerOfIsWq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicComplexIntegralBoundedSeriesLaws
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormPadicModelAbscissaLeOneOfTorsionCoprimeStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SigmaStarMulSqEqProdKernelQuotientsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicComplexIntegralOfSqIntegralOddStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExpMvPhiSeriesSubNsmulEqDivStatement
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.OkpDict
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.AdditionIdentityOfSigmaFormulaUnit
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InertPrimeTeichmuller.NormLeOneOfIntegralInt
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

noncomputable section
namespace GlobalTheory.CMNormPhi

open PowerSeries

variable {p : ℕ} [Fact p.Prime]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h n`. Conclude with `h (Finsupp.single () n)`. Introduce `h n`. Use `h (n ())` as an intermediate fact.

Rewrite `this` using `[PowerSeries.coeff_def (s := n) rfl]`. Then use the resulting hypothesis.
-/
theorem intSer_iff' {f : PowerSeries ℂ_[p]} : IntegralMv f ↔ IntSer f := by
  constructor
  · intro h n; exact h (Finsupp.single () n)
  · intro h n
    have := h (n ())
    rwa [PowerSeries.coeff_def (s := n) rfl] at this

/- English proof (translation)
Take `⟨v, rfl⟩` from `(PowerSeries.X_dvd_iff).2 hh0`. Establish `hv : IntSer v` using `fun m => by simpa [PowerSeries.coeff_succ_X_mul] using hh (m + 1)`. Establish `e' : v ^ 2 * F ^ 2 = C (τ ^ 2) * (f ^ n) ^ 2 * L`. Establish `hX : (X : PowerSeries ℂ_[p]) ^ 2 ≠ 0` using `pow_ne_zero _ X_ne_zero`. Apply `mul_left_cancel₀ hX` to reduce the goal to its premises.

Take the linear combination `e`. Establish `hτ0 : τ ≠ 0` using `by rintro rfl; simp at hτ`. Establish `hFi : F⁻¹ * F = 1` using `PowerSeries.inv_mul_cancel _ (by rw [hF]; exact one_ne_zero)`. Establish `hLi : L * L⁻¹ = 1` using `PowerSeries.mul_inv_cancel _ (by rw [hL0]; exact one_ne_zero)`. Establish `hc : C (τ⁻¹ ^ 2) * C (τ ^ 2) = (1 : PowerSeries ℂ_[p])`.

Rewrite using `[← map_mul, ← mul_pow, inv_mul_cancel₀ hτ0, one_pow, map_one]`. Establish `key : (F⁻¹ * f ^ n) ^ 2 = C (τ⁻¹ ^ 2) * v ^ 2 * L⁻¹`. Take the linear combination `(-(C (τ⁻¹ ^ 2)) * F⁻¹ ^ 2 * L⁻¹) * e' + (C (τ⁻¹ ^ 2) * v ^ 2 * L⁻¹ * (F⁻¹ * F + 1)) * hFi - (F⁻¹ ^ 2 * (f ^ n) ^ 2 * L * L⁻¹) * hc - (F⁻¹ ^ 2 * (f ^ n) ^ 2) * hLi`. Take `⟨hr, -, hC, -, hinv, -⟩` from `GlobalTheory.EvenTheta.SerRing.series_ring_laws p`. Rewrite using `[key]`.

Use `(hr _ _ (hr _ _ ((hC _).2 ?_) (by rw [sq]; exact (hr _ _ hv hv).2.2)).2.2 (hinv L hL (by rw [hL0, norm_one]))).2.2` and prove the remaining obligations. Rewrite using `[norm_pow, norm_inv, hτ]`. Simplify using the standard rewrite rules.
-/
theorem intSer_sq_of_eq (h F f L : PowerSeries ℂ_[p]) (τ : ℂ_[p]) (n : ℕ) (hh : IntSer h)
    (hh0 : constantCoeff h = 0) (hh1 : coeff 1 h = τ) (hτ : ‖τ‖ = 1) (hF : constantCoeff F = 1)
    (hL : IntSer L) (hL0 : constantCoeff L = 1)
    (e : h ^ 2 * F ^ 2 = C (τ ^ 2) * X ^ 2 * (f ^ n) ^ 2 * L) : IntSer ((F⁻¹ * f ^ n) ^ 2) := by
  obtain ⟨v, rfl⟩ := (PowerSeries.X_dvd_iff).2 hh0
  have hv : IntSer v := fun m => by simpa [PowerSeries.coeff_succ_X_mul] using hh (m + 1)
  have e' : v ^ 2 * F ^ 2 = C (τ ^ 2) * (f ^ n) ^ 2 * L := by
    have hX : (X : PowerSeries ℂ_[p]) ^ 2 ≠ 0 := pow_ne_zero _ X_ne_zero
    apply mul_left_cancel₀ hX
    linear_combination e
  have hτ0 : τ ≠ 0 := by rintro rfl; simp at hτ
  have hFi : F⁻¹ * F = 1 := PowerSeries.inv_mul_cancel _ (by rw [hF]; exact one_ne_zero)
  have hLi : L * L⁻¹ = 1 := PowerSeries.mul_inv_cancel _ (by rw [hL0]; exact one_ne_zero)
  have hc : C (τ⁻¹ ^ 2) * C (τ ^ 2) = (1 : PowerSeries ℂ_[p]) := by
    rw [← map_mul, ← mul_pow, inv_mul_cancel₀ hτ0, one_pow, map_one]
  have key : (F⁻¹ * f ^ n) ^ 2 = C (τ⁻¹ ^ 2) * v ^ 2 * L⁻¹ := by
    linear_combination (-(C (τ⁻¹ ^ 2)) * F⁻¹ ^ 2 * L⁻¹) * e' +
      (C (τ⁻¹ ^ 2) * v ^ 2 * L⁻¹ * (F⁻¹ * F + 1)) * hFi -
      (F⁻¹ ^ 2 * (f ^ n) ^ 2 * L * L⁻¹) * hc - (F⁻¹ ^ 2 * (f ^ n) ^ 2) * hLi
  obtain ⟨hr, -, hC, -, hinv, -⟩ := GlobalTheory.EvenTheta.SerRing.series_ring_laws p
  rw [key]
  refine (hr _ _ (hr _ _ ((hC _).2 ?_) (by rw [sq]; exact (hr _ _ hv hv).2.2)).2.2
    (hinv L hL (by rw [hL0, norm_one]))).2.2
  rw [norm_pow, norm_inv, hτ]; simp

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Take `⟨h1, h2⟩` from `(GlobalTheory.SerTransport.transport p g).2.1 1 (one_mem _)`. Simplify using `only [Finset.prod_empty]`. Use `⟨h1, ?_⟩` and prove the remaining obligations.

Rewrite using `[h2, lamC, dif_pos (one_mem _)]`. Conclude with `congrArg C (map_one g.lam)`. Consider the case `insert a s ha ih`. Simplify using `only [Finset.prod_insert ha]`. Rewrite using `[← ih.2]`.

Conclude with `((GlobalTheory.SerTransport.transport p g).1 _ _ (hF a) ih.1).1`.
-/
theorem atU_prod' (g : GL3Theta.G1 p) {ι : Type} (s : Finset ι) {F : ι → ℂ → ℂ} (hF : ∀ i, AlgEnt (F i)) :
    AlgEnt (fun z => ∏ i ∈ s, F i z) ∧ g.atU (fun z => ∏ i ∈ s, F i z) = ∏ i ∈ s, g.atU (F i) := by
  induction s using Finset.induction_on with
  | empty =>
    obtain ⟨h1, h2⟩ := (GlobalTheory.SerTransport.transport p g).2.1 1 (one_mem _)
    simp only [Finset.prod_empty]
    refine ⟨h1, ?_⟩
    rw [h2, lamC, dif_pos (one_mem _)]
    exact congrArg C (map_one g.lam)
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    rw [← ih.2]
    exact ((GlobalTheory.SerTransport.transport p g).1 _ _ (hF a) ih.1).1

/- English proof (translation)
Introduce `D hend _ p _ cc δ g hg hp a hcop`. Establish `hg'` using `hg`. Take `⟨hcc, -, hδ, hΛ, hok⟩` from `hg`. Establish `hcrv : Crv D cc δ` using `⟨hcc, hδ⟩`. Establish `hG` using `(GlobalTheory.InducedType.induced_type D).1`.

Take `⟨hlat, -, hdisc, -, hst⟩` from `GlobalTheory.CurveLattice.lattice_of_curve D hG cc δ hcrv`. Take `⟨⟨-, h2, h3⟩, hwp⟩` from `(GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data D hG).2 cc δ hcrv`. Establish `huse` using `(GlobalTheory.ThetaConj.cmTheta_taylorCoeff_algebraic_and_conjugate D cc δ hcrv).1`. Simplify using `only [tor0] at h2 h3`. Rewrite `hlat`, `hdisc`, `hst`, `h2`, `h3`, `hwp`, `huse` using `[← hΛ]`.

Establish `hlat' : IsLat g.abelian₂` using `hlat`. Establish `halgσ : AlgEnt (sgStar g.abelian₂)`. Establish `e : U1 g.abelian₂ 0 (sgStar g.abelian₂) = sgStar g.abelian₂` using `by funext z; simp [U1]`. Use `huse 0 ⟨1, one_pos, by simp⟩` as an intermediate fact. Rewrite `this` using `[e]`.

Conclude with `⟨hlat'.differentiable, this⟩`. Use `set β : ℂ := D.host.φ₀ ((a : D.host.K) : D.host.E) with hβdef`. Establish `hβQ : β ∈ Qbar` using `Formalism.MainNotions.Ext.test_vector_mem_schwartz_bruhat D _`. Establish `hβst : ∀ ω ∈ g.abelian₂, β * ω ∈ g.abelian₂` using `hst a`. Set `a' : 𝓞 D.host.K` to `⟨Formalism.MainNotions.Ext.conjK D (a : D.host.K), (RingOfIntegers.isIntegral_coe a).map (Formalism.MainNotions.Ext.conjK D).toIntAlgHom⟩`.

Establish `hconj : D.host.φ₀ ((a' : D.host.K) : D.host.E) = starRingEnd ℂ β` using `by show D.host.φ₀ ((Formalism.MainNotions.Ext.conjK D (a : D.host.K) : D.host.K) : D.host.E) = _`. Rewrite using `[Formalism.MainNotions.Ext.conjK_coe]`. Conclude with `D.host.conjE_apply D.host.φ₀ _`. Establish `hN : β * starRingEnd ℂ β = ((Algebra.norm ℤ a : ℤ) : ℂ)`. Establish `h` using `Formalism.MainNotions.UnusedSlot33.HK.norm_int D.host a`.

Rewrite `h` using `[Algebra.intNorm_eq_norm]`. Establish `h'` using `congrArg D.host.φ₀ h`. Establish `hc : D.host.φ₀ (D.host.conj ((a : D.host.K) : D.host.E)) = starRingEnd ℂ β` using `D.host.conjE_apply D.host.φ₀ _`. Rewrite `h'` using `[map_intCast, map_mul, hc]`. Conclude with `h'.symm`.

Establish `hnn : 0 ≤ (Algebra.norm ℤ a : ℤ)`. Establish `e1 : ((Algebra.norm ℤ a : ℤ) : ℂ) = ((Complex.normSq β : ℝ) : ℂ)`. Rewrite using `[← hN, Complex.mul_conj]`. Establish `e2 : ((Algebra.norm ℤ a : ℤ) : ℝ) = Complex.normSq β` using `by exact_mod_cast e1`. Use `Complex.normSq_nonneg β` as an intermediate fact.

Rewrite `this` using `[← e2]`. Conclude with `this` after adjusting the coercions. Establish `hn0 : (Algebra.norm ℤ a).natAbs ≠ 0`. Introduce `h0`. Rewrite `hcop` using `[h0, Nat.coprime_zero_left]`.

Conclude with `(Fact.out : p.Prime).one_lt.ne' hcop`. Take `⟨k, hk⟩` from `Nat.exists_eq_succ_of_ne_zero hn0`. Establish `hnk : (Algebra.norm ℤ a : ℤ) = ((k + 1 : ℕ) : ℤ)`. Use `Int.natAbs_of_nonneg hnn` as an intermediate fact. Rewrite `this` using `[hk]`.

Conclude with `this.symm`. Establish `hβN : β * starRingEnd ℂ β = ((k + 1 : ℕ) : ℂ)` using `by rw [hN, hnk]; push_cast; ring`. Establish `hcop' : Nat.Coprime (k + 1) p`. Use `hcop` as an intermediate fact. Rewrite `this` using `[hk]`. Then use the resulting hypothesis.

Use `set τ := GL3Theta.tauK D g.lam (a : D.host.K) with hτdef`. Establish `hτβ : τ = lamC g.lam β` using `rfl`. Establish `htn : τ * GL3Theta.tauKc D g.lam (a : D.host.K) = ((k + 1 : ℕ) : ℂ_[p])`. Rewrite using `[hτdef, Formalism.MainNotions.Ext.CutA.tau_norm, hnk]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `hτ1 : ‖τ‖ ≤ 1`. Rewrite using `[hτβ, hβdef, ← Formalism.MainNotions.Ext.tauKp_apply]`. Conclude with `PI.OkpW.norm_tau_le _ a`. Establish `hτc1 : ‖GL3Theta.tauKc D g.lam (a : D.host.K)‖ ≤ 1`.

Establish `e : GL3Theta.tauKc D g.lam (a : D.host.K) = Formalism.MainNotions.Ext.tauKp D g.lam (a' : D.host.K)`. Rewrite using `[Formalism.MainNotions.Ext.tauKp_apply]`. Use `show _ = lamC g.lam (D.host.φ₀ ((Formalism.MainNotions.Ext.conjK D (a : D.host.K) : D.host.K) : D.host.E))`. Rewrite using `[Formalism.MainNotions.Ext.conjK_coe]`. Both sides reduce to the same expression.

Rewrite using `[e]`. Conclude with `PI.OkpW.norm_tau_le _ a'`. Establish `hn1 : ‖((k + 1 : ℕ) : ℂ_[p])‖ = 1`. Rewrite using `[← map_natCast (algebraMap ℚ_[p] ℂ_[p]), norm_algebraMap']`. Conclude with `Padic.norm_natCast_eq_one_iff.2 hcop'.symm`.

Establish `hτu : ‖τ‖ = 1`. Use `congrArg norm htn` as an intermediate fact. Rewrite `this` using `[norm_mul, hn1]`. Use polynomial arithmetic with `[norm_nonneg τ, norm_nonneg (GL3Theta.tauKc D g.lam (a : D.host.K))]`. Take `⟨hmul, hconst, -, hscale⟩` from `GlobalTheory.SerTransport.transport p g`.

Take `⟨h, hh, hh0, hh1, hsub⟩` from `hscale hok β hβQ`. Take `⟨hu, hw, hw0, hE, hσ⟩` from `GlobalTheory.EvenTheta.DatumBasic.datum_basic p g hok hlat' h2 h3 hdisc`. Establish `hhI : IntSer h`. Use `hend p cc δ g hg' (τ, GL3Theta.tauKc D g.lam (a : D.host.K)) (subset_closure ⟨a, rfl⟩)` as an intermediate fact. Establish `h' : IntegralMv (h : MvPowerSeries Unit ℂ_[p])` using `by rw [hh]; exact this`.

Conclude with `intSer_iff'.1 h'`. Use `set f := ePhi1 g.lam g.abelian₂ g.C g.wq with hfdef`. Establish `hε0 : ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ≠ 0` using `Units.ne_zero _`. Take `⟨Q, hQ, hfac⟩` from `GlobalTheory.T.sigmaStar_mul_sq_eq_prod_kernel_quotients g.abelian₂ hlat' β k hβst hβN`. Establish `hLaQ : ∀ i, ((k + 1 : ℕ) : ℂ) * Q i ∈ g.abelian₂` using `fun i => by`.

Establish `e : ((k + 1 : ℕ) : ℂ) * Q i = D.host.φ₀ ((a' : D.host.K) : D.host.E) * (β * Q i)`. Rewrite using `[hconj, ← hβN]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `hst a' _ (hQ i).2`.

Establish `hsq : ∀ i, AlgEnt (sqTh g.abelian₂ (Q i)) ∧ g.atU (sqTh g.abelian₂ (Q i)) = f ^ 2 * lineSer g.wq⁻¹ (xAt g (Q i))` using `fun i => GlobalTheory.EvenTheta.Param.sqTh_atU p g hok.2.1 hlat' h2 h3 halgσ (Q i) (hQ i).1 (hwp _ ⟨k + 1, Nat.succ_pos k, hLaQ i⟩ (hQ i).1).1`. Establish `hx : ∀ i, ‖xAt g (Q i)‖ ≤ 1` using `fun i => GlobalTheory.T.norm_padicModelAbscissa_le_one_of_torsion_coprime D p cc δ g hg' (k + 1) (Q i) (Nat.succ_pos k) hcop' (hLaQ i) (hQ i).1`. Take `⟨hr, -, hC, hXI, -, -⟩` from `GlobalTheory.EvenTheta.SerRing.series_ring_laws p`. Establish `hlineI : ∀ x : ℂ_[p], ‖x‖ ≤ 1 → IntSer (lineSer g.wq⁻¹ x)` using `fun x hx => (hr _ _ hw ((hr _ _ ((hC x).2 hx) (by rw [sq]; exact (hr _ _ hXI hXI).2.2)).2.2)).2.1`. Apply the tactic sequence `have hLI : IntSer (∏ i, lineSer g.wq⁻¹ (xAt g (Q i))) := Finset.prod_induction _ IntSer (fun _ _ h1 h2 => (hr _ _ h1 h2).2.2) (fun n => by rw [coeff_one]; split_ifs <;> simp) (fun i _ => hlineI _ (hx i))`.

Establish `hL0 : constantCoeff (∏ i, lineSer g.wq⁻¹ (xAt g (Q i))) = 1`. Rewrite using `[map_prod]`. Use `Finset.prod_eq_one fun i _ => ?_` and prove the remaining obligations. Simplify using `only [lineSer, map_sub, map_mul, map_pow, constantCoeff_X, hw0, constantCoeff_C]`. Simplify using the standard rewrite rules.

Establish `hA` using `hsub _ halgσ`. Establish `hs : HasSubst h` using `HasSubst.of_constantCoeff_zero' hh0`. Establish `lhs : g.atU (fun z => sgStar g.abelian₂ (β * z) ^ 2) = (C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * h * subst h f) ^ 2`. Establish `e` using `(hmul _ _ hA.1 hA.1).1.2`. Establish `e2 : (fun z => sgStar g.abelian₂ (β * z) ^ 2) = fun z => sgStar g.abelian₂ (β * z) * sgStar g.abelian₂ (β * z)`.

Use function extensionality and compare the values at `z`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e2, e, hA.2, hσ, subst_mul hs, subst_mul hs, subst_C, subst_X hs, sq]`. Both sides reduce to the same expression. Establish `hτ2 : lamC g.lam (β ^ 2) = τ ^ 2`.

Establish `e : β ^ 2 = D.host.φ₀ (((a : D.host.K) * (a : D.host.K) : D.host.K) : D.host.E)`. Rewrite using `[IntermediateField.coe_mul, map_mul, sq]`. Rewrite using `[e, sq]`. Conclude with `Formalism.MainNotions.Ext.CutA.tauK_mul D g.lam _ _`. Establish `hG2 : AlgEnt (fun z => sgStar g.abelian₂ z ^ 2) ∧ g.atU (fun z => sgStar g.abelian₂ z ^ 2) = g.atU (sgStar g.abelian₂) ^ 2`.

Establish `e2 : (fun z => sgStar g.abelian₂ z ^ 2) = fun z => sgStar g.abelian₂ z * sgStar g.abelian₂ z` using `by funext z; ring`. Rewrite using `[e2, sq]`. Conclude with `(hmul _ _ halgσ halgσ).1`. Establish `hP` using `atU_prod' g Finset.univ (fun i => (hsq i).1)`. Establish `hGP` using `(hmul _ _ hG2.1 hP.1).1`.

Establish `hc` using `hconst (β ^ 2) (pow_mem hβQ 2)`. Establish `hcGP` using `(hmul _ _ hc.1 hGP.1).1`. Establish `rhs : g.atU (fun z => β ^ 2 * sgStar g.abelian₂ z ^ 2 * ∏ i, sqTh g.abelian₂ (Q i) z) = C (τ ^ 2) * ((C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * X * f) ^ 2 * ∏ i, (f ^ 2 * lineSer g.wq⁻¹ (xAt g (Q i))))`. Establish `e2 : (fun z => β ^ 2 * sgStar g.abelian₂ z ^ 2 * ∏ i, sqTh g.abelian₂ (Q i) z) = fun z => β ^ 2 * (sgStar g.abelian₂ z ^ 2 * ∏ i, sqTh g.abelian₂ (Q i) z)` using `by funext z; ring`. Rewrite using `[e2, hcGP.2, hc.2, hGP.2, hG2.2, hP.2, hσ, hτ2, Finset.prod_congr rfl fun i _ => (hsq i).2]`.

Establish `E1` using `congrArg g.atU (funext hfac : (fun z => sgStar g.abelian₂ (β * z) ^ 2) = fun z => β ^ 2 * sgStar g.abelian₂ z ^ 2 * ∏ i, sqTh g.abelian₂ (Q i) z)`. Rewrite `E1` using `[lhs, rhs, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]`. Establish `e : h ^ 2 * (subst h f : PowerSeries ℂ_[p]) ^ 2 = C (τ ^ 2) * X ^ 2 * (f ^ (k + 1)) ^ 2 * ∏ i, lineSer g.wq⁻¹ (xAt g (Q i))`. Establish `hε2 : (C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) : PowerSeries ℂ_[p]) ^ 2 ≠ 0` using `pow_ne_zero _ fun h0 => hε0 (by simpa using congrArg constantCoeff h0)`. Apply `mul_left_cancel₀ hε2` to reduce the goal to its premises.

Take the linear combination `E1`. Establish `hF0 : constantCoeff (subst h f : PowerSeries ℂ_[p]) = 1`. Rewrite using `[GlobalTheory.SerTransport.const_subst hh0, hE]`. Establish `hI2` using `intSer_sq_of_eq h (subst h f) f _ τ (k + 1) hhI hh0 hh1 hτu hF0 hLI hL0 e`. Establish `hH0 : constantCoeff ((subst h f : PowerSeries ℂ_[p])⁻¹ * f ^ (k + 1)) = 1`.

Rewrite using `[map_mul, PowerSeries.constantCoeff_inv, hF0, map_pow, hE]`. Simplify using the standard rewrite rules. Establish `hI` using `GlobalTheory.T.padicComplex_integral_of_sq_integral_odd p hp _ hH0 hI2`. Take `⟨c0, ex⟩` from `GlobalTheory.T.expMv_phiSeries_sub_nsmul_eq_div p g h (k + 1) hE hh0`. Establish `hmb : (g.mulBy τ (GL3Theta.Xv ()) : MvPowerSeries Unit ℂ_[p]) = h` using `hh.symm`.

Rewrite using `[hmb, htn]`. Use `⟨c0, ?_⟩` and prove the remaining obligations. Rewrite using `[ex]`. Conclude with `intSer_iff'.2 hI`.
-/
theorem phAt_mulBy_norm : ∀ (D : D7), GL3Theta.endInt D → GL3Theta.addInt D → ∀ (p : ℕ) [Fact p.Prime]
    (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : GL3Theta.G1 p), GL3Theta.At D cc δ g → p ≠ 2 →
    ∀ a : 𝓞 D.host.K, Nat.Coprime (Algebra.norm ℤ a).natAbs p →
    GL3Theta.Simeq (g.phAt (g.mulBy (GL3Theta.tauK D g.lam (a : D.host.K)) (GL3Theta.Xv ())) : MvPowerSeries Unit ℂ_[p])
      (MvPowerSeries.C (GL3Theta.tauK D g.lam (a : D.host.K) * GL3Theta.tauKc D g.lam (a : D.host.K)) *
        g.phAt (GL3Theta.Xv ())) := by
  intro D hend _ p _ cc δ g hg hp a hcop
  have hg' := hg
  obtain ⟨hcc, -, hδ, hΛ, hok⟩ := hg
  have hcrv : Crv D cc δ := ⟨hcc, hδ⟩
  have hG := (GlobalTheory.InducedType.induced_type D).1
  obtain ⟨hlat, -, hdisc, -, hst⟩ := GlobalTheory.CurveLattice.lattice_of_curve D hG cc δ hcrv
  obtain ⟨⟨-, h2, h3⟩, hwp⟩ := (GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data D hG).2 cc δ hcrv
  have huse := (GlobalTheory.ThetaConj.cmTheta_taylorCoeff_algebraic_and_conjugate D cc δ hcrv).1
  simp only [tor0] at h2 h3
  rw [← hΛ] at hlat hdisc hst h2 h3 hwp huse
  have hlat' : IsLat g.abelian₂ := hlat
  have halgσ : AlgEnt (sgStar g.abelian₂) := by
    have e : U1 g.abelian₂ 0 (sgStar g.abelian₂) = sgStar g.abelian₂ := by funext z; simp [U1]
    have := huse 0 ⟨1, one_pos, by simp⟩
    rw [e] at this
    exact ⟨hlat'.differentiable, this⟩

  set β : ℂ := D.host.φ₀ ((a : D.host.K) : D.host.E) with hβdef
  have hβQ : β ∈ Qbar := Formalism.MainNotions.Ext.test_vector_mem_schwartz_bruhat D _
  have hβst : ∀ ω ∈ g.abelian₂, β * ω ∈ g.abelian₂ := hst a
  let a' : 𝓞 D.host.K := ⟨Formalism.MainNotions.Ext.conjK D (a : D.host.K),
    (RingOfIntegers.isIntegral_coe a).map (Formalism.MainNotions.Ext.conjK D).toIntAlgHom⟩
  have hconj : D.host.φ₀ ((a' : D.host.K) : D.host.E) = starRingEnd ℂ β := by
    show D.host.φ₀ ((Formalism.MainNotions.Ext.conjK D (a : D.host.K) : D.host.K) : D.host.E) = _
    rw [Formalism.MainNotions.Ext.conjK_coe]
    exact D.host.conjE_apply D.host.φ₀ _
  have hN : β * starRingEnd ℂ β = ((Algebra.norm ℤ a : ℤ) : ℂ) := by
    have h := Formalism.MainNotions.UnusedSlot33.HK.norm_int D.host a
    rw [Algebra.intNorm_eq_norm] at h
    have h' := congrArg D.host.φ₀ h
    have hc : D.host.φ₀ (D.host.conj ((a : D.host.K) : D.host.E)) = starRingEnd ℂ β :=
      D.host.conjE_apply D.host.φ₀ _
    rw [map_intCast, map_mul, hc] at h'
    exact h'.symm
  have hnn : 0 ≤ (Algebra.norm ℤ a : ℤ) := by
    have e1 : ((Algebra.norm ℤ a : ℤ) : ℂ) = ((Complex.normSq β : ℝ) : ℂ) := by
      rw [← hN, Complex.mul_conj]
    have e2 : ((Algebra.norm ℤ a : ℤ) : ℝ) = Complex.normSq β := by exact_mod_cast e1
    have := Complex.normSq_nonneg β
    rw [← e2] at this
    exact_mod_cast this
  have hn0 : (Algebra.norm ℤ a).natAbs ≠ 0 := by
    intro h0
    rw [h0, Nat.coprime_zero_left] at hcop
    exact (Fact.out : p.Prime).one_lt.ne' hcop
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  have hnk : (Algebra.norm ℤ a : ℤ) = ((k + 1 : ℕ) : ℤ) := by
    have := Int.natAbs_of_nonneg hnn
    rw [hk] at this
    exact this.symm
  have hβN : β * starRingEnd ℂ β = ((k + 1 : ℕ) : ℂ) := by rw [hN, hnk]; push_cast; ring
  have hcop' : Nat.Coprime (k + 1) p := by
    have := hcop
    rwa [hk] at this

  set τ := GL3Theta.tauK D g.lam (a : D.host.K) with hτdef
  have hτβ : τ = lamC g.lam β := rfl
  have htn : τ * GL3Theta.tauKc D g.lam (a : D.host.K) = ((k + 1 : ℕ) : ℂ_[p]) := by
    rw [hτdef, Formalism.MainNotions.Ext.CutA.tau_norm, hnk]; push_cast; ring
  have hτ1 : ‖τ‖ ≤ 1 := by
    rw [hτβ, hβdef, ← Formalism.MainNotions.Ext.tauKp_apply]; exact PI.OkpW.norm_tau_le _ a
  have hτc1 : ‖GL3Theta.tauKc D g.lam (a : D.host.K)‖ ≤ 1 := by
    have e : GL3Theta.tauKc D g.lam (a : D.host.K) = Formalism.MainNotions.Ext.tauKp D g.lam (a' : D.host.K) := by
      rw [Formalism.MainNotions.Ext.tauKp_apply]
      show _ = lamC g.lam (D.host.φ₀ ((Formalism.MainNotions.Ext.conjK D (a : D.host.K) : D.host.K) : D.host.E))
      rw [Formalism.MainNotions.Ext.conjK_coe]; rfl
    rw [e]; exact PI.OkpW.norm_tau_le _ a'
  have hn1 : ‖((k + 1 : ℕ) : ℂ_[p])‖ = 1 := by
    rw [← map_natCast (algebraMap ℚ_[p] ℂ_[p]), norm_algebraMap']
    exact Padic.norm_natCast_eq_one_iff.2 hcop'.symm
  have hτu : ‖τ‖ = 1 := by
    have := congrArg norm htn
    rw [norm_mul, hn1] at this
    nlinarith [norm_nonneg τ, norm_nonneg (GL3Theta.tauKc D g.lam (a : D.host.K))]

  obtain ⟨hmul, hconst, -, hscale⟩ := GlobalTheory.SerTransport.transport p g
  obtain ⟨h, hh, hh0, hh1, hsub⟩ := hscale hok β hβQ
  obtain ⟨hu, hw, hw0, hE, hσ⟩ := GlobalTheory.EvenTheta.DatumBasic.datum_basic p g hok hlat' h2 h3 hdisc
  have hhI : IntSer h := by
    have := hend p cc δ g hg' (τ, GL3Theta.tauKc D g.lam (a : D.host.K)) (subset_closure ⟨a, rfl⟩)
    have h' : IntegralMv (h : MvPowerSeries Unit ℂ_[p]) := by rw [hh]; exact this
    exact intSer_iff'.1 h'

  set f := ePhi1 g.lam g.abelian₂ g.C g.wq with hfdef
  have hε0 : ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ≠ 0 := Units.ne_zero _
  obtain ⟨Q, hQ, hfac⟩ := GlobalTheory.T.sigmaStar_mul_sq_eq_prod_kernel_quotients g.abelian₂ hlat' β k hβst hβN
  have hLaQ : ∀ i, ((k + 1 : ℕ) : ℂ) * Q i ∈ g.abelian₂ := fun i => by
    have e : ((k + 1 : ℕ) : ℂ) * Q i = D.host.φ₀ ((a' : D.host.K) : D.host.E) * (β * Q i) := by
      rw [hconj, ← hβN]; ring
    rw [e]; exact hst a' _ (hQ i).2
  have hsq : ∀ i, AlgEnt (sqTh g.abelian₂ (Q i)) ∧
      g.atU (sqTh g.abelian₂ (Q i)) = f ^ 2 * lineSer g.wq⁻¹ (xAt g (Q i)) :=
    fun i => GlobalTheory.EvenTheta.Param.sqTh_atU p g hok.2.1 hlat' h2 h3 halgσ (Q i) (hQ i).1
      (hwp _ ⟨k + 1, Nat.succ_pos k, hLaQ i⟩ (hQ i).1).1
  have hx : ∀ i, ‖xAt g (Q i)‖ ≤ 1 := fun i =>
    GlobalTheory.T.norm_padicModelAbscissa_le_one_of_torsion_coprime D p cc δ g hg' (k + 1) (Q i) (Nat.succ_pos k) hcop' (hLaQ i) (hQ i).1
  obtain ⟨hr, -, hC, hXI, -, -⟩ := GlobalTheory.EvenTheta.SerRing.series_ring_laws p
  have hlineI : ∀ x : ℂ_[p], ‖x‖ ≤ 1 → IntSer (lineSer g.wq⁻¹ x) := fun x hx =>
    (hr _ _ hw ((hr _ _ ((hC x).2 hx) (by rw [sq]; exact (hr _ _ hXI hXI).2.2)).2.2)).2.1
  have hLI : IntSer (∏ i, lineSer g.wq⁻¹ (xAt g (Q i))) :=
    Finset.prod_induction _ IntSer (fun _ _ h1 h2 => (hr _ _ h1 h2).2.2)
      (fun n => by rw [coeff_one]; split_ifs <;> simp) (fun i _ => hlineI _ (hx i))
  have hL0 : constantCoeff (∏ i, lineSer g.wq⁻¹ (xAt g (Q i))) = 1 := by
    rw [map_prod]; refine Finset.prod_eq_one fun i _ => ?_
    simp only [lineSer, map_sub, map_mul, map_pow, constantCoeff_X, hw0, constantCoeff_C]; simp

  have hA := hsub _ halgσ
  have hs : HasSubst h := HasSubst.of_constantCoeff_zero' hh0
  have lhs : g.atU (fun z => sgStar g.abelian₂ (β * z) ^ 2) =
      (C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * h * subst h f) ^ 2 := by
    have e := (hmul _ _ hA.1 hA.1).1.2
    have e2 : (fun z => sgStar g.abelian₂ (β * z) ^ 2) = fun z => sgStar g.abelian₂ (β * z) * sgStar g.abelian₂ (β * z) := by
      funext z; ring
    rw [e2, e, hA.2, hσ, subst_mul hs, subst_mul hs, subst_C, subst_X hs, sq]
    rfl
  have hτ2 : lamC g.lam (β ^ 2) = τ ^ 2 := by
    have e : β ^ 2 = D.host.φ₀ (((a : D.host.K) * (a : D.host.K) : D.host.K) : D.host.E) := by
      rw [IntermediateField.coe_mul, map_mul, sq]
    rw [e, sq]
    exact Formalism.MainNotions.Ext.CutA.tauK_mul D g.lam _ _
  have hG2 : AlgEnt (fun z => sgStar g.abelian₂ z ^ 2) ∧
      g.atU (fun z => sgStar g.abelian₂ z ^ 2) = g.atU (sgStar g.abelian₂) ^ 2 := by
    have e2 : (fun z => sgStar g.abelian₂ z ^ 2) = fun z => sgStar g.abelian₂ z * sgStar g.abelian₂ z := by funext z; ring
    rw [e2, sq]; exact (hmul _ _ halgσ halgσ).1
  have hP := atU_prod' g Finset.univ (fun i => (hsq i).1)
  have hGP := (hmul _ _ hG2.1 hP.1).1
  have hc := hconst (β ^ 2) (pow_mem hβQ 2)
  have hcGP := (hmul _ _ hc.1 hGP.1).1
  have rhs : g.atU (fun z => β ^ 2 * sgStar g.abelian₂ z ^ 2 * ∏ i, sqTh g.abelian₂ (Q i) z) =
      C (τ ^ 2) * ((C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * X * f) ^ 2 *
        ∏ i, (f ^ 2 * lineSer g.wq⁻¹ (xAt g (Q i)))) := by
    have e2 : (fun z => β ^ 2 * sgStar g.abelian₂ z ^ 2 * ∏ i, sqTh g.abelian₂ (Q i) z) =
        fun z => β ^ 2 * (sgStar g.abelian₂ z ^ 2 * ∏ i, sqTh g.abelian₂ (Q i) z) := by funext z; ring
    rw [e2, hcGP.2, hc.2, hGP.2, hG2.2, hP.2, hσ, hτ2, Finset.prod_congr rfl fun i _ => (hsq i).2]
  have E1 := congrArg g.atU (funext hfac : (fun z => sgStar g.abelian₂ (β * z) ^ 2) =
    fun z => β ^ 2 * sgStar g.abelian₂ z ^ 2 * ∏ i, sqTh g.abelian₂ (Q i) z)
  rw [lhs, rhs, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at E1
  have e : h ^ 2 * (subst h f : PowerSeries ℂ_[p]) ^ 2 =
      C (τ ^ 2) * X ^ 2 * (f ^ (k + 1)) ^ 2 * ∏ i, lineSer g.wq⁻¹ (xAt g (Q i)) := by
    have hε2 : (C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) : PowerSeries ℂ_[p]) ^ 2 ≠ 0 :=
      pow_ne_zero _ fun h0 => hε0 (by simpa using congrArg constantCoeff h0)
    apply mul_left_cancel₀ hε2
    linear_combination E1
  have hF0 : constantCoeff (subst h f : PowerSeries ℂ_[p]) = 1 := by
    rw [GlobalTheory.SerTransport.const_subst hh0, hE]
  have hI2 := intSer_sq_of_eq h (subst h f) f _ τ (k + 1) hhI hh0 hh1 hτu hF0 hLI hL0 e
  have hH0 : constantCoeff ((subst h f : PowerSeries ℂ_[p])⁻¹ * f ^ (k + 1)) = 1 := by
    rw [map_mul, PowerSeries.constantCoeff_inv, hF0, map_pow, hE]; simp
  have hI := GlobalTheory.T.padicComplex_integral_of_sq_integral_odd p hp _ hH0 hI2
  obtain ⟨c0, ex⟩ := GlobalTheory.T.expMv_phiSeries_sub_nsmul_eq_div p g h (k + 1) hE hh0
  have hmb : (g.mulBy τ (GL3Theta.Xv ()) : MvPowerSeries Unit ℂ_[p]) = h := hh.symm
  rw [hmb, htn]
  refine ⟨c0, ?_⟩
  rw [ex]
  exact intSer_iff'.2 hI
end GlobalTheory.CMNormPhi
