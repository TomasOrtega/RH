import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTaylorCoeffsAlgebraicAtComplexMultiplicatioStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaPullbackConstantSqEqDetStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AdmissibleCharactersExistStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StandardPairLatticeLocallyOrthonormalBasisStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslationIntertwinerUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpaceSelfDualPairAtMostLineStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HermitianPairingRationalValuesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeOfAdelicPoint
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmQuadraticFormEqAlternatingForm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoordsAlongOrthonormalRealSubfieldBasisStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrthoProductThetaMemThetaSpaceOfLatticeStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SetAverageProdFundamentalDomainPlaneLatticePowStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LocalBasisLatticeIndexCoprimeStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGeneratorPowFractionalIdealNonarchSizeStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDeterminantIdealHermitianLatticeBasisStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrthonormalTransitionDetMulConjEqOneStatement

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.Vacuum

/- English proof (translation)
Establish `h1 : (-1 : ℂ) ^ k = Complex.exp (-(Real.pi * Complex.I) * k)`. Rewrite using `[mul_comm, Complex.exp_int_mul, Complex.exp_neg, Complex.exp_pi_mul_I]`. Evaluate the numerical expressions. Establish `h2 : (k : ℂ) * Complex.I = (ω * (starRingEnd ℂ) t - t * (starRingEnd ℂ) ω) / (area Λ : ℂ)`. Establish `: (k : ℂ) = ((gl3FieldFirst Λ ω (2 * t) : ℝ) : ℂ)` using `by rw [hk]; simp`.

Rewrite using `[this, gl3FieldFirst]`. Establish `h3` using `Complex.sub_conj (ω * (starRingEnd ℂ) t)`. Establish `h4 : (ω * (starRingEnd ℂ) (2 * t)).im = 2 * (ω * (starRingEnd ℂ) t).im`. Simplify using `[map_ofNat]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[h4]`. Simplify using `only [map_mul, Complex.conj_conj] at h3`. Rewrite using `[mul_comm t, h3]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only [U1]`. Rewrite using `[h1, show z + t + ω = z + ω + t by ring]`. Establish `aux : ∀ a x y u v w : ℂ, x + y = u + v + w → a * Complex.exp x * Complex.exp y = Complex.exp u * (a * Complex.exp v * Complex.exp w)`. Introduce `a x y u v w h`. Rewrite using `[mul_assoc, ← Complex.exp_add, h, Complex.exp_add, Complex.exp_add]`.

Expand and normalize the polynomial expressions, which then agree. Apply `aux` to reduce the goal to its premises. Establish `h5 : -((Real.pi : ℂ) * Complex.I) * k = -(Real.pi : ℂ) * (k * Complex.I)` using `by ring`. Rewrite using `[h5, h2]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_orthonormal_basis_family (Λ : AddSubgroup ℂ) (ω t : ℂ) (G : ℂ → ℂ) (k : ℤ) (hk : gl3FieldFirst Λ ω (2 * t) = k) (z : ℂ) :
    U1 Λ ω (U1 Λ t G) z = (-1 : ℂ) ^ k * U1 Λ t (U1 Λ ω G) z := by
  have h1 : (-1 : ℂ) ^ k = Complex.exp (-(Real.pi * Complex.I) * k) := by
    rw [mul_comm, Complex.exp_int_mul, Complex.exp_neg, Complex.exp_pi_mul_I]; norm_num
  have h2 : (k : ℂ) * Complex.I = (ω * (starRingEnd ℂ) t - t * (starRingEnd ℂ) ω) / (area Λ : ℂ) := by
    have : (k : ℂ) = ((gl3FieldFirst Λ ω (2 * t) : ℝ) : ℂ) := by rw [hk]; simp
    rw [this, gl3FieldFirst]
    have h3 := Complex.sub_conj (ω * (starRingEnd ℂ) t)
    have h4 : (ω * (starRingEnd ℂ) (2 * t)).im = 2 * (ω * (starRingEnd ℂ) t).im := by
      simp [map_ofNat]; ring
    rw [h4]
    simp only [map_mul, Complex.conj_conj] at h3
    rw [mul_comm t, h3]; push_cast; ring
  simp only [U1]
  rw [h1, show z + t + ω = z + ω + t by ring]
  have aux : ∀ a x y u v w : ℂ, x + y = u + v + w →
      a * Complex.exp x * Complex.exp y = Complex.exp u * (a * Complex.exp v * Complex.exp w) := by
    intro a x y u v w h
    rw [mul_assoc, ← Complex.exp_add, h, Complex.exp_add, Complex.exp_add]; ring
  apply aux
  have h5 : -((Real.pi : ℂ) * Complex.I) * k = -(Real.pi : ℂ) * (k * Complex.I) := by ring
  rw [h5, h2]; ring

/- English proof (translation)
Simplify using `only [U1]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem translate_operator_smul (Λ : AddSubgroup ℂ) (ω c : ℂ) (G : ℂ → ℂ) (z : ℂ) :
    U1 Λ ω (fun z => c * G z) z = c * U1 Λ ω G z := by
  simp only [U1]; ring

/- English proof (translation)
Establish `hG` using `(GlobalTheory.InducedType.induced_type D).1`. Establish `hlat` using `Parity.lamOf_eq_closure D cc δ hC`. Take `⟨⟨hd, -, -, hU⟩, hz, -⟩` from `GlobalTheory.OddTheta.sgStar_laws _ hlat`. Take `⟨hn, hp⟩` from `Parity.even_im_hermitian_sub D hG cc δ hC t0 ht`. Use `set Λ := lamOf D cc δ`.

Establish `h0 : U1 Λ t0 (sgStar Λ) 0 ≠ 0`. Simplify using `only [U1, zero_add]`. Conclude with `mul_ne_zero (fun h => hn ((hz _).1 h)) (Complex.exp_ne_zero _)`. Use `⟨?_, div_self h0, fun ω hω => ?_⟩` and prove the remaining obligations. Unfold `GL3Theta.th0`.

Use `Differentiable.div_const ?_ _` and prove the remaining obligations. Unfold `U1`. Use `fun_prop`. Take `⟨m, k, hm, hk, hmk⟩` from `hp ω hω`. Use `⟨m, hm, fun z => ?_⟩` and prove the remaining obligations.

Establish `e1 : GL3Theta.th0 Λ t0 = fun z => (U1 Λ t0 (sgStar Λ) 0)⁻¹ * U1 Λ t0 (sgStar Λ) z`. Use function extensionality and compare the values at `z`. Simplify using `only [GL3Theta.th0]`. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : U1 Λ ω (sgStar Λ) = fun z => (if ω / 2 ∈ Λ then 1 else -1) * sgStar Λ z`.

Use function extensionality and compare the values at `(hU ω hω)`. Rewrite using `[e1, translate_operator_smul, exists_orthonormal_basis_family Λ ω t0 _ k hk, e2, translate_operator_smul]`. Establish `e3 : (-1 : ℂ) ^ m * (-1 : ℂ) ^ k * (if ω / 2 ∈ Λ then 1 else -1) = 1`. Rewrite using `[← zpow_add₀ (by norm_num)]`. Use `split_ifs with h`.

Rewrite using `[(hmk.2 h).neg_one_zpow]`. Evaluate the numerical expressions. Rewrite using `[(Int.not_even_iff_odd.1 (fun h' => h (hmk.1 h'))).neg_one_zpow]`. Evaluate the numerical expressions. Take the linear combination `((U1 Λ t0 (sgStar Λ) 0)⁻¹ * U1 Λ t0 (sgStar Λ) z) * e3`.
-/
theorem evenTheta_properties_curveLattice (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (hC : Crv D cc δ) (t0 : ℂ)
    (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0) :
    Differentiable ℂ (GL3Theta.th0 (lamOf D cc δ) t0) ∧ GL3Theta.th0 (lamOf D cc δ) t0 0 = 1 ∧
      ∀ ω ∈ lamOf D cc δ, ∃ m : ℤ, q1 D (lamOf D cc δ) ω = m ∧
        ∀ z, (-1 : ℂ) ^ m * U1 (lamOf D cc δ) ω (GL3Theta.th0 (lamOf D cc δ) t0) z =
          GL3Theta.th0 (lamOf D cc δ) t0 z := by
  have hG := (GlobalTheory.InducedType.induced_type D).1
  have hlat := Parity.lamOf_eq_closure D cc δ hC
  obtain ⟨⟨hd, -, -, hU⟩, hz, -⟩ := GlobalTheory.OddTheta.sgStar_laws _ hlat
  obtain ⟨hn, hp⟩ := Parity.even_im_hermitian_sub D hG cc δ hC t0 ht
  set Λ := lamOf D cc δ
  have h0 : U1 Λ t0 (sgStar Λ) 0 ≠ 0 := by
    simp only [U1, zero_add]
    exact mul_ne_zero (fun h => hn ((hz _).1 h)) (Complex.exp_ne_zero _)
  refine ⟨?_, div_self h0, fun ω hω => ?_⟩
  · unfold GL3Theta.th0
    refine Differentiable.div_const ?_ _
    unfold U1
    fun_prop
  · obtain ⟨m, k, hm, hk, hmk⟩ := hp ω hω
    refine ⟨m, hm, fun z => ?_⟩
    have e1 : GL3Theta.th0 Λ t0 = fun z => (U1 Λ t0 (sgStar Λ) 0)⁻¹ * U1 Λ t0 (sgStar Λ) z := by
      funext z; simp only [GL3Theta.th0]; ring
    have e2 : U1 Λ ω (sgStar Λ) = fun z => (if ω / 2 ∈ Λ then 1 else -1) * sgStar Λ z :=
      funext (hU ω hω)
    rw [e1, translate_operator_smul, exists_orthonormal_basis_family Λ ω t0 _ k hk, e2, translate_operator_smul]
    have e3 : (-1 : ℂ) ^ m * (-1 : ℂ) ^ k * (if ω / 2 ∈ Λ then 1 else -1) = 1 := by
      rw [← zpow_add₀ (by norm_num)]
      split_ifs with h
      · rw [(hmk.2 h).neg_one_zpow]; norm_num
      · rw [(Int.not_even_iff_odd.1 (fun h' => h (hmk.1 h'))).neg_one_zpow]; norm_num
    linear_combination ((U1 Λ t0 (sgStar Λ) 0)⁻¹ * U1 Λ t0 (sgStar Λ) z) * e3

/- English proof (translation)
Simplify using `only [U1]`. Rewrite using `[norm_mul, mul_pow, Complex.norm_exp, ← Real.exp_nat_mul, mul_assoc, ← Real.exp_add, add_comm z ω]`. Use `congr 2`. Establish `h1 : -(Real.pi : ℂ) * z * (starRingEnd ℂ) ω / (area Λ : ℂ) - (Real.pi : ℂ) * ω * (starRingEnd ℂ) ω / (2 * (area Λ : ℂ)) = ((-Real.pi / area Λ : ℝ) : ℂ) * (z * (starRingEnd ℂ) ω + ω * (starRingEnd ℂ) ω / 2)` using `by push_cast; ring`. Rewrite using `[h1, Complex.re_ofReal_mul, Complex.sq_norm, Complex.sq_norm]`.

Simplify using `[Complex.normSq_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem norm_sq_mul_gaussian_latticeTranslate_eq_shifted (Λ : AddSubgroup ℂ) (ω : ℂ) (G : ℂ → ℂ) (z : ℂ) :
    ‖U1 Λ ω G z‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2 / area Λ) =
      ‖G (ω + z)‖ ^ 2 * Real.exp (-Real.pi * ‖ω + z‖ ^ 2 / area Λ) := by
  simp only [U1]
  rw [norm_mul, mul_pow, Complex.norm_exp, ← Real.exp_nat_mul, mul_assoc, ← Real.exp_add, add_comm z ω]
  congr 2
  have h1 : -(Real.pi : ℂ) * z * (starRingEnd ℂ) ω / (area Λ : ℂ) -
      (Real.pi : ℂ) * ω * (starRingEnd ℂ) ω / (2 * (area Λ : ℂ)) =
      ((-Real.pi / area Λ : ℝ) : ℂ) * (z * (starRingEnd ℂ) ω + ω * (starRingEnd ℂ) ω / 2) := by
    push_cast; ring
  rw [h1, Complex.re_ofReal_mul, Complex.sq_norm, Complex.sq_norm]
  simp [Complex.normSq_apply]
  ring

/- English proof (translation)
Establish `hG` using `(GlobalTheory.InducedType.induced_type D).1`. Establish `hlat` using `Parity.lamOf_eq_closure D cc δ hC`. Take `⟨-, -, hpar, hmem, hbij⟩` from `GlobalTheory.T.coords_along_orthonormal_realSubfield_basis D hG cc δ N N' r b hb`. Set `e0 : VC D N N' →ₗ[ℝ] (Fin r → ℂ)` to `{ toFun := fun z k => coordB D (tor0 D cc δ) b k z map_add' := fun z w => by`. Use function extensionality and compare the values at `k`.

Simplify using `[coordB, add_mul, Finset.sum_add_distrib]`. Use the proof step `map_smul' := fun c z => by`. Use function extensionality and compare the values at `k`. Simplify using `[coordB, Finset.mul_sum, mul_assoc] }`. Set `e : VC D N N' ≃ₗ[ℝ] (Fin r → ℂ)` to `LinearEquiv.ofBijective e0 hbij`.

Use `haveI h1 : (MeasureTheory.volume : MeasureTheory.Measure (Fin N → ℂ)).IsAddHaarMeasure := MeasureTheory.Measure.pi.isAddHaarMeasure _`. Use `haveI h2 : (MeasureTheory.volume : MeasureTheory.Measure (Fin N' → Fin N → ℂ)).IsAddHaarMeasure := MeasureTheory.Measure.pi.isAddHaarMeasure _`. Use `haveI h3 : (MeasureTheory.volume : MeasureTheory.Measure (VC D N N')).IsAddHaarMeasure := MeasureTheory.Measure.pi.isAddHaarMeasure _`. Establish `key` using `GlobalTheory.T.setAverage_prod_fundamentalDomain_planeLattice_pow (lamOf D cc δ) hlat (fun z => ‖g z‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2 / area (lamOf D cc δ))) (fun ω hω z => by rw [← norm_sq_mul_gaussian_latticeTranslate_eq_shifted, hg ω hω]) (VC D N N') MeasureTheory.volume r …`. Unfold `normSq nrm1Sq`.

Simplify using `only`. Rewrite using `[← key]`. Use `congr 1`. Use function extensionality and compare the values at `z`. Establish `h1 : (Hf D (tor0 D cc δ) z z).re = ∑ k, ‖e z k‖ ^ 2 / area (lamOf D cc δ)`.

Rewrite using `[Hf, hpar, Complex.div_ofReal_re, Complex.re_sum, Finset.sum_div]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Complex.mul_conj, Complex.ofReal_re, Complex.sq_norm]`. Both sides reduce to the same expression. Rewrite using `[h1, Finset.prod_mul_distrib, ← Real.exp_sum, Finset.mul_sum, pullB, norm_prod, Finset.prod_pow]`.

Use `congr 2`. Use `Finset.sum_congr rfl fun k _ => by ring` and prove the remaining obligations.
-/
theorem normSq_pullB (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (hC : Crv D cc δ) {N N' r : ℕ}
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (hb : OnB D b) (g : ℂ → ℂ)
    (hg : ∀ ω ∈ lamOf D cc δ, ∀ z, ‖U1 (lamOf D cc δ) ω g z‖ = ‖g z‖) :
    normSq D (tor0 D cc δ) (LaB D (tor0 D cc δ) b) (pullB D (tor0 D cc δ) b g) =
      nrm1Sq (lamOf D cc δ) g ^ r := by
  have hG := (GlobalTheory.InducedType.induced_type D).1
  have hlat := Parity.lamOf_eq_closure D cc δ hC
  obtain ⟨-, -, hpar, hmem, hbij⟩ := GlobalTheory.T.coords_along_orthonormal_realSubfield_basis D hG cc δ N N' r b hb
  let e0 : VC D N N' →ₗ[ℝ] (Fin r → ℂ) :=
    { toFun := fun z k => coordB D (tor0 D cc δ) b k z
      map_add' := fun z w => by
        funext k; simp [coordB, add_mul, Finset.sum_add_distrib]
      map_smul' := fun c z => by
        funext k; simp [coordB, Finset.mul_sum, mul_assoc] }
  let e : VC D N N' ≃ₗ[ℝ] (Fin r → ℂ) := LinearEquiv.ofBijective e0 hbij
  haveI h1 : (MeasureTheory.volume : MeasureTheory.Measure (Fin N → ℂ)).IsAddHaarMeasure :=
    MeasureTheory.Measure.pi.isAddHaarMeasure _
  haveI h2 : (MeasureTheory.volume : MeasureTheory.Measure (Fin N' → Fin N → ℂ)).IsAddHaarMeasure :=
    MeasureTheory.Measure.pi.isAddHaarMeasure _
  haveI h3 : (MeasureTheory.volume : MeasureTheory.Measure (VC D N N')).IsAddHaarMeasure :=
    MeasureTheory.Measure.pi.isAddHaarMeasure _
  have key := GlobalTheory.T.setAverage_prod_fundamentalDomain_planeLattice_pow (lamOf D cc δ) hlat
    (fun z => ‖g z‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2 / area (lamOf D cc δ)))
    (fun ω hω z => by rw [← norm_sq_mul_gaussian_latticeTranslate_eq_shifted, hg ω hω]) (VC D N N') MeasureTheory.volume r e
    (LaB D (tor0 D cc δ) b) hmem
  unfold normSq nrm1Sq
  simp only
  rw [← key]
  congr 1
  funext z
  have h1 : (Hf D (tor0 D cc δ) z z).re = ∑ k, ‖e z k‖ ^ 2 / area (lamOf D cc δ) := by
    rw [Hf, hpar, Complex.div_ofReal_re, Complex.re_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.sq_norm]; rfl
  rw [h1, Finset.prod_mul_distrib, ← Real.exp_sum, Finset.mul_sum, pullB, norm_prod, Finset.prod_pow]
  congr 2
  refine Finset.sum_congr rfl fun k _ => by ring

noncomputable def phiQ (D : D7) : D.host.E →+* Qbar :=
  D.host.φ₀.codRestrict (Qbar : IntermediateField ℚ ℂ) fun x => by
    rw [mem_algebraicClosure_iff]
    exact (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom D.host.φ₀.toRatAlgHom

/- English proof (translation)
Simplify using `[lamC, x.2]`.
-/
theorem lamC_coe {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (x : Qbar) : lamC lam (x : ℂ) = lam x := by
  simp [lamC, x.2]

/- English proof (translation)
Rewrite `h`, the goal using `[mem_algebraicClosure_iff]`. Conclude with `h.of_pow hn`.
-/
theorem mem_Qbar_of_pow {x : ℂ} {n : ℕ} (hn : 0 < n) (h : x ^ n ∈ Qbar) : x ∈ Qbar := by
  rw [mem_algebraicClosure_iff] at h ⊢
  exact h.of_pow hn

/- English proof (translation)
Take `⟨q, hq, h0'⟩` from `RingOfIntegers.isIntegral_coe c`. Establish `h0 : q.eval₂ (Int.castRingHom ℂ_[p]) (f (c : K)) = 0`. Use `congrArg f h0'` as an intermediate fact. Rewrite `this` using `[Polynomial.hom_eval₂, map_zero, RingHom.ext_int (f.comp _) (Int.castRingHom _)]`. Then use the resulting hypothesis. Assume the negation of the conclusion as `hlt`.

Use `push Not at hlt`. Use `set x := f (c : K)`. Rewrite `h0` using `[Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hq.coeff_natDegree, map_one, one_mul]`. Establish `h1 : x ^ q.natDegree = -∑ i ∈ Finset.range q.natDegree, Int.castRingHom ℂ_[p] (q.coeff i) * x ^ i`. Take the linear combination `h0`.

Establish `h2 : ‖x ^ q.natDegree‖ < ‖x‖ ^ q.natDegree`. Rewrite using `[h1, norm_neg]`. Break down `Nat.eq_zero_or_pos q.natDegree with hz | hz` into its components or cases. Simplify using `[hz]`. Use `lt_of_le_of_lt (IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (C := ‖x‖ ^ (q.natDegree - 1)) (by positivity) fun i hi => ?_) (pow_lt_pow_right₀ hlt (by omega))` and prove the remaining obligations.

Rewrite using `[norm_mul, norm_pow]`. Establish `h3 : ‖Int.castRingHom ℂ_[p] (q.coeff i)‖ ≤ 1`. Simplify using `using IsUltrametricDist.norm_intCast_le_one ℂ_[p] (q.coeff i)`. Establish `h4 : ‖x‖ ^ i ≤ ‖x‖ ^ (q.natDegree - 1)` using `pow_le_pow_right₀ hlt.le (by have := Finset.mem_range.1 hi; omega)`. Combine the equalities or inequalities in the displayed calculation.

Rewrite `h2` using `[norm_pow]`. Conclude with `lt_irrefl _ h2`.
-/
theorem norm_int_le {K : Type} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime] (f : K →+* ℂ_[p]) (c : 𝓞 K) :
    ‖f (c : K)‖ ≤ 1 := by
  obtain ⟨q, hq, h0'⟩ := RingOfIntegers.isIntegral_coe c
  have h0 : q.eval₂ (Int.castRingHom ℂ_[p]) (f (c : K)) = 0 := by
    have := congrArg f h0'
    rwa [Polynomial.hom_eval₂, map_zero, RingHom.ext_int (f.comp _) (Int.castRingHom _)] at this
  by_contra hlt
  push Not at hlt
  set x := f (c : K)
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hq.coeff_natDegree, map_one, one_mul] at h0
  have h1 : x ^ q.natDegree = -∑ i ∈ Finset.range q.natDegree, Int.castRingHom ℂ_[p] (q.coeff i) * x ^ i := by
    linear_combination h0
  have h2 : ‖x ^ q.natDegree‖ < ‖x‖ ^ q.natDegree := by
    rw [h1, norm_neg]
    rcases Nat.eq_zero_or_pos q.natDegree with hz | hz
    · simp [hz]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
      (C := ‖x‖ ^ (q.natDegree - 1)) (by positivity) fun i hi => ?_) (pow_lt_pow_right₀ hlt (by omega))
    rw [norm_mul, norm_pow]
    have h3 : ‖Int.castRingHom ℂ_[p] (q.coeff i)‖ ≤ 1 := by
      simpa using IsUltrametricDist.norm_intCast_le_one ℂ_[p] (q.coeff i)
    have h4 : ‖x‖ ^ i ≤ ‖x‖ ^ (q.natDegree - 1) :=
      pow_le_pow_right₀ hlt.le (by have := Finset.mem_range.1 hi; omega)
    calc _ ≤ 1 * ‖x‖ ^ i := by gcongr
      _ ≤ _ := by rwa [one_mul]
  rw [norm_pow] at h2
  exact lt_irrefl _ h2

/- English proof (translation)
Establish `h1 : (s : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] (s : ℚ_[p])` using `by simp`. Rewrite using `[h1, norm_algebraMap', Padic.norm_natCast_eq_one_iff]`. Conclude with `h.symm`.
-/
theorem norm_nat_coprime {p : ℕ} [Fact p.Prime] {s : ℕ} (h : Nat.Coprime s p) : ‖(s : ℂ_[p])‖ = 1 := by
  have h1 : (s : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] (s : ℚ_[p]) := by simp
  rw [h1, norm_algebraMap', Padic.norm_natCast_eq_one_iff]
  exact h.symm

/- English proof (translation)
Establish `hG` using `(GlobalTheory.InducedType.induced_type D).1`. Take `⟨I, hI, hloc⟩` from `GlobalTheory.T.exists_determinantIdeal_hermitianLattice_basis D N N' r _ b₀ (GlobalTheory.T.hermitian_pairing_integral_values D N N' _ _ hS hS') (fun i => by`. Take `⟨s, hs, h⟩` from `hl₀.2.1 i`. Use `⟨s, Nat.pos_of_ne_zero ?_, h⟩` and prove the remaining obligations. Introduce and unpack `rfl`.

Simplify using `at hs)`. Establish `hI0 : I ≠ ⊥`. Take `⟨⟨s, hs, h⟩, -⟩` from `hloc 2 b₀ hl₀`. Introduce and unpack `rfl`. Establish `hu` using `GlobalTheory.T.orthonormalTransition_det_mul_conj_eq_one D hG N N' r b₀ b₀ hb₀ hb₀`.

Rewrite `h` using `[Submodule.mem_bot, mul_eq_zero]`. Break down `h with h | h` into its components or cases. Establish `: s = 0` using `by exact_mod_cast h`. Substitute `this` using the available equality. Simplify using `at hs`.

Rewrite `hu` using `[h]`. Simplify using `at hu`. Take `⟨h, α, hh, hα, hv⟩` from `GlobalTheory.T.exists_generator_pow_fractionalIdeal_nonarch_size D.host.K I hI0 hI`. Establish `hαE : (α : D.host.E) ≠ 0` using `by simpa using hα`. Establish `hαE' : D.host.conj (α : D.host.E) ≠ 0` using `by simpa using hα`.

Use `set β : Qbar := phiQ D ((α : D.host.E) / D.host.conj (α : D.host.E)) with hβ`. Take `⟨κ, hκ⟩` from `IsAlgClosed.exists_pow_nat_eq (β : ℂ) (n := 4 * h) (by omega)`. Establish `hκQ : κ ∈ Qbar` using `mem_Qbar_of_pow (n := 4 * h) (by omega) (hκ ▸ β.2)`. Establish `hκ' : (⟨κ, hκQ⟩ : Qbar) ^ (4 * h) = β` using `Subtype.ext (by simpa using hκ)`. Use `⟨κ, ⟨hκQ, fun σ => ?_⟩, fun p _ lam b hb hl => ?_⟩` and prove the remaining obligations.

Establish `h1 : ‖σ β‖ = 1`. Use `D.host.conjE_apply (σ.comp (phiQ D)) (α : D.host.E)` as an intermediate fact. Establish `h2 : σ β = (σ.comp (phiQ D)) (α : D.host.E) / (σ.comp (phiQ D)) (D.host.conj (α : D.host.E))`. Rewrite using `[← map_div₀]`. Both sides reduce to the same expression.

Establish `h3 : (σ.comp (phiQ D)) (D.host.conj (α : D.host.E)) = (starRingEnd ℂ) ((σ.comp (phiQ D)) (α : D.host.E))` using `this`. Rewrite using `[h2, h3, norm_div, Complex.norm_conj, div_self]`. Simplify using `using hα`. Rewrite `h1` using `[← hκ', map_pow, norm_pow]`. Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg _) (by omega)).1 h1`.

Use `set u : D.host.K := (Matrix.of fun i j => hYY D (b j) (b₀ i)).det`. Take `⟨⟨s, hs, hsu⟩, hx⟩` from `hloc p b hl`. Establish `key : ∀ f : D.host.K →+* ℂ_[p], ‖f α‖ = ‖f u‖ ^ h`. Introduce `f`. Set `v : D.host.K →*₀ ℝ` to `(normHom (α := ℂ_[p])).comp f.toMonoidWithZeroHom`.

Establish `hv' : ∀ x, v x = ‖f x‖` using `fun x => rfl`. Establish `h1 : v ((s : D.host.K) * u) = ‖f u‖`. Rewrite using `[hv', map_mul, norm_mul, map_natCast, norm_nat_coprime hs, one_mul]`. Rewrite using `[← h1, ← hv']`. Use `hv v (fun x => norm_nonneg (f x)) (fun x y => ?_) (fun c => norm_int_le f c) _ hsu fun x hxI => ?_` and prove the remaining obligations.

Simplify using `only [hv', map_add]`. Conclude with `IsUltrametricDist.norm_add_le_max _ _`. Take `⟨s', c, hs', e⟩` from `hx x hxI`. Rewrite using `[h1, hv']`. Establish `h2` using `congrArg (fun y => ‖f y‖) e`.

Simplify using `only [map_mul, norm_mul, map_natCast, norm_nat_coprime hs', one_mul] at h2`. Rewrite using `[h2]`. Conclude with `mul_le_of_le_one_left (norm_nonneg _) (norm_int_le f c)`. Establish `k1` using `key ((lam.comp (phiQ D)).comp (algebraMap D.host.K D.host.E))`. Establish `k2` using `key (((lam.comp (phiQ D)).comp D.host.conj.toRingEquiv.toRingHom).comp (algebraMap D.host.K D.host.E))`.

Establish `hu` using `congrArg (fun y => ‖lam (phiQ D y)‖) (GlobalTheory.T.orthonormalTransition_det_mul_conj_eq_one D hG N N' r b₀ b hb₀ hb)`. Simplify using `only [map_mul, norm_mul, map_one, norm_one] at hu`. Express the relevant statement in the definitionally equal form `‖lam (phiQ D (α : D.host.E))‖ = ‖lam (phiQ D (u : D.host.E))‖ ^ h at k1`. Express the relevant statement in the definitionally equal form `‖lam (phiQ D (D.host.conj (α : D.host.E)))‖ = ‖lam (phiQ D (D.host.conj (u : D.host.E)))‖ ^ h at k2`. Express the relevant statement in the definitionally equal form `‖lam (phiQ D (u : D.host.E))‖ * ‖lam (phiQ D (D.host.conj (u : D.host.E)))‖ = 1 at hu`.

Establish `h3 : ‖lam ⟨κ, hκQ⟩‖ ^ (4 * h) = ‖lam (phiQ D (u : D.host.E))‖ ^ (2 * h)`. Rewrite using `[← norm_pow, ← map_pow, hκ', hβ, map_div₀, map_div₀, norm_div, k1, k2, ← div_pow, eq_inv_of_mul_eq_one_right hu, div_inv_eq_mul, pow_mul, sq]`. Rewrite using `[show lamC lam κ = lam ⟨κ, hκQ⟩ from lamC_coe lam ⟨κ, hκQ⟩]`. Use `(pow_left_inj₀ (by positivity) (norm_nonneg _) (n := 2 * h) (by omega)).1 ?_` and prove the remaining obligations. Rewrite using `[← h3, ← pow_mul]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_kappa (D : D7) (N N' r : ℕ) (b₀ : Fin r → Matrix (Fin N') (Fin N) D.host.E) (hb₀ : OnB D b₀)
    (hl₀ : LocBasis D 2 (YYl D (stdL D N) (stdL D N')) b₀) (hS : SD D (stdL D N)) (hS' : SD D (stdL D N')) :
    ∃ κ : ℂ, Mod1All κ ∧ ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p])
      (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), OnB D b →
      LocBasis D p (YYl D (stdL D N) (stdL D N')) b →
      ‖lamC lam κ‖ ^ 2 =
        ‖lam (phiQ D (((Matrix.of fun i j => hYY D (b j) (b₀ i)).det : D.host.K) : D.host.E))‖ := by
  have hG := (GlobalTheory.InducedType.induced_type D).1
  obtain ⟨I, hI, hloc⟩ := GlobalTheory.T.exists_determinantIdeal_hermitianLattice_basis D N N' r _ b₀ (GlobalTheory.T.hermitian_pairing_integral_values D N N' _ _ hS hS') (fun i => by
    obtain ⟨s, hs, h⟩ := hl₀.2.1 i
    refine ⟨s, Nat.pos_of_ne_zero ?_, h⟩
    rintro rfl
    simp at hs)
  have hI0 : I ≠ ⊥ := by
    obtain ⟨⟨s, hs, h⟩, -⟩ := hloc 2 b₀ hl₀
    rintro rfl
    have hu := GlobalTheory.T.orthonormalTransition_det_mul_conj_eq_one D hG N N' r b₀ b₀ hb₀ hb₀
    rw [Submodule.mem_bot, mul_eq_zero] at h
    rcases h with h | h
    · have : s = 0 := by exact_mod_cast h
      subst this; simp at hs
    · rw [h] at hu; simp at hu
  obtain ⟨h, α, hh, hα, hv⟩ := GlobalTheory.T.exists_generator_pow_fractionalIdeal_nonarch_size D.host.K I hI0 hI
  have hαE : (α : D.host.E) ≠ 0 := by simpa using hα
  have hαE' : D.host.conj (α : D.host.E) ≠ 0 := by simpa using hα
  set β : Qbar := phiQ D ((α : D.host.E) / D.host.conj (α : D.host.E)) with hβ
  obtain ⟨κ, hκ⟩ := IsAlgClosed.exists_pow_nat_eq (β : ℂ) (n := 4 * h) (by omega)
  have hκQ : κ ∈ Qbar := mem_Qbar_of_pow (n := 4 * h) (by omega) (hκ ▸ β.2)
  have hκ' : (⟨κ, hκQ⟩ : Qbar) ^ (4 * h) = β := Subtype.ext (by simpa using hκ)
  refine ⟨κ, ⟨hκQ, fun σ => ?_⟩, fun p _ lam b hb hl => ?_⟩
  · have h1 : ‖σ β‖ = 1 := by
      have := D.host.conjE_apply (σ.comp (phiQ D)) (α : D.host.E)
      have h2 : σ β = (σ.comp (phiQ D)) (α : D.host.E) / (σ.comp (phiQ D)) (D.host.conj (α : D.host.E)) := by
        rw [← map_div₀]; rfl
      have h3 : (σ.comp (phiQ D)) (D.host.conj (α : D.host.E)) =
          (starRingEnd ℂ) ((σ.comp (phiQ D)) (α : D.host.E)) := this
      rw [h2, h3, norm_div, Complex.norm_conj, div_self]
      simpa using hα
    rw [← hκ', map_pow, norm_pow] at h1
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by omega)).1 h1
  · set u : D.host.K := (Matrix.of fun i j => hYY D (b j) (b₀ i)).det
    obtain ⟨⟨s, hs, hsu⟩, hx⟩ := hloc p b hl
    have key : ∀ f : D.host.K →+* ℂ_[p], ‖f α‖ = ‖f u‖ ^ h := by
      intro f
      let v : D.host.K →*₀ ℝ := (normHom (α := ℂ_[p])).comp f.toMonoidWithZeroHom
      have hv' : ∀ x, v x = ‖f x‖ := fun x => rfl
      have h1 : v ((s : D.host.K) * u) = ‖f u‖ := by
        rw [hv', map_mul, norm_mul, map_natCast, norm_nat_coprime hs, one_mul]
      rw [← h1, ← hv']
      refine hv v (fun x => norm_nonneg (f x)) (fun x y => ?_) (fun c => norm_int_le f c) _ hsu fun x hxI => ?_
      · simp only [hv', map_add]; exact IsUltrametricDist.norm_add_le_max _ _
      · obtain ⟨s', c, hs', e⟩ := hx x hxI
        rw [h1, hv']
        have h2 := congrArg (fun y => ‖f y‖) e
        simp only [map_mul, norm_mul, map_natCast, norm_nat_coprime hs', one_mul] at h2
        rw [h2]
        exact mul_le_of_le_one_left (norm_nonneg _) (norm_int_le f c)
    have k1 := key ((lam.comp (phiQ D)).comp (algebraMap D.host.K D.host.E))
    have k2 := key (((lam.comp (phiQ D)).comp D.host.conj.toRingEquiv.toRingHom).comp
      (algebraMap D.host.K D.host.E))
    have hu := congrArg (fun y => ‖lam (phiQ D y)‖) (GlobalTheory.T.orthonormalTransition_det_mul_conj_eq_one D hG N N' r b₀ b hb₀ hb)
    simp only [map_mul, norm_mul, map_one, norm_one] at hu
    change ‖lam (phiQ D (α : D.host.E))‖ = ‖lam (phiQ D (u : D.host.E))‖ ^ h at k1
    change ‖lam (phiQ D (D.host.conj (α : D.host.E)))‖ = ‖lam (phiQ D (D.host.conj (u : D.host.E)))‖ ^ h at k2
    change ‖lam (phiQ D (u : D.host.E))‖ * ‖lam (phiQ D (D.host.conj (u : D.host.E)))‖ = 1 at hu
    have h3 : ‖lam ⟨κ, hκQ⟩‖ ^ (4 * h) = ‖lam (phiQ D (u : D.host.E))‖ ^ (2 * h) := by
      rw [← norm_pow, ← map_pow, hκ', hβ, map_div₀, map_div₀, norm_div, k1, k2, ← div_pow,
        eq_inv_of_mul_eq_one_right hu, div_inv_eq_mul, pow_mul, sq]
    rw [show lamC lam κ = lam ⟨κ, hκQ⟩ from lamC_coe lam ⟨κ, hκQ⟩]
    refine (pow_left_inj₀ (by positivity) (norm_nonneg _) (n := 2 * h) (by omega)).1 ?_
    rw [← h3, ← pow_mul]; congr 1; ring

/- English proof (translation)
Use function extensionality and compare the values at `z`. Simplify using `only [Iop, U]`. Rewrite using `[mul_left_comm c]`. Use `congr 1`. Rewrite using `[mul_finsum]`.

Use `congr 1`. Use function extensionality and compare the values at `q`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem Iop_smul (D : D7) (T : Tor D) {N N' : ℕ} (A₁ A₂ : AddSubgroup (VC D N N')) (c : ℂ) (G : VC D N N' → ℂ) :
    Iop D T A₁ A₂ (fun z => c * G z) = fun z => c * Iop D T A₁ A₂ G z := by
  funext z
  simp only [Iop, U]
  rw [mul_left_comm c]
  congr 1
  rw [mul_finsum]
  congr 1; funext q; ring

/- English proof (translation)
Use `⟨h.1.const_mul c, fun x hx z => ?_⟩` and prove the remaining obligations. Use `beta_reduce`. Rewrite using `[← h.2 x hx z]`. Simplify using `only [U]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem smul_mem_ThSp (D : D7) (T : Tor D) {N N' : ℕ} (A : AddSubgroup (VC D N N')) (c : ℂ) (G : VC D N N' → ℂ)
    (h : G ∈ ThSp D T A) : (fun z => c * G z) ∈ ThSp D T A := by
  refine ⟨h.1.const_mul c, fun x hx z => ?_⟩
  beta_reduce
  rw [← h.2 x hx z]; simp only [U]; ring

/- English proof (translation)
Simplify using `only [normSq, norm_mul, hc, one_mul]`.
-/
theorem normSq_smul (D : D7) (T : Tor D) {N N' : ℕ} (A : AddSubgroup (VC D N N')) (c : ℂ) (hc : ‖c‖ = 1)
    (G : VC D N N' → ℂ) : normSq D T A (fun z => c * G z) = normSq D T A G := by
  simp only [normSq, norm_mul, hc, one_mul]

/- English proof (translation)
Introduce `D cc δ hC t0 ht N N' hN`. Establish `hG` using `(GlobalTheory.InducedType.induced_type D).1`. Establish `hSD : ∀ n, SD D (stdL D n)` using `fun n => by`. Take `⟨Lt, h1, h2, -⟩` from `exists_lattice_of_adelic_point D n`. Conclude with `h2 ▸ (h1 1).2`.

Take `⟨hd, h0, hth⟩` from `evenTheta_properties_curveLattice D cc δ hC t0 ht`. Establish `hK0 : KLat D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N')` using `Or.inr ⟨_, _, hSD N, hSD N', rfl⟩`. Establish `hKb : ∀ b : Fin (fF D * N * N') → Matrix (Fin N') (Fin N) D.host.E, OnB D b → KLat D (tor0 D cc δ) (LaB D (tor0 D cc δ) b)` using `fun b hb => Or.inl ⟨_, b, hb, rfl⟩`. Establish `hP : ∀ b : Fin (fF D * N * N') → Matrix (Fin N') (Fin N) D.host.E, OnB D b → pullB D (tor0 D cc δ) b (GL3Theta.th0 (lamOf D cc δ) t0) ∈ ThSp D (tor0 D cc δ) (LaB D (tor0 D cc δ) b)`. Introduce `b hb`.

Take `⟨-, -, hpar, hmem, -⟩` from `GlobalTheory.T.coords_along_orthonormal_realSubfield_basis D hG cc δ N N' _ b hb`. Conclude with `GlobalTheory.T.orthoProductTheta_mem_thetaSpace_of_lattice D _ N N' _ b _ hpar hmem hd hth`. Take `⟨b₀, hb₀, hl₀⟩` from `GlobalTheory.T.standardPairLattice_locally_orthonormal_basis D N N' hN 2 Nat.prime_two`. Take `⟨κ, hκ, hκv⟩` from `exists_kappa D N N' _ b₀ hb₀ hl₀ (hSD N) (hSD N')`. Take `⟨hκQ, hκ1⟩` from `id hκ`.

Establish `hκn : ‖κ‖ = 1` using `hκ1 (Qbar : IntermediateField ℚ ℂ).val.toRingHom`. Establish `hκ0 : κ ≠ 0` using `by rintro rfl; simp at hκn`. Take `⟨-, u1, u2, u3⟩` from `GlobalTheory.T.intertwinerUnitary_all D cc δ hC N N' _ _ (hKb b₀ hb₀) hK0 _ (hP b₀ hb₀)`. Establish `hE : ThetaVectorUpToUnits D (tor0 D cc δ) t0 (stdL D N) (stdL D N') (fun z => κ * Iop D (tor0 D cc δ) (LaB D (tor0 D cc δ) b₀) (La0 D (tor0 D cc δ) N N') (pullB D (tor0 D cc δ) b₀ (GL3Theta.th0 (lamOf D cc δ) t0)) z)` using `⟨b₀, κ, hb₀, hκ, rfl⟩`. Use `⟨_, ⟨smul_mem_ThSp D _ _ κ _ u1, (GlobalTheory.T.thetaTaylorCoeffs_algebraic_at_complexMultiplication D cc δ hC t0 ht N N' _ _ (hSD N) (hSD N') hN _ hE).1, ?_, hE, ?_⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[normSq_smul D _ _ κ hκn, u2]`. Use `normSq_pullB D cc δ hC b₀ hb₀ _ fun ω hω z => ?_` and prove the remaining obligations. Take `⟨m, -, hm⟩` from `hth ω hω`. Rewrite using `[← hm z, norm_mul, norm_zpow]`. Simplify using the standard rewrite rules.

Introduce `p hp lam _`. Take `⟨b, hb, hl⟩` from `GlobalTheory.T.standardPairLattice_locally_orthonormal_basis D N N' hN p hp.out`. Take `⟨c, ζ, m, hm, hζ, hc, hpull⟩` from `GlobalTheory.T.thetaPullbackConstant_sq_eq_det D cc δ hC t0 ht N N' _ b₀ b hb₀ hb`. Take `⟨μ, hμ, hI⟩` from `GlobalTheory.T.admissible_characters_exist D cc δ hC N N' _ _ _ (hKb b₀ hb₀) (hKb b hb) hK0 _ (hP b₀ hb₀)`. Establish `hζQ : ζ ∈ Qbar` using `mem_Qbar_of_pow hm (hζ ▸ one_mem _)`.

Establish `hμQ : μ ∈ Qbar` using `mem_Qbar_of_pow (n := 8) (by norm_num) (hμ ▸ one_mem _)`. Use `set u := phiQ D (((Matrix.of fun i j => hYY D (b j) (b₀ i)).det : D.host.K) : D.host.E) with hu`. Establish `hc' : c ^ 2 = ζ * (u : ℂ)` using `hc`. Establish `hcQ : c ∈ Qbar` using `mem_Qbar_of_pow (n := 2) (by norm_num) (hc' ▸ mul_mem hζQ u.2)`. Establish `n1 : ‖lam ⟨ζ, hζQ⟩‖ = 1`.

Establish `: (⟨ζ, hζQ⟩ : Qbar) ^ m = 1` using `Subtype.ext (by simpa using hζ)`. Use `(pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').1 ?_` and prove the remaining obligations. Rewrite using `[← norm_pow, ← map_pow, this]`. Simplify using the standard rewrite rules. Establish `n2 : ‖lam ⟨μ, hμQ⟩‖ = 1`.

Establish `: (⟨μ, hμQ⟩ : Qbar) ^ 8 = 1` using `Subtype.ext (by simpa using hμ)`. Use `(pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num : 8 ≠ 0)).1 ?_` and prove the remaining obligations. Rewrite using `[← norm_pow, ← map_pow, this]`. Simplify using the standard rewrite rules. Establish `n3 : ‖lam ⟨c, hcQ⟩‖ = ‖lam ⟨κ, hκQ⟩‖`.

Establish `: (⟨c, hcQ⟩ : Qbar) ^ 2 = ⟨ζ, hζQ⟩ * u` using `Subtype.ext (by simpa using hc')`. Use `(pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) (n := 2) (by norm_num)).1 ?_` and prove the remaining obligations. Rewrite using `[← norm_pow, ← map_pow, this, map_mul, norm_mul, n1, one_mul, ← hκv p lam b hb hl, ← lamC_coe lam ⟨κ, hκQ⟩]`. Establish `n4 : ‖lam ⟨κ, hκQ⟩‖ ≠ 0`. Rewrite using `[norm_ne_zero_iff, map_ne_zero]`.

Conclude with `fun h => hκ0 (congrArg Subtype.val h)`. Establish `hc0 : c ≠ 0`. Introduce and unpack `rfl`. Conclude with `n4 (by rw [← n3]; exact norm_eq_zero.2 (map_zero lam))`. Establish `hμ0 : μ ≠ 0` using `by rintro rfl; simp at hμ`.

Set `ε : Qbar` to `⟨κ, hκQ⟩ / (⟨c, hcQ⟩ * ⟨μ, hμQ⟩)`. Establish `hε : (ε : ℂ) = κ / (c * μ)` using `by simp [ε]`. Use `⟨b, ε, hb, hl, ε.2, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[lamC_coe]`. Simplify using `only [ε, map_div₀, map_mul, norm_div, norm_mul, n2, n3, mul_one]`.

Conclude with `div_self n4`. Conclude with `GlobalTheory.T.localBasisLattice_index_coprime D hG cc δ N N' _ _ _ b p hp.out (GlobalTheory.T.theta_space_selfDual_pair_at_most_line D hG cc δ hC N N' _ hK0).2.2.2.2.1 hl`. Rewrite using `[hpull, Iop_smul, hI, hε]`. Use function extensionality and compare the values at `z`. Clear the denominators using the available nonvanishing facts.

Introduce `h`. Establish `h1 : Iop D (tor0 D cc δ) (LaB D (tor0 D cc δ) b₀) (La0 D (tor0 D cc δ) N N') (pullB D (tor0 D cc δ) b₀ (GL3Theta.th0 (lamOf D cc δ) t0)) = fun _ => 0`. Use function extensionality and compare the values at `z`. Conclude with `(mul_eq_zero.1 (congrFun h z)).resolve_left hκ0`. Rewrite `u3` using `[h1]`.

Establish `h2` using `congrFun u3 0`. Simplify using `[Iop, U, pullB, coordB, h0] at h2`.
-/
theorem exists_vacuum : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ →
    ∀ t0, GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → ∀ N N' : ℕ, Even (N * N') →
      ∃ e0 : VC D N N' → ℂ, oddE0 D cc δ t0 N N' e0 ∧ e0 ≠ 0 := by
  intro D cc δ hC t0 ht N N' hN
  have hG := (GlobalTheory.InducedType.induced_type D).1
  have hSD : ∀ n, SD D (stdL D n) := fun n => by
    obtain ⟨Lt, h1, h2, -⟩ := exists_lattice_of_adelic_point D n
    exact h2 ▸ (h1 1).2
  obtain ⟨hd, h0, hth⟩ := evenTheta_properties_curveLattice D cc δ hC t0 ht
  have hK0 : KLat D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') := Or.inr ⟨_, _, hSD N, hSD N', rfl⟩
  have hKb : ∀ b : Fin (fF D * N * N') → Matrix (Fin N') (Fin N) D.host.E, OnB D b →
      KLat D (tor0 D cc δ) (LaB D (tor0 D cc δ) b) := fun b hb => Or.inl ⟨_, b, hb, rfl⟩
  have hP : ∀ b : Fin (fF D * N * N') → Matrix (Fin N') (Fin N) D.host.E, OnB D b →
      pullB D (tor0 D cc δ) b (GL3Theta.th0 (lamOf D cc δ) t0) ∈ ThSp D (tor0 D cc δ) (LaB D (tor0 D cc δ) b) := by
    intro b hb
    obtain ⟨-, -, hpar, hmem, -⟩ := GlobalTheory.T.coords_along_orthonormal_realSubfield_basis D hG cc δ N N' _ b hb
    exact GlobalTheory.T.orthoProductTheta_mem_thetaSpace_of_lattice D _ N N' _ b _ hpar hmem hd hth
  obtain ⟨b₀, hb₀, hl₀⟩ := GlobalTheory.T.standardPairLattice_locally_orthonormal_basis D N N' hN 2 Nat.prime_two
  obtain ⟨κ, hκ, hκv⟩ := exists_kappa D N N' _ b₀ hb₀ hl₀ (hSD N) (hSD N')
  obtain ⟨hκQ, hκ1⟩ := id hκ
  have hκn : ‖κ‖ = 1 := hκ1 (Qbar : IntermediateField ℚ ℂ).val.toRingHom
  have hκ0 : κ ≠ 0 := by rintro rfl; simp at hκn
  obtain ⟨-, u1, u2, u3⟩ := GlobalTheory.T.intertwinerUnitary_all D cc δ hC N N' _ _ (hKb b₀ hb₀) hK0 _ (hP b₀ hb₀)
  have hE : ThetaVectorUpToUnits D (tor0 D cc δ) t0 (stdL D N) (stdL D N') (fun z => κ * Iop D (tor0 D cc δ)
      (LaB D (tor0 D cc δ) b₀) (La0 D (tor0 D cc δ) N N')
      (pullB D (tor0 D cc δ) b₀ (GL3Theta.th0 (lamOf D cc δ) t0)) z) := ⟨b₀, κ, hb₀, hκ, rfl⟩
  refine ⟨_, ⟨smul_mem_ThSp D _ _ κ _ u1,
    (GlobalTheory.T.thetaTaylorCoeffs_algebraic_at_complexMultiplication D cc δ hC t0 ht N N' _ _ (hSD N) (hSD N') hN _ hE).1, ?_, hE, ?_⟩, ?_⟩
  · rw [normSq_smul D _ _ κ hκn, u2]
    refine normSq_pullB D cc δ hC b₀ hb₀ _ fun ω hω z => ?_
    obtain ⟨m, -, hm⟩ := hth ω hω
    rw [← hm z, norm_mul, norm_zpow]; simp
  · intro p hp lam _
    obtain ⟨b, hb, hl⟩ := GlobalTheory.T.standardPairLattice_locally_orthonormal_basis D N N' hN p hp.out
    obtain ⟨c, ζ, m, hm, hζ, hc, hpull⟩ := GlobalTheory.T.thetaPullbackConstant_sq_eq_det D cc δ hC t0 ht N N' _ b₀ b hb₀ hb
    obtain ⟨μ, hμ, hI⟩ := GlobalTheory.T.admissible_characters_exist D cc δ hC N N' _ _ _ (hKb b₀ hb₀) (hKb b hb) hK0 _ (hP b₀ hb₀)
    have hζQ : ζ ∈ Qbar := mem_Qbar_of_pow hm (hζ ▸ one_mem _)
    have hμQ : μ ∈ Qbar := mem_Qbar_of_pow (n := 8) (by norm_num) (hμ ▸ one_mem _)
    set u := phiQ D (((Matrix.of fun i j => hYY D (b j) (b₀ i)).det : D.host.K) : D.host.E) with hu
    have hc' : c ^ 2 = ζ * (u : ℂ) := hc
    have hcQ : c ∈ Qbar := mem_Qbar_of_pow (n := 2) (by norm_num) (hc' ▸ mul_mem hζQ u.2)
    have n1 : ‖lam ⟨ζ, hζQ⟩‖ = 1 := by
      have : (⟨ζ, hζQ⟩ : Qbar) ^ m = 1 := Subtype.ext (by simpa using hζ)
      refine (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').1 ?_
      rw [← norm_pow, ← map_pow, this]; simp
    have n2 : ‖lam ⟨μ, hμQ⟩‖ = 1 := by
      have : (⟨μ, hμQ⟩ : Qbar) ^ 8 = 1 := Subtype.ext (by simpa using hμ)
      refine (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num : 8 ≠ 0)).1 ?_
      rw [← norm_pow, ← map_pow, this]; simp
    have n3 : ‖lam ⟨c, hcQ⟩‖ = ‖lam ⟨κ, hκQ⟩‖ := by
      have : (⟨c, hcQ⟩ : Qbar) ^ 2 = ⟨ζ, hζQ⟩ * u := Subtype.ext (by simpa using hc')
      refine (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) (n := 2) (by norm_num)).1 ?_
      rw [← norm_pow, ← map_pow, this, map_mul, norm_mul, n1, one_mul, ← hκv p lam b hb hl,
        ← lamC_coe lam ⟨κ, hκQ⟩]
    have n4 : ‖lam ⟨κ, hκQ⟩‖ ≠ 0 := by
      rw [norm_ne_zero_iff, map_ne_zero]
      exact fun h => hκ0 (congrArg Subtype.val h)
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact n4 (by rw [← n3]; exact norm_eq_zero.2 (map_zero lam))
    have hμ0 : μ ≠ 0 := by rintro rfl; simp at hμ
    let ε : Qbar := ⟨κ, hκQ⟩ / (⟨c, hcQ⟩ * ⟨μ, hμQ⟩)
    have hε : (ε : ℂ) = κ / (c * μ) := by simp [ε]
    refine ⟨b, ε, hb, hl, ε.2, ?_, ?_, ?_⟩
    · rw [lamC_coe]
      simp only [ε, map_div₀, map_mul, norm_div, norm_mul, n2, n3, mul_one]
      exact div_self n4
    · exact GlobalTheory.T.localBasisLattice_index_coprime D hG cc δ N N' _ _ _ b p hp.out
        (GlobalTheory.T.theta_space_selfDual_pair_at_most_line D hG cc δ hC N N' _ hK0).2.2.2.2.1 hl
    · rw [hpull, Iop_smul, hI, hε]
      funext z
      field_simp
  · intro h
    have h1 : Iop D (tor0 D cc δ) (LaB D (tor0 D cc δ) b₀) (La0 D (tor0 D cc δ) N N')
        (pullB D (tor0 D cc δ) b₀ (GL3Theta.th0 (lamOf D cc δ) t0)) = fun _ => 0 := by
      funext z
      exact (mul_eq_zero.1 (congrFun h z)).resolve_left hκ0
    rw [h1] at u3
    have h2 := congrFun u3 0
    simp [Iop, U, pullB, coordB, h0] at h2

end GlobalTheory.Vacuum
