import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.UniversalTripleFibreKeyDataNonemptyField
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RigidifiedSectionCorrespondenceExistsUniqueNonva
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.TangentVectorExistsUniqueUniformisingVector
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ThetaSectionNormAndHermitianFormIndepUniformisat
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsIsFramePolynomialOfRuleNumberField
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.FramePolynomialEquivariantAndNeZero
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FibreSectionNowhereZeroOfGenerates
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LieBasisIffTangentBasisPullbackUniversal
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LiePush

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.MetricTest

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

/- English proof (translation)
Take `⟨Φ₀⟩` from `GlobalTheory.LamT.nonempty_fibKey E H Dw l Xo ℂ x hpq`. Take `⟨-, hex, huniq⟩` from `GlobalTheory.SecTieEx.secTie_exists_unique E H Dw l Xo ℂ x Φ₀.T.t Φ₀.m`. Take `⟨th, hth⟩` from `hex s`. Establish `hnz` using `(huniq th s hth).2.1 (GlobalTheory.Frames.secNZ_of_secGen GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo ℂ x s hgen)`. Set `Φ : FibKey Xo ℂ x` to `{ Φ₀ with th := th, th_ne := hnz }`.

Take `⟨u, Hm, χ, -, hAH, hr, hd, -⟩` from `GlobalTheory.thetaUnifAV_all Φ.key.P Φ.key.rig Φ.key.rig_gen`. Take `⟨θ, hθ⟩` from `KeyPow.exists_isFn Φ.key.P.isLB u Φ.key.th`. Take `⟨Fd, hF⟩` from `KeyPow.exists_isAddFundamentalDomain u`. Establish `lift` using `(GlobalTheory.Frames.lieBasis_iff_tanBasis E H Dw l Xo ℂ x Φ.T.t.G Φ.m.φ Φ.m.cart).1`. Use `choose w hw using fun b i => lift (uu b i) (ht b i)`.

Establish `htan : ∀ b i, IsTangent (w b i)` using `fun b i => (Chart.tan_push Φ.m.cart (w b i)).2 (by rw [hw b i]; exact (ht b i).2)`. Use `choose W hW using fun b i => (hd (w b i) (htan b i)).exists`. Conclude with `⟨_, fun b i k => Real.pi * hermForm Hm (W b k) (W b i), Φ, u, Hm, χ, θ, Fd, w, W, hth, hAH, hr, hθ, hF, rfl, fun b i => ⟨hw b i, hW b i⟩, fun _ _ _ => rfl⟩`.
-/
theorem exists_isMetricAt (hpq : 1 ≤ Dw.p + Dw.q) (x : Sp ℂ ⟶ Xo.X) (s : LB.Sec (PPx x))
    (uu : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left))
    (hgen : SecGen x s) (ht : ∀ τ i, IsTanAt x (uu τ i)) : ∃ N Gr, IsMetricAt x s uu N Gr := by
  obtain ⟨Φ₀⟩ := GlobalTheory.LamT.nonempty_fibKey E H Dw l Xo ℂ x hpq
  obtain ⟨-, hex, huniq⟩ := GlobalTheory.SecTieEx.secTie_exists_unique E H Dw l Xo ℂ x Φ₀.T.t Φ₀.m
  obtain ⟨th, hth⟩ := hex s
  have hnz := (huniq th s hth).2.1
    (GlobalTheory.Frames.secNZ_of_secGen GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo ℂ x s hgen)
  let Φ : FibKey Xo ℂ x := { Φ₀ with th := th, th_ne := hnz }
  obtain ⟨u, Hm, χ, -, hAH, hr, hd, -⟩ := GlobalTheory.thetaUnifAV_all Φ.key.P Φ.key.rig Φ.key.rig_gen
  obtain ⟨θ, hθ⟩ := KeyPow.exists_isFn Φ.key.P.isLB u Φ.key.th
  obtain ⟨Fd, hF⟩ := KeyPow.exists_isAddFundamentalDomain u
  have lift := (GlobalTheory.Frames.lieBasis_iff_tanBasis E H Dw l Xo ℂ x Φ.T.t.G Φ.m.φ Φ.m.cart).1
  choose w hw using fun b i => lift (uu b i) (ht b i)
  have htan : ∀ b i, IsTangent (w b i) := fun b i =>
    (Chart.tan_push Φ.m.cart (w b i)).2 (by rw [hw b i]; exact (ht b i).2)
  choose W hW using fun b i => (hd (w b i) (htan b i)).exists
  exact ⟨_, fun b i k => Real.pi * hermForm Hm (W b k) (W b i), Φ, u, Hm, χ, θ, Fd, w, W, hth, hAH, hr, hθ, hF, rfl,
    fun b i => ⟨hw b i, hW b i⟩, fun _ _ _ => rfl⟩

/- English proof (translation)
The claim follows from `exists_isMetricAt hpq y.x y.s y.u y.gen y.tan`.
-/
theorem exists_isMetric (hpq : 1 ≤ Dw.p + Dw.q) {σ : c.F →+* ℂ} (y : FrPt Xo c (CAt σ)) :
    ∃ N Gr, IsMetric y N Gr :=
  exists_isMetricAt hpq y.x y.s y.u y.gen y.tan

/- English proof (translation)
Take `⟨Φ, u, Hm, χ, θ, Fd, w, W, -, hAH, -, -, -, hN, -, hGr⟩` from `h`. Use `⟨hN ▸ div_nonneg (integral_nonneg fun z => by positivity) ENNReal.toReal_nonneg, fun b => ?_⟩` and prove the remaining obligations. Establish `e : Gr b = (Real.pi : ℂ) • ((Matrix.of (W b)).map star * Hm.transpose * (Matrix.of (W b)).transpose)`. Use extensionality with `i k`. Simplify using `[hGr, hermForm, dotProduct, Matrix.mulVec, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]`.

Use `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring` and prove the remaining obligations. Establish `q : ∀ a : Fin (Dw.mult b) → ℂ, star a ⬝ᵥ (Gr b).mulVec a = Real.pi * ((Matrix.of (W b)).vecMul a ⬝ᵥ Hm.mulVec (star ((Matrix.of (W b)).vecMul a)))`. Introduce `a`. Rewrite using `[e, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.mulVec_transpose, Matrix.mulVec_transpose, dotProduct_comm, ← Matrix.dotProduct_mulVec]`. Use `congr 3`.

Use extensionality with `j`. Simplify using `[Matrix.vecMul, dotProduct]`. Use `⟨?_, fun a => ?_⟩` and prove the remaining obligations. Use extensionality with `i k`. Establish `hh : ∀ i j, star (Hm i j) = Hm j i` using `fun i j => hAH.1.apply j i`.

Simplify using `only [Matrix.conjTranspose_apply, hGr, hermForm, dotProduct, Matrix.mulVec, star_mul', star_sum, hh, Pi.star_apply, star_star, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by` and prove the remaining obligations. Simplify using `only [Complex.star_def, Complex.conj_ofReal]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[q, Complex.re_ofReal_mul]`. Distinguish the cases in `h0 : (Matrix.of (W b)).vecMul a = 0`. Simplify using `[h0]`. Conclude with `mul_nonneg Real.pi_pos.le (hAH.2.1 _ h0).le`.
-/
theorem posSemidef_of_isMetric {σ : c.F →+* ℂ} {y : FrPt Xo c (CAt σ)} {N : ℝ}
    {Gr : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) ℂ} (h : IsMetric y N Gr) :
    0 ≤ N ∧ ∀ b, (Gr b).IsHermitian ∧ ∀ a : Fin (Dw.mult b) → ℂ, 0 ≤ (star a ⬝ᵥ (Gr b).mulVec a).re := by
  obtain ⟨Φ, u, Hm, χ, θ, Fd, w, W, -, hAH, -, -, -, hN, -, hGr⟩ := h
  refine ⟨hN ▸ div_nonneg (integral_nonneg fun z => by positivity) ENNReal.toReal_nonneg, fun b => ?_⟩
  have e : Gr b = (Real.pi : ℂ) • ((Matrix.of (W b)).map star * Hm.transpose * (Matrix.of (W b)).transpose) := by
    ext i k
    simp [hGr, hermForm, dotProduct, Matrix.mulVec, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have q : ∀ a : Fin (Dw.mult b) → ℂ, star a ⬝ᵥ (Gr b).mulVec a =
      Real.pi * ((Matrix.of (W b)).vecMul a ⬝ᵥ Hm.mulVec (star ((Matrix.of (W b)).vecMul a))) := by
    intro a
    rw [e, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.dotProduct_mulVec, Matrix.mulVec_transpose, Matrix.mulVec_transpose, dotProduct_comm,
      ← Matrix.dotProduct_mulVec]
    congr 3
    ext j
    simp [Matrix.vecMul, dotProduct]
  refine ⟨?_, fun a => ?_⟩
  · ext i k
    have hh : ∀ i j, star (Hm i j) = Hm j i := fun i j => hAH.1.apply j i
    simp only [Matrix.conjTranspose_apply, hGr, hermForm, dotProduct, Matrix.mulVec, star_mul', star_sum, hh,
      Pi.star_apply, star_star, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by
      simp only [Complex.star_def, Complex.conj_ofReal]; ring
  · rw [q, Complex.re_ofReal_mul]
    by_cases h0 : (Matrix.of (W b)).vecMul a = 0
    · simp [h0]
    · exact mul_nonneg Real.pi_pos.le (hAH.2.1 _ h0).le

/- English proof (translation)
Use `lt_of_le_of_ne (posSemidef_of_isMetric h).1 fun h0 => ?_` and prove the remaining obligations. Take `⟨Φ, u, Hm, χ, θ, Fd, w, W, -, hAH, hR, hθ, hD, hN, -, -⟩` from `h`. Take `⟨n, hn, κ, -, -, -, -, hK⟩` from `keyFormulaPow_and_keyDegree.1`. Use `choose V hV using fun i => ((GlobalTheory.LamT.existsUnique_isDiff_and_linear Φ.key u).1 _ (Φ.key.basis.1 i)).exists`. Establish `k` using `hK Φ.key u Hm (Matrix.of V) χ θ Fd N _ hAH hR hθ hV hD hN rfl`.

Rewrite `k` using `[← h0, zero_pow (Nat.mul_ne_zero (by norm_num) (Nat.one_le_iff_ne_zero.1 (hn _))), MulZeroClass.mul_zero, MulZeroClass.zero_mul]`. Conclude with `absurd k (ne_of_lt (by positivity))`.
-/
theorem pos_of_isMetric {σ : c.F →+* ℂ} {y : FrPt Xo c (CAt σ)} {N : ℝ}
    {Gr : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) ℂ} (h : IsMetric y N Gr) : 0 < N := by
  refine lt_of_le_of_ne (posSemidef_of_isMetric h).1 fun h0 => ?_
  obtain ⟨Φ, u, Hm, χ, θ, Fd, w, W, -, hAH, hR, hθ, hD, hN, -, -⟩ := h
  obtain ⟨n, hn, κ, -, -, -, -, hK⟩ := keyFormulaPow_and_keyDegree.1
  choose V hV using fun i => ((GlobalTheory.LamT.existsUnique_isDiff_and_linear Φ.key u).1 _ (Φ.key.basis.1 i)).exists
  have k := hK Φ.key u Hm (Matrix.of V) χ θ Fd N _ hAH hR hθ hV hD hN rfl
  rw [← h0, zero_pow (Nat.mul_ne_zero (by norm_num) (Nat.one_le_iff_ne_zero.1 (hn _))), MulZeroClass.mul_zero, MulZeroClass.zero_mul] at k
  exact absurd k (ne_of_lt (by positivity))

end GlobalTheory.MetricTest
