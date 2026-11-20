import Mathlib
import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StProjectionCoordinateEquation
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Matrix

noncomputable section

/- English proof (translation)
Proceed by induction on `P using MvPolynomial.induction_on with`. Consider the case `C a`. Rewrite using `[← algebraMap_eq, AlgHom.commutes, AlgEquiv.commutes, Polynomial.algebraMap_apply, Polynomial.eval₂_C]`. Conclude with `((aeval y).commutes a).symm`. Consider the case `add p q hp hq => simp [hp, hq, Polynomial.eval₂_add]`.

Consider the case `mul_X p i hp`. Rewrite using `[map_mul, map_mul, Polynomial.eval₂_mul, hp]`. Use `congr 1`. Consider the cases of `i using Fin.cases with`. Consider the case `zero => simp [finSuccEquiv_X_zero]`.

Consider the case `succ i => simp [finSuccEquiv_X_succ]`.
-/
theorem aeval_cons_eq_eval₂_finSuccEquiv {k : ℕ} {B : Type*} [CommRing B] [Algebra ℂ B] (b : B)
    (y : Fin k → B) (P : MvPolynomial (Fin (k + 1)) ℂ) :
    aeval (Fin.cons b y : Fin (k + 1) → B) P =
      Polynomial.eval₂ (aeval y).toRingHom b (finSuccEquiv ℂ k P) := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    rw [← algebraMap_eq, AlgHom.commutes, AlgEquiv.commutes, Polynomial.algebraMap_apply,
      Polynomial.eval₂_C]
    exact ((aeval y).commutes a).symm
  | add p q hp hq => simp [hp, hq, Polynomial.eval₂_add]
  | mul_X p i hp =>
    rw [map_mul, map_mul, Polynomial.eval₂_mul, hp]
    congr 1
    cases i using Fin.cases with
    | zero => simp [finSuccEquiv_X_zero]
    | succ i => simp [finSuccEquiv_X_succ]

/- English proof (translation)
Proceed by induction on `P using MvPolynomial.induction_on with`. Consider the case `C a`. Rewrite using `[pderiv_C, map_zero, ← algebraMap_eq, AlgEquiv.commutes, Polynomial.algebraMap_apply, Polynomial.derivative_C]`. Consider the case `add p q hp hq => simp [hp, hq]`. Consider the case `mul_X p i hp`.

Rewrite using `[Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul, hp, map_mul, Polynomial.derivative_mul]`. Consider the cases of `i using Fin.cases with`. Consider the case `zero`. Simplify using `only [finSuccEquiv_X_zero, pderiv_X_self, map_one, Polynomial.derivative_X]`. Expand and normalize the polynomial expressions, which then agree.

Consider the case `succ i`. Simplify using `only [finSuccEquiv_X_succ, pderiv_X, Pi.single_apply, Fin.succ_ne_zero, if_false, map_zero, Polynomial.derivative_C]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem finSuccEquiv_pderiv_zero {k : ℕ} (P : MvPolynomial (Fin (k + 1)) ℂ) :
    finSuccEquiv ℂ k (pderiv 0 P) = Polynomial.derivative (finSuccEquiv ℂ k P) := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    rw [pderiv_C, map_zero, ← algebraMap_eq, AlgEquiv.commutes, Polynomial.algebraMap_apply,
      Polynomial.derivative_C]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul, hp, map_mul,
      Polynomial.derivative_mul]
    cases i using Fin.cases with
    | zero =>
      simp only [finSuccEquiv_X_zero, pderiv_X_self, map_one, Polynomial.derivative_X]
      ring
    | succ i =>
      simp only [finSuccEquiv_X_succ, pderiv_X, Pi.single_apply, Fin.succ_ne_zero, if_false, map_zero,
        Polynomial.derivative_C]
      ring

/- English proof (translation)
Rewrite using `[← AlgHom.comp_apply, comp_aeval]`. Conclude with `RingHom.congr_fun (coe_aeval_eq_eval _) P`.
-/
theorem algHom_aeval_eq_eval {σ : Type*} {B : Type*} [CommRing B] [Algebra ℂ B] (e : B →ₐ[ℂ] ℂ)
    (v : σ → B) (P : MvPolynomial σ ℂ) : e (aeval v P) = eval (fun i => e (v i)) P := by
  rw [← AlgHom.comp_apply, comp_aeval]
  exact RingHom.congr_fun (coe_aeval_eq_eval _) P

/- English proof (translation)
Introduce `n k J A O hV hO hOne hcov j`. Use `hV.isPrime` as an intermediate fact. Use `set B := MvPolynomial (Fin n) ℂ ⧸ J`. Set `π` to `Ideal.Quotient.mkₐ ℂ J`. Set `y : Fin k → B` to `fun i => π (∑ l, C (A i l) * X l)`.

Set `z : B` to `π (X j)`. Set `φ : MvPolynomial (Fin k) ℂ →+* B` to `(aeval y).toRingHom`. Establish `hev : ∀ x ∈ zeroLocus J, ∃ e : B →ₐ[ℂ] ℂ, (∀ i, e (y i) = (A *ᵥ x) i) ∧ e z = x j`. Introduce `x hx`. Set `e : B →ₐ[ℂ] ℂ` to `Ideal.Quotient.liftₐ J (aeval x) (fun q hq => (RingHom.congr_fun (coe_aeval_eq_eval x) q).trans (hx q hq))`.

Establish `he : ∀ q, e (π q) = aeval x q` using `fun q => rfl`. Use `⟨e, fun i => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[he]`. Simplify using `[Matrix.mulVec, dotProduct]`. Rewrite using `[he, aeval_X]`.

Establish `hind : AlgebraicIndependent ℂ y`. Rewrite using `[algebraicIndependent_iff]`. Introduce `F hF`. Take `⟨y₀, hy₀⟩` from `hOne`. Take `⟨ε, hε, hball⟩` from `Metric.isOpen_iff.mp hO y₀ hy₀`.

Use `funext_set (fun i => Metric.ball (y₀ i) ε) (fun i => infinite_of_mem_nhds (y₀ i) (Metric.ball_mem_nhds _ hε)) fun v hv => ?_` and prove the remaining obligations. Establish `hvO : v ∈ O` using `hball (by rw [ball_pi _ hε]; exact hv)`. Take `⟨x, hx, rfl⟩` from `hcov v hvO`. Take `⟨e, hey, -⟩` from `hev x hx`. Use `algHom_aeval_eq_eval e y F` as an intermediate fact.

Rewrite `this` using `[hF, map_zero]`. Simplify using `only [hey] at this`. Rewrite using `[map_zero, ← this]`. Establish `: Algebra.FiniteType ℂ B` using `inferInstance`. Establish `htr` using `GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg ℂ (A := B)`.

Rewrite `htr` using `[hV.dim]`. Establish `hle : Algebra.trdeg ℂ B ≤ k`. Rewrite using `[← Cardinal.toENat_le_natCast]`. Conclude with `le_of_eq (by exact_mod_cast htr.symm)`. Establish `hdep : ∀ b : B, ∃ p : Polynomial (MvPolynomial (Fin k) ℂ), p ≠ 0 ∧ p.eval₂ φ b = 0`.

Introduce `b`. Establish `hni : ¬ AlgebraicIndependent ℂ (Fin.cons b y : Fin (k + 1) → B)`. Introduce `h`. Use `h.cardinalMk_le_trdeg.trans hle` as an intermediate fact. Rewrite `this` using `[Cardinal.mk_fin, Nat.cast_le]`.

Use linear arithmetic over natural numbers and integers. Rewrite `hni` using `[algebraicIndependent_iff]`. Use `push Not at hni`. Take `⟨R, hR, hR0⟩` from `hni`. Use `⟨finSuccEquiv ℂ k R, fun h => hR0 ((finSuccEquiv ℂ k).injective (by rw [h, map_zero])), ?_⟩` and prove the remaining obligations.

Rewrite using `[← aeval_cons_eq_eval₂_finSuccEquiv, hR]`. Establish `hex : ∃ d, ∃ p : Polynomial (MvPolynomial (Fin k) ℂ), p ≠ 0 ∧ p.natDegree = d ∧ p.eval₂ φ z = 0`. Take `⟨p, hp, hpz⟩` from `hdep z`. Conclude with `⟨_, p, hp, rfl, hpz⟩`. Take `⟨P, hP0, hPd, hPz⟩` from `Nat.find_spec hex`.

Establish `hmin` using `fun d (hd : d < Nat.find hex) => Nat.find_min hex hd`. Establish `hdeg : P.natDegree ≠ 0`. Introduce `h0`. Rewrite `h0` using `[Polynomial.natDegree_eq_zero]`. Take `⟨c, rfl⟩` from `h0`.

Rewrite `hPz` using `[Polynomial.eval₂_C]`. Establish `hc : c = 0` using `(algebraicIndependent_iff.mp hind) c hPz`. Conclude with `hP0 (by rw [hc, map_zero])`. Establish `hP'0 : Polynomial.derivative P ≠ 0` using `fun h => hdeg (Polynomial.derivative_eq_zero.mp h)`. Use `set w := (Polynomial.derivative P).eval₂ φ z with hw`.

Establish `hw0 : w ≠ 0`. Introduce `h`. Use `hmin _ ?_ ⟨_, hP'0, rfl, h⟩` and prove the remaining obligations. Rewrite using `[← hPd]`. Conclude with `Polynomial.natDegree_derivative_lt hdeg`.

Take `⟨r, hr0, hrw⟩` from `hdep w`. Take `⟨q, hrq, hq⟩` from `Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd r hr0 0`. Rewrite `hq` using `[map_zero, sub_zero, Polynomial.X_dvd_iff]`. Rewrite `hrq` using `[map_zero, sub_zero]`. Establish `hqw : q.eval₂ φ w = 0`.

Rewrite `hrw` using `[hrq, Polynomial.eval₂_mul, Polynomial.eval₂_X_pow]`. Conclude with `(mul_eq_zero.mp hrw).resolve_left (pow_ne_zero _ hw0)`. Rewrite `hqw` using `[← Polynomial.divX_mul_X_add q, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_X, Polynomial.eval₂_C]`. Use `⟨(finSuccEquiv ℂ k).symm P, q.coeff 0, hq, fun x hx => ?_, fun x hx hD => ?_⟩` and prove the remaining obligations. Take `⟨e, hey, hez⟩` from `hev x hx`.

Establish `h1` using `algHom_aeval_eq_eval e (Fin.cons z y : Fin (k + 1) → B) ((finSuccEquiv ℂ k).symm P)`. Rewrite `h1` using `[aeval_cons_eq_eval₂_finSuccEquiv, AlgEquiv.apply_symm_apply]`. Establish `h2 : (fun i => e ((Fin.cons z y : Fin (k + 1) → B) i)) = Fin.cons (x j) (A *ᵥ x)`. Use function extensionality and compare the values at `i`. Consider the cases of `i using Fin.cases with`.

Consider the case `zero => simpa using hez`. Consider the case `succ i => simpa using hey i`. Rewrite using `[← h2, ← h1]`. Conclude with `hPz.symm ▸ map_zero e`. Take `⟨e, hey, hez⟩` from `hev x hx`.

Establish `h1` using `algHom_aeval_eq_eval e (Fin.cons z y : Fin (k + 1) → B) (pderiv 0 ((finSuccEquiv ℂ k).symm P))`. Rewrite `h1` using `[aeval_cons_eq_eval₂_finSuccEquiv, finSuccEquiv_pderiv_zero, AlgEquiv.apply_symm_apply]`. Establish `h2 : (fun i => e ((Fin.cons z y : Fin (k + 1) → B) i)) = Fin.cons (x j) (A *ᵥ x)`. Use function extensionality and compare the values at `i`. Consider the cases of `i using Fin.cases with`.

Consider the case `zero => simpa using hez`. Consider the case `succ i => simpa using hey i`. Rewrite using `[← h2, ← h1]`. Introduce `hwx`. Express the relevant statement in the definitionally equal form `e w = 0 at hwx`.

Apply `hD` to reduce the goal to its premises. Establish `h3` using `algHom_aeval_eq_eval e y (q.coeff 0)`. Establish `h4 : φ (q.coeff 0) = -((q.divX.eval₂ φ w) * w)` using `eq_neg_of_add_eq_zero_right hqw`. Express the relevant statement in the definitionally equal form `e (φ (q.coeff 0)) = _ at h3`. Rewrite `h3` using `[h4, map_neg, map_mul, hwx, mul_zero, neg_zero]`.

Simplify using `only [hey] at h3`. Conclude with `h3.symm`.
-/
theorem ProjectionCoordinateEquation.proof : ProjectionCoordinateEquation.Statement := by
  intro n k J A O hV hO hOne hcov j
  have := hV.isPrime
  set B := MvPolynomial (Fin n) ℂ ⧸ J
  let π := Ideal.Quotient.mkₐ ℂ J
  let y : Fin k → B := fun i => π (∑ l, C (A i l) * X l)
  let z : B := π (X j)
  let φ : MvPolynomial (Fin k) ℂ →+* B := (aeval y).toRingHom

  have hev : ∀ x ∈ zeroLocus J, ∃ e : B →ₐ[ℂ] ℂ, (∀ i, e (y i) = (A *ᵥ x) i) ∧ e z = x j := by
    intro x hx
    let e : B →ₐ[ℂ] ℂ := Ideal.Quotient.liftₐ J (aeval x) (fun q hq =>
      (RingHom.congr_fun (coe_aeval_eq_eval x) q).trans (hx q hq))
    have he : ∀ q, e (π q) = aeval x q := fun q => rfl
    refine ⟨e, fun i => ?_, ?_⟩
    · rw [he]
      simp [Matrix.mulVec, dotProduct]
    · rw [he, aeval_X]

  have hind : AlgebraicIndependent ℂ y := by
    rw [algebraicIndependent_iff]
    intro F hF
    obtain ⟨y₀, hy₀⟩ := hOne
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hO y₀ hy₀
    refine funext_set (fun i => Metric.ball (y₀ i) ε)
      (fun i => infinite_of_mem_nhds (y₀ i) (Metric.ball_mem_nhds _ hε)) fun v hv => ?_
    have hvO : v ∈ O := hball (by rw [ball_pi _ hε]; exact hv)
    obtain ⟨x, hx, rfl⟩ := hcov v hvO
    obtain ⟨e, hey, -⟩ := hev x hx
    have := algHom_aeval_eq_eval e y F
    rw [hF, map_zero] at this
    simp only [hey] at this
    rw [map_zero, ← this]

  have : Algebra.FiniteType ℂ B := inferInstance
  have htr := GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg ℂ (A := B)
  rw [hV.dim] at htr
  have hle : Algebra.trdeg ℂ B ≤ k := by
    rw [← Cardinal.toENat_le_natCast]
    exact le_of_eq (by exact_mod_cast htr.symm)
  have hdep : ∀ b : B, ∃ p : Polynomial (MvPolynomial (Fin k) ℂ), p ≠ 0 ∧ p.eval₂ φ b = 0 := by
    intro b
    have hni : ¬ AlgebraicIndependent ℂ (Fin.cons b y : Fin (k + 1) → B) := by
      intro h
      have := h.cardinalMk_le_trdeg.trans hle
      rw [Cardinal.mk_fin, Nat.cast_le] at this
      omega
    rw [algebraicIndependent_iff] at hni
    push Not at hni
    obtain ⟨R, hR, hR0⟩ := hni
    refine ⟨finSuccEquiv ℂ k R, fun h => hR0 ((finSuccEquiv ℂ k).injective (by rw [h, map_zero])), ?_⟩
    rw [← aeval_cons_eq_eval₂_finSuccEquiv, hR]

  have hex : ∃ d, ∃ p : Polynomial (MvPolynomial (Fin k) ℂ), p ≠ 0 ∧ p.natDegree = d ∧ p.eval₂ φ z = 0 := by
    obtain ⟨p, hp, hpz⟩ := hdep z
    exact ⟨_, p, hp, rfl, hpz⟩
  classical
  obtain ⟨P, hP0, hPd, hPz⟩ := Nat.find_spec hex
  have hmin := fun d (hd : d < Nat.find hex) => Nat.find_min hex hd
  have hdeg : P.natDegree ≠ 0 := by
    intro h0
    rw [Polynomial.natDegree_eq_zero] at h0
    obtain ⟨c, rfl⟩ := h0
    rw [Polynomial.eval₂_C] at hPz
    have hc : c = 0 := (algebraicIndependent_iff.mp hind) c hPz
    exact hP0 (by rw [hc, map_zero])
  have hP'0 : Polynomial.derivative P ≠ 0 := fun h =>
    hdeg (Polynomial.derivative_eq_zero.mp h)
  set w := (Polynomial.derivative P).eval₂ φ z with hw
  have hw0 : w ≠ 0 := by
    intro h
    refine hmin _ ?_ ⟨_, hP'0, rfl, h⟩
    rw [← hPd]
    exact Polynomial.natDegree_derivative_lt hdeg

  obtain ⟨r, hr0, hrw⟩ := hdep w
  obtain ⟨q, hrq, hq⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd r hr0 0
  rw [map_zero, sub_zero, Polynomial.X_dvd_iff] at hq
  rw [map_zero, sub_zero] at hrq
  have hqw : q.eval₂ φ w = 0 := by
    rw [hrq, Polynomial.eval₂_mul, Polynomial.eval₂_X_pow] at hrw
    exact (mul_eq_zero.mp hrw).resolve_left (pow_ne_zero _ hw0)
  rw [← Polynomial.divX_mul_X_add q, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_X,
    Polynomial.eval₂_C] at hqw
  refine ⟨(finSuccEquiv ℂ k).symm P, q.coeff 0, hq, fun x hx => ?_, fun x hx hD => ?_⟩
  · obtain ⟨e, hey, hez⟩ := hev x hx
    have h1 := algHom_aeval_eq_eval e (Fin.cons z y : Fin (k + 1) → B) ((finSuccEquiv ℂ k).symm P)
    rw [aeval_cons_eq_eval₂_finSuccEquiv, AlgEquiv.apply_symm_apply] at h1
    have h2 : (fun i => e ((Fin.cons z y : Fin (k + 1) → B) i)) = Fin.cons (x j) (A *ᵥ x) := by
      funext i
      cases i using Fin.cases with
      | zero => simpa using hez
      | succ i => simpa using hey i
    rw [← h2, ← h1]
    exact hPz.symm ▸ map_zero e
  · obtain ⟨e, hey, hez⟩ := hev x hx
    have h1 := algHom_aeval_eq_eval e (Fin.cons z y : Fin (k + 1) → B)
      (pderiv 0 ((finSuccEquiv ℂ k).symm P))
    rw [aeval_cons_eq_eval₂_finSuccEquiv, finSuccEquiv_pderiv_zero, AlgEquiv.apply_symm_apply] at h1
    have h2 : (fun i => e ((Fin.cons z y : Fin (k + 1) → B) i)) = Fin.cons (x j) (A *ᵥ x) := by
      funext i
      cases i using Fin.cases with
      | zero => simpa using hez
      | succ i => simpa using hey i
    rw [← h2, ← h1]
    intro hwx
    change e w = 0 at hwx
    apply hD
    have h3 := algHom_aeval_eq_eval e y (q.coeff 0)
    have h4 : φ (q.coeff 0) = -((q.divX.eval₂ φ w) * w) := eq_neg_of_add_eq_zero_right hqw
    change e (φ (q.coeff 0)) = _ at h3
    rw [h4, map_neg, map_mul, hwx, mul_zero, neg_zero] at h3
    simp only [hey] at h3
    exact h3.symm

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
