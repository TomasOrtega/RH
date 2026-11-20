import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.JacobiThetaHalfCharacteristic
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaNormUnimodularLattice

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.OddThetaNorm
open scoped BigOperators UpperHalfPlane Real
open MeasureTheory

noncomputable section

namespace GlobalTheory.ThetaNullNormSquares

open GlobalTheory.IndefiniteRowSideFullHecke.JacobiThetaHalfCharacteristic (thetaChar IsEvenChar IsPeriodLattice NormTheta0 jacobiTheta₂_half)

/- English proof (translation)
Unfold `GlobalTheory.Glob.IntegralWittCoefficients.normSq1 nrm1Sq`. Establish `: ∀ z : ℂ, -Real.pi * (GlobalTheory.Glob.IntegralWittCoefficients.hf1 Λ z z).re = -Real.pi * ‖z‖ ^ 2 / area Λ` using `fun z => by`. Unfold `GlobalTheory.Glob.IntegralWittCoefficients.hf1`. Rewrite using `[Complex.mul_conj, ← Complex.ofReal_div, Complex.ofReal_re, Complex.normSq_eq_norm_sq]`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only [this]`.
-/
theorem normSq1_eq_nrm1Sq (Λ : AddSubgroup ℂ) (G : ℂ → ℂ) :
    GlobalTheory.Glob.IntegralWittCoefficients.normSq1 Λ G = nrm1Sq Λ G := by
  unfold GlobalTheory.Glob.IntegralWittCoefficients.normSq1 nrm1Sq
  have : ∀ z : ℂ, -Real.pi * (GlobalTheory.Glob.IntegralWittCoefficients.hf1 Λ z z).re = -Real.pi * ‖z‖ ^ 2 / area Λ := fun z => by
    unfold GlobalTheory.Glob.IntegralWittCoefficients.hf1
    rw [Complex.mul_conj, ← Complex.ofReal_div, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    ring
  simp only [this]

/- English proof (translation)
The claim follows from `JacobiDeriv.thetaChar_half_half τ w`.
-/
theorem oddTheta_eq (τ : ℍ) (w : ℂ) : oddTheta τ w =
    Complex.exp (π * Complex.I * (τ / 4 + w + 1 / 2)) * jacobiTheta₂ (w + ((τ : ℂ) + 1) / 2) τ :=
  JacobiDeriv.thetaChar_half_half τ w

/- English proof (translation)
Establish `hy` using `τ.im_ne_zero`. Establish `him : u.im = ((A : ℕ) : ℝ) * τ.im / 2 + M * τ.im - τ.im / 2`. Use `congrArg Complex.im hu` as an intermediate fact. Simplify using `at this`. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite using `[oddTheta_eq, hu, jacobiTheta₂_add_lattice, jacobiTheta₂_half, norm_mul, norm_mul, norm_mul, Complex.norm_exp, Complex.norm_exp, Complex.norm_exp]`. Use `set T := ‖thetaChar A B 0 τ‖`. Establish `e : ∀ x y z w : ℝ, 2 * (x + y + z) + w = 0 → (Real.exp x * (Real.exp y * (Real.exp z * T))) ^ 2 * Real.exp w = T ^ 2` using `fun x y z w h => by`. Establish `: (Real.exp x * (Real.exp y * (Real.exp z * T))) ^ 2 * Real.exp w = Real.exp (2 * (x + y + z) + w) * T ^ 2`. Rewrite using `[Real.exp_add, show 2 * (x + y + z) = (x + y + z) + (x + y + z) by ring, Real.exp_add, Real.exp_add, Real.exp_add]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, h, Real.exp_zero, one_mul]`. Use `e _ _ _ _ ?_` and prove the remaining obligations. Simplify using `[Complex.mul_re, Complex.mul_im, sq, him]`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem norm_sq_oddTheta (τ : ℍ) (A B : Fin 2) (M K : ℤ) (u : ℂ)
    (hu : u + ((τ : ℂ) + 1) / 2 = (((A : ℕ) : ℂ) * τ + ((B : ℕ) : ℂ)) / 2 + (M * τ + K)) :
    ‖oddTheta τ u‖ ^ 2 * Real.exp (-2 * π * u.im ^ 2 / τ.im) = ‖thetaChar A B 0 τ‖ ^ 2 := by
  have hy := τ.im_ne_zero
  have him : u.im = ((A : ℕ) : ℝ) * τ.im / 2 + M * τ.im - τ.im / 2 := by
    have := congrArg Complex.im hu
    simp at this
    linarith
  rw [oddTheta_eq, hu, jacobiTheta₂_add_lattice, jacobiTheta₂_half, norm_mul, norm_mul, norm_mul,
    Complex.norm_exp, Complex.norm_exp, Complex.norm_exp]
  set T := ‖thetaChar A B 0 τ‖
  have e : ∀ x y z w : ℝ, 2 * (x + y + z) + w = 0 →
      (Real.exp x * (Real.exp y * (Real.exp z * T))) ^ 2 * Real.exp w = T ^ 2 := fun x y z w h => by
    have : (Real.exp x * (Real.exp y * (Real.exp z * T))) ^ 2 * Real.exp w =
        Real.exp (2 * (x + y + z) + w) * T ^ 2 := by
      rw [Real.exp_add, show 2 * (x + y + z) = (x + y + z) + (x + y + z) by ring, Real.exp_add,
        Real.exp_add, Real.exp_add]
      ring
    rw [this, h, Real.exp_zero, one_mul]
  refine e _ _ _ _ ?_
  simp [Complex.mul_re, Complex.mul_im, sq, him]
  field_simp
  ring

section

variable {Λ : AddSubgroup ℂ} {a : ℂ} {τ : ℍ} (ha : a ≠ 0)
  (h : ∀ x, x ∈ Λ ↔ ∃ m n : ℤ, a * (m * (τ : ℂ) + n) = x)
include ha h

/- English proof (translation)
Use `⟨a, a * τ, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[LinearIndependent.pair_iff]`. Introduce `s t hst`. Simplify using `only [Complex.real_smul] at hst`. Establish `e : (s : ℂ) + t * τ = 0` using `mul_left_cancel₀ ha (by linear_combination hst)`.

Establish `h1` using `congrArg Complex.im e`. Simplify using `[τ.im_ne_zero] at h1`. Simplify using `[h1] at e`. Conclude with `⟨e, h1⟩`. Use extensionality with `x`.

Rewrite using `[h, AddSubgroup.mem_closure_pair]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨m, n, rfl⟩`. Conclude with `⟨n, m, by simp; ring⟩`. Introduce and unpack `⟨n, m, rfl⟩`.

Conclude with `⟨m, n, by simp; ring⟩`.
-/
theorem lat_gen : ∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ Λ = AddSubgroup.closure {w₁, w₂} := by
  refine ⟨a, a * τ, ?_, ?_⟩
  · rw [LinearIndependent.pair_iff]
    intro s t hst
    simp only [Complex.real_smul] at hst
    have e : (s : ℂ) + t * τ = 0 := mul_left_cancel₀ ha (by linear_combination hst)
    have h1 := congrArg Complex.im e
    simp [τ.im_ne_zero] at h1
    simp [h1] at e
    exact ⟨e, h1⟩
  · ext x
    rw [h, AddSubgroup.mem_closure_pair]
    constructor
    · rintro ⟨m, n, rfl⟩
      exact ⟨n, m, by simp; ring⟩
    · rintro ⟨n, m, rfl⟩
      exact ⟨m, n, by simp; ring⟩

/- English proof (translation)
Take `⟨-, -, huniq, -⟩` from `GlobalTheory.OddTheta.sgStar_laws Λ (lat_gen ha h)`. Establish `hu` using `huniq _ (differentiable_canTheta a τ) (thetaTranslation_canonicalOddTheta_lattice ha h)`. Use `⟨_, fun h0 => ?_, hu⟩` and prove the remaining obligations. Establish `k` using `odd_theta_norm_canonical ha h`. Rewrite `k` using `[show canTheta a τ = fun z => (0 : ℂ) * sgStar Λ z from funext fun z => by rw [hu z, h0], odd_theta_norm_smul]`.

Establish `hy` using `τ.im_pos`. Establish `: 0 < (Real.sqrt (2 * τ.im))⁻¹` using `by positivity`. Rewrite `this` using `[← k]`. Simplify using `at this`.
-/
theorem canTheta_eq : ∃ c : ℂ, c ≠ 0 ∧ ∀ z, canTheta a τ z = c * sgStar Λ z := by
  obtain ⟨-, -, huniq, -⟩ := GlobalTheory.OddTheta.sgStar_laws Λ (lat_gen ha h)
  have hu := huniq _ (differentiable_canTheta a τ) (thetaTranslation_canonicalOddTheta_lattice ha h)
  refine ⟨_, fun h0 => ?_, hu⟩
  have k := odd_theta_norm_canonical ha h
  rw [show canTheta a τ = fun z => (0 : ℂ) * sgStar Λ z from funext fun z => by rw [hu z, h0],
    odd_theta_norm_smul] at k
  have hy := τ.im_pos
  have : 0 < (Real.sqrt (2 * τ.im))⁻¹ := by positivity
  rw [← k] at this
  simp at this

/- English proof (translation)
Take `⟨-, hz, -⟩` from `GlobalTheory.OddTheta.sgStar_laws Λ (lat_gen ha h)`. Take `⟨c, hc, hC⟩` from `canTheta_eq ha h`. Rewrite using `[← hz]`. Use `hC (a * w)` as an intermediate fact. Rewrite `this` using `[canTheta, mul_div_cancel_left₀ _ ha, oddTheta_eq]`.

Prove the components needed by the constructor for the conclusion. Introduce `h0`. Rewrite `this` using `[h0, mul_zero, mul_zero]`. Conclude with `(mul_eq_zero.1 this.symm).resolve_left hc`. Introduce `h0`.

Rewrite `this` using `[h0, mul_zero]`. Simplify `this` using `[Complex.exp_ne_zero]`.
-/
theorem jacobiTheta₂_eq_zero_iff (w : ℂ) :
    jacobiTheta₂ (w + ((τ : ℂ) + 1) / 2) τ = 0 ↔ a * w ∈ Λ := by
  obtain ⟨-, hz, -⟩ := GlobalTheory.OddTheta.sgStar_laws Λ (lat_gen ha h)
  obtain ⟨c, hc, hC⟩ := canTheta_eq ha h
  rw [← hz]
  have := hC (a * w)
  rw [canTheta, mul_div_cancel_left₀ _ ha, oddTheta_eq] at this
  constructor
  · intro h0
    rw [h0, mul_zero, mul_zero] at this
    exact (mul_eq_zero.1 this.symm).resolve_left hc
  · intro h0
    rw [h0, mul_zero] at this
    simpa [Complex.exp_ne_zero] using this

/- English proof (translation)
Take `⟨⟨-, -, -, hU⟩, hz, -⟩` from `GlobalTheory.OddTheta.sgStar_laws Λ (lat_gen ha h)`. Take `⟨c, hc, hC⟩` from `canTheta_eq ha h`. Establish `hy` using `τ.im_pos`. Establish `hn` using `norm_pos_iff.2 ha`. Establish `k` using `odd_theta_norm_canonical ha h`.

Rewrite `k` using `[show canTheta a τ = fun z => c * sgStar Λ z from funext hC, odd_theta_norm_smul]`. Establish `th : GlobalTheory.Glob.IntegralWittCoefficients.th0 Λ t = fun z => (U1 Λ t (sgStar Λ) 0)⁻¹ * U1 Λ t (sgStar Λ) z`. Use function extensionality and compare the values at `fun z => div_eq_inv_mul _ _`. Rewrite using `[th, odd_theta_norm_smul, odd_theta_norm_translate ha h hU, norm_inv, inv_pow]`. Establish `hS : sgStar Λ t ≠ 0` using `fun h0 => ht ((hz t).1 h0)`.

Establish `hU0 : U1 Λ t (sgStar Λ) 0 ≠ 0`. Simplify using `[U1, hS, Complex.exp_ne_zero]`. Establish `hval` using `thetaTranslation_weighted_normSq_mul Λ t (sgStar Λ) 0`. Simplify using `only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_div, Real.exp_zero, mul_one, zero_add] at hval`. Establish `hct` using `hC t`.

Rewrite `hct` using `[canTheta]`. Establish `hnorm : ‖c‖ ^ 2 * ‖U1 Λ t (sgStar Λ) 0‖ ^ 2 = ‖oddTheta τ (t / a)‖ ^ 2 * Real.exp (-2 * π * (t / a).im ^ 2 / τ.im)`. Establish `e1` using `congrArg (fun x => ‖x‖ ^ 2) hct`. Simplify using `only [norm_mul, mul_pow, Complex.norm_exp] at e1`. Establish `ht' : t = a * (t / a)` using `by field_simp`.

Establish `hre : (π * (t / a) ^ 2 / (2 * τ.im) : ℂ).re = π * ((t / a).re ^ 2 - (t / a).im ^ 2) / (2 * τ.im)`. Rewrite using `[show (2 * (τ.im : ℂ)) = ((2 * τ.im : ℝ) : ℂ) by push_cast; rfl, Complex.div_ofReal_re]`. Simplify using `[sq]`. Establish `hnt : ‖t‖ ^ 2 = ‖a‖ ^ 2 * ((t / a).re ^ 2 + (t / a).im ^ 2)` using `by conv_lhs => rw [ht']`. Rewrite using `[norm_mul, mul_pow, Complex.sq_norm (t / a), Complex.normSq_apply]`.

Expand and normalize the polynomial expressions, which then agree. Establish `eX : Real.exp (π * (t / a) ^ 2 / (2 * τ.im) : ℂ).re ^ 2 * Real.exp (-π * ‖t‖ ^ 2 / area Λ) = Real.exp (-2 * π * (t / a).im ^ 2 / τ.im)`. Rewrite using `[sq, ← Real.exp_add, ← Real.exp_add, hre, hnt, LatticeAreaBound.area_eq ha h]`. Use `congr 1`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hval, ← mul_assoc, ← e1, ← eX]`. Expand and normalize the polynomial expressions, which then agree. Establish `hNpos : 0 < nrm1Sq Λ (sgStar Λ)`. Establish `h1 : 0 < ‖c‖ ^ 2 * nrm1Sq Λ (sgStar Λ)` using `by rw [k]; positivity`.

Conclude with `(pos_iff_pos_of_mul_pos h1).1 (by positivity)`. Establish `hP : 0 < ‖U1 Λ t (sgStar Λ) 0‖ ^ 2` using `by positivity`. Use `⟨by positivity, ?_⟩` and prove the remaining obligations. Rewrite using `[← hnorm]`. Establish `hs : 0 < Real.sqrt (2 * τ.im)` using `by positivity`.

Establish `hc2 : 0 < ‖c‖ ^ 2` using `by positivity`. Use `set N := nrm1Sq Λ (sgStar Λ)`. Use `set P := ‖U1 Λ t (sgStar Λ) 0‖ ^ 2`. Use `set s := Real.sqrt (2 * τ.im)`. Use `set C := ‖c‖ ^ 2`.

Rewrite using `[mul_inv, inv_inv, show N⁻¹ = C * s by`. Rewrite using `[inv_eq_iff_eq_inv, eq_comm, inv_eq_iff_eq_inv]`. Clear denominators, using `at k ⊢` for the nonvanishing conditions. Use the proof step `linarith]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem meanSquare_normalizedThetaTwoTorsion {t : ℂ} (ht : t ∉ Λ) :
    0 < nrm1Sq Λ (GlobalTheory.Glob.IntegralWittCoefficients.th0 Λ t) ∧
    (nrm1Sq Λ (GlobalTheory.Glob.IntegralWittCoefficients.th0 Λ t))⁻¹ = Real.sqrt (2 * τ.im) *
      (‖oddTheta τ (t / a)‖ ^ 2 * Real.exp (-2 * π * (t / a).im ^ 2 / τ.im)) := by
  obtain ⟨⟨-, -, -, hU⟩, hz, -⟩ := GlobalTheory.OddTheta.sgStar_laws Λ (lat_gen ha h)
  obtain ⟨c, hc, hC⟩ := canTheta_eq ha h
  have hy := τ.im_pos
  have hn := norm_pos_iff.2 ha
  have k := odd_theta_norm_canonical ha h
  rw [show canTheta a τ = fun z => c * sgStar Λ z from funext hC, odd_theta_norm_smul] at k
  have th : GlobalTheory.Glob.IntegralWittCoefficients.th0 Λ t = fun z => (U1 Λ t (sgStar Λ) 0)⁻¹ * U1 Λ t (sgStar Λ) z :=
    funext fun z => div_eq_inv_mul _ _
  rw [th, odd_theta_norm_smul, odd_theta_norm_translate ha h hU, norm_inv, inv_pow]
  have hS : sgStar Λ t ≠ 0 := fun h0 => ht ((hz t).1 h0)
  have hU0 : U1 Λ t (sgStar Λ) 0 ≠ 0 := by
    simp [U1, hS, Complex.exp_ne_zero]
  have hval := thetaTranslation_weighted_normSq_mul Λ t (sgStar Λ) 0
  simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_div,
    Real.exp_zero, mul_one, zero_add] at hval
  have hct := hC t
  rw [canTheta] at hct
  have hnorm : ‖c‖ ^ 2 * ‖U1 Λ t (sgStar Λ) 0‖ ^ 2 =
      ‖oddTheta τ (t / a)‖ ^ 2 * Real.exp (-2 * π * (t / a).im ^ 2 / τ.im) := by
    have e1 := congrArg (fun x => ‖x‖ ^ 2) hct
    simp only [norm_mul, mul_pow, Complex.norm_exp] at e1
    have ht' : t = a * (t / a) := by field_simp
    have hre : (π * (t / a) ^ 2 / (2 * τ.im) : ℂ).re =
        π * ((t / a).re ^ 2 - (t / a).im ^ 2) / (2 * τ.im) := by
      rw [show (2 * (τ.im : ℂ)) = ((2 * τ.im : ℝ) : ℂ) by push_cast; rfl, Complex.div_ofReal_re]
      simp [sq]
    have hnt : ‖t‖ ^ 2 = ‖a‖ ^ 2 * ((t / a).re ^ 2 + (t / a).im ^ 2) := by
      conv_lhs => rw [ht']
      rw [norm_mul, mul_pow, Complex.sq_norm (t / a), Complex.normSq_apply]
      ring
    have eX : Real.exp (π * (t / a) ^ 2 / (2 * τ.im) : ℂ).re ^ 2 *
        Real.exp (-π * ‖t‖ ^ 2 / area Λ) = Real.exp (-2 * π * (t / a).im ^ 2 / τ.im) := by
      rw [sq, ← Real.exp_add, ← Real.exp_add, hre, hnt, LatticeAreaBound.area_eq ha h]
      congr 1
      field_simp
      ring
    rw [hval, ← mul_assoc, ← e1, ← eX]
    ring
  have hNpos : 0 < nrm1Sq Λ (sgStar Λ) := by
    have h1 : 0 < ‖c‖ ^ 2 * nrm1Sq Λ (sgStar Λ) := by rw [k]; positivity
    exact (pos_iff_pos_of_mul_pos h1).1 (by positivity)
  have hP : 0 < ‖U1 Λ t (sgStar Λ) 0‖ ^ 2 := by positivity
  refine ⟨by positivity, ?_⟩
  rw [← hnorm]
  have hs : 0 < Real.sqrt (2 * τ.im) := by positivity
  have hc2 : 0 < ‖c‖ ^ 2 := by positivity
  set N := nrm1Sq Λ (sgStar Λ)
  set P := ‖U1 Λ t (sgStar Λ) 0‖ ^ 2
  set s := Real.sqrt (2 * τ.im)
  set C := ‖c‖ ^ 2
  rw [mul_inv, inv_inv, show N⁻¹ = C * s by
    rw [inv_eq_iff_eq_inv, eq_comm, inv_eq_iff_eq_inv]
    field_simp at k ⊢
    linarith]
  ring

/- English proof (translation)
Establish `e : thetaChar A B ((m * (τ : ℂ) + n) / 2) τ = 0 ↔ jacobiTheta₂ ((m * (τ : ℂ) + n) / 2 + (((A : ℕ) : ℂ) * τ + ((B : ℕ) : ℂ)) / 2) τ = 0`. Simplify using `[thetaChar, Complex.exp_ne_zero]`. Establish `e2 : (m * (τ : ℂ) + n) / 2 + (((A : ℕ) : ℂ) * τ + ((B : ℕ) : ℂ)) / 2 = (((m + ((A : ℕ) : ℤ) - 1 : ℤ) : ℂ) * τ + ((n + ((B : ℕ) : ℤ) - 1 : ℤ) : ℂ)) / 2 + ((τ : ℂ) + 1) / 2`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e, e2, jacobiTheta₂_eq_zero_iff ha h, ← mul_div_assoc, half_mem_iff ha h]`. Generalize the expression as in `m + ((A : ℕ) : ℤ) - 1 = p`. Generalize the expression as in `n + ((B : ℕ) : ℤ) - 1 = q`. Simplify using `only [parity_simps]`. The claim follows by propositional logic.
-/
theorem thetaChar_eq_zero_iff (A B : Fin 2) (m n : ℤ) :
    thetaChar A B ((m * (τ : ℂ) + n) / 2) τ = 0 ↔
      Even (m + ((A : ℕ) : ℤ) - 1) ∧ Even (n + ((B : ℕ) : ℤ) - 1) := by
  have e : thetaChar A B ((m * (τ : ℂ) + n) / 2) τ = 0 ↔
      jacobiTheta₂ ((m * (τ : ℂ) + n) / 2 + (((A : ℕ) : ℂ) * τ + ((B : ℕ) : ℂ)) / 2) τ = 0 := by
    simp [thetaChar, Complex.exp_ne_zero]
  have e2 : (m * (τ : ℂ) + n) / 2 + (((A : ℕ) : ℂ) * τ + ((B : ℕ) : ℂ)) / 2 =
      (((m + ((A : ℕ) : ℤ) - 1 : ℤ) : ℂ) * τ + ((n + ((B : ℕ) : ℤ) - 1 : ℤ) : ℂ)) / 2 +
        ((τ : ℂ) + 1) / 2 := by
    push_cast
    ring
  rw [e, e2, jacobiTheta₂_eq_zero_iff ha h, ← mul_div_assoc, half_mem_iff ha h]
  generalize m + ((A : ℕ) : ℤ) - 1 = p
  generalize n + ((B : ℕ) : ℤ) - 1 = q
  simp only [parity_simps]
  tauto

end

/- English proof (translation)
Establish `huniq : ∀ A B A' B' : Fin 2, Even (m + ((A : ℕ) : ℤ) - 1) → Even (n + ((B : ℕ) : ℤ) - 1) → Even (m + ((A' : ℕ) : ℤ) - 1) → Even (n + ((B' : ℕ) : ℤ) - 1) → (A', B') = (A, B)`. Introduce `A B A' B' h1 h2 h3 h4`. Rewrite `h1`, `h2`, `h3`, `h4` using `[Int.even_iff]`. Use `A.isLt` as an intermediate fact. Use `B.isLt` as an intermediate fact.

Use `A'.isLt` as an intermediate fact. Use `B'.isLt` as an intermediate fact. Rewrite using `[Prod.mk.injEq, Fin.ext_iff, Fin.ext_iff]`. Use linear arithmetic over natural numbers and integers. Establish `hex : ∃ A B : Fin 2, IsEvenChar A B ∧ Even (m + ((A : ℕ) : ℤ) - 1) ∧ Even (n + ((B : ℕ) : ℤ) - 1)`.

Apply the tactic sequence `rcases Int.even_or_odd m with hm | hm <;> rcases Int.even_or_odd n with hn | hn`. Conclude with `absurd ⟨hm, hn⟩ hnot`. Conclude with `⟨1, 0, by simp [IsEvenChar], by simpa using hm, by simpa [parity_simps] using hn⟩`. Conclude with `⟨0, 1, by simp [IsEvenChar], by simpa [parity_simps] using hm, by simpa using hn⟩`. Conclude with `⟨0, 0, by simp [IsEvenChar], by simpa [parity_simps] using hm, by simpa [parity_simps] using hn⟩`.

Take `⟨A, B, h0, h1, h2⟩` from `hex`. Conclude with `⟨(A, B), ⟨h0, h1, h2⟩, fun c hc => huniq A B c.1 c.2 h1 h2 hc.2.1 hc.2.2⟩`.
-/
theorem existsUnique_char (m n : ℤ) (hnot : ¬ (Even m ∧ Even n)) :
    ∃! c : Fin 2 × Fin 2, IsEvenChar c.1 c.2 ∧
      Even (m + ((c.1 : ℕ) : ℤ) - 1) ∧ Even (n + ((c.2 : ℕ) : ℤ) - 1) := by
  have huniq : ∀ A B A' B' : Fin 2, Even (m + ((A : ℕ) : ℤ) - 1) → Even (n + ((B : ℕ) : ℤ) - 1) →
      Even (m + ((A' : ℕ) : ℤ) - 1) → Even (n + ((B' : ℕ) : ℤ) - 1) → (A', B') = (A, B) := by
    intro A B A' B' h1 h2 h3 h4
    rw [Int.even_iff] at h1 h2 h3 h4
    have := A.isLt
    have := B.isLt
    have := A'.isLt
    have := B'.isLt
    rw [Prod.mk.injEq, Fin.ext_iff, Fin.ext_iff]
    omega
  have hex : ∃ A B : Fin 2, IsEvenChar A B ∧ Even (m + ((A : ℕ) : ℤ) - 1) ∧
      Even (n + ((B : ℕ) : ℤ) - 1) := by
    rcases Int.even_or_odd m with hm | hm <;> rcases Int.even_or_odd n with hn | hn
    · exact absurd ⟨hm, hn⟩ hnot
    · exact ⟨1, 0, by simp [IsEvenChar], by simpa using hm, by simpa [parity_simps] using hn⟩
    · exact ⟨0, 1, by simp [IsEvenChar], by simpa [parity_simps] using hm, by simpa using hn⟩
    · exact ⟨0, 0, by simp [IsEvenChar], by simpa [parity_simps] using hm,
        by simpa [parity_simps] using hn⟩
  obtain ⟨A, B, h0, h1, h2⟩ := hex
  exact ⟨(A, B), ⟨h0, h1, h2⟩, fun c hc => huniq A B c.1 c.2 h1 h2 hc.2.1 hc.2.2⟩

/- English proof (translation)
Introduce `Λ ω₁ τ t₀ hω hτ hP h2 ht`. Set `τ' : ℍ` to `⟨τ, hτ⟩`. Establish `hτ' : (τ' : ℂ) = τ` using `rfl`. Establish `h : ∀ x, x ∈ Λ ↔ ∃ m n : ℤ, ω₁ * (m * (τ' : ℂ) + n) = x` using `fun x => by`. Rewrite using `[hP x]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨m, n, rfl⟩`. Conclude with `⟨n, m, by rw [hτ']; ring⟩`. Introduce and unpack `⟨m, n, rfl⟩`. Conclude with `⟨n, m, by rw [hτ']; ring⟩`.

Take `⟨m, n, hmn⟩` from `(h _).1 h2`. Establish `hu : t₀ / ω₁ = (m * (τ' : ℂ) + n) / 2`. Rewrite using `[div_eq_iff hω]`. Take the linear combination `(-1 / 2 : ℂ) * hmn`. Establish `hnot : ¬ (Even m ∧ Even n)`.

Introduce `hp`. Apply `ht` to reduce the goal to its premises. Establish `hm` using `(half_mem_iff hω h m n).2 (by`. Take `⟨hm, hn⟩` from `hp`. Simplify using `[parity_simps, hm, hn])`.

Rewrite `hm` using `[hmn, mul_div_cancel_left₀ _ (two_ne_zero)]`. Then use the resulting hypothesis. Rewrite using `[normSq1_eq_nrm1Sq]`. Take `⟨hpos, hinv⟩` from `meanSquare_normalizedThetaTwoTorsion hω h ht`. Use `⟨?_, hpos, ?_⟩` and prove the remaining obligations. Rewrite using `[hu]`.

Simplify using `only [show τ = (τ' : ℂ) from rfl, thetaChar_eq_zero_iff hω h]`. Conclude with `existsUnique_char m n hnot`. Introduce `A B _ hz`. Rewrite `hz` using `[hu, show τ = (τ' : ℂ) from rfl, thetaChar_eq_zero_iff hω h]`. Take `⟨⟨r, hr⟩, ⟨s, hs⟩⟩` from `hz`.

Rewrite using `[hinv]`. Use `congrArg (fun x => Real.sqrt (2 * τ.im) * x) (norm_sq_oddTheta τ' A B (r + 1 - ((A : ℕ) : ℤ)) (s + 1 - ((B : ℕ) : ℤ)) _ ?_)` and prove the remaining obligations. Establish `hm : (m : ℂ) = 2 * r + 1 - ((A : ℕ) : ℂ)`. Establish `: m = 2 * r + 1 - ((A : ℕ) : ℤ)` using `by omega`. Rewrite using `[this]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hn : (n : ℂ) = 2 * s + 1 - ((B : ℕ) : ℂ)`. Establish `: n = 2 * s + 1 - ((B : ℕ) : ℤ)` using `by omega`. Rewrite using `[this]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hu, hm, hn]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem normTheta0 : NormTheta0 := by
  intro Λ ω₁ τ t₀ hω hτ hP h2 ht
  let τ' : ℍ := ⟨τ, hτ⟩
  have hτ' : (τ' : ℂ) = τ := rfl
  have h : ∀ x, x ∈ Λ ↔ ∃ m n : ℤ, ω₁ * (m * (τ' : ℂ) + n) = x := fun x => by
    rw [hP x]
    constructor
    · rintro ⟨m, n, rfl⟩
      exact ⟨n, m, by rw [hτ']; ring⟩
    · rintro ⟨m, n, rfl⟩
      exact ⟨n, m, by rw [hτ']; ring⟩
  obtain ⟨m, n, hmn⟩ := (h _).1 h2
  have hu : t₀ / ω₁ = (m * (τ' : ℂ) + n) / 2 := by
    rw [div_eq_iff hω]
    linear_combination (-1 / 2 : ℂ) * hmn
  have hnot : ¬ (Even m ∧ Even n) := by
    intro hp
    apply ht
    have hm := (half_mem_iff hω h m n).2 (by
      obtain ⟨hm, hn⟩ := hp
      simp [parity_simps, hm, hn])
    rwa [hmn, mul_div_cancel_left₀ _ (two_ne_zero)] at hm
  rw [normSq1_eq_nrm1Sq]
  obtain ⟨hpos, hinv⟩ := meanSquare_normalizedThetaTwoTorsion hω h ht
  refine ⟨?_, hpos, ?_⟩
  · rw [hu]
    simp only [show τ = (τ' : ℂ) from rfl, thetaChar_eq_zero_iff hω h]
    exact existsUnique_char m n hnot
  · intro A B _ hz
    rw [hu, show τ = (τ' : ℂ) from rfl, thetaChar_eq_zero_iff hω h] at hz
    obtain ⟨⟨r, hr⟩, ⟨s, hs⟩⟩ := hz
    rw [hinv]
    refine congrArg (fun x => Real.sqrt (2 * τ.im) * x) (norm_sq_oddTheta τ' A B
      (r + 1 - ((A : ℕ) : ℤ)) (s + 1 - ((B : ℕ) : ℤ)) _ ?_)
    have hm : (m : ℂ) = 2 * r + 1 - ((A : ℕ) : ℂ) := by
      have : m = 2 * r + 1 - ((A : ℕ) : ℤ) := by omega
      rw [this]
      push_cast
      ring
    have hn : (n : ℂ) = 2 * s + 1 - ((B : ℕ) : ℂ) := by
      have : n = 2 * s + 1 - ((B : ℕ) : ℤ) := by omega
      rw [this]
      push_cast
      ring
    rw [hu, hm, hn]
    push_cast
    ring

end GlobalTheory.ThetaNullNormSquares
