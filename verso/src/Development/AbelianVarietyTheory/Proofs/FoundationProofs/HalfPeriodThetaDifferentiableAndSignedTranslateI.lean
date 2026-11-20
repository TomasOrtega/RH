import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealPeriodLatticeOfCurveDatum
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeCovolumePosAndSelfDual
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntegerMapEqHalfOneAddSqrt
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.HalfPeriodTheta

/- English proof (translation)
Evaluate the decidable proposition.
-/
theorem parity_mod_two : ∀ a b c d s₁ s₂ x₁ x₂ : ZMod 2,
    a * a + b * c = a → a * b + b * d = b → c * a + d * c = c → c * b + d * d = d →
    ¬ (a * s₁ + c * s₂ = 0 ∧ b * s₁ + d * s₂ = 0) →
    ¬ (s₁ - (a * s₁ + c * s₂) = 0 ∧ s₂ - (b * s₁ + d * s₂) = 0) →
    (((a * x₁ + c * x₂) * x₂ - (b * x₁ + d * x₂) * x₁) + (x₁ * s₂ - x₂ * s₁) = 0 ↔ x₁ = 0 ∧ x₂ = 0) := by
  decide

/- English proof (translation)
Establish `h : ((gl3FieldFirst Λ ω (2 * t) : ℝ) : ℂ) * Complex.I = (ω * (starRingEnd ℂ) t - t * (starRingEnd ℂ) ω) / (area Λ : ℂ)`. Establish `h2` using `Complex.sub_conj (ω * (starRingEnd ℂ) t)`. Rewrite `h2` using `[map_mul, Complex.conj_conj, mul_comm ((starRingEnd ℂ) ω) t]`. Establish `h3 : (ω * (starRingEnd ℂ) (2 * t)).im = 2 * (ω * (starRingEnd ℂ) t).im` using `by simp; ring`. Rewrite using `[h2, gl3FieldFirst, h3]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `h' : -(Real.pi : ℂ) * Complex.I * (gl3FieldFirst Λ ω (2 * t) : ℂ) = -(Real.pi : ℂ) * ((ω * (starRingEnd ℂ) t - t * (starRingEnd ℂ) ω) / (area Λ : ℂ))`. Rewrite using `[← h]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[h']`. Simplify using `only [U1]`. Rewrite using `[add_right_comm z t ω, mul_assoc (G _), mul_assoc (G _), ← Complex.exp_add, ← Complex.exp_add, mul_left_comm _ (G _), ← Complex.exp_add]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_orthonormal_basis_family (Λ : AddSubgroup ℂ) (ω t : ℂ) (G : ℂ → ℂ) (z : ℂ) :
    U1 Λ ω (U1 Λ t G) z =
      Complex.exp (-(Real.pi : ℂ) * Complex.I * (gl3FieldFirst Λ ω (2 * t) : ℂ)) * U1 Λ t (U1 Λ ω G) z := by
  have h : ((gl3FieldFirst Λ ω (2 * t) : ℝ) : ℂ) * Complex.I =
      (ω * (starRingEnd ℂ) t - t * (starRingEnd ℂ) ω) / (area Λ : ℂ) := by
    have h2 := Complex.sub_conj (ω * (starRingEnd ℂ) t)
    rw [map_mul, Complex.conj_conj, mul_comm ((starRingEnd ℂ) ω) t] at h2
    have h3 : (ω * (starRingEnd ℂ) (2 * t)).im = 2 * (ω * (starRingEnd ℂ) t).im := by
      simp; ring
    rw [h2, gl3FieldFirst, h3]
    push_cast
    ring
  have h' : -(Real.pi : ℂ) * Complex.I * (gl3FieldFirst Λ ω (2 * t) : ℂ) =
      -(Real.pi : ℂ) * ((ω * (starRingEnd ℂ) t - t * (starRingEnd ℂ) ω) / (area Λ : ℂ)) := by
    rw [← h]; ring
  rw [h']
  simp only [U1]
  rw [add_right_comm z t ω, mul_assoc (G _), mul_assoc (G _), ← Complex.exp_add, ← Complex.exp_add,
    mul_left_comm _ (G _), ← Complex.exp_add]
  congr 2
  ring

/- English proof (translation)
Establish `mem : ∀ z, z ∈ Λ ↔ ∃ x y : ℤ, z = x * w₁ + y * w₂`. Introduce `z`. Rewrite using `[hΛ, AddSubgroup.mem_closure_pair]`. Simplify using `only [zsmul_eq_mul, eq_comm]`. Establish `uniq : ∀ x y : ℤ, (x : ℂ) * w₁ + y * w₂ = 0 → x = 0 ∧ y = 0`.

Introduce `x y h`. Use `LinearIndependent.pair_iff.1 hi (x : ℝ) (y : ℝ) (by simpa using h)` as an intermediate fact. Conclude with `this` after adjusting the coercions. Establish `half : ∀ x y : ℤ, ((x : ℂ) * w₁ + y * w₂) / 2 ∈ Λ ↔ (x : ZMod 2) = 0 ∧ (y : ZMod 2) = 0`. Introduce `x y`.

Rewrite using `[mem, ZMod.intCast_eq_zero_iff_even, ZMod.intCast_eq_zero_iff_even]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u, v, h⟩`. Take `⟨e1, e2⟩` from `uniq (x - 2 * u) (y - 2 * v) (by push_cast; linear_combination 2 * h)`. Conclude with `⟨⟨u, by omega⟩, ⟨v, by omega⟩⟩`.

Introduce and unpack `⟨⟨u, rfl⟩, ⟨v, rfl⟩⟩`. Conclude with `⟨u, v, by push_cast; ring⟩`. Establish `hw₁ : w₁ ∈ Λ` using `(mem _).2 ⟨1, 0, by simp⟩`. Establish `hw₂ : w₂ ∈ Λ` using `(mem _).2 ⟨0, 1, by simp⟩`. Take `⟨e, he⟩` from `(hsd w₁).1 hw₁ w₂ hw₂`.

Establish `EFr : ∀ x y u v : ℝ, gl3FieldFirst Λ (x * w₁ + y * w₂) (u * w₁ + v * w₂) = (x * v - y * u) * e`. Introduce `x y u v`. Rewrite using `[← he]`. Simplify using `only [gl3FieldFirst]`. Simplify using the standard rewrite rules.

Expand and normalize the polynomial expressions, which then agree. Establish `EFi : ∀ x y u v : ℤ, gl3FieldFirst Λ (x * w₁ + y * w₂) (u * w₁ + v * w₂) = (((x * v - y * u) * e : ℤ) : ℝ)`. Introduce `x y u v`. Use `EFr x y u v` as an intermediate fact. Move the coercions through the operations in `at this ⊢`.

Conclude with `this`. Establish `hodd : (e : ZMod 2) = 1`. Rewrite using `[ZMod.intCast_eq_one_iff_odd, ← Int.not_even_iff_odd]`. Introduce and unpack `⟨k, hk⟩`. Establish `: (((1 : ℤ) : ℂ) * w₁ + ((0 : ℤ) : ℂ) * w₂) / 2 ∈ Λ`.

Rewrite using `[hsd]`. Introduce `w hw`. Take `⟨u, v, rfl⟩` from `(mem _).1 hw`. Use `⟨v * k, ?_⟩` and prove the remaining obligations. Use `EFr (1 / 2) 0 u v` as an intermediate fact.

Rewrite `this` using `[hk]`. Move the coercions through the operations in `at this ⊢`. Rewrite using `[show (1 * w₁ + 0 * w₂) / 2 = 1 / 2 * w₁ + 0 * w₂ by ring, this]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `this` using `[half]`.

Conclude with `absurd this.1 (by decide)`. Take `⟨a, b, hab⟩` from `(mem _).1 (hst _ hw₁)`. Take `⟨c, d, hcd⟩` from `(mem _).1 (hst _ hw₂)`. Take `⟨s₁, s₂, hs⟩` from `(mem _).1 ht`. Take `⟨x₁, x₂, rfl⟩` from `(mem _).1 hω`.

Establish `mul : ∀ x y : ℤ, θ * ((x : ℂ) * w₁ + y * w₂) = ((a * x + c * y : ℤ) : ℂ) * w₁ + ((b * x + d * y : ℤ) : ℂ) * w₂`. Introduce `x y`. Use `push_cast`. Take the linear combination `(x : ℂ) * hab + (y : ℂ) * hcd`. Take `⟨r1, r2⟩` from `uniq (a * a + b * c - a + N) (a * b + b * d - b) (by`.

Use `push_cast`. Take the linear combination `w₁ * hθ - (θ + a - 1) * hab - (b : ℂ) * hcd)`. Take `⟨r3, r4⟩` from `uniq (c * a + d * c - c) (c * b + d * d - d + N) (by`. Use `push_cast`. Take the linear combination `w₂ * hθ - (θ + d - 1) * hcd - (c : ℂ) * hab)`.

Establish `hN2 : (N : ZMod 2) = 0` using `ZMod.intCast_eq_zero_iff_even.2 hN`. Establish `q1` using `congrArg (Int.cast : ℤ → ZMod 2) r1`. Establish `q2` using `congrArg (Int.cast : ℤ → ZMod 2) r2`. Establish `q3` using `congrArg (Int.cast : ℤ → ZMod 2) r3`. Establish `q4` using `congrArg (Int.cast : ℤ → ZMod 2) r4`.

Move the coercions through the operations in `at q1 q2 q3 q4`. Establish `e1 : θ * t = (((a * s₁ + c * s₂ : ℤ) : ℂ) * w₁ + ((b * s₁ + d * s₂ : ℤ) : ℂ) * w₂) / 2`. Rewrite using `[← mul, ← hs]`. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : (1 - θ) * t = (((s₁ - (a * s₁ + c * s₂) : ℤ) : ℂ) * w₁ + ((s₂ - (b * s₁ + d * s₂) : ℤ) : ℂ) * w₂) / 2`.

Move the coercions through the operations in `at e1 ⊢`. Take the linear combination `(1 / 2) * hs - e1`. Rewrite `h1` using `[e1, half]`. Rewrite `h2` using `[e2, half]`. Move the coercions through the operations in `at h1 h2`.

Use `⟨_, _, by rw [mul, EFi], by rw [hs, EFi], ?_⟩` and prove the remaining obligations. Rewrite using `[half, ← ZMod.intCast_eq_zero_iff_even]`. Use `push_cast`. Rewrite using `[hodd, mul_one, mul_one]`. Conclude with `parity_mod_two _ _ _ _ _ _ _ _ (by linear_combination q1 - hN2) (by linear_combination q2) (by linear_combination q3) (by linear_combination q4 - hN2) h1 h2`.
-/
theorem even_im_hermitian_sub (Λ : AddSubgroup ℂ) (w₁ w₂ : ℂ) (hi : LinearIndependent ℝ ![w₁, w₂])
    (hΛ : Λ = AddSubgroup.closure {w₁, w₂})
    (hsd : ∀ z : ℂ, z ∈ Λ ↔ ∀ w ∈ Λ, ∃ m : ℤ, gl3FieldFirst Λ z w = m)
    (θ : ℂ) (N : ℤ) (hN : Even N) (hθ : θ * θ = θ - N) (hst : ∀ w ∈ Λ, θ * w ∈ Λ)
    (t : ℂ) (ht : 2 * t ∈ Λ) (h1 : θ * t ∉ Λ) (h2 : (1 - θ) * t ∉ Λ) (ω : ℂ) (hω : ω ∈ Λ) :
    ∃ m n : ℤ, gl3FieldFirst Λ (θ * ω) ω = m ∧ gl3FieldFirst Λ ω (2 * t) = n ∧ (Even (m + n) ↔ ω / 2 ∈ Λ) := by
  have mem : ∀ z, z ∈ Λ ↔ ∃ x y : ℤ, z = x * w₁ + y * w₂ := by
    intro z
    rw [hΛ, AddSubgroup.mem_closure_pair]
    simp only [zsmul_eq_mul, eq_comm]
  have uniq : ∀ x y : ℤ, (x : ℂ) * w₁ + y * w₂ = 0 → x = 0 ∧ y = 0 := by
    intro x y h
    have := LinearIndependent.pair_iff.1 hi (x : ℝ) (y : ℝ) (by simpa using h)
    exact_mod_cast this
  have half : ∀ x y : ℤ, ((x : ℂ) * w₁ + y * w₂) / 2 ∈ Λ ↔ (x : ZMod 2) = 0 ∧ (y : ZMod 2) = 0 := by
    intro x y
    rw [mem, ZMod.intCast_eq_zero_iff_even, ZMod.intCast_eq_zero_iff_even]
    constructor
    · rintro ⟨u, v, h⟩
      obtain ⟨e1, e2⟩ := uniq (x - 2 * u) (y - 2 * v) (by push_cast; linear_combination 2 * h)
      exact ⟨⟨u, by omega⟩, ⟨v, by omega⟩⟩
    · rintro ⟨⟨u, rfl⟩, ⟨v, rfl⟩⟩
      exact ⟨u, v, by push_cast; ring⟩
  have hw₁ : w₁ ∈ Λ := (mem _).2 ⟨1, 0, by simp⟩
  have hw₂ : w₂ ∈ Λ := (mem _).2 ⟨0, 1, by simp⟩
  obtain ⟨e, he⟩ := (hsd w₁).1 hw₁ w₂ hw₂
  have EFr : ∀ x y u v : ℝ, gl3FieldFirst Λ (x * w₁ + y * w₂) (u * w₁ + v * w₂) = (x * v - y * u) * e := by
    intro x y u v
    rw [← he]
    simp only [gl3FieldFirst]
    simp
    ring
  have EFi : ∀ x y u v : ℤ, gl3FieldFirst Λ (x * w₁ + y * w₂) (u * w₁ + v * w₂) = (((x * v - y * u) * e : ℤ) : ℝ) := by
    intro x y u v
    have := EFr x y u v
    push_cast at this ⊢
    exact this
  have hodd : (e : ZMod 2) = 1 := by
    rw [ZMod.intCast_eq_one_iff_odd, ← Int.not_even_iff_odd]
    rintro ⟨k, hk⟩
    have : (((1 : ℤ) : ℂ) * w₁ + ((0 : ℤ) : ℂ) * w₂) / 2 ∈ Λ := by
      rw [hsd]
      intro w hw
      obtain ⟨u, v, rfl⟩ := (mem _).1 hw
      refine ⟨v * k, ?_⟩
      have := EFr (1 / 2) 0 u v
      rw [hk] at this
      push_cast at this ⊢
      rw [show (1 * w₁ + 0 * w₂) / 2 = 1 / 2 * w₁ + 0 * w₂ by ring, this]
      ring
    rw [half] at this
    exact absurd this.1 (by decide)
  obtain ⟨a, b, hab⟩ := (mem _).1 (hst _ hw₁)
  obtain ⟨c, d, hcd⟩ := (mem _).1 (hst _ hw₂)
  obtain ⟨s₁, s₂, hs⟩ := (mem _).1 ht
  obtain ⟨x₁, x₂, rfl⟩ := (mem _).1 hω
  have mul : ∀ x y : ℤ, θ * ((x : ℂ) * w₁ + y * w₂) =
      ((a * x + c * y : ℤ) : ℂ) * w₁ + ((b * x + d * y : ℤ) : ℂ) * w₂ := by
    intro x y
    push_cast
    linear_combination (x : ℂ) * hab + (y : ℂ) * hcd
  obtain ⟨r1, r2⟩ := uniq (a * a + b * c - a + N) (a * b + b * d - b) (by
    push_cast
    linear_combination w₁ * hθ - (θ + a - 1) * hab - (b : ℂ) * hcd)
  obtain ⟨r3, r4⟩ := uniq (c * a + d * c - c) (c * b + d * d - d + N) (by
    push_cast
    linear_combination w₂ * hθ - (θ + d - 1) * hcd - (c : ℂ) * hab)
  have hN2 : (N : ZMod 2) = 0 := ZMod.intCast_eq_zero_iff_even.2 hN
  have q1 := congrArg (Int.cast : ℤ → ZMod 2) r1
  have q2 := congrArg (Int.cast : ℤ → ZMod 2) r2
  have q3 := congrArg (Int.cast : ℤ → ZMod 2) r3
  have q4 := congrArg (Int.cast : ℤ → ZMod 2) r4
  push_cast at q1 q2 q3 q4
  have e1 : θ * t = (((a * s₁ + c * s₂ : ℤ) : ℂ) * w₁ + ((b * s₁ + d * s₂ : ℤ) : ℂ) * w₂) / 2 := by
    rw [← mul, ← hs]; ring
  have e2 : (1 - θ) * t = (((s₁ - (a * s₁ + c * s₂) : ℤ) : ℂ) * w₁ + ((s₂ - (b * s₁ + d * s₂) : ℤ) : ℂ) * w₂) / 2 := by
    push_cast at e1 ⊢
    linear_combination (1 / 2) * hs - e1
  rw [e1, half] at h1
  rw [e2, half] at h2
  push_cast at h1 h2
  refine ⟨_, _, by rw [mul, EFi], by rw [hs, EFi], ?_⟩
  rw [half, ← ZMod.intCast_eq_zero_iff_even]
  push_cast
  rw [hodd, mul_one, mul_one]
  exact parity_mod_two _ _ _ _ _ _ _ _ (by linear_combination q1 - hN2) (by linear_combination q2)
    (by linear_combination q3) (by linear_combination q4 - hN2) h1 h2

/- English proof (translation)
Introduce `D hG cc δ hC t0 ht`. Take `⟨hb, -, -, -, hst⟩` from `GlobalTheory.CurveLattice.lattice_of_curve D hG cc δ hC`. Use `set Λ := lamOf D cc δ`. Take `⟨⟨hdiff, -, -, hlaw⟩, -⟩` from `GlobalTheory.OddTheta.sgStar_laws Λ hb`. Take `⟨L, hL⟩` from `GlobalTheory.OddTheta.exists_periodPair Λ hb`.

Take `⟨-, hsd⟩` from `GlobalTheory.PlaneLattice.area_pos_and_selfDual L Λ hL`. Take `⟨w₁, w₂, hi, hΛ⟩` from `hb`. Take `⟨a, ha⟩` from `GlobalTheory.NormSum.exists_integer_map_eq_w0 D`. Establish `hd : D.host.d % 16 = 7` using `D.host.hyp.2.2.2.1`. Take `⟨k, hk⟩ : ∃ k : ℕ, D.host.d = 16 * k + 7` from `⟨D.host.d / 16, by omega⟩`.

Establish `hsq : ((Real.sqrt D.host.d : ℝ) : ℂ) * (Real.sqrt D.host.d : ℝ) = 16 * (k : ℂ) + 7`. Rewrite using `[← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _), hk]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `⟨?_, fun ω hω => ?_⟩` and prove the remaining obligations.

Unfold `GL3Theta.th0 U1`. Use `Differentiable.div_const (Differentiable.mul (hdiff.comp (differentiable_id.add_const _)) ?_) _` and prove the remaining obligations. Use `fun_prop`. Take `⟨m, n, hm, hn, hpar⟩` from `even_im_hermitian_sub Λ w₁ w₂ hi hΛ hsd (w0 D) (4 * k + 2) ⟨2 * k + 1, by ring⟩ (by`. Unfold `w0`.

Use `push_cast`. Take the linear combination `(((Real.sqrt D.host.d : ℝ) : ℂ) ^ 2 / 4) * Complex.I_mul_I - (1 / 4) * hsq)`. Use the proof step `(fun w hw => ha ▸ hst a w hw) t0 ht.1 ht.2.1`. Use the proof step `(by`. Use `ht.2.2` as an intermediate fact.

Use `this using 3` and compare the differences between its conclusion and the goal. Unfold `w0`. Use the proof step `ring) ω hω`. Use `⟨m, ?_, fun z => ?_⟩` and prove the remaining obligations. Rewrite using `[← hm, q1, gl3FieldFirst, mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq, w0]`.

Rewrite using `[mul_comm ((1 + _) / 2 : ℂ), Complex.im_ofReal_mul]`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Establish `e1 : U1 Λ ω (GL3Theta.th0 Λ t0) z = U1 Λ ω (U1 Λ t0 (sgStar Λ)) z / U1 Λ t0 (sgStar Λ) 0` using `by conv_lhs => rw [U1] conv_rhs => rw [U1]`. Simplify using `only [GL3Theta.th0]`.

Expand and normalize the polynomial expressions, which then agree. Establish `e2 : U1 Λ t0 (U1 Λ ω (sgStar Λ)) z = (if ω / 2 ∈ Λ then 1 else -1) * U1 Λ t0 (sgStar Λ) z` using `by conv_lhs => rw [U1]`. Rewrite using `[hlaw ω hω, mul_assoc]`. Both sides reduce to the same expression. Establish `e3 : Complex.exp (-(Real.pi : ℂ) * Complex.I * ((n : ℝ) : ℂ)) = (-1) ^ n`.

Rewrite using `[show -(Real.pi : ℂ) * Complex.I * ((n : ℝ) : ℂ) = (n : ℂ) * (-(Real.pi * Complex.I)) by push_cast; ring, Complex.exp_int_mul, Complex.exp_neg, Complex.exp_pi_mul_I]`. Evaluate the numerical expressions. Establish `e4 : (-1 : ℂ) ^ m * (-1) ^ n * (if ω / 2 ∈ Λ then 1 else -1) = 1`. Rewrite using `[← zpow_add₀ (by norm_num)]`. Use `split_ifs with h`.

Rewrite using `[(hpar.2 h).neg_one_zpow]`. Simplify using the standard rewrite rules. Rewrite using `[(Int.not_even_iff_odd.1 (mt hpar.1 h)).neg_one_zpow]`. Simplify using the standard rewrite rules. Rewrite using `[e1, exists_orthonormal_basis_family, hn, e2, e3]`.

Simplify using `only [GL3Theta.th0]`. Take the linear combination `(U1 Λ t0 (sgStar Λ) z / U1 Λ t0 (sgStar Λ) 0) * e4`.
-/
theorem theta_signed_translation : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ t0, GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → Differentiable ℂ (GL3Theta.th0 (lamOf D cc δ) t0) ∧ ∀ ω ∈ lamOf D cc δ, ∃ m : ℤ, q1 D (lamOf D cc δ) ω = (m : ℝ) ∧ ∀ z, (-1 : ℂ) ^ m * U1 (lamOf D cc δ) ω (GL3Theta.th0 (lamOf D cc δ) t0) z = GL3Theta.th0 (lamOf D cc δ) t0 z := by
  intro D hG cc δ hC t0 ht
  obtain ⟨hb, -, -, -, hst⟩ := GlobalTheory.CurveLattice.lattice_of_curve D hG cc δ hC
  set Λ := lamOf D cc δ
  obtain ⟨⟨hdiff, -, -, hlaw⟩, -⟩ := GlobalTheory.OddTheta.sgStar_laws Λ hb
  obtain ⟨L, hL⟩ := GlobalTheory.OddTheta.exists_periodPair Λ hb
  obtain ⟨-, hsd⟩ := GlobalTheory.PlaneLattice.area_pos_and_selfDual L Λ hL
  obtain ⟨w₁, w₂, hi, hΛ⟩ := hb
  obtain ⟨a, ha⟩ := GlobalTheory.NormSum.exists_integer_map_eq_w0 D
  have hd : D.host.d % 16 = 7 := D.host.hyp.2.2.2.1
  obtain ⟨k, hk⟩ : ∃ k : ℕ, D.host.d = 16 * k + 7 := ⟨D.host.d / 16, by omega⟩
  have hsq : ((Real.sqrt D.host.d : ℝ) : ℂ) * (Real.sqrt D.host.d : ℝ) = 16 * (k : ℂ) + 7 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _), hk]
    push_cast; ring
  refine ⟨?_, fun ω hω => ?_⟩
  · unfold GL3Theta.th0 U1
    refine Differentiable.div_const (Differentiable.mul (hdiff.comp (differentiable_id.add_const _)) ?_) _
    fun_prop
  obtain ⟨m, n, hm, hn, hpar⟩ := even_im_hermitian_sub Λ w₁ w₂ hi hΛ hsd (w0 D) (4 * k + 2) ⟨2 * k + 1, by ring⟩
    (by
      unfold w0
      push_cast
      linear_combination (((Real.sqrt D.host.d : ℝ) : ℂ) ^ 2 / 4) * Complex.I_mul_I - (1 / 4) * hsq)
    (fun w hw => ha ▸ hst a w hw) t0 ht.1 ht.2.1
    (by
      have := ht.2.2
      convert this using 3
      unfold w0; ring) ω hω
  refine ⟨m, ?_, fun z => ?_⟩
  · rw [← hm, q1, gl3FieldFirst, mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq, w0]
    rw [mul_comm ((1 + _) / 2 : ℂ), Complex.im_ofReal_mul]
    simp
    ring
  · have e1 : U1 Λ ω (GL3Theta.th0 Λ t0) z = U1 Λ ω (U1 Λ t0 (sgStar Λ)) z / U1 Λ t0 (sgStar Λ) 0 := by
      conv_lhs => rw [U1]
      conv_rhs => rw [U1]
      simp only [GL3Theta.th0]
      ring
    have e2 : U1 Λ t0 (U1 Λ ω (sgStar Λ)) z = (if ω / 2 ∈ Λ then 1 else -1) * U1 Λ t0 (sgStar Λ) z := by
      conv_lhs => rw [U1]
      rw [hlaw ω hω, mul_assoc]
      rfl
    have e3 : Complex.exp (-(Real.pi : ℂ) * Complex.I * ((n : ℝ) : ℂ)) = (-1) ^ n := by
      rw [show -(Real.pi : ℂ) * Complex.I * ((n : ℝ) : ℂ) = (n : ℂ) * (-(Real.pi * Complex.I)) by push_cast; ring,
        Complex.exp_int_mul, Complex.exp_neg, Complex.exp_pi_mul_I]
      norm_num
    have e4 : (-1 : ℂ) ^ m * (-1) ^ n * (if ω / 2 ∈ Λ then 1 else -1) = 1 := by
      rw [← zpow_add₀ (by norm_num)]
      split_ifs with h
      · rw [(hpar.2 h).neg_one_zpow]; simp
      · rw [(Int.not_even_iff_odd.1 (mt hpar.1 h)).neg_one_zpow]; simp
    rw [e1, exists_orthonormal_basis_family, hn, e2, e3]
    simp only [GL3Theta.th0]
    linear_combination (U1 Λ t0 (sgStar Λ) z / U1 Λ t0 (sgStar Λ) 0) * e4

end GlobalTheory.HalfPeriodTheta
