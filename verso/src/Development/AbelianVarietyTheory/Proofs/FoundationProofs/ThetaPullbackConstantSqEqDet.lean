import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsAddHaarMeasurePi
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslationIntertwinerUnitary
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AdmissibleCharactersExist
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpaceSelfDualPairAtMostLine
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntegerMapEqHalfOneAddSqrt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoordsAlongOrthonormalRealSubfieldBasis
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrthoProductThetaMemThetaSpaceOfLattice
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeanSquareOrthoProductThetaEqProd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeisenbergReproducingKernelSumSpec
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PhDetMulIntegral
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralHeisKerSumDiag

section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.UnitaryTheta.HalfPeriod

/- English proof (translation)
Take `⟨L, hL⟩` from `GlobalTheory.CurveLattice.exists_periodPair_lamOf D cc δ hC`. Use `⟨L.ω₁, L.ω₂, L.indep, AddSubgroup.ext fun z => ?_⟩` and prove the remaining obligations. Rewrite using `[hL, PeriodPair.lattice, ← Submodule.span_int_eq_addSubgroupClosure, Submodule.mem_toAddSubgroup]`.
-/
theorem exists_basis_lamOf (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (hC : Crv D cc δ) :
    ∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ lamOf D cc δ = AddSubgroup.closure {w₁, w₂} := by
  obtain ⟨L, hL⟩ := GlobalTheory.CurveLattice.exists_periodPair_lamOf D cc δ hC
  refine ⟨L.ω₁, L.ω₂, L.indep, AddSubgroup.ext fun z => ?_⟩
  rw [hL, PeriodPair.lattice, ← Submodule.span_int_eq_addSubgroupClosure, Submodule.mem_toAddSubgroup]

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
Introduce `D cc δ hC t0 ht`. Establish `hb` using `exists_basis_lamOf D cc δ hC`. Establish `hst` using `fun a w hw => GlobalTheory.ThetaInter.lam_mul_mem (D := D) (cc := cc) (δ := δ) a (w := w) hw`. Use `set Λ := lamOf D cc δ`. Take `⟨⟨hdiff, -, -, hlaw⟩, -⟩` from `GlobalTheory.OddTheta.sgStar_laws Λ hb`.

Take `⟨L, hL⟩` from `GlobalTheory.OddTheta.exists_periodPair Λ hb`. Take `⟨-, hsd⟩` from `GlobalTheory.PlaneLattice.area_pos_and_selfDual L Λ hL`. Take `⟨w₁, w₂, hi, hΛ⟩` from `hb`. Take `⟨a, ha⟩` from `GlobalTheory.NormSum.exists_integer_map_eq_w0 D`. Establish `hd : D.host.d % 16 = 7` using `D.host.hyp.2.2.2.1`.

Take `⟨k, hk⟩ : ∃ k : ℕ, D.host.d = 16 * k + 7` from `⟨D.host.d / 16, by omega⟩`. Establish `hsq : ((Real.sqrt D.host.d : ℝ) : ℂ) * (Real.sqrt D.host.d : ℝ) = 16 * (k : ℂ) + 7`. Rewrite using `[← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _), hk]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Use `⟨?_, fun ω hω => ?_⟩` and prove the remaining obligations. Unfold `GL3Theta.th0 U1`. Use `Differentiable.div_const (Differentiable.mul (hdiff.comp (differentiable_id.add_const _)) ?_) _` and prove the remaining obligations. Use `fun_prop`. Take `⟨m, n, hm, hn, hpar⟩` from `even_im_hermitian_sub Λ w₁ w₂ hi hΛ hsd (w0 D) (4 * k + 2) ⟨2 * k + 1, by ring⟩ (by`.

Unfold `w0`. Use `push_cast`. Take the linear combination `(((Real.sqrt D.host.d : ℝ) : ℂ) ^ 2 / 4) * Complex.I_mul_I - (1 / 4) * hsq)`. Use the proof step `(fun w hw => ha ▸ hst a w hw) t0 ht.1 ht.2.1`. Use the proof step `(by`.

Use `ht.2.2` as an intermediate fact. Use `this using 3` and compare the differences between its conclusion and the goal. Unfold `w0`. Use the proof step `ring) ω hω`. Use `⟨m, ?_, fun z => ?_⟩` and prove the remaining obligations.

Rewrite using `[← hm, q1, gl3FieldFirst, mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq, w0]`. Rewrite using `[mul_comm ((1 + _) / 2 : ℂ), Complex.im_ofReal_mul]`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Establish `e1 : U1 Λ ω (GL3Theta.th0 Λ t0) z = U1 Λ ω (U1 Λ t0 (sgStar Λ)) z / U1 Λ t0 (sgStar Λ) 0` using `by conv_lhs => rw [U1] conv_rhs => rw [U1]`.

Simplify using `only [GL3Theta.th0]`. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : U1 Λ t0 (U1 Λ ω (sgStar Λ)) z = (if ω / 2 ∈ Λ then 1 else -1) * U1 Λ t0 (sgStar Λ) z` using `by conv_lhs => rw [U1]`. Rewrite using `[hlaw ω hω, mul_assoc]`. Both sides reduce to the same expression.

Establish `e3 : Complex.exp (-(Real.pi : ℂ) * Complex.I * ((n : ℝ) : ℂ)) = (-1) ^ n`. Rewrite using `[show -(Real.pi : ℂ) * Complex.I * ((n : ℝ) : ℂ) = (n : ℂ) * (-(Real.pi * Complex.I)) by push_cast; ring, Complex.exp_int_mul, Complex.exp_neg, Complex.exp_pi_mul_I]`. Evaluate the numerical expressions. Establish `e4 : (-1 : ℂ) ^ m * (-1) ^ n * (if ω / 2 ∈ Λ then 1 else -1) = 1`. Rewrite using `[← zpow_add₀ (by norm_num)]`.

Use `split_ifs with h`. Rewrite using `[(hpar.2 h).neg_one_zpow]`. Simplify using the standard rewrite rules. Rewrite using `[(Int.not_even_iff_odd.1 (mt hpar.1 h)).neg_one_zpow]`. Simplify using the standard rewrite rules.

Rewrite using `[e1, exists_orthonormal_basis_family, hn, e2, e3]`. Simplify using `only [GL3Theta.th0]`. Take the linear combination `(U1 Λ t0 (sgStar Λ) z / U1 Λ t0 (sgStar Λ) 0) * e4`.
-/
theorem theta_signed_translation : ∀ (D : D7), ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ t0, GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → Differentiable ℂ (GL3Theta.th0 (lamOf D cc δ) t0) ∧ ∀ ω ∈ lamOf D cc δ, ∃ m : ℤ, q1 D (lamOf D cc δ) ω = (m : ℝ) ∧ ∀ z, (-1 : ℂ) ^ m * U1 (lamOf D cc δ) ω (GL3Theta.th0 (lamOf D cc δ) t0) z = GL3Theta.th0 (lamOf D cc δ) t0 z := by
  intro D cc δ hC t0 ht
  have hb := exists_basis_lamOf D cc δ hC
  have hst := fun a w hw => GlobalTheory.ThetaInter.lam_mul_mem (D := D) (cc := cc) (δ := δ) a (w := w) hw
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

end GlobalTheory.UnitaryTheta.HalfPeriod

end

noncomputable section
namespace GlobalTheory.UnitaryTheta

section Core
open Complex MeasureTheory GlobalTheory.Phase
open scoped BigOperators ComplexConjugate Real Classical

/- English proof (translation)
Use `⟨h1, h2, fun x hx y hy => ?_⟩` and prove the remaining obligations. Take `⟨z, hz⟩` from `Function.ne_iff.1 hθ`. Establish `e1` using `hfix (x + y) (Λ.add_mem hx hy) z`. Establish `e2` using `hfix x hx z`. Establish `e3` using `hfix y hy (z + x)`.

Simplify using `only [Heisenberg₂] at e1 e2 e3`. Rewrite `e2` using `[← e3]`. Establish `hne : θ (z + (x + y)) * cexp (-(π : ℂ) * H z (x + y) - (π : ℂ) * H (x + y) (x + y) / 2) ≠ 0`. Introduce `h`. Rewrite `e1` using `[h, mul_zero]`.

Conclude with `hz e1.symm`. Apply `mul_right_cancel₀ hne` to reduce the goal to its premises. Rewrite using `[e1, ← e2, add_assoc]`. Establish `hi : ((H x y).im : ℂ) * I = (H x y - H y x) / 2`. Rewrite using `[hH.1 y x, Complex.sub_conj]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `: cexp (-(π : ℂ) * H (z + x) y - (π : ℂ) * H y y / 2) * cexp (-(π : ℂ) * H z x - (π : ℂ) * H x x / 2) = cexp (-((π : ℂ) * I) * ((H x y).im : ℂ)) * cexp (-(π : ℂ) * H z (x + y) - (π : ℂ) * H (x + y) (x + y) / 2)`. Rewrite using `[← Complex.exp_add, ← Complex.exp_add]`. Use `congr 1`.

Simplify using `only [map_add, LinearMap.add_apply]`. Take the linear combination `(π : ℂ) * hi`. Take the linear combination `α x * α y * θ (z + (x + y)) * this`.
-/
theorem isSemichar_of_fixed {V : Type} [AddCommGroup V] [Module ℂ V] (H : Sesq V) (hH : IsPosHerm H)
    (Λ : AddSubgroup V) (α : V → ℂ) (h1 : ∀ x ∈ Λ, α x = 1 ∨ α x = -1)
    (h2 : ∀ x ∈ Λ, ∀ y ∈ Λ, ∃ m : ℤ, (H x y).im = m) (θ : V → ℂ) (hθ : θ ≠ 0)
    (hfix : ∀ x ∈ Λ, ∀ z, α x * Heisenberg₂ H x θ z = θ z) : IsSemichar H Λ α := by
  refine ⟨h1, h2, fun x hx y hy => ?_⟩
  obtain ⟨z, hz⟩ := Function.ne_iff.1 hθ
  have e1 := hfix (x + y) (Λ.add_mem hx hy) z
  have e2 := hfix x hx z
  have e3 := hfix y hy (z + x)
  simp only [Heisenberg₂] at e1 e2 e3
  rw [← e3] at e2
  have hne : θ (z + (x + y)) * cexp (-(π : ℂ) * H z (x + y) - (π : ℂ) * H (x + y) (x + y) / 2) ≠ 0 := by
    intro h
    rw [h, mul_zero] at e1
    exact hz e1.symm
  apply mul_right_cancel₀ hne
  rw [e1, ← e2, add_assoc]
  have hi : ((H x y).im : ℂ) * I = (H x y - H y x) / 2 := by
    rw [hH.1 y x, Complex.sub_conj]; push_cast; ring
  have : cexp (-(π : ℂ) * H (z + x) y - (π : ℂ) * H y y / 2) * cexp (-(π : ℂ) * H z x - (π : ℂ) * H x x / 2) =
      cexp (-((π : ℂ) * I) * ((H x y).im : ℂ)) *
        cexp (-(π : ℂ) * H z (x + y) - (π : ℂ) * H (x + y) (x + y) / 2) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    simp only [map_add, LinearMap.add_apply]
    linear_combination (π : ℂ) * hi
  linear_combination α x * α y * θ (z + (x + y)) * this

/- English proof (translation)
Take `⟨m, hm, h⟩` from `h`. Use `⟨m, hm, ?_⟩` and prove the remaining obligations. Rewrite `h` using `[norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.le, ofReal_mul, mul_pow, mul_pow]`. Conclude with `mul_right_cancel₀ (pow_ne_zero m (ofReal_ne_zero.2 ht.ne')) h`.
-/
theorem ph_of_mul_pos {c : ℂ} {t : ℝ} (ht : 0 < t) (h : Ph (c * t)) : Ph c := by
  obtain ⟨m, hm, h⟩ := h
  refine ⟨m, hm, ?_⟩
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.le, ofReal_mul, mul_pow, mul_pow] at h
  exact mul_right_cancel₀ (pow_ne_zero m (ofReal_ne_zero.2 ht.ne')) h

/- English proof (translation)
Establish `hL` using `Graph.ph_det_mul_integral V μ H hH a ha hdet Λ Λ' hfg hle hfi haΛ α hα hαa Fd hFd`. Take `⟨-, hd, hf⟩` from `KerSum.kerSum_spec V H hH Λ α hα`. Establish `hR` using `fun q => integral_heis_kerSum_diag V μ H hH Λ Λ' hle α hα Fd hFd hfin (r q) (hr q)`. Establish `key : ∀ z, kerSum H Λ α z (a z) * cexp (-(π : ℂ) * H z z) = c * ∑ q, α (r q) * (Heisenberg₂ H (r q) (kerSum H Λ α z) z * cexp (-(π : ℂ) * H z z))`. Introduce `z`.

Take `⟨b, hb⟩` from `hline _ (hd z) (hf z)`. Rewrite using `[hb, Pi.smul_apply, hc z, smul_eq_mul, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Simplify using `only [Heisenberg₂, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hr0 : r q₀ ∈ Λ` using `(hq q₀).2 rfl`. Establish `hα0 : α (r q₀) * α (-r q₀) = 1`. Establish `e` using `hα.2.2 _ hr0 _ (Λ.neg_mem hr0)`. Establish `e0` using `hα.2.2 0 Λ.zero_mem 0 Λ.zero_mem`. Establish `him : (H (r q₀) (r q₀)).im = 0`.

Use `congrArg Complex.im (hH.1 (r q₀) (r q₀))` as an intermediate fact. Simplify using `only [conj_im] at this`. Combine the linear equalities and inequalities to obtain the conclusion. Simplify using `only [add_neg_cancel, map_neg, neg_im, him, neg_zero, ofReal_zero, mul_zero, Complex.exp_zero, mul_one] at e`. Simplify using `only [add_zero, map_zero, zero_im, ofReal_zero, mul_zero, Complex.exp_zero, mul_one] at e0`.

Break down `hα.1 0 Λ.zero_mem with h | h` into its components or cases. Rewrite using `[← e, h]`. Rewrite `e0` using `[h]`. Evaluate the numerical expressions using `at e0`. Simplify using `only [key] at hL`.

Rewrite `hL` using `[integral_const_mul, integral_finsetSum _ (fun q _ => (hR q).1.const_mul _)]`. Simplify using `only [integral_const_mul, fun q => (hR q).2, hq, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at hL`. Use `ph_of_mul_pos (t := μ.real Fd) (ENNReal.toReal_pos h0 hfin) ?_` and prove the remaining obligations. Use `hL using 1` and compare the differences between its conclusion and the goal. Take the linear combination `(-(LinearMap.det (1 - (a : V →ₗ[ℂ] V)) * c * (μ.real Fd : ℂ))) * hα0`.
-/
theorem ph_const_mul_det {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (H : Sesq V) (hH : IsPosHerm H)
    (a : V ≃ₗ[ℂ] V) (ha : ∀ z w, H (a z) (a w) = H z w) (hdet : LinearMap.det (1 - (a : V →ₗ[ℂ] V)) ≠ 0)
    (Λ Λ' : AddSubgroup V) [DiscreteTopology Λ] (hfg : Λ.FG) (hle : Λ' ≤ Λ)
    (hfi : (Λ'.addSubgroupOf Λ).FiniteIndex) (haΛ : ∀ y ∈ Λ', a y ∈ Λ) (α : V → ℂ) (hα : IsSemichar H Λ α)
    (hαa : ∀ y ∈ Λ', α (a y) = α y) (Fd : Set V) (hFd : IsAddFundamentalDomain Λ' Fd μ) (h0 : μ Fd ≠ 0)
    (hfin : μ Fd ≠ ⊤) (θ : V → ℂ)
    (hline : ∀ F : V → ℂ, Differentiable ℂ F → (∀ x ∈ Λ, ∀ z, α x * Heisenberg₂ H x F z = F z) → ∃ b : ℂ, F = b • θ)
    {Q : Type} [Fintype Q] (r : Q → V) (hr : ∀ q, ∀ y ∈ Λ', ∃ m : ℤ, (H (r q) y).im = m)
    (q₀ : Q) (hq : ∀ q, r q ∈ Λ ↔ q = q₀) (c : ℂ)
    (hc : ∀ z, θ (a z) = c * ∑ q, α (r q) * Heisenberg₂ H (r q) θ z) :
    Ph (c * LinearMap.det (1 - (a : V →ₗ[ℂ] V))) := by
  have hL := Graph.ph_det_mul_integral V μ H hH a ha hdet Λ Λ' hfg hle hfi haΛ α hα hαa Fd hFd
  obtain ⟨-, hd, hf⟩ := KerSum.kerSum_spec V H hH Λ α hα
  have hR := fun q => integral_heis_kerSum_diag V μ H hH Λ Λ' hle α hα Fd hFd hfin (r q) (hr q)
  have key : ∀ z, kerSum H Λ α z (a z) * cexp (-(π : ℂ) * H z z) =
      c * ∑ q, α (r q) * (Heisenberg₂ H (r q) (kerSum H Λ α z) z * cexp (-(π : ℂ) * H z z)) := by
    intro z
    obtain ⟨b, hb⟩ := hline _ (hd z) (hf z)
    rw [hb, Pi.smul_apply, hc z, smul_eq_mul, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp only [Heisenberg₂, Pi.smul_apply, smul_eq_mul]
    ring
  have hr0 : r q₀ ∈ Λ := (hq q₀).2 rfl
  have hα0 : α (r q₀) * α (-r q₀) = 1 := by
    have e := hα.2.2 _ hr0 _ (Λ.neg_mem hr0)
    have e0 := hα.2.2 0 Λ.zero_mem 0 Λ.zero_mem
    have him : (H (r q₀) (r q₀)).im = 0 := by
      have := congrArg Complex.im (hH.1 (r q₀) (r q₀))
      simp only [conj_im] at this
      linarith
    simp only [add_neg_cancel, map_neg, neg_im, him, neg_zero, ofReal_zero, mul_zero, Complex.exp_zero,
      mul_one] at e
    simp only [add_zero, map_zero, zero_im, ofReal_zero, mul_zero, Complex.exp_zero, mul_one] at e0
    rcases hα.1 0 Λ.zero_mem with h | h
    · rw [← e, h]
    · rw [h] at e0; norm_num at e0
  simp only [key] at hL
  rw [integral_const_mul, integral_finsetSum _ (fun q _ => (hR q).1.const_mul _)] at hL
  simp only [integral_const_mul, fun q => (hR q).2, hq, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] at hL
  refine ph_of_mul_pos (t := μ.real Fd) (ENNReal.toReal_pos h0 hfin) ?_
  convert hL using 1
  linear_combination (-(LinearMap.det (1 - (a : V →ₗ[ℂ] V)) * c * (μ.real Fd : ℂ))) * hα0

/- English proof (translation)
Use `set d := (1 - G.conjTranspose).det with hd'`. Establish `h' : Ph (c * d)` using `ph_of_mul_pos ht (by convert h using 1; ring)`. Take `⟨m, hm, h'⟩` from `h'`. Rewrite `h'` using `[norm_mul, hc, one_mul]`. Establish `hG' : G * G.conjTranspose = 1` using `mul_eq_one_comm.1 hG`.

Establish `hconj : conj d = (-1) ^ r * G.det * d`. Establish `e1 : conj d = (1 - G).det`. Rewrite using `[hd', ← RCLike.star_def, ← Matrix.det_conjTranspose]`. Simplify using the standard rewrite rules. Establish `e2 : (1 - G) = (-G) * (1 - G.conjTranspose)`.

Rewrite using `[mul_sub, mul_one, neg_mul, hG']`. Normalize the expressions using the abelian group laws. Rewrite using `[e1, e2, Matrix.det_mul, Matrix.det_neg, Fintype.card_fin]`. Establish `hn : ((‖d‖ : ℝ) : ℂ) ^ 2 = d * conj d`. Rewrite using `[Complex.mul_conj, Complex.normSq_eq_norm_sq]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hn0 : ((‖d‖ : ℝ) : ℂ) ≠ 0` using `ofReal_ne_zero.2 (norm_ne_zero_iff.2 hd)`. Use `⟨(c * d / ‖d‖) ^ 2 * (-1) ^ r, ⟨2 * m, by omega, ?_⟩, ?_⟩` and prove the remaining obligations. Establish `: (c * d / ‖d‖) ^ m = 1` using `by rw [div_pow, h', div_self (pow_ne_zero _ hn0)]`.

Rewrite using `[mul_pow, ← pow_mul, ← pow_mul, show 2 * (2 * m) = m * 4 by ring, pow_mul, this, show r * (2 * m) = 2 * (r * m) by ring, pow_mul (-1 : ℂ)]`. Simplify using the standard rewrite rules. Establish `hs : ((-1 : ℂ) ^ r) * (-1) ^ r = 1` using `by rw [← mul_pow]; simp`. Establish `hGd : G.det ≠ 0`. Introduce `h0`.

Use `congrArg Matrix.det hG` as an intermediate fact. Rewrite `this` using `[Matrix.det_mul, h0, mul_zero, Matrix.det_one]`. Conclude with `zero_ne_one this`. Rewrite using `[div_pow, hn, hconj]`. Clear the denominators using the available nonvanishing facts.
-/
theorem sq_eq_of_ph {r : ℕ} (G : Matrix (Fin r) (Fin r) ℂ) (hG : G.conjTranspose * G = 1)
    (hd : (1 - G.conjTranspose).det ≠ 0) (c : ℂ) (hc : ‖c‖ = 1) (t : ℝ) (ht : 0 < t)
    (h : Ph (c * t * (1 - G.conjTranspose).det)) : ∃ ζ : ℂ, IsMu ζ ∧ c ^ 2 = ζ * G.det := by
  set d := (1 - G.conjTranspose).det with hd'
  have h' : Ph (c * d) := ph_of_mul_pos ht (by convert h using 1; ring)
  obtain ⟨m, hm, h'⟩ := h'
  rw [norm_mul, hc, one_mul] at h'
  have hG' : G * G.conjTranspose = 1 := mul_eq_one_comm.1 hG
  have hconj : conj d = (-1) ^ r * G.det * d := by
    have e1 : conj d = (1 - G).det := by
      rw [hd', ← RCLike.star_def, ← Matrix.det_conjTranspose]; simp
    have e2 : (1 - G) = (-G) * (1 - G.conjTranspose) := by
      rw [mul_sub, mul_one, neg_mul, hG']; abel
    rw [e1, e2, Matrix.det_mul, Matrix.det_neg, Fintype.card_fin]
  have hn : ((‖d‖ : ℝ) : ℂ) ^ 2 = d * conj d := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  have hn0 : ((‖d‖ : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.2 (norm_ne_zero_iff.2 hd)
  refine ⟨(c * d / ‖d‖) ^ 2 * (-1) ^ r, ⟨2 * m, by omega, ?_⟩, ?_⟩
  · have : (c * d / ‖d‖) ^ m = 1 := by rw [div_pow, h', div_self (pow_ne_zero _ hn0)]
    rw [mul_pow, ← pow_mul, ← pow_mul, show 2 * (2 * m) = m * 4 by ring, pow_mul, this,
      show r * (2 * m) = 2 * (r * m) by ring, pow_mul (-1 : ℂ)]
    simp
  · have hs : ((-1 : ℂ) ^ r) * (-1) ^ r = 1 := by rw [← mul_pow]; simp
    have hGd : G.det ≠ 0 := by
      intro h0
      have := congrArg Matrix.det hG
      rw [Matrix.det_mul, h0, mul_zero, Matrix.det_one] at this
      exact zero_ne_one this
    rw [div_pow, hn, hconj]
    field_simp

end Core

section Prelim
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum MeasureTheory
open scoped BigOperators

/- English proof (translation)
Take `⟨a, ha⟩` from `GlobalTheory.NormSum.exists_integer_map_eq_w0 D`. Set `φ : D.host.K →+* ℂ` to `D.host.φ₀.comp (algebraMap D.host.K D.host.E)`. Set `s : D.host.K` to `2 * (a : D.host.K) - 1`. Establish `hs : φ s = Complex.I * (Real.sqrt D.host.d : ℂ)`. Establish `: φ (a : D.host.K) = w0 D` using `ha`.

Simplify using `only [s, map_sub, map_mul, map_ofNat, map_one, this, w0]`. Expand and normalize the polynomial expressions, which then agree. Establish `hd : 0 < D.host.d` using `D.host.hyp.2.1.pos`. Establish `hne : ∀ n : ℕ, (n : ℂ) - φ s ≠ 0` using `fun n h => by`. Use `congrArg Complex.im h` as an intermediate fact.

Simplify using `[hs] at this`. Conclude with `hd.ne' this`. Establish `hne' : ∀ n : ℕ, (n : ℂ) + φ s ≠ 0` using `fun n h => by`. Use `congrArg Complex.im h` as an intermediate fact. Simplify using `[hs] at this`.

Conclude with `hd.ne' this`. Establish `hc : (starRingEnd ℂ) (φ s) = -φ s` using `by simp [hs]`. Establish `hs0 : φ s ≠ 0` using `by simpa using hne' 0`. Use `Set.infinite_of_injective_forall_mem (f := fun n : ℕ => ((n : D.host.K) + s) / ((n : D.host.K) - s)) (fun n m h => ?_) (fun n => ?_)` and prove the remaining obligations. Establish `e` using `congrArg φ h`.

Simplify using `only [map_div₀, map_add, map_sub, map_natCast] at e`. Rewrite `e` using `[div_eq_div_iff (hne n) (hne m)]`. Establish `: (n : ℂ) = m`. Apply `mul_left_cancel₀ (mul_ne_zero two_ne_zero hs0)` to reduce the goal to its premises. Take the linear combination `-e`.

Conclude with `this` after adjusting the coercions. Express the relevant statement in the definitionally equal form `φ (((n : D.host.K) + s) / ((n : D.host.K) - s)) * (starRingEnd ℂ) (φ (((n : D.host.K) + s) / ((n : D.host.K) - s))) = 1`. Simplify using `only [map_div₀, map_add, map_sub, map_natCast, hc]`. Establish `h1` using `hne n`. Establish `h2` using `hne' n`.

Rewrite using `[sub_neg_eq_add, ← sub_eq_add_neg]`. Clear the denominators using the available nonvanishing facts.
-/
theorem infinite_norm_one (D : D7) :
    Set.Infinite {z : D.host.K | D.host.φ₀ (z : D.host.E) * (starRingEnd ℂ) (D.host.φ₀ (z : D.host.E)) = 1} := by
  obtain ⟨a, ha⟩ := GlobalTheory.NormSum.exists_integer_map_eq_w0 D
  let φ : D.host.K →+* ℂ := D.host.φ₀.comp (algebraMap D.host.K D.host.E)
  let s : D.host.K := 2 * (a : D.host.K) - 1
  have hs : φ s = Complex.I * (Real.sqrt D.host.d : ℂ) := by
    have : φ (a : D.host.K) = w0 D := ha
    simp only [s, map_sub, map_mul, map_ofNat, map_one, this, w0]
    ring
  have hd : 0 < D.host.d := D.host.hyp.2.1.pos
  have hne : ∀ n : ℕ, (n : ℂ) - φ s ≠ 0 := fun n h => by
    have := congrArg Complex.im h
    simp [hs] at this
    exact hd.ne' this
  have hne' : ∀ n : ℕ, (n : ℂ) + φ s ≠ 0 := fun n h => by
    have := congrArg Complex.im h
    simp [hs] at this
    exact hd.ne' this
  have hc : (starRingEnd ℂ) (φ s) = -φ s := by simp [hs]
  have hs0 : φ s ≠ 0 := by simpa using hne' 0
  refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ => ((n : D.host.K) + s) / ((n : D.host.K) - s))
    (fun n m h => ?_) (fun n => ?_)
  · have e := congrArg φ h
    simp only [map_div₀, map_add, map_sub, map_natCast] at e
    rw [div_eq_div_iff (hne n) (hne m)] at e
    have : (n : ℂ) = m := by
      apply mul_left_cancel₀ (mul_ne_zero two_ne_zero hs0)
      linear_combination -e
    exact_mod_cast this
  · change φ (((n : D.host.K) + s) / ((n : D.host.K) - s)) *
      (starRingEnd ℂ) (φ (((n : D.host.K) + s) / ((n : D.host.K) - s))) = 1
    simp only [map_div₀, map_add, map_sub, map_natCast, hc]
    have h1 := hne n
    have h2 := hne' n
    rw [sub_neg_eq_add, ← sub_eq_add_neg]
    field_simp

/- English proof (translation)
Establish `hL` using `HalfPeriod.exists_basis_lamOf D cc δ hC`. Take `⟨a, ha⟩` from `GlobalTheory.NormSum.exists_integer_map_eq_w0 D`. Use `div_self (mul_ne_zero ?_ (Complex.exp_ne_zero _))` and prove the remaining obligations. Rewrite using `[zero_add, Ne, (GlobalTheory.OddTheta.sgStar_laws _ hL).2.1]`. Introduce `h`.

Use `GlobalTheory.ThetaInter.lam_mul_mem a h` as an intermediate fact. Rewrite `this` using `[ha]`. Conclude with `ht.2.1 this`.
-/
theorem evenTheta_zero_eq_one (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (hC : Crv D cc δ) (t0 : ℂ)
    (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0) : GL3Theta.th0 (lamOf D cc δ) t0 0 = 1 := by
  have hL := HalfPeriod.exists_basis_lamOf D cc δ hC
  obtain ⟨a, ha⟩ := GlobalTheory.NormSum.exists_integer_map_eq_w0 D
  refine div_self (mul_ne_zero ?_ (Complex.exp_ne_zero _))
  rw [zero_add, Ne, (GlobalTheory.OddTheta.sgStar_laws _ hL).2.1]
  intro h
  have := GlobalTheory.ThetaInter.lam_mul_mem a h
  rw [ha] at this
  exact ht.2.1 this

/- English proof (translation)
Establish `hG1` using `(GlobalTheory.InducedType.induced_type D).1`. Take `⟨h1, h2, h3, -, h5⟩` from `GlobalTheory.OnCoord.coords_of_orthonormal_basis D hG1 cc δ N N' r b hb`. Take `⟨-, h2', -, -, h5'⟩` from `GlobalTheory.OnCoord.coords_of_orthonormal_basis D hG1 cc δ N N' r b' hb'`. Establish `hc : ∀ x (c : Fin r → Matrix (Fin N') (Fin N) D.host.E) j, coordB D (tor0 D cc δ) c j (embV D (tor0 D cc δ) x) = D.host.φ₀ ((hYY D x (c j) : D.host.K) : D.host.E)` using `fun x c j => (map_hYY D x (c j)).symm`. Set `e : VC D N N' ≃ₗ[ℂ] (Fin r → ℂ)` to `LinearEquiv.ofBijective (LinearMap.pi fun j => GlobalTheory.PullNorm.coordLin D (tor0 D cc δ) b j) h5`.

Set `e' : VC D N N' ≃ₗ[ℂ] (Fin r → ℂ)` to `LinearEquiv.ofBijective (LinearMap.pi fun j => GlobalTheory.PullNorm.coordLin D (tor0 D cc δ) b' j) h5'`. Establish `he : ∀ z j, e z j = coordB D (tor0 D cc δ) b j z` using `fun _ _ => rfl`. Establish `he' : ∀ z j, e' z j = coordB D (tor0 D cc δ) b' j z` using `fun _ _ => rfl`. Use `⟨?_, e'.trans e.symm, fun z j => by rw [← he, ← he']; simp, ?_⟩` and prove the remaining obligations. Use extensionality with `i j`.

Use `h3 (embV D (tor0 D cc δ) (b' j)) (embV D (tor0 D cc δ) (b' i))` as an intermediate fact. Express the relevant statement in the definitionally equal form `coordB D (tor0 D cc δ) b' i (embV D (tor0 D cc δ) (b' j)) = _ at this`. Rewrite `this` using `[h2']`. Rewrite using `[Matrix.mul_apply, Matrix.one_apply, if_congr (eq_comm (a := i)) rfl rfl, this]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[hc, hc, Matrix.conjTranspose_apply, hG, hG, mul_comm]`. Both sides reduce to the same expression. Rewrite using `[← LinearMap.det_conj _ e, ← LinearMap.det_toLin']`. Use `congr 1`. Use `LinearMap.pi_ext' fun i => LinearMap.ext_ring ?_` and prove the remaining obligations.

Establish `hi : e.symm (Pi.single i 1) = embV D (tor0 D cc δ) (b i)`. Rewrite using `[LinearEquiv.symm_apply_eq]`. Use function extensionality and compare the values at `j`. Rewrite using `[he, h2, Pi.single_apply, if_congr (eq_comm (a := i)) rfl rfl]`. Use function extensionality and compare the values at `j`.

Simplify using `only [LinearMap.comp_apply, LinearMap.coe_single, LinearEquiv.coe_coe, LinearMap.sub_apply, Module.End.one_apply, map_sub, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, Pi.sub_apply, Matrix.toLin'_one, LinearMap.id_apply, Matrix.toLin'_apply, Matrix.mulVec_single_one]`. Rewrite using `[hi, he', hc, map_hYY_symm, ← hG]`. Both sides reduce to the same expression.
-/
theorem exists_unitary (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (N N' r : ℕ)
    (b b' : Fin r → Matrix (Fin N') (Fin N) D.host.E) (hb : OnB D b) (hb' : OnB D b')
    (G : Matrix (Fin r) (Fin r) ℂ)
    (hG : ∀ i j, G i j = D.host.φ₀ (((hYY D (b' j) (b i) : D.host.K)) : D.host.E)) :
    G.conjTranspose * G = 1 ∧ ∃ a : VC D N N' ≃ₗ[ℂ] VC D N N',
      (∀ z j, coordB D (tor0 D cc δ) b j (a z) = coordB D (tor0 D cc δ) b' j z) ∧
      LinearMap.det (1 - (a : VC D N N' →ₗ[ℂ] VC D N N')) = (1 - G.conjTranspose).det := by
  have hG1 := (GlobalTheory.InducedType.induced_type D).1
  obtain ⟨h1, h2, h3, -, h5⟩ := GlobalTheory.OnCoord.coords_of_orthonormal_basis D hG1 cc δ N N' r b hb
  obtain ⟨-, h2', -, -, h5'⟩ := GlobalTheory.OnCoord.coords_of_orthonormal_basis D hG1 cc δ N N' r b' hb'
  have hc : ∀ x (c : Fin r → Matrix (Fin N') (Fin N) D.host.E) j,
      coordB D (tor0 D cc δ) c j (embV D (tor0 D cc δ) x) = D.host.φ₀ ((hYY D x (c j) : D.host.K) : D.host.E) :=
    fun x c j => (map_hYY D x (c j)).symm
  let e : VC D N N' ≃ₗ[ℂ] (Fin r → ℂ) :=
    LinearEquiv.ofBijective (LinearMap.pi fun j => GlobalTheory.PullNorm.coordLin D (tor0 D cc δ) b j) h5
  let e' : VC D N N' ≃ₗ[ℂ] (Fin r → ℂ) :=
    LinearEquiv.ofBijective (LinearMap.pi fun j => GlobalTheory.PullNorm.coordLin D (tor0 D cc δ) b' j) h5'
  have he : ∀ z j, e z j = coordB D (tor0 D cc δ) b j z := fun _ _ => rfl
  have he' : ∀ z j, e' z j = coordB D (tor0 D cc δ) b' j z := fun _ _ => rfl
  refine ⟨?_, e'.trans e.symm, fun z j => by rw [← he, ← he']; simp, ?_⟩
  · ext i j
    have := h3 (embV D (tor0 D cc δ) (b' j)) (embV D (tor0 D cc δ) (b' i))
    change coordB D (tor0 D cc δ) b' i (embV D (tor0 D cc δ) (b' j)) = _ at this
    rw [h2'] at this
    rw [Matrix.mul_apply, Matrix.one_apply, if_congr (eq_comm (a := i)) rfl rfl, this]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hc, hc, Matrix.conjTranspose_apply, hG, hG, mul_comm]
    rfl
  · rw [← LinearMap.det_conj _ e, ← LinearMap.det_toLin']
    congr 1
    refine LinearMap.pi_ext' fun i => LinearMap.ext_ring ?_
    have hi : e.symm (Pi.single i 1) = embV D (tor0 D cc δ) (b i) := by
      rw [LinearEquiv.symm_apply_eq]
      funext j
      rw [he, h2, Pi.single_apply, if_congr (eq_comm (a := i)) rfl rfl]
    funext j
    simp only [LinearMap.comp_apply, LinearMap.coe_single, LinearEquiv.coe_coe, LinearMap.sub_apply,
      Module.End.one_apply, map_sub, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, Pi.sub_apply,
      Matrix.toLin'_one, LinearMap.id_apply, Matrix.toLin'_apply, Matrix.mulVec_single_one]
    rw [hi, he', hc, map_hYY_symm, ← hG]
    rfl

/- English proof (translation)
The claim follows from `hb ▸ ZSpan.isAddFundamentalDomain' b μ`.
-/
theorem exists_bounded_domain {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    [MeasurableSpace W] [BorelSpace W] (μ : Measure W) {κ : Type} [Fintype κ] (b : Module.Basis κ ℝ W)
    {A : AddSubgroup W} (hb : (Submodule.span ℤ (Set.range b)).toAddSubgroup = A) :
    IsAddFundamentalDomain A (ZSpan.fundamentalDomain b) μ :=
  hb ▸ ZSpan.isAddFundamentalDomain' b μ

/- English proof (translation)
Take `⟨hfg, hsp, hd, hs⟩` from `GlobalTheory.ThetaInter.klat_facts hC hA`. Establish `hH` using `GlobalTheory.ThetaInter.isHerm_sesqOf D (tor0 D cc δ) N N'`. Establish `hdisc` using `GlobalTheory.ThetaInter.discrete_of_selfDual hH hd hfg`. Establish `: Countable A` using `countable_of_Lindelof_of_discrete`. Take `⟨n, b, hb⟩` from `GlobalTheory.ThetaInter.exists_basis hdisc hsp`.

Establish `hFd` using `exists_bounded_domain volume b hb`. Use `set f := GlobalTheory.ThetaInter.rho (GlobalTheory.ThetaInter.sesqOf D (tor0 D cc δ) N N') G with hf`. Establish `hper : ∀ x ∈ A, ∀ z, f (z + x) = f z` using `fun x hx z => GlobalTheory.ThetaInter.rho_add_of_fixed hH hs hG.2 hx z`. Establish `hcont : Continuous f` using `GlobalTheory.ThetaInter.continuous_rho hH hG.1.continuous`. Establish `hnn : ∀ z, 0 ≤ f z` using `fun z => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le`.

Express the relevant statement in the definitionally equal form `GlobalTheory.ThetaInter.mean volume A f ≠ 0`. Rewrite using `[GlobalTheory.ThetaInter.mean_eq volume b hb hper, setAverage_eq, smul_eq_mul]`. Establish `hbd` using `ZSpan.fundamentalDomain_isBounded b`. Use `mul_ne_zero (inv_ne_zero (ENNReal.toReal_pos (hFd.measure_ne_zero (NeZero.ne _)) hbd.measure_lt_top.ne).ne') (ne_of_gt ?_)` and prove the remaining obligations. Rewrite using `[setIntegral_pos_iff_support_of_nonneg_ae (Filter.Eventually.of_forall hnn) ((hcont.continuousOn.integrableOn_compact hbd.isCompact_closure).mono_set subset_closure), pos_iff_ne_zero]`.

Introduce `h0`. Establish `h1 : volume (Function.support f) = 0` using `hFd.measure_zero_of_invariant _ (fun g => by`. Use extensionality with `z`. Rewrite using `[Set.mem_vadd_set_iff_neg_vadd_mem, Function.mem_support, Function.mem_support, AddSubgroup.vadd_def, vadd_eq_add, add_comm, hper _ (-g).2]) h0`. Take `⟨z, hz⟩` from `Function.ne_iff.1 hne`.

Conclude with `(hcont.isOpen_support.measure_pos volume ⟨z, mul_ne_zero (pow_ne_zero _ (norm_ne_zero_iff.2 hz)) (Real.exp_pos _).ne'⟩).ne' h1`.
-/
theorem normSq_ne_zero (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (hC : Crv D cc δ) {N N' : ℕ}
    {A : AddSubgroup (VC D N N')} (hA : KLat D (tor0 D cc δ) A) {G : VC D N N' → ℂ}
    (hG : G ∈ ThSp D (tor0 D cc δ) A) (hne : G ≠ 0) : normSq D (tor0 D cc δ) A G ≠ 0 := by
  obtain ⟨hfg, hsp, hd, hs⟩ := GlobalTheory.ThetaInter.klat_facts hC hA
  have hH := GlobalTheory.ThetaInter.isHerm_sesqOf D (tor0 D cc δ) N N'
  have hdisc := GlobalTheory.ThetaInter.discrete_of_selfDual hH hd hfg
  have : Countable A := countable_of_Lindelof_of_discrete
  obtain ⟨n, b, hb⟩ := GlobalTheory.ThetaInter.exists_basis hdisc hsp
  have hFd := exists_bounded_domain volume b hb
  set f := GlobalTheory.ThetaInter.rho (GlobalTheory.ThetaInter.sesqOf D (tor0 D cc δ) N N') G with hf
  have hper : ∀ x ∈ A, ∀ z, f (z + x) = f z := fun x hx z =>
    GlobalTheory.ThetaInter.rho_add_of_fixed hH hs hG.2 hx z
  have hcont : Continuous f := GlobalTheory.ThetaInter.continuous_rho hH hG.1.continuous
  have hnn : ∀ z, 0 ≤ f z := fun z => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  change GlobalTheory.ThetaInter.mean volume A f ≠ 0
  rw [GlobalTheory.ThetaInter.mean_eq volume b hb hper, setAverage_eq, smul_eq_mul]
  have hbd := ZSpan.fundamentalDomain_isBounded b
  refine mul_ne_zero (inv_ne_zero (ENNReal.toReal_pos (hFd.measure_ne_zero (NeZero.ne _))
    hbd.measure_lt_top.ne).ne') (ne_of_gt ?_)
  rw [setIntegral_pos_iff_support_of_nonneg_ae (Filter.Eventually.of_forall hnn)
    ((hcont.continuousOn.integrableOn_compact hbd.isCompact_closure).mono_set subset_closure), pos_iff_ne_zero]
  intro h0
  have h1 : volume (Function.support f) = 0 := hFd.measure_zero_of_invariant _ (fun g => by
    ext z
    rw [Set.mem_vadd_set_iff_neg_vadd_mem, Function.mem_support, Function.mem_support, AddSubgroup.vadd_def,
      vadd_eq_add, add_comm, hper _ (-g).2]) h0
  obtain ⟨z, hz⟩ := Function.ne_iff.1 hne
  exact (hcont.isOpen_support.measure_pos volume
    ⟨z, mul_ne_zero (pow_ne_zero _ (norm_ne_zero_iff.2 hz)) (Real.exp_pos _).ne'⟩).ne' h1

/- English proof (translation)
Establish `hG1` using `(GlobalTheory.InducedType.induced_type D).1`. Take `⟨h1, h2, h3, h4, -⟩` from `GlobalTheory.OnCoord.coords_of_orthonormal_basis D hG1 cc δ N N' r b hb`. Take `⟨hd, hinv⟩` from `HalfPeriod.theta_signed_translation D cc δ hC t0 ht`. Use `⟨GlobalTheory.ProdTheta.pullB_mem_ThSp D _ N N' r b _ h3 h4 hd hinv, ?_, ?_⟩` and prove the remaining obligations. Simplify using `[pullB, coordB, evenTheta_zero_eq_one D cc δ hC t0 ht]`.

Use `GlobalTheory.PullNorm.normSq_pullB D (tor0 D cc δ) N N' r b (HalfPeriod.exists_basis_lamOf D cc δ hC) (fun i j => by rw [h2, if_congr (eq_comm (a := i)) rfl rfl]) h1 _ hd.continuous fun ω hω z => ?_` and prove the remaining obligations. Take `⟨m, -, hm⟩` from `hinv ω hω`. Rewrite using `[← hm z, norm_mul, norm_zpow, norm_neg, norm_one, one_zpow, one_mul]`. Both sides reduce to the same expression.
-/
theorem pullB_mem (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (hC : Crv D cc δ) (t0 : ℂ)
    (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0) (N N' r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E)
    (hb : OnB D b) :
    pullB D (tor0 D cc δ) b (GL3Theta.th0 (lamOf D cc δ) t0) ∈ ThSp D (tor0 D cc δ) (LaB D (tor0 D cc δ) b) ∧
      pullB D (tor0 D cc δ) b (GL3Theta.th0 (lamOf D cc δ) t0) 0 = 1 ∧
      normSq D (tor0 D cc δ) (LaB D (tor0 D cc δ) b) (pullB D (tor0 D cc δ) b (GL3Theta.th0 (lamOf D cc δ) t0)) =
        nrm1Sq (lamOf D cc δ) (GL3Theta.th0 (lamOf D cc δ) t0) ^ r := by
  have hG1 := (GlobalTheory.InducedType.induced_type D).1
  obtain ⟨h1, h2, h3, h4, -⟩ := GlobalTheory.OnCoord.coords_of_orthonormal_basis D hG1 cc δ N N' r b hb
  obtain ⟨hd, hinv⟩ := HalfPeriod.theta_signed_translation D cc δ hC t0 ht
  refine ⟨GlobalTheory.ProdTheta.pullB_mem_ThSp D _ N N' r b _ h3 h4 hd hinv, ?_, ?_⟩
  · simp [pullB, coordB, evenTheta_zero_eq_one D cc δ hC t0 ht]
  · refine GlobalTheory.PullNorm.normSq_pullB D (tor0 D cc δ) N N' r b
      (HalfPeriod.exists_basis_lamOf D cc δ hC)
      (fun i j => by rw [h2, if_congr (eq_comm (a := i)) rfl rfl]) h1 _ hd.continuous fun ω hω z => ?_
    obtain ⟨m, -, hm⟩ := hinv ω hω
    rw [← hm z, norm_mul, norm_zpow, norm_neg, norm_one, one_zpow, one_mul]
    rfl

end Prelim

section Torus
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum MeasureTheory GlobalTheory.Phase
open scoped BigOperators

/- English proof (translation)
Unfold `Iop`. Rewrite using `[mul_left_comm, mul_finsum _ c]`. Use `congr 1`. Use `finsum_congr fun q => ?_` and prove the remaining obligations. Simplify using `only [U]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem iop_smul (D : D7) (T : Tor D) {N N' : ℕ} (A B : AddSubgroup (VC D N N')) (c : ℂ) (G : VC D N N' → ℂ)
    (z : VC D N N') : Iop D T A B (fun w => c * G w) z = c * Iop D T A B G z := by
  unfold Iop
  rw [mul_left_comm, mul_finsum _ c]
  congr 1
  refine finsum_congr fun q => ?_
  simp only [U]; ring

/- English proof (translation)
Use function extensionality and compare the values at `z`. Simplify using `[Iop, h]`.
-/
theorem iop_eq_zero (D : D7) (T : Tor D) {N N' : ℕ} (A B : AddSubgroup (VC D N N')) (G : VC D N N' → ℂ)
    (h : (A.addSubgroupOf B).index = 0) : Iop D T A B G = 0 := by
  funext z
  simp [Iop, h]

/- English proof (translation)
Unfold `normSq`. Simplify using `only [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow, mul_assoc, average, integral_const_mul]`.
-/
theorem normSq_smul (D : D7) (T : Tor D) {N N' : ℕ} (A : AddSubgroup (VC D N N')) (c : ℂ) (G : VC D N N' → ℂ) :
    normSq D T A (c • G) = ‖c‖ ^ 2 * normSq D T A G := by
  unfold normSq
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow, mul_assoc, average, integral_const_mul]

/- English proof (translation)
Establish `hG1` using `(GlobalTheory.InducedType.induced_type D).1`. Establish `harea : 0 < area (tor0 D cc δ).abelian₂` using `area_pos D cc δ hC`. Establish `hK : KLat D (tor0 D cc δ) (LaB D (tor0 D cc δ) b)` using `Or.inl ⟨r, b, hb, rfl⟩`. Establish `hK' : KLat D (tor0 D cc δ) (LaB D (tor0 D cc δ) b')` using `Or.inl ⟨r, b', hb', rfl⟩`. Take `⟨hline, -, hint, -, hfg, hspan, -⟩` from `GlobalTheory.ThetaLine.theta_line D hG1 cc δ hC N N' _ hK`.

Take `⟨hline', -, hint', -⟩` from `GlobalTheory.ThetaLine.theta_line D hG1 cc δ hC N N' _ hK'`. Take `⟨hθ, hθ0, hθn⟩` from `pullB_mem D cc δ hC t0 ht N N' r b hb`. Take `⟨hθ', -, hθn'⟩` from `pullB_mem D cc δ hC t0 ht N N' r b' hb'`. Take `⟨-, hI, hIn, hII⟩` from `GlobalTheory.theta_translation_intertwiner_unitary D cc δ hC N N' _ _ hK hK' _ hθ`. Take `⟨hGG, a, ha, hadet⟩` from `exists_unitary D cc δ N N' r b b' hb hb' G hG`.

Take `⟨-, -, hH, hmem, -⟩` from `GlobalTheory.OnCoord.coords_of_orthonormal_basis D hG1 cc δ N N' r b hb`. Take `⟨-, -, hH', hmem', -⟩` from `GlobalTheory.OnCoord.coords_of_orthonormal_basis D hG1 cc δ N N' r b' hb'`. Establish `hθa : pullB D (tor0 D cc δ) b' (GL3Theta.th0 (lamOf D cc δ) t0) = fun z => pullB D (tor0 D cc δ) b (GL3Theta.th0 (lamOf D cc δ) t0) (a z)`. Use function extensionality and compare the values at `z`. Simplify using `only [pullB, ha]`.

Establish `hau : ∀ z w, Hf D (tor0 D cc δ) (a z) (a w) = Hf D (tor0 D cc δ) z w`. Introduce `z w`. Rewrite using `[Hf, Hf, hH, hH']`. Simplify using `only [ha]`. Establish `haA : ∀ z, z ∈ LaB D (tor0 D cc δ) b' ↔ a z ∈ LaB D (tor0 D cc δ) b`.

Introduce `z`. Rewrite using `[hmem, hmem']`. Simplify using `only [ha]`. Establish `hnz` using `fun h => normSq_ne_zero D cc δ hC hK hθ h`. Establish `hdisc` using `GlobalTheory.ThetaInter.discrete_of_selfDual (GlobalTheory.ThetaInter.isHerm_sesqOf D (tor0 D cc δ) N N') (GlobalTheory.ThetaInter.klat_facts hC hK).2.2.1 hfg`.

Rewrite `hθn'` using `[← hθn]`. Generalize the expression as in `LaB D (tor0 D cc δ) b = A at *`. Generalize the expression as in `LaB D (tor0 D cc δ) b' = A' at *`. Generalize the expression as in `pullB D (tor0 D cc δ) b (GL3Theta.th0 (lamOf D cc δ) t0) = θ at *`. Generalize the expression as in `pullB D (tor0 D cc δ) b' (GL3Theta.th0 (lamOf D cc δ) t0) = θ' at *`.

Generalize the expression as in `tor0 D cc δ = T at *`. Establish `hθne : θ ≠ 0` using `fun h => by rw [h] at hθ0; exact zero_ne_one hθ0`. Establish `hIne : Iop D T A A' θ ≠ 0` using `fun h => by`. Apply `hθne` to reduce the goal to its premises. Rewrite using `[← hII, h]`.

Use function extensionality and compare the values at `z`. Simplify using `[Iop, U]`. Establish `hn : (A.addSubgroupOf A').index ≠ 0` using `fun h => hIne (iop_eq_zero D T _ _ _ h)`. Establish `hn' : (A'.addSubgroupOf A).index ≠ 0` using `fun h => hθne (hII ▸ iop_eq_zero D T _ _ _ h)`. Take `⟨c, hc⟩` from `hline' θ' hθ' _ hI hIne`.

Establish `: Countable A` using `countable_of_Lindelof_of_discrete`. Establish `hfi : ((A ⊓ A').addSubgroupOf A).FiniteIndex` using `⟨by rwa [AddSubgroup.inf_addSubgroupOf_left]⟩`. Establish `: (A'.addSubgroupOf A).FiniteIndex` using `⟨hn'⟩`. Establish `hsp` using `GlobalTheory.ThetaInter.span_inf_eq_top (A₁ := A') hspan`. Rewrite `hsp` using `[inf_comm]`.

Take `⟨n, β, hβ⟩` from `GlobalTheory.ThetaInter.exists_basis (A := A ⊓ A') (DiscreteTopology.of_subset hdisc (inf_le_left : A ⊓ A' ≤ A)) hsp`. Establish `hFd` using `exists_bounded_domain volume β hβ`. Establish `hbd` using `ZSpan.fundamentalDomain_isBounded β`. Establish `: Countable ↥(A ⊓ A')` using `(AddSubgroup.inclusion_injective (inf_le_left : A ⊓ A' ≤ A)).countable`. Establish `hc1 : ‖c‖ = 1`.

Establish `e` using `hθn'`. Rewrite `e` using `[hc, normSq_smul, hIn]`. Establish `e2 : ‖c‖ ^ 2 = 1` using `mul_left_eq_self₀.1 e |>.resolve_right (hnz hθne)`. Conclude with `(sq_eq_sq₀ (norm_nonneg c) zero_le_one).1 (by rw [e2, one_pow])`. Establish `hHp` using `isPosHerm_formV D T N N' harea`.

Establish `hal : ∀ x : VC D N N', al D T x = 1 ∨ al D T x = -1` using `fun x => by`. Unfold `al`. Break down `Int.even_or_odd (round (Real.sqrt D.host.d / 2 * (Hf D T x x).re)) with h | h` into its components or cases. Conclude with `Or.inl h.neg_one_zpow`. Conclude with `Or.inr h.neg_one_zpow`.

Establish `hsc : IsSemichar (formV D T N N') A (al D T)` using `isSemichar_of_fixed _ hHp A _ (fun x _ => hal x) hint θ hθne hθ.2`. Establish `: (A.addSubgroupOf A').FiniteIndex` using `⟨hn⟩`. Establish `: Fintype (A' ⧸ A.addSubgroupOf A')` using `Fintype.ofFinite _`. Establish `hpos : 0 < (Real.sqrt ((A.addSubgroupOf A').index : ℝ))⁻¹` using `inv_pos.2 (Real.sqrt_pos.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)))`. Establish `hph` using `ph_const_mul_det volume (formV D T N N') hHp a hau (by rwa [hadet]) A (A ⊓ A') hfg inf_le_left hfi (fun y hy => (haA y).1 hy.2) (al D T) hsc (fun y _ => by simp only [al, hau]) _ hFd (hFd.measure_ne_zero (NeZero.ne _)) hbd.measure_lt_top.ne θ (fun F hF hF' => hline F ⟨hF, hF'⟩ θ …`.

Rewrite using `[← AddSubgroup.mem_addSubgroupOf, ← QuotientAddGroup.eq_zero_iff, QuotientAddGroup.out_eq', QuotientAddGroup.mk_zero])`. Use the proof step `(c * ((Real.sqrt ((A.addSubgroupOf A').index : ℝ))⁻¹ : ℝ)) (fun z => by`. Establish `e` using `congrFun (hθa.symm.trans hc) z`. Simplify using `only [Pi.smul_apply, smul_eq_mul, Iop, finsum_eq_sum_of_fintype] at e`. Rewrite using `[e, mul_assoc, Complex.ofReal_inv]`.

Use the proof step `rfl)`. Rewrite `hph` using `[hadet]`. Take `⟨ζ, hζ, hsq⟩` from `sq_eq_of_ph G hGG hd c hc1 _ hpos hph`. Conclude with `⟨c, ζ, hζ, hsq, hc⟩`.
-/
theorem const_sq_of_det_ne_zero (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (hC : Crv D cc δ) (t0 : ℂ)
    (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0) (N N' r : ℕ) (b b' : Fin r → Matrix (Fin N') (Fin N) D.host.E)
    (hb : OnB D b) (hb' : OnB D b') (G : Matrix (Fin r) (Fin r) ℂ)
    (hG : ∀ i j, G i j = D.host.φ₀ (((hYY D (b' j) (b i) : D.host.K)) : D.host.E))
    (hd : (1 - G.conjTranspose).det ≠ 0) :
    ∃ c ζ : ℂ, IsMu ζ ∧ c ^ 2 = ζ * G.det ∧
      pullB D (tor0 D cc δ) b' (GL3Theta.th0 (lamOf D cc δ) t0) = fun z => c *
        Iop D (tor0 D cc δ) (LaB D (tor0 D cc δ) b) (LaB D (tor0 D cc δ) b')
          (pullB D (tor0 D cc δ) b (GL3Theta.th0 (lamOf D cc δ) t0)) z := by
  have hG1 := (GlobalTheory.InducedType.induced_type D).1
  have harea : 0 < area (tor0 D cc δ).abelian₂ := area_pos D cc δ hC
  have hK : KLat D (tor0 D cc δ) (LaB D (tor0 D cc δ) b) := Or.inl ⟨r, b, hb, rfl⟩
  have hK' : KLat D (tor0 D cc δ) (LaB D (tor0 D cc δ) b') := Or.inl ⟨r, b', hb', rfl⟩
  obtain ⟨hline, -, hint, -, hfg, hspan, -⟩ := GlobalTheory.ThetaLine.theta_line D hG1 cc δ hC N N' _ hK
  obtain ⟨hline', -, hint', -⟩ := GlobalTheory.ThetaLine.theta_line D hG1 cc δ hC N N' _ hK'
  obtain ⟨hθ, hθ0, hθn⟩ := pullB_mem D cc δ hC t0 ht N N' r b hb
  obtain ⟨hθ', -, hθn'⟩ := pullB_mem D cc δ hC t0 ht N N' r b' hb'
  obtain ⟨-, hI, hIn, hII⟩ := GlobalTheory.theta_translation_intertwiner_unitary D cc δ hC N N' _ _ hK hK' _ hθ
  obtain ⟨hGG, a, ha, hadet⟩ := exists_unitary D cc δ N N' r b b' hb hb' G hG
  obtain ⟨-, -, hH, hmem, -⟩ := GlobalTheory.OnCoord.coords_of_orthonormal_basis D hG1 cc δ N N' r b hb
  obtain ⟨-, -, hH', hmem', -⟩ := GlobalTheory.OnCoord.coords_of_orthonormal_basis D hG1 cc δ N N' r b' hb'
  have hθa : pullB D (tor0 D cc δ) b' (GL3Theta.th0 (lamOf D cc δ) t0) =
      fun z => pullB D (tor0 D cc δ) b (GL3Theta.th0 (lamOf D cc δ) t0) (a z) := by
    funext z; simp only [pullB, ha]
  have hau : ∀ z w, Hf D (tor0 D cc δ) (a z) (a w) = Hf D (tor0 D cc δ) z w := by
    intro z w; rw [Hf, Hf, hH, hH']; simp only [ha]
  have haA : ∀ z, z ∈ LaB D (tor0 D cc δ) b' ↔ a z ∈ LaB D (tor0 D cc δ) b := by
    intro z; rw [hmem, hmem']; simp only [ha]
  have hnz := fun h => normSq_ne_zero D cc δ hC hK hθ h
  have hdisc := GlobalTheory.ThetaInter.discrete_of_selfDual (GlobalTheory.ThetaInter.isHerm_sesqOf D (tor0 D cc δ) N N')
    (GlobalTheory.ThetaInter.klat_facts hC hK).2.2.1 hfg
  rw [← hθn] at hθn'
  generalize LaB D (tor0 D cc δ) b = A at *
  generalize LaB D (tor0 D cc δ) b' = A' at *
  generalize pullB D (tor0 D cc δ) b (GL3Theta.th0 (lamOf D cc δ) t0) = θ at *
  generalize pullB D (tor0 D cc δ) b' (GL3Theta.th0 (lamOf D cc δ) t0) = θ' at *
  generalize tor0 D cc δ = T at *
  have hθne : θ ≠ 0 := fun h => by rw [h] at hθ0; exact zero_ne_one hθ0
  have hIne : Iop D T A A' θ ≠ 0 := fun h => by
    apply hθne
    rw [← hII, h]
    funext z
    simp [Iop, U]
  have hn : (A.addSubgroupOf A').index ≠ 0 := fun h => hIne (iop_eq_zero D T _ _ _ h)
  have hn' : (A'.addSubgroupOf A).index ≠ 0 := fun h => hθne (hII ▸ iop_eq_zero D T _ _ _ h)
  obtain ⟨c, hc⟩ := hline' θ' hθ' _ hI hIne
  have : Countable A := countable_of_Lindelof_of_discrete
  have hfi : ((A ⊓ A').addSubgroupOf A).FiniteIndex := ⟨by rwa [AddSubgroup.inf_addSubgroupOf_left]⟩
  have : (A'.addSubgroupOf A).FiniteIndex := ⟨hn'⟩
  have hsp := GlobalTheory.ThetaInter.span_inf_eq_top (A₁ := A') hspan
  rw [inf_comm] at hsp
  obtain ⟨n, β, hβ⟩ := GlobalTheory.ThetaInter.exists_basis (A := A ⊓ A')
    (DiscreteTopology.of_subset hdisc (inf_le_left : A ⊓ A' ≤ A)) hsp
  have hFd := exists_bounded_domain volume β hβ
  have hbd := ZSpan.fundamentalDomain_isBounded β
  have : Countable ↥(A ⊓ A') := (AddSubgroup.inclusion_injective (inf_le_left : A ⊓ A' ≤ A)).countable
  have hc1 : ‖c‖ = 1 := by
    have e := hθn'
    rw [hc, normSq_smul, hIn] at e
    have e2 : ‖c‖ ^ 2 = 1 := mul_left_eq_self₀.1 e |>.resolve_right (hnz hθne)
    exact (sq_eq_sq₀ (norm_nonneg c) zero_le_one).1 (by rw [e2, one_pow])
  have hHp := isPosHerm_formV D T N N' harea
  have hal : ∀ x : VC D N N', al D T x = 1 ∨ al D T x = -1 := fun x => by
    unfold al
    rcases Int.even_or_odd (round (Real.sqrt D.host.d / 2 * (Hf D T x x).re)) with h | h
    · exact Or.inl h.neg_one_zpow
    · exact Or.inr h.neg_one_zpow
  have hsc : IsSemichar (formV D T N N') A (al D T) :=
    isSemichar_of_fixed _ hHp A _ (fun x _ => hal x) hint θ hθne hθ.2
  have : (A.addSubgroupOf A').FiniteIndex := ⟨hn⟩
  have : Fintype (A' ⧸ A.addSubgroupOf A') := Fintype.ofFinite _
  have hpos : 0 < (Real.sqrt ((A.addSubgroupOf A').index : ℝ))⁻¹ :=
    inv_pos.2 (Real.sqrt_pos.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)))
  have hph := ph_const_mul_det volume (formV D T N N') hHp a hau (by rwa [hadet]) A (A ⊓ A') hfg inf_le_left hfi
    (fun y hy => (haA y).1 hy.2) (al D T) hsc (fun y _ => by simp only [al, hau]) _ hFd
    (hFd.measure_ne_zero (NeZero.ne _)) hbd.measure_lt_top.ne θ
    (fun F hF hF' => hline F ⟨hF, hF'⟩ θ hθ hθne)
    (fun q : A' ⧸ A.addSubgroupOf A' => ((Quotient.out q : A') : VC D N N'))
    (fun q y hy => hint' _ (Quotient.out q : A').2 y hy.2) (QuotientAddGroup.mk 0)
    (fun q => by
      rw [← AddSubgroup.mem_addSubgroupOf, ← QuotientAddGroup.eq_zero_iff, QuotientAddGroup.out_eq',
        QuotientAddGroup.mk_zero])
    (c * ((Real.sqrt ((A.addSubgroupOf A').index : ℝ))⁻¹ : ℝ)) (fun z => by
      have e := congrFun (hθa.symm.trans hc) z
      simp only [Pi.smul_apply, smul_eq_mul, Iop, finsum_eq_sum_of_fintype] at e
      rw [e, mul_assoc, Complex.ofReal_inv]
      rfl)
  rw [hadet] at hph
  obtain ⟨ζ, hζ, hsq⟩ := sq_eq_of_ph G hGG hd c hc1 _ hpos hph
  exact ⟨c, ζ, hζ, hsq, hc⟩

/- English proof (translation)
Introduce `D cc δ hC t0 ht N N' r b b' hb hb'`. Set `φ : D.host.K →+* ℂ` to `D.host.φ₀.comp (algebraMap D.host.K D.host.E)`. Establish `hφ : ∀ z : D.host.K, D.host.φ₀ (z : D.host.E) = φ z` using `fun _ => rfl`. Set `G : Matrix (Fin r) (Fin r) ℂ` to `Matrix.of fun i j => φ (hYY D (b' j) (b i))`. Establish `hGd : φ (Matrix.of fun i j => hYY D (b' j) (b i)).det = G.det`.

Rewrite using `[RingHom.map_det]`. Both sides reduce to the same expression. Choose the witnesses or unpack the hypotheses as in `⟨z, hz, hzn⟩ : ∃ z : D.host.K, φ z * (starRingEnd ℂ) (φ z) = 1 ∧ φ z ∉ insert (1 : ℂ) (spectrum ℂ G) := by`. Establish `hf : ((φ : D.host.K → ℂ) ⁻¹' (insert (1 : ℂ) (spectrum ℂ G))).Finite` using `((Matrix.finite_spectrum G).insert 1).preimage φ.injective.injOn`. Take `⟨z, hz, hzn⟩` from `(infinite_norm_one D).exists_notMem_finite hf`.

Conclude with `⟨z, hz, hzn⟩`. Rewrite `hzn` using `[Set.mem_insert_iff, not_or]`. Establish `hb''` using `onB_smul D b hb z hz`. Take `⟨c₁, ζ₁, hζ₁, hs₁, he₁⟩` from `const_sq_of_det_ne_zero D cc δ hC t0 ht N N' r b _ hb hb'' (φ z • (1 : Matrix (Fin r) (Fin r) ℂ)) (fun i j => by`. Rewrite using `[map_hYY_smul_left, hb.1 j i, hφ, hφ, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]`.

Distinguish the cases in `h : i = j`. Simplify using `[h]`. Simplify using `[h, Ne.symm h]) (by`. Establish `: (1 - (φ z • (1 : Matrix (Fin r) (Fin r) ℂ)).conjTranspose) = (1 - star (φ z)) • 1`. Rewrite using `[Matrix.conjTranspose_smul, Matrix.conjTranspose_one, sub_smul, one_smul]`.

Rewrite using `[this, Matrix.det_smul, Matrix.det_one, mul_one]`. Use `pow_ne_zero _ (sub_ne_zero.2 fun h => hzn.1 ?_)` and prove the remaining obligations. Rewrite using `[← star_star (φ z), ← h, star_one])`. Take `⟨c₂, ζ₂, hζ₂, hs₂, he₂⟩` from `const_sq_of_det_ne_zero D cc δ hC t0 ht N N' r _ b' hb'' hb' ((starRingEnd ℂ) (φ z) • G) (fun i j => by rw [map_hYY_smul_right]; rfl) (by`. Establish `h1 : (1 - ((starRingEnd ℂ) (φ z) • G).conjTranspose) = (((starRingEnd ℂ) (φ z)) • (algebraMap ℂ (Matrix (Fin r) (Fin r) ℂ) (φ z) - G)).conjTranspose`.

Rewrite using `[smul_sub, Algebra.algebraMap_eq_smul_one, smul_smul, mul_comm, hz, one_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_one]`. Rewrite using `[h1, Matrix.det_conjTranspose, star_ne_zero, Matrix.det_smul]`. Use `mul_ne_zero (pow_ne_zero _ fun h => ?_) ?_` and prove the remaining obligations. Rewrite `hz` using `[h, mul_zero]`. Conclude with `zero_ne_one hz`.

Conclude with `((Matrix.isUnit_iff_isUnit_det _).1 (spectrum.notMem_iff.1 hzn.2)).ne_zero)`. Take `⟨μ, hμ, he⟩` from `GlobalTheory.TripleIntertwiner.triple_constant D cc δ hC N N' _ _ _ (Or.inl ⟨r, b, hb, rfl⟩) (Or.inl ⟨r, _, hb'', rfl⟩) (Or.inl ⟨r, b', hb', rfl⟩) _ (pullB_mem D cc δ hC t0 ht N N' r b hb).1`. Take `⟨m₁, hm₁, h₁⟩` from `hζ₁`. Take `⟨m₂, hm₂, h₂⟩` from `hζ₂`. Use `⟨c₂ * c₁ * μ, ζ₁ * ζ₂ * μ ^ 2, 4 * (m₁ * m₂), by positivity, ?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[mul_pow, mul_pow, ← pow_mul μ, show 2 * (4 * (m₁ * m₂)) = 8 * (m₁ * m₂) by ring, pow_mul μ, hμ, show 4 * (m₁ * m₂) = m₁ * (4 * m₂) by ring, pow_mul ζ₁, h₁, show m₁ * (4 * m₂) = m₂ * (4 * m₁) by ring, pow_mul ζ₂, h₂]`. Simplify using the standard rewrite rules. Rewrite using `[hφ, hGd, mul_pow, mul_pow, hs₁, hs₂, Matrix.det_smul, Matrix.det_smul, Matrix.det_one]`. Establish `: φ z ^ Fintype.card (Fin r) * (starRingEnd ℂ) (φ z) ^ Fintype.card (Fin r) = 1`. Rewrite using `[← mul_pow, hz, one_pow]`.

Take the linear combination `ζ₁ * ζ₂ * μ ^ 2 * G.det * this`. Rewrite using `[he₂, he₁]`. Use function extensionality and compare the values at `w`. Rewrite using `[iop_smul, he]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem const_sq_eq_det : ∀ D : D7, LemmaCGaussConstant D := by
  intro D cc δ hC t0 ht N N' r b b' hb hb'
  let φ : D.host.K →+* ℂ := D.host.φ₀.comp (algebraMap D.host.K D.host.E)
  have hφ : ∀ z : D.host.K, D.host.φ₀ (z : D.host.E) = φ z := fun _ => rfl
  let G : Matrix (Fin r) (Fin r) ℂ := Matrix.of fun i j => φ (hYY D (b' j) (b i))
  have hGd : φ (Matrix.of fun i j => hYY D (b' j) (b i)).det = G.det := by
    rw [RingHom.map_det]; rfl
  obtain ⟨z, hz, hzn⟩ : ∃ z : D.host.K, φ z * (starRingEnd ℂ) (φ z) = 1 ∧
      φ z ∉ insert (1 : ℂ) (spectrum ℂ G) := by
    have hf : ((φ : D.host.K → ℂ) ⁻¹' (insert (1 : ℂ) (spectrum ℂ G))).Finite :=
      ((Matrix.finite_spectrum G).insert 1).preimage φ.injective.injOn
    obtain ⟨z, hz, hzn⟩ := (infinite_norm_one D).exists_notMem_finite hf
    exact ⟨z, hz, hzn⟩
  rw [Set.mem_insert_iff, not_or] at hzn
  have hb'' := onB_smul D b hb z hz
  obtain ⟨c₁, ζ₁, hζ₁, hs₁, he₁⟩ := const_sq_of_det_ne_zero D cc δ hC t0 ht N N' r b _ hb hb''
    (φ z • (1 : Matrix (Fin r) (Fin r) ℂ)) (fun i j => by
      rw [map_hYY_smul_left, hb.1 j i, hφ, hφ, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
      by_cases h : i = j
      · simp [h]
      · simp [h, Ne.symm h]) (by
      have : (1 - (φ z • (1 : Matrix (Fin r) (Fin r) ℂ)).conjTranspose) = (1 - star (φ z)) • 1 := by
        rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, sub_smul, one_smul]
      rw [this, Matrix.det_smul, Matrix.det_one, mul_one]
      refine pow_ne_zero _ (sub_ne_zero.2 fun h => hzn.1 ?_)
      rw [← star_star (φ z), ← h, star_one])
  obtain ⟨c₂, ζ₂, hζ₂, hs₂, he₂⟩ := const_sq_of_det_ne_zero D cc δ hC t0 ht N N' r _ b' hb'' hb'
    ((starRingEnd ℂ) (φ z) • G) (fun i j => by rw [map_hYY_smul_right]; rfl) (by
      have h1 : (1 - ((starRingEnd ℂ) (φ z) • G).conjTranspose) =
          (((starRingEnd ℂ) (φ z)) • (algebraMap ℂ (Matrix (Fin r) (Fin r) ℂ) (φ z) - G)).conjTranspose := by
        rw [smul_sub, Algebra.algebraMap_eq_smul_one, smul_smul, mul_comm, hz, one_smul, Matrix.conjTranspose_sub,
          Matrix.conjTranspose_one]
      rw [h1, Matrix.det_conjTranspose, star_ne_zero, Matrix.det_smul]
      refine mul_ne_zero (pow_ne_zero _ fun h => ?_) ?_
      · rw [h, mul_zero] at hz; exact zero_ne_one hz
      · exact ((Matrix.isUnit_iff_isUnit_det _).1 (spectrum.notMem_iff.1 hzn.2)).ne_zero)
  obtain ⟨μ, hμ, he⟩ := GlobalTheory.TripleIntertwiner.triple_constant D cc δ hC N N' _ _ _ (Or.inl ⟨r, b, hb, rfl⟩) (Or.inl ⟨r, _, hb'', rfl⟩)
    (Or.inl ⟨r, b', hb', rfl⟩) _ (pullB_mem D cc δ hC t0 ht N N' r b hb).1
  obtain ⟨m₁, hm₁, h₁⟩ := hζ₁
  obtain ⟨m₂, hm₂, h₂⟩ := hζ₂
  refine ⟨c₂ * c₁ * μ, ζ₁ * ζ₂ * μ ^ 2, 4 * (m₁ * m₂), by positivity, ?_, ?_, ?_⟩
  · rw [mul_pow, mul_pow, ← pow_mul μ, show 2 * (4 * (m₁ * m₂)) = 8 * (m₁ * m₂) by ring, pow_mul μ, hμ,
      show 4 * (m₁ * m₂) = m₁ * (4 * m₂) by ring, pow_mul ζ₁, h₁,
      show m₁ * (4 * m₂) = m₂ * (4 * m₁) by ring, pow_mul ζ₂, h₂]
    simp
  · rw [hφ, hGd, mul_pow, mul_pow, hs₁, hs₂, Matrix.det_smul, Matrix.det_smul, Matrix.det_one]
    have : φ z ^ Fintype.card (Fin r) * (starRingEnd ℂ) (φ z) ^ Fintype.card (Fin r) = 1 := by
      rw [← mul_pow, hz, one_pow]
    linear_combination ζ₁ * ζ₂ * μ ^ 2 * G.det * this
  · rw [he₂, he₁]
    funext w
    rw [iop_smul, he]
    ring

end Torus

end GlobalTheory.UnitaryTheta
