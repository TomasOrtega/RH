import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableComb
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.GalTheta
open scoped BigOperators

namespace GlobalTheory.GalThetaSign

/- English proof (translation)
Establish `key : ∀ {a a' : ℕ} {b b' : ℤ}, a ≤ a' → (p : ℝ) ^ a * q = (b : ℝ) → (p : ℝ) ^ a' * q = (b' : ℝ) → (-1 : ℂ) ^ b' = (-1 : ℂ) ^ b`. Introduce `a a' b b' hle hb hb'`. Take `⟨j, rfl⟩` from `Nat.exists_eq_add_of_le hle`. Establish `hr : (b' : ℝ) = ((p : ℤ) ^ j * b : ℤ)`. Rewrite using `[← hb', Int.cast_mul, Int.cast_pow, Int.cast_natCast, ← hb, pow_add]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hi : b' = (p : ℤ) ^ j * b` using `by exact_mod_cast hr`. Establish `hoddp : Odd ((p : ℤ) ^ j)` using `(by exact_mod_cast hp : Odd (p : ℤ)).pow`. Establish `hev : Even (b' - b)`. Rewrite using `[hi, show (p : ℤ) ^ j * b - b = ((p : ℤ) ^ j - 1) * b by ring]`.

Conclude with `(hoddp.sub_odd odd_one).mul_right b`. Rewrite using `[show b' = b + (b' - b) by ring, zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), hev.neg_one_zpow, mul_one]`. Break down `le_total k k' with hle | hle` into its components or cases. Conclude with `key hle h h'`. Conclude with `(key hle h' h).symm`.
-/
theorem sign_eq {p k k' : ℕ} {m m' : ℤ} {q : ℝ} (hp : Odd p) (h : (p : ℝ) ^ k * q = (m : ℝ))
    (h' : (p : ℝ) ^ k' * q = (m' : ℝ)) : (-1 : ℂ) ^ m' = (-1 : ℂ) ^ m := by
  have key : ∀ {a a' : ℕ} {b b' : ℤ}, a ≤ a' → (p : ℝ) ^ a * q = (b : ℝ) → (p : ℝ) ^ a' * q = (b' : ℝ) →
      (-1 : ℂ) ^ b' = (-1 : ℂ) ^ b := by
    intro a a' b b' hle hb hb'
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hle
    have hr : (b' : ℝ) = ((p : ℤ) ^ j * b : ℤ) := by
      rw [← hb', Int.cast_mul, Int.cast_pow, Int.cast_natCast, ← hb, pow_add]
      ring
    have hi : b' = (p : ℤ) ^ j * b := by exact_mod_cast hr
    have hoddp : Odd ((p : ℤ) ^ j) := (by exact_mod_cast hp : Odd (p : ℤ)).pow
    have hev : Even (b' - b) := by
      rw [hi, show (p : ℤ) ^ j * b - b = ((p : ℤ) ^ j - 1) * b by ring]
      exact (hoddp.sub_odd odd_one).mul_right b
    rw [show b' = b + (b' - b) by ring, zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), hev.neg_one_zpow, mul_one]
  rcases le_total k k' with hle | hle
  · exact key hle h h'
  · exact (key hle h' h).symm

/- English proof (translation)
Establish `hodd : Odd p` using `hp.odd_of_ne_two h2`. Rewrite using `[wPh, if_neg h2]`. Establish `hex : ∃ s : ℂ, ∃ (k : ℕ) (m : ℤ), (p : ℝ) ^ k * qH D T x = (m : ℝ) ∧ s = (-1 : ℂ) ^ m` using `⟨_, k, m, h, rfl⟩`. Take `⟨k0, m0, h0, hs⟩` from `Classical.epsilon_spec hex`. Rewrite using `[hs]`.

Conclude with `sign_eq hodd h h0`.
-/
theorem wPh_eq (D : D7) (T : Tor D) {N N' : ℕ} (x : VC D N N') {p k : ℕ} {m : ℤ} (hp : p.Prime) (h2 : p ≠ 2)
    (h : (p : ℝ) ^ k * qH D T x = (m : ℝ)) : wPh D T p x = (-1 : ℂ) ^ m := by
  have hodd : Odd p := hp.odd_of_ne_two h2
  rw [wPh, if_neg h2]
  have hex : ∃ s : ℂ, ∃ (k : ℕ) (m : ℤ), (p : ℝ) ^ k * qH D T x = (m : ℝ) ∧ s = (-1 : ℂ) ^ m :=
    ⟨_, k, m, h, rfl⟩
  obtain ⟨k0, m0, h0, hs⟩ := Classical.epsilon_spec hex
  rw [hs]
  exact sign_eq hodd h h0

/- English proof (translation)
Rewrite using `[ee, ← Complex.exp_nat_mul]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ee_half_pow (q : ℝ) (n : ℕ) :
    ee (q / 2) ^ n = Complex.exp ((((n : ℝ) * q : ℝ) : ℂ) * ((Real.pi : ℂ) * Complex.I)) := by
  rw [ee, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/- English proof (translation)
Rewrite using `[Complex.exp_int_mul, Complex.exp_pi_mul_I]`.
-/
theorem exp_int_pi (m : ℤ) : Complex.exp ((m : ℂ) * ((Real.pi : ℂ) * Complex.I)) = (-1 : ℂ) ^ m := by
  rw [Complex.exp_int_mul, Complex.exp_pi_mul_I]

/- English proof (translation)
Establish `hl : ∀ w : ℂ, liftM ⊤ w = (⟨w, IntermediateField.mem_top⟩ : (⊤ : IntermediateField ℚ ℂ))` using `fun w => dif_pos IntermediateField.mem_top`. Simplify using `only [cj]`. Rewrite using `[hl, hl, ← map_pow]`. Use `congr 1`.
-/
theorem cj_top_pow (σ : (⊤ : IntermediateField ℚ ℂ) →ₐ[ℚ] ℂ) (z : ℂ) (n : ℕ) :
    cj ⊤ σ (z ^ n) = cj ⊤ σ z ^ n := by
  have hl : ∀ w : ℂ, liftM ⊤ w = (⟨w, IntermediateField.mem_top⟩ : (⊤ : IntermediateField ℚ ℂ)) :=
    fun w => dif_pos IntermediateField.mem_top
  simp only [cj]
  rw [hl, hl, ← map_pow]
  congr 1

/- English proof (translation)
Establish `hl : ∀ w : ℂ, liftM ⊤ w = (⟨w, IntermediateField.mem_top⟩ : (⊤ : IntermediateField ℚ ℂ))` using `fun w => dif_pos IntermediateField.mem_top`. Establish `he : (⟨(-1 : ℂ) ^ m, IntermediateField.mem_top⟩ : (⊤ : IntermediateField ℚ ℂ)) = (-1) ^ m`. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(-1 : ℂ) ^ m = (⊤ : IntermediateField ℚ ℂ).val ((-1) ^ m)`. Rewrite using `[map_zpow₀, map_neg, map_one]`.

Simplify using `only [cj]`. Rewrite using `[hl, he, map_zpow₀, map_neg, map_one]`.
-/
theorem cj_top_sign (σ : (⊤ : IntermediateField ℚ ℂ) →ₐ[ℚ] ℂ) (m : ℤ) :
    cj ⊤ σ ((-1 : ℂ) ^ m) = (-1 : ℂ) ^ m := by
  have hl : ∀ w : ℂ, liftM ⊤ w = (⟨w, IntermediateField.mem_top⟩ : (⊤ : IntermediateField ℚ ℂ)) :=
    fun w => dif_pos IntermediateField.mem_top
  have he : (⟨(-1 : ℂ) ^ m, IntermediateField.mem_top⟩ : (⊤ : IntermediateField ℚ ℂ)) = (-1) ^ m := by
    apply Subtype.ext
    change (-1 : ℂ) ^ m = (⊤ : IntermediateField ℚ ℂ).val ((-1) ^ m)
    rw [map_zpow₀, map_neg, map_one]
  simp only [cj]
  rw [hl, he, map_zpow₀, map_neg, map_one]

/- English proof (translation)
Introduce `D T T' N N' x x' σ p k m hp h2 h hcj`. Use `⟨wPh_eq D T x hp h2 h, ?_⟩` and prove the remaining obligations. Establish `h1 : wdPh D T x ^ (p ^ k) = (-1 : ℂ) ^ m`. Rewrite using `[wdPh, ee_half_pow, Nat.cast_pow, h, ← exp_int_pi m, Complex.ofReal_intCast]`. Establish `h3 : wdPh D T' x' ^ (p ^ k) = (-1 : ℂ) ^ m`.

Rewrite using `[← hcj, ← cj_top_pow, h1, cj_top_sign]`. Rewrite `h3` using `[wdPh, ee_half_pow, ← exp_int_pi m, Complex.exp_eq_exp_iff_exists_int]`. Take `⟨l, hl⟩` from `h3`. Establish `hπ : (Real.pi : ℂ) * Complex.I ≠ 0` using `mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) Complex.I_ne_zero`. Establish `hreal : (p : ℝ) ^ k * qH D T' x' = ((m + 2 * l : ℤ) : ℝ)`.

Establish `hc : (((p : ℝ) ^ k * qH D T' x' : ℝ) : ℂ) = (((m + 2 * l : ℤ) : ℝ) : ℂ)`. Apply `mul_right_cancel₀ hπ` to reduce the goal to its premises. Move the coercions through the operations in `at hl ⊢`. Take the linear combination `hl`. Conclude with `Complex.ofReal_injective hc`.

Rewrite using `[wPh_eq D T' x' hp h2 hreal, zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), (even_two_mul l).neg_one_zpow, mul_one]`.
-/
theorem wPh_conj : ∀ (D : D7) (T T' : Tor D) (N N' : ℕ) (x x' : VC D N N') (σ : (⊤ : IntermediateField ℚ ℂ) →ₐ[ℚ] ℂ) (p k : ℕ) (m : ℤ), p.Prime → p ≠ 2 → (p : ℝ) ^ k * qH D T x = (m : ℝ) → cj ⊤ σ (wdPh D T x) = wdPh D T' x' → wPh D T p x = (-1 : ℂ) ^ m ∧ wPh D T' p x' = (-1 : ℂ) ^ m := by
  intro D T T' N N' x x' σ p k m hp h2 h hcj
  refine ⟨wPh_eq D T x hp h2 h, ?_⟩
  have h1 : wdPh D T x ^ (p ^ k) = (-1 : ℂ) ^ m := by
    rw [wdPh, ee_half_pow, Nat.cast_pow, h, ← exp_int_pi m, Complex.ofReal_intCast]
  have h3 : wdPh D T' x' ^ (p ^ k) = (-1 : ℂ) ^ m := by
    rw [← hcj, ← cj_top_pow, h1, cj_top_sign]
  rw [wdPh, ee_half_pow, ← exp_int_pi m, Complex.exp_eq_exp_iff_exists_int] at h3
  obtain ⟨l, hl⟩ := h3
  have hπ : (Real.pi : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) Complex.I_ne_zero
  have hreal : (p : ℝ) ^ k * qH D T' x' = ((m + 2 * l : ℤ) : ℝ) := by
    have hc : (((p : ℝ) ^ k * qH D T' x' : ℝ) : ℂ) = (((m + 2 * l : ℤ) : ℝ) : ℂ) := by
      apply mul_right_cancel₀ hπ
      push_cast at hl ⊢
      linear_combination hl
    exact Complex.ofReal_injective hc
  rw [wPh_eq D T' x' hp h2 hreal, zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), (even_two_mul l).neg_one_zpow, mul_one]

end GlobalTheory.GalThetaSign
