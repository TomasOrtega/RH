import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

namespace PositivityTheory.Xgf

section SlopeTestRemainingChoices

variable {O J : Type} [CommRing O] [Fintype J] [DecidableEq J]

/- English proof (translation)
Use `haveI : Fact d.Prime := ⟨hd⟩`. Rewrite using `[Algebra.trace_eq_matrix_trace b y, ← ZMod.intCast_zmod_eq_zero_iff_dvd]`. Establish `hnil : IsNilpotent ((Algebra.leftMulMatrix b y).map (Int.castRingHom (ZMod d)))`. Use `⟨2, ?_⟩` and prove the remaining obligations. Establish `e : (d : O) * z = (d : ℤ) • z` using `by simp [zsmul_eq_mul]`.

Rewrite using `[← Matrix.map_pow, ← map_pow, h, e, map_zsmul]`. Use extensionality with `i j`. Simplify using `only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply, eq_intCast, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self]`. Simplify using the standard rewrite rules. Establish `htr` using `(Matrix.isNilpotent_trace_of_isNilpotent hnil).eq_zero`.

Establish `hc : ((Algebra.leftMulMatrix b y).map (Int.castRingHom (ZMod d))).trace = (((Algebra.leftMulMatrix b y).trace : ℤ) : ZMod d)`. Simplify using `[Matrix.trace, Matrix.map_apply]`. Rewrite using `[← hc]`. Conclude with `htr`.
-/
theorem prime_dvd_trace_of_sq (b : Module.Basis J ℤ O) (d : ℕ) (hd : d.Prime) (y z : O) (h : y ^ 2 = (d : O) * z) :
    (d : ℤ) ∣ Algebra.trace ℤ O y := by
  classical
  haveI : Fact d.Prime := ⟨hd⟩
  rw [Algebra.trace_eq_matrix_trace b y, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hnil : IsNilpotent ((Algebra.leftMulMatrix b y).map (Int.castRingHom (ZMod d))) := by
    refine ⟨2, ?_⟩
    have e : (d : O) * z = (d : ℤ) • z := by simp [zsmul_eq_mul]
    rw [← Matrix.map_pow, ← map_pow, h, e, map_zsmul]
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply, eq_intCast,
      Int.cast_mul, Int.cast_natCast, ZMod.natCast_self]
    simp
  have htr := (Matrix.isNilpotent_trace_of_isNilpotent hnil).eq_zero
  have hc : ((Algebra.leftMulMatrix b y).map (Int.castRingHom (ZMod d))).trace
      = (((Algebra.leftMulMatrix b y).trace : ℤ) : ZMod d) := by
    simp [Matrix.trace, Matrix.map_apply]
  rw [← hc]
  exact htr

/- English proof (translation)
Rewrite using `[Matrix.mul_apply]`. Simplify using `only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, Algebra.leftMulMatrix_eq_repr_mul]`. Use `conv_rhs => rw [← b.sum_repr (r * b j), Finset.mul_sum, map_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[mul_smul_comm, LinearMap.map_smul, smul_eq_mul, mul_comm]`.
-/
theorem traceMatrix_mul_leftMulMatrix (b : Module.Basis J ℤ O) (r : O) (i j : J) :
    (Algebra.traceMatrix ℤ b * Algebra.leftMulMatrix b r) i j = Algebra.trace ℤ O (b i * (r * b j)) := by
  rw [Matrix.mul_apply]
  simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, Algebra.leftMulMatrix_eq_repr_mul]
  conv_rhs => rw [← b.sum_repr (r * b j), Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_smul_comm, LinearMap.map_smul, smul_eq_mul, mul_comm]

/- English proof (translation)
Establish `hd0 : (d : ℤ) ≠ 0` using `by exact_mod_cast hd.ne_zero`. Establish `hent : ∀ i j, (d : ℤ) ∣ (Algebra.traceMatrix ℤ b * Algebra.leftMulMatrix b r) i j`. Introduce `i j`. Rewrite using `[traceMatrix_mul_leftMulMatrix b r i j]`. Use `prime_dvd_trace_of_sq b d hd (b i * (r * b j)) (-((b i) ^ 2 * (b j) ^ 2)) ?_` and prove the remaining obligations.

Establish `e : (b i * (r * b j)) ^ 2 = (b i) ^ 2 * (b j) ^ 2 * r ^ 2` using `by ring`. Rewrite using `[e, hr]`. Expand and normalize the polynomial expressions, which then agree. Set `C : Matrix J J ℤ` to `fun i j => (Algebra.traceMatrix ℤ b * Algebra.leftMulMatrix b r) i j / d`. Establish `hTL : Algebra.traceMatrix ℤ b * Algebra.leftMulMatrix b r = (d : ℤ) • C`.

Use extensionality with `i j`. Simplify using `only [C, Matrix.smul_apply, smul_eq_mul]`. Conclude with `(Int.mul_ediv_cancel' (hent i j)).symm`. Establish `hL2 : (Algebra.leftMulMatrix b r).det ^ 2 = (-(d : ℤ)) ^ Fintype.card J`. Rewrite using `[sq, ← Matrix.det_mul, ← map_mul, ← sq, hr]`.

Establish `e : (-(d : O)) = algebraMap ℤ O (-(d : ℤ))` using `by simp`. Rewrite using `[e, AlgHom.commutes, Algebra.algebraMap_eq_smul_one, Matrix.det_smul, Matrix.det_one, _root_.mul_one]`. Establish `h1 : (Algebra.traceMatrix ℤ b * Algebra.leftMulMatrix b r).det ^ 2 = ((d : ℤ) ^ Fintype.card J) ^ 2 * C.det ^ 2`. Rewrite using `[hTL, Matrix.det_smul]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite `h1` using `[Matrix.det_mul, mul_pow, hL2, ← Algebra.discr_def, neg_pow]`. Establish `key2 : Algebra.discr ℤ b ^ 2 * (-1) ^ Fintype.card J = (d : ℤ) ^ Fintype.card J * C.det ^ 2`. Apply `mul_right_cancel₀ (pow_ne_zero (Fintype.card J) hd0)` to reduce the goal to its premises. Take the linear combination `h1`. Establish `hdv : (d : ℤ) ^ Fintype.card J ∣ Algebra.discr ℤ b ^ 2`.

Establish `h2 : (d : ℤ) ^ Fintype.card J ∣ Algebra.discr ℤ b ^ 2 * (-1) ^ Fintype.card J` using `⟨_, key2⟩`. Apply the tactic sequence `rcases neg_one_pow_eq_or ℤ (Fintype.card J) with h | h <;> rw [h] at h2 <;> simpa using h2`. Conclude with `Int.le_of_dvd (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 h0))) hdv`.
-/
theorem discriminant_bound_sqrt_neg_prime (b : Module.Basis J ℤ O) (d : ℕ) (hd : d.Prime) (r : O) (hr : r ^ 2 = -(d : O))
    (h0 : Algebra.discr ℤ b ≠ 0) : (d : ℤ) ^ Fintype.card J ≤ Algebra.discr ℤ b ^ 2 := by
  classical
  have hd0 : (d : ℤ) ≠ 0 := by exact_mod_cast hd.ne_zero
  have hent : ∀ i j, (d : ℤ) ∣ (Algebra.traceMatrix ℤ b * Algebra.leftMulMatrix b r) i j := by
    intro i j
    rw [traceMatrix_mul_leftMulMatrix b r i j]
    refine prime_dvd_trace_of_sq b d hd (b i * (r * b j)) (-((b i) ^ 2 * (b j) ^ 2)) ?_
    have e : (b i * (r * b j)) ^ 2 = (b i) ^ 2 * (b j) ^ 2 * r ^ 2 := by ring
    rw [e, hr]
    ring
  let C : Matrix J J ℤ := fun i j => (Algebra.traceMatrix ℤ b * Algebra.leftMulMatrix b r) i j / d
  have hTL : Algebra.traceMatrix ℤ b * Algebra.leftMulMatrix b r = (d : ℤ) • C := by
    ext i j
    simp only [C, Matrix.smul_apply, smul_eq_mul]
    exact (Int.mul_ediv_cancel' (hent i j)).symm
  have hL2 : (Algebra.leftMulMatrix b r).det ^ 2 = (-(d : ℤ)) ^ Fintype.card J := by
    rw [sq, ← Matrix.det_mul, ← map_mul, ← sq, hr]
    have e : (-(d : O)) = algebraMap ℤ O (-(d : ℤ)) := by simp
    rw [e, AlgHom.commutes, Algebra.algebraMap_eq_smul_one, Matrix.det_smul, Matrix.det_one,
      _root_.mul_one]
  have h1 : (Algebra.traceMatrix ℤ b * Algebra.leftMulMatrix b r).det ^ 2
      = ((d : ℤ) ^ Fintype.card J) ^ 2 * C.det ^ 2 := by
    rw [hTL, Matrix.det_smul]
    ring
  rw [Matrix.det_mul, mul_pow, hL2, ← Algebra.discr_def, neg_pow] at h1
  have key2 : Algebra.discr ℤ b ^ 2 * (-1) ^ Fintype.card J = (d : ℤ) ^ Fintype.card J * C.det ^ 2 := by
    apply mul_right_cancel₀ (pow_ne_zero (Fintype.card J) hd0)
    linear_combination h1
  have hdv : (d : ℤ) ^ Fintype.card J ∣ Algebra.discr ℤ b ^ 2 := by
    have h2 : (d : ℤ) ^ Fintype.card J ∣ Algebra.discr ℤ b ^ 2 * (-1) ^ Fintype.card J := ⟨_, key2⟩
    rcases neg_one_pow_eq_or ℤ (Fintype.card J) with h | h <;> rw [h] at h2 <;> simpa using h2
  exact Int.le_of_dvd (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 h0))) hdv

end SlopeTestRemainingChoices

/- English proof (translation)
Introduce `E _ _ _ H`. Establish `hd` using `H.d_prime`. Establish `hd1 : (1 : ℝ) ≤ H.d` using `by exact_mod_cast hd.one_lt.le`. Use `⟨by simpa using Real.sqrt_le_sqrt hd1, ?_⟩` and prove the remaining obligations. Use `set n := Module.finrank ℚ E with hn`.

Establish `hn0 : n ≠ 0` using `Module.finrank_pos.ne'`. Establish `hD : (H.d : ℤ) ^ n ≤ (discr E) ^ 2`. Establish `h` using `discriminant_bound_sqrt_neg_prime (RingOfIntegers.basis E) H.d hd H.rt H.rt_sq (discr_ne_zero E)`. Rewrite `h` using `[← Module.finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank]`. Conclude with `h`.

Establish `hR : ((Real.sqrt H.d) ^ n) ^ 2 ≤ |((discr E : ℤ) : ℝ)| ^ 2`. Rewrite using `[← pow_mul, mul_comm n 2, pow_mul, Real.sq_sqrt (by positivity), sq_abs]`. Conclude with `hD` after adjusting the coercions. Establish `hR2 : (Real.sqrt H.d) ^ n ≤ |((discr E : ℤ) : ℝ)|` using `(pow_le_pow_iff_left₀ (by positivity) (abs_nonneg _) two_ne_zero).mp hR`. Unfold `rootDiscr`.

Rewrite using `[Int.cast_abs]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem sqrt_discriminant_bounds_cm_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E), 1 ≤ Real.sqrt H.d ∧ Real.sqrt H.d ≤ rootDiscr E := by
  intro E _ _ _ H
  classical
  have hd := H.d_prime
  have hd1 : (1 : ℝ) ≤ H.d := by exact_mod_cast hd.one_lt.le
  refine ⟨by simpa using Real.sqrt_le_sqrt hd1, ?_⟩
  set n := Module.finrank ℚ E with hn
  have hn0 : n ≠ 0 := Module.finrank_pos.ne'
  have hD : (H.d : ℤ) ^ n ≤ (discr E) ^ 2 := by
    have h := discriminant_bound_sqrt_neg_prime (RingOfIntegers.basis E) H.d hd H.rt H.rt_sq (discr_ne_zero E)
    rw [← Module.finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank] at h
    exact h
  have hR : ((Real.sqrt H.d) ^ n) ^ 2 ≤ |((discr E : ℤ) : ℝ)| ^ 2 := by
    rw [← pow_mul, mul_comm n 2, pow_mul, Real.sq_sqrt (by positivity), sq_abs]
    exact_mod_cast hD
  have hR2 : (Real.sqrt H.d) ^ n ≤ |((discr E : ℤ) : ℝ)| :=
    (pow_le_pow_iff_left₀ (by positivity) (abs_nonneg _) two_ne_zero).mp hR
  unfold rootDiscr
  rw [Int.cast_abs]
  calc Real.sqrt H.d = ((Real.sqrt H.d) ^ n) ^ ((n : ℝ)⁻¹) :=
        (Real.pow_rpow_inv_natCast (Real.sqrt_nonneg _) hn0).symm
    _ ≤ _ := Real.rpow_le_rpow (by positivity) hR2 (by positivity)

end PositivityTheory.Xgf
