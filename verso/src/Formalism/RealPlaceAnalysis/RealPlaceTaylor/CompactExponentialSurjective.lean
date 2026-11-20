import Formalism.RealPlaceAnalysis.SmoothOnGVIff
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IndefiniteUnitaryPreservesForm

open Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section
namespace Formalism.REAL

/- English proof (translation)
Establish `hz0 : z ≠ 0`. Introduce and unpack `rfl`. Simplify using `at hz`. Use `set θ := Complex.arg z with hθ`. Establish `hre : z.re = Real.cos θ` using `by rw [Complex.cos_arg hz0, hz, div_one]`.

Establish `him : z.im = Real.sin θ` using `by rw [Complex.sin_arg, hz, div_one]`. Establish `hlog : ‖Complex.log z‖ ^ 2 = θ ^ 2`. Rewrite using `[Complex.sq_norm, Complex.normSq_apply, Complex.log_re, Complex.log_im, hz, Real.log_one]`. Expand and normalize the polynomial expressions, which then agree. Establish `hc : Real.cos θ = 1 - 2 * Real.sin (θ / 2) ^ 2`.

Establish `h1` using `Real.cos_sq_add_sin_sq (θ / 2)`. Establish `h2` using `Real.cos_two_mul (θ / 2)`. Rewrite `h2` using `[show 2 * (θ / 2) = θ by ring]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hsub : ‖z - 1‖ ^ 2 = 4 * Real.sin (θ / 2) ^ 2`.

Rewrite using `[Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, hre, him]`. Take the linear combination `Real.cos_sq_add_sin_sq θ - 2 * hc`. Establish `key : ∀ y : ℝ, 0 ≤ y → y ≤ Real.pi / 2 → 4 * y ^ 2 ≤ 12 * Real.sin y ^ 2`. Introduce `y hy0 hy1`. Establish `hs` using `Real.mul_le_sin hy0 hy1`.

Establish `hpi0` using `Real.pi_pos`. Establish `hpi : Real.pi ^ 2 ≤ 12` using `by nlinarith [Real.pi_lt_d2]`. Establish `ha0 : 0 ≤ 2 / Real.pi * y` using `by positivity`. Establish `h1 : (2 / Real.pi * y) ^ 2 ≤ Real.sin y ^ 2` using `pow_le_pow_left₀ ha0 hs 2`. Establish `h2 : 4 * y ^ 2 = Real.pi ^ 2 * (2 / Real.pi * y) ^ 2`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h2]`. Use polynomial arithmetic with `[sq_nonneg (2 / Real.pi * y)]`. Establish `hb : |θ| ≤ Real.pi` using `abs_le.2 ⟨(Complex.neg_pi_lt_arg z).le, Complex.arg_le_pi z⟩`.

Rewrite using `[hlog, hsub]`. Break down `le_or_gt 0 θ with h | h` into its components or cases. Use `key (θ / 2) (by linarith) (by rw [abs_of_nonneg h] at hb; linarith)` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Use `key (-(θ / 2)) (by linarith) (by rw [abs_of_neg h] at hb; linarith)` as an intermediate fact.

Rewrite `this` using `[Real.sin_neg, neg_sq, neg_sq]`. Use the polynomial consequences of the given equalities and inequalities.
-/
lemma norm_log_sq_le_unit_circle (z : ℂ) (hz : ‖z‖ = 1) : ‖Complex.log z‖ ^ 2 ≤ 3 * ‖z - 1‖ ^ 2 := by
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp at hz
  set θ := Complex.arg z with hθ
  have hre : z.re = Real.cos θ := by rw [Complex.cos_arg hz0, hz, div_one]
  have him : z.im = Real.sin θ := by rw [Complex.sin_arg, hz, div_one]
  have hlog : ‖Complex.log z‖ ^ 2 = θ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.log_re, Complex.log_im, hz, Real.log_one]
    ring
  have hc : Real.cos θ = 1 - 2 * Real.sin (θ / 2) ^ 2 := by
    have h1 := Real.cos_sq_add_sin_sq (θ / 2)
    have h2 := Real.cos_two_mul (θ / 2)
    rw [show 2 * (θ / 2) = θ by ring] at h2
    linarith
  have hsub : ‖z - 1‖ ^ 2 = 4 * Real.sin (θ / 2) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re,
      Complex.one_im, hre, him]
    linear_combination Real.cos_sq_add_sin_sq θ - 2 * hc
  have key : ∀ y : ℝ, 0 ≤ y → y ≤ Real.pi / 2 → 4 * y ^ 2 ≤ 12 * Real.sin y ^ 2 := by
    intro y hy0 hy1
    have hs := Real.mul_le_sin hy0 hy1
    have hpi0 := Real.pi_pos
    have hpi : Real.pi ^ 2 ≤ 12 := by nlinarith [Real.pi_lt_d2]
    have ha0 : 0 ≤ 2 / Real.pi * y := by positivity
    have h1 : (2 / Real.pi * y) ^ 2 ≤ Real.sin y ^ 2 := pow_le_pow_left₀ ha0 hs 2
    have h2 : 4 * y ^ 2 = Real.pi ^ 2 * (2 / Real.pi * y) ^ 2 := by
      field_simp
      ring
    rw [h2]
    nlinarith [sq_nonneg (2 / Real.pi * y)]
  have hb : |θ| ≤ Real.pi := abs_le.2 ⟨(Complex.neg_pi_lt_arg z).le, Complex.arg_le_pi z⟩
  rw [hlog, hsub]
  rcases le_or_gt 0 θ with h | h
  · have := key (θ / 2) (by linarith) (by rw [abs_of_nonneg h] at hb; linarith)
    nlinarith
  · have := key (-(θ / 2)) (by linarith) (by rw [abs_of_neg h] at hb; linarith)
    rw [Real.sin_neg, neg_sq, neg_sq] at this
    nlinarith

/- English proof (translation)
Simplify using `only [hs, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.star_apply]`. Use `push_cast`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Complex.star_def, Complex.conj_mul']`.
-/
lemma frobenius_eq_trace {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    ((hs A : ℝ) : ℂ) = (star A * A).trace := by
  simp only [hs, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.star_apply]
  push_cast
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, Complex.conj_mul']

/- English proof (translation)
Unfold `hs`. Check the signs of the components of the expression.
-/
lemma frobenius_nonneg_matrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ hs A := by
  unfold hs
  positivity

/- English proof (translation)
Take `⟨hu, hJ⟩` from `hk`. Establish `hN : IsStarNormal k` using `isStarNormal_of_mem_unitary hu`. Establish `hcont : ∀ f : ℂ → ℂ, ContinuousOn f (spectrum ℂ k)` using `fun f => (Matrix.finite_spectrum k).continuousOn f`. Establish `hcirc : ∀ z ∈ spectrum ℂ k, ‖z‖ = 1` using `fun z hz => spectrum.norm_eq_one_of_unitary hu hz`. Establish `hJs : star (Jm ε) = Jm ε` using `by rw [Matrix.star_eq_conjTranspose, Jm_conjTranspose]`.

Establish `hstarJ : star k * Jm ε = Jm ε * star k`. Use `congrArg star hJ` as an intermediate fact. Simplify using `only [star_mul, hJs] at this`. Conclude with `this.symm`. Use `set Y := cfc Complex.log k with hY`.

Establish `hcomm : Commute Y (Jm ε)` using `Commute.cfc hJ hstarJ Complex.log`. Establish `hstarY : star Y = -Y`. Rewrite using `[hY, ← cfc_star, ← cfc_neg Complex.log k]`. Use `cfc_congr fun z hz => ?_` and prove the remaining obligations. Establish `h1` using `hcirc z hz`.

Apply the tactic sequence `apply Complex.ext <;> simp [Complex.log_re, Complex.log_im, h1]`. Use `⟨Y, ⟨?_, hcomm.eq⟩, ?_, ?_⟩` and prove the remaining obligations. Use `show Yᴴ * Jm ε + Jm ε * Y = 0`. Rewrite using `[← Matrix.star_eq_conjTranspose, hstarY, neg_mul, hcomm.eq]`. Conclude with `neg_add_cancel _`.

Rewrite using `[← CFC.complex_exp_eq_normedSpace_exp, hY, ← cfc_comp Complex.exp Complex.log k (hg := Complex.continuous_exp.continuousOn) (hf := hcont _)]`. Rewrite using `[cfc_congr (g := id) (fun z hz => by`. Establish `h1` using `hcirc z hz`. Establish `h0 : z ≠ 0`. Introduce and unpack `rfl`.

Simplify using `at h1`. Simplify using `[Complex.exp_log h0])]`. Conclude with `cfc_id ℂ k`. Use the proof step `(have hF : cfc (fun z => 3 * (star (z - 1) * (z - 1)) - star (Complex.log z) * Complex.log z) k = (3 : ℂ) • (star (k - 1) * (k - 1)) - star Y * Y := by`. Rewrite using `[cfc_sub (fun z => 3 * (star (z - 1) * (z - 1))) (fun z => star (Complex.log z) * Complex.log z) k (hcont _) (hcont _)]`.

Rewrite using `[cfc_const_mul 3 (fun z => star (z - 1) * (z - 1)) k (hcont _)]`. Rewrite using `[cfc_mul (fun z => star (z - 1)) (fun z => z - 1) k (hcont _) (hcont _)]`. Rewrite using `[cfc_mul (fun z => star (Complex.log z)) Complex.log k (hcont _) (hcont _)]`. Rewrite using `[cfc_star (fun z => z - 1) k, cfc_star Complex.log k]`. Rewrite using `[cfc_sub (fun z => z) (fun _ => 1) k (hcont _) (hcont _), cfc_id' ℂ k, cfc_const_one ℂ k]`.

Use `set G := cfc (fun z => ((Real.sqrt (3 * ‖z - 1‖ ^ 2 - ‖Complex.log z‖ ^ 2) : ℝ) : ℂ)) k with hG`. Establish `hFG : cfc (fun z => 3 * (star (z - 1) * (z - 1)) - star (Complex.log z) * Complex.log z) k = star G * G`. Rewrite using `[hG, ← cfc_star, ← cfc_mul _ _ k (hcont _) (hcont _)]`. Use `cfc_congr fun z hz => ?_` and prove the remaining obligations. Establish `hsc` using `norm_log_sq_le_unit_circle z (hcirc z hz)`.

Establish `hnn : 0 ≤ 3 * ‖z - 1‖ ^ 2 - ‖Complex.log z‖ ^ 2` using `by linarith`. Simplify using `only [Complex.star_def, Complex.conj_ofReal]`. Rewrite using `[Complex.conj_mul', Complex.conj_mul', ← Complex.ofReal_mul, Real.mul_self_sqrt hnn]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `htr` using `congrArg Matrix.trace (hF.symm.trans hFG)`. Rewrite `htr` using `[Matrix.trace_sub, Matrix.trace_smul, ← frobenius_eq_trace, ← frobenius_eq_trace, ← frobenius_eq_trace, smul_eq_mul]`. Establish `h4 : (3 : ℂ) * (hs (k - 1) : ℂ) - (hs Y : ℂ) = ((3 * hs (k - 1) - hs Y : ℝ) : ℂ)` using `by push_cast; ring`. Rewrite `htr` using `[h4]`. Establish `h5` using `Complex.ofReal_injective htr`.

Establish `h6` using `frobenius_nonneg_matrix G`. Use the proof step `linarith)`.
-/
lemma compact_exists_log_bounded {n : ℕ} (ε : Fin n → Bool) (k : Matrix (Fin n) (Fin n) ℂ) (hk : k ∈ Kset ε) :
    ∃ Y : Matrix (Fin n) (Fin n) ℂ, inK ε Y ∧ NormedSpace.exp Y = k ∧ hs Y ≤ 3 * hs (k - 1) := by
  obtain ⟨hu, hJ⟩ := hk
  have hN : IsStarNormal k := isStarNormal_of_mem_unitary hu
  have hcont : ∀ f : ℂ → ℂ, ContinuousOn f (spectrum ℂ k) :=
    fun f => (Matrix.finite_spectrum k).continuousOn f
  have hcirc : ∀ z ∈ spectrum ℂ k, ‖z‖ = 1 := fun z hz => spectrum.norm_eq_one_of_unitary hu hz
  have hJs : star (Jm ε) = Jm ε := by rw [Matrix.star_eq_conjTranspose, Jm_conjTranspose]
  have hstarJ : star k * Jm ε = Jm ε * star k := by
    have := congrArg star hJ
    simp only [star_mul, hJs] at this
    exact this.symm
  set Y := cfc Complex.log k with hY
  have hcomm : Commute Y (Jm ε) := Commute.cfc hJ hstarJ Complex.log
  have hstarY : star Y = -Y := by
    rw [hY, ← cfc_star, ← cfc_neg Complex.log k]
    refine cfc_congr fun z hz => ?_
    have h1 := hcirc z hz
    apply Complex.ext <;> simp [Complex.log_re, Complex.log_im, h1]
  refine ⟨Y, ⟨?_, hcomm.eq⟩, ?_, ?_⟩
  · show Yᴴ * Jm ε + Jm ε * Y = 0
    rw [← Matrix.star_eq_conjTranspose, hstarY, neg_mul, hcomm.eq]
    exact neg_add_cancel _
  · rw [← CFC.complex_exp_eq_normedSpace_exp, hY,
      ← cfc_comp Complex.exp Complex.log k (hg := Complex.continuous_exp.continuousOn) (hf := hcont _)]
    rw [cfc_congr (g := id) (fun z hz => by
      have h1 := hcirc z hz
      have h0 : z ≠ 0 := by
        rintro rfl
        simp at h1
      simp [Complex.exp_log h0])]
    exact cfc_id ℂ k
  · (have hF : cfc (fun z => 3 * (star (z - 1) * (z - 1)) - star (Complex.log z) * Complex.log z) k =
        (3 : ℂ) • (star (k - 1) * (k - 1)) - star Y * Y := by
       rw [cfc_sub (fun z => 3 * (star (z - 1) * (z - 1))) (fun z => star (Complex.log z) * Complex.log z) k
         (hcont _) (hcont _)]
       rw [cfc_const_mul 3 (fun z => star (z - 1) * (z - 1)) k (hcont _)]
       rw [cfc_mul (fun z => star (z - 1)) (fun z => z - 1) k (hcont _) (hcont _)]
       rw [cfc_mul (fun z => star (Complex.log z)) Complex.log k (hcont _) (hcont _)]
       rw [cfc_star (fun z => z - 1) k, cfc_star Complex.log k]
       rw [cfc_sub (fun z => z) (fun _ => 1) k (hcont _) (hcont _), cfc_id' ℂ k, cfc_const_one ℂ k]
     set G := cfc (fun z => ((Real.sqrt (3 * ‖z - 1‖ ^ 2 - ‖Complex.log z‖ ^ 2) : ℝ) : ℂ)) k with hG
     have hFG : cfc (fun z => 3 * (star (z - 1) * (z - 1)) - star (Complex.log z) * Complex.log z) k =
         star G * G := by
       rw [hG, ← cfc_star, ← cfc_mul _ _ k (hcont _) (hcont _)]
       refine cfc_congr fun z hz => ?_
       have hsc := norm_log_sq_le_unit_circle z (hcirc z hz)
       have hnn : 0 ≤ 3 * ‖z - 1‖ ^ 2 - ‖Complex.log z‖ ^ 2 := by linarith
       simp only [Complex.star_def, Complex.conj_ofReal]
       rw [Complex.conj_mul', Complex.conj_mul', ← Complex.ofReal_mul, Real.mul_self_sqrt hnn]
       push_cast
       ring
     have htr := congrArg Matrix.trace (hF.symm.trans hFG)
     rw [Matrix.trace_sub, Matrix.trace_smul, ← frobenius_eq_trace, ← frobenius_eq_trace, ← frobenius_eq_trace,
       smul_eq_mul] at htr
     have h4 : (3 : ℂ) * (hs (k - 1) : ℂ) - (hs Y : ℂ) = ((3 * hs (k - 1) - hs Y : ℝ) : ℂ) := by push_cast; ring
     rw [h4] at htr
     have h5 := Complex.ofReal_injective htr
     have h6 := frobenius_nonneg_matrix G
     linarith)

/- English proof (translation)
Introduce `_ ε k hk` and use `compact_exists_log_bounded ε k hk`.
-/
theorem compact_exponential_surjective : KExp := fun _ ε k hk => compact_exists_log_bounded ε k hk

/- English proof (translation)
Introduce `n ε g hg`. Take `⟨k, X, hk, hX, rfl⟩` from `(polar_decomposition_holds n ε).1 g hg`. Take `⟨Z, hZ, hZk, -⟩` from `h n ε k hk`. Conclude with `⟨Z, X, hZ, hX, by rw [hZk]⟩`.
-/
theorem genExp_of (h : KExp) : GenExp := by
  intro n ε g hg
  obtain ⟨k, X, hk, hX, rfl⟩ := (polar_decomposition_holds n ε).1 g hg
  obtain ⟨Z, hZ, hZk, -⟩ := h n ε k hk
  exact ⟨Z, X, hZ, hX, by rw [hZk]⟩

end Formalism.REAL
