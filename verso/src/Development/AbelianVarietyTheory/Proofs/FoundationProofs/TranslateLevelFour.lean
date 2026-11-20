import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableComb
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPeriodPairIdealCurveLatticeStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoordsAlongOrthonormalRealSubfieldBasis
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpaceSelfDualPairAtMostLine

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.GalTheta
open scoped BigOperators

namespace GlobalTheory.OddThetaTranslate

/- English proof (translation)
Simplify using `only [coordB, Pi.add_apply, add_mul, Finset.sum_add_distrib]`.
-/
theorem coordB_add (D : D7) (T : Tor D) {N N' r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (k : Fin r)
    (z x : VC D N N') : coordB D T b k (z + x) = coordB D T b k z + coordB D T b k x := by
  simp only [coordB, Pi.add_apply, add_mul, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `only [coordB, Pi.smul_apply, nsmul_eq_mul, mul_assoc, Finset.mul_sum]`.
-/
theorem coordB_nsmul (D : D7) (T : Tor D) {N N' r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (k : Fin r)
    (n : ℕ) (z : VC D N N') : coordB D T b k (n • z) = n * coordB D T b k z := by
  simp only [coordB, Pi.smul_apply, nsmul_eq_mul, mul_assoc, Finset.mul_sum]

/- English proof (translation)
Simplify using `[coordB]`.
-/
theorem coordB_zero (D : D7) (T : Tor D) {N N' r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (k : Fin r) :
    coordB D T b k (0 : VC D N N') = 0 := by
  simp [coordB]

/- English proof (translation)
Unfold `U U1 pullB Hf`. Rewrite using `[Finset.prod_mul_distrib, ← Complex.exp_sum, hP, hP]`. Simplify using `only [coordB_add]`. Use `congr 2`. Rewrite using `[Finset.sum_div, Finset.sum_div, Finset.mul_sum, Finset.mul_sum, Finset.sum_div, ← Finset.sum_sub_distrib]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem U_pullB (D : D7) (T : Tor D) {N N' r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (g : ℂ → ℂ)
    (hP : ∀ z w : VC D N N', ∑ τ, ∑ i, ∑ j, z τ i j * (starRingEnd ℂ) (w τ i j) =
      ∑ k, coordB D T b k z * (starRingEnd ℂ) (coordB D T b k w)) (x z : VC D N N') :
    U D T x (pullB D T b g) z = ∏ k, U1 T.abelian₂ (coordB D T b k x) g (coordB D T b k z) := by
  unfold U U1 pullB Hf
  rw [Finset.prod_mul_distrib, ← Complex.exp_sum, hP, hP]
  simp only [coordB_add]
  congr 2
  rw [Finset.sum_div, Finset.sum_div, Finset.mul_sum, Finset.mul_sum, Finset.sum_div, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/- English proof (translation)
Rewrite using `[AddSubgroup.mem_closure_pair]`. Introduce and unpack `⟨m, n, hmn⟩`. Establish `h0` using `(LinearIndependent.pair_iff.1 h) (2 * (m : ℝ) - 1) (2 * (n : ℝ)) (by`. Simplify using `only [zsmul_eq_mul] at hmn`. Simplify using `only [Complex.real_smul]`.

Use `push_cast`. Take the linear combination `2 * hmn)`. Establish `h1 : (2 * m - 1 : ℤ) = 0` using `by exact_mod_cast h0.1`. Use linear arithmetic over natural numbers and integers.
-/
theorem half_not_mem {w₁ w₂ : ℂ} (h : LinearIndependent ℝ ![w₁, w₂]) :
    w₁ / 2 ∉ AddSubgroup.closure ({w₁, w₂} : Set ℂ) := by
  rw [AddSubgroup.mem_closure_pair]
  rintro ⟨m, n, hmn⟩
  have h0 := (LinearIndependent.pair_iff.1 h) (2 * (m : ℝ) - 1) (2 * (n : ℝ)) (by
    simp only [zsmul_eq_mul] at hmn
    simp only [Complex.real_smul]
    push_cast
    linear_combination 2 * hmn)
  have h1 : (2 * m - 1 : ℤ) = 0 := by exact_mod_cast h0.1
  omega

/- English proof (translation)
Rewrite using `[ha, ← Complex.exp_int_mul_two_pi_mul_I (-m)]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exp_neg_pi_I_even (m : ℤ) (a : ℝ) (ha : a = 2 * m) :
    Complex.exp (-(Real.pi : ℂ) * Complex.I * (a : ℂ)) = 1 := by
  rw [ha, ← Complex.exp_int_mul_two_pi_mul_I (-m)]
  congr 1
  push_cast
  ring

/- English proof (translation)
Introduce `D hG cc δ hC N N' r b hb`. Choose the witnesses or unpack the hypotheses as in `⟨w₁, w₂, hli, hΛ⟩ : ∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ lamOf D cc δ = AddSubgroup.closure {w₁, w₂} := by`. Take `⟨L, hL⟩` from `GlobalTheory.T.exists_periodPair_idealCurveLattice D cc δ hC`. Use `⟨L.ω₁, L.ω₂, L.indep, ?_⟩` and prove the remaining obligations. Use extensionality with `z`.

Rewrite using `[hL, PeriodPair.mem_lattice, AddSubgroup.mem_closure_pair]`. Simplify using `only [zsmul_eq_mul]`. Take `⟨-, -, hP, hL, hbij⟩` from `GlobalTheory.OnCoord.coords_of_orthonormal_basis D hG cc δ N N' r b hb`. Take `⟨⟨hd, -, -, hU⟩, hz, -⟩` from `GlobalTheory.OddTheta.sgStar_laws (lamOf D cc δ) ⟨w₁, w₂, hli, hΛ⟩`. Take `⟨-, -, hint, -⟩` from `GlobalTheory.ThetaLine.theta_line D hG cc δ hC N N' (LaB D (tor0 D cc δ) b) (Or.inl ⟨r, b, hb, rfl⟩)`.

Establish `hw : w₁ ∈ lamOf D cc δ` using `by rw [hΛ]; exact AddSubgroup.subset_closure (by simp)`. Establish `hw2 : w₁ / 2 ∉ lamOf D cc δ` using `by rw [hΛ]; exact half_not_mem hli`. Take `⟨t, ht⟩` from `hbij.2 (fun _ => w₁ / 2)`. Establish `ht' : ∀ k, coordB D (tor0 D cc δ) b k t = w₁ / 2` using `fun k => congrFun ht k`. Establish `h2t : 2 • t ∈ LaB D (tor0 D cc δ) b`.

Rewrite using `[hL]`. Introduce `k`. Rewrite using `[coordB_nsmul, ht']`. Establish `: ((2 : ℕ) : ℂ) * (w₁ / 2) = w₁` using `by push_cast; ring`. Rewrite using `[this]`.

Conclude with `hw`. Use `⟨?_, t, h2t, ?_, ?_⟩` and prove the remaining obligations. Establish `hc : ∀ k, Differentiable ℂ (coordB D (tor0 D cc δ) b k)`. Introduce `k`. Unfold `coordB`.

Use `fun_prop`. Unfold `pullB`. Use `fun_prop`. Simplify using `only [U, zero_add, pullB, ht']`. Use `mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => ?_) (Complex.exp_ne_zero _)` and prove the remaining obligations.

Conclude with `fun h => hw2 ((hz _).1 h)`. Introduce `ω hω`. Establish `hfix : U D (tor0 D cc δ) (4 • ω) (pullB D (tor0 D cc δ) b (sgStar (lamOf D cc δ))) = pullB D (tor0 D cc δ) b (sgStar (lamOf D cc δ))`. Use function extensionality and compare the values at `z`. Rewrite using `[U_pullB D _ b _ hP]`.

Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Establish `hk` using `(hL ω).1 hω k`. Establish `h4 : coordB D (tor0 D cc δ) b k (4 • ω) ∈ lamOf D cc δ` using `(hL _).1 (AddSubgroup.nsmul_mem _ hω 4) k`. Establish `h2 : coordB D (tor0 D cc δ) b k (4 • ω) / 2 ∈ lamOf D cc δ`. Establish `: coordB D (tor0 D cc δ) b k (4 • ω) / 2 = coordB D (tor0 D cc δ) b k ω + coordB D (tor0 D cc δ) b k ω`.

Rewrite using `[coordB_nsmul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `add_mem hk hk`.

Use `hU _ h4 (coordB D (tor0 D cc δ) b k z)` as an intermediate fact. Rewrite `this` using `[if_pos h2, one_mul]`. Conclude with `this`. Take `⟨m, hm⟩` from `hint ω hω _ h2t`. Establish `ha : (Hf D (tor0 D cc δ) (4 • ω) t).im = 2 * m`.

Rewrite `hm` using `[Hf_nsmul_right]`. Rewrite using `[Hf_nsmul_left, ← hm]`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Establish `hb' : (Hf D (tor0 D cc δ) t (4 • ω)).im = 2 * ((-m : ℤ) : ℝ)`.

Rewrite using `[Hf_im_swap, ha]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use function extensionality and compare the values at `z`. Establish `e` using `U_U D (tor0 D cc δ) t (4 • ω) (pullB D (tor0 D cc δ) b (sgStar (lamOf D cc δ))) z`.

Rewrite `e` using `[hfix, exp_neg_pi_I_even _ _ hb', one_mul]`. Rewrite using `[U_U, exp_neg_pi_I_even _ _ ha, one_mul, e, add_comm]`.
-/
theorem translate_level_four : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), OnB D b → Differentiable ℂ (pullB D (tor0 D cc δ) b (sgStar (lamOf D cc δ))) ∧ ∃ t : VC D N N', 2 • t ∈ LaB D (tor0 D cc δ) b ∧ U D (tor0 D cc δ) t (pullB D (tor0 D cc δ) b (sgStar (lamOf D cc δ))) 0 ≠ 0 ∧ ∀ ω ∈ LaB D (tor0 D cc δ) b, U D (tor0 D cc δ) (4 • ω) (U D (tor0 D cc δ) t (pullB D (tor0 D cc δ) b (sgStar (lamOf D cc δ)))) = U D (tor0 D cc δ) t (pullB D (tor0 D cc δ) b (sgStar (lamOf D cc δ))) := by
  intro D hG cc δ hC N N' r b hb
  obtain ⟨w₁, w₂, hli, hΛ⟩ : ∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧
      lamOf D cc δ = AddSubgroup.closure {w₁, w₂} := by
    obtain ⟨L, hL⟩ := GlobalTheory.T.exists_periodPair_idealCurveLattice D cc δ hC
    refine ⟨L.ω₁, L.ω₂, L.indep, ?_⟩
    ext z
    rw [hL, PeriodPair.mem_lattice, AddSubgroup.mem_closure_pair]
    simp only [zsmul_eq_mul]
  obtain ⟨-, -, hP, hL, hbij⟩ := GlobalTheory.OnCoord.coords_of_orthonormal_basis D hG cc δ N N' r b hb
  obtain ⟨⟨hd, -, -, hU⟩, hz, -⟩ := GlobalTheory.OddTheta.sgStar_laws (lamOf D cc δ) ⟨w₁, w₂, hli, hΛ⟩
  obtain ⟨-, -, hint, -⟩ := GlobalTheory.ThetaLine.theta_line D hG cc δ hC N N' (LaB D (tor0 D cc δ) b)
    (Or.inl ⟨r, b, hb, rfl⟩)
  have hw : w₁ ∈ lamOf D cc δ := by rw [hΛ]; exact AddSubgroup.subset_closure (by simp)
  have hw2 : w₁ / 2 ∉ lamOf D cc δ := by rw [hΛ]; exact half_not_mem hli
  obtain ⟨t, ht⟩ := hbij.2 (fun _ => w₁ / 2)
  have ht' : ∀ k, coordB D (tor0 D cc δ) b k t = w₁ / 2 := fun k => congrFun ht k
  have h2t : 2 • t ∈ LaB D (tor0 D cc δ) b := by
    rw [hL]
    intro k
    rw [coordB_nsmul, ht']
    have : ((2 : ℕ) : ℂ) * (w₁ / 2) = w₁ := by push_cast; ring
    rw [this]; exact hw
  refine ⟨?_, t, h2t, ?_, ?_⟩
  · have hc : ∀ k, Differentiable ℂ (coordB D (tor0 D cc δ) b k) := by
      intro k
      unfold coordB
      fun_prop
    unfold pullB
    fun_prop
  · simp only [U, zero_add, pullB, ht']
    refine mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => ?_) (Complex.exp_ne_zero _)
    exact fun h => hw2 ((hz _).1 h)
  · intro ω hω
    have hfix : U D (tor0 D cc δ) (4 • ω) (pullB D (tor0 D cc δ) b (sgStar (lamOf D cc δ))) =
        pullB D (tor0 D cc δ) b (sgStar (lamOf D cc δ)) := by
      funext z
      rw [U_pullB D _ b _ hP]
      refine Finset.prod_congr rfl fun k _ => ?_
      have hk := (hL ω).1 hω k
      have h4 : coordB D (tor0 D cc δ) b k (4 • ω) ∈ lamOf D cc δ :=
        (hL _).1 (AddSubgroup.nsmul_mem _ hω 4) k
      have h2 : coordB D (tor0 D cc δ) b k (4 • ω) / 2 ∈ lamOf D cc δ := by
        have : coordB D (tor0 D cc δ) b k (4 • ω) / 2 =
            coordB D (tor0 D cc δ) b k ω + coordB D (tor0 D cc δ) b k ω := by
          rw [coordB_nsmul]; push_cast; ring
        rw [this]; exact add_mem hk hk
      have := hU _ h4 (coordB D (tor0 D cc δ) b k z)
      rw [if_pos h2, one_mul] at this
      exact this
    obtain ⟨m, hm⟩ := hint ω hω _ h2t
    have ha : (Hf D (tor0 D cc δ) (4 • ω) t).im = 2 * m := by
      rw [Hf_nsmul_right] at hm
      rw [Hf_nsmul_left, ← hm]
      simp
      ring
    have hb' : (Hf D (tor0 D cc δ) t (4 • ω)).im = 2 * ((-m : ℤ) : ℝ) := by
      rw [Hf_im_swap, ha]; push_cast; ring
    funext z
    have e := U_U D (tor0 D cc δ) t (4 • ω) (pullB D (tor0 D cc δ) b (sgStar (lamOf D cc δ))) z
    rw [hfix, exp_neg_pi_I_even _ _ hb', one_mul] at e
    rw [U_U, exp_neg_pi_I_even _ _ ha, one_mul, e, add_comm]

end GlobalTheory.OddThetaTranslate
