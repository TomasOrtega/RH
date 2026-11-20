import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ActAApply
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CompletedStandardAdelicLatticePropertiesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeOfAdelicPointStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpaceSelfDualPairAtMostLineStatement

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil.RatTransl

variable {D : D7} {T : Tor D} {N N' : ℕ}

/- English proof (translation)
Simplify using `only [Hf, Pi.add_apply, add_mul, Finset.sum_add_distrib, add_div]`.
-/
theorem hf_add_left (x y z : VC D N N') : Hf D T (x + y) z = Hf D T x z + Hf D T y z := by
  simp only [Hf, Pi.add_apply, add_mul, Finset.sum_add_distrib, add_div]

/- English proof (translation)
Simplify using `only [Hf, Pi.smul_apply, nsmul_eq_mul, map_mul, map_natCast]`. Use `congr 1`. Use `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring` and prove the remaining obligations.
-/
theorem hf_nsmul (n : ℕ) (x z : VC D N N') : Hf D T (n • x) z = Hf D T x (n • z) := by
  simp only [Hf, Pi.smul_apply, nsmul_eq_mul, map_mul, map_natCast]
  congr 1
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => by ring

/- English proof (translation)
Simplify using `only [Hf, map_div₀, map_sum, map_mul, Complex.conj_conj, Complex.conj_ofReal]`. Use `congr 1`. Use `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring` and prove the remaining obligations.
-/
theorem hf_conj (x z : VC D N N') : Hf D T z x = (starRingEnd ℂ) (Hf D T x z) := by
  simp only [Hf, map_div₀, map_sum, map_mul, Complex.conj_conj, Complex.conj_ofReal]
  congr 1
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => by ring

/- English proof (translation)
Unfold `Hf`. Use `fun_prop`.
-/
theorem differentiable_hf (x : VC D N N') : Differentiable ℂ (fun z => Hf D T z x) := by
  unfold Hf
  fun_prop

/- English proof (translation)
Establish `h` using `differentiable_hf (T := T) x`. Unfold `Wd U`. Use `fun_prop`.
-/
theorem differentiable_wd (x : VC D N N') {G : VC D N N' → ℂ} (hG : Differentiable ℂ G) :
    Differentiable ℂ (Wd D T x G) := by
  have h := differentiable_hf (T := T) x
  unfold Wd U
  fun_prop

/- English proof (translation)
Establish `h1` using `congrFun hx (w + z)`. Establish `h2 : Hf D T x z = Hf D T z x + 2 * Complex.I * m`. Rewrite using `[hf_conj x z]`. Apply the tactic sequence `apply Complex.ext <;> simp [hm]`. Expand and normalize the polynomial expressions, which then agree.

Establish `h3 : Complex.exp (-(Real.pi : ℂ) * Hf D T (w + x) z - (Real.pi : ℂ) * Hf D T z z / 2) * Complex.exp (-(Real.pi : ℂ) * Hf D T w x - (Real.pi : ℂ) * Hf D T x x / 2) = Complex.exp (-(Real.pi : ℂ) * Hf D T (w + z) x - (Real.pi : ℂ) * Hf D T x x / 2) * Complex.exp (-(Real.pi : ℂ) * Hf …`. Rewrite using `[← Complex.exp_add, ← Complex.exp_add, Complex.exp_eq_exp_iff_exists_int]`. Use `⟨-m, ?_⟩` and prove the remaining obligations. Rewrite using `[hf_add_left, hf_add_left, h2]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Simplify using `only [Wd, U] at h1 ⊢`. Rewrite using `[← h1, add_right_comm w x z]`. Take the linear combination `(wdPh D T x * wdPh D T z * G (w + z + x)) * h3`.
-/
theorem wd_wd_of_int {x z : VC D N N'} {G : VC D N N' → ℂ} (hx : Wd D T x G = G) (m : ℤ)
    (hm : (Hf D T x z).im = m) (w : VC D N N') : Wd D T x (Wd D T z G) w = Wd D T z G w := by
  have h1 := congrFun hx (w + z)
  have h2 : Hf D T x z = Hf D T z x + 2 * Complex.I * m := by
    rw [hf_conj x z]
    apply Complex.ext <;> simp [hm]
    ring
  have h3 : Complex.exp (-(Real.pi : ℂ) * Hf D T (w + x) z - (Real.pi : ℂ) * Hf D T z z / 2) *
      Complex.exp (-(Real.pi : ℂ) * Hf D T w x - (Real.pi : ℂ) * Hf D T x x / 2) =
      Complex.exp (-(Real.pi : ℂ) * Hf D T (w + z) x - (Real.pi : ℂ) * Hf D T x x / 2) *
      Complex.exp (-(Real.pi : ℂ) * Hf D T w z - (Real.pi : ℂ) * Hf D T z z / 2) := by
    rw [← Complex.exp_add, ← Complex.exp_add, Complex.exp_eq_exp_iff_exists_int]
    refine ⟨-m, ?_⟩
    rw [hf_add_left, hf_add_left, h2]
    push_cast
    ring
  simp only [Wd, U] at h1 ⊢
  rw [← h1, add_right_comm w x z]
  linear_combination (wdPh D T x * wdPh D T z * G (w + z + x)) * h3

/- English proof (translation)
Take `⟨Lt, h1, h2, -⟩` from `GlobalTheory.T.Lt_eq_iff_inv_mul_mem_intG_and_transport D N`. Conclude with `h2 ▸ (h1 1).2`.
-/
theorem sd_std (D : D7) (N : ℕ) : SD D (stdL D N) := by
  obtain ⟨Lt, h1, h2, -⟩ := GlobalTheory.T.Lt_eq_iff_inv_mul_mem_intG_and_transport D N
  exact h2 ▸ (h1 1).2

/- English proof (translation)
Use function extensionality and compare the values at `τ i j`. Simplify using `only [pt, embV, tor0, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul, map_mul, map_natCast]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pt_nsmul (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (n : ℕ) (z : Matrix (Fin N') (Fin N) D.host.E) :
    pt D (tor0 D cc δ) δ (n • z) = n • pt D (tor0 D cc δ) δ z := by
  funext τ i j
  simp only [pt, embV, tor0, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul, map_mul, map_natCast]
  ring

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Matrix.map_apply, Matrix.smul_apply, map_nsmul]`.
-/
theorem map_inc_nsmul (n : ℕ) (z : Matrix (Fin N') (Fin N) D.host.E) :
    (n • z).map (inc D) = n • z.map (inc D) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, map_nsmul]

/- English proof (translation)
Introduce and unpack `D hg cc δ hc N N' z F ⟨hd, m, hm, hF⟩`. Take `⟨h1, -, -, h4, -⟩` from `GlobalTheory.T.completedStandardAdelicLattice_properties D hg cc δ hc N N'`. Take `⟨-, -, hI, -⟩` from `GlobalTheory.T.theta_space_selfDual_pair_at_most_line D hg cc δ hc N N' (La0 D (tor0 D cc δ) N N') (Or.inr ⟨_, _, sd_std D _, sd_std D _, rfl⟩)`. Take `⟨n, hn, hz⟩` from `h4 (z.map (inc D))`. Rewrite `hz` using `[← map_inc_nsmul, h1, pt_nsmul]`.

Use `⟨differentiable_wd _ hd, n * m, Nat.mul_pos hn hm, fun x hx => ?_⟩` and prove the remaining obligations. Take `⟨k, hk⟩` from `hI _ (AddSubgroup.nsmul_mem _ hx m) _ hz`. Establish `h0 : Wd D (tor0 D cc δ) ((n * m) • x) F = F`. Rewrite using `[mul_comm, mul_smul]`. Conclude with `hF _ (AddSubgroup.nsmul_mem _ hx n)`.

Use function extensionality and compare the values at `w`. Conclude with `wd_wd_of_int h0 k (by rw [mul_smul, hf_nsmul, hk]) w`.
-/
theorem wd_mem_TT : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ) (z : Matrix (Fin N') (Fin N) D.host.E), ∀ F ∈ TT D (tor0 D cc δ) N N', Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) F ∈ TT D (tor0 D cc δ) N N' := by
  rintro D hg cc δ hc N N' z F ⟨hd, m, hm, hF⟩
  obtain ⟨h1, -, -, h4, -⟩ := GlobalTheory.T.completedStandardAdelicLattice_properties D hg cc δ hc N N'
  obtain ⟨-, -, hI, -⟩ := GlobalTheory.T.theta_space_selfDual_pair_at_most_line D hg cc δ hc N N' (La0 D (tor0 D cc δ) N N')
    (Or.inr ⟨_, _, sd_std D _, sd_std D _, rfl⟩)
  obtain ⟨n, hn, hz⟩ := h4 (z.map (inc D))
  rw [← map_inc_nsmul, h1, pt_nsmul] at hz
  refine ⟨differentiable_wd _ hd, n * m, Nat.mul_pos hn hm, fun x hx => ?_⟩
  obtain ⟨k, hk⟩ := hI _ (AddSubgroup.nsmul_mem _ hx m) _ hz
  have h0 : Wd D (tor0 D cc δ) ((n * m) • x) F = F := by
    rw [mul_comm, mul_smul]
    exact hF _ (AddSubgroup.nsmul_mem _ hx n)
  funext w
  exact wd_wd_of_int h0 k (by rw [mul_smul, hf_nsmul, hk]) w

end GlobalTheory.FinWeil.RatTransl
