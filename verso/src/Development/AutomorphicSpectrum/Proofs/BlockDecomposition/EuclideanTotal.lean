import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FockTranslateSchwartzMajorant

noncomputable section
open MeasureTheory Filter Topology
open scoped NNReal ENNReal ComplexConjugate

namespace GlobalTheory.CompanionTheory.ThTot.EucT

variable {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  [MeasurableSpace Z] [BorelSpace Z]

/- English proof (translation)
Establish `h1 : (1 + r) ^ n / (n.factorial : ℝ) ≤ Real.exp (1 + r)` using `Real.pow_div_factorial_le_exp _ (by positivity) n`. Establish `h1' : (1 + r) ^ n ≤ (n.factorial : ℝ) * Real.exp (1 + r)`. Rewrite `h1` using `[div_le_iff₀ (by positivity)]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h2 : (1 + r) + (b * r - a * r ^ 2) ≤ 1 + (1 + b) ^ 2 / (4 * a)`.

Establish `e : (1 + b) ^ 2 / (4 * a) - ((1 + b) * r - a * r ^ 2) = (1 + b - 2 * a * r) ^ 2 / (4 * a)`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `h3 : 0 ≤ (1 + b - 2 * a * r) ^ 2 / (4 * a)` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities.

Establish `hp : 0 < (1 + r) ^ n` using `by positivity`. Rewrite using `[Real.rpow_neg (by positivity), Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ hp]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Real.exp_add (1 + r) (b * r - a * r ^ 2)]`. Expand and normalize the polynomial expressions, which then agree.

Use `_ ≤ _ := by gcongr`.
-/
lemma exp_bound (a b : ℝ) (ha : 0 < a) (n : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    Real.exp (b * r - a * r ^ 2) ≤
      ((n.factorial : ℝ) * Real.exp (1 + (1 + b) ^ 2 / (4 * a))) * (1 + r) ^ (-(n : ℝ)) := by
  have h1 : (1 + r) ^ n / (n.factorial : ℝ) ≤ Real.exp (1 + r) :=
    Real.pow_div_factorial_le_exp _ (by positivity) n
  have h1' : (1 + r) ^ n ≤ (n.factorial : ℝ) * Real.exp (1 + r) := by
    rw [div_le_iff₀ (by positivity)] at h1
    linarith
  have h2 : (1 + r) + (b * r - a * r ^ 2) ≤ 1 + (1 + b) ^ 2 / (4 * a) := by
    have e : (1 + b) ^ 2 / (4 * a) - ((1 + b) * r - a * r ^ 2) = (1 + b - 2 * a * r) ^ 2 / (4 * a) := by
      field_simp
      ring
    have h3 : 0 ≤ (1 + b - 2 * a * r) ^ 2 / (4 * a) := by positivity
    nlinarith
  have hp : 0 < (1 + r) ^ n := by positivity
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ hp]
  calc Real.exp (b * r - a * r ^ 2) * (1 + r) ^ n
      ≤ Real.exp (b * r - a * r ^ 2) * ((n.factorial : ℝ) * Real.exp (1 + r)) := by gcongr
    _ = (n.factorial : ℝ) * Real.exp ((1 + r) + (b * r - a * r ^ 2)) := by
        rw [Real.exp_add (1 + r) (b * r - a * r ^ 2)]; ring
    _ ≤ _ := by gcongr

/- English proof (translation)
Establish `hn : ((Module.finrank ℝ Z : ℕ) : ℝ) < ((Module.finrank ℝ Z + 1 : ℕ) : ℝ)` using `by push_cast; linarith`. Establish `hi` using `(integrable_one_add_norm (E := Z) (μ := lam) hn).const_mul (((Module.finrank ℝ Z + 1).factorial : ℝ) * Real.exp (1 + (1 + b) ^ 2 / (4 * a)))`. Use `hi.mono' (Continuous.aestronglyMeasurable (by fun_prop)) (Eventually.of_forall fun z => ?_)` and prove the remaining obligations. Rewrite using `[Real.norm_of_nonneg (Real.exp_pos _).le]`. Conclude with `exp_bound a b ha _ _ (norm_nonneg z)`.
-/
lemma integrable_gauss (lam : Measure Z) [lam.IsAddHaarMeasure] (a b : ℝ) (ha : 0 < a) :
    Integrable (fun z : Z => Real.exp (b * ‖z‖ - a * ‖z‖ ^ 2)) lam := by
  have hn : ((Module.finrank ℝ Z : ℕ) : ℝ) < ((Module.finrank ℝ Z + 1 : ℕ) : ℝ) := by
    push_cast; linarith
  have hi := (integrable_one_add_norm (E := Z) (μ := lam) hn).const_mul
    (((Module.finrank ℝ Z + 1).factorial : ℝ) * Real.exp (1 + (1 + b) ^ 2 / (4 * a)))
  refine hi.mono' (Continuous.aestronglyMeasurable (by fun_prop)) (Eventually.of_forall fun z => ?_)
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  exact exp_bound a b ha _ _ (norm_nonneg z)

/- English proof (translation)
Establish `h1` using `Real.pow_div_factorial_le_exp |x| (abs_nonneg x) n`. Rewrite `h1` using `[div_le_iff₀ (by positivity)]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma pow_abs_le (x : ℝ) (n : ℕ) : |x| ^ n ≤ (n.factorial : ℝ) * Real.exp |x| := by
  have h1 := Real.pow_div_factorial_le_exp |x| (abs_nonneg x) n
  rw [div_le_iff₀ (by positivity)] at h1
  linarith

/- English proof (translation)
Simplify using `using ℓ.le_opNorm z`.
-/
lemma abs_le_op (ℓ : Z →L[ℝ] ℝ) (z : Z) : |ℓ z| ≤ ‖ℓ‖ * ‖z‖ := by
  simpa using ℓ.le_opNorm z

/- English proof (translation)
Establish `hi` using `(integrable_gauss lam a ‖ℓ‖ ha).const_mul (K * (n.factorial : ℝ))`. Use `hi.mono' (Continuous.aestronglyMeasurable (by fun_prop)) (Eventually.of_forall fun z => ?_)` and prove the remaining obligations. Rewrite using `[norm_smul, norm_pow, Real.norm_eq_abs]`. Establish `h1 : |ℓ z| ^ n ≤ (n.factorial : ℝ) * Real.exp (‖ℓ‖ * ‖z‖)` using `(pow_abs_le _ n).trans (by gcongr; exact abs_le_op ℓ z)`. Combine the equalities or inequalities in the displayed calculation.

Conclude with `hb z`. Use `_ = K * (n.factorial : ℝ) * Real.exp (‖ℓ‖ * ‖z‖ - a * ‖z‖ ^ 2) := by`. Rewrite using `[sub_eq_add_neg, Real.exp_add, neg_mul_eq_neg_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma int_mom {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (lam : Measure Z) [lam.IsAddHaarMeasure]
    (f : Z → E) (hf : Continuous f) (K a : ℝ) (ha : 0 < a) (hK : 0 ≤ K)
    (hb : ∀ z, ‖f z‖ ≤ K * Real.exp (-a * ‖z‖ ^ 2)) (ℓ : Z →L[ℝ] ℝ) (n : ℕ) :
    Integrable (fun z => (ℓ z) ^ n • f z) lam := by
  have hi := (integrable_gauss lam a ‖ℓ‖ ha).const_mul (K * (n.factorial : ℝ))
  refine hi.mono' (Continuous.aestronglyMeasurable (by fun_prop)) (Eventually.of_forall fun z => ?_)
  rw [norm_smul, norm_pow, Real.norm_eq_abs]
  have h1 : |ℓ z| ^ n ≤ (n.factorial : ℝ) * Real.exp (‖ℓ‖ * ‖z‖) :=
    (pow_abs_le _ n).trans (by gcongr; exact abs_le_op ℓ z)
  calc |ℓ z| ^ n * ‖f z‖ ≤ ((n.factorial : ℝ) * Real.exp (‖ℓ‖ * ‖z‖)) * (K * Real.exp (-a * ‖z‖ ^ 2)) := by
        gcongr
        exact hb z
    _ = K * (n.factorial : ℝ) * Real.exp (‖ℓ‖ * ‖z‖ - a * ‖z‖ ^ 2) := by
        rw [sub_eq_add_neg, Real.exp_add, neg_mul_eq_neg_mul]; ring

/- English proof (translation)
Establish `hre : ∀ k, (fun z => (((c k z).re : ℝ) : ℂ)) ∈ A`. Introduce `k`. Establish `: (fun z => (((c k z).re : ℝ) : ℂ)) = (1 / 2 : ℂ) • ((fun z => c k z) + fun z => conj (c k z))`. Use function extensionality and compare the values at `z`. Simplify using `only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, Complex.add_conj]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `A.smul_mem (A.add_mem (hc k) (hconj k)) _`. Establish `him : ∀ k, (fun z => (((c k z).im : ℝ) : ℂ)) ∈ A`.

Introduce `k`. Establish `: (fun z => (((c k z).im : ℝ) : ℂ)) = (-Complex.I / 2 : ℂ) • ((fun z => c k z) - fun z => conj (c k z))`. Use function extensionality and compare the values at `z`. Simplify using `only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Complex.sub_conj]`. Use `push_cast`.

Use `Complex.I_mul_I` as an intermediate fact. Take the linear combination `(((c k z).im : ℂ)) * this`. Rewrite using `[this]`. Conclude with `A.smul_mem (A.sub_mem (hc k) (hconj k)) _`. Set `T : Z →ₗ[ℝ] (ι → ℂ)` to `LinearMap.pi fun k => (c k : Z →ₗ[ℝ] ℂ)`.

Establish `hT : LinearMap.ker T = ⊥`. Rewrite using `[LinearMap.ker_eq_bot']`. Introduce `z hz`. Conclude with `hsep z fun k => congrFun hz k`. Take `⟨S, hS⟩` from `T.exists_leftInverse_of_injective hT`.

Set `φ : (ι → ℂ) →ₗ[ℝ] ℝ` to `(ℓ : Z →ₗ[ℝ] ℝ) ∘ₗ S`. Establish `hφ : ∀ z, ℓ z = ∑ k, ((c k z).re * φ (Pi.single k 1) + (c k z).im * φ (Pi.single k Complex.I))`. Introduce `z`. Establish `h0 : ℓ z = φ (T z)`. Establish `: S (T z) = z` using `LinearMap.congr_fun hS z`.

Simplify using `[φ, this]`. Establish `h1 : T z = ∑ k, ((c k z).re • (Pi.single k 1 : ι → ℂ) + (c k z).im • (Pi.single k Complex.I : ι → ℂ))`. Use function extensionality and compare the values at `j`. Simplify using `only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, Pi.single_apply]`. Simplify using `[T, Finset.sum_add_distrib, Complex.re_add_im]`.

Rewrite using `[h0, h1, map_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]`. Establish `: (fun z => ((ℓ z : ℝ) : ℂ)) = ∑ k, (((φ (Pi.single k 1) : ℝ) : ℂ) • (fun z => (((c k z).re : ℝ) : ℂ)) + ((φ (Pi.single k Complex.I) : ℝ) : ℂ) • (fun z => (((c k z).im : ℝ) : ℂ)))`. Use function extensionality and compare the values at `z`.

Rewrite using `[hφ z]`. Simplify using `only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]`. Use `push_cast`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this]`. Conclude with `A.sum_mem fun k _ => A.add_mem (A.smul_mem (hre k) _) (A.smul_mem (him k) _)`.
-/
lemma dual_mem {ι : Type} [Fintype ι] (c : ι → Z →L[ℝ] ℂ) (hsep : ∀ z, (∀ k, c k z = 0) → z = 0)
    (A : Subalgebra ℂ (Z → ℂ)) (hc : ∀ k, (fun z => c k z) ∈ A) (hconj : ∀ k, (fun z => conj (c k z)) ∈ A)
    (ℓ : Z →L[ℝ] ℝ) : (fun z => ((ℓ z : ℝ) : ℂ)) ∈ A := by
  classical
  have hre : ∀ k, (fun z => (((c k z).re : ℝ) : ℂ)) ∈ A := by
    intro k
    have : (fun z => (((c k z).re : ℝ) : ℂ)) =
        (1 / 2 : ℂ) • ((fun z => c k z) + fun z => conj (c k z)) := by
      funext z
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, Complex.add_conj]
      push_cast; ring
    rw [this]
    exact A.smul_mem (A.add_mem (hc k) (hconj k)) _
  have him : ∀ k, (fun z => (((c k z).im : ℝ) : ℂ)) ∈ A := by
    intro k
    have : (fun z => (((c k z).im : ℝ) : ℂ)) =
        (-Complex.I / 2 : ℂ) • ((fun z => c k z) - fun z => conj (c k z)) := by
      funext z
      simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Complex.sub_conj]
      push_cast
      have := Complex.I_mul_I
      linear_combination (((c k z).im : ℂ)) * this
    rw [this]
    exact A.smul_mem (A.sub_mem (hc k) (hconj k)) _
  let T : Z →ₗ[ℝ] (ι → ℂ) := LinearMap.pi fun k => (c k : Z →ₗ[ℝ] ℂ)
  have hT : LinearMap.ker T = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro z hz
    exact hsep z fun k => congrFun hz k
  obtain ⟨S, hS⟩ := T.exists_leftInverse_of_injective hT
  let φ : (ι → ℂ) →ₗ[ℝ] ℝ := (ℓ : Z →ₗ[ℝ] ℝ) ∘ₗ S
  have hφ : ∀ z, ℓ z = ∑ k, ((c k z).re * φ (Pi.single k 1) + (c k z).im * φ (Pi.single k Complex.I)) := by
    intro z
    have h0 : ℓ z = φ (T z) := by
      have : S (T z) = z := LinearMap.congr_fun hS z
      simp [φ, this]
    have h1 : T z = ∑ k, ((c k z).re • (Pi.single k 1 : ι → ℂ) + (c k z).im • (Pi.single k Complex.I : ι → ℂ)) := by
      funext j
      simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, Pi.single_apply]
      simp [T, Finset.sum_add_distrib, Complex.re_add_im]
    rw [h0, h1, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  have : (fun z => ((ℓ z : ℝ) : ℂ)) = ∑ k, (((φ (Pi.single k 1) : ℝ) : ℂ) • (fun z => (((c k z).re : ℝ) : ℂ)) +
      ((φ (Pi.single k Complex.I) : ℝ) : ℂ) • (fun z => (((c k z).im : ℝ) : ℂ))) := by
    funext z
    rw [hφ z]
    simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [this]
  exact A.sum_mem fun k _ => A.add_mem (A.smul_mem (hre k) _) (A.smul_mem (him k) _)

/- English proof (translation)
Establish `h : HasSum (fun n : ℕ => x ^ n / (n.factorial : ℂ)) (Complex.exp x)`. Rewrite using `[Complex.exp_eq_exp_ℂ]`. Conclude with `NormedSpace.expSeries_div_hasSum_exp x`. Conclude with `h.tendsto_sum_nat`.
-/
lemma exp_series (x : ℂ) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, x ^ n / (n.factorial : ℂ)) atTop (𝓝 (Complex.exp x)) := by
  have h : HasSum (fun n : ℕ => x ^ n / (n.factorial : ℂ)) (Complex.exp x) := by
    rw [Complex.exp_eq_exp_ℂ]
    exact NormedSpace.expSeries_div_hasSum_exp x
  exact h.tendsto_sum_nat

/- English proof (translation)
Set `F : ℕ → Z → ℂ` to `fun N z => (h z : ℂ) * ∑ n ∈ Finset.range N, ((ℓ z : ℂ) * Complex.I) ^ n / (n.factorial : ℂ)`. Establish `hbi : Integrable (fun z => K * Real.exp (‖ℓ‖ * ‖z‖ - a * ‖z‖ ^ 2)) lam` using `(integrable_gauss lam a ‖ℓ‖ ha).const_mul K`. Establish `hbound : ∀ N z, ‖F N z‖ ≤ K * Real.exp (‖ℓ‖ * ‖z‖ - a * ‖z‖ ^ 2)`. Introduce `N z`. Establish `hs : ‖∑ n ∈ Finset.range N, ((ℓ z : ℂ) * Complex.I) ^ n / (n.factorial : ℂ)‖ ≤ Real.exp (‖ℓ‖ * ‖z‖)`.

Use `(norm_sum_le _ _).trans ?_` and prove the remaining obligations. Establish `: ∀ n ∈ Finset.range N, ‖((ℓ z : ℂ) * Complex.I) ^ n / (n.factorial : ℂ)‖ = |ℓ z| ^ n / (n.factorial : ℝ)`. Introduce `n _`. Simplify using `[norm_pow, Complex.norm_real]`. Rewrite using `[Finset.sum_congr rfl this]`.

Use `(Real.sum_le_exp_of_nonneg (abs_nonneg _) N).trans ?_` and prove the remaining obligations. Use `gcongr`. Conclude with `abs_le_op ℓ z`. Establish `hh : ‖(h z : ℂ)‖ = ‖h z‖` using `by simp`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [F, norm_mul, hh]`. Use `_ ≤ (K * Real.exp (-a * ‖z‖ ^ 2)) * Real.exp (‖ℓ‖ * ‖z‖) := by gcongr`. Conclude with `hb z`. Use `_ = K * Real.exp (‖ℓ‖ * ‖z‖ - a * ‖z‖ ^ 2) := by`. Rewrite using `[sub_eq_add_neg, Real.exp_add, neg_mul_eq_neg_mul]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hzero : ∀ N, ∫ z, F N z ∂lam = 0`. Introduce `N`. Establish `hF : F N = fun z => ∑ n ∈ Finset.range N, (Complex.I ^ n / (n.factorial : ℂ)) * (((ℓ z) ^ n * h z : ℝ) : ℂ)`. Use function extensionality and compare the values at `z`.

Simplify using `only [F, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun n _ => ?_` and prove the remaining obligations. Use `push_cast`. Rewrite using `[mul_pow]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hF, integral_finset_sum]`. Use `Finset.sum_eq_zero fun n _ => ?_` and prove the remaining obligations. Rewrite using `[integral_const_mul, integral_complex_ofReal, hm ℓ n]`. Simplify using the standard rewrite rules. Introduce `n _`.

Use `int_mom lam h hc K a ha hK hb ℓ n` as an intermediate fact. Simplify using `only [smul_eq_mul] at this`. Conclude with `this.ofReal.const_mul _`. Establish `hlim` using `tendsto_integral_of_dominated_convergence (μ := lam) (F := F) (f := fun z => (h z : ℂ) * Complex.exp (ℓ z * Complex.I)) _ (fun N => Continuous.aestronglyMeasurable (by simp only [F]; fun_prop)) hbi (fun N => Eventually.of_forall (hbound N)) (Eventually.of_forall fun z => (exp_ser …`. Simplify using `only [hzero] at hlim`.

Conclude with `(tendsto_nhds_unique hlim tendsto_const_nhds)`.
-/
lemma char_zero (lam : Measure Z) [lam.IsAddHaarMeasure] (h : Z → ℝ) (hc : Continuous h) (K a : ℝ)
    (ha : 0 < a) (hK : 0 ≤ K) (hb : ∀ z, ‖h z‖ ≤ K * Real.exp (-a * ‖z‖ ^ 2))
    (hm : ∀ (ℓ : Z →L[ℝ] ℝ) (n : ℕ), ∫ z, (ℓ z) ^ n * h z ∂lam = 0) (ℓ : Z →L[ℝ] ℝ) :
    ∫ z, (h z : ℂ) * Complex.exp (ℓ z * Complex.I) ∂lam = 0 := by
  let F : ℕ → Z → ℂ := fun N z =>
    (h z : ℂ) * ∑ n ∈ Finset.range N, ((ℓ z : ℂ) * Complex.I) ^ n / (n.factorial : ℂ)
  have hbi : Integrable (fun z => K * Real.exp (‖ℓ‖ * ‖z‖ - a * ‖z‖ ^ 2)) lam :=
    (integrable_gauss lam a ‖ℓ‖ ha).const_mul K
  have hbound : ∀ N z, ‖F N z‖ ≤ K * Real.exp (‖ℓ‖ * ‖z‖ - a * ‖z‖ ^ 2) := by
    intro N z
    have hs : ‖∑ n ∈ Finset.range N, ((ℓ z : ℂ) * Complex.I) ^ n / (n.factorial : ℂ)‖
        ≤ Real.exp (‖ℓ‖ * ‖z‖) := by
      refine (norm_sum_le _ _).trans ?_
      have : ∀ n ∈ Finset.range N, ‖((ℓ z : ℂ) * Complex.I) ^ n / (n.factorial : ℂ)‖
          = |ℓ z| ^ n / (n.factorial : ℝ) := by
        intro n _
        simp [norm_pow, Complex.norm_real]
      rw [Finset.sum_congr rfl this]
      refine (Real.sum_le_exp_of_nonneg (abs_nonneg _) N).trans ?_
      gcongr
      exact abs_le_op ℓ z
    have hh : ‖(h z : ℂ)‖ = ‖h z‖ := by simp
    calc ‖F N z‖ = ‖h z‖ * ‖∑ n ∈ Finset.range N, ((ℓ z : ℂ) * Complex.I) ^ n / (n.factorial : ℂ)‖ := by
          simp only [F, norm_mul, hh]
      _ ≤ (K * Real.exp (-a * ‖z‖ ^ 2)) * Real.exp (‖ℓ‖ * ‖z‖) := by
          gcongr
          exact hb z
      _ = K * Real.exp (‖ℓ‖ * ‖z‖ - a * ‖z‖ ^ 2) := by
          rw [sub_eq_add_neg, Real.exp_add, neg_mul_eq_neg_mul]; ring
  have hzero : ∀ N, ∫ z, F N z ∂lam = 0 := by
    intro N
    have hF : F N = fun z => ∑ n ∈ Finset.range N,
        (Complex.I ^ n / (n.factorial : ℂ)) * (((ℓ z) ^ n * h z : ℝ) : ℂ) := by
      funext z
      simp only [F, Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      push_cast
      rw [mul_pow]
      ring
    rw [hF, integral_finset_sum]
    · refine Finset.sum_eq_zero fun n _ => ?_
      rw [integral_const_mul, integral_complex_ofReal, hm ℓ n]
      simp
    · intro n _
      have := int_mom lam h hc K a ha hK hb ℓ n
      simp only [smul_eq_mul] at this
      exact this.ofReal.const_mul _
  have hlim := tendsto_integral_of_dominated_convergence (μ := lam) (F := F)
    (f := fun z => (h z : ℂ) * Complex.exp (ℓ z * Complex.I)) _
    (fun N => Continuous.aestronglyMeasurable (by simp only [F]; fun_prop)) hbi
    (fun N => Eventually.of_forall (hbound N))
    (Eventually.of_forall fun z => (exp_series _).const_mul _)
  simp only [hzero] at hlim
  exact (tendsto_nhds_unique hlim tendsto_const_nhds)

/- English proof (translation)
Use `haveI : ProperSpace Z := FiniteDimensional.proper ℝ Z`. Establish `hi : Integrable h lam`. Use `int_mom lam h hc K a ha hK hb 0 0` as an intermediate fact. Simplify using `using this`. Set `fp : Z → ℝ≥0` to `fun z => Real.toNNReal (h z)`.

Set `fm : Z → ℝ≥0` to `fun z => Real.toNNReal (-h z)`. Establish `cfp : Continuous fp` using `continuous_real_toNNReal.comp hc`. Establish `cfm : Continuous fm` using `continuous_real_toNNReal.comp hc.neg`. Use `haveI : IsFiniteMeasure (lam.withDensity fun z => (fp z : ℝ≥0∞)) := isFiniteMeasure_withDensity_ofReal hi.2`. Use `haveI : IsFiniteMeasure (lam.withDensity fun z => (fm z : ℝ≥0∞)) := isFiniteMeasure_withDensity_ofReal hi.neg.2`.

Establish `key : ∀ (f : Z → ℝ≥0), Continuous f → (∀ z, (f z : ℝ) ≤ ‖h z‖) → ∀ ℓ : Z →L[ℝ] ℝ, Integrable (fun z => f z • Complex.exp (ℓ z * Complex.I)) lam`. Introduce `f cf hf ℓ`. Use `hi.norm.mono' (Continuous.aestronglyMeasurable ?_) (Eventually.of_forall fun z => ?_)` and prove the remaining obligations. Establish `: (fun z => f z • Complex.exp (ℓ z * Complex.I)) = fun z => ((f z : ℝ) : ℂ) * Complex.exp (ℓ z * Complex.I)`. Use function extensionality and compare the values at `z`.

Rewrite using `[NNReal.smul_def, Complex.real_smul]`. Rewrite using `[this]`. Establish `cf' : Continuous fun z => (f z : ℝ)` using `NNReal.continuous_coe.comp cf`. Use `fun_prop`. Rewrite using `[NNReal.smul_def, norm_smul, Complex.norm_exp_ofReal_mul_I, mul_one]`.

Simplify using `using hf z`. Establish `hchar : charFunDual (lam.withDensity fun z => (fp z : ℝ≥0∞)) = charFunDual (lam.withDensity fun z => (fm z : ℝ≥0∞))`. Use function extensionality and compare the values at `ℓ`. Rewrite using `[charFunDual_apply, charFunDual_apply, integral_withDensity_eq_integral_smul cfp.measurable, integral_withDensity_eq_integral_smul cfm.measurable, ← sub_eq_zero, ← integral_sub (key fp cfp (fun z => ?_) ℓ) (key fm cfm (fun z => ?_) ℓ)]`. Rewrite using `[← char_zero lam h hc K a ha hK hb hm ℓ]`.

Use `integral_congr_ae (Eventually.of_forall fun z => ?_)` and prove the remaining obligations. Simplify using `only [fp, fm, NNReal.smul_def, Complex.real_smul, Real.coe_toNNReal']`. Rewrite using `[← sub_mul, ← Complex.ofReal_sub, max_zero_sub_eq_self]`. Simplify using `only [fp, Real.coe_toNNReal', Real.norm_eq_abs]`. Conclude with `max_le (le_abs_self _) (abs_nonneg _)`.

Simplify using `only [fm, Real.coe_toNNReal', Real.norm_eq_abs]`. Conclude with `max_le (neg_le_abs _) (abs_nonneg _)`. Establish `heq` using `Measure.ext_of_charFunDual hchar`. Establish `hae` using `(withDensity_eq_iff_of_sigmaFinite (ENNReal.continuous_coe.comp cfp).measurable.aemeasurable (ENNReal.continuous_coe.comp cfm).measurable.aemeasurable).1 heq`. Establish `hall` using `(Continuous.ae_eq_iff_eq lam (ENNReal.continuous_coe.comp cfp) (ENNReal.continuous_coe.comp cfm)).1 hae`.

Establish `h1 : fp z = fm z` using `ENNReal.coe_injective (congrFun hall z)`. Establish `h2 : ((fp z : ℝ≥0) : ℝ) = fm z` using `congrArg _ h1`. Simplify using `only [fp, fm, Real.coe_toNNReal'] at h2`. Use `max_zero_sub_eq_self (h z)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma real_zero (lam : Measure Z) [lam.IsAddHaarMeasure] (h : Z → ℝ) (hc : Continuous h) (K a : ℝ)
    (ha : 0 < a) (hK : 0 ≤ K) (hb : ∀ z, ‖h z‖ ≤ K * Real.exp (-a * ‖z‖ ^ 2))
    (hm : ∀ (ℓ : Z →L[ℝ] ℝ) (n : ℕ), ∫ z, (ℓ z) ^ n * h z ∂lam = 0) (z : Z) : h z = 0 := by
  haveI : ProperSpace Z := FiniteDimensional.proper ℝ Z
  have hi : Integrable h lam := by
    have := int_mom lam h hc K a ha hK hb 0 0
    simpa using this
  let fp : Z → ℝ≥0 := fun z => Real.toNNReal (h z)
  let fm : Z → ℝ≥0 := fun z => Real.toNNReal (-h z)
  have cfp : Continuous fp := continuous_real_toNNReal.comp hc
  have cfm : Continuous fm := continuous_real_toNNReal.comp hc.neg
  haveI : IsFiniteMeasure (lam.withDensity fun z => (fp z : ℝ≥0∞)) :=
    isFiniteMeasure_withDensity_ofReal hi.2
  haveI : IsFiniteMeasure (lam.withDensity fun z => (fm z : ℝ≥0∞)) :=
    isFiniteMeasure_withDensity_ofReal hi.neg.2
  have key : ∀ (f : Z → ℝ≥0), Continuous f → (∀ z, (f z : ℝ) ≤ ‖h z‖) → ∀ ℓ : Z →L[ℝ] ℝ,
      Integrable (fun z => f z • Complex.exp (ℓ z * Complex.I)) lam := by
    intro f cf hf ℓ
    refine hi.norm.mono' (Continuous.aestronglyMeasurable ?_) (Eventually.of_forall fun z => ?_)
    · have : (fun z => f z • Complex.exp (ℓ z * Complex.I)) =
          fun z => ((f z : ℝ) : ℂ) * Complex.exp (ℓ z * Complex.I) := by
        funext z
        rw [NNReal.smul_def, Complex.real_smul]
      rw [this]
      have cf' : Continuous fun z => (f z : ℝ) := NNReal.continuous_coe.comp cf
      fun_prop
    · rw [NNReal.smul_def, norm_smul, Complex.norm_exp_ofReal_mul_I, mul_one]
      simpa using hf z
  have hchar : charFunDual (lam.withDensity fun z => (fp z : ℝ≥0∞)) =
      charFunDual (lam.withDensity fun z => (fm z : ℝ≥0∞)) := by
    funext ℓ
    rw [charFunDual_apply, charFunDual_apply,
      integral_withDensity_eq_integral_smul cfp.measurable,
      integral_withDensity_eq_integral_smul cfm.measurable, ← sub_eq_zero,
      ← integral_sub (key fp cfp (fun z => ?_) ℓ) (key fm cfm (fun z => ?_) ℓ)]
    · rw [← char_zero lam h hc K a ha hK hb hm ℓ]
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      simp only [fp, fm, NNReal.smul_def, Complex.real_smul, Real.coe_toNNReal']
      rw [← sub_mul, ← Complex.ofReal_sub, max_zero_sub_eq_self]
    · simp only [fp, Real.coe_toNNReal', Real.norm_eq_abs]
      exact max_le (le_abs_self _) (abs_nonneg _)
    · simp only [fm, Real.coe_toNNReal', Real.norm_eq_abs]
      exact max_le (neg_le_abs _) (abs_nonneg _)
  have heq := Measure.ext_of_charFunDual hchar
  have hae := (withDensity_eq_iff_of_sigmaFinite
    (ENNReal.continuous_coe.comp cfp).measurable.aemeasurable
    (ENNReal.continuous_coe.comp cfm).measurable.aemeasurable).1 heq
  have hall := (Continuous.ae_eq_iff_eq lam (ENNReal.continuous_coe.comp cfp)
    (ENNReal.continuous_coe.comp cfm)).1 hae
  have h1 : fp z = fm z := ENNReal.coe_injective (congrFun hall z)
  have h2 : ((fp z : ℝ≥0) : ℝ) = fm z := congrArg _ h1
  simp only [fp, fm, Real.coe_toNNReal'] at h2
  have := max_zero_sub_eq_self (h z)
  linarith

/- English proof (translation)
Introduce `Z _ _ _ _ _ lam _ ι _ c hsep A hc hconj g gc gpos C a ha hg w wc hw hint`. Take `⟨B, hB⟩` from `hw`. Establish `hB0 : 0 ≤ B` using `(norm_nonneg _).trans (hB 0)`. Establish `hC0 : 0 ≤ C`. Establish `h0` using `(gpos 0).trans_le (hg 0)`.

Conclude with `((mul_pos_iff_of_pos_right (Real.exp_pos _)).1 h0).le`. Establish `hK : 0 ≤ B * C` using `mul_nonneg hB0 hC0`. Establish `hmom : ∀ (ℓ : Z →L[ℝ] ℝ) (n : ℕ), ∫ z, (ℓ z) ^ n • (w z * (g z : ℂ)) ∂lam = 0`. Introduce `ℓ n`. Establish `hP` using `hint _ (pow_mem (dual_mem c hsep A hc hconj ℓ) n)`.

Rewrite using `[← hP]`. Use `integral_congr_ae (Eventually.of_forall fun z => ?_)` and prove the remaining obligations. Simplify using `only [Pi.pow_apply, Complex.real_smul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `hF : Continuous fun z => w z * (g z : ℂ)` using `by fun_prop`. Establish `hFb : ∀ z, ‖w z * (g z : ℂ)‖ ≤ B * C * Real.exp (-a * ‖z‖ ^ 2)`. Introduce `z`. Establish `hgz : ‖(g z : ℂ)‖ = g z` using `by simp [abs_of_pos (gpos z)]`. Rewrite using `[norm_mul, hgz, mul_assoc]`.

Conclude with `mul_le_mul (hB z) (hg z) (gpos z).le hB0`. Establish `hre : ∀ z, (w z * (g z : ℂ)).re = 0`. Use `real_zero lam (fun z => (w z * (g z : ℂ)).re) (by fun_prop) (B * C) a ha hK (fun z => (show ‖(w z * (g z : ℂ)).re‖ ≤ ‖w z * (g z : ℂ)‖ by` and prove the remaining obligations. Rewrite using `[Real.norm_eq_abs]`. Conclude with `Complex.abs_re_le_norm _).trans (hFb z)) ?_`.

Introduce `ℓ n`. Use `Complex.reCLM.integral_comp_comm (int_mom lam _ hF (B * C) a ha hK hFb ℓ n)` as an intermediate fact. Rewrite `this` using `[hmom ℓ n]`. Simplify `this` using `only [Complex.reCLM_apply, Complex.smul_re, smul_eq_mul, Complex.zero_re]`. Establish `him : ∀ z, (w z * (g z : ℂ)).im = 0`.

Use `real_zero lam (fun z => (w z * (g z : ℂ)).im) (by fun_prop) (B * C) a ha hK (fun z => (show ‖(w z * (g z : ℂ)).im‖ ≤ ‖w z * (g z : ℂ)‖ by` and prove the remaining obligations. Rewrite using `[Real.norm_eq_abs]`. Conclude with `Complex.abs_im_le_norm _).trans (hFb z)) ?_`. Introduce `ℓ n`. Use `Complex.imCLM.integral_comp_comm (int_mom lam _ hF (B * C) a ha hK hFb ℓ n)` as an intermediate fact.

Rewrite `this` using `[hmom ℓ n]`. Simplify `this` using `only [Complex.imCLM_apply, Complex.smul_im, smul_eq_mul, Complex.zero_im]`. Use function extensionality and compare the values at `z`. Establish `hz : w z * (g z : ℂ) = 0` using `Complex.ext (hre z) (him z)`. Establish `hgz : (g z : ℂ) ≠ 0` using `by exact_mod_cast (gpos z).ne'`.

Conclude with `(mul_eq_zero.1 hz).resolve_right hgz`.
-/
theorem eucTotal : EucTotal := by
  intro Z _ _ _ _ _ lam _ ι _ c hsep A hc hconj g gc gpos C a ha hg w wc hw hint
  obtain ⟨B, hB⟩ := hw
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hC0 : 0 ≤ C := by
    have h0 := (gpos 0).trans_le (hg 0)
    exact ((mul_pos_iff_of_pos_right (Real.exp_pos _)).1 h0).le
  have hK : 0 ≤ B * C := mul_nonneg hB0 hC0
  have hmom : ∀ (ℓ : Z →L[ℝ] ℝ) (n : ℕ), ∫ z, (ℓ z) ^ n • (w z * (g z : ℂ)) ∂lam = 0 := by
    intro ℓ n
    have hP := hint _ (pow_mem (dual_mem c hsep A hc hconj ℓ) n)
    rw [← hP]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [Pi.pow_apply, Complex.real_smul]
    push_cast
    ring
  have hF : Continuous fun z => w z * (g z : ℂ) := by fun_prop
  have hFb : ∀ z, ‖w z * (g z : ℂ)‖ ≤ B * C * Real.exp (-a * ‖z‖ ^ 2) := by
    intro z
    have hgz : ‖(g z : ℂ)‖ = g z := by simp [abs_of_pos (gpos z)]
    rw [norm_mul, hgz, mul_assoc]
    exact mul_le_mul (hB z) (hg z) (gpos z).le hB0
  have hre : ∀ z, (w z * (g z : ℂ)).re = 0 := by
    refine real_zero lam (fun z => (w z * (g z : ℂ)).re) (by fun_prop) (B * C) a ha hK
      (fun z => (show ‖(w z * (g z : ℂ)).re‖ ≤ ‖w z * (g z : ℂ)‖ by
        rw [Real.norm_eq_abs]; exact Complex.abs_re_le_norm _).trans (hFb z)) ?_
    intro ℓ n
    have := Complex.reCLM.integral_comp_comm (int_mom lam _ hF (B * C) a ha hK hFb ℓ n)
    rw [hmom ℓ n] at this
    simpa only [Complex.reCLM_apply, Complex.smul_re, smul_eq_mul, Complex.zero_re] using this
  have him : ∀ z, (w z * (g z : ℂ)).im = 0 := by
    refine real_zero lam (fun z => (w z * (g z : ℂ)).im) (by fun_prop) (B * C) a ha hK
      (fun z => (show ‖(w z * (g z : ℂ)).im‖ ≤ ‖w z * (g z : ℂ)‖ by
        rw [Real.norm_eq_abs]; exact Complex.abs_im_le_norm _).trans (hFb z)) ?_
    intro ℓ n
    have := Complex.imCLM.integral_comp_comm (int_mom lam _ hF (B * C) a ha hK hFb ℓ n)
    rw [hmom ℓ n] at this
    simpa only [Complex.imCLM_apply, Complex.smul_im, smul_eq_mul, Complex.zero_im] using this
  funext z
  have hz : w z * (g z : ℂ) = 0 := Complex.ext (hre z) (him z)
  have hgz : (g z : ℂ) ≠ 0 := by exact_mod_cast (gpos z).ne'
  exact (mul_eq_zero.1 hz).resolve_right hgz

end GlobalTheory.CompanionTheory.ThTot.EucT

end
