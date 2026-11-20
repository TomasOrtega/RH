import Mathlib
import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.EquivariantSections.EquivSection
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.OneParam

noncomputable section

open Matrix

namespace GlobalTheory.CompanionTheory.RgDsTor

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7 ReciprocityTheory.ChartRestriction.DS.HW PositivityTheory.RgDs.K

variable {n : ℕ}

/- English proof (translation)
Unfold `inK inG Jm`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal, Matrix.diagonal_add, ← Matrix.diagonal_zero]`. Use `congr 1`. Use function extensionality and compare the values at `a`.

Simplify using `only [Pi.star_apply, star_mul', Complex.star_def, Complex.conj_ofReal, Complex.conj_I]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]`. Use `congr 1`. Use function extensionality and compare the values at `a`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem diagI_inK (ε : Fin n → Bool) (θ : Fin n → ℝ) :
    inK ε (Matrix.diagonal fun a => (θ a : ℂ) * Complex.I) := by
  unfold inK inG Jm
  refine ⟨?_, ?_⟩
  · rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_add, ← Matrix.diagonal_zero]
    congr 1
    funext a
    simp only [Pi.star_apply, star_mul', Complex.star_def, Complex.conj_ofReal, Complex.conj_I]
    ring
  · rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext a
    ring

/- English proof (translation)
Rewrite using `[Complex.ofReal_one, one_smul, Matrix.exp_diagonal, Pi.exp_def]`. Unfold `tor`. Use `congr 1`. Use function extensionality and compare the values at `a`. Rewrite using `[Complex.exp_eq_exp_ℂ]`.
-/
theorem tor_eq_exp (θ : Fin n → ℝ) :
    tor θ = NormedSpace.exp (((1 : ℝ) : ℂ) • Matrix.diagonal fun a => (θ a : ℂ) * Complex.I) := by
  rw [Complex.ofReal_one, one_smul, Matrix.exp_diagonal, Pi.exp_def]
  unfold tor
  congr 1
  funext a
  rw [Complex.exp_eq_exp_ℂ]

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Rewrite using `[pow_succ, ContinuousLinearMap.mul_apply, h, map_smul, ih, smul_smul, ← pow_succ']`.
-/
private theorem pow_apply_eq_pow_smul_of_apply_eq_smul {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (A : V →L[ℂ] V) (c : ℂ) (w : V) (h : A w = c • w) (k : ℕ) : (A ^ k) w = c ^ k • w := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ContinuousLinearMap.mul_apply, h, map_smul, ih, smul_smul, ← pow_succ']

/- English proof (translation)
Establish `h1` using `(NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) A).mapL (ContinuousLinearMap.apply ℂ V w)`. Establish `h2` using `(NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) c).smul_const w`. Rewrite `h2` using `[← Complex.exp_eq_exp_ℂ]`. Establish `h3 : HasSum (fun k : ℕ => (ContinuousLinearMap.apply ℂ V w) (((k.factorial : ℂ))⁻¹ • A ^ k)) (Complex.exp c • w)`. Use `h2 using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `k`. Rewrite using `[ContinuousLinearMap.apply_apply, ContinuousLinearMap.smul_apply, pow_apply_eq_pow_smul_of_apply_eq_smul A c w h k, smul_smul, smul_eq_mul]`. Establish `e` using `h1.unique h3`. Rewrite `e` using `[ContinuousLinearMap.apply_apply]`. Then use the resulting hypothesis.
-/
theorem exp_apply_of_eigen {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    (A : V →L[ℂ] V) (c : ℂ) (w : V) (h : A w = c • w) :
    NormedSpace.exp A w = Complex.exp c • w := by
  have h1 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) A).mapL (ContinuousLinearMap.apply ℂ V w)
  have h2 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) c).smul_const w
  rw [← Complex.exp_eq_exp_ℂ] at h2
  have h3 : HasSum (fun k : ℕ => (ContinuousLinearMap.apply ℂ V w) (((k.factorial : ℂ))⁻¹ • A ^ k))
      (Complex.exp c • w) := by
    convert h2 using 1
    funext k
    rw [ContinuousLinearMap.apply_apply, ContinuousLinearMap.smul_apply,
      pow_apply_eq_pow_smul_of_apply_eq_smul A c w h k, smul_smul, smul_eq_mul]
  have e := h1.unique h3
  rwa [ContinuousLinearMap.apply_apply] at e

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[Matrix.sum_apply]`. Simplify using `only [Matrix.smul_apply, Matrix.single_apply, Matrix.diagonal_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality.

Simplify using the standard rewrite rules. Rewrite using `[if_neg hij]`. Use `symm`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `c _`.

Rewrite using `[if_neg]`. Introduce and unpack `⟨rfl, rfl⟩`. Conclude with `hij rfl`.
-/
private theorem diagonal_mul_I_eq_sum_single (θ : Fin n → ℝ) :
    (Matrix.diagonal fun a => (θ a : ℂ) * Complex.I) =
      ∑ a, ((θ a : ℂ) * Complex.I) • Matrix.single a a (1 : ℂ) := by
  ext i j
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, Matrix.single_apply, Matrix.diagonal_apply, smul_eq_mul, mul_ite, mul_one,
    mul_zero]
  by_cases hij : i = j
  · subst hij
    simp
  · rw [if_neg hij]
    symm
    apply Finset.sum_eq_zero
    intro c _
    rw [if_neg]
    rintro ⟨rfl, rfl⟩
    exact hij rfl

/- English proof (translation)
Rewrite using `[diagonal_mul_I_eq_sum_single, map_sum, ContinuousLinearMap.sum_apply]`. Repeatedly rewrite using `[map_smul, ContinuousLinearMap.smul_apply, T.13, smul_smul]`. Rewrite using `[← Finset.sum_smul]`. Use `congr 1`. Use `push_cast`.

Rewrite using `[Finset.sum_mul]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dtau_diag_w {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (θ : Fin n → ℝ) :
    T.dτ (Matrix.diagonal fun a => (θ a : ℂ) * Complex.I) T.w =
      (((∑ a, Λ a * θ a : ℝ) : ℂ) * Complex.I) • T.w := by
  rw [diagonal_mul_I_eq_sum_single, map_sum, ContinuousLinearMap.sum_apply]
  simp_rw [map_smul, ContinuousLinearMap.smul_apply, T.13, smul_smul]
  rw [← Finset.sum_smul]
  congr 1
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

/- English proof (translation)
Introduce `n ε Λ T θ k hk`. Establish `hX` using `diagI_inK ε θ`. Take `⟨γ, hγ⟩` from `exists_curve ε hX`. Establish `h1 : γ 1 = k` using `onep_KG_ext (by rw [hγ 1, hk, tor_eq_exp])`. Rewrite using `[← h1, KType.op_curve T hX γ hγ 1]`.

Apply `exp_apply_of_eigen` to reduce the goal to its premises. Rewrite using `[ContinuousLinearMap.smul_apply, dtau_diag_w, smul_smul, Complex.ofReal_one, one_mul]`.
-/
theorem torW : TorW := by
  intro n ε Λ T θ k hk
  have hX := diagI_inK ε θ
  obtain ⟨γ, hγ⟩ := exists_curve ε hX
  have h1 : γ 1 = k := onep_KG_ext (by rw [hγ 1, hk, tor_eq_exp])
  rw [← h1, KType.op_curve T hX γ hγ 1]
  apply exp_apply_of_eigen
  rw [ContinuousLinearMap.smul_apply, dtau_diag_w, smul_smul, Complex.ofReal_one, one_mul]

end GlobalTheory.CompanionTheory.RgDsTor
