import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableExpNegL1Norm
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.EntirePeriodicEqZeroOfFourierCoeffEqZero
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TauPeriod Complex
open scoped Real ContDiff

noncomputable section

namespace GlobalTheory.TauPeriod

/- English proof (translation)
Use `set p : (Fin g → ℝ) → UnitAddTorus (Fin g) := fun x i ↦ (x i : UnitAddCircle) with hp`. Establish `hq : IsOpenQuotientMap p` using `IsOpenQuotientMap.piMap fun _ ↦ QuotientAddGroup.isOpenQuotientMap_mk`. Use `set f₀ : UnitAddTorus (Fin g) → ℂ := fun z ↦ A (Function.surjInv hq.surjective z) with hf₀`. Establish `hfp : ∀ x, f₀ (p x) = A x` using `fun x ↦ by set x' := Function.surjInv hq.surjective (p x)`. Establish `h1 : p x' = p x` using `Function.surjInv_eq _ _`.

Establish `h2 : ∀ i, ∃ n : ℤ, (n : ℝ) = x' i - x i` using `fun i ↦ by`. Establish `h3 : ((x' i - x i : ℝ) : UnitAddCircle) = 0`. Rewrite using `[AddCircle.coe_sub, sub_eq_zero]`. Conclude with `congrFun h1 i`. Take `⟨n, hn⟩` from `(AddCircle.coe_eq_zero_iff _).1 h3`.

Conclude with `⟨n, by simpa using hn⟩`. Use `choose n hn using h2`. Rewrite using `[← GlobalTheory.apply_add_intCast_of_periodic_single hA n x]`. Express the relevant statement in the definitionally equal form `A x' = _`. Use `congr 1`.

Use function extensionality and compare the values at `i`. Simplify using `[hn]`. Set `f : C(UnitAddTorus (Fin g), ℂ)` to `⟨f₀, hq.isQuotientMap.continuous_iff.2 <| by`. Rewrite using `[show f₀ ∘ p = A from funext hfp]`. Conclude with `hc⟩`.

Establish `hchar : ∀ n x, UnitAddTorus.mFourier (-n) (p x) = cexp (-(2 * Real.pi * I) * ∑ i, (n i : ℂ) * (x i : ℂ))` using `fun n x ↦ by`. Simplify using `only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, hp, fourier_coe_apply, ← Complex.exp_sum]`. Use `congr 1`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ ↦ ?_` and prove the remaining obligations.

Simplify using `only [Pi.neg_apply]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hchar' : ∀ n x, UnitAddTorus.mFourier n (p x) = cexp (2 * Real.pi * I * ∑ i, (n i : ℂ) * (x i : ℂ))` using `fun n x ↦ by`. Simplify using `only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, hp, fourier_coe_apply, ← Complex.exp_sum]`.

Use `congr 1`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ ↦ ?_` and prove the remaining obligations. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `hcoeff : ∀ n, UnitAddTorus.mFourierCoeff f n = ∫ x in Set.Icc (0 : Fin g → ℝ) 1, A x * cexp (-(2 * Real.pi * I) * ∑ i, (n i : ℂ) * (x i : ℂ))` using `fun n ↦ by`. Rewrite using `[UnitAddTorus.mFourierCoeff_eq_integral f n 0]`. Simplify using `only [Pi.zero_apply, zero_add]`. Establish `h2 : {x : Fin g → ℝ | ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1} = Set.pi Set.univ fun i ↦ Set.Ioc ((0 : Fin g → ℝ) i) ((1 : Fin g → ℝ) i)`. Use extensionality with `x`.

Simplify using the standard rewrite rules. Rewrite using `[h2, MeasureTheory.setIntegral_congr_set (μ := MeasureTheory.volume) MeasureTheory.Measure.univ_pi_Ioc_ae_eq_Icc]`. Use `MeasureTheory.integral_congr_ae (.of_forall fun x ↦ ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `UnitAddTorus.mFourier (-n) (p x) • f₀ (p x) = _`. Simplify using `only [hchar, hfp, smul_eq_mul, mul_comm]`.

Establish `hsum` using `UnitAddTorus.hasSum_mFourier_series_apply_of_summable (f := f) (by rw [funext hcoeff]; exact hs) (p y)`. Express the relevant statement in the definitionally equal form `HasSum _ (f₀ (p _)) at hsum`. Simplify using `only [hcoeff, hchar', hfp, smul_eq_mul] at hsum`. Conclude with `hsum`.
-/
theorem hasSum_cube_fourier_of_summable {g : ℕ} {A : (Fin g → ℝ) → ℂ} (hc : Continuous A)
    (hA : ∀ (i : Fin g) x, A (x + Pi.single i 1) = A x)
    (hs : Summable fun m : Fin g → ℤ => ∫ x in Set.Icc (0 : Fin g → ℝ) 1,
      A x * cexp (-(2 * Real.pi * I) * ∑ i, (m i : ℂ) * (x i : ℂ))) (y : Fin g → ℝ) :
    HasSum (fun m : Fin g → ℤ => (∫ x in Set.Icc (0 : Fin g → ℝ) 1,
      A x * cexp (-(2 * Real.pi * I) * ∑ i, (m i : ℂ) * (x i : ℂ))) *
        cexp (2 * Real.pi * I * ∑ i, (m i : ℂ) * (y i : ℂ))) (A y) := by
  set p : (Fin g → ℝ) → UnitAddTorus (Fin g) := fun x i ↦ (x i : UnitAddCircle) with hp
  have hq : IsOpenQuotientMap p :=
    IsOpenQuotientMap.piMap fun _ ↦ QuotientAddGroup.isOpenQuotientMap_mk
  set f₀ : UnitAddTorus (Fin g) → ℂ := fun z ↦ A (Function.surjInv hq.surjective z) with hf₀
  have hfp : ∀ x, f₀ (p x) = A x := fun x ↦ by
    set x' := Function.surjInv hq.surjective (p x)
    have h1 : p x' = p x := Function.surjInv_eq _ _
    have h2 : ∀ i, ∃ n : ℤ, (n : ℝ) = x' i - x i := fun i ↦ by
      have h3 : ((x' i - x i : ℝ) : UnitAddCircle) = 0 := by
        rw [AddCircle.coe_sub, sub_eq_zero]; exact congrFun h1 i
      obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff _).1 h3
      exact ⟨n, by simpa using hn⟩
    choose n hn using h2
    rw [← GlobalTheory.apply_add_intCast_of_periodic_single hA n x]
    change A x' = _
    congr 1
    funext i
    simp [hn]
  let f : C(UnitAddTorus (Fin g), ℂ) := ⟨f₀,
    hq.isQuotientMap.continuous_iff.2 <| by
      rw [show f₀ ∘ p = A from funext hfp]; exact hc⟩
  have hchar : ∀ n x, UnitAddTorus.mFourier (-n) (p x) =
      cexp (-(2 * Real.pi * I) * ∑ i, (n i : ℂ) * (x i : ℂ)) := fun n x ↦ by
    simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, hp, fourier_coe_apply,
      ← Complex.exp_sum]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [Pi.neg_apply]
    push_cast
    ring
  have hchar' : ∀ n x, UnitAddTorus.mFourier n (p x) =
      cexp (2 * Real.pi * I * ∑ i, (n i : ℂ) * (x i : ℂ)) := fun n x ↦ by
    simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, hp, fourier_coe_apply,
      ← Complex.exp_sum]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    push_cast
    ring
  have hcoeff : ∀ n, UnitAddTorus.mFourierCoeff f n = ∫ x in Set.Icc (0 : Fin g → ℝ) 1,
      A x * cexp (-(2 * Real.pi * I) * ∑ i, (n i : ℂ) * (x i : ℂ)) := fun n ↦ by
    rw [UnitAddTorus.mFourierCoeff_eq_integral f n 0]
    simp only [Pi.zero_apply, zero_add]
    have h2 : {x : Fin g → ℝ | ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1} =
        Set.pi Set.univ fun i ↦ Set.Ioc ((0 : Fin g → ℝ) i) ((1 : Fin g → ℝ) i) := by
      ext x; simp
    rw [h2, MeasureTheory.setIntegral_congr_set
      (μ := MeasureTheory.volume) MeasureTheory.Measure.univ_pi_Ioc_ae_eq_Icc]
    refine MeasureTheory.integral_congr_ae (.of_forall fun x ↦ ?_)
    change UnitAddTorus.mFourier (-n) (p x) • f₀ (p x) = _
    simp only [hchar, hfp, smul_eq_mul, mul_comm]
  have hsum := UnitAddTorus.hasSum_mFourier_series_apply_of_summable (f := f)
    (by rw [funext hcoeff]; exact hs) (p y)
  change HasSum _ (f₀ (p _)) at hsum
  simp only [hcoeff, hchar', hfp, smul_eq_mul] at hsum
  exact hsum

/- English proof (translation)
Use `set w : Fin g → ℂ := fun i => I * ((z i).im : ℂ) with hw`. Use `set A : (Fin g → ℝ) → ℂ := fun x => f ((fun i => (x i : ℂ)) + w) with hAdef`. Establish `hcA : Continuous A`. Use `hf.continuous` as an intermediate fact. Use `fun_prop`.

Establish `hperA : ∀ (i : Fin g) x, A (x + Pi.single i 1) = A x` using `fun i x => by`. Simplify using `only [hAdef]`. Rewrite using `[← hper i ((fun i => (x i : ℂ)) + w)]`. Use `congr 1`. Use function extensionality and compare the values at `j`.

Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Simplify using `[hj]`.

Establish `hcoef : ∀ m : Fin g → ℤ, (∫ x in Set.Icc (0 : Fin g → ℝ) 1, A x * cexp (-(2 * Real.pi * I) * ∑ i, (m i : ℂ) * (x i : ℂ))) = ex m w * cf f m`. Introduce `m`. Rewrite using `[← cf_translate f hf hper m w]`. Both sides reduce to the same expression. Use `set S : ℝ := ∑ i, |(z i).im| with hS`.

Establish `hS0 : 0 ≤ S` using `Finset.sum_nonneg fun _ _ => abs_nonneg _`. Take `⟨M, hM⟩` from `hdec (S + 1) (by linarith)`. Establish `hbound : ∀ m : Fin g → ℤ, ‖ex m w * cf f m‖ ≤ M * Real.exp (-(2 * π) * l1 m)`. Introduce `m`. Rewrite using `[norm_mul, norm_ex]`.

Establish `hwim : ∀ i, (w i).im = (z i).im` using `fun i => by simp [hw]`. Establish `key : -(2 * π) * ∑ i, (m i : ℝ) * (w i).im ≤ (2 * π) * (S * l1 m)`. Establish `h1 : -∑ i, (m i : ℝ) * (w i).im ≤ S * l1 m`. Rewrite using `[← Finset.sum_neg_distrib, l1, Finset.mul_sum]`. Use `Finset.sum_le_sum fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[hwim]`. Establish `ha : |(z i).im| ≤ S` using `Finset.single_le_sum (f := fun j => |(z j).im|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)`. Combine the equalities or inequalities in the displayed calculation. Use polynomial arithmetic with `[Real.pi_pos]`. Establish `hcf` using `hM m`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_left_comm, ← Real.exp_add]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree. Establish `hsA : Summable fun m : Fin g → ℤ => ∫ x in Set.Icc (0 : Fin g → ℝ) 1, A x * cexp (-(2 * Real.pi * I) * ∑ i, (m i : ℂ) * (x i : ℂ))`.

Simplify using `only [hcoef]`. Use `Summable.of_norm_bounded ?_ hbound` and prove the remaining obligations. Conclude with `(summable_exp_neg_l1Norm (by positivity : (0 : ℝ) < 2 * π)).mul_left M`. Establish `h` using `hasSum_cube_fourier_of_summable hcA hperA hsA (fun i => (z i).re)`. Simplify using `only [hcoef] at h`.

Establish `hz : (fun i => (((z i).re : ℝ) : ℂ)) + w = z`. Use function extensionality and compare the values at `i`. Simplify using `only [Pi.add_apply, hw]`. Rewrite using `[mul_comm]`. Conclude with `Complex.re_add_im (z i)`.

Establish `hA : A (fun i => (z i).re) = f z`. Simplify using `only [hAdef]`. Rewrite using `[hz]`. Rewrite `h` using `[hA]`. Use `h.congr_fun fun m => ?_` and prove the remaining obligations.

Establish `he : ex m z = ex m (fun i => (((z i).re : ℝ) : ℂ)) * ex m w`. Rewrite using `[← ex_add, hz]`. Rewrite using `[he]`. Simplify using `only [ex]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hasSum_cf_mul_ex {g : ℕ} (f : (Fin g → ℂ) → ℂ) (hf : Differentiable ℂ f)
    (hper : ∀ (j : Fin g) z, f (z + Pi.single j 1) = f z)
    (hdec : ∀ R : ℝ, 0 ≤ R → ∃ M : ℝ, ∀ n : Fin g → ℤ,
      ‖cf f n‖ ≤ M * Real.exp (-(2 * π * R) * l1 n)) (z : Fin g → ℂ) :
    HasSum (fun n : Fin g → ℤ => cf f n * ex n z) (f z) := by
  set w : Fin g → ℂ := fun i => I * ((z i).im : ℂ) with hw
  set A : (Fin g → ℝ) → ℂ := fun x => f ((fun i => (x i : ℂ)) + w) with hAdef
  have hcA : Continuous A := by
    have := hf.continuous
    fun_prop
  have hperA : ∀ (i : Fin g) x, A (x + Pi.single i 1) = A x := fun i x => by
    simp only [hAdef]
    rw [← hper i ((fun i => (x i : ℂ)) + w)]
    congr 1
    funext j
    by_cases hj : j = i
    · subst hj; simp; ring
    · simp [hj]
  have hcoef : ∀ m : Fin g → ℤ, (∫ x in Set.Icc (0 : Fin g → ℝ) 1,
      A x * cexp (-(2 * Real.pi * I) * ∑ i, (m i : ℂ) * (x i : ℂ))) = ex m w * cf f m := by
    intro m
    rw [← cf_translate f hf hper m w]
    rfl
  set S : ℝ := ∑ i, |(z i).im| with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => abs_nonneg _
  obtain ⟨M, hM⟩ := hdec (S + 1) (by linarith)
  have hbound : ∀ m : Fin g → ℤ, ‖ex m w * cf f m‖ ≤ M * Real.exp (-(2 * π) * l1 m) := by
    intro m
    rw [norm_mul, norm_ex]
    have hwim : ∀ i, (w i).im = (z i).im := fun i => by simp [hw]
    have key : -(2 * π) * ∑ i, (m i : ℝ) * (w i).im ≤ (2 * π) * (S * l1 m) := by
      have h1 : -∑ i, (m i : ℝ) * (w i).im ≤ S * l1 m := by
        rw [← Finset.sum_neg_distrib, l1, Finset.mul_sum]
        refine Finset.sum_le_sum fun i _ => ?_
        rw [hwim]
        have ha : |(z i).im| ≤ S :=
          Finset.single_le_sum (f := fun j => |(z j).im|) (fun _ _ => abs_nonneg _)
            (Finset.mem_univ i)
        calc -((m i : ℝ) * (z i).im) ≤ |(m i : ℝ) * (z i).im| := neg_le_abs _
          _ = |(m i : ℝ)| * |(z i).im| := abs_mul _ _
          _ ≤ |(m i : ℝ)| * S := mul_le_mul_of_nonneg_left ha (abs_nonneg _)
          _ = S * |(m i : ℝ)| := mul_comm _ _
      nlinarith [Real.pi_pos]
    have hcf := hM m
    calc Real.exp (-(2 * π) * ∑ i, (m i : ℝ) * (w i).im) * ‖cf f m‖
        ≤ Real.exp ((2 * π) * (S * l1 m)) * (M * Real.exp (-(2 * π * (S + 1)) * l1 m)) :=
          mul_le_mul (Real.exp_le_exp.2 key) hcf (norm_nonneg _) (Real.exp_pos _).le
      _ = M * Real.exp (-(2 * π) * l1 m) := by
          rw [mul_left_comm, ← Real.exp_add]
          congr 2
          ring
  have hsA : Summable fun m : Fin g → ℤ => ∫ x in Set.Icc (0 : Fin g → ℝ) 1,
      A x * cexp (-(2 * Real.pi * I) * ∑ i, (m i : ℂ) * (x i : ℂ)) := by
    simp only [hcoef]
    refine Summable.of_norm_bounded ?_ hbound
    exact (summable_exp_neg_l1Norm (by positivity : (0 : ℝ) < 2 * π)).mul_left M
  have h := hasSum_cube_fourier_of_summable hcA hperA hsA (fun i => (z i).re)
  simp only [hcoef] at h
  have hz : (fun i => (((z i).re : ℝ) : ℂ)) + w = z := by
    funext i
    simp only [Pi.add_apply, hw]
    rw [mul_comm]
    exact Complex.re_add_im (z i)
  have hA : A (fun i => (z i).re) = f z := by
    simp only [hAdef]
    rw [hz]
  rw [hA] at h
  refine h.congr_fun fun m => ?_
  have he : ex m z = ex m (fun i => (((z i).re : ℝ) : ℂ)) * ex m w := by
    rw [← ex_add, hz]
  rw [he]
  simp only [ex]
  ring

end GlobalTheory.TauPeriod
