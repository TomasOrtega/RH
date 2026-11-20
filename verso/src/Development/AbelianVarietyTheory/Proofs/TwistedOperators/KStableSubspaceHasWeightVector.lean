import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementB
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace

noncomputable section
namespace GlobalTheory.TorusWtExist

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨δ, hδ, hδc⟩ : ∃ δ > 0, ∀ s, |s| ≤ δ → ‖χ s - 1‖ ≤ 1 / 2 := by`. Use `Metric.continuous_iff.mp hc 0 (1 / 2) (by norm_num)` as an intermediate fact. Take `⟨δ, hδ, h⟩` from `this`. Use `⟨δ / 2, by positivity, fun s hs => ?_⟩` and prove the remaining obligations. Use `h s (by rw [Real.dist_eq, sub_zero]; linarith)` as an intermediate fact.

Rewrite `this` using `[dist_eq_norm, h0]`. Conclude with `this.le`. Use `set c : ℂ := ∫ s in (0 : ℝ)..δ, χ s with hcdef`. Establish `hint : ∀ a b : ℝ, IntervalIntegrable χ MeasureTheory.volume a b` using `fun a b => hc.intervalIntegrable a b`. Establish `hc0 : c ≠ 0`.

Introduce `h`. Establish `h1 : ‖∫ s in (0 : ℝ)..δ, (χ s - 1)‖ ≤ 1 / 2 * |δ - 0|`. Apply `intervalIntegral.norm_integral_le_of_norm_le_const` to reduce the goal to its premises. Introduce `s hs`. Rewrite `hs` using `[Set.uIoc_of_le hδ.le]`.

Apply the tactic sequence `exact hδc s (by rw [abs_le]; constructor <;> linarith [hs.1, hs.2])`. Rewrite `h1` using `[intervalIntegral.integral_sub (hint 0 δ) intervalIntegrable_const, ← hcdef, h]`. Simplify using `only [intervalIntegral.integral_const, sub_zero, zero_sub, norm_neg, Complex.real_smul, mul_one] at h1`. Rewrite `h1` using `[Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ]`. Combine the linear equalities and inequalities to obtain the conclusion.

Use `set F : ℝ → ℂ := fun u => ∫ s in (0 : ℝ)..u, χ s with hF`. Establish `hFd : ∀ t, HasDerivAt F (χ t) t` using `fun t => (hc.integral_hasStrictDerivAt 0 t).hasDerivAt`. Establish `hid : ∀ t, χ t = (F (t + δ) - F t) / c`. Introduce `t`. Rewrite using `[eq_div_iff hc0]`.

Establish `h1 : ∫ s in (0 : ℝ)..δ, χ (t + s) = F (t + δ) - F t`. Rewrite using `[intervalIntegral.integral_comp_add_left (fun x => χ x) t, add_zero, hF]`. Simplify using `only`. Rewrite using `[intervalIntegral.integral_interval_sub_left (hint 0 _) (hint 0 _)]`. Rewrite using `[← h1, hcdef, ← intervalIntegral.integral_const_mul]`.

Use `congr 1`. Use function extensionality and compare the values at `s`. Rewrite using `[hm]`. Use `set a : ℂ := (χ δ - 1) / c with ha`. Establish `hd : ∀ t : ℝ, HasDerivAt χ (χ t * a) t`.

Introduce `t`. Establish `h1 : HasDerivAt (fun t => (F (t + δ) - F t) / c) ((χ (t + δ) - χ t) / c) t`. Use `((hFd (t + δ)).comp_add_const t δ).sub (hFd t)` as an intermediate fact. Conclude with `this.div_const c`. Establish `hfun : χ = fun t => (F (t + δ) - F t) / c` using `funext hid`.

Establish `h3 : (χ (t + δ) - χ t) / c = χ t * a` using `by rw [hm, ha]; ring`. Rewrite `h1` using `[h3, ← hfun]`. Conclude with `h1`. Establish `hg : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Complex.exp (-(a * t)) * χ t) 0 t`. Introduce `t`.

Establish `h1 : HasDerivAt (fun t : ℝ => Complex.exp (-(a * t))) (Complex.exp (-(a * t)) * (-a)) t`. Establish `: HasDerivAt (fun t : ℝ => -(a * (t : ℂ))) (-a) t`. Simplify using `using ((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul a).fun_neg`. Conclude with `this.cexp`. Establish `h2` using `h1.mul (hd t)`.

Establish `h3 : Complex.exp (-(a * t)) * (-a) * χ t + Complex.exp (-(a * t)) * (χ t * a) = 0` using `by ring`. Rewrite `h2` using `[h3]`. Conclude with `h2`. Establish `hconst : ∀ t : ℝ, Complex.exp (-(a * t)) * χ t = 1`. Introduce `t`.

Use `is_const_of_deriv_eq_zero (fun t => (hg t).differentiableAt) (fun t => (hg t).deriv) t 0` as an intermediate fact. Rewrite using `[this]`. Simplify using `[h0]`. Establish `hexp : ∀ t : ℝ, χ t = Complex.exp (a * t)`. Introduce `t`.

Establish `h` using `hconst t`. Rewrite `h` using `[Complex.exp_neg]`. Clear denominators, using `at h` for the nonvanishing conditions. Conclude with `h`. Establish `h2'` using `h2`.

Rewrite `h2'` using `[hexp, Complex.exp_eq_one_iff]`. Take `⟨k, hk⟩` from `h2'`. Establish `hpi : ((2 * Real.pi : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast (by positivity : (2 * Real.pi) ≠ 0)`. Establish `hak : a = k * Complex.I`. Establish `: a * ((2 * Real.pi : ℝ) : ℂ) = (k * Complex.I) * ((2 * Real.pi : ℝ) : ℂ)`.

Rewrite using `[hk]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Conclude with `mul_right_cancel₀ hpi this`. Use `⟨k, fun t => ?_⟩` and prove the remaining obligations.

Rewrite using `[hexp, hak]`. Use `push_cast`. Put the polynomial expressions in normal form.
-/
theorem charR_eq_exp (χ : ℝ → ℂ) (hc : Continuous χ) (hm : ∀ s t, χ (s + t) = χ s * χ t)
    (h0 : χ 0 = 1) (h2 : χ (2 * Real.pi) = 1) : ∃ m : ℤ, ∀ t : ℝ, χ t = Complex.exp (((m * t : ℝ) : ℂ) * Complex.I) := by
  obtain ⟨δ, hδ, hδc⟩ : ∃ δ > 0, ∀ s, |s| ≤ δ → ‖χ s - 1‖ ≤ 1 / 2 := by
    have := Metric.continuous_iff.mp hc 0 (1 / 2) (by norm_num)
    obtain ⟨δ, hδ, h⟩ := this
    refine ⟨δ / 2, by positivity, fun s hs => ?_⟩
    have := h s (by rw [Real.dist_eq, sub_zero]; linarith)
    rw [dist_eq_norm, h0] at this
    exact this.le
  set c : ℂ := ∫ s in (0 : ℝ)..δ, χ s with hcdef
  have hint : ∀ a b : ℝ, IntervalIntegrable χ MeasureTheory.volume a b := fun a b => hc.intervalIntegrable a b
  have hc0 : c ≠ 0 := by
    intro h
    have h1 : ‖∫ s in (0 : ℝ)..δ, (χ s - 1)‖ ≤ 1 / 2 * |δ - 0| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro s hs
      rw [Set.uIoc_of_le hδ.le] at hs
      exact hδc s (by rw [abs_le]; constructor <;> linarith [hs.1, hs.2])
    rw [intervalIntegral.integral_sub (hint 0 δ) intervalIntegrable_const, ← hcdef, h] at h1
    simp only [intervalIntegral.integral_const, sub_zero, zero_sub, norm_neg, Complex.real_smul, mul_one] at h1
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ] at h1
    linarith
  set F : ℝ → ℂ := fun u => ∫ s in (0 : ℝ)..u, χ s with hF
  have hFd : ∀ t, HasDerivAt F (χ t) t := fun t => (hc.integral_hasStrictDerivAt 0 t).hasDerivAt
  have hid : ∀ t, χ t = (F (t + δ) - F t) / c := by
    intro t
    rw [eq_div_iff hc0]
    have h1 : ∫ s in (0 : ℝ)..δ, χ (t + s) = F (t + δ) - F t := by
      rw [intervalIntegral.integral_comp_add_left (fun x => χ x) t, add_zero, hF]
      simp only
      rw [intervalIntegral.integral_interval_sub_left (hint 0 _) (hint 0 _)]
    rw [← h1, hcdef, ← intervalIntegral.integral_const_mul]
    congr 1; funext s; rw [hm]
  set a : ℂ := (χ δ - 1) / c with ha
  have hd : ∀ t : ℝ, HasDerivAt χ (χ t * a) t := by
    intro t
    have h1 : HasDerivAt (fun t => (F (t + δ) - F t) / c) ((χ (t + δ) - χ t) / c) t := by
      have := ((hFd (t + δ)).comp_add_const t δ).sub (hFd t)
      exact this.div_const c
    have hfun : χ = fun t => (F (t + δ) - F t) / c := funext hid
    have h3 : (χ (t + δ) - χ t) / c = χ t * a := by rw [hm, ha]; ring
    rw [h3, ← hfun] at h1
    exact h1
  have hg : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Complex.exp (-(a * t)) * χ t) 0 t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => Complex.exp (-(a * t))) (Complex.exp (-(a * t)) * (-a)) t := by
      have : HasDerivAt (fun t : ℝ => -(a * (t : ℂ))) (-a) t := by
        simpa using ((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul a).fun_neg
      exact this.cexp
    have h2 := h1.mul (hd t)
    have h3 : Complex.exp (-(a * t)) * (-a) * χ t + Complex.exp (-(a * t)) * (χ t * a) = 0 := by ring
    rw [h3] at h2
    exact h2
  have hconst : ∀ t : ℝ, Complex.exp (-(a * t)) * χ t = 1 := by
    intro t
    have := is_const_of_deriv_eq_zero (fun t => (hg t).differentiableAt) (fun t => (hg t).deriv) t 0
    rw [this]; simp [h0]
  have hexp : ∀ t : ℝ, χ t = Complex.exp (a * t) := by
    intro t
    have h := hconst t
    rw [Complex.exp_neg] at h
    field_simp at h
    exact h
  have h2' := h2
  rw [hexp, Complex.exp_eq_one_iff] at h2'
  obtain ⟨k, hk⟩ := h2'
  have hpi : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (2 * Real.pi) ≠ 0)
  have hak : a = k * Complex.I := by
    have : a * ((2 * Real.pi : ℝ) : ℂ) = (k * Complex.I) * ((2 * Real.pi : ℝ) : ℂ) := by
      rw [hk]; push_cast; ring
    exact mul_right_cancel₀ hpi this
  refine ⟨k, fun t => ?_⟩
  rw [hexp, hak]; push_cast; ring_nf

def dT {n : ℕ} (θ : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I)

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, dT, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Simplify using `[← Complex.exp_conj, ← Complex.exp_add]`.

Rewrite using `[dT, Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dT_mem_Kset {n : ℕ} (ε : Fin n → Bool) (θ : Fin n → ℝ) : dT θ ∈ Formalism.REAL.Kset ε := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, dT, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    simp [← Complex.exp_conj, ← Complex.exp_add]
  · rw [dT, Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext a
    ring

/- English proof (translation)
Introduce and unpack `g ⟨hu, hc⟩`. Use `show gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε`. Rewrite `hu` using `[Matrix.mem_unitaryGroup_iff']`. Rewrite using `[mul_assoc, ← hc, ← mul_assoc, ← Matrix.star_eq_conjTranspose, hu, one_mul]`.
-/
theorem Kset_sub_UJset {n : ℕ} (ε : Fin n → Bool) :
    ∀ g ∈ Formalism.REAL.Kset ε, g ∈ Formalism.MainNotions.S.UJset ε := by
  rintro g ⟨hu, hc⟩
  show gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε
  rw [Matrix.mem_unitaryGroup_iff'] at hu
  rw [mul_assoc, ← hc, ← mul_assoc, ← Matrix.star_eq_conjTranspose, hu, one_mul]

/- English proof (translation)
Rewrite using `[dT, dT, dT, Matrix.diagonal_mul_diagonal]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Rewrite using `[← Complex.exp_add]`. Use `congr 1`.

Simplify using `only [Pi.add_apply]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dT_add {n : ℕ} (θ θ' : Fin n → ℝ) : dT (θ + θ') = dT θ * dT θ' := by
  rw [dT, dT, dT, Matrix.diagonal_mul_diagonal]
  congr 1; funext a
  rw [← Complex.exp_add]; congr 1; simp only [Pi.add_apply]; push_cast; ring

/- English proof (translation)
Rewrite using `[dT, ← Matrix.diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Simplify using the standard rewrite rules.
-/
theorem dT_zero {n : ℕ} : dT (0 : Fin n → ℝ) = 1 := by
  rw [dT, ← Matrix.diagonal_one]; congr 1; funext a; simp

/- English proof (translation)
Rewrite using `[dT, ← Matrix.diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `b`. Distinguish the cases in `h : b = a`. Substitute `h` using the available equality.

Simplify using `only [Pi.single_eq_same, Pi.one_apply]`. Rewrite using `[Complex.exp_eq_one_iff]; exact ⟨1, by push_cast; ring⟩`. Simplify using `[Pi.single_eq_of_ne h]`.
-/
theorem dT_two_pi {n : ℕ} (a : Fin n) : dT (Pi.single a (2 * Real.pi)) = 1 := by
  rw [dT, ← Matrix.diagonal_one]; congr 1; funext b
  by_cases h : b = a
  · subst h; simp only [Pi.single_eq_same, Pi.one_apply]
    rw [Complex.exp_eq_one_iff]; exact ⟨1, by push_cast; ring⟩
  · simp [Pi.single_eq_of_ne h]

/- English proof (translation)
Unfold `dT`. Apply `Continuous.matrix_diagonal` to reduce the goal to its premises. Use `fun_prop`.
-/
theorem continuous_dT {n : ℕ} : Continuous (dT (n := n)) := by
  unfold dT
  apply Continuous.matrix_diagonal
  fun_prop

/- English proof (translation)
Introduce `n ε H _ _ ρ hrep hcont _ S hfd hstab hne`. Use `set T : (Fin n → ℝ) → (H →L[ℂ] H) := fun θ => ρ (dT θ) with hT`. Establish `hmem : ∀ θ, dT θ ∈ Formalism.MainNotions.S.UJset ε` using `fun θ => Kset_sub_UJset ε _ (dT_mem_Kset ε θ)`. Establish `hTadd : ∀ θ θ' v, T (θ + θ') v = T θ (T θ' v)`. Introduce `θ θ' v`.

Simplify using `only [hT, dT_add, hrep.2 _ (hmem θ) _ (hmem θ'), ContinuousLinearMap.comp_apply]`. Establish `hTcomm : ∀ θ θ' v, T θ (T θ' v) = T θ' (T θ v)`. Introduce `θ θ' v`. Rewrite using `[← hTadd, ← hTadd, add_comm]`. Establish `hTS : ∀ θ, ∀ v ∈ S, T θ v ∈ S` using `fun θ v hv => hstab _ (dT_mem_Kset ε θ) v hv`.

Set `P : Submodule ℂ H → Prop` to `fun W => W ≤ S ∧ W ≠ ⊥ ∧ ∀ θ, ∀ v ∈ W, T θ v ∈ W`. Establish `hex : ∃ k, ∃ W, P W ∧ Module.finrank ℂ W = k` using `⟨_, S, ⟨le_rfl, hne, hTS⟩, rfl⟩`. Take `⟨W, hPW, hWk⟩` from `Nat.find_spec hex`. Establish `hmin : ∀ W', P W' → Module.finrank ℂ W ≤ Module.finrank ℂ W'`. Introduce `W' hW'`.

Rewrite using `[hWk]`. Conclude with `Nat.find_min' hex ⟨W', hW', rfl⟩`. Establish `hWfd : FiniteDimensional ℂ W` using `Submodule.finiteDimensional_of_le hPW.1`. Establish `hscal : ∀ θ, ∃ c : ℂ, ∀ v ∈ W, T θ v = c • v`. Introduce `θ`.

Establish `: Nontrivial W` using `Submodule.nontrivial_iff_ne_bot.mpr hPW.2.1`. Set `f : Module.End ℂ W` to `(T θ : H →ₗ[ℂ] H).restrict (fun v hv => hPW.2.2 θ v hv)`. Take `⟨c, hc⟩` from `Module.End.exists_eigenvalue f`. Take `⟨x, hx⟩` from `hc.exists_hasEigenvector`. Establish `hx1 : f x = c • x` using `Module.End.mem_eigenspace_iff.mp hx.1`.

Establish `hx3 : T θ x = c • (x : H)`. Use `congrArg Subtype.val hx1` as an intermediate fact. Simplify `this` using `[f]`. Set `E : Submodule ℂ H` to `W ⊓ Module.End.eigenspace (T θ : H →ₗ[ℂ] H) c`. Establish `hPE : P E`.

Use `⟨inf_le_left.trans hPW.1, ?_, ?_⟩` and prove the remaining obligations. Introduce `h`. Establish `: (x : H) ∈ E` using `⟨x.2, Module.End.mem_eigenspace_iff.mpr hx3⟩`. Rewrite `this` using `[h, Submodule.mem_bot]`. Conclude with `hx.2 (Subtype.ext this)`.

Introduce `θ' u hu`. Establish `h2 : T θ u = c • u` using `Module.End.mem_eigenspace_iff.mp hu.2`. Use `⟨hPW.2.2 θ' u hu.1, Module.End.mem_eigenspace_iff.mpr ?_⟩` and prove the remaining obligations. Use `show T θ (T θ' u) = c • T θ' u`. Rewrite using `[hTcomm, h2, map_smul]`.

Establish `hEW : E = W` using `Submodule.eq_of_le_of_finrank_le inf_le_left (hmin E hPE)`. Use `⟨c, fun v hv => ?_⟩` and prove the remaining obligations. Establish `: v ∈ E` using `hEW ▸ hv`. Conclude with `Module.End.mem_eigenspace_iff.mp this.2`. Take `⟨v, hvW, hv0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hPW.2.1`.

Establish `hvv : (inner ℂ v v : ℂ) ≠ 0` using `inner_self_ne_zero.mpr hv0`. Use `set χ : (Fin n → ℝ) → ℂ := fun θ => inner ℂ v (T θ v) / inner ℂ v v with hχ`. Establish `hTv : ∀ θ, T θ v = χ θ • v`. Introduce `θ`. Take `⟨c, hc⟩` from `hscal θ`.

Rewrite using `[hc v hvW, hχ]`. Simplify using `only [hc v hvW, inner_smul_right]`. Rewrite using `[mul_div_cancel_right₀ _ hvv]`. Establish `hχeq : ∀ θ c, T θ v = c • v → χ θ = c`. Introduce `θ c h`.

Use `hTv θ` as an intermediate fact. Rewrite `this` using `[h]`. Conclude with `(smul_left_injective ℂ hv0 this).symm`. Establish `hχadd : ∀ θ θ', χ (θ + θ') = χ θ * χ θ'`. Introduce `θ θ'`.

Apply `hχeq` to reduce the goal to its premises. Rewrite using `[hTadd, hTv θ', map_smul, hTv θ, smul_smul, mul_comm]`. Establish `hχcont : Continuous χ`. Establish `h1 : Continuous fun θ => T θ v` using `(hcont v).comp_continuous continuous_dT hmem`. Conclude with `(continuous_const.inner h1).div_const _`.

Establish `hχ2 : ∀ a, χ (Pi.single a (2 * Real.pi)) = 1`. Introduce `a`. Apply `hχeq` to reduce the goal to its premises. Simplify using `only [hT, dT_two_pi, hrep.1, ContinuousLinearMap.one_apply, one_smul]`. Establish `hχ0 : χ 0 = 1`.

Apply `hχeq` to reduce the goal to its premises. Simplify using `only [hT, dT_zero, hrep.1, ContinuousLinearMap.one_apply, one_smul]`. Establish `hcoord : ∀ a, ∃ m : ℤ, ∀ t : ℝ, χ (Pi.single a t) = Complex.exp (((m * t : ℝ) : ℂ) * Complex.I)`. Introduce `a`. Use `charR_eq_exp (fun t => χ (Pi.single a t)) ?_ ?_ ?_ (hχ2 a)` and prove the remaining obligations.

Conclude with `hχcont.comp (continuous_single (A := fun _ : Fin n => ℝ) a)`. Introduce `s t`. Use `show χ _ = χ _ * χ _`. Rewrite using `[Pi.single_add, hχadd]`. Simplify using `only [Pi.single_zero, hχ0]`.

Use `choose m hm using hcoord`. Establish `hprod : ∀ (s : Finset (Fin n)) (θ : Fin n → ℝ), χ (∑ a ∈ s, Pi.single a (θ a)) = ∏ a ∈ s, χ (Pi.single a (θ a))`. Introduce `s θ`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [hχ0]`.

Consider the case `insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, hχadd, ih]`. Use `⟨fun a => (m a : ℝ), v, hPW.1 hvW, hv0, ?_⟩` and prove the remaining obligations. Introduce `θ _`. Establish `h1 : ρ (Matrix.diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I)) v = T θ v` using `rfl`. Rewrite using `[h1, hTv]`.

Use `congr 1`. Establish `hθ : θ = ∑ a, Pi.single a (θ a)` using `(Finset.univ_sum_single θ).symm`. Rewrite using `[hθ, hprod]`. Simplify using `only [hm]`. Rewrite using `[← Complex.exp_sum]`.

Use `congr 1`. Use `push_cast`. Rewrite using `[Finset.sum_mul]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `a _`.

Simplify using `[Finset.sum_apply, Pi.single_apply]`.
-/
theorem exists_torus_weight_vector : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.QuantumDeterminants.IsCRepOn (Formalism.MainNotions.S.UJset ε) ρ →
    (∀ v, ContinuousOn (fun g => ρ g v) (Formalism.MainNotions.S.UJset ε)) → (∀ k ∈ Formalism.REAL.Kset ε, ∀ v, ‖ρ k v‖ = ‖v‖) →
    ∀ S : Submodule ℂ H, FiniteDimensional ℂ S → Formalism.MainNotions.S.IsKStableOn ε ρ S → S ≠ ⊥ →
    ∃ (μ : Fin n → ℝ) (v : H), v ∈ S ∧ v ≠ 0 ∧ Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) ρ μ v := by
  intro n ε H _ _ ρ hrep hcont _ S hfd hstab hne
  classical
  set T : (Fin n → ℝ) → (H →L[ℂ] H) := fun θ => ρ (dT θ) with hT
  have hmem : ∀ θ, dT θ ∈ Formalism.MainNotions.S.UJset ε := fun θ => Kset_sub_UJset ε _ (dT_mem_Kset ε θ)
  have hTadd : ∀ θ θ' v, T (θ + θ') v = T θ (T θ' v) := by
    intro θ θ' v
    simp only [hT, dT_add, hrep.2 _ (hmem θ) _ (hmem θ'), ContinuousLinearMap.comp_apply]
  have hTcomm : ∀ θ θ' v, T θ (T θ' v) = T θ' (T θ v) := by
    intro θ θ' v; rw [← hTadd, ← hTadd, add_comm]
  have hTS : ∀ θ, ∀ v ∈ S, T θ v ∈ S := fun θ v hv => hstab _ (dT_mem_Kset ε θ) v hv

  let P : Submodule ℂ H → Prop := fun W => W ≤ S ∧ W ≠ ⊥ ∧ ∀ θ, ∀ v ∈ W, T θ v ∈ W
  have hex : ∃ k, ∃ W, P W ∧ Module.finrank ℂ W = k := ⟨_, S, ⟨le_rfl, hne, hTS⟩, rfl⟩
  obtain ⟨W, hPW, hWk⟩ := Nat.find_spec hex
  have hmin : ∀ W', P W' → Module.finrank ℂ W ≤ Module.finrank ℂ W' := by
    intro W' hW'; rw [hWk]; exact Nat.find_min' hex ⟨W', hW', rfl⟩
  have hWfd : FiniteDimensional ℂ W := Submodule.finiteDimensional_of_le hPW.1

  have hscal : ∀ θ, ∃ c : ℂ, ∀ v ∈ W, T θ v = c • v := by
    intro θ
    have : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hPW.2.1
    let f : Module.End ℂ W := (T θ : H →ₗ[ℂ] H).restrict (fun v hv => hPW.2.2 θ v hv)
    obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue f
    obtain ⟨x, hx⟩ := hc.exists_hasEigenvector
    have hx1 : f x = c • x := Module.End.mem_eigenspace_iff.mp hx.1
    have hx3 : T θ x = c • (x : H) := by
      have := congrArg Subtype.val hx1
      simpa [f] using this
    let E : Submodule ℂ H := W ⊓ Module.End.eigenspace (T θ : H →ₗ[ℂ] H) c
    have hPE : P E := by
      refine ⟨inf_le_left.trans hPW.1, ?_, ?_⟩
      · intro h
        have : (x : H) ∈ E := ⟨x.2, Module.End.mem_eigenspace_iff.mpr hx3⟩
        rw [h, Submodule.mem_bot] at this
        exact hx.2 (Subtype.ext this)
      · intro θ' u hu
        have h2 : T θ u = c • u := Module.End.mem_eigenspace_iff.mp hu.2
        refine ⟨hPW.2.2 θ' u hu.1, Module.End.mem_eigenspace_iff.mpr ?_⟩
        show T θ (T θ' u) = c • T θ' u
        rw [hTcomm, h2, map_smul]
    have hEW : E = W := Submodule.eq_of_le_of_finrank_le inf_le_left (hmin E hPE)
    refine ⟨c, fun v hv => ?_⟩
    have : v ∈ E := hEW ▸ hv
    exact Module.End.mem_eigenspace_iff.mp this.2
  obtain ⟨v, hvW, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hPW.2.1
  have hvv : (inner ℂ v v : ℂ) ≠ 0 := inner_self_ne_zero.mpr hv0
  set χ : (Fin n → ℝ) → ℂ := fun θ => inner ℂ v (T θ v) / inner ℂ v v with hχ
  have hTv : ∀ θ, T θ v = χ θ • v := by
    intro θ
    obtain ⟨c, hc⟩ := hscal θ
    rw [hc v hvW, hχ]
    simp only [hc v hvW, inner_smul_right]
    rw [mul_div_cancel_right₀ _ hvv]
  have hχeq : ∀ θ c, T θ v = c • v → χ θ = c := by
    intro θ c h
    have := hTv θ
    rw [h] at this
    exact (smul_left_injective ℂ hv0 this).symm
  have hχadd : ∀ θ θ', χ (θ + θ') = χ θ * χ θ' := by
    intro θ θ'
    apply hχeq
    rw [hTadd, hTv θ', map_smul, hTv θ, smul_smul, mul_comm]
  have hχcont : Continuous χ := by
    have h1 : Continuous fun θ => T θ v :=
      (hcont v).comp_continuous continuous_dT hmem
    exact (continuous_const.inner h1).div_const _
  have hχ2 : ∀ a, χ (Pi.single a (2 * Real.pi)) = 1 := by
    intro a; apply hχeq
    simp only [hT, dT_two_pi, hrep.1, ContinuousLinearMap.one_apply, one_smul]
  have hχ0 : χ 0 = 1 := by
    apply hχeq; simp only [hT, dT_zero, hrep.1, ContinuousLinearMap.one_apply, one_smul]

  have hcoord : ∀ a, ∃ m : ℤ, ∀ t : ℝ, χ (Pi.single a t) = Complex.exp (((m * t : ℝ) : ℂ) * Complex.I) := by
    intro a
    refine charR_eq_exp (fun t => χ (Pi.single a t)) ?_ ?_ ?_ (hχ2 a)
    · exact hχcont.comp (continuous_single (A := fun _ : Fin n => ℝ) a)
    · intro s t; show χ _ = χ _ * χ _; rw [Pi.single_add, hχadd]
    · simp only [Pi.single_zero, hχ0]
  choose m hm using hcoord
  have hprod : ∀ (s : Finset (Fin n)) (θ : Fin n → ℝ), χ (∑ a ∈ s, Pi.single a (θ a)) = ∏ a ∈ s, χ (Pi.single a (θ a)) := by
    intro s θ
    induction s using Finset.induction_on with
    | empty => simp [hχ0]
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, hχadd, ih]
  refine ⟨fun a => (m a : ℝ), v, hPW.1 hvW, hv0, ?_⟩
  intro θ _
  have h1 : ρ (Matrix.diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I)) v = T θ v := rfl
  rw [h1, hTv]
  congr 1
  have hθ : θ = ∑ a, Pi.single a (θ a) := (Finset.univ_sum_single θ).symm
  rw [hθ, hprod]
  simp only [hm]
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  simp [Finset.sum_apply, Pi.single_apply]

end GlobalTheory.TorusWtExist
