import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.HahnPowOrderLeadingCoeff
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
import Development.AbelianVarietyTheory.Definitions.Foundations.SiegelNeZeroIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelUnitQExpansionCoefficients
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.QuotientIntegralHolomorphic
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UpperHalfPlaneCodiscreteGermIdentityAndUnits
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularTowerFunctionSlTwoIntInvariantStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularTowerFunctionTendstoConstTermExponentialStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ConstOfSlTwoIntInvariantBoundedUpperHalfPlaneStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HahnSeriesPowOfLeadingQInvStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteDimensionalFixedFieldMapOfFiniteIndexStatement

noncomputable section
open scoped MatrixGroups
open GlobalTheory.KZ

namespace GlobalTheory.K4.LevFin

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

/- English proof (translation)
Use `set Y := max y 0 + 1 with hY`. Use `set w : ℂ := Complex.I * Y`. Establish `hwim : w.im = Y` using `by simp [w]`. Establish `h0Y : 0 ≤ max y 0` using `le_max_right _ _`. Establish `hyY : y ≤ max y 0` using `le_max_left _ _`.

Establish `hw : w ∈ Hs` using `by show 0 < w.im`. Rewrite using `[hwim]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h1` using `mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp hS w hw`. Establish `h2 : {z : ℂ | max y 0 < z.im} ∈ nhdsWithin w {w}ᶜ` using `nhdsWithin_le_nhds ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds (show max y 0 < w.im by rw [hwim]; linarith))`.

Take `⟨z, hz1, hz2⟩` from `Filter.nonempty_of_mem (Filter.inter_mem h1 h2)`. Establish `hz2' : max y 0 < z.im` using `hz2`. Break down `hz1 with h | h` into its components or cases. Conclude with `⟨z, h, by linarith⟩`. Conclude with `absurd (show 0 < z.im by linarith) h`.
-/
theorem exists_im_gt {S : Set ℂ} (hS : S ∈ Filter.codiscreteWithin Hs) (y : ℝ) : ∃ z ∈ S, y < z.im := by
  set Y := max y 0 + 1 with hY
  set w : ℂ := Complex.I * Y
  have hwim : w.im = Y := by simp [w]
  have h0Y : 0 ≤ max y 0 := le_max_right _ _
  have hyY : y ≤ max y 0 := le_max_left _ _
  have hw : w ∈ Hs := by
    show 0 < w.im
    rw [hwim]; linarith
  have h1 := mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp hS w hw
  have h2 : {z : ℂ | max y 0 < z.im} ∈ nhdsWithin w {w}ᶜ :=
    nhdsWithin_le_nhds ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds
      (show max y 0 < w.im by rw [hwim]; linarith))
  obtain ⟨z, hz1, hz2⟩ := Filter.nonempty_of_mem (Filter.inter_mem h1 h2)
  have hz2' : max y 0 < z.im := hz2
  rcases hz1 with h | h
  · exact ⟨z, h, by linarith⟩
  · exact absurd (show 0 < z.im by linarith) h

/- English proof (translation)
Take `⟨φ, C, hφ, hsum⟩` from `X.an_exp h`. Establish `hmob : ∀ z : ℂ, mob (ofSL ModularGroup.T) z = z + 1`. Introduce `z`. Establish `he : ∀ i j, ent (ofSL ModularGroup.T) i j = ((ModularGroup.T : Matrix (Fin 2) (Fin 2) ℤ) i j : ℚ)` using `fun _ _ => rfl`. Simplify using `[mob, he, ModularGroup.coe_T]`.

Establish `h1` using `X.an_sl (ofSL ModularGroup.T) h φ hφ`. Rewrite `h1` using `[hT, hφ]`. Simplify using `only [hmob] at h1`. Establish `hev : {z : ℂ | φ z = φ (z + 1)} ∈ Filter.codiscreteWithin Hs` using `Filter.Germ.coe_eq.mp h1`. Set `d : ℚ → ℂ` to `fun r => ε ((X.exp h).coeff r) * (Complex.exp (2 * Real.pi * Complex.I * (r : ℂ)) - 1)`.

Establish `hs : ∀ z : ℂ, C < z.im → HasSum (fun r : ℚ => d r * Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * z)) (φ (z + 1) - φ z)`. Introduce `z hz`. Use `(hsum (z + 1) (by simpa using hz)).sub (hsum z hz)` as an intermediate fact. Establish `e : (fun r : ℚ => d r * Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * z)) = fun r : ℚ => ε ((X.exp h).coeff r) * Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * (z + 1)) - ε ((X.exp h).coeff r) * Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * z)`. Use function extensionality and compare the values at `r`.

Simplify using `only [d]`. Rewrite using `[mul_add, mul_one, Complex.exp_add]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `this`.

Establish `hd : d = 0`. Use `GlobalTheory.KExp.uniq d ?_ {z | C < z.im ∧ φ z = φ (z + 1)} ?_ (Complex.I * (|C| + 1)) ?_ ?_` and prove the remaining obligations. Use `(X.exp h).isWF_support.mono ?_` and prove the remaining obligations. Introduce `r hr`. Assume the negation of the conclusion as `hn`.

Apply `hr` to reduce the goal to its premises. Establish `: (X.exp h).coeff r = 0` using `by simpa [HahnSeries.support] using hn`. Simplify using `[d, this]`. Introduce `z hz`. Use `hs z hz.1` as an intermediate fact.

Rewrite `this` using `[← hz.2, sub_self]`. Then use the resulting hypothesis. Use `(hs _ ?_).summable simp` and prove the remaining obligations. Use `le_abs_self C` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `y`.

Take `⟨z, hz, hy⟩` from `exists_im_gt hev (max y C)`. Conclude with `⟨z, ⟨lt_of_le_of_lt (le_max_right _ _) hy, hz⟩, lt_of_le_of_lt (le_max_left _ _) hy⟩`. Establish `h2` using `congrFun hd r`. Simplify using `only [d, Pi.zero_apply, mul_eq_zero, map_eq_zero, hr, false_or, sub_eq_zero] at h2`. Take `⟨n, hn⟩` from `Complex.exp_eq_one_iff.mp h2`.

Use `⟨n, ?_⟩` and prove the remaining obligations. Establish `h3 : (r : ℂ) = n`. Establish `hne : (2 * Real.pi * Complex.I : ℂ) ≠ 0` using `Complex.two_pi_I_ne_zero`. Apply `mul_left_cancel₀ hne` to reduce the goal to its premises. Rewrite using `[hn]`.

Expand and normalize the polynomial expressions, which then agree. Conclude with `h3` after adjusting the coercions.
-/
theorem exponent_int (X : Tower Ω ε) (h : X.K) (hT : X.sl (ofSL ModularGroup.T) h = h) (r : ℚ)
    (hr : (X.exp h).coeff r ≠ 0) : ∃ m : ℤ, r = m := by
  obtain ⟨φ, C, hφ, hsum⟩ := X.an_exp h
  have hmob : ∀ z : ℂ, mob (ofSL ModularGroup.T) z = z + 1 := by
    intro z
    have he : ∀ i j, ent (ofSL ModularGroup.T) i j = ((ModularGroup.T : Matrix (Fin 2) (Fin 2) ℤ) i j : ℚ) :=
      fun _ _ => rfl
    simp [mob, he, ModularGroup.coe_T]
  have h1 := X.an_sl (ofSL ModularGroup.T) h φ hφ
  rw [hT, hφ] at h1
  simp only [hmob] at h1
  have hev : {z : ℂ | φ z = φ (z + 1)} ∈ Filter.codiscreteWithin Hs := Filter.Germ.coe_eq.mp h1
  let d : ℚ → ℂ := fun r => ε ((X.exp h).coeff r) * (Complex.exp (2 * Real.pi * Complex.I * (r : ℂ)) - 1)
  have hs : ∀ z : ℂ, C < z.im →
      HasSum (fun r : ℚ => d r * Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * z)) (φ (z + 1) - φ z) := by
    intro z hz
    have := (hsum (z + 1) (by simpa using hz)).sub (hsum z hz)
    have e : (fun r : ℚ => d r * Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * z)) = fun r : ℚ =>
        ε ((X.exp h).coeff r) * Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * (z + 1)) -
          ε ((X.exp h).coeff r) * Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * z) := by
      funext r
      simp only [d]
      rw [mul_add, mul_one, Complex.exp_add]
      ring
    rw [e]
    exact this
  have hd : d = 0 := by
    refine GlobalTheory.KExp.uniq d ?_ {z | C < z.im ∧ φ z = φ (z + 1)} ?_ (Complex.I * (|C| + 1)) ?_ ?_
    · refine (X.exp h).isWF_support.mono ?_
      intro r hr
      by_contra hn
      apply hr
      have : (X.exp h).coeff r = 0 := by simpa [HahnSeries.support] using hn
      simp [d, this]
    · intro z hz
      have := hs z hz.1
      rwa [← hz.2, sub_self] at this
    · refine (hs _ ?_).summable
      simp; have := le_abs_self C; linarith
    · intro y
      obtain ⟨z, hz, hy⟩ := exists_im_gt hev (max y C)
      exact ⟨z, ⟨lt_of_le_of_lt (le_max_right _ _) hy, hz⟩, lt_of_le_of_lt (le_max_left _ _) hy⟩
  have h2 := congrFun hd r
  simp only [d, Pi.zero_apply, mul_eq_zero, map_eq_zero, hr, false_or, sub_eq_zero] at h2
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h2
  refine ⟨n, ?_⟩
  have h3 : (r : ℂ) = n := by
    have hne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
    apply mul_left_cancel₀ hne
    rw [hn]; ring
  exact_mod_cast h3

/- English proof (translation)
Use `set a0 := (X.exp h).coeff 0 with ha0`. Establish `hsupp : ∀ r : ℚ, (X.exp h).coeff r ≠ 0 → ∃ n : ℕ, r = n`. Introduce `r hr`. Take `⟨m, rfl⟩` from `exponent_int X h (hinv _) r hr`. Establish `hm : 0 ≤ m`.

Assume the negation of the conclusion as `hm`. Conclude with `hr (hneg _ (by exact_mod_cast (not_le.1 hm)))`. Conclude with `⟨m.toNat, by rw [← Int.cast_natCast, Int.toNat_of_nonneg hm]⟩`. Take `⟨B, t, hB⟩` from `GlobalTheory.T.modularTower_function_tendsto_constTerm_exponential X h φ hd.continuousOn ha hsupp`. Establish `hinvφ` using `GlobalTheory.T.modularTower_function_slTwoInt_invariant X h φ hd.continuousOn ha hinv`.

Establish `hexp1 : ∀ z : ℂ, t < z.im → Real.exp (-(2 * Real.pi * (z.im - t))) ≤ 1`. Introduce `z hz`. Rewrite using `[Real.exp_le_one_iff]`. Establish `: 0 < z.im - t` using `by linarith`. Use `Real.pi_pos` as an intermediate fact.

Use the polynomial consequences of the given equalities and inequalities. Take `⟨c, hc⟩` from `GlobalTheory.T.const_of_slTwoInt_invariant_bounded_upperHalfPlane φ hd hinvφ ⟨‖ε a0‖ + |B|, t, fun z hz hzt => by`. Establish `h1` using `hB z hz hzt`. Establish `h2` using `hexp1 z hzt`. Establish `h3 : B * Real.exp (-(2 * Real.pi * (z.im - t))) ≤ |B|`.

Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation. Establish `hca : c = ε a0`. Establish `hle : ∀ s : ℝ, max t 0 < s → ‖c - ε a0‖ ≤ B * Real.exp (-(2 * Real.pi * (s - t)))`. Introduce `s hs`.

Establish `hs0 : 0 < s` using `lt_of_le_of_lt (le_max_right _ _) hs`. Establish `hst : t < s` using `lt_of_le_of_lt (le_max_left _ _) hs`. Establish `hz : ((s : ℂ) * Complex.I) ∈ Hs` using `by simp [Hs, hs0]`. Use `hB _ hz (by simpa using hst)` as an intermediate fact. Rewrite `this` using `[hc _ hz]`.

Simplify using `using this`. Establish `ht : Filter.Tendsto (fun s : ℝ => B * Real.exp (-(2 * Real.pi * (s - t)))) Filter.atTop (nhds 0)`. Establish `h1 : Filter.Tendsto (fun s : ℝ => 2 * Real.pi * (s - t)) Filter.atTop Filter.atTop`. Apply `Filter.Tendsto.const_mul_atTop Real.two_pi_pos` to reduce the goal to its premises. Conclude with `Filter.tendsto_atTop_add_const_right _ _ Filter.tendsto_id`.

Establish `h2` using `(Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).const_mul B`. Simplify using `using h2`. Establish `h0 : ‖c - ε a0‖ ≤ 0` using `ge_of_tendsto ht (Filter.eventually_gt_atTop (max t 0) |>.mono hle)`. Use `norm_le_zero_iff.1 h0` as an intermediate fact. Conclude with `sub_eq_zero.1 this`.

Apply `SiegelModel.an_injective X` to reduce the goal to its premises. Rewrite using `[ha, X.an_c]`. Conclude with `SiegelModel.germ_eq_of_eqOn fun z hz => by rw [hc z hz, hca]`.
-/
theorem eq_const_of_nonneg (X : Tower Ω ε) (h : X.K) (hinv : ∀ γ : SL(2, ℤ), X.sl (ofSL γ) h = h)
    (φ : ℂ → ℂ) (hd : DifferentiableOn ℂ φ Hs) (ha : X.an h = (φ : Mero))
    (hneg : ∀ r : ℚ, r < 0 → (X.exp h).coeff r = 0) :
    h = algebraMap Ω X.K ((X.exp h).coeff 0) := by
  set a0 := (X.exp h).coeff 0 with ha0
  have hsupp : ∀ r : ℚ, (X.exp h).coeff r ≠ 0 → ∃ n : ℕ, r = n := by
    intro r hr
    obtain ⟨m, rfl⟩ := exponent_int X h (hinv _) r hr
    have hm : 0 ≤ m := by
      by_contra hm
      exact hr (hneg _ (by exact_mod_cast (not_le.1 hm)))
    exact ⟨m.toNat, by rw [← Int.cast_natCast, Int.toNat_of_nonneg hm]⟩
  obtain ⟨B, t, hB⟩ := GlobalTheory.T.modularTower_function_tendsto_constTerm_exponential X h φ hd.continuousOn ha hsupp
  have hinvφ := GlobalTheory.T.modularTower_function_slTwoInt_invariant X h φ hd.continuousOn ha hinv
  have hexp1 : ∀ z : ℂ, t < z.im → Real.exp (-(2 * Real.pi * (z.im - t))) ≤ 1 := by
    intro z hz
    rw [Real.exp_le_one_iff]
    have : 0 < z.im - t := by linarith
    have := Real.pi_pos
    nlinarith
  obtain ⟨c, hc⟩ := GlobalTheory.T.const_of_slTwoInt_invariant_bounded_upperHalfPlane φ hd hinvφ ⟨‖ε a0‖ + |B|, t, fun z hz hzt => by
    have h1 := hB z hz hzt
    have h2 := hexp1 z hzt
    have h3 : B * Real.exp (-(2 * Real.pi * (z.im - t))) ≤ |B| := by
      calc B * Real.exp (-(2 * Real.pi * (z.im - t))) ≤ |B| * Real.exp (-(2 * Real.pi * (z.im - t))) :=
            mul_le_mul_of_nonneg_right (le_abs_self B) (Real.exp_pos _).le
        _ ≤ |B| * 1 := mul_le_mul_of_nonneg_left h2 (abs_nonneg B)
        _ = |B| := mul_one _
    calc ‖φ z‖ = ‖(φ z - ε a0) + ε a0‖ := by ring_nf
      _ ≤ ‖φ z - ε a0‖ + ‖ε a0‖ := norm_add_le _ _
      _ ≤ ‖ε a0‖ + |B| := by linarith⟩
  have hca : c = ε a0 := by
    have hle : ∀ s : ℝ, max t 0 < s → ‖c - ε a0‖ ≤ B * Real.exp (-(2 * Real.pi * (s - t))) := by
      intro s hs
      have hs0 : 0 < s := lt_of_le_of_lt (le_max_right _ _) hs
      have hst : t < s := lt_of_le_of_lt (le_max_left _ _) hs
      have hz : ((s : ℂ) * Complex.I) ∈ Hs := by simp [Hs, hs0]
      have := hB _ hz (by simpa using hst)
      rw [hc _ hz] at this
      simpa using this
    have ht : Filter.Tendsto (fun s : ℝ => B * Real.exp (-(2 * Real.pi * (s - t)))) Filter.atTop (nhds 0) := by
      have h1 : Filter.Tendsto (fun s : ℝ => 2 * Real.pi * (s - t)) Filter.atTop Filter.atTop := by
        apply Filter.Tendsto.const_mul_atTop Real.two_pi_pos
        exact Filter.tendsto_atTop_add_const_right _ _ Filter.tendsto_id
      have h2 := (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).const_mul B
      simpa using h2
    have h0 : ‖c - ε a0‖ ≤ 0 := ge_of_tendsto ht (Filter.eventually_gt_atTop (max t 0) |>.mono hle)
    have := norm_le_zero_iff.1 h0
    exact sub_eq_zero.1 this
  apply SiegelModel.an_injective X
  rw [ha, X.an_c]
  exact SiegelModel.germ_eq_of_eqOn fun z hz => by rw [hc z hz, hca]

/- English proof (translation)
Take `⟨ψ, hψa, hψ⟩` from `X.j_hol`. Establish `key : ∀ n : ℕ, ∀ h : X.K, (∀ γ : SL(2, ℤ), X.sl (ofSL γ) h = h) → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an h = (φ : Mero)) → (∀ r : ℚ, r < -(n : ℚ) → (X.exp h).coeff r = 0) → h ∈ Algebra.adjoin Ω {X.jK}`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`.

Introduce `h hinv hol hneg`. Take `⟨φ, hd, ha⟩` from `hol`. Rewrite using `[eq_const_of_nonneg X h hinv φ hd ha (by simpa using hneg)]`. Conclude with `Subalgebra.algebraMap_mem _ _`. Consider the case `succ n ih`.

Introduce `h hinv hol hneg`. Take `⟨φ, hd, ha⟩` from `hol`. Take `⟨c, hcdef⟩ : ∃ c : Ω, c = (X.exp h).coeff (-((n + 1 : ℕ) : ℚ))` from `⟨_, rfl⟩`. Take `⟨h', hh'⟩ : ∃ h' : X.K, h' = h - algebraMap Ω X.K c * X.jK ^ (n + 1)` from `⟨_, rfl⟩`. Establish `hj` using `GlobalTheory.T.hahnSeries_pow_of_leading_qInv (X.exp X.jK) X.j_exp.1 X.j_exp.2.1 (n + 1)`.

Establish `hinv' : ∀ γ : SL(2, ℤ), X.sl (ofSL γ) h' = h'`. Introduce `γ`. Rewrite using `[hh', map_sub, map_mul, map_pow, X.j_inv, hinv, AlgEquiv.commutes]`. Establish `hol' : ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an h' = (φ : Mero)`. Use `⟨fun z => φ z - ε c * ψ z ^ (n + 1), ?_, ?_⟩` and prove the remaining obligations.

Conclude with `hd.sub ((hψ.pow _).const_mul _)`. Rewrite using `[hh', map_sub, map_mul, map_pow, X.an_c, ha, hψa]`. Both sides reduce to the same expression. Establish `hneg' : ∀ r : ℚ, r < -(n : ℚ) → (X.exp h').coeff r = 0`. Introduce `r hr`.

Assume the negation of the conclusion as `hrz`. Take `⟨m, rfl⟩` from `exponent_int X h' (hinv' _) r hrz`. Apply `hrz` to reduce the goal to its premises. Establish `hcoe : (X.exp h').coeff (m : ℚ) = (X.exp h).coeff m - c * ((X.exp X.jK) ^ (n + 1)).coeff m`. Rewrite using `[hh', map_sub, map_mul, AlgHom.commutes, map_pow, HahnSeries.coeff_sub, HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, HahnSeries.ofPowerSeries_C, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]`.

Rewrite using `[hcoe]`. Establish `hm : m ≤ -((n : ℤ) + 1)`. Establish `: (m : ℚ) < -(n : ℚ)` using `hr`. Establish `: m < -(n : ℤ)` using `by exact_mod_cast this`. Use linear arithmetic over natural numbers and integers.

Break down `hm.lt_or_eq with hlt | heq` into its components or cases. Establish `hq : (m : ℚ) < -((n + 1 : ℕ) : ℚ)` using `by push_cast; exact_mod_cast hlt`. Rewrite using `[hneg _ hq, hj.2 _ hq]`. Expand and normalize the polynomial expressions, which then agree. Establish `hq : (m : ℚ) = -((n + 1 : ℕ) : ℚ)` using `by rw [heq]; push_cast; ring`.

Rewrite using `[hq, hj.1, hcdef]`. Expand and normalize the polynomial expressions, which then agree. Establish `hmem` using `ih h' hinv' hol' hneg'`. Establish `hsum : h = h' + algebraMap Ω X.K c * X.jK ^ (n + 1)` using `by rw [hh']; abel`. Establish `hjm : X.jK ∈ Algebra.adjoin Ω {X.jK}` using `Algebra.self_mem_adjoin_singleton Ω X.jK`.

Rewrite using `[hsum]`. Conclude with `add_mem hmem (mul_mem (Subalgebra.algebraMap_mem _ _) (pow_mem hjm _))`. Introduce `h hinv hol`. Use `key ⌈-(X.exp h).order⌉₊ h hinv hol fun r hr => HahnSeries.coeff_eq_zero_of_lt_order ?_` and prove the remaining obligations. Use `Nat.le_ceil (-(X.exp h).order)` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem mem_adjoin_j (X : Tower Ω ε) : ∀ h : X.K,
    (∀ γ : SL(2, ℤ), X.sl (ofSL γ) h = h) → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an h = (φ : Mero)) →
    h ∈ Algebra.adjoin Ω {X.jK} := by
  obtain ⟨ψ, hψa, hψ⟩ := X.j_hol
  have key : ∀ n : ℕ, ∀ h : X.K, (∀ γ : SL(2, ℤ), X.sl (ofSL γ) h = h) →
      (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an h = (φ : Mero)) →
      (∀ r : ℚ, r < -(n : ℚ) → (X.exp h).coeff r = 0) → h ∈ Algebra.adjoin Ω {X.jK} := by
    intro n
    induction n with
    | zero =>
      intro h hinv hol hneg
      obtain ⟨φ, hd, ha⟩ := hol
      rw [eq_const_of_nonneg X h hinv φ hd ha (by simpa using hneg)]
      exact Subalgebra.algebraMap_mem _ _
    | succ n ih =>
      intro h hinv hol hneg
      obtain ⟨φ, hd, ha⟩ := hol
      obtain ⟨c, hcdef⟩ : ∃ c : Ω, c = (X.exp h).coeff (-((n + 1 : ℕ) : ℚ)) := ⟨_, rfl⟩
      obtain ⟨h', hh'⟩ : ∃ h' : X.K, h' = h - algebraMap Ω X.K c * X.jK ^ (n + 1) := ⟨_, rfl⟩
      have hj := GlobalTheory.T.hahnSeries_pow_of_leading_qInv (X.exp X.jK) X.j_exp.1 X.j_exp.2.1 (n + 1)
      have hinv' : ∀ γ : SL(2, ℤ), X.sl (ofSL γ) h' = h' := by
        intro γ
        rw [hh', map_sub, map_mul, map_pow, X.j_inv, hinv, AlgEquiv.commutes]
      have hol' : ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an h' = (φ : Mero) := by
        refine ⟨fun z => φ z - ε c * ψ z ^ (n + 1), ?_, ?_⟩
        · exact hd.sub ((hψ.pow _).const_mul _)
        · rw [hh', map_sub, map_mul, map_pow, X.an_c, ha, hψa]
          rfl
      have hneg' : ∀ r : ℚ, r < -(n : ℚ) → (X.exp h').coeff r = 0 := by
        intro r hr
        by_contra hrz
        obtain ⟨m, rfl⟩ := exponent_int X h' (hinv' _) r hrz
        apply hrz
        have hcoe : (X.exp h').coeff (m : ℚ) =
            (X.exp h).coeff m - c * ((X.exp X.jK) ^ (n + 1)).coeff m := by
          rw [hh', map_sub, map_mul, AlgHom.commutes, map_pow, HahnSeries.coeff_sub, HahnSeries.algebraMap_apply',
            PowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, HahnSeries.ofPowerSeries_C,
            HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]
        rw [hcoe]
        have hm : m ≤ -((n : ℤ) + 1) := by
          have : (m : ℚ) < -(n : ℚ) := hr
          have : m < -(n : ℤ) := by exact_mod_cast this
          omega
        rcases hm.lt_or_eq with hlt | heq
        · have hq : (m : ℚ) < -((n + 1 : ℕ) : ℚ) := by push_cast; exact_mod_cast hlt
          rw [hneg _ hq, hj.2 _ hq]
          ring
        · have hq : (m : ℚ) = -((n + 1 : ℕ) : ℚ) := by rw [heq]; push_cast; ring
          rw [hq, hj.1, hcdef]
          ring
      have hmem := ih h' hinv' hol' hneg'
      have hsum : h = h' + algebraMap Ω X.K c * X.jK ^ (n + 1) := by rw [hh']; abel
      have hjm : X.jK ∈ Algebra.adjoin Ω {X.jK} := Algebra.self_mem_adjoin_singleton Ω X.jK
      rw [hsum]
      exact add_mem hmem (mul_mem (Subalgebra.algebraMap_mem _ _) (pow_mem hjm _))
  intro h hinv hol
  refine key ⌈-(X.exp h).order⌉₊ h hinv hol fun r hr => HahnSeries.coeff_eq_zero_of_lt_order ?_
  have := Nat.le_ceil (-(X.exp h).order)
  linarith

/- English proof (translation)
Proceed by induction on `hb using Algebra.adjoin_induction with`. Consider the case `mem x hx`. Take `⟨ψ, hψa, hψ⟩` from `X.j_hol`. Rewrite using `[Set.mem_singleton_iff.1 hx]`. Conclude with `⟨ψ, hψ, hψa⟩`.

Consider the case `algebraMap c => exact ⟨fun _ => ε c, differentiableOn_const _, X.an_c c⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨a, ha, ha'⟩` from `hx`. Take `⟨b, hb, hb'⟩` from `hy`. Conclude with `⟨a + b, ha.add hb, by rw [map_add, ha', hb']; rfl⟩`.

Consider the case `mul x y _ _ hx hy`. Take `⟨a, ha, ha'⟩` from `hx`. Take `⟨b, hb, hb'⟩` from `hy`. Conclude with `⟨a * b, ha.mul hb, by rw [map_mul, ha', hb']; rfl⟩`.
-/
theorem hol_of_mem_adjoin (X : Tower Ω ε) (b : X.K) (hb : b ∈ Algebra.adjoin Ω {X.jK}) :
    ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an b = (φ : Mero) := by
  induction hb using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨ψ, hψa, hψ⟩ := X.j_hol
    rw [Set.mem_singleton_iff.1 hx]
    exact ⟨ψ, hψ, hψa⟩
  | algebraMap c => exact ⟨fun _ => ε c, differentiableOn_const _, X.an_c c⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, ha'⟩ := hx
    obtain ⟨b, hb, hb'⟩ := hy
    exact ⟨a + b, ha.add hb, by rw [map_add, ha', hb']; rfl⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, ha, ha'⟩ := hx
    obtain ⟨b, hb, hb'⟩ := hy
    exact ⟨a * b, ha.mul hb, by rw [map_mul, ha', hb']; rfl⟩

/- English proof (translation)
Establish `hcongr` using `@SiegelModel.germ_eq_of_eqOn`. Establish `hid` using `GlobalTheory.FN.germ_main.2.1`. Establish `hunit` using `GlobalTheory.FN.germ_main.2.2`. Take `⟨P, hPm, hP⟩` from `hy`. Use `set n := P.natDegree with hn`.

Use `choose r hrd hran using fun i : Fin n => hol_of_mem_adjoin X _ (P.coeff i).2`. Establish `heq : X.an y ^ n + ∑ i : Fin n, ((r i : ℂ → ℂ) : Mero) * X.an y ^ (i : ℕ) = 0`. Establish `h0` using `congrArg X.an hP`. Rewrite `h0` using `[hPm.as_sum]`. Simplify using `only [Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_finset_sum, Polynomial.eval₂_mul, Polynomial.eval₂_C, map_add, map_pow, map_sum, map_mul, map_zero] at h0`.

Rewrite `h0` using `[← hn, Finset.sum_range (fun i => X.an (algebraMap _ X.K (P.coeff i)) * X.an y ^ i)]`. Rewrite using `[← h0]`. Use `congr 1`. Use `Finset.sum_congr rfl (fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[← hran i]`.

Both sides reduce to the same expression. Take `⟨a, b, ha, hb, hb0, hab⟩` from `X.an_mero y`. Establish `hbz : ∃ z ∈ Hs, b z ≠ 0`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`.

Apply `hb0` to reduce the goal to its premises. Use `hcongr (φ := b) (ψ := fun _ => 0) hc` as an intermediate fact. Rewrite using `[this]`. Both sides reduce to the same expression. Establish `hF : ((fun z => a z ^ n + ∑ i : Fin n, r i z * a z ^ (i : ℕ) * b z ^ (n - i) : ℂ → ℂ) : Mero) = 0`.

Establish `e1 : (fun z => a z ^ n + ∑ i : Fin n, r i z * a z ^ (i : ℕ) * b z ^ (n - i) : ℂ → ℂ) = a ^ n + ∑ i : Fin n, r i * a ^ (i : ℕ) * b ^ (n - i)`. Use function extensionality and compare the values at `z`. Simplify using `[Finset.sum_apply]`. Rewrite using `[e1]`. Establish `e2 : ((a ^ n + ∑ i : Fin n, r i * a ^ (i : ℕ) * b ^ (n - i) : ℂ → ℂ) : Mero) = (a : Mero) ^ n + ∑ i : Fin n, ((r i : ℂ → ℂ) : Mero) * (a : Mero) ^ (i : ℕ) * (b : Mero) ^ (n - i)`.

Use `map_add (Filter.Germ.coeRingHom (R := ℂ) (Filter.codiscreteWithin Hs)) (a ^ n) (∑ i : Fin n, r i * a ^ (i : ℕ) * b ^ (n - i))` as an intermediate fact. Simplify using `only [map_sum, map_mul, map_pow] at this`. Conclude with `this`. Rewrite using `[e2, ← hab]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[mul_add, Finset.mul_sum, mul_pow, mul_comm ((b : Mero) ^ n)]`. Use `congr 1`. Use `Finset.sum_congr rfl (fun i _ => ?_)` and prove the remaining obligations. Establish `hi : (i : ℕ) ≤ n` using `i.2.le`. Rewrite using `[mul_pow, ← pow_mul_pow_sub (b : Mero) hi]`.

Expand and normalize the polynomial expressions, which then agree. Use `_ = 0 := by rw [heq, mul_zero]`. Establish `hFd : DifferentiableOn ℂ (fun z => a z ^ n + ∑ i : Fin n, r i z * a z ^ (i : ℕ) * b z ^ (n - i)) Hs`. Use `(ha.pow n).add (DifferentiableOn.fun_sum (fun i _ => ((hrd i).mul (ha.pow _)).mul (hb.pow _)))` and prove the remaining obligations. Establish `hFz : ∀ z ∈ Hs, a z ^ n + ∑ i : Fin n, r i z * a z ^ (i : ℕ) * b z ^ (n - i) = 0`.

Introduce `z hz`. Conclude with `hid _ (fun _ => (0 : ℂ)) hFd (differentiableOn_const 0) (by rw [hF]; rfl) z hz`. Take `⟨h0, hh0, hah0, -⟩` from `GlobalTheory.quotient_integral_holomorphic Hs n a b r GlobalTheory.FN.isOpen_Hs GlobalTheory.FN.isPreconnected_Hs ha hb hrd hbz hFz`. Establish `hbu : IsUnit (b : Mero)` using `(hunit b hb hb0).2`. Use `⟨h0, hh0, ?_⟩` and prove the remaining obligations.

Establish `e : (a : Mero) = ((h0 : ℂ → ℂ) : Mero) * (b : Mero)`. Rewrite using `[hcongr (φ := a) (ψ := h0 * b) hah0]`. Both sides reduce to the same expression. Rewrite `hab` using `[e]`. Conclude with `hbu.mul_right_cancel hab`.
-/
theorem hol_of_isIntegral (X : Tower Ω ε) (y : X.K) (hy : IsIntegral (Algebra.adjoin Ω {X.jK}) y) :
    ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an y = (φ : Mero) := by
  have hcongr := @SiegelModel.germ_eq_of_eqOn
  have hid := GlobalTheory.FN.germ_main.2.1
  have hunit := GlobalTheory.FN.germ_main.2.2
  obtain ⟨P, hPm, hP⟩ := hy
  set n := P.natDegree with hn
  choose r hrd hran using fun i : Fin n => hol_of_mem_adjoin X _ (P.coeff i).2
  have heq : X.an y ^ n + ∑ i : Fin n, ((r i : ℂ → ℂ) : Mero) * X.an y ^ (i : ℕ) = 0 := by
    have h0 := congrArg X.an hP
    rw [hPm.as_sum] at h0
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_finset_sum,
      Polynomial.eval₂_mul, Polynomial.eval₂_C, map_add, map_pow, map_sum, map_mul, map_zero] at h0
    rw [← hn, Finset.sum_range (fun i => X.an (algebraMap _ X.K (P.coeff i)) * X.an y ^ i)] at h0
    rw [← h0]
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← hran i]; rfl
  obtain ⟨a, b, ha, hb, hb0, hab⟩ := X.an_mero y
  have hbz : ∃ z ∈ Hs, b z ≠ 0 := by
    by_contra hc
    push_neg at hc
    apply hb0
    have := hcongr (φ := b) (ψ := fun _ => 0) hc
    rw [this]; rfl
  have hF : ((fun z => a z ^ n + ∑ i : Fin n, r i z * a z ^ (i : ℕ) * b z ^ (n - i) : ℂ → ℂ) : Mero) = 0 := by
    have e1 : (fun z => a z ^ n + ∑ i : Fin n, r i z * a z ^ (i : ℕ) * b z ^ (n - i) : ℂ → ℂ) =
        a ^ n + ∑ i : Fin n, r i * a ^ (i : ℕ) * b ^ (n - i) := by
      funext z; simp [Finset.sum_apply]
    rw [e1]
    have e2 : ((a ^ n + ∑ i : Fin n, r i * a ^ (i : ℕ) * b ^ (n - i) : ℂ → ℂ) : Mero) =
        (a : Mero) ^ n + ∑ i : Fin n, ((r i : ℂ → ℂ) : Mero) * (a : Mero) ^ (i : ℕ) * (b : Mero) ^ (n - i) := by
      have := map_add (Filter.Germ.coeRingHom (R := ℂ) (Filter.codiscreteWithin Hs)) (a ^ n)
        (∑ i : Fin n, r i * a ^ (i : ℕ) * b ^ (n - i))
      simp only [map_sum, map_mul, map_pow] at this
      exact this
    rw [e2, ← hab]
    calc (X.an y * (b : Mero)) ^ n + ∑ i : Fin n, ((r i : ℂ → ℂ) : Mero) * (X.an y * (b : Mero)) ^ (i : ℕ) *
          (b : Mero) ^ (n - i)
        = (b : Mero) ^ n * (X.an y ^ n + ∑ i : Fin n, ((r i : ℂ → ℂ) : Mero) * X.an y ^ (i : ℕ)) := by
          rw [mul_add, Finset.mul_sum, mul_pow, mul_comm ((b : Mero) ^ n)]
          congr 1
          refine Finset.sum_congr rfl (fun i _ => ?_)
          have hi : (i : ℕ) ≤ n := i.2.le
          rw [mul_pow, ← pow_mul_pow_sub (b : Mero) hi]
          ring
      _ = 0 := by rw [heq, mul_zero]
  have hFd : DifferentiableOn ℂ (fun z => a z ^ n + ∑ i : Fin n, r i z * a z ^ (i : ℕ) * b z ^ (n - i)) Hs := by
    refine (ha.pow n).add (DifferentiableOn.fun_sum (fun i _ => ((hrd i).mul (ha.pow _)).mul (hb.pow _)))
  have hFz : ∀ z ∈ Hs, a z ^ n + ∑ i : Fin n, r i z * a z ^ (i : ℕ) * b z ^ (n - i) = 0 := by
    intro z hz
    exact hid _ (fun _ => (0 : ℂ)) hFd (differentiableOn_const 0) (by rw [hF]; rfl) z hz
  obtain ⟨h0, hh0, hah0, -⟩ := GlobalTheory.quotient_integral_holomorphic Hs n a b r GlobalTheory.FN.isOpen_Hs
    GlobalTheory.FN.isPreconnected_Hs ha hb hrd hbz hFz
  have hbu : IsUnit (b : Mero) := (hunit b hb hb0).2
  refine ⟨h0, hh0, ?_⟩
  have e : (a : Mero) = ((h0 : ℂ → ℂ) : Mero) * (b : Mero) := by
    rw [hcongr (φ := a) (ψ := h0 * b) hah0]; rfl
  rw [e] at hab
  exact hbu.mul_right_cancel hab

/- English proof (translation)
Use `Polynomial.aeval_algHom_apply (X.sl (ofSL γ)) X.jK P` as an intermediate fact. Rewrite `this` using `[X.j_inv]`. Conclude with `this.symm`.
-/
theorem sl_aeval (X : Tower Ω ε) (γ : SL(2, ℤ)) (P : Polynomial Ω) :
    X.sl (ofSL γ) (Polynomial.aeval X.jK P) = Polynomial.aeval X.jK P := by
  have := Polynomial.aeval_algHom_apply (X.sl (ofSL γ)) X.jK P
  rw [X.j_inv] at this
  exact this.symm

/- English proof (translation)
Take `⟨p, hp0, hpi⟩` from `(IntermediateField.isAlgebraic_adjoin_iff.1 (X.alg_j f)).exists_integral_multiple`. Establish `hpf : p • f = (p : X.K) * f` using `rfl`. Rewrite `hpi` using `[hpf]`. Establish `hrange : ∀ b ∈ Algebra.adjoin Ω {X.jK}, ∃ Q : Polynomial Ω, Polynomial.aeval X.jK Q = b`. Introduce `b hb`.

Rewrite `hb` using `[Algebra.adjoin_singleton_eq_range_aeval]`. Conclude with `hb`. Take `⟨Q, hQ⟩` from `hrange _ p.2`. Establish `hmem` using `mem_adjoin_j X ((p : X.K) * f) (fun γ => by rw [map_mul, hf, ← hQ, sl_aeval]) (hol_of_isIntegral X _ hpi)`. Take `⟨P, hP⟩` from `hrange _ hmem`.

Establish `hp0' : (p : X.K) ≠ 0` using `fun h => hp0 (Subtype.ext h)`. Use `⟨P, Q, ?_⟩` and prove the remaining obligations. Rewrite using `[hP, hQ]`. Clear the denominators using the available nonvanishing facts.
-/
theorem exists_eq_div (X : Tower Ω ε) (f : X.K) (hf : ∀ γ : SL(2, ℤ), X.sl (ofSL γ) f = f) :
    ∃ P Q : Polynomial Ω, f = Polynomial.aeval X.jK P / Polynomial.aeval X.jK Q := by
  obtain ⟨p, hp0, hpi⟩ := (IntermediateField.isAlgebraic_adjoin_iff.1 (X.alg_j f)).exists_integral_multiple
  have hpf : p • f = (p : X.K) * f := rfl
  rw [hpf] at hpi
  have hrange : ∀ b ∈ Algebra.adjoin Ω {X.jK}, ∃ Q : Polynomial Ω, Polynomial.aeval X.jK Q = b := by
    intro b hb
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hb
    exact hb
  obtain ⟨Q, hQ⟩ := hrange _ p.2
  have hmem := mem_adjoin_j X ((p : X.K) * f) (fun γ => by rw [map_mul, hf, ← hQ, sl_aeval])
    (hol_of_isIntegral X _ hpi)
  obtain ⟨P, hP⟩ := hrange _ hmem
  have hp0' : (p : X.K) ≠ 0 := fun h => hp0 (Subtype.ext h)
  refine ⟨P, Q, ?_⟩
  rw [hP, hQ]
  field_simp

end GlobalTheory.K4.LevFin

namespace GlobalTheory.K4

/- English proof (translation)
Introduce `Ω _ _ ε X Γ' M hM hle`. Use `letI := GlobalTheory.K4.algRat X Γ'`. Use `letI : Algebra (RatFunc Ω) X.K := ((lev X Γ').subtype.comp (jRat X Γ')).toAlgebra`. Establish `hpoly : ∀ P : Polynomial Ω, algebraMap (RatFunc Ω) X.K (algebraMap (Polynomial Ω) (RatFunc Ω) P) = Polynomial.aeval X.jK P`. Introduce `P`.

Rewrite using `[← coe_jPoly X Γ', ← jRat_algebraMap]`. Both sides reduce to the same expression. Establish `hfix : ∀ (γ : SL(2, ℤ)) (R : RatFunc Ω), X.sl (ofSL γ) (algebraMap (RatFunc Ω) X.K R) = algebraMap (RatFunc Ω) X.K R`. Introduce `γ R`. Rewrite using `[← RatFunc.num_div_denom R, map_div₀, map_div₀, hpoly, hpoly, LevFin.sl_aeval, LevFin.sl_aeval]`.

Set `act : SL(2, ℤ) →* (X.K ≃ₐ[RatFunc Ω] X.K)` to `{ toFun := fun γ => AlgEquiv.ofRingEquiv (f := (X.sl (ofSL γ⁻¹)).toRingEquiv) (hfix γ⁻¹) map_one' := by`. Use extensionality with `f`. Use `show X.sl (ofSL 1⁻¹) f = f`. Rewrite using `[inv_one, map_one, X.sl_one]`. Use the proof step `map_mul' := by`.

Introduce `g h`. Use extensionality with `f`. Use `show X.sl (ofSL (g * h)⁻¹) f = X.sl (ofSL g⁻¹) (X.sl (ofSL h⁻¹) f)`. Rewrite using `[mul_inv_rev, map_mul, X.sl_mul] }`. Establish `hact : ∀ γ f, act γ f = X.sl (ofSL γ⁻¹) f` using `fun _ _ => rfl`.

Use `haveI : NeZero M := ⟨hM.ne'⟩`. Establish `hfi : Γ'.FiniteIndex` using `Subgroup.finiteIndex_of_le hle`. Establish `hfin` using `GlobalTheory.T.finiteDimensional_fixedField_map_of_finiteIndex' SL(2, ℤ) act Γ' hfi (by`. Introduce `x hx`. Take `⟨P, Q, hPQ⟩` from `LevFin.exists_eq_div X x (fun γ => by`.

Use `hx γ⁻¹` as an intermediate fact. Rewrite using `[hact, inv_inv] at this)` and apply the resulting hypothesis. Rewrite using `[IntermediateField.mem_bot]`. Conclude with `⟨algebraMap (Polynomial Ω) (RatFunc Ω) P / algebraMap (Polynomial Ω) (RatFunc Ω) Q, by`. Rewrite using `[map_div₀, hpoly, hpoly, hPQ]⟩)`.

Set `ι : lev X Γ' →ₗ[RatFunc Ω] IntermediateField.fixedField (Γ'.map act)` to `{ toFun := fun f => ⟨f, by`. Rewrite using `[IntermediateField.mem_fixedField_iff]`. Introduce and unpack `_ ⟨γ, hγ, rfl⟩`. Rewrite using `[hact]`. Conclude with `(mem_lev_iff X Γ' f).1 f.2 _ (inv_mem hγ)⟩`.

Use the proof step `map_add' := fun _ _ => rfl`. Use the proof step `map_smul' := fun _ _ => rfl }`. Conclude with `Module.Finite.of_injective ι (fun a b h => Subtype.ext (congrArg (fun x : IntermediateField.fixedField (Γ'.map act) => (x : X.K)) h))`.
-/
theorem finiteDimensional_lev : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε)
    (Γ' : Subgroup SL(2, ℤ)) (M : ℕ), 0 < M → CongruenceSubgroup.Gamma M ≤ Γ' →
    letI := GlobalTheory.K4.algRat X Γ'; FiniteDimensional (RatFunc Ω) (GlobalTheory.K4.lev X Γ') := by
  intro Ω _ _ ε X Γ' M hM hle
  letI := GlobalTheory.K4.algRat X Γ'
  letI : Algebra (RatFunc Ω) X.K := ((lev X Γ').subtype.comp (jRat X Γ')).toAlgebra
  have hpoly : ∀ P : Polynomial Ω,
      algebraMap (RatFunc Ω) X.K (algebraMap (Polynomial Ω) (RatFunc Ω) P) = Polynomial.aeval X.jK P := by
    intro P
    rw [← coe_jPoly X Γ', ← jRat_algebraMap]
    rfl
  have hfix : ∀ (γ : SL(2, ℤ)) (R : RatFunc Ω),
      X.sl (ofSL γ) (algebraMap (RatFunc Ω) X.K R) = algebraMap (RatFunc Ω) X.K R := by
    intro γ R
    rw [← RatFunc.num_div_denom R, map_div₀, map_div₀, hpoly, hpoly, LevFin.sl_aeval, LevFin.sl_aeval]
  let act : SL(2, ℤ) →* (X.K ≃ₐ[RatFunc Ω] X.K) :=
    { toFun := fun γ => AlgEquiv.ofRingEquiv (f := (X.sl (ofSL γ⁻¹)).toRingEquiv) (hfix γ⁻¹)
      map_one' := by
        ext f
        show X.sl (ofSL 1⁻¹) f = f
        rw [inv_one, map_one, X.sl_one]
      map_mul' := by
        intro g h
        ext f
        show X.sl (ofSL (g * h)⁻¹) f = X.sl (ofSL g⁻¹) (X.sl (ofSL h⁻¹) f)
        rw [mul_inv_rev, map_mul, X.sl_mul] }
  have hact : ∀ γ f, act γ f = X.sl (ofSL γ⁻¹) f := fun _ _ => rfl
  haveI : NeZero M := ⟨hM.ne'⟩
  have hfi : Γ'.FiniteIndex := Subgroup.finiteIndex_of_le hle
  have hfin := GlobalTheory.T.finiteDimensional_fixedField_map_of_finiteIndex' SL(2, ℤ) act Γ' hfi (by
    intro x hx
    obtain ⟨P, Q, hPQ⟩ := LevFin.exists_eq_div X x (fun γ => by
      have := hx γ⁻¹
      rwa [hact, inv_inv] at this)
    rw [IntermediateField.mem_bot]
    exact ⟨algebraMap (Polynomial Ω) (RatFunc Ω) P / algebraMap (Polynomial Ω) (RatFunc Ω) Q, by
      rw [map_div₀, hpoly, hpoly, hPQ]⟩)
  let ι : lev X Γ' →ₗ[RatFunc Ω] IntermediateField.fixedField (Γ'.map act) :=
    { toFun := fun f => ⟨f, by
        rw [IntermediateField.mem_fixedField_iff]
        rintro _ ⟨γ, hγ, rfl⟩
        rw [hact]
        exact (mem_lev_iff X Γ' f).1 f.2 _ (inv_mem hγ)⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact Module.Finite.of_injective ι (fun a b h => Subtype.ext
    (congrArg (fun x : IntermediateField.fixedField (Γ'.map act) => (x : X.K)) h))

end GlobalTheory.K4
