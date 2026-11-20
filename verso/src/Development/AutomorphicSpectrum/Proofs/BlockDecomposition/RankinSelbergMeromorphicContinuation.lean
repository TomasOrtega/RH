import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral

noncomputable section

open MeasureTheory Matrix Filter Topology
open GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.GodementSectionLocal
open GroundTheory.Automorphic.GLnLocal (integralGL)
open scoped ValuativeRel ENNReal ComplexConjugate
open Ad3

namespace GlobalTheory.CompanionTheory.RankinSelbergMellinContinuation

/- English proof (translation)
Rewrite using `[IsLocallyConstant.iff_exists_open]`. Introduce `g`. Use `⟨{x | g⁻¹ * x ∈ U}, hU.preimage (continuous_const.mul continuous_id), by simp [U.one_mem], fun x hx => ?_⟩` and prove the remaining obligations. Use `h g _ hx` as an intermediate fact. Simplify using `using this`.
-/
theorem isLocallyConstant_of_invariant {G X : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (f : G → X) (U : Subgroup G) (hU : IsOpen (U : Set G))
    (h : ∀ g, ∀ u ∈ U, f (g * u) = f g) : IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_exists_open]
  intro g
  refine ⟨{x | g⁻¹ * x ∈ U}, hU.preimage (continuous_const.mul continuous_id), by simp [U.one_mem],
    fun x hx => ?_⟩
  have := h g _ hx
  simpa using this

/- English proof (translation)
Use `haveI : Finite (K ⧸ U) := Subgroup.quotient_finite_of_isOpen U hU`. Use `haveI := Fintype.ofFinite (K ⧸ U)`. Set `S : K ⧸ U → Set K` to `fun q => {κ | (κ : K ⧸ U) = q}`. Establish `hSeq : ∀ q, S q = (fun κ => (Quotient.out q)⁻¹ * κ) ⁻¹' (U : Set K)`. Introduce `q`.

Use extensionality with `κ`. Simplify using `only [S, Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe]`. Use `conv_lhs => rw [← QuotientGroup.out_eq' q]`. Rewrite using `[eq_comm, QuotientGroup.eq]`. Establish `hS : ∀ q, MeasurableSet (S q)` using `fun q => by`.

Rewrite using `[hSeq]`. Conclude with `(hU.preimage (continuous_const.mul continuous_id)).measurableSet`. Establish `hconst : ∀ s κ q, κ ∈ S q → G s κ = G s (Quotient.out q)`. Introduce `s κ q hκ`. Rewrite `hκ` using `[hSeq]`.

Use `hinv s (Quotient.out q) _ hκ` as an intermediate fact. Simplify using `using this`. Establish `key : ∀ s, ∫ κ, G s κ ∂m = ∑ q : K ⧸ U, m.real (S q) • G s (Quotient.out q)`. Introduce `s`. Establish `hpt : (fun κ => G s κ) = fun κ => ∑ q : K ⧸ U, (S q).indicator (fun _ => G s (Quotient.out q)) κ`.

Use function extensionality and compare the values at `κ`. Rewrite using `[Finset.sum_eq_single (κ : K ⧸ U)]`. Rewrite using `[Set.indicator_of_mem (show κ ∈ S (κ : K ⧸ U) from rfl)]`. Conclude with `hconst s κ _ rfl`. Introduce `b _ hb`.

Conclude with `Set.indicator_of_notMem (fun h => hb h.symm) _`. Simplify using the standard rewrite rules. Rewrite using `[hpt, integral_finset_sum _ (fun q _ => (integrable_const _).indicator (hS q))]`. Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Rewrite using `[integral_indicator_const _ (hS q)]`.

Establish `e : (fun s => ∫ κ, G s κ ∂m) = fun s => ∑ q : K ⧸ U, m.real (S q) • G s (Quotient.out q)`. Use function extensionality and compare the values at `key`. Rewrite using `[e]`. Conclude with `DifferentiableOn.fun_sum fun q _ => (hd (Quotient.out q)).const_smul (m.real (S q))`.
-/
theorem differentiableOn_integral_of_invariant {K : Type*} [Group K] [TopologicalSpace K]
    [IsTopologicalGroup K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] (m : Measure K)
    [IsFiniteMeasure m] (U : Subgroup K) (hU : IsOpen (U : Set K)) (G : ℂ → K → ℂ) (D : Set ℂ)
    (hinv : ∀ s κ, ∀ u ∈ U, G s (κ * u) = G s κ)
    (hd : ∀ κ, DifferentiableOn ℂ (fun s => G s κ) D) :
    DifferentiableOn ℂ (fun s => ∫ κ, G s κ ∂m) D := by
  classical
  haveI : Finite (K ⧸ U) := Subgroup.quotient_finite_of_isOpen U hU
  haveI := Fintype.ofFinite (K ⧸ U)
  let S : K ⧸ U → Set K := fun q => {κ | (κ : K ⧸ U) = q}
  have hSeq : ∀ q, S q = (fun κ => (Quotient.out q)⁻¹ * κ) ⁻¹' (U : Set K) := by
    intro q
    ext κ
    simp only [S, Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe]
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    rw [eq_comm, QuotientGroup.eq]
  have hS : ∀ q, MeasurableSet (S q) := fun q => by
    rw [hSeq]
    exact (hU.preimage (continuous_const.mul continuous_id)).measurableSet
  have hconst : ∀ s κ q, κ ∈ S q → G s κ = G s (Quotient.out q) := by
    intro s κ q hκ
    rw [hSeq] at hκ
    have := hinv s (Quotient.out q) _ hκ
    simpa using this
  have key : ∀ s, ∫ κ, G s κ ∂m = ∑ q : K ⧸ U, m.real (S q) • G s (Quotient.out q) := by
    intro s
    have hpt : (fun κ => G s κ) = fun κ => ∑ q : K ⧸ U, (S q).indicator (fun _ => G s (Quotient.out q)) κ := by
      funext κ
      rw [Finset.sum_eq_single (κ : K ⧸ U)]
      · rw [Set.indicator_of_mem (show κ ∈ S (κ : K ⧸ U) from rfl)]
        exact hconst s κ _ rfl
      · intro b _ hb
        exact Set.indicator_of_notMem (fun h => hb h.symm) _
      · simp
    rw [hpt, integral_finset_sum _ (fun q _ => (integrable_const _).indicator (hS q))]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [integral_indicator_const _ (hS q)]
  have e : (fun s => ∫ κ, G s κ ∂m) = fun s => ∑ q : K ⧸ U, m.real (S q) • G s (Quotient.out q) :=
    funext key
  rw [e]
  exact DifferentiableOn.fun_sum fun q _ => (hd (Quotient.out q)).const_smul (m.real (S q))

section Mellin

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/- English proof (translation)
Simplify using `[quasiCharExponent, h]`.
-/
theorem exponent_eq_zero {χ : Fˣ →* ℂˣ} (h : ∀ x, ‖((χ x : ℂˣ) : ℂ)‖ = 1) :
    quasiCharExponent χ = 0 := by
  simp [quasiCharExponent, h]

/- English proof (translation)
Conclude with `modulus_pos a.ne_zero` after adjusting the coercions.
-/
theorem modulus_pos' (a : Fˣ) : (0 : ℝ) < modulus (a : F) := by
  exact_mod_cast modulus_pos a.ne_zero

/- English proof (translation)
Establish `hq` using `residueCard_pos_real (K := F)`. Rewrite using `[modulus_of_ne_zero a.ne_zero, NNReal.coe_zpow, NNReal.coe_natCast, ← Real.rpow_intCast, ← Real.rpow_mul hq.le, ← Real.rpow_intCast, ← Real.rpow_mul hq.le]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem modulus_rpow (a : Fˣ) (t : ℝ) :
    (modulus (a : F) : ℝ) ^ t = ((residueCard F : ℝ) ^ (-t)) ^ ord (a : F) := by
  have hq := residueCard_pos_real (K := F)
  rw [modulus_of_ne_zero a.ne_zero, NNReal.coe_zpow, NNReal.coe_natCast, ← Real.rpow_intCast,
    ← Real.rpow_mul hq.le, ← Real.rpow_intCast, ← Real.rpow_mul hq.le]
  congr 1
  push_cast
  ring

/- English proof (translation)
The claim follows from `Complex.norm_cpow_eq_rpow_re_of_pos (modulus_pos' a) s`.
-/
theorem norm_mp (a : Fˣ) (s : ℂ) : ‖mp a s‖ = (modulus (a : F) : ℝ) ^ s.re :=
  Complex.norm_cpow_eq_rpow_re_of_pos (modulus_pos' a) s

/- English proof (translation)
The claim follows from `Complex.cpow_add _ _ (Complex.ofReal_ne_zero.2 (modulus_pos' a).ne')`.
-/
theorem mp_add (a : Fˣ) (s t : ℂ) : mp a (s + t) = mp a s * mp a t :=
  Complex.cpow_add _ _ (Complex.ofReal_ne_zero.2 (modulus_pos' a).ne')

/- English proof (translation)
Use `(Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp (continuous_modulus.comp Units.continuous_val))).cpow continuous_const fun u => ?_` and prove the remaining obligations. Conclude with `Complex.ofReal_mem_slitPlane.mpr (modulus_pos' u)`.
-/
theorem continuous_mp (s : ℂ) : Continuous fun a : Fˣ => mp a s := by
  refine (Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp
    (continuous_modulus.comp Units.continuous_val))).cpow continuous_const fun u => ?_
  exact Complex.ofReal_mem_slitPlane.mpr (modulus_pos' u)

/- English proof (translation)
Establish `hq : (1 : ℝ) < residueCard F` using `by exact_mod_cast one_lt_residueCard (K := F)`. Take `⟨n, hn⟩` from `pow_unbounded_of_one_lt B hq`. Use `⟨-(n : ℤ), fun a ha => ?_⟩` and prove the remaining obligations. Establish `h1 : (modulus (a : F) : ℝ) = (residueCard F : ℝ) ^ (-ord (a : F))`. Rewrite using `[modulus_of_ne_zero a.ne_zero, NNReal.coe_zpow, NNReal.coe_natCast]`.

Establish `h2 : (residueCard F : ℝ) ^ (-ord (a : F)) < (residueCard F : ℝ) ^ (n : ℤ)`. Rewrite using `[zpow_natCast, ← h1]`. Conclude with `ha.trans_lt hn`. Use `(zpow_lt_zpow_iff_right₀ hq).1 h2` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem exists_ord_ge (B : ℝ) : ∃ M : ℤ, ∀ a : Fˣ, (modulus (a : F) : ℝ) ≤ B → M ≤ ord (a : F) := by
  have hq : (1 : ℝ) < residueCard F := by exact_mod_cast one_lt_residueCard (K := F)
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt B hq
  refine ⟨-(n : ℤ), fun a ha => ?_⟩
  have h1 : (modulus (a : F) : ℝ) = (residueCard F : ℝ) ^ (-ord (a : F)) := by
    rw [modulus_of_ne_zero a.ne_zero, NNReal.coe_zpow, NNReal.coe_natCast]
  have h2 : (residueCard F : ℝ) ^ (-ord (a : F)) < (residueCard F : ℝ) ^ (n : ℤ) := by
    rw [zpow_natCast, ← h1]
    exact ha.trans_lt hn
  have := (zpow_lt_zpow_iff_right₀ hq).1 h2
  omega

variable [MeasurableSpace F] [BorelSpace F]

/- English proof (translation)
Take `⟨M, hM⟩` from `exists_ord_ge (F := F) B`. Establish `hC0 : 0 ≤ C`. Establish `h1` using `(norm_nonneg _).trans (hb 1)`. Conclude with `(mul_nonneg_iff_of_pos_right (Real.rpow_pos_of_pos (modulus_pos' 1) τ)).1 h1`. Establish `hf` using `indicator_valBall_mem_schwartzBruhat (K := F) M`.

Establish `hχ : Continuous (1 : Fˣ →* ℂˣ)` using `continuous_const`. Establish `hexp : quasiCharExponent (1 : Fˣ →* ℂˣ) = 0` using `exponent_eq_zero (by simp)`. Establish `hI` using `integrable_localZeta (s := ((s.re + τ : ℝ) : ℂ)) hf hχ (by rw [hexp]; simp only [Complex.ofReal_re]; linarith)`. Use `(hI.norm.const_mul C).mono' ?_ (Eventually.of_forall fun a => ?_)` and prove the remaining obligations. Conclude with `(hG.mul (continuous_mp s)).aestronglyMeasurable`.

Distinguish the cases in `h0 : G a = 0`. Simplify using `only [h0, zero_mul, norm_zero]`. Check the signs of the components of the expression. Establish `hmem : (a : F) ∈ (valBall F M : Set F)` using `(mem_valBall_iff_le_ord a.ne_zero).2 (hM a (hsupp a h0))`. Rewrite using `[Set.indicator_of_mem hmem]`.

Simplify using `only [MonoidHom.one_apply, Units.val_one, mul_one, one_mul, norm_mul, norm_mp]`. Establish `e : ‖((modulus (a : F) : ℝ) : ℂ) ^ ((s.re + τ : ℝ) : ℂ)‖ = (modulus (a : F) : ℝ) ^ τ * (modulus (a : F) : ℝ) ^ s.re`. Rewrite using `[Complex.norm_cpow_eq_rpow_re_of_pos (modulus_pos' a), Complex.ofReal_re, add_comm, Real.rpow_add (modulus_pos' a)]`. Rewrite using `[e, ← mul_assoc]`. Conclude with `mul_le_mul_of_nonneg_right (hb a) (Real.rpow_nonneg (modulus_pos' a).le _)`.
-/
theorem integrable_mellin {G : Fˣ → ℂ} (hG : Continuous G) {C B τ : ℝ}
    (hb : ∀ a, ‖G a‖ ≤ C * (modulus (a : F) : ℝ) ^ τ)
    (hsupp : ∀ a, G a ≠ 0 → (modulus (a : F) : ℝ) ≤ B) {s : ℂ} (hs : -τ < s.re) :
    Integrable (fun a => G a * mp a s) (multHaar F) := by
  obtain ⟨M, hM⟩ := exists_ord_ge (F := F) B
  have hC0 : 0 ≤ C := by
    have h1 := (norm_nonneg _).trans (hb 1)
    exact (mul_nonneg_iff_of_pos_right (Real.rpow_pos_of_pos (modulus_pos' 1) τ)).1 h1
  have hf := indicator_valBall_mem_schwartzBruhat (K := F) M
  have hχ : Continuous (1 : Fˣ →* ℂˣ) := continuous_const
  have hexp : quasiCharExponent (1 : Fˣ →* ℂˣ) = 0 := exponent_eq_zero (by simp)
  have hI := integrable_localZeta (s := ((s.re + τ : ℝ) : ℂ)) hf hχ
    (by rw [hexp]; simp only [Complex.ofReal_re]; linarith)
  refine (hI.norm.const_mul C).mono' ?_ (Eventually.of_forall fun a => ?_)
  · exact (hG.mul (continuous_mp s)).aestronglyMeasurable
  · by_cases h0 : G a = 0
    · simp only [h0, zero_mul, norm_zero]
      positivity
    have hmem : (a : F) ∈ (valBall F M : Set F) :=
      (mem_valBall_iff_le_ord a.ne_zero).2 (hM a (hsupp a h0))
    rw [Set.indicator_of_mem hmem]
    simp only [MonoidHom.one_apply, Units.val_one, mul_one, one_mul, norm_mul, norm_mp]
    have e : ‖((modulus (a : F) : ℝ) : ℂ) ^ ((s.re + τ : ℝ) : ℂ)‖ =
        (modulus (a : F) : ℝ) ^ τ * (modulus (a : F) : ℝ) ^ s.re := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (modulus_pos' a), Complex.ofReal_re,
        add_comm, Real.rpow_add (modulus_pos' a)]
    rw [e, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hb a) (Real.rpow_nonneg (modulus_pos' a).le _)

/- English proof (translation)
Take `⟨M, hM⟩` from `exists_ord_ge (F := F) B`. Establish `hq : (1 : ℝ) < residueCard F` using `by exact_mod_cast one_lt_residueCard (K := F)`. Establish `hq0 : (0 : ℝ) < residueCard F` using `residueCard_pos_real`. Establish `hC0 : 0 ≤ C`. Establish `h1` using `(norm_nonneg _).trans (hb 1)`.

Conclude with `(mul_nonneg_iff_of_pos_right (Real.rpow_pos_of_pos (modulus_pos' 1) τ)).1 h1`. Use `set A : ℤ → ℂ := fun k => ∫ u in ordShell F k, G u ∂multHaar F with hAdef`. Use `set r : ℝ := (residueCard F : ℝ) ^ (-τ) with hr`. Establish `hr0 : 0 < r` using `Real.rpow_pos_of_pos hq0 _`. Establish `hterm : ∀ (s : ℂ) (k : ℤ), ∫ u in ordShell F k, G u * mp u s ∂multHaar F = A k * ((residueCard F : ℂ) ^ (-s)) ^ k`.

Introduce `s k`. Simplify using `only [hAdef]`. Rewrite using `[← integral_mul_const]`. Use `setIntegral_congr_fun (measurableSet_ordShell k) fun u hu => ?_` and prove the remaining obligations. Simplify using `only [mp]`.

Rewrite using `[modulus_cpow_eq_zpow, mem_ordShell.mp hu]`. Establish `hsum : ∀ s : ℂ, -τ < s.re → HasSum (fun k : ℤ => A k * ((residueCard F : ℂ) ^ (-s)) ^ k) (∫ a, G a * mp a s ∂multHaar F)` using `fun s hs => by`. Use `hasSum_setIntegral_ordShell (integrable_mellin hG hb hsupp hs)` as an intermediate fact. Simplify `this` using `only [hterm]`. Establish `hlow : ∀ k, k < M → A k = 0`.

Introduce `k hk`. Use `setIntegral_eq_zero_of_forall_eq_zero fun u hu => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `h0`. Use `hM u (hsupp u h0)` as an intermediate fact. Rewrite `this` using `[mem_ordShell.mp hu]`.

Use linear arithmetic over natural numbers and integers. Establish `hA : ∀ k, ‖A k‖ ≤ C * r ^ k`. Introduce `k`. Establish `h1 : ‖A k‖ ≤ (C * r ^ k) * (multHaar F).real (ordShell F k)` using `norm_setIntegral_le_of_norm_le_const (by rw [multHaar_ordShell]; exact ENNReal.one_lt_top) fun u hu => by`. Use `hb u` as an intermediate fact.

Rewrite `this` using `[modulus_rpow, mem_ordShell.mp hu]`. Then use the resulting hypothesis. Simplify `h1` using `[measureReal_def, multHaar_ordShell]`. Introduce `s0 h0`. Establish `h0' : -τ < s0.re` using `h0`. Use `set σ : ℝ := (s0.re - τ) / 2 with hσ`.

Establish `hσ1 : -τ < σ` using `by rw [hσ]; linarith`. Establish `hσ2 : σ < s0.re` using `by rw [hσ]; linarith`. Use `set ρ : ℝ := (residueCard F : ℝ) ^ (-(τ + σ)) with hρ`. Establish `hρ0 : 0 ≤ ρ` using `(Real.rpow_pos_of_pos hq0 _).le`. Establish `hρ1 : ρ < 1` using `Real.rpow_lt_one_of_one_lt_of_neg hq (by linarith)`.

Establish `hT : Differentiable ℂ fun s : ℂ => (residueCard F : ℂ) ^ (-s)` using `differentiable_qpow (K := F)`. Establish `hopen : IsOpen {s : ℂ | σ < s.re}` using `isOpen_lt continuous_const Complex.continuous_re`. Establish `hdiff : DifferentiableOn ℂ (fun s => ∑' n : ℕ, A (M + n) * ((residueCard F : ℂ) ^ (-s)) ^ n) {s : ℂ | σ < s.re}`. Use `Complex.differentiableOn_tsum_of_summable_norm (u := fun n : ℕ => C * r ^ M * ρ ^ n) ((summable_geometric_of_lt_one hρ0 hρ1).mul_left _) (fun n => ((hT.pow n).const_mul _).differentiableOn) hopen fun n s hs => ?_` and prove the remaining obligations. Establish `hs' : σ < s.re` using `hs`.

Establish `hTn : ‖(residueCard F : ℂ) ^ (-s)‖ ≤ (residueCard F : ℝ) ^ (-σ)`. Rewrite using `[norm_qpow]`. Conclude with `Real.rpow_le_rpow_of_exponent_le hq.le (by linarith)`. Rewrite using `[norm_mul, norm_pow]`. Combine the equalities or inequalities in the displayed calculation.

Establish `: ρ = r * (residueCard F : ℝ) ^ (-σ)`. Rewrite using `[hρ, hr, ← Real.rpow_add hq0]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, mul_pow, zpow_add₀ hr0.ne', zpow_natCast]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hinj : Function.Injective (fun n : ℕ => M + (n : ℤ))` using `fun a b hab => by`. Simplify using `using hab`. Establish `heq : ∀ s ∈ {s : ℂ | σ < s.re}, ∫ a, G a * mp a s ∂multHaar F = ((residueCard F : ℂ) ^ (-s)) ^ M * ∑' n : ℕ, A (M + n) * ((residueCard F : ℂ) ^ (-s)) ^ n`. Introduce `s hs`.

Establish `hs' : σ < s.re` using `hs`. Establish `h1` using `hsum s (by linarith)`. Establish `hvan : ∀ x ∉ Set.range (fun n : ℕ => M + (n : ℤ)), A x * ((residueCard F : ℂ) ^ (-s)) ^ x = 0`. Introduce `x hx`. Establish `: x < M`.

Assume the negation of the conclusion as `hle`. Conclude with `hx ⟨(x - M).toNat, by simp only; omega⟩`. Rewrite using `[hlow x this, zero_mul]`. Establish `h2` using `(hinj.hasSum_iff hvan).2 h1`. Establish `hne : ((residueCard F : ℂ) ^ (-s)) ≠ 0` using `qpow_ne_zero s`.

Rewrite using `[← tsum_mul_left, ← h2.tsum_eq]`. Use `tsum_congr fun n => ?_` and prove the remaining obligations. Simplify using `only [Function.comp]`. Rewrite using `[zpow_add₀ hne, zpow_natCast]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hfin : DifferentiableOn ℂ (fun s => ∫ a, G a * mp a s ∂multHaar F) {s : ℂ | σ < s.re}` using `(((hT.zpow (Or.inl fun s => qpow_ne_zero s)).differentiableOn).mul hdiff).congr heq`. Conclude with `(hfin.differentiableAt (hopen.mem_nhds hσ2)).differentiableWithinAt`.
-/
theorem differentiableOn_mellin {G : Fˣ → ℂ} (hG : Continuous G) {C B τ : ℝ}
    (hb : ∀ a, ‖G a‖ ≤ C * (modulus (a : F) : ℝ) ^ τ)
    (hsupp : ∀ a, G a ≠ 0 → (modulus (a : F) : ℝ) ≤ B) :
    DifferentiableOn ℂ (fun s => ∫ a, G a * mp a s ∂multHaar F) {s | -τ < s.re} := by
  obtain ⟨M, hM⟩ := exists_ord_ge (F := F) B
  have hq : (1 : ℝ) < residueCard F := by exact_mod_cast one_lt_residueCard (K := F)
  have hq0 : (0 : ℝ) < residueCard F := residueCard_pos_real
  have hC0 : 0 ≤ C := by
    have h1 := (norm_nonneg _).trans (hb 1)
    exact (mul_nonneg_iff_of_pos_right (Real.rpow_pos_of_pos (modulus_pos' 1) τ)).1 h1
  set A : ℤ → ℂ := fun k => ∫ u in ordShell F k, G u ∂multHaar F with hAdef
  set r : ℝ := (residueCard F : ℝ) ^ (-τ) with hr
  have hr0 : 0 < r := Real.rpow_pos_of_pos hq0 _
  have hterm : ∀ (s : ℂ) (k : ℤ), ∫ u in ordShell F k, G u * mp u s ∂multHaar F =
      A k * ((residueCard F : ℂ) ^ (-s)) ^ k := by
    intro s k
    simp only [hAdef]
    rw [← integral_mul_const]
    refine setIntegral_congr_fun (measurableSet_ordShell k) fun u hu => ?_
    simp only [mp]
    rw [modulus_cpow_eq_zpow, mem_ordShell.mp hu]
  have hsum : ∀ s : ℂ, -τ < s.re → HasSum (fun k : ℤ => A k * ((residueCard F : ℂ) ^ (-s)) ^ k)
      (∫ a, G a * mp a s ∂multHaar F) := fun s hs => by
    have := hasSum_setIntegral_ordShell (integrable_mellin hG hb hsupp hs)
    simpa only [hterm] using this
  have hlow : ∀ k, k < M → A k = 0 := by
    intro k hk
    refine setIntegral_eq_zero_of_forall_eq_zero fun u hu => ?_
    by_contra h0
    have := hM u (hsupp u h0)
    rw [mem_ordShell.mp hu] at this
    omega
  have hA : ∀ k, ‖A k‖ ≤ C * r ^ k := by
    intro k
    have h1 : ‖A k‖ ≤ (C * r ^ k) * (multHaar F).real (ordShell F k) :=
      norm_setIntegral_le_of_norm_le_const (by rw [multHaar_ordShell]; exact ENNReal.one_lt_top)
        fun u hu => by
          have := hb u
          rwa [modulus_rpow, mem_ordShell.mp hu] at this
    simpa [measureReal_def, multHaar_ordShell] using h1
  intro s0 h0
  have h0' : -τ < s0.re := h0
  set σ : ℝ := (s0.re - τ) / 2 with hσ
  have hσ1 : -τ < σ := by rw [hσ]; linarith
  have hσ2 : σ < s0.re := by rw [hσ]; linarith
  set ρ : ℝ := (residueCard F : ℝ) ^ (-(τ + σ)) with hρ
  have hρ0 : 0 ≤ ρ := (Real.rpow_pos_of_pos hq0 _).le
  have hρ1 : ρ < 1 := Real.rpow_lt_one_of_one_lt_of_neg hq (by linarith)
  have hT : Differentiable ℂ fun s : ℂ => (residueCard F : ℂ) ^ (-s) := differentiable_qpow (K := F)
  have hopen : IsOpen {s : ℂ | σ < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hdiff : DifferentiableOn ℂ (fun s => ∑' n : ℕ, A (M + n) * ((residueCard F : ℂ) ^ (-s)) ^ n)
      {s : ℂ | σ < s.re} := by
    refine Complex.differentiableOn_tsum_of_summable_norm (u := fun n : ℕ => C * r ^ M * ρ ^ n)
      ((summable_geometric_of_lt_one hρ0 hρ1).mul_left _)
      (fun n => ((hT.pow n).const_mul _).differentiableOn) hopen fun n s hs => ?_
    have hs' : σ < s.re := hs
    have hTn : ‖(residueCard F : ℂ) ^ (-s)‖ ≤ (residueCard F : ℝ) ^ (-σ) := by
      rw [norm_qpow]
      exact Real.rpow_le_rpow_of_exponent_le hq.le (by linarith)
    rw [norm_mul, norm_pow]
    calc ‖A (M + n)‖ * ‖(residueCard F : ℂ) ^ (-s)‖ ^ n
        ≤ (C * r ^ (M + n : ℤ)) * ((residueCard F : ℝ) ^ (-σ)) ^ n :=
          mul_le_mul (hA _) (pow_le_pow_left₀ (norm_nonneg _) hTn n) (by positivity)
            (mul_nonneg hC0 (zpow_nonneg hr0.le _))
      _ = C * r ^ M * ρ ^ n := by
          have : ρ = r * (residueCard F : ℝ) ^ (-σ) := by
            rw [hρ, hr, ← Real.rpow_add hq0]
            congr 1
            ring
          rw [this, mul_pow, zpow_add₀ hr0.ne', zpow_natCast]
          ring
  have hinj : Function.Injective (fun n : ℕ => M + (n : ℤ)) := fun a b hab => by
    simpa using hab
  have heq : ∀ s ∈ {s : ℂ | σ < s.re}, ∫ a, G a * mp a s ∂multHaar F =
      ((residueCard F : ℂ) ^ (-s)) ^ M * ∑' n : ℕ, A (M + n) * ((residueCard F : ℂ) ^ (-s)) ^ n := by
    intro s hs
    have hs' : σ < s.re := hs
    have h1 := hsum s (by linarith)
    have hvan : ∀ x ∉ Set.range (fun n : ℕ => M + (n : ℤ)),
        A x * ((residueCard F : ℂ) ^ (-s)) ^ x = 0 := by
      intro x hx
      have : x < M := by
        by_contra hle
        exact hx ⟨(x - M).toNat, by simp only; omega⟩
      rw [hlow x this, zero_mul]
    have h2 := (hinj.hasSum_iff hvan).2 h1
    have hne : ((residueCard F : ℂ) ^ (-s)) ≠ 0 := qpow_ne_zero s
    rw [← tsum_mul_left, ← h2.tsum_eq]
    refine tsum_congr fun n => ?_
    simp only [Function.comp]
    rw [zpow_add₀ hne, zpow_natCast]
    ring
  have hfin : DifferentiableOn ℂ (fun s => ∫ a, G a * mp a s ∂multHaar F) {s : ℂ | σ < s.re} :=
    (((hT.zpow (Or.inl fun s => qpow_ne_zero s)).differentiableOn).mul hdiff).congr heq
  exact (hfin.differentiableAt (hopen.mem_nhds hσ2)).differentiableWithinAt

end Mellin

section Loc

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/- English proof (translation)
Establish `h : Continuous fun a : Fˣ => (dg2 a 1 : GL (Fin 2) F)`. Rewrite using `[Units.continuous_iff]`. Establish `hinv : Continuous fun a : Fˣ => ((a⁻¹ : Fˣ) : F)` using `Units.continuous_val.comp continuous_inv`. Prove the components needed by the constructor for the conclusion. Apply the tactic sequence `refine continuous_matrix fun i j => ?_ fin_cases i <;> fin_cases j`.

Conclude with `Units.continuous_val`. Conclude with `continuous_const`. Conclude with `continuous_const`. Conclude with `continuous_const`. Apply the tactic sequence `refine continuous_matrix fun i j => ?_ fin_cases i <;> fin_cases j`.

Conclude with `hinv`. Conclude with `continuous_const`. Conclude with `continuous_const`. Conclude with `continuous_const`. Conclude with `h.mul continuous_const`.
-/
theorem continuous_diagGL2 (κ : GL (Fin 2) F) :
    Continuous fun a : Fˣ => (dg2 a 1 * κ : GL (Fin 2) F) := by
  have h : Continuous fun a : Fˣ => (dg2 a 1 : GL (Fin 2) F) := by
    rw [Units.continuous_iff]
    have hinv : Continuous fun a : Fˣ => ((a⁻¹ : Fˣ) : F) := Units.continuous_val.comp continuous_inv
    constructor
    · refine continuous_matrix fun i j => ?_
      fin_cases i <;> fin_cases j
      · exact Units.continuous_val
      · exact continuous_const
      · exact continuous_const
      · exact continuous_const
    · refine continuous_matrix fun i j => ?_
      fin_cases i <;> fin_cases j
      · exact hinv
      · exact continuous_const
      · exact continuous_const
      · exact continuous_const
  exact h.mul continuous_const

def Gf (W W' : GL (Fin 2) F → ℂ) (c : Fˣ →* ℂˣ) (κ : GL (Fin 2) F) (a : Fˣ) : ℂ :=
  W (dg2 a 1 * κ) * conj (W' (dg2 a 1 * κ)) * ((c a : ℂˣ) : ℂ) * mp a (-1)

/- English proof (translation)
Rewrite using `[show s - 1 = -1 + s by ring, mp_add]`. Simplify using `only [Gf]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem integrand_eq (W W' : GL (Fin 2) F → ℂ) (c : Fˣ →* ℂˣ) (κ : GL (Fin 2) F) (s : ℂ) (a : Fˣ) :
    W (dg2 a 1 * κ) * conj (W' (dg2 a 1 * κ)) * ((c a : ℂˣ) : ℂ) * mp a (s - 1) =
      Gf W W' c κ a * mp a s := by
  rw [show s - 1 = -1 + s by ring, mp_add]
  simp only [Gf]
  ring

/- English proof (translation)
The claim follows from `(((hW.continuous.comp (continuous_diagGL2 κ)).mul (Complex.continuous_conj.comp (hW'.continuous.comp (continuous_diagGL2 κ)))).mul (Units.continuous_val.comp hc)).mul (continuous_mp _)`.
-/
theorem continuous_Gf {W W' : GL (Fin 2) F → ℂ} (hW : IsLocallyConstant W)
    (hW' : IsLocallyConstant W') {c : Fˣ →* ℂˣ} (hc : Continuous c) (κ : GL (Fin 2) F) :
    Continuous (Gf W W' c κ) :=
  (((hW.continuous.comp (continuous_diagGL2 κ)).mul
    (Complex.continuous_conj.comp (hW'.continuous.comp (continuous_diagGL2 κ)))).mul
    (Units.continuous_val.comp hc)).mul (continuous_mp _)

/- English proof (translation)
Take `⟨C, B, h⟩` from `H.bound W hW ε hε`. Take `⟨C', B', h'⟩` from `H.bound W' hW' ε hε`. Use `⟨C * C', B, fun a => ?_, fun a ha => (h a κ hκ).2 fun h0 => ha ?_⟩` and prove the remaining obligations. Establish `e1` using `(h a κ hκ).1`. Establish `e2` using `(h' a κ hκ).1`.

Establish `hx` using `modulus_pos' a`. Establish `e3` using `mul_le_mul e1 e2 (norm_nonneg _) ((norm_nonneg _).trans e1)`. Simplify using `only [Gf, norm_mul, Complex.norm_conj, hc.2 a, norm_mp, mul_one]`. Establish `hre : (-1 : ℂ).re = -1` using `by simp`. Rewrite using `[hre]`.

Combine the equalities or inequalities in the displayed calculation. Establish `: (modulus (a : F) : ℝ) ^ (-(2 * ε)) = (modulus (a : F) : ℝ) ^ (1 / 2 - ε) * (modulus (a : F) : ℝ) ^ (1 / 2 - ε) * (modulus (a : F) : ℝ) ^ (-1 : ℝ)`. Rewrite using `[← Real.rpow_add hx, ← Real.rpow_add hx]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `[Gf, h0]`.
-/
theorem Gf_bound {ψ : AddChar F Circle} {μ₁ μ₂ : Fˣ →* ℂˣ} [MeasurableSpace F] [BorelSpace F]
    {V : Submodule ℂ (GL (Fin 2) F → ℂ)}
    (H : WhittakerModelGL2 ψ μ₁ μ₂ V) {W W' : GL (Fin 2) F → ℂ} (hW : W ∈ V) (hW' : W' ∈ V) {c : Fˣ →* ℂˣ}
    (hc : IsUnit1 c) {ε : ℝ} (hε : 0 < ε) {κ : GL (Fin 2) F} (hκ : κ ∈ integralGL F 2) :
    ∃ C B : ℝ, (∀ a, ‖Gf W W' c κ a‖ ≤ C * (modulus (a : F) : ℝ) ^ (-(2 * ε))) ∧
      ∀ a, Gf W W' c κ a ≠ 0 → (modulus (a : F) : ℝ) ≤ B := by
  obtain ⟨C, B, h⟩ := H.bound W hW ε hε
  obtain ⟨C', B', h'⟩ := H.bound W' hW' ε hε
  refine ⟨C * C', B, fun a => ?_, fun a ha => (h a κ hκ).2 fun h0 => ha ?_⟩
  · have e1 := (h a κ hκ).1
    have e2 := (h' a κ hκ).1
    have hx := modulus_pos' a
    have e3 := mul_le_mul e1 e2 (norm_nonneg _) ((norm_nonneg _).trans e1)
    simp only [Gf, norm_mul, Complex.norm_conj, hc.2 a, norm_mp, mul_one]
    have hre : (-1 : ℂ).re = -1 := by simp
    rw [hre]
    calc ‖W (dg2 a 1 * κ)‖ * ‖W' (dg2 a 1 * κ)‖ * (modulus (a : F) : ℝ) ^ (-1 : ℝ)
        ≤ (C * (modulus (a : F) : ℝ) ^ (1 / 2 - ε) * (C' * (modulus (a : F) : ℝ) ^ (1 / 2 - ε))) *
            (modulus (a : F) : ℝ) ^ (-1 : ℝ) :=
          mul_le_mul_of_nonneg_right e3 (Real.rpow_nonneg hx.le _)
      _ = C * C' * (modulus (a : F) : ℝ) ^ (-(2 * ε)) := by
          have : (modulus (a : F) : ℝ) ^ (-(2 * ε)) = (modulus (a : F) : ℝ) ^ (1 / 2 - ε) *
              (modulus (a : F) : ℝ) ^ (1 / 2 - ε) * (modulus (a : F) : ℝ) ^ (-1 : ℝ) := by
            rw [← Real.rpow_add hx, ← Real.rpow_add hx]
            congr 1
            ring
          rw [this]
          ring
  · simp [Gf, h0]

variable [MeasurableSpace F] [BorelSpace F]

/- English proof (translation)
Take `⟨N, M, hMN, hinv, hsupp⟩` from `exists_invariant_of_mem_schwartzBruhat2 hΦ`. Use `⟨max (N - M).toNat (max (quasiCharConductor χ₁) 1), fun s g u hu ↦ ?_⟩` and prove the remaining obligations. Use `set m := max (N - M).toNat (max (quasiCharConductor χ₁) 1) with hm`. Establish `hu0 : u ∈ GLnLocal.integralGL F 2` using `GLnLocal.congruenceSubgroup_le F 2 m hu`. Establish `hR : GodementSectionLocal.rightTranslate u Φ = Φ`.

Use function extensionality and compare the values at `x`. Simplify using `only [GodementSectionLocal.rightTranslate]`. Distinguish the cases in `hx : x ∈ box F M`. Use `set D : Matrix (Fin 2) (Fin 2) F := (u : Matrix (Fin 2) (Fin 2) F) - 1 with hD`. Establish `hxD : x ᵥ* D ∈ box F N`.

Use `box_antitone (show N ≤ M + m by omega) (mem_box.2 fun j ↦ ?_)` and prove the remaining obligations. Simplify using `only [Matrix.vecMul, dotProduct, Fin.sum_univ_two]`. Conclude with `add_mem (mul_mem_valBall (mem_box.1 hx 0) (sub_one_mem_valBall_of_mem_congruenceSubgroup hu 0 j)) (mul_mem_valBall (mem_box.1 hx 1) (sub_one_mem_valBall_of_mem_congruenceSubgroup hu 1 j))`. Establish `he : x ᵥ* (u : Matrix (Fin 2) (Fin 2) F) = x + x ᵥ* D`. Rewrite using `[hD, Matrix.vecMul_sub, Matrix.vecMul_one]`.

Normalize the expressions using the abelian group laws. Rewrite using `[he, hinv x _ hxD]`. Establish `h0 : Φ x = 0`. Assume the negation of the conclusion as `h`. Conclude with `hx (hsupp x h)`.

Establish `h1 : Φ (x ᵥ* (u : Matrix (Fin 2) (Fin 2) F)) = 0`. Assume the negation of the conclusion as `h`. Conclude with `hx ((vecMul_mem_box_iff hu0 M x).1 (hsupp _ h))`. Rewrite using `[h0, h1]`. Establish `hdet : χ₁ (detU u) = 1`.

Establish `hmem : detU u ∈ unitFiltrationUnits F m` using `(mem_unitFiltrationUnits_iff_valBall (by omega)).2 (det_sub_one_mem_valBall hu)`. Conclude with `unitFiltrationUnits_quasiCharConductor_le_ker h₁ (unitFiltrationUnits_antitone (by omega) hmem)`. Rewrite using `[localSection_mul, hR, hdet, modPow_units_eq_zpow, ord_det_eq_zero hu0]`. Simplify using the standard rewrite rules.
-/
theorem exists_level_localSection {χ₁ : Fˣ →* ℂˣ} (h₁ : Continuous χ₁) (χ₂ : Fˣ →* ℂˣ)
    {Φ : (Fin 2 → F) → ℂ} (hΦ : Φ ∈ schwartzBruhat2 F) :
    ∃ m : ℕ, ∀ (s : ℂ) (g : GL (Fin 2) F), ∀ u ∈ GLnLocal.congruenceSubgroup F 2 m,
      localSection χ₁ χ₂ s Φ (g * u) = localSection χ₁ χ₂ s Φ g := by
  obtain ⟨N, M, hMN, hinv, hsupp⟩ := exists_invariant_of_mem_schwartzBruhat2 hΦ
  refine ⟨max (N - M).toNat (max (quasiCharConductor χ₁) 1), fun s g u hu ↦ ?_⟩
  set m := max (N - M).toNat (max (quasiCharConductor χ₁) 1) with hm
  have hu0 : u ∈ GLnLocal.integralGL F 2 := GLnLocal.congruenceSubgroup_le F 2 m hu
  have hR : GodementSectionLocal.rightTranslate u Φ = Φ := by
    funext x
    simp only [GodementSectionLocal.rightTranslate]
    by_cases hx : x ∈ box F M
    · set D : Matrix (Fin 2) (Fin 2) F := (u : Matrix (Fin 2) (Fin 2) F) - 1 with hD
      have hxD : x ᵥ* D ∈ box F N := by
        refine box_antitone (show N ≤ M + m by omega) (mem_box.2 fun j ↦ ?_)
        simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
        exact add_mem (mul_mem_valBall (mem_box.1 hx 0)
            (sub_one_mem_valBall_of_mem_congruenceSubgroup hu 0 j))
          (mul_mem_valBall (mem_box.1 hx 1)
            (sub_one_mem_valBall_of_mem_congruenceSubgroup hu 1 j))
      have he : x ᵥ* (u : Matrix (Fin 2) (Fin 2) F) = x + x ᵥ* D := by
        rw [hD, Matrix.vecMul_sub, Matrix.vecMul_one]
        abel
      rw [he, hinv x _ hxD]
    · have h0 : Φ x = 0 := by
        by_contra h
        exact hx (hsupp x h)
      have h1 : Φ (x ᵥ* (u : Matrix (Fin 2) (Fin 2) F)) = 0 := by
        by_contra h
        exact hx ((vecMul_mem_box_iff hu0 M x).1 (hsupp _ h))
      rw [h0, h1]
  have hdet : χ₁ (detU u) = 1 := by
    have hmem : detU u ∈ unitFiltrationUnits F m :=
      (mem_unitFiltrationUnits_iff_valBall (by omega)).2 (det_sub_one_mem_valBall hu)
    exact unitFiltrationUnits_quasiCharConductor_le_ker h₁
      (unitFiltrationUnits_antitone (by omega) hmem)
  rw [localSection_mul, hR, hdet, modPow_units_eq_zpow, ord_det_eq_zero hu0]
  simp

/- English proof (translation)
Establish `hexp` using `exponent_eq_zero h1`. Take `⟨P, hP⟩` from `exists_localZeta_eq_mul_evalQpow hf hχ`. Establish `hL : DifferentiableOn ℂ (localLFactor χ) {s | 0 < s.re}`. Distinguish the cases in `h : IsUnramifiedChar χ`. Establish `e : localLFactor χ = fun s => (1 - ((χ (unifUnit F) : ℂˣ) : ℂ) * (residueCard F : ℂ) ^ (-s))⁻¹`.

Use function extensionality and compare the values at `fun s => localLFactor_of_isUnramified h s`. Rewrite using `[e]`. Conclude with `((((differentiable_qpow (K := F)).const_mul _).const_sub 1).differentiableOn).inv fun s hs => one_sub_quasiChar_unifUnit_mul_qpow_ne_zero hχ (by rw [hexp]; simpa using hs)`. Establish `e : localLFactor χ = fun _ => (1 : ℂ)`. Use function extensionality and compare the values at `fun s => localLFactor_of_not_isUnramified h s`.

Rewrite using `[e]`. Conclude with `differentiableOn_const _`. Establish `h2 : Differentiable ℂ fun s : ℂ => 2 * s` using `differentiable_id.const_mul 2`. Establish `hmaps : Set.MapsTo (fun s : ℂ => 2 * s) {s | 0 < s.re} {s | 0 < s.re}` using `fun s hs => by`. Establish `hs' : 0 < s.re` using `hs`.

Simplify using `using hs'`. Establish `h3 : DifferentiableOn ℂ (fun s => localLFactor χ (2 * s) * evalQpow F P (2 * s)) {s | 0 < s.re}` using `(hL.comp h2.differentiableOn hmaps).mul (((differentiable_evalQpow P).comp h2).differentiableOn)`. Use `h3.congr fun s hs => hP (2 * s) ?_` and prove the remaining obligations. Establish `hs' : 0 < s.re` using `hs`. Rewrite using `[hexp]`.

Simplify using `using hs'`.
-/
theorem differentiableOn_localZeta {f : F → ℂ} (hf : f ∈ schwartzBruhat F) {χ : Fˣ →* ℂˣ}
    (hχ : Continuous χ) (h1 : ∀ x, ‖((χ x : ℂˣ) : ℂ)‖ = 1) :
    DifferentiableOn ℂ (fun s => localZeta f χ (2 * s)) {s | 0 < s.re} := by
  have hexp := exponent_eq_zero h1
  obtain ⟨P, hP⟩ := exists_localZeta_eq_mul_evalQpow hf hχ
  have hL : DifferentiableOn ℂ (localLFactor χ) {s | 0 < s.re} := by
    by_cases h : IsUnramifiedChar χ
    · have e : localLFactor χ = fun s =>
          (1 - ((χ (unifUnit F) : ℂˣ) : ℂ) * (residueCard F : ℂ) ^ (-s))⁻¹ :=
        funext fun s => localLFactor_of_isUnramified h s
      rw [e]
      exact ((((differentiable_qpow (K := F)).const_mul _).const_sub 1).differentiableOn).inv
        fun s hs => one_sub_quasiChar_unifUnit_mul_qpow_ne_zero hχ (by rw [hexp]; simpa using hs)
    · have e : localLFactor χ = fun _ => (1 : ℂ) :=
        funext fun s => localLFactor_of_not_isUnramified h s
      rw [e]
      exact differentiableOn_const _
  have h2 : Differentiable ℂ fun s : ℂ => 2 * s := differentiable_id.const_mul 2
  have hmaps : Set.MapsTo (fun s : ℂ => 2 * s) {s | 0 < s.re} {s | 0 < s.re} := fun s hs => by
    have hs' : 0 < s.re := hs
    simpa using hs'
  have h3 : DifferentiableOn ℂ (fun s => localLFactor χ (2 * s) * evalQpow F P (2 * s)) {s | 0 < s.re} :=
    (hL.comp h2.differentiableOn hmaps).mul
      (((differentiable_evalQpow P).comp h2).differentiableOn)
  refine h3.congr fun s hs => hP (2 * s) ?_
  have hs' : 0 < s.re := hs
  rw [hexp]
  simpa using hs'

/- English proof (translation)
Establish `hχ : Continuous (c * c⁻¹⁻¹)` using `continuous_mul_inv hc.1 (continuous_quasiChar_inv hc.1)`. Establish `h1 : ∀ x, ‖(((c * c⁻¹⁻¹) x : ℂˣ) : ℂ)‖ = 1` using `fun x => by simp [hc.2]`. Establish `hz` using `differentiableOn_localZeta (slice_mem hΨ g) hχ h1`. Establish `hm : Differentiable ℂ fun s : ℂ => modPow (detU g : F) s`. Use `differentiable_id.const_cpow (Or.inl ?_)` and prove the remaining obligations.

Conclude with `Complex.ofReal_ne_zero.2 (modulus_pos' (detU g)).ne'`. Conclude with `((hm.const_mul _).differentiableOn).mul hz`.
-/
theorem differentiableOn_localSection {c : Fˣ →* ℂˣ} (hc : IsUnit1 c) {Ψ : (Fin 2 → F) → ℂ}
    (hΨ : Ψ ∈ schwartzBruhat2 F) (g : GL (Fin 2) F) :
    DifferentiableOn ℂ (fun s => localSection c c⁻¹ s Ψ g) {s | 0 < s.re} := by
  have hχ : Continuous (c * c⁻¹⁻¹) := continuous_mul_inv hc.1 (continuous_quasiChar_inv hc.1)
  have h1 : ∀ x, ‖(((c * c⁻¹⁻¹) x : ℂˣ) : ℂ)‖ = 1 := fun x => by simp [hc.2]
  have hz := differentiableOn_localZeta (slice_mem hΨ g) hχ h1
  have hm : Differentiable ℂ fun s : ℂ => modPow (detU g : F) s := by
    refine differentiable_id.const_cpow (Or.inl ?_)
    exact Complex.ofReal_ne_zero.2 (modulus_pos' (detU g)).ne'
  exact ((hm.const_mul _).differentiableOn).mul hz

end Loc

/- English proof (translation)
Introduce `hL F _ _ _ _ _ _ ψ hψ _ _ m _ _ μ₁ μ₂ c h₁ h₂ hc W hW W' hW'`. Establish `H` using `(hL F ψ hψ μ₁ μ₂ h₁ h₂).1`. Take `⟨U, hU⟩` from `H.smooth W hW`. Take `⟨U', hU'⟩` from `H.smooth W' hW'`. Establish `lW : IsLocallyConstant W` using `isLocallyConstant_of_invariant W U.toSubgroup U.isOpen hU`.

Establish `lW' : IsLocallyConstant W'` using `isLocallyConstant_of_invariant W' U'.toSubgroup U'.isOpen hU'`. Establish `hUU : IsOpen ((U.toSubgroup ⊓ U'.toSubgroup : Subgroup (GL (Fin 2) F)) : Set (GL (Fin 2) F))` using `U.isOpen.inter U'.isOpen`. Establish `hAvI : ∀ (s : ℂ) (g : GL (Fin 2) F), ∀ u ∈ U.toSubgroup ⊓ U'.toSubgroup, R.Av W W' c s (g * u) = R.Av W W' c s g`. Introduce `s g u hu`. Simplify using `only [R.Av]`.

Use `integral_congr_ae (Eventually.of_forall fun a => ?_)` and prove the remaining obligations. Simplify using `only [← mul_assoc (dg2 a 1) g u]`. Rewrite using `[hU _ u hu.1, hU' _ u hu.2]`. Establish `hcont : ∀ κ, Continuous (Gf W W' c κ)` using `fun κ => continuous_Gf lW lW' hc.1 κ`. Establish `hAvD : ∀ κ ∈ integralGL F 2, DifferentiableOn ℂ (fun s => R.Av W W' c s κ) {s | 0 < s.re}`.

Introduce `κ hκ s0 h0`. Establish `h0' : 0 < s0.re` using `h0`. Take `⟨C, B, hb, hs⟩` from `Gf_bound H hW hW' hc (ε := s0.re / 4) (by linarith) hκ`. Establish `hD` using `differentiableOn_mellin (hcont κ) hb hs`. Establish `hopen : IsOpen {s : ℂ | -(-(2 * (s0.re / 4))) < s.re}` using `isOpen_lt continuous_const Complex.continuous_re`.

Establish `hat` using `hD.differentiableAt (hopen.mem_nhds (show -(-(2 * (s0.re / 4))) < s0.re by linarith))`. Establish `e : (fun s => R.Av W W' c s κ) = fun s => ∫ a, Gf W W' c κ a * mp a s ∂multHaar F`. Use function extensionality and compare the values at `s`. Simplify using `only [R.Av, integrand_eq]`. Rewrite using `[e]`.

Conclude with `hat.differentiableWithinAt`. Use `⟨fun s hs => ⟨fun κ hκ => ?_, ?_⟩, fun Ψ hΨ => ?_⟩` and prove the remaining obligations. Take `⟨C, B, hb, hs'⟩` from `Gf_bound H hW hW' hc (ε := s.re / 4) (by linarith) hκ`. Establish `hI` using `integrable_mellin (hcont κ) hb hs' (s := s) (by linarith)`. Establish `e : (fun a => W (dg2 a 1 * κ) * conj (W' (dg2 a 1 * κ)) * ((c a : ℂˣ) : ℂ) * mp a (s - 1)) = fun a => Gf W W' c κ a * mp a s` using `funext fun a => integrand_eq W W' c κ s a`.

Rewrite using `[e]`. Conclude with `hI`. Conclude with `isLocallyConstant_of_invariant _ _ hUU (hAvI s)`. Take `⟨l, hl⟩` from `exists_level_localSection hc.1 c⁻¹ hΨ`. Establish `hKopen` using `GLnLocal.isOpen_congruenceSubgroup F 2 l`.

Use `⟨fun s _ => isLocallyConstant_of_invariant _ _ hKopen (hl s), ?_⟩` and prove the remaining obligations. Use `haveI : CompactSpace (integralGL F 2) := isCompact_iff_compactSpace.mp (GLnLocal.isCompact_integralGL F 2)`. Set `Uk : Subgroup (integralGL F 2)` to `((U.toSubgroup ⊓ U'.toSubgroup) ⊓ GLnLocal.congruenceSubgroup F 2 l).comap (integralGL F 2).subtype`. Establish `hUk : IsOpen (Uk : Set (integralGL F 2))` using `(hUU.inter hKopen).preimage continuous_subtype_val`. Use `differentiableOn_integral_of_invariant m Uk hUk (fun s κ => GodementSectionLocal.localSection c c⁻¹ s Ψ κ.1 * R.Av W W' c s κ.1) _ ?_ ?_` and prove the remaining obligations.

Introduce `s κ u hu`. Establish `hu' : (u : GL (Fin 2) F) ∈ (U.toSubgroup ⊓ U'.toSubgroup) ⊓ GLnLocal.congruenceSubgroup F 2 l` using `hu`. Simplify using `only [Subgroup.coe_mul]`. Rewrite using `[hl s _ _ hu'.2, hAvI s _ _ hu'.1]`. Introduce `κ`.

Conclude with `(differentiableOn_localSection hc hΨ κ.1).mul (hAvD κ.1 κ.2)`.
-/
theorem a10 : Ad3.Loc2 → Ad3.R.A10 := by
  intro hL F _ _ _ _ _ _ ψ hψ _ _ m _ _ μ₁ μ₂ c h₁ h₂ hc W hW W' hW'
  have H := (hL F ψ hψ μ₁ μ₂ h₁ h₂).1
  obtain ⟨U, hU⟩ := H.smooth W hW
  obtain ⟨U', hU'⟩ := H.smooth W' hW'
  have lW : IsLocallyConstant W := isLocallyConstant_of_invariant W U.toSubgroup U.isOpen hU
  have lW' : IsLocallyConstant W' := isLocallyConstant_of_invariant W' U'.toSubgroup U'.isOpen hU'
  have hUU : IsOpen ((U.toSubgroup ⊓ U'.toSubgroup : Subgroup (GL (Fin 2) F)) : Set (GL (Fin 2) F)) :=
    U.isOpen.inter U'.isOpen
  have hAvI : ∀ (s : ℂ) (g : GL (Fin 2) F), ∀ u ∈ U.toSubgroup ⊓ U'.toSubgroup,
      R.Av W W' c s (g * u) = R.Av W W' c s g := by
    intro s g u hu
    simp only [R.Av]
    refine integral_congr_ae (Eventually.of_forall fun a => ?_)
    simp only [← mul_assoc (dg2 a 1) g u]
    rw [hU _ u hu.1, hU' _ u hu.2]
  have hcont : ∀ κ, Continuous (Gf W W' c κ) := fun κ => continuous_Gf lW lW' hc.1 κ
  have hAvD : ∀ κ ∈ integralGL F 2, DifferentiableOn ℂ (fun s => R.Av W W' c s κ) {s | 0 < s.re} := by
    intro κ hκ s0 h0
    have h0' : 0 < s0.re := h0
    obtain ⟨C, B, hb, hs⟩ := Gf_bound H hW hW' hc (ε := s0.re / 4) (by linarith) hκ
    have hD := differentiableOn_mellin (hcont κ) hb hs
    have hopen : IsOpen {s : ℂ | -(-(2 * (s0.re / 4))) < s.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    have hat := hD.differentiableAt (hopen.mem_nhds (show -(-(2 * (s0.re / 4))) < s0.re by linarith))
    have e : (fun s => R.Av W W' c s κ) = fun s => ∫ a, Gf W W' c κ a * mp a s ∂multHaar F := by
      funext s
      simp only [R.Av, integrand_eq]
    rw [e]
    exact hat.differentiableWithinAt
  refine ⟨fun s hs => ⟨fun κ hκ => ?_, ?_⟩, fun Ψ hΨ => ?_⟩
  · obtain ⟨C, B, hb, hs'⟩ := Gf_bound H hW hW' hc (ε := s.re / 4) (by linarith) hκ
    have hI := integrable_mellin (hcont κ) hb hs' (s := s) (by linarith)
    have e : (fun a => W (dg2 a 1 * κ) * conj (W' (dg2 a 1 * κ)) * ((c a : ℂˣ) : ℂ) * mp a (s - 1)) =
        fun a => Gf W W' c κ a * mp a s := funext fun a => integrand_eq W W' c κ s a
    rw [e]
    exact hI
  · exact isLocallyConstant_of_invariant _ _ hUU (hAvI s)
  · obtain ⟨l, hl⟩ := exists_level_localSection hc.1 c⁻¹ hΨ
    have hKopen := GLnLocal.isOpen_congruenceSubgroup F 2 l
    refine ⟨fun s _ => isLocallyConstant_of_invariant _ _ hKopen (hl s), ?_⟩
    haveI : CompactSpace (integralGL F 2) :=
      isCompact_iff_compactSpace.mp (GLnLocal.isCompact_integralGL F 2)
    let Uk : Subgroup (integralGL F 2) :=
      ((U.toSubgroup ⊓ U'.toSubgroup) ⊓ GLnLocal.congruenceSubgroup F 2 l).comap (integralGL F 2).subtype
    have hUk : IsOpen (Uk : Set (integralGL F 2)) :=
      (hUU.inter hKopen).preimage continuous_subtype_val
    refine differentiableOn_integral_of_invariant m Uk hUk
      (fun s κ => GodementSectionLocal.localSection c c⁻¹ s Ψ κ.1 * R.Av W W' c s κ.1) _ ?_ ?_
    · intro s κ u hu
      have hu' : (u : GL (Fin 2) F) ∈ (U.toSubgroup ⊓ U'.toSubgroup) ⊓ GLnLocal.congruenceSubgroup F 2 l := hu
      simp only [Subgroup.coe_mul]
      rw [hl s _ _ hu'.2, hAvI s _ _ hu'.1]
    · intro κ
      exact (differentiableOn_localSection hc hΨ κ.1).mul (hAvD κ.1 κ.2)

end GlobalTheory.CompanionTheory.RankinSelbergMellinContinuation
