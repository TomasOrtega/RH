import Formalism.HermitianCurvature.StatementJ

open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open MeasureTheory Formalism.H
open scoped FourierTransform ComplexConjugate nonZeroDivisors

namespace Formalism.FourierDecayAlt.P

namespace Jx4

/- English proof (translation)
Establish `h : (0 : ℝ) < ((|NumberField.discr E| : ℤ) : ℝ)`. Conclude with `abs_pos.mpr (NumberField.discr_ne_zero E)` after adjusting the coercions. Unfold `S6.rd`. Use `first`. Consider the case `exact Real.rpow_pos_of_pos h _`.

Consider the case `exact Real.rpow_pos h _`.
-/
theorem rd_pos (E : Type) [Field E] [NumberField E] [IsCMField E] : 0 < S6.rd E := by
  have h : (0 : ℝ) < ((|NumberField.discr E| : ℤ) : ℝ) := by
    exact_mod_cast abs_pos.mpr (NumberField.discr_ne_zero E)
  unfold S6.rd
  first
    | exact Real.rpow_pos_of_pos h _
    | exact Real.rpow_pos h _

end Jx4

/- English proof (translation)
Introduce `V _ _ _ _ _ φ`. Use `first`. Consider the case `(simp [Real.fourier_eq]; done)`. Consider the case `(simp [Real.fourierIntegral_eq']; done)`. Consider the case `(simp [Real.fourierIntegral_eq]; done)`.

Consider the case `(simp [Real.fourierIntegral, VectorFourier.fourierIntegral]; done)`. Consider the case `(simp [FourierTransform.fourier, Real.fourierIntegral, VectorFourier.fourierIntegral]; done)`. Consider the case `(simp [VectorFourier.fourierIntegral]; done)`.
-/
theorem fourier_transform_at_zero : Formalism.FourierDecayAlt.J.TransformAtZero := by
  intro V _ _ _ _ _ φ
  first
    | (simp [Real.fourier_eq]; done)
    | (simp [Real.fourierIntegral_eq']; done)
    | (simp [Real.fourierIntegral_eq]; done)
    | (simp [Real.fourierIntegral, VectorFourier.fourierIntegral]; done)
    | (simp [FourierTransform.fourier, Real.fourierIntegral, VectorFourier.fourierIntegral]; done)
    | (simp [VectorFourier.fourierIntegral]; done)

/- English proof (translation)
Introduce `hF hJ E W _ D V _ _ _ _ _ ι _ π hπ Λ _ _ emb dmap hFr hW`. Introduce `ε hε i hi1 hi2 w Y hY κ hκ t₀ B hB S hS`. Take `⟨φ, Cφ, hc, hb, hnn, hdiag, hhat⟩` from `hW ε hε i hi1 hi2 w Y hY κ hκ`. Take `⟨hinj, hmem, hd0, hdual⟩` from `hFr i hi1 hi2`. Establish `key` using `hJ hF V ι π hπ (Λ i) E (emb i) (dmap i) (D.La i 1) (D.Lad i) φ Cφ (D.Nhat ε i w Y κ) hinj hmem hd0 hdual hc hb hnn hhat t₀ B hB S (fun t ht => (hS t ht).2)`.

Use `Eq.trans_le ?_ key` and prove the remaining obligations. Conclude with `Finset.sum_congr rfl fun t ht => hdiag t (hS t ht).1`.
-/
theorem poisson_level_joint : Formalism.FourierDecayAlt.J.PoissonStepJoint := by
  intro hF hJ E W _ D V _ _ _ _ _ ι _ π hπ Λ _ _ emb dmap hFr hW
  intro ε hε i hi1 hi2 w Y hY κ hκ t₀ B hB S hS
  obtain ⟨φ, Cφ, hc, hb, hnn, hdiag, hhat⟩ := hW ε hε i hi1 hi2 w Y hY κ hκ
  obtain ⟨hinj, hmem, hd0, hdual⟩ := hFr i hi1 hi2
  have key := hJ hF V ι π hπ (Λ i) E (emb i) (dmap i) (D.La i 1) (D.Lad i) φ Cφ
    (D.Nhat ε i w Y κ) hinj hmem hd0 hdual hc hb hnn hhat t₀ B hB S (fun t ht => (hS t ht).2)
  refine Eq.trans_le ?_ key
  exact Finset.sum_congr rfl fun t ht => hdiag t (hS t ht).1

/- English proof (translation)
Introduce `hF hJ E _ _ D H _ _ W _ Φ tr i V _ _ _ _ _ ι _ π hπ Λ _ _ emb dmap hinj hmem hd0 hdual hW`. Introduce `w Hd kap hHd hk t0 T hT B hB`. Take `⟨φ, Cφ, hc, hb, hnn, hdiag, hhat⟩` from `hW w Hd kap hHd hk`. Establish `key` using `hJ hF V ι π hπ Λ E emb dmap (D.La i 1) (D.Lv i) φ Cφ (tr w Hd kap) hinj hmem hd0 hdual hc hb hnn hhat t0 B hB T (fun t ht => (hT t ht).2)`. Use `Eq.trans_le ?_ key` and prove the remaining obligations.

Conclude with `Finset.sum_congr rfl fun t ht => hdiag t (hT t ht).1`.
-/
theorem poisson_joint_first_reduction : Formalism.FourierDecayAlt.J.PoissonJointTA := by
  intro hF hJ E _ _ D H _ _ W _ Φ tr i V _ _ _ _ _ ι _ π hπ Λ _ _ emb dmap hinj hmem hd0 hdual hW
  intro w Hd kap hHd hk t0 T hT B hB
  obtain ⟨φ, Cφ, hc, hb, hnn, hdiag, hhat⟩ := hW w Hd kap hHd hk
  have key := hJ hF V ι π hπ Λ E emb dmap (D.La i 1) (D.Lv i) φ Cφ (tr w Hd kap)
    hinj hmem hd0 hdual hc hb hnn hhat t0 B hB T (fun t ht => (hT t ht).2)
  refine Eq.trans_le ?_ key
  exact Finset.sum_congr rfl fun t ht => hdiag t (hT t ht).1

/- English proof (translation)
Introduce `hA hT E W _ _ _ D H _ _ Φ ε i hε hi1 hi2 hwt hgram hPS`. Introduce `w Hd kap hHd hk t0 T hTT B hB`. Establish `hw : ((D.wt w : ℝ) : ℂ) ≠ 0` using `Complex.ofReal_ne_zero.mpr (hwt w)`. Establish `e : i - 1 + 1 = i` using `Nat.sub_add_cancel hi1`. Establish `hlev : ∀ h ∈ Hd, TB.level h = i - 1` using `fun h hh => (hHd h hh).1`.

Establish `hpsd : TB.PSDOn Hd (fun h h' => kap h' h)` using `hT _ Hd kap ((hA _ Hd kap).1.mpr hk)`. Establish `hT' : ∀ t ∈ T, t ≠ 0 ∧ t - t0 ∈ D.La i 1`. Introduce `t ht`. Use `⟨(hTT t ht).1, ?_⟩` and prove the remaining obligations. Establish `h2` using `(hTT t ht).2`.

Express the relevant statement in the definitionally equal form `t - t0 ∈ D.La (i - 1 + 1) 1 at h2`. Rewrite `h2` using `[e]`. Then use the resulting hypothesis. Establish `hN : ∀ t, TA.Nst (Φ w) Hd kap 1 t t = D.Nst ε i 1 w Hd (fun h h' => kap h' h) t t`. Introduce `t`. Unfold `TA.Nst TB.Data.Nst`.

Simplify using `only [hgram]`. Rewrite using `[Finset.sum_comm, eq_div_iff hw, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_mul]`. Use `Finset.sum_congr rfl fun y _ => ?_` and prove the remaining obligations.

Simplify using `only [TA.ext, TB.join]`. Expand and normalize the polynomial expressions, which then agree. Use `Eq.trans_le ?_ (hPS ε hε i hi1 hi2 w Hd hlev _ hpsd t0 B hB T hT')` and prove the remaining obligations. Conclude with `Finset.sum_congr rfl fun t _ => congrArg Complex.re (hN t)`.
-/
theorem poisson_forms_agree : Formalism.FourierDecayAlt.J.PoissonAgree := by
  intro hA hT E W _ _ _ D H _ _ Φ ε i hε hi1 hi2 hwt hgram hPS
  intro w Hd kap hHd hk t0 T hTT B hB
  have hw : ((D.wt w : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hwt w)
  have e : i - 1 + 1 = i := Nat.sub_add_cancel hi1
  have hlev : ∀ h ∈ Hd, TB.level h = i - 1 := fun h hh => (hHd h hh).1
  have hpsd : TB.PSDOn Hd (fun h h' => kap h' h) := hT _ Hd kap ((hA _ Hd kap).1.mpr hk)
  have hT' : ∀ t ∈ T, t ≠ 0 ∧ t - t0 ∈ D.La i 1 := by
    intro t ht
    refine ⟨(hTT t ht).1, ?_⟩
    have h2 := (hTT t ht).2
    change t - t0 ∈ D.La (i - 1 + 1) 1 at h2
    rwa [e] at h2
  have hN : ∀ t, TA.Nst (Φ w) Hd kap 1 t t = D.Nst ε i 1 w Hd (fun h h' => kap h' h) t t := by
    intro t
    unfold TA.Nst TB.Data.Nst
    simp only [hgram]
    rw [Finset.sum_comm, eq_div_iff hw, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [TA.ext, TB.join]
    ring
  refine Eq.trans_le ?_ (hPS ε hε i hi1 hi2 w Hd hlev _ hpsd t0 B hB T hT')
  exact Finset.sum_congr rfl fun t _ => congrArg Complex.re (hN t)

/- English proof (translation)
Introduce `hEmb hTD hTw hPow E _ _ _ g r hg i hi1 hi2`. Establish `hgE : (g : E) ≠ 0` using `Nat.cast_ne_zero.mpr hg.ne'`. Establish `hdd : S6.dd E ≠ 0`. Unfold `S6.dd`. Rewrite using `[Ne, FractionalIdeal.coeIdeal_eq_zero]`.

Use `first`. Consider the case `exact differentIdeal_ne_bot`. Consider the case `(intro h; have h2 := NumberField.absNorm_differentIdeal (K := E); rw [h, Ideal.absNorm_bot] at h2; exact NumberField.discr_ne_zero E (Int.natAbs_eq_zero.mp h2.symm))`. Establish `hB0 : ∀ ν : ℤ, S6.idl E g 2 ν ≠ 0`. Introduce `ν`.

Unfold `S6.idl`. Use `mul_ne_zero (zpow_ne_zero _ hdd) ?_` and prove the remaining obligations. Rewrite using `[Ne, FractionalIdeal.spanSingleton_eq_zero_iff]`. Conclude with `zpow_ne_zero _ hgE`. Establish `hBA : ∀ ν : ℤ, S6.idl E g 2 ν ≤ S6.idl E g 1 ν`.

Introduce `ν`. Unfold `S6.idl`. Establish `hs : FractionalIdeal.spanSingleton (𝓞 E)⁰ ((g : E) ^ (2 : ℤ)) ≤ FractionalIdeal.spanSingleton (𝓞 E)⁰ ((g : E) ^ (1 : ℤ))`. Rewrite using `[FractionalIdeal.spanSingleton_le_iff_mem, FractionalIdeal.mem_spanSingleton]`. Conclude with `⟨(g : 𝓞 E), by simp only [Algebra.smul_def, map_natCast, zpow_one, zpow_two]⟩`.

Use `first`. Consider the case `exact FractionalIdeal.mul_le.mpr fun a ha b hb => FractionalIdeal.mul_mem_mul ha (hs hb)`. Consider the case `exact mul_le_mul_left' hs _`. Consider the case `(gcongr; exact hs)`. Establish `hc0 : S6.rd E ^ (-(S6.nuBlock r i 1)) ≠ 0` using `zpow_ne_zero _ (Jx4.rd_pos E).ne'`.

Take `⟨hinj, -, -, hsm, -⟩` from `hEmb E`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `beta_reduce`. Establish `hfun : ⇑(semb E (S6.rd E ^ (-(S6.nuBlock r i 1)))) = fun t => S6.rd E ^ (-(S6.nuBlock r i 1)) • cemb E t` using `funext (hsm _)`. Rewrite using `[hfun]`.

Conclude with `(smul_right_injective (CV E) hc0).comp hinj`. Use `beta_reduce`. Introduce `t ht`. Conclude with `Submodule.mem_map.mpr ⟨t, ht, rfl⟩`. Use `beta_reduce`.

Unfold `dm`. Use extensionality with `w`. Simplify using the standard rewrite rules. Use `beta_reduce`. Introduce `μ hμ`.

Establish `hL` using `hTw E _ _ 1 (hB0 (S6.nuBlock r i 1)) (hBA _) (hPow E g 2 (S6.nuBlock r i 1))`. Conclude with `(hTD E _ g _ hg hc0 hL.2 μ).1 hμ`.
-/
theorem block_poisson_frame : Formalism.FourierDecayAlt.J.BlockPoissonFrame := by
  intro hEmb hTD hTw hPow E _ _ _ g r hg i hi1 hi2
  have hgE : (g : E) ≠ 0 := Nat.cast_ne_zero.mpr hg.ne'
  have hdd : S6.dd E ≠ 0 := by
    unfold S6.dd
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]
    first
      | exact differentIdeal_ne_bot
      | (intro h; have h2 := NumberField.absNorm_differentIdeal (K := E); rw [h, Ideal.absNorm_bot] at h2; exact NumberField.discr_ne_zero E (Int.natAbs_eq_zero.mp h2.symm))
  have hB0 : ∀ ν : ℤ, S6.idl E g 2 ν ≠ 0 := by
    intro ν
    unfold S6.idl
    refine mul_ne_zero (zpow_ne_zero _ hdd) ?_
    rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]
    exact zpow_ne_zero _ hgE
  have hBA : ∀ ν : ℤ, S6.idl E g 2 ν ≤ S6.idl E g 1 ν := by
    intro ν
    unfold S6.idl
    have hs : FractionalIdeal.spanSingleton (𝓞 E)⁰ ((g : E) ^ (2 : ℤ)) ≤
        FractionalIdeal.spanSingleton (𝓞 E)⁰ ((g : E) ^ (1 : ℤ)) := by
      rw [FractionalIdeal.spanSingleton_le_iff_mem, FractionalIdeal.mem_spanSingleton]
      exact ⟨(g : 𝓞 E), by simp only [Algebra.smul_def, map_natCast, zpow_one, zpow_two]⟩
    first
      | exact FractionalIdeal.mul_le.mpr fun a ha b hb => FractionalIdeal.mul_mem_mul ha (hs hb)
      | exact mul_le_mul_left' hs _
      | (gcongr; exact hs)
  have hc0 : S6.rd E ^ (-(S6.nuBlock r i 1)) ≠ 0 := zpow_ne_zero _ (Jx4.rd_pos E).ne'
  obtain ⟨hinj, -, -, hsm, -⟩ := hEmb E
  refine ⟨?_, ?_, ?_, ?_⟩
  · beta_reduce
    have hfun : ⇑(semb E (S6.rd E ^ (-(S6.nuBlock r i 1)))) =
        fun t => S6.rd E ^ (-(S6.nuBlock r i 1)) • cemb E t := funext (hsm _)
    rw [hfun]
    exact (smul_right_injective (CV E) hc0).comp hinj
  · beta_reduce
    intro t ht
    exact Submodule.mem_map.mpr ⟨t, ht, rfl⟩
  · beta_reduce
    unfold dm
    ext w
    simp
  · beta_reduce
    intro μ hμ
    have hL := hTw E _ _ 1 (hB0 (S6.nuBlock r i 1)) (hBA _) (hPow E g 2 (S6.nuBlock r i 1))
    exact (hTD E _ g _ hg hc0 hL.2 μ).1 hμ

/- English proof (translation)
Introduce `m i C ka N I A g B`. Establish `h : 2 * (i - 1) + 1 - 1 = 2 * i - 2` using `by omega`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Unfold `Sz.xThreshold Sz.lamThreshold`. Rewrite using `[h]`.

Unfold `Sz.xHat Sz.lamHat`. Rewrite using `[h]`.
-/
theorem lattice_x_eq_lambda_one : Formalism.FourierDecayAlt.J.XIsLamOne := by
  intro m i C ka N I A g B
  have h : 2 * (i - 1) + 1 - 1 = 2 * i - 2 := by omega
  refine ⟨?_, ?_⟩
  · unfold Sz.xThreshold Sz.lamThreshold
    rw [h]
  · unfold Sz.xHat Sz.lamHat
    rw [h]

/- English proof (translation)
Introduce `r i s C rd g N I A TT hi hs hrd hg`. Take `⟨n, rfl⟩ : ∃ n, i = n + 1` from `⟨i - 1, by omega⟩`. Take `⟨t, rfl⟩ : ∃ t, s = t + 1` from `⟨s - 1, by omega⟩`. Establish `hrd0 : rd ≠ 0` using `hrd.ne'`. Establish `hg0 : g ≠ 0` using `hg.ne'`.

Establish `hpi : (2 * Real.pi) ≠ 0` using `by positivity`. Establish `e1 : 2 * r + 2 - 1 = 2 * r + 1` using `by omega`. Prove the components needed by the constructor for the conclusion. Establish `hz : rd ^ (S6.nuBlock (r : ℤ) ((n + 1 : ℕ) : ℤ) ((t + 1 : ℕ) : ℤ) + 1) = rd ^ (2 * r + 1) / rd ^ (2 * n + t)`. Rewrite using `[← zpow_natCast, ← zpow_natCast, ← zpow_sub₀ hrd0]`.

Use `congr 1`. Unfold `S6.nuBlock`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : 2 * (n + 1 - 1) + (t + 1) - 1 = 2 * n + t` using `by omega`.

Unfold `Sz.lamThreshold Sz.lamHat`. Rewrite using `[hz, e1, e2]`. Establish `b1 : C * (2 * Real.pi / g) * N / I = (2 * Real.pi / g) * (C * N / I)` using `by ring`. Establish `b2 : C * (2 * Real.pi / rd) * N / (g * I) = (2 * Real.pi / (rd * g)) * (C * N / I)` using `by ring`. Rewrite using `[b1, b2, mul_pow, mul_pow]`.

Generalize the expression as in `C * N / I = X`. Simplify using `only [div_eq_mul_inv, mul_pow, inv_pow, mul_inv, inv_inv]`. Expand and normalize the polynomial expressions, which then agree. Establish `hz : rd ^ (S6.nuBlock (r : ℤ) ((n + 1 : ℕ) : ℤ) ((r : ℤ) + 2 - ((n + 1 : ℕ) : ℤ))) = rd ^ r / rd ^ n`. Rewrite using `[← zpow_natCast, ← zpow_natCast, ← zpow_sub₀ hrd0]`.

Use `congr 1`. Unfold `S6.nuBlock`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `key : ∀ P a : ℝ, 0 ≤ a → √P * a = √(P * a ^ 2)` using `fun P a ha => by`.

Rewrite using `[Real.sqrt_mul' _ (sq_nonneg a), Real.sqrt_sq ha]`. Rewrite using `[hz, key _ _ (mul_nonneg hg.le (div_nonneg (pow_nonneg hrd.le _) (pow_nonneg hrd.le _)))]`. Unfold `Sz.lamPrimeHat Sz.lamPrimeSq`. Use `congr 1`. Establish `e3 : 2 * (n + 1) - 1 = 2 * n + 1` using `by omega`.

Establish `e4 : 2 * (n + 1 - 1) = 2 * n` using `by omega`. Establish `e5 : 2 * (n + 1) - 2 = 2 * n` using `by omega`. Rewrite using `[e1, e3, e4, e5]`. Establish `b3 : C * (2 * Real.pi / rd) * N / I = (2 * Real.pi / rd) * (C * N / I)` using `by ring`. Rewrite using `[b3, mul_pow]`.

Generalize the expression as in `C * N / I = X`. Generalize the expression as in `(Real.sqrt TT)⁻¹ = Y`. Simplify using `only [div_eq_mul_inv, mul_pow, inv_pow, mul_inv, inv_inv]`. Establish `hg1 : g * g⁻¹ = 1` using `mul_inv_cancel₀ hg0`. Establish `hr1 : rd * rd⁻¹ = 1` using `mul_inv_cancel₀ hrd0`.

Take the linear combination `(C * A * Y * X ^ (2 * n) * ((2 * Real.pi) ^ (2 * r + 1))⁻¹ * (2 * Real.pi) ^ (2 * n + 1) * g ^ (2 * r + 2) * (g ^ (2 * n))⁻¹ * rd ^ (2 * r) * (rd ^ (2 * n))⁻¹) * hg1 - (C * A * Y * X ^ (2 * n) * ((2 * Real.pi) ^ (2 * r + 1))⁻¹ * (2 * Real.pi) ^ (2 * n + 1) * g ^ (2 * r + 2) * (g …`.
-/
theorem frame_product_identities : Formalism.FourierDecayAlt.J.FrameProducts := by
  intro r i s C rd g N I A TT hi hs hrd hg
  obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  have hrd0 : rd ≠ 0 := hrd.ne'
  have hg0 : g ≠ 0 := hg.ne'
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  have e1 : 2 * r + 2 - 1 = 2 * r + 1 := by omega
  constructor
  · have hz : rd ^ (S6.nuBlock (r : ℤ) ((n + 1 : ℕ) : ℤ) ((t + 1 : ℕ) : ℤ) + 1) =
        rd ^ (2 * r + 1) / rd ^ (2 * n + t) := by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_sub₀ hrd0]
      congr 1
      unfold S6.nuBlock
      push_cast
      ring
    have e2 : 2 * (n + 1 - 1) + (t + 1) - 1 = 2 * n + t := by omega
    unfold Sz.lamThreshold Sz.lamHat
    rw [hz, e1, e2]
    have b1 : C * (2 * Real.pi / g) * N / I = (2 * Real.pi / g) * (C * N / I) := by ring
    have b2 : C * (2 * Real.pi / rd) * N / (g * I) = (2 * Real.pi / (rd * g)) * (C * N / I) := by ring
    rw [b1, b2, mul_pow, mul_pow]
    generalize C * N / I = X
    simp only [div_eq_mul_inv, mul_pow, inv_pow, mul_inv, inv_inv]
    ring
  · have hz : rd ^ (S6.nuBlock (r : ℤ) ((n + 1 : ℕ) : ℤ) ((r : ℤ) + 2 - ((n + 1 : ℕ) : ℤ))) =
        rd ^ r / rd ^ n := by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_sub₀ hrd0]
      congr 1
      unfold S6.nuBlock
      push_cast
      ring
    have key : ∀ P a : ℝ, 0 ≤ a → √P * a = √(P * a ^ 2) := fun P a ha => by
      rw [Real.sqrt_mul' _ (sq_nonneg a), Real.sqrt_sq ha]
    rw [hz, key _ _ (mul_nonneg hg.le (div_nonneg (pow_nonneg hrd.le _) (pow_nonneg hrd.le _)))]
    unfold Sz.lamPrimeHat Sz.lamPrimeSq
    congr 1
    have e3 : 2 * (n + 1) - 1 = 2 * n + 1 := by omega
    have e4 : 2 * (n + 1 - 1) = 2 * n := by omega
    have e5 : 2 * (n + 1) - 2 = 2 * n := by omega
    rw [e1, e3, e4, e5]
    have b3 : C * (2 * Real.pi / rd) * N / I = (2 * Real.pi / rd) * (C * N / I) := by ring
    rw [b3, mul_pow]
    generalize C * N / I = X
    generalize (Real.sqrt TT)⁻¹ = Y
    simp only [div_eq_mul_inv, mul_pow, inv_pow, mul_inv, inv_inv]
    have hg1 : g * g⁻¹ = 1 := mul_inv_cancel₀ hg0
    have hr1 : rd * rd⁻¹ = 1 := mul_inv_cancel₀ hrd0
    linear_combination
      (C * A * Y * X ^ (2 * n) * ((2 * Real.pi) ^ (2 * r + 1))⁻¹ * (2 * Real.pi) ^ (2 * n + 1) *
          g ^ (2 * r + 2) * (g ^ (2 * n))⁻¹ * rd ^ (2 * r) * (rd ^ (2 * n))⁻¹) * hg1 -
        (C * A * Y * X ^ (2 * n) * ((2 * Real.pi) ^ (2 * r + 1))⁻¹ * (2 * Real.pi) ^ (2 * n + 1) *
          g ^ (2 * r + 2) * (g ^ (2 * n))⁻¹ * rd ^ (2 * r) * (rd ^ (2 * n))⁻¹) * hr1

end Formalism.FourierDecayAlt.P
