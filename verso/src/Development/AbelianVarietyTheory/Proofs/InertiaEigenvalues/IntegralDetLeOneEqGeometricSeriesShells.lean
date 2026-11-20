import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOfMemSmoothSpan
import Development.AbelianVarietyTheory.Definitions.Divisors.MemMspan
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNormRsHatLeConst
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaIntegralUpperMspan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousIntegralOfCompact
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetIntegralRsHatZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormRapidKernelSmoothSpanSmoothCuspidalBound
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DifferentiableIntegralMulCpow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegrableOnAbsDetRpowLeOneFundamentalDomain
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CuspRep GlobalTheory.UnitaryBC GroundTheory.Global.IdeleGroup Formalism.L2.Host
open scoped nonZeroDivisors ComplexConjugate

noncomputable section

namespace GlobalTheory.RSThetaGeom

/- English proof (translation)
Introduce `E _ _ _ a ha μ _ 𝓕 h𝓕 F hF C hC hinv χ hχ hχF s hs`. Use `set δ : GA E a → ℝ := fun g => (ideleModule E (GeneralLinearGroup.det g) : ℝ) with hδ`. Use `set L : ℝ := (a : ℝ) * (Module.finrank ℚ E : ℝ) with hLdef`. Use `set e : GA E a := splitCentre E a 1 with he`. Establish `hδc : Continuous δ` using `GlobalTheory.RSTheta.continuous_absDet`.

Establish `hδ0 : ∀ g, 0 < δ g` using `fun g => (ideleModule E _).2`. Establish `hδr : ∀ γ g, δ (ratGL E a γ * g) = δ g` using `fun γ g => by`. Simplify using `only [hδ, map_mul, GlobalTheory.ShortVecDecay.ideleModule_det_rat, one_mul]`. Establish `hd0 : (0 : ℝ) < Module.finrank ℚ E` using `Nat.cast_pos.2 Module.finrank_pos`. Establish `hL : 0 < L` using `mul_pos (Nat.cast_pos.2 ha) hd0`.

Establish `hTL : Real.exp 1 ^ (a * Module.finrank ℚ E) = Real.exp L`. Rewrite using `[Real.exp_one_pow, hLdef]`. Use `push_cast`. Both sides reduce to the same expression. Establish `hδk : ∀ (k : ℕ) g, δ (e ^ k * g) = Real.exp (L * k) * δ g` using `fun k g => by`.

Establish `h` using `GlobalTheory.RSTheta.absDet_zpow_mul (E := E) (a := a) (k : ℤ) g`. Rewrite `h` using `[zpow_natCast, hTL, zpow_natCast, ← Real.exp_nat_mul, mul_comm (k : ℝ)]`. Conclude with `h`. Establish `hFk : ∀ (k : ℕ) g, F (e ^ k * g) = χ ^ k * F g`. Introduce `k`.

Proceed by induction on `k with`. Consider the case `zero => intro g`. Simplify using the standard rewrite rules. Consider the case `succ k ih => intro g`. Rewrite using `[pow_succ', mul_assoc, hχF, ih, pow_succ']`.

Expand and normalize the polynomial expressions, which then agree. Use `set f : GA E a → ℂ := fun g => F g * ((δ g : ℝ) : ℂ) ^ (s - 1) with hf`. Establish `hfc : Continuous f` using `hF.mul ((Complex.continuous_ofReal.comp hδc).cpow continuous_const fun g => Complex.ofReal_mem_slitPlane.2 (hδ0 g))`. Establish `hfr : ∀ γ g, f (ratGL E a γ * g) = f g` using `fun γ g => by`. Simplify using `only [hf, hinv, hδr]`.

Use `set S : ℕ → Set (GA E a) := fun k => {g | Real.exp (-(L * ((k : ℝ) + 1))) < δ g ∧ δ g ≤ Real.exp (-(L * k))} with hS`. Establish `hSm : ∀ k, MeasurableSet (S k)` using `fun k => (isOpen_lt continuous_const hδc).measurableSet.inter (isClosed_le hδc continuous_const).measurableSet`. Establish `hSU : (⋃ k, S k) = {g | δ g ≤ 1}`. Use extensionality with `g`. Simplify using `only [hS, Set.mem_iUnion, Set.mem_setOf_eq]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨k, -, h2⟩`. Conclude with `h2.trans (Real.exp_le_one_iff.2 (by have : (0:ℝ) ≤ k := k.cast_nonneg; nlinarith))`. Introduce `h`. Establish `hl : 0 ≤ -Real.log (δ g) / L` using `div_nonneg (neg_nonneg.2 (Real.log_nonpos (hδ0 g).le h)) hL.le`.

Establish `h1` using `Nat.lt_floor_add_one (-Real.log (δ g) / L)`. Establish `h2` using `Nat.floor_le hl`. Use `set k := ⌊-Real.log (δ g) / L⌋₊`. Use `⟨k, ?_, ?_⟩` and prove the remaining obligations. Rewrite `h1` using `[div_lt_iff₀ hL]`.

Rewrite using `[← Real.exp_log (hδ0 g)]`. Conclude with `Real.exp_lt_exp.2 (by linarith)`. Rewrite `h2` using `[le_div_iff₀ hL]`. Rewrite using `[← Real.exp_log (hδ0 g)]`. Conclude with `Real.exp_le_exp.2 (by linarith)`.

Establish `hSd : Pairwise (Function.onFun Disjoint S)`. Establish `key : ∀ j k : ℕ, j < k → Disjoint (S j) (S k)`. Introduce `j k hjk`. Use `Set.disjoint_left.2 fun g hj hk => ?_` and prove the remaining obligations. Establish `h1 : Real.exp (-(L * k)) ≤ Real.exp (-(L * ((j : ℝ) + 1)))`.

Use `Real.exp_le_exp.2 ?_` and prove the remaining obligations. Establish `: (j : ℝ) + 1 ≤ k` using `by exact_mod_cast hjk`. Use the polynomial consequences of the given equalities and inequalities. Conclude with `absurd (hk.2.trans h1) (not_le.2 hj.1)`. Introduce `j k hjk`.

Break down `lt_or_gt_of_ne hjk with h | h` into its components or cases. Conclude with `key j k h`. Conclude with `(key k j h).symm`. Establish `hint : IntegrableOn f (𝓕 ∩ {g | δ g ≤ 1}) μ`. Establish `h0` using `(GlobalTheory.RSThetaLow.integrableOn_absDet_rpow_low E a ha μ 𝓕 h𝓕 (s.re - 1) (by linarith)).const_mul C`.

Use `h0.mono' hfc.aestronglyMeasurable.restrict (.of_forall fun g => ?_)` and prove the remaining obligations. Rewrite using `[hf, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (hδ0 g)]`. Simplify using `only [Complex.sub_re, Complex.one_re]`. Conclude with `mul_le_mul_of_nonneg_right (hC g) (Real.rpow_nonneg (hδ0 g).le _)`. Establish `hsum1` using `hasSum_integral_iUnion (μ := μ.restrict 𝓕) (f := f) hSm hSd (by rw [hSU, IntegrableOn, Measure.restrict_restrict (isClosed_le hδc continuous_const).measurableSet, Set.inter_comm]; exact hint)`.

Rewrite `hsum1` using `[hSU, Measure.restrict_restrict (isClosed_le hδc continuous_const).measurableSet, Set.inter_comm]`. Use `set r : ℂ := starRingEnd ℂ χ * Complex.exp (-(((L : ℝ) : ℂ) * (s - 1))) with hr`. Establish `hr1 : ‖r‖ < 1`. Establish `hre : (-(((L : ℝ) : ℂ) * (s - 1))).re = -(L * (s.re - 1))` using `by simp`. Establish `hpos : 0 < L * (s.re - 1)` using `mul_pos hL (by linarith)`.

Rewrite using `[hr, norm_mul, Complex.norm_conj, hχ, one_mul, Complex.norm_exp, hre]`. Conclude with `(Real.exp_lt_exp.2 (by linarith : -(L * (s.re - 1)) < 0)).trans_eq Real.exp_zero`. Establish `hcancel : ∀ k : ℕ, r ^ k * (χ ^ k * Complex.exp (((L * k : ℝ) : ℂ) * (s - 1))) = 1`. Introduce `k`. Establish `hc : starRingEnd ℂ χ * χ = 1`.

Rewrite using `[mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hχ]`. Simplify using the standard rewrite rules. Establish `he1 : Complex.exp (((L * k : ℝ) : ℂ) * (s - 1)) = Complex.exp (((L : ℝ) : ℂ) * (s - 1)) ^ k`. Rewrite using `[← Complex.exp_nat_mul]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[he1, ← mul_pow, ← mul_pow, hr]`. Establish `: starRingEnd ℂ χ * Complex.exp (-(((L : ℝ) : ℂ) * (s - 1))) * (χ * Complex.exp (((L : ℝ) : ℂ) * (s - 1))) = (starRingEnd ℂ χ * χ) * (Complex.exp (-(((L : ℝ) : ℂ) * (s - 1))) * Complex.exp (((L : ℝ) : ℂ) * (s - 1)))` using `by ring`. Rewrite using `[this, hc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero]`.

Simplify using the standard rewrite rules. Use `haveI : Countable (ratGL E a).range := by haveI : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable haveI : Countable (Matrix (Fin a) (Fin a) E) := inferInstanceAs (Countable (Fin a → Fin a → E)) haveI : Countable (GL (Fin a) E) := Units.val_injective.countable`. Conclude with `(ratGL E a).rangeRestrict_surjective.countable`. Establish `hexp : ∀ t : ℝ, ((Real.exp t : ℝ) : ℂ) ^ (s - 1) = Complex.exp (((t : ℝ) : ℂ) * (s - 1))`. Introduce `t`.

Rewrite using `[Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos t).ne'), ← Complex.ofReal_log (Real.exp_pos t).le, Real.log_exp]`. Establish `hfd : ∀ k : ℕ, IsFundamentalDomain (ratGL E a).range ((fun y => (e ^ k)⁻¹ * y) ⁻¹' 𝓕) μ`. Introduce `k`. Use `h𝓕.preimage_of_equiv (measurePreserving_mul_left μ ((e ^ k)⁻¹)).quasiMeasurePreserving (e := id) Function.bijective_id fun γ x => ?_` and prove the remaining obligations. Establish `hc0 : Commute e (γ : GA E a)` using `CuspidalL2GL.splitCentre_comm 1 _`.

Establish `hc : Commute ((e ^ k)⁻¹) (γ : GA E a)` using `(hc0.pow_left k).inv_left`. Use `show (e ^ k)⁻¹ * ((γ : GA E a) * x) = (γ : GA E a) * ((e ^ k)⁻¹ * x)`. Rewrite using `[← mul_assoc, hc.eq, mul_assoc]`. Establish `hG0 : ∀ (γ : (ratGL E a).range) (x : GA E a), (S 0).indicator f (γ • x) = (S 0).indicator f x`. Introduce and unpack `⟨_, γ, rfl⟩ x`.

Use `show (S 0).indicator f (ratGL E a γ * x) = (S 0).indicator f x`. Simplify using `only [Set.indicator_apply, hS, Set.mem_setOf_eq, hδr, hfr]`. Establish `hshell : ∀ k : ℕ, ∫ g in S k, f g ∂(μ.restrict 𝓕) = r ^ k * ∫ g in S 0, f g ∂(μ.restrict 𝓕)`. Introduce `k`. Establish `hX : 0 < Real.exp (L * k)` using `Real.exp_pos _`.

Establish `hmem : ∀ g, g ∈ S k ↔ e ^ k * g ∈ S 0`. Introduce `g`. Establish `e1 : Real.exp (L * k) * Real.exp (-(L * ((k : ℝ) + 1))) = Real.exp (-(L * (((0 : ℕ) : ℝ) + 1)))`. Rewrite using `[← Real.exp_add]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : Real.exp (L * k) * Real.exp (-(L * k)) = Real.exp (-(L * ((0 : ℕ) : ℝ)))`. Rewrite using `[← Real.exp_add]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `show (Real.exp (-(L * ((k : ℝ) + 1))) < δ g ∧ δ g ≤ Real.exp (-(L * k))) ↔ (Real.exp (-(L * (((0 : ℕ) : ℝ) + 1))) < δ (e ^ k * g) ∧ δ (e ^ k * g) ≤ Real.exp (-(L * ((0 : ℕ) : ℝ))))`. Rewrite using `[hδk, ← e1, ← e2, mul_lt_mul_iff_of_pos_left hX, mul_le_mul_iff_of_pos_left hX]`. Establish `hpt : ∀ g, (S k).indicator f g = r ^ k * (S 0).indicator f (e ^ k * g)`.

Introduce `g`. Distinguish the cases in `hg : g ∈ S k`. Rewrite using `[Set.indicator_of_mem hg, Set.indicator_of_mem ((hmem g).1 hg)]`. Simplify using `only [hf, hFk, hδk]`. Rewrite using `[Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (Real.exp_pos _).le (hδ0 g).le, hexp]`.

Take the linear combination `(-(F g * ((δ g : ℝ) : ℂ) ^ (s - 1))) * hcancel k`. Rewrite using `[Set.indicator_of_notMem hg, Set.indicator_of_notMem (mt (hmem g).2 hg), mul_zero]`. Establish `hpre : (fun x => e ^ k * x) ⁻¹' ((fun y => (e ^ k)⁻¹ * y) ⁻¹' 𝓕) = 𝓕` using `by ext x; simp`. Rewrite using `[← integral_indicator (hSm k), ← integral_indicator (hSm 0), integral_congr_ae (.of_forall hpt), integral_const_mul]`. Use `congr 1`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hpre]`. Use `_ = ∫ y in (fun y => (e ^ k)⁻¹ * y) ⁻¹' 𝓕, (S 0).indicator f y ∂μ := (measurePreserving_mul_left μ (e ^ k)).setIntegral_preimage_emb (measurableEmbedding_mulLeft _) _ _`. Use `_ = ∫ y in 𝓕, (S 0).indicator f y ∂μ := (hfd k).setIntegral_eq h𝓕 hG0`. Establish `hgeo` using `(hasSum_geometric_of_norm_lt_one hr1).mul_right (∫ g in S 0, f g ∂(μ.restrict 𝓕))`.

Establish `hsum2 : HasSum (fun k : ℕ => ∫ g in S k, f g ∂(μ.restrict 𝓕)) ((1 - r)⁻¹ * ∫ g in S 0, f g ∂(μ.restrict 𝓕))`. Rewrite using `[show (fun k : ℕ => ∫ g in S k, f g ∂(μ.restrict 𝓕)) = fun k => r ^ k * ∫ g in S 0, f g ∂(μ.restrict 𝓕) from`. Use function extensionality and compare the values at `hshell]`. Conclude with `hgeo`. Establish `hS0 : S 0 = {g | Real.exp (-L) < δ g ∧ δ g ≤ 1}`.

Use extensionality with `g`. Simplify using `[hS]`. Establish `hI0 : ∫ g in S 0, f g ∂(μ.restrict 𝓕) = ∫ g in 𝓕 ∩ {g | Real.exp (-L) < δ g ∧ δ g ≤ 1}, f g ∂μ`. Rewrite using `[Measure.restrict_restrict (hSm 0), Set.inter_comm, hS0]`. Use `show ∫ g in 𝓕 ∩ {g | δ g ≤ 1}, f g ∂μ = (∫ g in 𝓕 ∩ {g | Real.exp (-L) < δ g ∧ δ g ≤ 1}, f g ∂μ) / (1 - r)`.

Rewrite using `[← hI0, hsum1.unique hsum2, div_eq_inv_mul]`.
-/
theorem integral_low_geometric : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 0 < a → ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure] (𝓕 : Set (GA E a)), IsFundamentalDomain (ratGL E a).range 𝓕 μ → ∀ (F : GA E a → ℂ), Continuous F → ∀ C : ℝ, (∀ g, ‖F g‖ ≤ C) → (∀ (γ : GL (Fin a) E) (g : GA E a), F (ratGL E a γ * g) = F g) → ∀ χ : ℂ, ‖χ‖ = 1 → (∀ g, F (splitCentre E a 1 * g) = χ * F g) → ∀ s : ℂ, 1 < s.re → ∫ g in 𝓕 ∩ {g | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1}, F g * ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ) ^ (s - 1) ∂μ = (∫ g in 𝓕 ∩ {g | Real.exp (-((a : ℝ) * (Module.finrank ℚ E : ℝ))) < (ideleModule E (GeneralLinearGroup.det g) : ℝ) ∧ (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1}, F g * ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ) ^ (s - 1) ∂μ) / (1 - starRingEnd ℂ χ * Complex.exp (-((((a : ℝ) * (Module.finrank ℚ E : ℝ) : ℝ) : ℂ) * (s - 1)))) := by
  intro E _ _ _ a ha μ _ 𝓕 h𝓕 F hF C hC hinv χ hχ hχF s hs
  set δ : GA E a → ℝ := fun g => (ideleModule E (GeneralLinearGroup.det g) : ℝ) with hδ
  set L : ℝ := (a : ℝ) * (Module.finrank ℚ E : ℝ) with hLdef
  set e : GA E a := splitCentre E a 1 with he
  have hδc : Continuous δ := GlobalTheory.RSTheta.continuous_absDet
  have hδ0 : ∀ g, 0 < δ g := fun g => (ideleModule E _).2
  have hδr : ∀ γ g, δ (ratGL E a γ * g) = δ g := fun γ g => by
    simp only [hδ, map_mul, GlobalTheory.ShortVecDecay.ideleModule_det_rat, one_mul]
  have hd0 : (0 : ℝ) < Module.finrank ℚ E := Nat.cast_pos.2 Module.finrank_pos
  have hL : 0 < L := mul_pos (Nat.cast_pos.2 ha) hd0
  have hTL : Real.exp 1 ^ (a * Module.finrank ℚ E) = Real.exp L := by
    rw [Real.exp_one_pow, hLdef]; push_cast; rfl
  have hδk : ∀ (k : ℕ) g, δ (e ^ k * g) = Real.exp (L * k) * δ g := fun k g => by
    have h := GlobalTheory.RSTheta.absDet_zpow_mul (E := E) (a := a) (k : ℤ) g
    rw [zpow_natCast, hTL, zpow_natCast, ← Real.exp_nat_mul, mul_comm (k : ℝ)] at h
    exact h
  have hFk : ∀ (k : ℕ) g, F (e ^ k * g) = χ ^ k * F g := by
    intro k
    induction k with
    | zero => intro g; simp
    | succ k ih => intro g; rw [pow_succ', mul_assoc, hχF, ih, pow_succ']; ring

  set f : GA E a → ℂ := fun g => F g * ((δ g : ℝ) : ℂ) ^ (s - 1) with hf
  have hfc : Continuous f := hF.mul ((Complex.continuous_ofReal.comp hδc).cpow continuous_const
    fun g => Complex.ofReal_mem_slitPlane.2 (hδ0 g))
  have hfr : ∀ γ g, f (ratGL E a γ * g) = f g := fun γ g => by
    simp only [hf, hinv, hδr]

  set S : ℕ → Set (GA E a) := fun k => {g | Real.exp (-(L * ((k : ℝ) + 1))) < δ g ∧ δ g ≤ Real.exp (-(L * k))} with hS
  have hSm : ∀ k, MeasurableSet (S k) := fun k =>
    (isOpen_lt continuous_const hδc).measurableSet.inter (isClosed_le hδc continuous_const).measurableSet

  have hSU : (⋃ k, S k) = {g | δ g ≤ 1} := by
    ext g
    simp only [hS, Set.mem_iUnion, Set.mem_setOf_eq]
    constructor
    · rintro ⟨k, -, h2⟩
      exact h2.trans (Real.exp_le_one_iff.2 (by have : (0:ℝ) ≤ k := k.cast_nonneg; nlinarith))
    · intro h
      have hl : 0 ≤ -Real.log (δ g) / L := div_nonneg (neg_nonneg.2 (Real.log_nonpos (hδ0 g).le h)) hL.le
      have h1 := Nat.lt_floor_add_one (-Real.log (δ g) / L)
      have h2 := Nat.floor_le hl
      set k := ⌊-Real.log (δ g) / L⌋₊
      refine ⟨k, ?_, ?_⟩
      ·
        rw [div_lt_iff₀ hL] at h1
        rw [← Real.exp_log (hδ0 g)]
        exact Real.exp_lt_exp.2 (by linarith)
      · rw [le_div_iff₀ hL] at h2
        rw [← Real.exp_log (hδ0 g)]
        exact Real.exp_le_exp.2 (by linarith)
  have hSd : Pairwise (Function.onFun Disjoint S) := by
    have key : ∀ j k : ℕ, j < k → Disjoint (S j) (S k) := by
      intro j k hjk
      refine Set.disjoint_left.2 fun g hj hk => ?_
      have h1 : Real.exp (-(L * k)) ≤ Real.exp (-(L * ((j : ℝ) + 1))) := by
        refine Real.exp_le_exp.2 ?_
        have : (j : ℝ) + 1 ≤ k := by exact_mod_cast hjk
        nlinarith
      exact absurd (hk.2.trans h1) (not_le.2 hj.1)
    intro j k hjk
    rcases lt_or_gt_of_ne hjk with h | h
    · exact key j k h
    · exact (key k j h).symm

  have hint : IntegrableOn f (𝓕 ∩ {g | δ g ≤ 1}) μ := by
    have h0 := (GlobalTheory.RSThetaLow.integrableOn_absDet_rpow_low E a ha μ 𝓕 h𝓕 (s.re - 1) (by linarith)).const_mul C
    refine h0.mono' hfc.aestronglyMeasurable.restrict (.of_forall fun g => ?_)
    rw [hf, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (hδ0 g)]
    simp only [Complex.sub_re, Complex.one_re]
    exact mul_le_mul_of_nonneg_right (hC g) (Real.rpow_nonneg (hδ0 g).le _)
  have hsum1 := hasSum_integral_iUnion (μ := μ.restrict 𝓕) (f := f) hSm hSd
    (by rw [hSU, IntegrableOn, Measure.restrict_restrict (isClosed_le hδc continuous_const).measurableSet,
      Set.inter_comm]; exact hint)
  rw [hSU, Measure.restrict_restrict (isClosed_le hδc continuous_const).measurableSet, Set.inter_comm] at hsum1

  set r : ℂ := starRingEnd ℂ χ * Complex.exp (-(((L : ℝ) : ℂ) * (s - 1))) with hr
  have hr1 : ‖r‖ < 1 := by
    have hre : (-(((L : ℝ) : ℂ) * (s - 1))).re = -(L * (s.re - 1)) := by simp
    have hpos : 0 < L * (s.re - 1) := mul_pos hL (by linarith)
    rw [hr, norm_mul, Complex.norm_conj, hχ, one_mul, Complex.norm_exp, hre]
    exact (Real.exp_lt_exp.2 (by linarith : -(L * (s.re - 1)) < 0)).trans_eq Real.exp_zero
  have hcancel : ∀ k : ℕ, r ^ k * (χ ^ k * Complex.exp (((L * k : ℝ) : ℂ) * (s - 1))) = 1 := by
    intro k
    have hc : starRingEnd ℂ χ * χ = 1 := by
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hχ]; simp
    have he1 : Complex.exp (((L * k : ℝ) : ℂ) * (s - 1)) = Complex.exp (((L : ℝ) : ℂ) * (s - 1)) ^ k := by
      rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
    rw [he1, ← mul_pow, ← mul_pow, hr]
    have : starRingEnd ℂ χ * Complex.exp (-(((L : ℝ) : ℂ) * (s - 1))) * (χ * Complex.exp (((L : ℝ) : ℂ) * (s - 1))) =
        (starRingEnd ℂ χ * χ) * (Complex.exp (-(((L : ℝ) : ℂ) * (s - 1))) * Complex.exp (((L : ℝ) : ℂ) * (s - 1))) := by ring
    rw [this, hc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero]; simp

  haveI : Countable (ratGL E a).range := by
    haveI : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
    haveI : Countable (Matrix (Fin a) (Fin a) E) := inferInstanceAs (Countable (Fin a → Fin a → E))
    haveI : Countable (GL (Fin a) E) := Units.val_injective.countable
    exact (ratGL E a).rangeRestrict_surjective.countable
  have hexp : ∀ t : ℝ, ((Real.exp t : ℝ) : ℂ) ^ (s - 1) = Complex.exp (((t : ℝ) : ℂ) * (s - 1)) := by
    intro t
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos t).ne'), ← Complex.ofReal_log (Real.exp_pos t).le,
      Real.log_exp]
  have hfd : ∀ k : ℕ, IsFundamentalDomain (ratGL E a).range ((fun y => (e ^ k)⁻¹ * y) ⁻¹' 𝓕) μ := by
    intro k
    refine h𝓕.preimage_of_equiv (measurePreserving_mul_left μ ((e ^ k)⁻¹)).quasiMeasurePreserving
      (e := id) Function.bijective_id fun γ x => ?_
    have hc0 : Commute e (γ : GA E a) := CuspidalL2GL.splitCentre_comm 1 _
    have hc : Commute ((e ^ k)⁻¹) (γ : GA E a) := (hc0.pow_left k).inv_left
    show (e ^ k)⁻¹ * ((γ : GA E a) * x) = (γ : GA E a) * ((e ^ k)⁻¹ * x)
    rw [← mul_assoc, hc.eq, mul_assoc]
  have hG0 : ∀ (γ : (ratGL E a).range) (x : GA E a), (S 0).indicator f (γ • x) = (S 0).indicator f x := by
    rintro ⟨_, γ, rfl⟩ x
    show (S 0).indicator f (ratGL E a γ * x) = (S 0).indicator f x
    simp only [Set.indicator_apply, hS, Set.mem_setOf_eq, hδr, hfr]
  have hshell : ∀ k : ℕ, ∫ g in S k, f g ∂(μ.restrict 𝓕) = r ^ k * ∫ g in S 0, f g ∂(μ.restrict 𝓕) := by
    intro k
    have hX : 0 < Real.exp (L * k) := Real.exp_pos _
    have hmem : ∀ g, g ∈ S k ↔ e ^ k * g ∈ S 0 := by
      intro g
      have e1 : Real.exp (L * k) * Real.exp (-(L * ((k : ℝ) + 1))) = Real.exp (-(L * (((0 : ℕ) : ℝ) + 1))) := by
        rw [← Real.exp_add]; congr 1; push_cast; ring
      have e2 : Real.exp (L * k) * Real.exp (-(L * k)) = Real.exp (-(L * ((0 : ℕ) : ℝ))) := by
        rw [← Real.exp_add]; congr 1; push_cast; ring
      show (Real.exp (-(L * ((k : ℝ) + 1))) < δ g ∧ δ g ≤ Real.exp (-(L * k))) ↔
        (Real.exp (-(L * (((0 : ℕ) : ℝ) + 1))) < δ (e ^ k * g) ∧ δ (e ^ k * g) ≤ Real.exp (-(L * ((0 : ℕ) : ℝ))))
      rw [hδk, ← e1, ← e2, mul_lt_mul_iff_of_pos_left hX, mul_le_mul_iff_of_pos_left hX]
    have hpt : ∀ g, (S k).indicator f g = r ^ k * (S 0).indicator f (e ^ k * g) := by
      intro g
      by_cases hg : g ∈ S k
      · rw [Set.indicator_of_mem hg, Set.indicator_of_mem ((hmem g).1 hg)]
        simp only [hf, hFk, hδk]
        rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (Real.exp_pos _).le (hδ0 g).le, hexp]
        linear_combination (-(F g * ((δ g : ℝ) : ℂ) ^ (s - 1))) * hcancel k
      · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (mt (hmem g).2 hg), mul_zero]
    have hpre : (fun x => e ^ k * x) ⁻¹' ((fun y => (e ^ k)⁻¹ * y) ⁻¹' 𝓕) = 𝓕 := by ext x; simp
    rw [← integral_indicator (hSm k), ← integral_indicator (hSm 0), integral_congr_ae (.of_forall hpt),
      integral_const_mul]
    congr 1
    calc ∫ g in 𝓕, (S 0).indicator f (e ^ k * g) ∂μ
        = ∫ g in (fun x => e ^ k * x) ⁻¹' ((fun y => (e ^ k)⁻¹ * y) ⁻¹' 𝓕), (S 0).indicator f (e ^ k * g) ∂μ := by
          rw [hpre]
      _ = ∫ y in (fun y => (e ^ k)⁻¹ * y) ⁻¹' 𝓕, (S 0).indicator f y ∂μ :=
          (measurePreserving_mul_left μ (e ^ k)).setIntegral_preimage_emb (measurableEmbedding_mulLeft _) _ _
      _ = ∫ y in 𝓕, (S 0).indicator f y ∂μ := (hfd k).setIntegral_eq h𝓕 hG0
  have hgeo := (hasSum_geometric_of_norm_lt_one hr1).mul_right (∫ g in S 0, f g ∂(μ.restrict 𝓕))
  have hsum2 : HasSum (fun k : ℕ => ∫ g in S k, f g ∂(μ.restrict 𝓕))
      ((1 - r)⁻¹ * ∫ g in S 0, f g ∂(μ.restrict 𝓕)) := by
    rw [show (fun k : ℕ => ∫ g in S k, f g ∂(μ.restrict 𝓕)) = fun k => r ^ k * ∫ g in S 0, f g ∂(μ.restrict 𝓕) from
      funext hshell]
    exact hgeo
  have hS0 : S 0 = {g | Real.exp (-L) < δ g ∧ δ g ≤ 1} := by
    ext g; simp [hS]
  have hI0 : ∫ g in S 0, f g ∂(μ.restrict 𝓕) = ∫ g in 𝓕 ∩ {g | Real.exp (-L) < δ g ∧ δ g ≤ 1}, f g ∂μ := by
    rw [Measure.restrict_restrict (hSm 0), Set.inter_comm, hS0]
  show ∫ g in 𝓕 ∩ {g | δ g ≤ 1}, f g ∂μ = (∫ g in 𝓕 ∩ {g | Real.exp (-L) < δ g ∧ δ g ≤ 1}, f g ∂μ) / (1 - r)
  rw [← hI0, hsum1.unique hsum2, div_eq_inv_mul]

end GlobalTheory.RSThetaGeom

end
