import Mathlib
import GroundTheory.AutomorphicForms.GL2.GJInducedCoeff
import GroundTheory.AutomorphicForms.GL2.ExistsEqPowMulOfValuationLe
import GroundTheory.AutomorphicForms.GL2.GJInducedZeta
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Automorphic

namespace GodementJacquet

open Matrix GLnLocal Parabolic Iwasawa MeasureTheory Polynomial
open scoped NNReal ENNReal

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]

section Shells

/- English proof (translation)
The claim follows from `(isClopen_shell F n k).isOpen.measurableSet`.
-/
theorem measurableSet_shell (k : ℤ) : MeasurableSet {g : GL (Fin n) F | ordDet g = k} :=
  (isClopen_shell F n k).isOpen.measurableSet

omit [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)] in
/- English proof (translation)
Introduce `a b hab`. Use `Set.disjoint_left.2 fun g ha hb => hab ?_` and prove the remaining obligations. Conclude with `ha.symm.trans hb`.
-/
theorem pairwise_disjoint_shell :
    Pairwise (Function.onFun Disjoint fun k : ℤ => {g : GL (Fin n) F | ordDet g = k}) := by
  intro a b hab
  refine Set.disjoint_left.2 fun g ha hb => hab ?_
  exact ha.symm.trans hb

omit [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)] in
/- English proof (translation)
The claim follows from `Set.eq_univ_of_forall fun g => Set.mem_iUnion.2 ⟨ordDet g, rfl⟩`.
-/
theorem iUnion_shell : (⋃ k : ℤ, {g : GL (Fin n) F | ordDet g = k}) = Set.univ :=
  Set.eq_univ_of_forall fun g => Set.mem_iUnion.2 ⟨ordDet g, rfl⟩

/- English proof (translation)
Use `hasSum_integral_iUnion (μ := μ) (f := H) measurableSet_shell pairwise_disjoint_shell (by rw [iUnion_shell]; exact hH.integrableOn)` as an intermediate fact. Rewrite `this` using `[iUnion_shell, Measure.restrict_univ]`. Then use the resulting hypothesis.
-/
theorem hasSum_integral_shell (μ : Measure (GL (Fin n) F)) {H : GL (Fin n) F → ℂ}
    (hH : Integrable H μ) :
    HasSum (fun k : ℤ => ∫ g in {g : GL (Fin n) F | ordDet g = k}, H g ∂μ) (∫ g, H g ∂μ) := by
  have := hasSum_integral_iUnion (μ := μ) (f := H) measurableSet_shell pairwise_disjoint_shell
    (by rw [iUnion_shell]; exact hH.integrableOn)
  rwa [iUnion_shell, Measure.restrict_univ] at this

/- English proof (translation)
Rewrite using `[← lintegral_iUnion measurableSet_shell pairwise_disjoint_shell, iUnion_shell, Measure.restrict_univ]`.
-/
theorem lintegral_eq_tsum_shell (μ : Measure (GL (Fin n) F)) (H : GL (Fin n) F → ℝ≥0∞) :
    ∫⁻ g, H g ∂μ = ∑' k : ℤ, ∫⁻ g in {g : GL (Fin n) F | ordDet g = k}, H g ∂μ := by
  rw [← lintegral_iUnion measurableSet_shell pairwise_disjoint_shell, iUnion_shell,
    Measure.restrict_univ]

end Shells

section Bound

variable {α : Type*} [LinearOrder α] {β : Fin n → α}
  {W : Type*} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ (levi F n β) W}

/- English proof (translation)
Use `set f : GL (Fin n) F → ℂ := fun g => lam (parabolicInd F n β σ g φ) with hfdef`. Establish `hfl : ∀ k ∈ K, ∀ g, f (k * g) = f g` using `fun k hk g => by`. Simplify using `only [f, map_mul, Module.End.mul_apply, hlam k hk]`. Establish `hfr : ∀ k ∈ K, ∀ g, f (g * k) = f g` using `fun k hk g => by`. Simplify using `only [f, map_mul, Module.End.mul_apply]`.

Rewrite using `[show parabolicInd F n β σ k φ = φ from hφ k hk]`. Use `set u : GL (Fin n) F → ℂ := fun g => if h g * f g = 0 then 0 else (starRingEnd ℂ) (h g * f g) / (‖h g * f g‖ : ℂ) with hudef`. Establish `hu1 : ∀ g, ‖u g‖ ≤ 1` using `fun g => by`. Simplify using `only [u]`. Use `split_ifs with h0`.

Simplify using the standard rewrite rules. Rewrite using `[norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), div_self (norm_ne_zero_iff.2 h0)]`. Establish `huf : ∀ g, u g * h g * f g = (‖h g * f g‖ : ℂ)` using `fun g => by`. Simplify using `only [u]`. Use `split_ifs with h0`.

Simplify using `[h0]`. Establish `hne : ((‖h g * f g‖ : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast norm_ne_zero_iff.2 h0`. Rewrite using `[mul_assoc, div_mul_eq_mul_div, Complex.conj_mul', sq, mul_div_assoc, div_self hne, mul_one]`. Use `set h' : GL (Fin n) F → ℂ := fun g => u g * h g with hh'def`. Establish `hh' : HasCompactSupport h'` using `hh.mul_left`.

Establish `hul : ∀ k ∈ K, ∀ g, u (k * g) = u g` using `fun k hk g => by`. Simplify using `only [u, hhl k hk, hfl k hk]`. Establish `hur : ∀ k ∈ K, ∀ g, u (g * k) = u g` using `fun k hk g => by`. Simplify using `only [u, hhr k hk, hfr k hk]`. Establish `key` using `integral_mul_coeff_eq μ hKc hKo hφ hdec hh' (fun k hk g => by simp only [h', hul k hk, hhl k hk]) (fun k hk g => by simp only [h', hur k hk, hhr k hk])`.

Establish `hL : ∫ g, h' g * f g ∂μ = ((∫ g, ‖h g * f g‖ ∂μ : ℝ) : ℂ)`. Rewrite using `[← integral_complex_ofReal]`. Conclude with `integral_congr_ae (Filter.Eventually.of_forall fun g => by`. Simplify using `only [h']`. Conclude with `huf g)`.

Establish `hineq : ∫ g, ‖h g * f g‖ ∂μ ≤ ∑ x ∈ R, ∫ g, ‖h g‖ * ‖ℓ x ((φ : GL (Fin n) F → W) (x * g))‖ ∂μ`. Establish `h1 : ‖∫ g, h' g * f g ∂μ‖ = ∫ g, ‖h g * f g‖ ∂μ`. Rewrite using `[hL, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun g => norm_nonneg _)]`. Rewrite using `[← h1, key]`. Use `(norm_sum_le _ _).trans (Finset.sum_le_sum fun x hx => ?_)` and prove the remaining obligations.

Use `(norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg (Filter.Eventually.of_forall fun g => norm_nonneg _) (hint x hx) (Filter.Eventually.of_forall fun g => ?_))` and prove the remaining obligations. Simplify using `only [h', norm_mul]`. Conclude with `mul_le_mul_of_nonneg_right (mul_le_of_le_one_left (norm_nonneg _) (hu1 g)) (norm_nonneg _)`. Rewrite using `[← ofReal_integral_eq_lintegral_ofReal hhf (Filter.Eventually.of_forall fun g => norm_nonneg _)]`. Rewrite using `[Finset.sum_congr rfl fun x hx => (ofReal_integral_eq_lintegral_ofReal (hint x hx) (Filter.Eventually.of_forall fun g => mul_nonneg (norm_nonneg _) (norm_nonneg _))).symm, ← ENNReal.ofReal_sum_of_nonneg fun x _ => integral_nonneg fun g => mul_nonneg (norm_nonneg _) (norm_nonneg _ …`.

Conclude with `ENNReal.ofReal_le_ofReal hineq`.
-/
theorem lintegral_norm_mul_coeff_le (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure]
    {K : Subgroup (GL (Fin n) F)} (hKc : IsCompact (K : Set (GL (Fin n) F)))
    (hKo : IsOpen (K : Set (GL (Fin n) F)))
    {lam : Module.Dual ℂ (parabolicIndSpace F n β σ)}
    (hlam : ∀ k ∈ K, ∀ ψ, lam (parabolicInd F n β σ k ψ) = lam ψ)
    {φ : parabolicIndSpace F n β σ} (hφ : φ ∈ fixedVectors (parabolicInd F n β σ) K)
    {R : Finset (GL (Fin n) F)} {ℓ : GL (Fin n) F → Module.Dual ℂ W}
    (hdec : ∀ ψ ∈ fixedVectors (parabolicInd F n β σ) K,
      lam ψ = ∑ x ∈ R, ℓ x ((ψ : GL (Fin n) F → W) x))
    {h : GL (Fin n) F → ℂ} (hh : HasCompactSupport h) (hhl : ∀ k ∈ K, ∀ g, h (k * g) = h g)
    (hhr : ∀ k ∈ K, ∀ g, h (g * k) = h g)
    (hhf : Integrable (fun g => ‖h g * lam (parabolicInd F n β σ g φ)‖) μ)
    (hint : ∀ x ∈ R, Integrable (fun g => ‖h g‖ * ‖ℓ x ((φ : GL (Fin n) F → W) (x * g))‖) μ) :
    ∫⁻ g, ENNReal.ofReal ‖h g * lam (parabolicInd F n β σ g φ)‖ ∂μ ≤
      ∑ x ∈ R, ∫⁻ g, ENNReal.ofReal (‖h g‖ * ‖ℓ x ((φ : GL (Fin n) F → W) (x * g))‖) ∂μ := by
  classical
  set f : GL (Fin n) F → ℂ := fun g => lam (parabolicInd F n β σ g φ) with hfdef
  have hfl : ∀ k ∈ K, ∀ g, f (k * g) = f g := fun k hk g => by
    simp only [f, map_mul, Module.End.mul_apply, hlam k hk]
  have hfr : ∀ k ∈ K, ∀ g, f (g * k) = f g := fun k hk g => by
    simp only [f, map_mul, Module.End.mul_apply]
    rw [show parabolicInd F n β σ k φ = φ from hφ k hk]

  set u : GL (Fin n) F → ℂ := fun g => if h g * f g = 0 then 0 else
    (starRingEnd ℂ) (h g * f g) / (‖h g * f g‖ : ℂ) with hudef
  have hu1 : ∀ g, ‖u g‖ ≤ 1 := fun g => by
    simp only [u]
    split_ifs with h0
    · simp
    · rw [norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg _), div_self (norm_ne_zero_iff.2 h0)]
  have huf : ∀ g, u g * h g * f g = (‖h g * f g‖ : ℂ) := fun g => by
    simp only [u]
    split_ifs with h0
    · simp [h0]
    · have hne : ((‖h g * f g‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 h0
      rw [mul_assoc, div_mul_eq_mul_div, Complex.conj_mul', sq, mul_div_assoc, div_self hne,
        mul_one]
  set h' : GL (Fin n) F → ℂ := fun g => u g * h g with hh'def
  have hh' : HasCompactSupport h' := hh.mul_left
  have hul : ∀ k ∈ K, ∀ g, u (k * g) = u g := fun k hk g => by
    simp only [u, hhl k hk, hfl k hk]
  have hur : ∀ k ∈ K, ∀ g, u (g * k) = u g := fun k hk g => by
    simp only [u, hhr k hk, hfr k hk]
  have key := integral_mul_coeff_eq μ hKc hKo hφ hdec hh'
    (fun k hk g => by simp only [h', hul k hk, hhl k hk])
    (fun k hk g => by simp only [h', hur k hk, hhr k hk])

  have hL : ∫ g, h' g * f g ∂μ = ((∫ g, ‖h g * f g‖ ∂μ : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    exact integral_congr_ae (Filter.Eventually.of_forall fun g => by
      simp only [h']; exact huf g)
  have hineq : ∫ g, ‖h g * f g‖ ∂μ ≤
      ∑ x ∈ R, ∫ g, ‖h g‖ * ‖ℓ x ((φ : GL (Fin n) F → W) (x * g))‖ ∂μ := by
    have h1 : ‖∫ g, h' g * f g ∂μ‖ = ∫ g, ‖h g * f g‖ ∂μ := by
      rw [hL, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (integral_nonneg fun g => norm_nonneg _)]
    rw [← h1, key]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x hx => ?_)
    refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun g => norm_nonneg _) (hint x hx)
      (Filter.Eventually.of_forall fun g => ?_))
    simp only [h', norm_mul]
    exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_left (norm_nonneg _) (hu1 g))
      (norm_nonneg _)
  rw [← ofReal_integral_eq_lintegral_ofReal hhf (Filter.Eventually.of_forall fun g => norm_nonneg _)]
  rw [Finset.sum_congr rfl fun x hx => (ofReal_integral_eq_lintegral_ofReal (hint x hx)
    (Filter.Eventually.of_forall fun g => mul_nonneg (norm_nonneg _) (norm_nonneg _))).symm,
    ← ENNReal.ofReal_sum_of_nonneg fun x _ => integral_nonneg fun g =>
      mul_nonneg (norm_nonneg _) (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal hineq

end Bound

section Core

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin n) F) V}

omit [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)] in

/- English proof (translation)
Rewrite using `[IsLocallyConstant.iff_exists_open]`. Introduce `x`. Use `⟨(fun y => x⁻¹ * y) ⁻¹' (K : Set (GL (Fin n) F)), hKo.preimage (continuous_const.mul continuous_id), by simp [K.one_mem], fun y hy => ?_⟩` and prove the remaining obligations. Use `hf x (x⁻¹ * y) hy` as an intermediate fact. Rewrite `this` using `[mul_inv_cancel_left]`. Then use the resulting hypothesis.
-/
theorem isLocallyConstant_of_mul_right {γ : Type*} {K : Subgroup (GL (Fin n) F)}
    (hKo : IsOpen (K : Set (GL (Fin n) F))) {f : GL (Fin n) F → γ}
    (hf : ∀ g, ∀ k ∈ K, f (g * k) = f g) : IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨(fun y => x⁻¹ * y) ⁻¹' (K : Set (GL (Fin n) F)),
    hKo.preimage (continuous_const.mul continuous_id), by simp [K.one_mem], fun y hy => ?_⟩
  have := hf x (x⁻¹ * y) hy
  rwa [mul_inv_cancel_left] at this

/- English proof (translation)
Take `⟨β, W, _, _, σ, hσirr, hσs, hσc, -, ι, hι⟩` from `exists_embedding_parabolicInd (π := π) hπ.1`. Use `hσirr` as an intermediate fact. Take `⟨s₀, D, hD0, hJ⟩` from `exists_inducedZeta (β := β) hσs hσc μ`. Use `⟨s₀, D, hD0, fun Φ hΦ v ℓ hℓ => ?_⟩` and prove the remaining obligations. Take `⟨m₀, hm₀⟩` from `hΦ.exists_congruence_invariant`.

Take `⟨m₁, -, hm₁⟩` from `(hasBasis_nhds_one F n).mem_iff.1 ((hπ.1 v).mem_nhds (one_mem (stabilizerOf π v)))`. Take `⟨m₂, -, hm₂⟩` from `(hasBasis_nhds_one F n).mem_iff.1 ((mem_smoothVectors.1 hℓ).mem_nhds (one_mem (stabilizerOf (Representation.dual π) ℓ)))`. Use `set m := max m₀ (max m₁ m₂) with hmdef`. Use `set K := congruenceSubgroup F n m with hKdef`. Establish `hKc : IsCompact (K : Set (GL (Fin n) F))` using `isCompact_congruenceSubgroup F n m`.

Establish `hKo : IsOpen (K : Set (GL (Fin n) F))` using `isOpen_congruenceSubgroup F n m`. Establish `hK0 : ∀ k ∈ K, k ∈ integralGL F n` using `fun k hk => congruenceSubgroup_le F n m hk`. Establish `hvK : ∀ k ∈ K, π k v = v` using `fun k hk => hm₁ (congruenceSubgroup_antitone F n (le_max_of_le_right (le_max_left m₁ m₂)) hk)`. Establish `hℓK : ∀ k ∈ K, ∀ x, ℓ (π k x) = ℓ x` using `mem_fixedVectors_dual.1 fun k hk => hm₂ (congruenceSubgroup_antitone F n (le_max_of_le_right (le_max_right m₁ m₂)) hk)`. Establish `hΦK : ∀ k ∈ K, ∀ X, Φ ((k : Matrix (Fin n) (Fin n) F) * X) = Φ X ∧ Φ (X * (k : Matrix (Fin n) (Fin n) F)) = Φ X` using `fun k hk => hm₀ k (congruenceSubgroup_antitone F n (le_max_left _ _) hk)`.

Take `⟨lam, hlamK, hlam⟩` from `exists_extend_dual hπ.1 (isSmooth_parabolicInd σ) ι hι hKc hKo hℓK`. Take `⟨R, hR₀, hR⟩` from `exists_reps_congruenceSubgroup F n m`. Take `⟨ℓx, hℓxK, hdec⟩` from `exists_eval_decomposition hσs hR₀ hR lam`. Use `set φ : parabolicIndSpace F n β σ := ι v with hφdef`. Establish `hφK : φ ∈ fixedVectors (parabolicInd F n β σ) K` using `fun k hk => by`.

Rewrite using `[hφdef, ← ι.isIntertwining, hvK k hk]`. Establish `hf : ∀ g, matrixCoeff π v ℓ g = lam (parabolicInd F n β σ g φ)` using `fun g => by`. Rewrite using `[matrixCoeff, ← hlam, hφdef, ι.isIntertwining]`. Establish `hℓxs : ∀ x, ℓx x ∈ smoothVectors (Representation.dual σ)` using `fun x => mem_smoothVectors_of_mem_fixedVectors (isOpen_subgroupOf_levi hKo) (hℓxK x)`. Establish `hJx` using `fun x : GL (Fin n) F => hJ (fun X => Φ (((x⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * X)) (hΦ.comp_mul_left x⁻¹) (φ : GL (Fin n) F → W) φ.2 (ℓx x) (hℓxs x)`.

Use `choose hJint N P hJeq using hJx`. Use `set T : GL (Fin n) F → ℂ → GL (Fin n) F → ℂ := fun x s g => Φ (g : Matrix (Fin n) (Fin n) F) * detPow g s * ℓx x ((φ : GL (Fin n) F → W) (x * g)) with hTdef`. Establish `hTJ : ∀ x ∈ R, ∀ s g, T x s g = (fun y : GL (Fin n) F => Φ (((x⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (y : Matrix (Fin n) (Fin n) F)) * detPow y s * ℓx x ((φ : GL (Fin n) F → W) y)) (x * g)`. Introduce `x hx s g`. Simplify using `only [T]`.

Rewrite using `[detPow_mul, detPow_of_mem_integralGL (hR₀ x hx), one_mul, Units.val_mul, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]`. Establish `hTint : ∀ x ∈ R, ∀ s : ℂ, s₀ < s.re → Integrable (T x s) μ`. Introduce `x hx s hs`. Conclude with `((hJint x s hs).comp_mul_left x).congr (Filter.Eventually.of_forall fun g => (hTJ x hx s g).symm)`. Establish `hTeq : ∀ x ∈ R, ∀ s, ∫ g, T x s g ∂μ = ∫ g, Φ (((x⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (g : Matrix (Fin n) (Fin n) F)) * detPow g s * ℓx x ((φ : GL (Fin n) F → W) g) ∂μ`.

Introduce `x hx s`. Rewrite using `[integral_congr_ae (Filter.Eventually.of_forall (hTJ x hx s))]`. Conclude with `integral_mul_left_eq_self (μ := μ) (fun y : GL (Fin n) F => Φ (((x⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (y : Matrix (Fin n) (Fin n) F)) * detPow y s * ℓx x ((φ : GL (Fin n) F → W) y)) x`. Take `⟨r, A, -, hA⟩` from `hΦ.exists_invariant`. Use `set h : ℤ → GL (Fin n) F → ℂ := fun k => {g : GL (Fin n) F | ordDet g = k}.indicator fun g => Φ (g : Matrix (Fin n) (Fin n) F) with hhdef`.

Establish `hhcs : ∀ k, HasCompactSupport (h k)` using `fun k => HasCompactSupport.intro (isCompact_shell F n A k) fun g hg => by`. Simplify using `only [h, Set.indicator_apply, Set.mem_ofPred_eq]`. Use `split_ifs with hk`. Assume the negation of the conclusion as `hne`. Conclude with `hg ⟨hA _ hne, hk⟩`.

Both sides reduce to the same expression. Establish `hhl : ∀ k, ∀ k' ∈ K, ∀ g, h k (k' * g) = h k g` using `fun k k' hk' g => by`. Simplify using `only [h, Set.indicator_apply, Set.mem_ofPred_eq, ordDet_mul, ordDet_of_mem_integralGL (hK0 k' hk'), zero_add, Units.val_mul, (hΦK k' hk' _).1]`. Establish `hhr : ∀ k, ∀ k' ∈ K, ∀ g, h k (g * k') = h k g` using `fun k k' hk' g => by`. Simplify using `only [h, Set.indicator_apply, Set.mem_ofPred_eq, ordDet_mul, ordDet_of_mem_integralGL (hK0 k' hk'), add_zero, Units.val_mul, (hΦK k' hk' _).2]`.

Establish `hcont : ∀ H : GL (Fin n) F → ℂ, (∀ g, ∀ k ∈ K, H (g * k) = H g) → Continuous H` using `fun H hH => (isLocallyConstant_of_mul_right hKo hH).continuous`. Establish `hfr : ∀ g, ∀ k ∈ K, lam (parabolicInd F n β σ (g * k) φ) = lam (parabolicInd F n β σ g φ)` using `fun g k hk => by rw [map_mul, Module.End.mul_apply, show parabolicInd F n β σ k φ = φ from hφK k hk]`. Establish `hφr : ∀ x g, ∀ k ∈ K, (φ : GL (Fin n) F → W) (x * (g * k)) = (φ : GL (Fin n) F → W) (x * g)` using `fun x g k hk => by`. Use `congrArg (fun ψ : parabolicIndSpace F n β σ => (ψ : GL (Fin n) F → W) (x * g)) (hφK k hk)` as an intermediate fact. Simplify using `only [coe_indRep_apply] at this`.

Rewrite using `[← mul_assoc, this]`. Establish `hdetr : ∀ s g, ∀ k ∈ K, detPow (g * k) s = detPow g s` using `fun s g k hk => by`. Rewrite using `[detPow_mul, detPow_of_mem_integralGL (hK0 k hk), mul_one]`. Establish `hΦr : ∀ g, ∀ k ∈ K, Φ ((g * k : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = Φ (g : Matrix (Fin n) (Fin n) F)` using `fun g k hk => by rw [Units.val_mul, (hΦK k hk _).2]`. Establish `hhf : ∀ k, Integrable (fun g => ‖h k g * lam (parabolicInd F n β σ g φ)‖) μ` using `fun k => ((hcont _ fun g k' hk' => by rw [hhr k k' hk', hfr g k' hk']).norm).integrable_of_hasCompactSupport (hhcs k).mul_right.norm`.

Establish `hhint : ∀ k, ∀ x ∈ R, Integrable (fun g => ‖h k g‖ * ‖ℓx x ((φ : GL (Fin n) F → W) (x * g))‖) μ` using `fun k x _ => ((hcont _ fun g k' hk' => by rw [hhr k k' hk']).norm.mul (hcont _ fun g k' hk' => by rw [hφr x g k' hk']).norm).integrable_of_hasCompactSupport (hhcs k).norm.mul_right`. Establish `hshellZ : ∀ s k g, {g : GL (Fin n) F | ordDet g = k}.indicator (fun g => Φ (g : Matrix (Fin n) (Fin n) F) * matrixCoeff π v ℓ g * detPow g s) g = qs F s ^ k * (h k g * lam (parabolicInd F n β σ g φ))`. Introduce `s k g`. Simplify using `only [h, Set.indicator_apply, Set.mem_ofPred_eq]`. Use `split_ifs with hk`.

Rewrite using `[hf g, detPow_eq_qs_zpow, hk]`. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules. Establish `hshellT : ∀ x s k g, {g : GL (Fin n) F | ordDet g = k}.indicator (T x s) g = qs F s ^ k * (h k g * ℓx x ((φ : GL (Fin n) F → W) (x * g)))`. Introduce `x s k g`.

Simplify using `only [h, T, Set.indicator_apply, Set.mem_ofPred_eq]`. Use `split_ifs with hk`. Rewrite using `[detPow_eq_qs_zpow, hk]`. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules.

Establish `hZint : ∀ s : ℂ, s₀ < s.re → Integrable (fun g : GL (Fin n) F => Φ (g : Matrix (Fin n) (Fin n) F) * matrixCoeff π v ℓ g * detPow g s) μ`. Introduce `s hs`. Use `⟨(hcont _ fun g k hk => by` and prove the remaining obligations. Rewrite using `[hΦr g k hk, hdetr s g k hk, hf, hf, hfr g k hk]).aestronglyMeasurable, ?_⟩`. Rewrite using `[HasFiniteIntegral]`.

Repeatedly rewrite using `[← ofReal_norm]`. Rewrite using `[lintegral_eq_tsum_shell]`. Establish `hterm : ∀ k : ℤ, ∫⁻ g in {g : GL (Fin n) F | ordDet g = k}, ENNReal.ofReal ‖Φ (g : Matrix (Fin n) (Fin n) F) * matrixCoeff π v ℓ g * detPow g s‖ ∂μ ≤ ∑ x ∈ R, ∫⁻ g in {g : GL (Fin n) F | ordDet g = k}, ENNReal.ofReal ‖T x s g‖ ∂μ`. Introduce `k`. Establish `e1 : ∀ g, {g : GL (Fin n) F | ordDet g = k}.indicator (fun g => ENNReal.ofReal ‖Φ (g : Matrix (Fin n) (Fin n) F) * matrixCoeff π v ℓ g * detPow g s‖) g = ENNReal.ofReal (‖qs F s‖ ^ k) * ENNReal.ofReal ‖h k g * lam (parabolicInd F n β σ g φ)‖`.

Introduce `g`. Rewrite using `[← ENNReal.ofReal_mul (zpow_nonneg (norm_nonneg _) _), ← norm_zpow, ← norm_mul, ← hshellZ s k g]`. Distinguish the cases in `hg : g ∈ {g : GL (Fin n) F | ordDet g = k}`. Simplify using `[Set.indicator_of_mem hg]`. Simplify using `[Set.indicator_of_notMem hg]`.

Establish `e2 : ∀ x g, {g : GL (Fin n) F | ordDet g = k}.indicator (fun g => ENNReal.ofReal ‖T x s g‖) g = ENNReal.ofReal (‖qs F s‖ ^ k) * ENNReal.ofReal (‖h k g‖ * ‖ℓx x ((φ : GL (Fin n) F → W) (x * g))‖)`. Introduce `x g`. Rewrite using `[← ENNReal.ofReal_mul (zpow_nonneg (norm_nonneg _) _), ← norm_zpow, ← norm_mul, ← norm_mul, ← hshellT x s k g]`. Distinguish the cases in `hg : g ∈ {g : GL (Fin n) F | ordDet g = k}`. Simplify using `[Set.indicator_of_mem hg]`.

Simplify using `[Set.indicator_of_notMem hg]`. Rewrite using `[← lintegral_indicator (measurableSet_shell k), lintegral_congr e1, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]`. Repeatedly rewrite using `[← lintegral_indicator (measurableSet_shell k), e2]`. Repeatedly rewrite using `[lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← Finset.mul_sum]`. Conclude with `mul_le_mul' le_rfl (lintegral_norm_mul_coeff_le μ hKc hKo hlamK hφK hdec (hhcs k) (hhl k) (hhr k) (hhf k) (hhint k))`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Summable.tsum_finsetSum fun _ _ => ENNReal.summable]`. Conclude with `Finset.sum_congr rfl fun x _ => (lintegral_eq_tsum_shell μ _).symm`. Use `_ < ∞ := by`. Use `ENNReal.sum_lt_top.2 fun x hx => ?_` and prove the remaining obligations.

Use `(hTint x hx s hs).2` as an intermediate fact. Simplify `this` using `[HasFiniteIntegral, ofReal_norm]`. Use `⟨hZint, ?_⟩` and prove the remaining obligations. Use `⟨∑ x ∈ R, N x, ∑ x ∈ R, P x * X ^ (∑ y ∈ R, N y - N x), fun s hs => ?_⟩` and prove the remaining obligations. Establish `hZsum` using `hasSum_integral_shell μ (hZint s hs)`.

Establish `hTsum : ∀ x ∈ R, HasSum (fun k : ℤ => ∫ g in {g : GL (Fin n) F | ordDet g = k}, T x s g ∂μ) (∫ g, T x s g ∂μ)` using `fun x hx => hasSum_integral_shell μ (hTint x hx s hs)`. Establish `hsum` using `hasSum_sum hTsum`. Establish `hshell_eq : ∀ k : ℤ, ∫ g in {g : GL (Fin n) F | ordDet g = k}, Φ (g : Matrix (Fin n) (Fin n) F) * matrixCoeff π v ℓ g * detPow g s ∂μ = ∑ x ∈ R, ∫ g in {g : GL (Fin n) F | ordDet g = k}, T x s g ∂μ`. Introduce `k`. Rewrite using `[← integral_indicator (measurableSet_shell k)]`.

Repeatedly rewrite using `[hshellZ s k]`. Rewrite using `[integral_const_mul, integral_mul_coeff_eq μ hKc hKo hφK hdec (hhcs k) (hhl k) (hhr k), Finset.mul_sum]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Rewrite using `[← integral_indicator (measurableSet_shell k)]`. Repeatedly rewrite using `[hshellT x s k]`.

Rewrite using `[integral_const_mul]`. Establish `hZ : ∫ g, Φ (g : Matrix (Fin n) (Fin n) F) * matrixCoeff π v ℓ g * detPow g s ∂μ = ∑ x ∈ R, ∫ g, T x s g ∂μ`. Use `hZsum.unique ?_` and prove the remaining obligations. Use `hsum using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `k`.

Conclude with `hshell_eq k`. Establish `hterm : ∀ x ∈ R, D.eval (qs F s) * ∫ g, T x s g ∂μ = (P x).eval (qs F s) / qs F s ^ N x`. Introduce `x hx`. Rewrite using `[hTeq x hx s]`. Conclude with `hJeq x s hs`.

Rewrite using `[hZ, Finset.mul_sum, Finset.sum_congr rfl hterm, eval_finsetSum, Finset.sum_div]`. Use `Finset.sum_congr rfl fun x hx => ?_` and prove the remaining obligations. Establish `hle : N x ≤ ∑ y ∈ R, N y` using `Finset.single_le_sum (fun _ _ => Nat.zero_le _) hx`. Rewrite using `[eval_mul, eval_pow, eval_X, pow_sub₀ _ (qs_ne_zero s) hle]`. Clear the denominators using the available nonvanishing facts.

Conclude with `(mul_div_mul_right _ _ (pow_ne_zero _ (qs_ne_zero s))).symm`.
-/
theorem exists_zeta_core [π.IsIrreducible] (hπ : IsAdmissible π)
    (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure] :
    ∃ s₀ : ℝ, ∃ D : ℂ[X], D.eval 0 = 1 ∧
      ∀ Φ : Matrix (Fin n) (Fin n) F → ℂ, IsSchwartzBruhat Φ → ∀ (v : V) (ℓ : Module.Dual ℂ V),
        ℓ ∈ smoothVectors (Representation.dual π) →
        (∀ s : ℂ, s₀ < s.re → Integrable (fun g : GL (Fin n) F =>
          Φ (g : Matrix (Fin n) (Fin n) F) * matrixCoeff π v ℓ g * detPow g s) μ) ∧
        ∃ (N : ℕ) (P : ℂ[X]), ∀ s : ℂ, s₀ < s.re →
          D.eval (qs F s) * ∫ g, Φ (g : Matrix (Fin n) (Fin n) F) * matrixCoeff π v ℓ g *
            detPow g s ∂μ = P.eval (qs F s) / qs F s ^ N := by
  classical
  obtain ⟨β, W, _, _, σ, hσirr, hσs, hσc, -, ι, hι⟩ := exists_embedding_parabolicInd (π := π) hπ.1
  have := hσirr
  obtain ⟨s₀, D, hD0, hJ⟩ := exists_inducedZeta (β := β) hσs hσc μ
  refine ⟨s₀, D, hD0, fun Φ hΦ v ℓ hℓ => ?_⟩

  obtain ⟨m₀, hm₀⟩ := hΦ.exists_congruence_invariant
  obtain ⟨m₁, -, hm₁⟩ := (hasBasis_nhds_one F n).mem_iff.1
    ((hπ.1 v).mem_nhds (one_mem (stabilizerOf π v)))
  obtain ⟨m₂, -, hm₂⟩ := (hasBasis_nhds_one F n).mem_iff.1
    ((mem_smoothVectors.1 hℓ).mem_nhds (one_mem (stabilizerOf (Representation.dual π) ℓ)))
  set m := max m₀ (max m₁ m₂) with hmdef
  set K := congruenceSubgroup F n m with hKdef
  have hKc : IsCompact (K : Set (GL (Fin n) F)) := isCompact_congruenceSubgroup F n m
  have hKo : IsOpen (K : Set (GL (Fin n) F)) := isOpen_congruenceSubgroup F n m
  have hK0 : ∀ k ∈ K, k ∈ integralGL F n := fun k hk => congruenceSubgroup_le F n m hk
  have hvK : ∀ k ∈ K, π k v = v := fun k hk =>
    hm₁ (congruenceSubgroup_antitone F n (le_max_of_le_right (le_max_left m₁ m₂)) hk)
  have hℓK : ∀ k ∈ K, ∀ x, ℓ (π k x) = ℓ x := mem_fixedVectors_dual.1 fun k hk =>
    hm₂ (congruenceSubgroup_antitone F n (le_max_of_le_right (le_max_right m₁ m₂)) hk)
  have hΦK : ∀ k ∈ K, ∀ X, Φ ((k : Matrix (Fin n) (Fin n) F) * X) = Φ X ∧
      Φ (X * (k : Matrix (Fin n) (Fin n) F)) = Φ X := fun k hk =>
    hm₀ k (congruenceSubgroup_antitone F n (le_max_left _ _) hk)

  obtain ⟨lam, hlamK, hlam⟩ := exists_extend_dual hπ.1 (isSmooth_parabolicInd σ) ι hι hKc hKo hℓK
  obtain ⟨R, hR₀, hR⟩ := exists_reps_congruenceSubgroup F n m
  obtain ⟨ℓx, hℓxK, hdec⟩ := exists_eval_decomposition hσs hR₀ hR lam
  set φ : parabolicIndSpace F n β σ := ι v with hφdef
  have hφK : φ ∈ fixedVectors (parabolicInd F n β σ) K := fun k hk => by
    rw [hφdef, ← ι.isIntertwining, hvK k hk]
  have hf : ∀ g, matrixCoeff π v ℓ g = lam (parabolicInd F n β σ g φ) := fun g => by
    rw [matrixCoeff, ← hlam, hφdef, ι.isIntertwining]
  have hℓxs : ∀ x, ℓx x ∈ smoothVectors (Representation.dual σ) := fun x =>
    mem_smoothVectors_of_mem_fixedVectors (isOpen_subgroupOf_levi hKo) (hℓxK x)

  have hJx := fun x : GL (Fin n) F => hJ
    (fun X => Φ (((x⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * X))
    (hΦ.comp_mul_left x⁻¹) (φ : GL (Fin n) F → W) φ.2 (ℓx x) (hℓxs x)
  choose hJint N P hJeq using hJx

  set T : GL (Fin n) F → ℂ → GL (Fin n) F → ℂ := fun x s g =>
    Φ (g : Matrix (Fin n) (Fin n) F) * detPow g s * ℓx x ((φ : GL (Fin n) F → W) (x * g))
    with hTdef
  have hTJ : ∀ x ∈ R, ∀ s g, T x s g = (fun y : GL (Fin n) F =>
      Φ (((x⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (y : Matrix (Fin n) (Fin n) F)) *
        detPow y s * ℓx x ((φ : GL (Fin n) F → W) y)) (x * g) := by
    intro x hx s g
    simp only [T]
    rw [detPow_mul, detPow_of_mem_integralGL (hR₀ x hx), one_mul, Units.val_mul, ← mul_assoc,
      ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
  have hTint : ∀ x ∈ R, ∀ s : ℂ, s₀ < s.re → Integrable (T x s) μ := by
    intro x hx s hs
    exact ((hJint x s hs).comp_mul_left x).congr
      (Filter.Eventually.of_forall fun g => (hTJ x hx s g).symm)
  have hTeq : ∀ x ∈ R, ∀ s, ∫ g, T x s g ∂μ = ∫ g,
      Φ (((x⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (g : Matrix (Fin n) (Fin n) F)) *
        detPow g s * ℓx x ((φ : GL (Fin n) F → W) g) ∂μ := by
    intro x hx s
    rw [integral_congr_ae (Filter.Eventually.of_forall (hTJ x hx s))]
    exact integral_mul_left_eq_self (μ := μ) (fun y : GL (Fin n) F =>
      Φ (((x⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (y : Matrix (Fin n) (Fin n) F)) *
        detPow y s * ℓx x ((φ : GL (Fin n) F → W) y)) x

  obtain ⟨r, A, -, hA⟩ := hΦ.exists_invariant
  set h : ℤ → GL (Fin n) F → ℂ := fun k =>
    {g : GL (Fin n) F | ordDet g = k}.indicator fun g => Φ (g : Matrix (Fin n) (Fin n) F)
    with hhdef
  have hhcs : ∀ k, HasCompactSupport (h k) := fun k =>
    HasCompactSupport.intro (isCompact_shell F n A k) fun g hg => by
      simp only [h, Set.indicator_apply, Set.mem_ofPred_eq]
      split_ifs with hk
      · by_contra hne
        exact hg ⟨hA _ hne, hk⟩
      · rfl
  have hhl : ∀ k, ∀ k' ∈ K, ∀ g, h k (k' * g) = h k g := fun k k' hk' g => by
    simp only [h, Set.indicator_apply, Set.mem_ofPred_eq, ordDet_mul,
      ordDet_of_mem_integralGL (hK0 k' hk'), zero_add, Units.val_mul, (hΦK k' hk' _).1]
  have hhr : ∀ k, ∀ k' ∈ K, ∀ g, h k (g * k') = h k g := fun k k' hk' g => by
    simp only [h, Set.indicator_apply, Set.mem_ofPred_eq, ordDet_mul,
      ordDet_of_mem_integralGL (hK0 k' hk'), add_zero, Units.val_mul, (hΦK k' hk' _).2]

  have hcont : ∀ H : GL (Fin n) F → ℂ, (∀ g, ∀ k ∈ K, H (g * k) = H g) → Continuous H :=
    fun H hH => (isLocallyConstant_of_mul_right hKo hH).continuous
  have hfr : ∀ g, ∀ k ∈ K, lam (parabolicInd F n β σ (g * k) φ) = lam (parabolicInd F n β σ g φ) :=
    fun g k hk => by rw [map_mul, Module.End.mul_apply, show parabolicInd F n β σ k φ = φ from hφK k hk]
  have hφr : ∀ x g, ∀ k ∈ K, (φ : GL (Fin n) F → W) (x * (g * k)) = (φ : GL (Fin n) F → W) (x * g) :=
    fun x g k hk => by
      have := congrArg (fun ψ : parabolicIndSpace F n β σ => (ψ : GL (Fin n) F → W) (x * g)) (hφK k hk)
      simp only [coe_indRep_apply] at this
      rw [← mul_assoc, this]
  have hdetr : ∀ s g, ∀ k ∈ K, detPow (g * k) s = detPow g s := fun s g k hk => by
    rw [detPow_mul, detPow_of_mem_integralGL (hK0 k hk), mul_one]
  have hΦr : ∀ g, ∀ k ∈ K, Φ ((g * k : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      Φ (g : Matrix (Fin n) (Fin n) F) := fun g k hk => by rw [Units.val_mul, (hΦK k hk _).2]

  have hhf : ∀ k, Integrable (fun g => ‖h k g * lam (parabolicInd F n β σ g φ)‖) μ := fun k =>
    ((hcont _ fun g k' hk' => by rw [hhr k k' hk', hfr g k' hk']).norm).integrable_of_hasCompactSupport
      (hhcs k).mul_right.norm
  have hhint : ∀ k, ∀ x ∈ R, Integrable (fun g => ‖h k g‖ * ‖ℓx x ((φ : GL (Fin n) F → W) (x * g))‖) μ :=
    fun k x _ => ((hcont _ fun g k' hk' => by rw [hhr k k' hk']).norm.mul
      (hcont _ fun g k' hk' => by rw [hφr x g k' hk']).norm).integrable_of_hasCompactSupport
      (hhcs k).norm.mul_right
  have hshellZ : ∀ s k g, {g : GL (Fin n) F | ordDet g = k}.indicator (fun g =>
      Φ (g : Matrix (Fin n) (Fin n) F) * matrixCoeff π v ℓ g * detPow g s) g =
      qs F s ^ k * (h k g * lam (parabolicInd F n β σ g φ)) := by
    intro s k g
    simp only [h, Set.indicator_apply, Set.mem_ofPred_eq]
    split_ifs with hk
    · rw [hf g, detPow_eq_qs_zpow, hk]; ring
    · simp
  have hshellT : ∀ x s k g, {g : GL (Fin n) F | ordDet g = k}.indicator (T x s) g =
      qs F s ^ k * (h k g * ℓx x ((φ : GL (Fin n) F → W) (x * g))) := by
    intro x s k g
    simp only [h, T, Set.indicator_apply, Set.mem_ofPred_eq]
    split_ifs with hk
    · rw [detPow_eq_qs_zpow, hk]; ring
    · simp

  have hZint : ∀ s : ℂ, s₀ < s.re → Integrable (fun g : GL (Fin n) F =>
      Φ (g : Matrix (Fin n) (Fin n) F) * matrixCoeff π v ℓ g * detPow g s) μ := by
    intro s hs
    refine ⟨(hcont _ fun g k hk => by
      rw [hΦr g k hk, hdetr s g k hk, hf, hf, hfr g k hk]).aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral]
    simp_rw [← ofReal_norm]
    rw [lintegral_eq_tsum_shell]
    have hterm : ∀ k : ℤ, ∫⁻ g in {g : GL (Fin n) F | ordDet g = k}, ENNReal.ofReal
        ‖Φ (g : Matrix (Fin n) (Fin n) F) * matrixCoeff π v ℓ g * detPow g s‖ ∂μ ≤
        ∑ x ∈ R, ∫⁻ g in {g : GL (Fin n) F | ordDet g = k}, ENNReal.ofReal ‖T x s g‖ ∂μ := by
      intro k
      have e1 : ∀ g, {g : GL (Fin n) F | ordDet g = k}.indicator (fun g => ENNReal.ofReal
          ‖Φ (g : Matrix (Fin n) (Fin n) F) * matrixCoeff π v ℓ g * detPow g s‖) g =
          ENNReal.ofReal (‖qs F s‖ ^ k) * ENNReal.ofReal ‖h k g * lam (parabolicInd F n β σ g φ)‖ := by
        intro g
        rw [← ENNReal.ofReal_mul (zpow_nonneg (norm_nonneg _) _), ← norm_zpow, ← norm_mul,
          ← hshellZ s k g]
        by_cases hg : g ∈ {g : GL (Fin n) F | ordDet g = k}
        · simp [Set.indicator_of_mem hg]
        · simp [Set.indicator_of_notMem hg]
      have e2 : ∀ x g, {g : GL (Fin n) F | ordDet g = k}.indicator (fun g => ENNReal.ofReal
          ‖T x s g‖) g = ENNReal.ofReal (‖qs F s‖ ^ k) *
            ENNReal.ofReal (‖h k g‖ * ‖ℓx x ((φ : GL (Fin n) F → W) (x * g))‖) := by
        intro x g
        rw [← ENNReal.ofReal_mul (zpow_nonneg (norm_nonneg _) _), ← norm_zpow, ← norm_mul,
          ← norm_mul, ← hshellT x s k g]
        by_cases hg : g ∈ {g : GL (Fin n) F | ordDet g = k}
        · simp [Set.indicator_of_mem hg]
        · simp [Set.indicator_of_notMem hg]
      rw [← lintegral_indicator (measurableSet_shell k), lintegral_congr e1,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      simp_rw [← lintegral_indicator (measurableSet_shell k), e2]
      simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← Finset.mul_sum]
      exact mul_le_mul' le_rfl (lintegral_norm_mul_coeff_le μ hKc hKo hlamK hφK hdec (hhcs k)
        (hhl k) (hhr k) (hhf k) (hhint k))
    calc ∑' k : ℤ, ∫⁻ g in {g : GL (Fin n) F | ordDet g = k}, ENNReal.ofReal
          ‖Φ (g : Matrix (Fin n) (Fin n) F) * matrixCoeff π v ℓ g * detPow g s‖ ∂μ
        ≤ ∑' k : ℤ, ∑ x ∈ R, ∫⁻ g in {g : GL (Fin n) F | ordDet g = k},
            ENNReal.ofReal ‖T x s g‖ ∂μ := ENNReal.tsum_le_tsum hterm
      _ = ∑ x ∈ R, ∫⁻ g, ENNReal.ofReal ‖T x s g‖ ∂μ := by
          rw [Summable.tsum_finsetSum fun _ _ => ENNReal.summable]
          exact Finset.sum_congr rfl fun x _ => (lintegral_eq_tsum_shell μ _).symm
      _ < ∞ := by
          refine ENNReal.sum_lt_top.2 fun x hx => ?_
          have := (hTint x hx s hs).2
          simpa [HasFiniteIntegral, ofReal_norm] using this
  refine ⟨hZint, ?_⟩

  refine ⟨∑ x ∈ R, N x, ∑ x ∈ R, P x * X ^ (∑ y ∈ R, N y - N x), fun s hs => ?_⟩
  have hZsum := hasSum_integral_shell μ (hZint s hs)
  have hTsum : ∀ x ∈ R, HasSum (fun k : ℤ => ∫ g in {g : GL (Fin n) F | ordDet g = k}, T x s g ∂μ)
      (∫ g, T x s g ∂μ) := fun x hx => hasSum_integral_shell μ (hTint x hx s hs)
  have hsum := hasSum_sum hTsum
  have hshell_eq : ∀ k : ℤ, ∫ g in {g : GL (Fin n) F | ordDet g = k},
      Φ (g : Matrix (Fin n) (Fin n) F) * matrixCoeff π v ℓ g * detPow g s ∂μ =
      ∑ x ∈ R, ∫ g in {g : GL (Fin n) F | ordDet g = k}, T x s g ∂μ := by
    intro k
    rw [← integral_indicator (measurableSet_shell k)]
    simp_rw [hshellZ s k]
    rw [integral_const_mul, integral_mul_coeff_eq μ hKc hKo hφK hdec (hhcs k) (hhl k) (hhr k),
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← integral_indicator (measurableSet_shell k)]
    simp_rw [hshellT x s k]
    rw [integral_const_mul]
  have hZ : ∫ g, Φ (g : Matrix (Fin n) (Fin n) F) * matrixCoeff π v ℓ g * detPow g s ∂μ =
      ∑ x ∈ R, ∫ g, T x s g ∂μ := by
    refine hZsum.unique ?_
    convert hsum using 1
    funext k
    exact hshell_eq k
  have hterm : ∀ x ∈ R, D.eval (qs F s) * ∫ g, T x s g ∂μ = (P x).eval (qs F s) / qs F s ^ N x := by
    intro x hx
    rw [hTeq x hx s]
    exact hJeq x s hs
  rw [hZ, Finset.mul_sum, Finset.sum_congr rfl hterm, eval_finsetSum, Finset.sum_div]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hle : N x ≤ ∑ y ∈ R, N y := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hx
  rw [eval_mul, eval_pow, eval_X, pow_sub₀ _ (qs_ne_zero s) hle]
  field_simp
  exact (mul_div_mul_right _ _ (pow_ne_zero _ (qs_ne_zero s))).symm

end Core

end GodementJacquet

end GroundTheory.Automorphic
