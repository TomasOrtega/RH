import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.FourierIsolation

def meanExp (N : ℕ) (μ : ℝ) : ℂ :=
  (N : ℂ)⁻¹ * ∫ s in (0:ℝ)..N, Complex.exp (-(2 * Real.pi * Complex.I) * ((s * μ : ℝ) : ℂ))

/- English proof (translation)
Rewrite using `[Complex.norm_exp]`. Simplify using the standard rewrite rules.
-/
theorem norm_exp_phase (x : ℝ) : ‖Complex.exp (-(2 * Real.pi * Complex.I) * (x : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  simp

/- English proof (translation)
Unfold `meanExp`. Break down `Nat.eq_zero_or_pos N with rfl | hN` into its components or cases. Simplify using the standard rewrite rules. Rewrite using `[norm_mul, norm_inv, Complex.norm_natCast]`. Establish `h` using `intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := (N:ℝ)) (C := 1) (f := fun s : ℝ => Complex.exp (-(2 * Real.pi * Complex.I) * ((s * μ : ℝ) : ℂ))) (fun s _ => le_of_eq (norm_exp_phase _))`.

Establish `hN' : (0:ℝ) < N` using `by exact_mod_cast hN`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_meanExp_le (N : ℕ) (μ : ℝ) : ‖meanExp N μ‖ ≤ 1 := by
  unfold meanExp
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := (N:ℝ)) (C := 1)
    (f := fun s : ℝ => Complex.exp (-(2 * Real.pi * Complex.I) * ((s * μ : ℝ) : ℂ)))
    (fun s _ => le_of_eq (norm_exp_phase _))
  have hN' : (0:ℝ) < N := by exact_mod_cast hN
  calc (N:ℝ)⁻¹ * ‖∫ s in (0:ℝ)..N, Complex.exp (-(2 * Real.pi * Complex.I) * ((s * μ : ℝ) : ℂ))‖
      ≤ (N:ℝ)⁻¹ * (1 * |(N:ℝ) - 0|) := by gcongr
    _ = 1 := by rw [sub_zero, abs_of_pos hN', one_mul, inv_mul_cancel₀ hN'.ne']

/- English proof (translation)
Unfold `meanExp`. Establish `hN' : (N : ℂ) ≠ 0` using `by exact_mod_cast hN.ne'`. Simplify using `[hN']`.
-/
theorem meanExp_zero {N : ℕ} (hN : 0 < N) : meanExp N 0 = 1 := by
  unfold meanExp
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  simp [hN']

/- English proof (translation)
Use `set c : ℂ := -(2 * Real.pi * Complex.I) * μ with hcdef`. Establish `hc : c ≠ 0`. Simplify using `[c, hμ, Real.pi_ne_zero, Complex.I_ne_zero]`. Establish `hf : ∀ N : ℕ, meanExp N μ = (N : ℂ)⁻¹ * ((Complex.exp (c * N) - 1) / c)`. Introduce `N`.

Unfold `meanExp`. Use `congr 1`. Establish `: (fun s : ℝ => Complex.exp (-(2 * Real.pi * Complex.I) * ((s * μ : ℝ) : ℂ))) = fun s : ℝ => Complex.exp (c * s)`. Use function extensionality and compare the values at `s`. Simplify using `only [c]`.

Use `push_cast`. Put the polynomial expressions in normal form. Rewrite using `[this, integral_exp_mul_complex hc]`. Simplify using the standard rewrite rules. Establish `hexp : ∀ N : ℕ, ‖Complex.exp (c * N)‖ = 1`.

Introduce `N`. Establish `: c * N = -(2 * Real.pi * Complex.I) * ((μ * N : ℝ) : ℂ)`. Simplify using `only [c]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this, norm_exp_phase]`. Establish `hb : ∀ N : ℕ, ‖meanExp N μ‖ ≤ (N:ℝ)⁻¹ * (2 / ‖c‖)`. Introduce `N`. Rewrite using `[hf, norm_mul, norm_inv, Complex.norm_natCast, norm_div]`. Use `gcongr`.

Combine the equalities or inequalities in the displayed calculation. Establish `ht : Tendsto (fun N : ℕ => (N:ℝ)⁻¹ * (2 / ‖c‖)) atTop (𝓝 0)`. Simplify using `using (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const (2 / ‖c‖)`. Conclude with `squeeze_zero_norm hb ht`.
-/
theorem tendsto_meanExp {μ : ℝ} (hμ : μ ≠ 0) : Tendsto (fun N : ℕ => meanExp N μ) atTop (𝓝 0) := by
  set c : ℂ := -(2 * Real.pi * Complex.I) * μ with hcdef
  have hc : c ≠ 0 := by
    simp [c, hμ, Real.pi_ne_zero, Complex.I_ne_zero]
  have hf : ∀ N : ℕ, meanExp N μ = (N : ℂ)⁻¹ * ((Complex.exp (c * N) - 1) / c) := by
    intro N
    unfold meanExp
    congr 1
    have : (fun s : ℝ => Complex.exp (-(2 * Real.pi * Complex.I) * ((s * μ : ℝ) : ℂ))) =
        fun s : ℝ => Complex.exp (c * s) := by
      funext s
      simp only [c]
      push_cast
      ring_nf
    rw [this, integral_exp_mul_complex hc]
    simp
  have hexp : ∀ N : ℕ, ‖Complex.exp (c * N)‖ = 1 := by
    intro N
    have : c * N = -(2 * Real.pi * Complex.I) * ((μ * N : ℝ) : ℂ) := by
      simp only [c]; push_cast; ring
    rw [this, norm_exp_phase]
  have hb : ∀ N : ℕ, ‖meanExp N μ‖ ≤ (N:ℝ)⁻¹ * (2 / ‖c‖) := by
    intro N
    rw [hf, norm_mul, norm_inv, Complex.norm_natCast, norm_div]
    gcongr
    calc ‖Complex.exp (c * N) - 1‖ ≤ ‖Complex.exp (c * N)‖ + ‖(1:ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [hexp, norm_one]; norm_num
  have ht : Tendsto (fun N : ℕ => (N:ℝ)⁻¹ * (2 / ‖c‖)) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const (2 / ‖c‖)
  exact squeeze_zero_norm hb ht

/- English proof (translation)
Establish `hN : (0:ℝ) ≤ N` using `Nat.cast_nonneg N`. Simplify using `only [meanExp, intervalIntegral.integral_of_le hN]`. Establish `hna : Summable (fun i => ‖a i‖)` using `summable_norm_iff.mpr ha`. Establish `hint : ∀ i, Integrable (fun s : ℝ => a i * Complex.exp (-(2 * Real.pi * Complex.I) * ((s * μ i : ℝ) : ℂ))) (volume.restrict (Set.Ioc (0:ℝ) N))`. Introduce `i`.

Conclude with `(Continuous.integrableOn_Icc (by fun_prop)).mono_set Set.Ioc_subset_Icc_self`. Establish `hsum : Summable (fun i => ∫ s in Set.Ioc (0:ℝ) N, ‖a i * Complex.exp (-(2 * Real.pi * Complex.I) * ((s * μ i : ℝ) : ℂ))‖)`. Establish `: (fun i => ∫ s in Set.Ioc (0:ℝ) N, ‖a i * Complex.exp (-(2 * Real.pi * Complex.I) * ((s * μ i : ℝ) : ℂ))‖) = fun i => ‖a i‖ * N`. Use function extensionality and compare the values at `i`. Simplify using `only [norm_mul, norm_exp_phase, mul_one]`.

Rewrite using `[integral_const]`. Simplify using `[mul_comm]`. Rewrite using `[this]`. Conclude with `hna.mul_right _`. Rewrite using `[← integral_tsum_of_summable_integral_norm hint hsum, ← tsum_mul_left]`.

Use `congr 1`. Use function extensionality and compare the values at `i`. Rewrite using `[integral_const_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem tsum_meanExp {ι : Type*} [Countable ι] (a : ι → ℂ) (ha : Summable a) (μ : ι → ℝ) (N : ℕ) :
    (N : ℂ)⁻¹ * ∫ s in (0:ℝ)..N, ∑' i, a i * Complex.exp (-(2 * Real.pi * Complex.I) * ((s * μ i : ℝ) : ℂ))
      = ∑' i, a i * meanExp N (μ i) := by
  have hN : (0:ℝ) ≤ N := Nat.cast_nonneg N
  simp only [meanExp, intervalIntegral.integral_of_le hN]
  have hna : Summable (fun i => ‖a i‖) := summable_norm_iff.mpr ha
  have hint : ∀ i, Integrable (fun s : ℝ => a i * Complex.exp (-(2 * Real.pi * Complex.I) * ((s * μ i : ℝ) : ℂ)))
      (volume.restrict (Set.Ioc (0:ℝ) N)) := by
    intro i
    exact (Continuous.integrableOn_Icc (by fun_prop)).mono_set Set.Ioc_subset_Icc_self
  have hsum : Summable (fun i => ∫ s in Set.Ioc (0:ℝ) N,
      ‖a i * Complex.exp (-(2 * Real.pi * Complex.I) * ((s * μ i : ℝ) : ℂ))‖) := by
    have : (fun i => ∫ s in Set.Ioc (0:ℝ) N,
        ‖a i * Complex.exp (-(2 * Real.pi * Complex.I) * ((s * μ i : ℝ) : ℂ))‖) = fun i => ‖a i‖ * N := by
      funext i
      simp only [norm_mul, norm_exp_phase, mul_one]
      rw [integral_const]
      simp [mul_comm]
    rw [this]
    exact hna.mul_right _
  rw [← integral_tsum_of_summable_integral_norm hint hsum, ← tsum_mul_left]
  congr 1
  funext i
  rw [integral_const_mul]
  ring

/- English proof (translation)
Establish `h0 : ∀ N : ℕ, ∑' i, a i * meanExp N (μ i) = 0`. Introduce `N`. Rewrite using `[← tsum_meanExp a ha μ N]`. Simplify using `only [h, intervalIntegral.integral_zero, mul_zero]`. Establish `hT : Tendsto (fun N : ℕ => ∑' i, a i * meanExp N (μ i)) atTop (𝓝 (∑' i, Set.indicator {i | μ i = 0} a i))`.

Use `tendsto_tsum_of_dominated_convergence (bound := fun i => ‖a i‖) (summable_norm_iff.mpr ha) (fun i => ?_) ?_` and prove the remaining obligations. Distinguish the cases in `hi : μ i = 0`. Establish `e : Set.indicator {i | μ i = 0} a i = a i` using `by simp [Set.indicator, hi]`. Rewrite using `[e]`. Use `tendsto_const_nhds.congr' ?_` and prove the remaining obligations.

Use `filter_upwards [eventually_gt_atTop 0] with N hN`. Rewrite using `[hi, meanExp_zero hN, mul_one]`. Establish `e : Set.indicator {i | μ i = 0} a i = 0` using `by simp [Set.indicator, hi]`. Rewrite using `[e]`. Simplify using `using (tendsto_meanExp hi).const_mul (a i)`.

Conclude with `Eventually.of_forall fun N i => by`. Rewrite using `[norm_mul]`. Conclude with `mul_le_of_le_one_right (norm_nonneg _) (norm_meanExp_le N (μ i))`. Simplify using `only [h0] at hT`. Conclude with `tendsto_nhds_unique hT tendsto_const_nhds`.
-/
theorem tsum_indicator_eq_zero_of_mean {ι : Type*} [Countable ι] (a : ι → ℂ) (ha : Summable a) (μ : ι → ℝ)
    (h : ∀ s : ℝ, ∑' i, a i * Complex.exp (-(2 * Real.pi * Complex.I) * ((s * μ i : ℝ) : ℂ)) = 0) :
    ∑' i, Set.indicator {i | μ i = 0} a i = 0 := by
  have h0 : ∀ N : ℕ, ∑' i, a i * meanExp N (μ i) = 0 := by
    intro N
    rw [← tsum_meanExp a ha μ N]
    simp only [h, intervalIntegral.integral_zero, mul_zero]
  have hT : Tendsto (fun N : ℕ => ∑' i, a i * meanExp N (μ i)) atTop
      (𝓝 (∑' i, Set.indicator {i | μ i = 0} a i)) := by
    refine tendsto_tsum_of_dominated_convergence (bound := fun i => ‖a i‖) (summable_norm_iff.mpr ha)
      (fun i => ?_) ?_
    · by_cases hi : μ i = 0
      · have e : Set.indicator {i | μ i = 0} a i = a i := by simp [Set.indicator, hi]
        rw [e]
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_gt_atTop 0] with N hN
        rw [hi, meanExp_zero hN, mul_one]
      · have e : Set.indicator {i | μ i = 0} a i = 0 := by simp [Set.indicator, hi]
        rw [e]
        simpa using (tendsto_meanExp hi).const_mul (a i)
    · exact Eventually.of_forall fun N i => by
        rw [norm_mul]
        exact mul_le_of_le_one_right (norm_nonneg _) (norm_meanExp_le N (μ i))
  simp only [h0] at hT
  exact tendsto_nhds_unique hT tendsto_const_nhds

/- English proof (translation)
Introduce `K`. Proceed by induction on `K with`. Consider the case `zero`. Introduce `a ha μ h`. Establish `hμ : ∀ i, μ i = 0` using `fun i => Subsingleton.elim _ _`.

Establish `e : Set.indicator {i | μ i = 0} a = a`. Use function extensionality and compare the values at `i`. Simplify using `[Set.indicator, hμ]`. Rewrite using `[e]`. Simplify using `using h 0`.

Consider the case `succ K ih`. Introduce `a ha μ h`. Use `set b : ι → ℂ := Set.indicator {i | μ i 0 = 0} a with hbdef`. Establish `hb : Summable b` using `ha.indicator _`. Establish `h1 : ∀ s' : Fin K → ℝ, ∑' i, b i * Complex.exp (-(2 * Real.pi * Complex.I) * ((∑ k, s' k * μ i k.succ : ℝ) : ℂ)) = 0`.

Introduce `s'`. Use `set a' : ι → ℂ := fun i => a i * Complex.exp (-(2 * Real.pi * Complex.I) * ((∑ k, s' k * μ i k.succ : ℝ) : ℂ)) with ha'def`. Establish `ha' : Summable a'`. Use `Summable.of_norm ((summable_norm_iff.mpr ha).congr fun i => ?_)` and prove the remaining obligations. Simplify using `only [a', norm_mul, norm_exp_phase, mul_one]`.

Establish `hh` using `tsum_indicator_eq_zero_of_mean a' ha' (fun i => μ i 0) (fun t => by`. Rewrite using `[← h (Fin.cons t s')]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Simplify using `only [a', Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]`.

Rewrite using `[mul_assoc, ← Complex.exp_add]`. Use `congr 2`. Use `push_cast`. Use the proof step `ring)`. Rewrite using `[← hh]`.

Use `congr 1`. Use function extensionality and compare the values at `i`. Apply the tactic sequence `by_cases h0 : μ i 0 = 0 <;> simp [b, a', Set.indicator, h0]`. Establish `h2` using `ih b hb (fun i k => μ i k.succ) h1`. Rewrite using `[← h2]`.

Use `congr 1`. Use function extensionality and compare the values at `i`. Establish `key : μ i = 0 ↔ (μ i 0 = 0 ∧ (fun k : Fin K => μ i k.succ) = 0)`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `hz`.

Conclude with `⟨by rw [hz]; rfl, by funext k; rw [hz]; rfl⟩`. Introduce and unpack `⟨h0, hs⟩`. Use function extensionality and compare the values at `k`. Use `Fin.cases h0 (fun k => congrFun hs k) k` and prove the remaining obligations. Apply the tactic sequence `by_cases h0 : μ i 0 = 0 <;> by_cases hs : (fun k : Fin K => μ i k.succ) = 0 <;>`.

Simplify using `[b, Set.indicator, h0, hs, key]`.
-/
theorem tsum_indicator_eq_zero_of_mean_fin {ι : Type*} [Countable ι] : ∀ (K : ℕ) (a : ι → ℂ), Summable a →
    ∀ (μ : ι → Fin K → ℝ),
    (∀ s : Fin K → ℝ, ∑' i, a i * Complex.exp (-(2 * Real.pi * Complex.I) * ((∑ k, s k * μ i k : ℝ) : ℂ)) = 0) →
    ∑' i, Set.indicator {i | μ i = 0} a i = 0 := by
  intro K
  induction K with
  | zero =>
    intro a ha μ h
    have hμ : ∀ i, μ i = 0 := fun i => Subsingleton.elim _ _
    have e : Set.indicator {i | μ i = 0} a = a := by
      funext i; simp [Set.indicator, hμ]
    rw [e]
    simpa using h 0
  | succ K ih =>
    intro a ha μ h
    set b : ι → ℂ := Set.indicator {i | μ i 0 = 0} a with hbdef
    have hb : Summable b := ha.indicator _
    have h1 : ∀ s' : Fin K → ℝ, ∑' i, b i * Complex.exp (-(2 * Real.pi * Complex.I) *
        ((∑ k, s' k * μ i k.succ : ℝ) : ℂ)) = 0 := by
      intro s'
      set a' : ι → ℂ := fun i => a i * Complex.exp (-(2 * Real.pi * Complex.I) *
        ((∑ k, s' k * μ i k.succ : ℝ) : ℂ)) with ha'def
      have ha' : Summable a' := by
        refine Summable.of_norm ((summable_norm_iff.mpr ha).congr fun i => ?_)
        simp only [a', norm_mul, norm_exp_phase, mul_one]
      have hh := tsum_indicator_eq_zero_of_mean a' ha' (fun i => μ i 0) (fun t => by
        rw [← h (Fin.cons t s')]
        congr 1
        funext i
        simp only [a', Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
        rw [mul_assoc, ← Complex.exp_add]
        congr 2
        push_cast
        ring)
      rw [← hh]
      congr 1
      funext i
      by_cases h0 : μ i 0 = 0 <;> simp [b, a', Set.indicator, h0]
    have h2 := ih b hb (fun i k => μ i k.succ) h1
    rw [← h2]
    congr 1
    funext i
    have key : μ i = 0 ↔ (μ i 0 = 0 ∧ (fun k : Fin K => μ i k.succ) = 0) := by
      constructor
      · rintro hz
        exact ⟨by rw [hz]; rfl, by funext k; rw [hz]; rfl⟩
      · rintro ⟨h0, hs⟩
        funext k
        refine Fin.cases h0 (fun k => congrFun hs k) k
    by_cases h0 : μ i 0 = 0 <;> by_cases hs : (fun k : Fin K => μ i k.succ) = 0 <;>
      simp [b, Set.indicator, h0, hs, key]

end GlobalTheory.FourierIsolation

namespace GlobalTheory.FourierIsolation

section Adelic

variable {F : Type} [Field F] [NumberField F]

def evH : AF F →+* mixedEmbedding.mixedSpace F :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp (RingHom.fst _ _)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem evH_apply (a : AF F) : evH a = evI F a := rfl

/- English proof (translation)
Rewrite using `[← evH_apply, map_mul, evH_apply, evH_apply, Algebra.smul_def]`. Use `congr 1`. Simplify using `[evI, realAd]`.
-/
theorem evI_realAd_mul' (t : ℝ) (c : AF F) : evI F (realAd F t * c) = t • evI F c := by
  rw [← evH_apply, map_mul, evH_apply, evH_apply, Algebra.smul_def]
  congr 1
  simp [evI, realAd]

/- English proof (translation)
Introduce `b hb`. Establish `h1 : b.1 = 0`. Establish `: InfiniteAdeleRing.ringEquiv_mixedSpace F b.1 = 0` using `hb`. Conclude with `(map_eq_zero_iff _ (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective).mp this`. Rewrite using `[smul_eq_mul, ← mul_assoc]`.

Establish `: b * realAd F t = 0` using `Prod.ext (by show b.1 * _ = 0; rw [h1, zero_mul]) (by show _ * (realAd F t).2 = 0; simp [realAd])`. Rewrite using `[this, zero_mul]`.
-/
theorem at_realAd_mul' (t : ℝ) (c : AF F) : At (evI F) (realAd F t * c) := by
  intro b hb
  have h1 : b.1 = 0 := by
    have : InfiniteAdeleRing.ringEquiv_mixedSpace F b.1 = 0 := hb
    exact (map_eq_zero_iff _ (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective).mp this
  rw [smul_eq_mul, ← mul_assoc]
  have : b * realAd F t = 0 :=
    Prod.ext (by show b.1 * _ = 0; rw [h1, zero_mul]) (by show _ * (realAd F t).2 = 0; simp [realAd])
  rw [this, zero_mul]

/- English proof (translation)
Rewrite using `[InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]`. Both sides reduce to the same expression.
-/
theorem evI_algebraMap' (x : F) : evI F (algebraMap F (AF F) x) = mixedEmbedding F x := by
  rw [InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]; rfl

omit [NumberField F] in
/- English proof (translation)
Establish `h1 : a ⊗ₜ[F] e = a • ((1 : R) ⊗ₜ[F] e)`. Rewrite using `[TensorProduct.smul_tmul', smul_eq_mul, mul_one]`. Rewrite using `[h1, map_smul, Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange, smul_eq_mul]`.
-/
theorem trace_baseChange_tmul' {E : Type} [Field E] [Algebra F E] [FiniteDimensional F E] (R : Type) [CommRing R]
    [Algebra F R] (a : R) (e : E) :
    Algebra.trace R (R ⊗[F] E) (a ⊗ₜ[F] e) = a * algebraMap F R (Algebra.trace F E e) := by
  have h1 : a ⊗ₜ[F] e = a • ((1 : R) ⊗ₜ[F] e) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [h1, map_smul, Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul,
    LinearMap.trace_baseChange, smul_eq_mul]

end Adelic

/- English proof (translation)
Introduce `F E _ _ _ _ _ ψ hψ n a ha h`. Use `haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E`. Use `haveI : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable`. Use `set b := Module.finBasis ℚ (Fin n → E) with hbdef`. Use `set K := Module.finrank ℚ (Fin n → E)`.

Set `q : (Fin n → E) → (Fin n → E) → ℚ` to `fun ξ w => Algebra.trace ℚ F (Algebra.trace F E (∑ i, ξ i * w i))`. Set `μ : (Fin n → E) → Fin K → ℝ` to `fun ξ k => (q ξ (b k) : ℝ)`. Establish `key : ∀ (ξ : Fin n → E) (s : Fin K → ℝ), ψ (Algebra.trace (AF F) (AE F E) (∑ i, incV F ξ i * ∑ k, realAd F (s k) ⊗ₜ[F] b k i)) = Complex.exp (-(2 * Real.pi * Complex.I) * ((∑ k, s k * μ ξ k : ℝ) : ℂ))`. Introduce `ξ s`. Establish `e1 : (∑ i, incV F ξ i * ∑ k, realAd F (s k) ⊗ₜ[F] b k i) = ∑ k, realAd F (s k) ⊗ₜ[F] (∑ i, ξ i * b k i)`.

Repeatedly rewrite using `[TensorProduct.tmul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `((1 : AF F) ⊗ₜ[F] ξ i) * _ = _`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, one_mul]`. Rewrite using `[e1, map_sum]`. Repeatedly rewrite using `[trace_baseChange_tmul']`. Rewrite using `[hψ.2.2 _ (fun u hu => by`.

Rewrite using `[smul_eq_mul, Finset.mul_sum]`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Simplify `at_realAd_mul' (s k) (algebraMap F (AF F) (Algebra.trace F E (∑ i, ξ i * b k i))) u hu)]` using `[smul_eq_mul]`. Use `congr 3`. Rewrite using `[← evH_apply, map_sum, map_sum]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[evH_apply, evI_realAd_mul', map_smul, evI_algebraMap', GlobalTheory.PsiNontriv.trace_mixedEmbedding, smul_eq_mul]`. Establish `hμ0 : μ 0 = 0`. Use function extensionality and compare the values at `k`. Simplify using `[μ, q]`.

Establish `hinj : ∀ ξ, μ ξ = 0 → ξ = 0`. Introduce `ξ hξ`. Assume the negation of the conclusion as `hne`. Choose the witnesses or unpack the hypotheses as in `⟨j, hj⟩ : ∃ j, ξ j ≠ 0 := by`. Assume the negation of the conclusion as `hc`.

Use `push_neg at hc`. Conclude with `hne (funext hc)`. Set `L : (Fin n → E) →ₗ[ℚ] ℚ` to `{ toFun := fun w => q ξ w map_add' := fun w w' => by`. Simplify using `only [q, Pi.add_apply, mul_add, Finset.sum_add_distrib, map_add]`. Use the proof step `map_smul' := fun c w => by`.

Simplify using `only [q, Pi.smul_apply, mul_smul_comm, ← Finset.smul_sum, map_rat_smul, RingHom.id_apply] }`. Establish `hL : L = 0` using `b.ext fun k => by`. Use `congrFun hξ k` as an intermediate fact. Simplify using `only [μ, Pi.zero_apply, Rat.cast_eq_zero] at this`. Conclude with `this`.

Establish `h1` using `LinearMap.congr_fun hL (Pi.single j (ξ j)⁻¹)`. Establish `hs : (∑ i, ξ i * Pi.single (M` using `fun _ => E) j (ξ j)⁻¹ i) = 1 := by`. Rewrite using `[Finset.sum_eq_single j (fun i _ hi => by rw [Pi.single_eq_of_ne hi, mul_zero]) (by simp)]`. Rewrite using `[Pi.single_eq_same, mul_inv_cancel₀ hj]`. Express the relevant statement in the definitionally equal form `q ξ _ = 0 at h1`.

Simplify using `only [q, hs] at h1`. Rewrite `h1` using `[← map_one (algebraMap F E), Algebra.trace_algebraMap, map_nsmul, ← map_one (algebraMap ℚ F), Algebra.trace_algebraMap]`. Establish `hp1 : 0 < Module.finrank F E` using `Module.finrank_pos`. Establish `hp2 : 0 < Module.finrank ℚ F` using `Module.finrank_pos`. Simplify using `only [nsmul_eq_mul, mul_one] at h1`.

Establish `: ((Module.finrank F E : ℚ) * Module.finrank ℚ F) ≠ 0` using `by positivity`. Conclude with `this h1`. Establish `hB` using `tsum_indicator_eq_zero_of_mean_fin K a ha μ (fun s => by`. Rewrite using `[← h (fun i => ∑ k, realAd F (s k) ⊗ₜ[F] b k i)]`. Use `congr 1`.

Use function extensionality and compare the values at `ξ`. Rewrite using `[key, mul_comm])`. Rewrite using `[tsum_eq_single 0 (fun ξ hξ => by`. Establish `: ¬ μ ξ = 0` using `fun h' => hξ (hinj ξ h')`. Simplify using `[Set.indicator, this])] at hB`.

Simplify `hB` using `[Set.indicator, hμ0]`.
-/
theorem coeff_zero_eq_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (n : ℕ) (a : (Fin n → E) → ℂ), Summable a →
    (∀ z : Fin n → AE F E, ∑' ξ : Fin n → E, ψ (Algebra.trace (AF F) (AE F E) (∑ i, incV F ξ i * z i)) * a ξ = 0) →
    a 0 = 0 := by
  intro F E _ _ _ _ _ ψ hψ n a ha h
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  set b := Module.finBasis ℚ (Fin n → E) with hbdef
  set K := Module.finrank ℚ (Fin n → E)
  let q : (Fin n → E) → (Fin n → E) → ℚ := fun ξ w => Algebra.trace ℚ F (Algebra.trace F E (∑ i, ξ i * w i))
  let μ : (Fin n → E) → Fin K → ℝ := fun ξ k => (q ξ (b k) : ℝ)
  have key : ∀ (ξ : Fin n → E) (s : Fin K → ℝ),
      ψ (Algebra.trace (AF F) (AE F E) (∑ i, incV F ξ i * ∑ k, realAd F (s k) ⊗ₜ[F] b k i)) =
        Complex.exp (-(2 * Real.pi * Complex.I) * ((∑ k, s k * μ ξ k : ℝ) : ℂ)) := by
    intro ξ s
    have e1 : (∑ i, incV F ξ i * ∑ k, realAd F (s k) ⊗ₜ[F] b k i) =
        ∑ k, realAd F (s k) ⊗ₜ[F] (∑ i, ξ i * b k i) := by
      simp_rw [TensorProduct.tmul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      change ((1 : AF F) ⊗ₜ[F] ξ i) * _ = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rw [e1, map_sum]
    simp_rw [trace_baseChange_tmul']
    rw [hψ.2.2 _ (fun u hu => by
      rw [smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_eq_zero fun k _ => ?_
      simpa [smul_eq_mul] using at_realAd_mul' (s k) (algebraMap F (AF F) (Algebra.trace F E (∑ i, ξ i * b k i))) u hu)]
    congr 3
    rw [← evH_apply, map_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [evH_apply, evI_realAd_mul', map_smul, evI_algebraMap', GlobalTheory.PsiNontriv.trace_mixedEmbedding, smul_eq_mul]
  have hμ0 : μ 0 = 0 := by
    funext k; simp [μ, q]
  have hinj : ∀ ξ, μ ξ = 0 → ξ = 0 := by
    intro ξ hξ
    by_contra hne
    obtain ⟨j, hj⟩ : ∃ j, ξ j ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hne (funext hc)
    let L : (Fin n → E) →ₗ[ℚ] ℚ :=
      { toFun := fun w => q ξ w
        map_add' := fun w w' => by
          simp only [q, Pi.add_apply, mul_add, Finset.sum_add_distrib, map_add]
        map_smul' := fun c w => by
          simp only [q, Pi.smul_apply, mul_smul_comm, ← Finset.smul_sum, map_rat_smul, RingHom.id_apply] }
    have hL : L = 0 := b.ext fun k => by
      have := congrFun hξ k
      simp only [μ, Pi.zero_apply, Rat.cast_eq_zero] at this
      exact this
    have h1 := LinearMap.congr_fun hL (Pi.single j (ξ j)⁻¹)
    have hs : (∑ i, ξ i * Pi.single (M := fun _ => E) j (ξ j)⁻¹ i) = 1 := by
      rw [Finset.sum_eq_single j (fun i _ hi => by rw [Pi.single_eq_of_ne hi, mul_zero]) (by simp)]
      rw [Pi.single_eq_same, mul_inv_cancel₀ hj]
    change q ξ _ = 0 at h1
    simp only [q, hs] at h1
    rw [← map_one (algebraMap F E), Algebra.trace_algebraMap, map_nsmul, ← map_one (algebraMap ℚ F),
      Algebra.trace_algebraMap] at h1
    have hp1 : 0 < Module.finrank F E := Module.finrank_pos
    have hp2 : 0 < Module.finrank ℚ F := Module.finrank_pos
    simp only [nsmul_eq_mul, mul_one] at h1
    have : ((Module.finrank F E : ℚ) * Module.finrank ℚ F) ≠ 0 := by positivity
    exact this h1
  have hB := tsum_indicator_eq_zero_of_mean_fin K a ha μ (fun s => by
    rw [← h (fun i => ∑ k, realAd F (s k) ⊗ₜ[F] b k i)]
    congr 1
    funext ξ
    rw [key, mul_comm])
  rw [tsum_eq_single 0 (fun ξ hξ => by
    have : ¬ μ ξ = 0 := fun h' => hξ (hinj ξ h')
    simp [Set.indicator, this])] at hB
  simpa [Set.indicator, hμ0] using hB

end GlobalTheory.FourierIsolation
