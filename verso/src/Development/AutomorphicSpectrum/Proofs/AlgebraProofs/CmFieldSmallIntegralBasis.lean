import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GroupDict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
import GroundTheory.GlobalFields.TateThesis.TraceDualLattice
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FinrankMulDiscrRpowLeSumSqOfMemTraceDual
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsIndependentLeOfDualMin
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace

namespace GlobalTheory.CompanionTheory.Ar.Cusp

section ShortIntegers

open NumberField.InfinitePlace NumberField.mixedEmbedding Module GroundTheory.Global
open scoped ComplexConjugate nonZeroDivisors Classical

variable (K : Type) [Field K] [NumberField K]

/- English proof (translation)
Establish `h3 : ∀ w : InfinitePlace K, ∑ φ ∈ Finset.univ.filter (fun φ : K →+* ℂ => InfinitePlace.mk φ = w), ‖φ x‖ ^ 2 = mult w * (w x) ^ 2`. Introduce `w`. Establish `h : ∀ φ ∈ Finset.univ.filter (fun φ : K →+* ℂ => InfinitePlace.mk φ = w), ‖φ x‖ ^ 2 = (w x) ^ 2`. Introduce `φ hφ`. Rewrite using `[← (Finset.mem_filter.mp hφ).2, InfinitePlace.apply]`.

Rewrite using `[Finset.sum_congr rfl h, Finset.sum_const, card_filter_mk_eq, nsmul_eq_mul]`. Rewrite using `[← Finset.sum_fiberwise Finset.univ (fun φ : K →+* ℂ => InfinitePlace.mk φ) (fun φ => ‖φ x‖ ^ 2)]`. Repeatedly rewrite using `[h3]`. Rewrite using `[sum_eq_sum_add_sum]`. Use `congr 1`.

Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations. Rewrite using `[mult_isReal, Nat.cast_one, one_mul, mixedEmbedding_apply_isReal, ← InfinitePlace.norm_embedding_of_isReal w.2 x, Real.norm_eq_abs, sq_abs]`. Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations. Rewrite using `[mult_isComplex, mixedEmbedding_apply_isComplex, InfinitePlace.norm_embedding_eq]`. Evaluate the numerical expressions.
-/
theorem sum_norm_sq_embeddings (x : K) :
    ∑ σ : K →+* ℂ, ‖σ x‖ ^ 2 = ∑ w, (mixedEmbedding K x).1 w ^ 2 +
      ∑ w, 2 * ‖(mixedEmbedding K x).2 w‖ ^ 2 := by
  have h3 : ∀ w : InfinitePlace K,
      ∑ φ ∈ Finset.univ.filter (fun φ : K →+* ℂ => InfinitePlace.mk φ = w), ‖φ x‖ ^ 2 =
        mult w * (w x) ^ 2 := by
    intro w
    have h : ∀ φ ∈ Finset.univ.filter (fun φ : K →+* ℂ => InfinitePlace.mk φ = w),
        ‖φ x‖ ^ 2 = (w x) ^ 2 := by
      intro φ hφ
      rw [← (Finset.mem_filter.mp hφ).2, InfinitePlace.apply]
    rw [Finset.sum_congr rfl h, Finset.sum_const, card_filter_mk_eq, nsmul_eq_mul]
  rw [← Finset.sum_fiberwise Finset.univ (fun φ : K →+* ℂ => InfinitePlace.mk φ)
    (fun φ => ‖φ x‖ ^ 2)]
  simp_rw [h3]
  rw [sum_eq_sum_add_sum]
  congr 1
  · refine Finset.sum_congr rfl fun w _ => ?_
    rw [mult_isReal, Nat.cast_one, one_mul, mixedEmbedding_apply_isReal,
      ← InfinitePlace.norm_embedding_of_isReal w.2 x, Real.norm_eq_abs, sq_abs]
  · refine Finset.sum_congr rfl fun w _ => ?_
    rw [mult_isComplex, mixedEmbedding_apply_isComplex, InfinitePlace.norm_embedding_eq]
    norm_num

omit [Field K] [NumberField K] in
/- English proof (translation)
Rewrite using `[Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re, _root_.norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (by norm_num)]`.
-/
theorem re_conj_sqrtTwo_smul_mul (z : ℂ) :
    (conj ((√2 : ℝ) • z) * ((√2 : ℝ) • z)).re = 2 * ‖z‖ ^ 2 := by
  rw [Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re, _root_.norm_smul, mul_pow,
    Real.norm_eq_abs, sq_abs, Real.sq_sqrt (by norm_num)]

/- English proof (translation)
Rewrite using `[← real_inner_self_eq_norm_sq, mixedToEuclidean, ContinuousLinearEquiv.trans_apply, inner_toMixed_symm]`. Simplify using `only [mapComplexCoord_apply, sqrtTwoSMulComplex_apply]`. Use `congr 1`. Conclude with `Finset.sum_congr rfl fun w _ => by ring`. Conclude with `Finset.sum_congr rfl fun w _ => re_conj_sqrtTwo_smul_mul _`.
-/
theorem norm_sq_mixedToEuclidean (x : mixedSpace K) :
    ‖mixedToEuclidean K x‖ ^ 2 = ∑ w, x.1 w ^ 2 + ∑ w, 2 * ‖x.2 w‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, mixedToEuclidean, ContinuousLinearEquiv.trans_apply,
    inner_toMixed_symm]
  simp only [mapComplexCoord_apply, sqrtTwoSMulComplex_apply]
  congr 1
  · exact Finset.sum_congr rfl fun w _ => by ring
  · exact Finset.sum_congr rfl fun w _ => re_conj_sqrtTwo_smul_mul _

/- English proof (translation)
Rewrite using `[← real_inner_self_eq_norm_sq, mixedToEuclideanConj, ContinuousLinearEquiv.trans_apply, inner_toMixed_symm]`. Simplify using `only [mapComplexCoord_apply, sqrtTwoSMulConj_apply]`. Use `congr 1`. Conclude with `Finset.sum_congr rfl fun w _ => by ring`. Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations.

Rewrite using `[re_conj_sqrtTwo_smul_mul, Complex.norm_conj]`.
-/
theorem norm_sq_mixedToEuclideanConj (x : mixedSpace K) :
    ‖mixedToEuclideanConj K x‖ ^ 2 = ∑ w, x.1 w ^ 2 + ∑ w, 2 * ‖x.2 w‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, mixedToEuclideanConj, ContinuousLinearEquiv.trans_apply,
    inner_toMixed_symm]
  simp only [mapComplexCoord_apply, sqrtTwoSMulConj_apply]
  congr 1
  · exact Finset.sum_congr rfl fun w _ => by ring
  · refine Finset.sum_congr rfl fun w _ => ?_
    rw [re_conj_sqrtTwo_smul_mul, Complex.norm_conj]

noncomputable def integersEuclid : Submodule ℤ (euclidean.mixedSpace K) :=
  ZLattice.comap ℝ (idealLattice K 1) (mixedToEuclidean K).symm.toLinearMap

instance : DiscreteTopology (integersEuclid K) := by
  rw [integersEuclid]
  infer_instance

instance : IsZLattice ℝ (integersEuclid K) := by
  simp_rw [integersEuclid]
  infer_instance

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(mixedToEuclidean K).symm z ∈ idealLattice K 1 ↔ _`. Rewrite using `[mem_idealLattice]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, h⟩`. Establish `hy1 : y ∈ (1 : FractionalIdeal (𝓞 K)⁰ K)` using `by simpa using hy`.

Take `⟨a, rfl⟩` from `(FractionalIdeal.mem_one_iff _).1 hy1`. Use `⟨a, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `mixedToEuclidean K (mixedEmbedding K (algebraMap (𝓞 K) K a)) = z`. Rewrite using `[h, ContinuousLinearEquiv.apply_symm_apply]`. Introduce and unpack `⟨a, rfl⟩`.

Use `⟨(a : K), ?_, by simp⟩` and prove the remaining obligations. Establish `: (a : K) ∈ (1 : FractionalIdeal (𝓞 K)⁰ K)` using `(FractionalIdeal.mem_one_iff _).2 ⟨a, rfl⟩`. Simplify using `using this`.
-/
theorem mem_integersEuclid {z : euclidean.mixedSpace K} :
    z ∈ integersEuclid K ↔ ∃ a : 𝓞 K, mixedToEuclidean K (mixedEmbedding K (a : K)) = z := by
  change (mixedToEuclidean K).symm z ∈ idealLattice K 1 ↔ _
  rw [mem_idealLattice]
  constructor
  · rintro ⟨y, hy, h⟩
    have hy1 : y ∈ (1 : FractionalIdeal (𝓞 K)⁰ K) := by simpa using hy
    obtain ⟨a, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hy1
    refine ⟨a, ?_⟩
    change mixedToEuclidean K (mixedEmbedding K (algebraMap (𝓞 K) K a)) = z
    rw [h, ContinuousLinearEquiv.apply_symm_apply]
  · rintro ⟨a, rfl⟩
    refine ⟨(a : K), ?_, by simp⟩
    have : (a : K) ∈ (1 : FractionalIdeal (𝓞 K)⁰ K) :=
      (FractionalIdeal.mem_one_iff _).2 ⟨a, rfl⟩
    simpa using this

/- English proof (translation)
Rewrite using `[norm_sq_mixedToEuclidean, sum_norm_sq_embeddings]`.
-/
theorem norm_sq_mixedToEuclidean_embedding (x : K) :
    ‖mixedToEuclidean K (mixedEmbedding K x)‖ ^ 2 = ∑ σ : K →+* ℂ, ‖σ x‖ ^ 2 := by
  rw [norm_sq_mixedToEuclidean, sum_norm_sq_embeddings]

/- English proof (translation)
Use `set y0 := (mixedToEuclideanConj K).symm y with hy0`. Establish `hmem : y0 ∈ idealLattice K (traceDualIdeal K 1)`. Rewrite using `[mem_idealLattice_traceDualIdeal_iff]`. Introduce `x hx`. Take `⟨m, hm⟩` from `h (mixedToEuclidean K x) (by`.

Express the relevant statement in the definitionally equal form `(mixedToEuclidean K).symm (mixedToEuclidean K x) ∈ idealLattice K 1`. Simplify using `using hx)`. Use `⟨m, ?_⟩` and prove the remaining obligations. Rewrite using `[mixedTraceForm_comm, mixedTraceForm_eq_inner, hy0, ContinuousLinearEquiv.apply_symm_apply, hm]`. Take `⟨t, ht, hty⟩` from `(mem_idealLattice K _).1 hmem`.

Establish `hyy : y = mixedToEuclideanConj K (mixedEmbedding K t)`. Rewrite using `[hty, hy0, ContinuousLinearEquiv.apply_symm_apply]`. Establish `ht0 : t ≠ 0`. Introduce and unpack `rfl`. Conclude with `hy (by simpa using hyy)`.

Establish `ht' : t ∈ (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K)⁻¹`. Rewrite using `[← GlobalTheory.dual_one_eq_inv_differentIdeal]`. Simplify `ht` using `[coe_traceDualIdeal]`. Establish `hb` using `GlobalTheory.finrank_div_rootDiscr_sq_le_sum_sq ht' ht0`. Rewrite using `[hyy, norm_sq_mixedToEuclideanConj, ← sum_norm_sq_embeddings]`.

Conclude with `hb`.
-/
theorem finrank_div_rootDiscr_sq_le_norm_sq {y : euclidean.mixedSpace K} (hy : y ≠ 0)
    (h : ∀ x ∈ integersEuclid K, ∃ m : ℤ, ⟪x, y⟫_ℝ = m) :
    (finrank ℚ K : ℝ) / rootDiscr K ^ 2 ≤ ‖y‖ ^ 2 := by
  set y0 := (mixedToEuclideanConj K).symm y with hy0
  have hmem : y0 ∈ idealLattice K (traceDualIdeal K 1) := by
    rw [mem_idealLattice_traceDualIdeal_iff]
    intro x hx
    obtain ⟨m, hm⟩ := h (mixedToEuclidean K x) (by
      change (mixedToEuclidean K).symm (mixedToEuclidean K x) ∈ idealLattice K 1
      simpa using hx)
    refine ⟨m, ?_⟩
    rw [mixedTraceForm_comm, mixedTraceForm_eq_inner, hy0,
      ContinuousLinearEquiv.apply_symm_apply, hm]
  obtain ⟨t, ht, hty⟩ := (mem_idealLattice K _).1 hmem
  have hyy : y = mixedToEuclideanConj K (mixedEmbedding K t) := by
    rw [hty, hy0, ContinuousLinearEquiv.apply_symm_apply]
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact hy (by simpa using hyy)
  have ht' : t ∈ (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K)⁻¹ := by
    rw [← GlobalTheory.dual_one_eq_inv_differentIdeal]
    simpa [coe_traceDualIdeal] using ht
  have hb := GlobalTheory.finrank_div_rootDiscr_sq_le_sum_sq ht' ht0
  rw [hyy, norm_sq_mixedToEuclideanConj, ← sum_norm_sq_embeddings]
  exact hb

/- English proof (translation)
Establish `hfr : finrank ℝ (euclidean.mixedSpace K) = finrank ℚ K` using `euclidean.finrank K`. Establish `hn : (0 : ℝ) < finrank ℚ K` using `by exact_mod_cast finrank_pos`. Establish `hrd : 0 < rootDiscr K`. Rewrite using `[rootDiscr_def]`. Conclude with `Real.rpow_pos_of_pos (by exact_mod_cast abs_pos.2 (discr_ne_zero K)) _`.

Establish `hμ : 0 < √(finrank ℚ K : ℝ) / rootDiscr K` using `by positivity`. Establish `hdual : ∀ y : euclidean.mixedSpace K, y ≠ 0 → (∀ x ∈ integersEuclid K, ∃ m : ℤ, ⟪x, y⟫_ℝ = m) → √(finrank ℚ K : ℝ) / rootDiscr K ≤ ‖y‖`. Introduce `y hy h`. Use `(sq_le_sq₀ hμ.le (norm_nonneg y)).1 ?_` and prove the remaining obligations. Rewrite using `[div_pow, Real.sq_sqrt hn.le]`.

Conclude with `finrank_div_rootDiscr_sq_le_norm_sq K hy h`. Take `⟨b, hbL, hbi, hbn⟩` from `exists_independent_le_of_dual_min (euclidean.mixedSpace K) (integersEuclid K) _ hμ hdual`. Establish `hbound : (finrank ℚ K : ℝ) ^ (3 / 2 : ℝ) / (√(finrank ℚ K : ℝ) / rootDiscr K) = finrank ℚ K * rootDiscr K`. Rewrite using `[show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hn, Real.rpow_one, ← Real.sqrt_eq_rpow]`. Establish `: √(finrank ℚ K : ℝ) ≠ 0` using `(Real.sqrt_pos.2 hn).ne'`.

Clear the denominators using the available nonvanishing facts. Establish `hb' : ∀ i : Fin (finrank ℚ K), ∃ a : 𝓞 K, mixedToEuclidean K (mixedEmbedding K (a : K)) = b (Fin.cast hfr.symm i)` using `fun i => (mem_integersEuclid K).1 (hbL _)`. Use `choose a ha using hb'`. Use `⟨a, ?_, fun i σ => ?_⟩` and prove the remaining obligations. Establish `h1 : LinearIndependent ℤ (fun i : Fin (finrank ℚ K) => b (Fin.cast hfr.symm i))` using `(hbi.comp _ (Fin.cast_injective _)).restrict_scalars (R := ℤ) (fun x y h => by simpa using h)`.

Rewrite using `[← LinearIndependent.iff_fractionRing (R := ℤ) (K := ℚ)]`. Set `g : K →ₗ[ℤ] euclidean.mixedSpace K` to `AddMonoidHom.toIntLinearMap { toFun := fun x => mixedToEuclidean K (mixedEmbedding K x) map_zero' := by simp map_add' := fun x y => by simp }`. Establish `hg : (⇑g ∘ fun i => ((a i : 𝓞 K) : K)) = fun i => b (Fin.cast hfr.symm i)` using `funext ha`. Use `LinearIndependent.of_comp g ?_` and prove the remaining obligations. Rewrite using `[hg]`.

Conclude with `h1`. Establish `h2 : ‖σ (a i)‖ ^ 2 ≤ ∑ τ : K →+* ℂ, ‖τ (a i)‖ ^ 2` using `Finset.single_le_sum (f := fun τ : K →+* ℂ => ‖τ (a i)‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ σ)`. Rewrite `h2` using `[← norm_sq_mixedToEuclidean_embedding, ha i]`. Establish `h3` using `hbn (Fin.cast hfr.symm i)`. Rewrite `h3` using `[show ((finrank ℝ (euclidean.mixedSpace K) : ℕ) : ℝ) = finrank ℚ K by rw [hfr], hbound]`.

Conclude with `(sq_le_sq₀ (norm_nonneg _) (by positivity)).1 (h2.trans (pow_le_pow_left₀ (norm_nonneg _) h3 2))`.
-/
theorem exists_short_integers :
    ∃ a : Fin (finrank ℚ K) → 𝓞 K, LinearIndependent ℚ (fun i => (a i : K)) ∧
      ∀ i (σ : K →+* ℂ), ‖σ (a i)‖ ≤ finrank ℚ K * rootDiscr K := by
  have hfr : finrank ℝ (euclidean.mixedSpace K) = finrank ℚ K := euclidean.finrank K
  have hn : (0 : ℝ) < finrank ℚ K := by exact_mod_cast finrank_pos
  have hrd : 0 < rootDiscr K := by
    rw [rootDiscr_def]
    exact Real.rpow_pos_of_pos (by exact_mod_cast abs_pos.2 (discr_ne_zero K)) _
  have hμ : 0 < √(finrank ℚ K : ℝ) / rootDiscr K := by positivity
  have hdual : ∀ y : euclidean.mixedSpace K, y ≠ 0 →
      (∀ x ∈ integersEuclid K, ∃ m : ℤ, ⟪x, y⟫_ℝ = m) →
      √(finrank ℚ K : ℝ) / rootDiscr K ≤ ‖y‖ := by
    intro y hy h
    refine (sq_le_sq₀ hμ.le (norm_nonneg y)).1 ?_
    rw [div_pow, Real.sq_sqrt hn.le]
    exact finrank_div_rootDiscr_sq_le_norm_sq K hy h
  obtain ⟨b, hbL, hbi, hbn⟩ := exists_independent_le_of_dual_min (euclidean.mixedSpace K) (integersEuclid K) _ hμ hdual
  have hbound : (finrank ℚ K : ℝ) ^ (3 / 2 : ℝ) / (√(finrank ℚ K : ℝ) / rootDiscr K) =
      finrank ℚ K * rootDiscr K := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hn, Real.rpow_one,
      ← Real.sqrt_eq_rpow]
    have : √(finrank ℚ K : ℝ) ≠ 0 := (Real.sqrt_pos.2 hn).ne'
    field_simp
  have hb' : ∀ i : Fin (finrank ℚ K), ∃ a : 𝓞 K,
      mixedToEuclidean K (mixedEmbedding K (a : K)) = b (Fin.cast hfr.symm i) :=
    fun i => (mem_integersEuclid K).1 (hbL _)
  choose a ha using hb'
  refine ⟨a, ?_, fun i σ => ?_⟩
  · have h1 : LinearIndependent ℤ (fun i : Fin (finrank ℚ K) => b (Fin.cast hfr.symm i)) :=
      (hbi.comp _ (Fin.cast_injective _)).restrict_scalars (R := ℤ)
        (fun x y h => by simpa using h)
    rw [← LinearIndependent.iff_fractionRing (R := ℤ) (K := ℚ)]
    let g : K →ₗ[ℤ] euclidean.mixedSpace K := AddMonoidHom.toIntLinearMap
      { toFun := fun x => mixedToEuclidean K (mixedEmbedding K x)
        map_zero' := by simp
        map_add' := fun x y => by simp }
    have hg : (⇑g ∘ fun i => ((a i : 𝓞 K) : K)) = fun i => b (Fin.cast hfr.symm i) := funext ha
    refine LinearIndependent.of_comp g ?_
    rw [hg]
    exact h1
  · have h2 : ‖σ (a i)‖ ^ 2 ≤ ∑ τ : K →+* ℂ, ‖τ (a i)‖ ^ 2 :=
      Finset.single_le_sum (f := fun τ : K →+* ℂ => ‖τ (a i)‖ ^ 2)
        (fun _ _ => by positivity) (Finset.mem_univ σ)
    rw [← norm_sq_mixedToEuclidean_embedding, ha i] at h2
    have h3 := hbn (Fin.cast hfr.symm i)
    rw [show ((finrank ℝ (euclidean.mixedSpace K) : ℕ) : ℝ) = finrank ℚ K by rw [hfr], hbound] at h3
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).1
      (h2.trans (pow_le_pow_left₀ (norm_nonneg _) h3 2))

end ShortIntegers

/- English proof (translation)
Introduce `E _ _ _`. Establish `h : hostRd E = rootDiscr E` using `by simp [hostRd, rootDiscr_def]`. Rewrite using `[h]`. Conclude with `exists_short_integers E`.
-/
theorem exists_full_family_conjugates_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E],
    ∃ a : Fin (Module.finrank ℚ E) → 𝓞 E, LinearIndependent ℚ (fun i => (a i : E)) ∧
      ∀ i (σ : E →+* ℂ), ‖σ (a i)‖ ≤ Module.finrank ℚ E * hostRd E := by
  intro E _ _ _
  have h : hostRd E = rootDiscr E := by simp [hostRd, rootDiscr_def]
  rw [h]
  exact exists_short_integers E

end GlobalTheory.CompanionTheory.Ar.Cusp
