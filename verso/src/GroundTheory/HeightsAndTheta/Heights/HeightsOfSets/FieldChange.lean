import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.FiniteSupportHeight
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CardEmbeddingsRestrict
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField Module

noncomputable section

section Extension

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

open Classical in

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.CardEmbeddingsRestrict.card_embeddings_restrict τ`.
-/
theorem card_embeddings_restrict (τ : K →+* ℂ) :
    (Finset.univ.filter fun σ : L →+* ℂ ↦ σ.comp (algebraMap K L) = τ).card = finrank K L :=
  _root_.UpperTheory.Reformulated.B.CardEmbeddingsRestrict.card_embeddings_restrict τ

/- English proof (translation)
Rewrite using `[← Finset.sum_fiberwise Finset.univ (fun σ : L →+* ℂ ↦ σ.comp (algebraMap K L)), Finset.mul_sum]`. Use `Finset.sum_congr rfl fun τ _ ↦ ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_congr rfl (g := fun _ ↦ f τ) (fun σ hσ ↦ by rw [(Finset.mem_filter.mp hσ).2]), Finset.sum_const, card_embeddings_restrict, nsmul_eq_mul]`.
-/
theorem sum_embeddings_restrict (f : (K →+* ℂ) → ℝ) :
    ∑ σ : L →+* ℂ, f (σ.comp (algebraMap K L)) = finrank K L * ∑ τ : K →+* ℂ, f τ := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ (fun σ : L →+* ℂ ↦ σ.comp (algebraMap K L)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ ↦ ?_
  rw [Finset.sum_congr rfl (g := fun _ ↦ f τ) (fun σ hσ ↦ by rw [(Finset.mem_filter.mp hσ).2]),
    Finset.sum_const, card_embeddings_restrict, nsmul_eq_mul]

/- English proof (translation)
Use `set y' : ι → 𝓞 L := fun i ↦ algebraMap (𝓞 K) (𝓞 L) (y i) with hy'`. Establish `hinj : Function.Injective (algebraMap (𝓞 K) (𝓞 L))`. Introduce `a b hab`. Establish `h1 : algebraMap K L (a : K) = algebraMap K L (b : K)` using `congrArg (fun t : 𝓞 L ↦ (t : L)) hab`. Conclude with `RingOfIntegers.ext ((algebraMap K L).injective h1)`.

Establish `hy'0 : y' ≠ 0`. Take `⟨i, hi⟩` from `Function.ne_iff.mp hy`. Conclude with `Function.ne_iff.mpr ⟨i, fun h ↦ hi (hinj (h.trans (map_zero _).symm))⟩`. Establish `hK` using `absNorm_mul_finprod_finitePlace_eq_one (K := K) hy`. Establish `hL` using `absNorm_mul_finprod_finitePlace_eq_one (K := L) hy'0`.

Establish `hspan : Ideal.span (Set.range y') = (Ideal.span (Set.range y)).map (algebraMap (𝓞 K) (𝓞 L))`. Rewrite using `[Ideal.map_span, ← Set.range_comp]`. Both sides reduce to the same expression. Rewrite `hL` using `[hspan, Ideal.absNorm_algebraMap, ← IsFractionRing.finrank_eq (𝓞 K) K (𝓞 L) L]`. Establish `hL' : ∏ᶠ w : FinitePlace L, ⨆ i, w (algebraMap K L (y i)) = ∏ᶠ w : FinitePlace L, ⨆ i, w (y' i)` using `rfl`.

Rewrite using `[hL']`. Use `set N : ℝ := ((Ideal.span (Set.range y)).absNorm : ℝ)`. Establish `hN : N ≠ 0`. Introduce `h`. Rewrite `hK` using `[h, zero_mul]`.

Conclude with `zero_ne_one hK`. Move the coercions through the operations in `at hL`. Rewrite using `[eq_inv_of_mul_eq_one_right hL, eq_inv_of_mul_eq_one_right hK, inv_pow]`.
-/
theorem finprod_iSup_algebraMap_int {ι : Type*} [Finite ι] {y : ι → 𝓞 K} (hy : y ≠ 0) :
    ∏ᶠ w : FinitePlace L, ⨆ i, w (algebraMap K L (y i)) =
      (∏ᶠ v : FinitePlace K, ⨆ i, v (y i)) ^ finrank K L := by
  set y' : ι → 𝓞 L := fun i ↦ algebraMap (𝓞 K) (𝓞 L) (y i) with hy'
  have hinj : Function.Injective (algebraMap (𝓞 K) (𝓞 L)) := by
    intro a b hab
    have h1 : algebraMap K L (a : K) = algebraMap K L (b : K) := congrArg (fun t : 𝓞 L ↦ (t : L)) hab
    exact RingOfIntegers.ext ((algebraMap K L).injective h1)
  have hy'0 : y' ≠ 0 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hy
    exact Function.ne_iff.mpr ⟨i, fun h ↦ hi (hinj (h.trans (map_zero _).symm))⟩
  have hK := absNorm_mul_finprod_finitePlace_eq_one (K := K) hy
  have hL := absNorm_mul_finprod_finitePlace_eq_one (K := L) hy'0
  have hspan : Ideal.span (Set.range y') =
      (Ideal.span (Set.range y)).map (algebraMap (𝓞 K) (𝓞 L)) := by
    rw [Ideal.map_span, ← Set.range_comp]
    rfl
  rw [hspan, Ideal.absNorm_algebraMap, ← IsFractionRing.finrank_eq (𝓞 K) K (𝓞 L) L] at hL
  have hL' : ∏ᶠ w : FinitePlace L, ⨆ i, w (algebraMap K L (y i)) =
      ∏ᶠ w : FinitePlace L, ⨆ i, w (y' i) := rfl
  rw [hL']
  set N : ℝ := ((Ideal.span (Set.range y)).absNorm : ℝ)
  have hN : N ≠ 0 := by
    intro h
    rw [h, zero_mul] at hK
    exact zero_ne_one hK
  push_cast at hL
  rw [eq_inv_of_mul_eq_one_right hL, eq_inv_of_mul_eq_one_right hK, inv_pow]

/- English proof (translation)
Take `⟨i0, hi0⟩` from `Function.ne_iff.mp hy`. Establish `: Nonempty {j // y j ≠ 0}` using `⟨⟨i0, hi0⟩⟩`. Establish `h` using `Function.HasFiniteMulSupport.iSup (ι := {j // y j ≠ 0}) (f := fun i (w : FinitePlace F) ↦ w (y i)) fun i ↦ FinitePlace.hasFiniteMulSupport i.2`. Establish `e : (fun w : FinitePlace F ↦ ⨆ i, w (y i)) = fun w ↦ ⨆ i : {j // y j ≠ 0}, w (y i)`. Use function extensionality and compare the values at `fun w ↦ Finite.iSup_eq_iSup_subtype hy`.

Rewrite using `[e]`. Conclude with `h`.
-/
theorem hasFiniteMulSupport_iSup_place {F : Type*} [Field F] [NumberField F] {ι : Type*} [Finite ι]
    {y : ι → F} (hy : y ≠ 0) : Function.HasFiniteMulSupport fun w : FinitePlace F ↦ ⨆ i, w (y i) := by
  obtain ⟨i0, hi0⟩ := Function.ne_iff.mp hy
  have : Nonempty {j // y j ≠ 0} := ⟨⟨i0, hi0⟩⟩
  have h := Function.HasFiniteMulSupport.iSup (ι := {j // y j ≠ 0})
    (f := fun i (w : FinitePlace F) ↦ w (y i)) fun i ↦ FinitePlace.hasFiniteMulSupport i.2
  have e : (fun w : FinitePlace F ↦ ⨆ i, w (y i)) = fun w ↦ ⨆ i : {j // y j ≠ 0}, w (y i) :=
    funext fun w ↦ Finite.iSup_eq_iSup_subtype hy
  rw [e]
  exact h

/- English proof (translation)
Rewrite using `[FinitePlace.prod_eq_inv_abs_norm ((map_ne_zero _).mpr hc), FinitePlace.prod_eq_inv_abs_norm hc, ← Algebra.norm_norm (S := K), Algebra.norm_algebraMap, map_pow]`. Use `push_cast`. Rewrite using `[abs_pow, inv_pow]`.
-/
theorem finprod_algebraMap {c : K} (hc : c ≠ 0) :
    ∏ᶠ w : FinitePlace L, w (algebraMap K L c) = (∏ᶠ v : FinitePlace K, v c) ^ finrank K L := by
  rw [FinitePlace.prod_eq_inv_abs_norm ((map_ne_zero _).mpr hc), FinitePlace.prod_eq_inv_abs_norm hc,
    ← Algebra.norm_norm (S := K), Algebra.norm_algebraMap, map_pow]
  push_cast
  rw [abs_pow, inv_pow]

/- English proof (translation)
Take `⟨⟨b, hb⟩, hint⟩` from `IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 K)) y`. Use `choose z hz using hint`. Establish `hb0 : (b : K) ≠ 0`. Rewrite using `[Ne, RingOfIntegers.coe_eq_zero_iff]`. Conclude with `nonZeroDivisors.ne_zero hb`.

Establish `hzy : ∀ i, ((z i : 𝓞 K) : K) = (b : K) * y i` using `fun i ↦ by`. Establish `h` using `hz i`. Simplify using `only [Algebra.smul_def] at h`. Conclude with `h`. Establish `hz0 : z ≠ 0`.

Take `⟨i, hi⟩` from `Function.ne_iff.mp hy`. Use `Function.ne_iff.mpr ⟨i, fun h ↦ hi ?_⟩` and prove the remaining obligations. Establish `h1 : (b : K) * y i = 0` using `by rw [← hzy i, h]; simp`. Conclude with `(mul_eq_zero.mp h1).resolve_left hb0`. Establish `key` using `finprod_iSup_algebraMap_int (L := L) hz0`.

Establish `hsupK : ∀ v : FinitePlace K, ⨆ i, v (z i : K) = v (b : K) * ⨆ i, v (y i)`. Introduce `v`. Repeatedly rewrite using `[hzy, map_mul]`. Conclude with `(Real.mul_iSup_of_nonneg (apply_nonneg v _) _).symm`. Establish `hsupL : ∀ w : FinitePlace L, ⨆ i, w (algebraMap K L (z i : K)) = w (algebraMap K L (b : K)) * ⨆ i, w (algebraMap K L (y i))`.

Introduce `w`. Repeatedly rewrite using `[hzy, map_mul]`. Conclude with `(Real.mul_iSup_of_nonneg (apply_nonneg w _) _).symm`. Rewrite `key` using `[hsupK, hsupL]`. Establish `hyL : (fun i ↦ algebraMap K L (y i)) ≠ 0`.

Take `⟨i, hi⟩` from `Function.ne_iff.mp hy`. Conclude with `Function.ne_iff.mpr ⟨i, (map_ne_zero _).mpr hi⟩`. Rewrite `key` using `[finprod_mul_distrib (FinitePlace.hasFiniteMulSupport ((map_ne_zero _).mpr hb0)) (hasFiniteMulSupport_iSup_place hyL), finprod_mul_distrib (FinitePlace.hasFiniteMulSupport hb0) (hasFiniteMulSupport_iSup_place hy), mul_pow, finprod_algebraMap hb0]`. Establish `hne : (∏ᶠ v : FinitePlace K, v (b : K)) ^ finrank K L ≠ 0`. Rewrite using `[FinitePlace.prod_eq_inv_abs_norm hb0]`.

Simplify using `[hb0]`. Conclude with `mul_left_cancel₀ hne key`.
-/
theorem finprod_iSup_algebraMap {ι : Type*} [Finite ι] {y : ι → K} (hy : y ≠ 0) :
    ∏ᶠ w : FinitePlace L, ⨆ i, w (algebraMap K L (y i)) =
      (∏ᶠ v : FinitePlace K, ⨆ i, v (y i)) ^ finrank K L := by
  obtain ⟨⟨b, hb⟩, hint⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 K)) y
  choose z hz using hint
  have hb0 : (b : K) ≠ 0 := by
    rw [Ne, RingOfIntegers.coe_eq_zero_iff]
    exact nonZeroDivisors.ne_zero hb
  have hzy : ∀ i, ((z i : 𝓞 K) : K) = (b : K) * y i := fun i ↦ by
    have h := hz i
    simp only [Algebra.smul_def] at h
    exact h
  have hz0 : z ≠ 0 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hy
    refine Function.ne_iff.mpr ⟨i, fun h ↦ hi ?_⟩
    have h1 : (b : K) * y i = 0 := by rw [← hzy i, h]; simp
    exact (mul_eq_zero.mp h1).resolve_left hb0
  have key := finprod_iSup_algebraMap_int (L := L) hz0
  have hsupK : ∀ v : FinitePlace K, ⨆ i, v (z i : K) = v (b : K) * ⨆ i, v (y i) := by
    intro v
    simp_rw [hzy, map_mul]
    exact (Real.mul_iSup_of_nonneg (apply_nonneg v _) _).symm
  have hsupL : ∀ w : FinitePlace L, ⨆ i, w (algebraMap K L (z i : K)) =
      w (algebraMap K L (b : K)) * ⨆ i, w (algebraMap K L (y i)) := by
    intro w
    simp_rw [hzy, map_mul]
    exact (Real.mul_iSup_of_nonneg (apply_nonneg w _) _).symm
  simp_rw [hsupK, hsupL] at key
  have hyL : (fun i ↦ algebraMap K L (y i)) ≠ 0 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hy
    exact Function.ne_iff.mpr ⟨i, (map_ne_zero _).mpr hi⟩
  rw [finprod_mul_distrib (FinitePlace.hasFiniteMulSupport ((map_ne_zero _).mpr hb0))
      (hasFiniteMulSupport_iSup_place hyL),
    finprod_mul_distrib (FinitePlace.hasFiniteMulSupport hb0) (hasFiniteMulSupport_iSup_place hy),
    mul_pow, finprod_algebraMap hb0] at key
  have hne : (∏ᶠ v : FinitePlace K, v (b : K)) ^ finrank K L ≠ 0 := by
    rw [FinitePlace.prod_eq_inv_abs_norm hb0]
    simp [hb0]
  exact mul_left_cancel₀ hne key

/- English proof (translation)
Establish `hf' : (Function.mulSupport f).Finite` using `hf`. Establish `hs : Function.support (fun a ↦ Real.log (f a)) ⊆ hf'.toFinset`. Introduce `a ha`. Rewrite using `[Set.Finite.coe_toFinset]`. Introduce `h1`.

Conclude with `ha (by show Real.log (f a) = 0; rw [h1, Real.log_one])`. Rewrite using `[finsum_eq_sum_of_support_subset _ hs, finprod_eq_prod_of_mulSupport_subset (s := hf'.toFinset) f (by rw [Set.Finite.coe_toFinset]), Real.log_prod fun a _ ↦ (hpos a).ne']`.
-/
theorem finsum_log_eq_log_finprod {α : Type*} {f : α → ℝ} (hpos : ∀ a, 0 < f a)
    (hf : Function.HasFiniteMulSupport f) : ∑ᶠ a, Real.log (f a) = Real.log (∏ᶠ a, f a) := by
  have hf' : (Function.mulSupport f).Finite := hf
  have hs : Function.support (fun a ↦ Real.log (f a)) ⊆ hf'.toFinset := by
    intro a ha
    rw [Set.Finite.coe_toFinset]
    intro h1
    exact ha (by show Real.log (f a) = 0; rw [h1, Real.log_one])
  rw [finsum_eq_sum_of_support_subset _ hs,
    finprod_eq_prod_of_mulSupport_subset (s := hf'.toFinset) f (by rw [Set.Finite.coe_toFinset]),
    Real.log_prod fun a _ ↦ (hpos a).ne']

/- English proof (translation)
Take `⟨i0, hi0⟩` from `Function.ne_iff.mp hy`. Conclude with `lt_of_lt_of_le ((FinitePlace.pos_iff (w := w)).mpr hi0) (le_ciSup (f := fun i ↦ w (y i)) (Set.finite_range _).bddAbove i0)`.
-/
theorem iSup_place_pos {F : Type*} [Field F] [NumberField F] {ι : Type*} [Finite ι] {y : ι → F}
    (hy : y ≠ 0) (w : FinitePlace F) : 0 < ⨆ i, w (y i) := by
  obtain ⟨i0, hi0⟩ := Function.ne_iff.mp hy
  exact lt_of_lt_of_le ((FinitePlace.pos_iff (w := w)).mpr hi0)
    (le_ciSup (f := fun i ↦ w (y i)) (Set.finite_range _).bddAbove i0)

/- English proof (translation)
Establish `hyL : (fun i ↦ algebraMap K L (y i)) ≠ 0`. Take `⟨i, hi⟩` from `Function.ne_iff.mp hy`. Conclude with `Function.ne_iff.mpr ⟨i, (map_ne_zero _).mpr hi⟩`. Rewrite using `[finsum_log_eq_log_finprod (iSup_place_pos hyL) (hasFiniteMulSupport_iSup_place hyL), finsum_log_eq_log_finprod (iSup_place_pos hy) (hasFiniteMulSupport_iSup_place hy), finprod_iSup_algebraMap hy, Real.log_pow]`.
-/
theorem finsum_log_iSup_algebraMap {ι : Type*} [Finite ι] {y : ι → K} (hy : y ≠ 0) :
    ∑ᶠ w : FinitePlace L, Real.log (⨆ i, w (algebraMap K L (y i))) =
      finrank K L * ∑ᶠ v : FinitePlace K, Real.log (⨆ i, v (y i)) := by
  have hyL : (fun i ↦ algebraMap K L (y i)) ≠ 0 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hy
    exact Function.ne_iff.mpr ⟨i, (map_ne_zero _).mpr hi⟩
  rw [finsum_log_eq_log_finprod (iSup_place_pos hyL) (hasFiniteMulSupport_iSup_place hyL),
    finsum_log_eq_log_finprod (iSup_place_pos hy) (hasFiniteMulSupport_iSup_place hy),
    finprod_iSup_algebraMap hy, Real.log_pow]

end Extension

/- English proof (translation)
Establish `hS : (⋃ k, Function.support (g k)).Finite` using `Set.finite_iUnion hg`. Establish `hsub : ∀ k, Function.support (g k) ⊆ hS.toFinset` using `fun k ↦ by`. Rewrite using `[Set.Finite.coe_toFinset]`. Conclude with `Set.subset_iUnion (fun k ↦ Function.support (g k)) k`. Establish `hsum : Function.support (fun a ↦ ∑ k, c k * g k a) ⊆ hS.toFinset`.

Introduce `a ha`. Rewrite using `[Set.Finite.coe_toFinset, Set.mem_iUnion]`. Assume the negation of the conclusion as `h`. Use `push Not at h`. Conclude with `ha (Finset.sum_eq_zero fun k _ ↦ by rw [Function.notMem_support.mp (h k), mul_zero])`.

Rewrite using `[finsum_eq_sum_of_support_subset _ hsum, Finset.sum_comm]`. Use `Finset.sum_congr rfl fun k _ ↦ ?_` and prove the remaining obligations. Rewrite using `[finsum_eq_sum_of_support_subset _ (hsub k), Finset.mul_sum]`.
-/
theorem finsum_sum_mul {α ι : Type*} [Fintype ι] (c : ι → ℝ) (g : ι → α → ℝ)
    (hg : ∀ k, (Function.support (g k)).Finite) :
    ∑ᶠ a, ∑ k, c k * g k a = ∑ k, c k * ∑ᶠ a, g k a := by
  have hS : (⋃ k, Function.support (g k)).Finite := Set.finite_iUnion hg
  have hsub : ∀ k, Function.support (g k) ⊆ hS.toFinset := fun k ↦ by
    rw [Set.Finite.coe_toFinset]
    exact Set.subset_iUnion (fun k ↦ Function.support (g k)) k
  have hsum : Function.support (fun a ↦ ∑ k, c k * g k a) ⊆ hS.toFinset := by
    intro a ha
    rw [Set.Finite.coe_toFinset, Set.mem_iUnion]
    by_contra h
    push Not at h
    exact ha (Finset.sum_eq_zero fun k _ ↦ by rw [Function.notMem_support.mp (h k), mul_zero])
  rw [finsum_eq_sum_of_support_subset _ hsum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [finsum_eq_sum_of_support_subset _ (hsub k), Finset.mul_sum]

/- English proof (translation)
Use `Set.Finite.subset (hasFiniteMulSupport_iSup_place hy) fun w hw h1 ↦ hw ?_` and prove the remaining obligations. Establish `h1' : (⨆ i, w (y i)) = 1` using `h1`. Express the relevant statement in the definitionally equal form `Real.log (⨆ i, w (y i)) = 0`. Rewrite using `[h1', Real.log_one]`.
-/
theorem support_log_iSup_place_finite {F : Type*} [Field F] [NumberField F] {ι : Type*} [Finite ι]
    {y : ι → F} (hy : y ≠ 0) :
    (Function.support fun w : FinitePlace F ↦ Real.log (⨆ i, w (y i))).Finite := by
  refine Set.Finite.subset (hasFiniteMulSupport_iSup_place hy) fun w hw h1 ↦ hw ?_
  have h1' : (⨆ i, w (y i)) = 1 := h1
  change Real.log (⨆ i, w (y i)) = 0
  rw [h1', Real.log_one]

section Cone

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

omit [DecidableEq ι] in

/- English proof (translation)
Establish `hyL : ∀ k, (fun i ↦ algebraMap K L (y k i)) ≠ 0` using `fun k ↦ by`. Take `⟨i, hi⟩` from `Function.ne_iff.mp (hy k)`. Conclude with `Function.ne_iff.mpr ⟨i, (map_ne_zero _).mpr hi⟩`. Unfold `finiteTerm`. Rewrite using `[finsum_sum_mul _ _ fun k ↦ support_log_iSup_place_finite (hyL k), finsum_sum_mul _ _ fun k ↦ support_log_iSup_place_finite (hy k), Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun k _ ↦ ?_` and prove the remaining obligations. Rewrite using `[finsum_log_iSup_algebraMap (hy k)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem finsum_finiteTerm_algebraMap {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] (A : HermLine n) {y : Cone n K} (hy : BlockNonzero y) :
    ∑ᶠ w : FinitePlace L, finiteTerm A w (fun k i ↦ algebraMap K L (y k i)) =
      finrank K L * ∑ᶠ v : FinitePlace K, finiteTerm A v y := by
  have hyL : ∀ k, (fun i ↦ algebraMap K L (y k i)) ≠ 0 := fun k ↦ by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp (hy k)
    exact Function.ne_iff.mpr ⟨i, (map_ne_zero _).mpr hi⟩
  unfold finiteTerm
  rw [finsum_sum_mul _ _ fun k ↦ support_log_iSup_place_finite (hyL k),
    finsum_sum_mul _ _ fun k ↦ support_log_iSup_place_finite (hy k), Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [finsum_log_iSup_algebraMap (hy k)]
  ring

omit [DecidableEq ι] in

/- English proof (translation)
Establish `hKL : coordField x ≤ L` using `IntermediateField.adjoin_le_iff.mpr (by rintro _ ⟨v, rfl⟩; exact hx v.1 v.2)`. Set `_ : Algebra (coordField x) L` to `(IntermediateField.inclusion hKL).toRingHom.toAlgebra`. Establish `hco : coordIn L x hx = fun k i ↦ algebraMap (coordField x) L (coordVec x k i)` using `rfl`. Establish `hblock : BlockNonzero (coordVec x)` using `fun k h ↦ hx0 k (funext fun i ↦ by`. Use `congrFun h i` as an intermediate fact.

Conclude with `congrArg Subtype.val this)`. Establish `hfin` using `finsum_finiteTerm_algebraMap (L := L) A hblock`. Establish `harch` using `sum_embeddings_restrict (K := coordField x) (L := L) (fun τ ↦ Real.log (A.metric fun k i ↦ τ (coordVec x k i)))`. Establish `hdeg` using `Module.finrank_mul_finrank ℚ (coordField x) L`. Rewrite using `[hco, hfin]`.

Express the relevant statement in the definitionally equal form `_ = _ * (_ + ∑ σ : L →+* ℂ, Real.log (A.metric fun k i ↦ (σ.comp (algebraMap (coordField x) L)) (coordVec x k i)))`. Rewrite using `[harch, ← hdeg]`. Unfold `height`. Establish `h1 : (0 : ℝ) < finrank ℚ (coordField x)` using `by exact_mod_cast Module.finrank_pos`. Establish `h2 : (0 : ℝ) < finrank (coordField x) L` using `by exact_mod_cast Module.finrank_pos`.

Use `push_cast`. Clear the denominators using the available nonvanishing facts. Both sides reduce to the same expression.
-/
theorem height_eq_of_le (A : HermLine n) {x : Cone n (AlgebraicClosure ℚ)} (hx0 : BlockNonzero x)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField L] (hx : ∀ k i, x k i ∈ L) :
    height A x = ((finrank ℚ L : ℝ))⁻¹ *
      (∑ᶠ w : FinitePlace L, finiteTerm A w (coordIn L x hx) +
        ∑ σ : L →+* ℂ, Real.log (A.metric fun k i ↦ σ (coordIn L x hx k i))) := by
  have hKL : coordField x ≤ L :=
    IntermediateField.adjoin_le_iff.mpr (by rintro _ ⟨v, rfl⟩; exact hx v.1 v.2)
  let _ : Algebra (coordField x) L := (IntermediateField.inclusion hKL).toRingHom.toAlgebra
  have hco : coordIn L x hx = fun k i ↦ algebraMap (coordField x) L (coordVec x k i) := rfl
  have hblock : BlockNonzero (coordVec x) := fun k h ↦ hx0 k (funext fun i ↦ by
    have := congrFun h i
    exact congrArg Subtype.val this)
  have hfin := finsum_finiteTerm_algebraMap (L := L) A hblock
  have harch := sum_embeddings_restrict (K := coordField x) (L := L)
    (fun τ ↦ Real.log (A.metric fun k i ↦ τ (coordVec x k i)))
  have hdeg := Module.finrank_mul_finrank ℚ (coordField x) L
  rw [hco, hfin]
  change _ = _ * (_ + ∑ σ : L →+* ℂ, Real.log (A.metric fun k i ↦
    (σ.comp (algebraMap (coordField x) L)) (coordVec x k i)))
  rw [harch, ← hdeg]
  unfold height
  have h1 : (0 : ℝ) < finrank ℚ (coordField x) := by exact_mod_cast Module.finrank_pos
  have h2 : (0 : ℝ) < finrank (coordField x) L := by exact_mod_cast Module.finrank_pos
  push_cast
  field_simp
  rfl

/- English proof (translation)
Introduce `ι ι' _ _ _ _ n n' A A' x x' hx0 hx0' L _ hx hx' hfin harch`. Rewrite using `[height_eq_of_le A hx0 L hx, height_eq_of_le A' hx0' L hx', finsum_congr hfin, Finset.sum_congr rfl fun σ _ ↦ by rw [harch σ]]`.
-/
theorem heightLocalAgreement : HeightLocalAgreement.Statement := by
  intro ι ι' _ _ _ _ n n' A A' x x' hx0 hx0' L _ hx hx' hfin harch
  rw [height_eq_of_le A hx0 L hx, height_eq_of_le A' hx0' L hx', finsum_congr hfin,
    Finset.sum_congr rfl fun σ _ ↦ by rw [harch σ]]

end Cone

/- English proof (translation)
Use `symm`. Use `Fintype.sum_of_injective j hj _ _ (fun k' hk' ↦ ?_) (fun k ↦ ?_)` and prove the remaining obligations. Rewrite using `[Function.extend_apply' _ _ _ (fun ⟨k, hk⟩ ↦ hk' ⟨k, hk⟩), Pi.zero_apply, Int.cast_zero, zero_mul]`. Rewrite using `[hj.extend_apply]`.
-/
theorem sum_extend_mul {ι ι' : Type} [Fintype ι] [Fintype ι'] {j : ι → ι'}
    (hj : Function.Injective j) (a : ι → ℤ) (r : ι' → ℝ) :
    ∑ k', ((Function.extend j a 0 k' : ℤ) : ℝ) * r k' = ∑ k, (a k : ℝ) * r (j k) := by
  classical
  symm
  refine Fintype.sum_of_injective j hj _ _ (fun k' hk' ↦ ?_) (fun k ↦ ?_)
  · rw [Function.extend_apply' _ _ _ (fun ⟨k, hk⟩ ↦ hk' ⟨k, hk⟩), Pi.zero_apply, Int.cast_zero,
      zero_mul]
  · rw [hj.extend_apply]

/- English proof (translation)
Introduce `ι ι' _ _ _ _ n' j hj A x hx`. Establish `hxL : ∀ k i, x k i ∈ coordField x` using `fun k i ↦ IntermediateField.subset_adjoin ℚ _ ⟨⟨k, i⟩, rfl⟩`. Establish `hpL : ∀ k i, HermLine.project j x k i ∈ coordField x` using `fun k i ↦ hxL (j k) i`. Use `heightLocalAgreement ι' ι n' (n' ∘ j) (A.pullback j hj) A x (HermLine.project j x) hx (fun k ↦ hx (j k)) (coordField x) hxL hpL (fun v ↦ ?_) (fun σ ↦ rfl)` and prove the remaining obligations. Unfold `finiteTerm`.

Conclude with `sum_extend_mul hj A.deg (fun k' ↦ Real.log (⨆ i, v (coordIn (coordField x) x hxL k' i)))`.
-/
theorem heightPullback : HeightPullback.Statement := by
  intro ι ι' _ _ _ _ n' j hj A x hx
  have hxL : ∀ k i, x k i ∈ coordField x := fun k i ↦
    IntermediateField.subset_adjoin ℚ _ ⟨⟨k, i⟩, rfl⟩
  have hpL : ∀ k i, HermLine.project j x k i ∈ coordField x := fun k i ↦ hxL (j k) i
  refine heightLocalAgreement ι' ι n' (n' ∘ j) (A.pullback j hj) A x (HermLine.project j x) hx
    (fun k ↦ hx (j k)) (coordField x) hxL hpL (fun v ↦ ?_) (fun σ ↦ rfl)
  unfold finiteTerm
  exact sum_extend_mul hj A.deg (fun k' ↦ Real.log (⨆ i, v (coordIn (coordField x) x hxL k' i)))

end

end GroundTheory.Heights₂.Heights
