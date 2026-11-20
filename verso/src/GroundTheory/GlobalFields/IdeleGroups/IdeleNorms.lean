import Mathlib
import GroundTheory.GlobalFields.IdeleGroups.InfiniteProjInfiniteEmbeddingOfNe

namespace GroundTheory.Global

open NumberField IsDedekindDomain Topology Filter
open scoped NumberField.AdeleRing RestrictedProduct

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

namespace IdeleGroup

variable {K}

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem adele_fst_mul_apply (a b : 𝔸[K]) (w : InfinitePlace K) :
    (a * b).1 w = a.1 w * b.1 w := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem adele_snd_mul_apply (a b : 𝔸[K]) (v : HeightOneSpectrum (𝓞 K)) :
    (a * b).2 v = a.2 v * b.2 v := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem adele_fst_one_apply (w : InfinitePlace K) : (1 : 𝔸[K]).1 w = 1 := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem adele_snd_one_apply (v : HeightOneSpectrum (𝓞 K)) : (1 : 𝔸[K]).2 v = 1 := rfl

/- English proof (translation)
Establish `ha' : ‖a‖ ≤ 1` using `(Valued.toNormedField.norm_le_one_iff).2 ((HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 K) K v).1 ha)`. Establish `hb' : ‖b‖ ≤ 1` using `(Valued.toNormedField.norm_le_one_iff).2 ((HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 K) K v).1 hb)`. Establish `h1 : ‖a‖ * ‖b‖ = 1` using `by rw [← norm_mul, hab, norm_one]`. Use polynomial arithmetic with `[norm_nonneg a, norm_nonneg b]`.
-/
theorem norm_eq_one_of_mul_eq_one {v : HeightOneSpectrum (𝓞 K)} {a b : v.adicCompletion K}
    (hab : a * b = 1) (ha : a ∈ v.adicCompletionIntegers K)
    (hb : b ∈ v.adicCompletionIntegers K) : ‖a‖ = 1 := by
  have ha' : ‖a‖ ≤ 1 := (Valued.toNormedField.norm_le_one_iff).2
    ((HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 K) K v).1 ha)
  have hb' : ‖b‖ ≤ 1 := (Valued.toNormedField.norm_le_one_iff).2
    ((HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 K) K v).1 hb)
  have h1 : ‖a‖ * ‖b‖ = 1 := by rw [← norm_mul, hab, norm_one]
  nlinarith [norm_nonneg a, norm_nonneg b]

/- English proof (translation)
Establish `h : ((x : 𝔸[K]) * ((x⁻¹ : IdeleGroup K) : 𝔸[K])).2 v = 1` using `by simp`. Rewrite `h` using `[adele_snd_mul_apply]`. Then use the resulting hypothesis.
-/
theorem finite_mul_inv (x : IdeleGroup K) (v : HeightOneSpectrum (𝓞 K)) :
    (x : 𝔸[K]).2 v * ((x⁻¹ : IdeleGroup K) : 𝔸[K]).2 v = 1 := by
  have h : ((x : 𝔸[K]) * ((x⁻¹ : IdeleGroup K) : 𝔸[K])).2 v = 1 := by simp
  rwa [adele_snd_mul_apply] at h

/- English proof (translation)
Establish `h : ((x : 𝔸[K]) * ((x⁻¹ : IdeleGroup K) : 𝔸[K])).1 w = 1` using `by simp`. Rewrite `h` using `[adele_fst_mul_apply]`. Then use the resulting hypothesis.
-/
theorem infinite_mul_inv (x : IdeleGroup K) (w : InfinitePlace K) :
    (x : 𝔸[K]).1 w * ((x⁻¹ : IdeleGroup K) : 𝔸[K]).1 w = 1 := by
  have h : ((x : 𝔸[K]) * ((x⁻¹ : IdeleGroup K) : 𝔸[K])).1 w = 1 := by simp
  rwa [adele_fst_mul_apply] at h

/- English proof (translation)
The claim follows from `left_ne_zero_of_mul_eq_one (finite_mul_inv x v)`.
-/
theorem finite_ne_zero (x : IdeleGroup K) (v : HeightOneSpectrum (𝓞 K)) :
    (x : 𝔸[K]).2 v ≠ 0 :=
  left_ne_zero_of_mul_eq_one (finite_mul_inv x v)

/- English proof (translation)
The claim follows from `left_ne_zero_of_mul_eq_one (infinite_mul_inv x w)`.
-/
theorem infinite_ne_zero (x : IdeleGroup K) (w : InfinitePlace K) : (x : 𝔸[K]).1 w ≠ 0 :=
  left_ne_zero_of_mul_eq_one (infinite_mul_inv x w)

/- English proof (translation)
Use `filter_upwards [(x : 𝔸[K]).2.2, ((x⁻¹ : IdeleGroup K) : 𝔸[K]).2.2] with v h1 h2`. Conclude with `norm_eq_one_of_mul_eq_one (finite_mul_inv x v) h1 h2`.
-/
theorem eventually_norm_eq_one (x : IdeleGroup K) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 K) in cofinite, ‖(x : 𝔸[K]).2 v‖ = 1 := by
  filter_upwards [(x : 𝔸[K]).2.2, ((x⁻¹ : IdeleGroup K) : 𝔸[K]).2.2] with v h1 h2
  exact norm_eq_one_of_mul_eq_one (finite_mul_inv x v) h1 h2

/- English proof (translation)
The claim follows from `Filter.eventually_cofinite.1 (eventually_norm_eq_one x)`.
-/
theorem finite_mulSupport_norm (x : IdeleGroup K) :
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 K) ↦ ‖(x : 𝔸[K]).2 v‖).Finite :=
  Filter.eventually_cofinite.1 (eventually_norm_eq_one x)

def infiniteModule (x : IdeleGroup K) : ℝ :=
  ∏ w : InfinitePlace K, ‖(x : 𝔸[K]).1 w‖ ^ w.mult

def finiteModule (x : IdeleGroup K) : ℝ :=
  ∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖(x : 𝔸[K]).2 v‖

/- English proof (translation)
Simplify using `only [infiniteModule, Units.val_mul, adele_fst_mul_apply, norm_mul, mul_pow, Finset.prod_mul_distrib]`.
-/
theorem infiniteModule_mul (x y : IdeleGroup K) :
    infiniteModule (x * y) = infiniteModule x * infiniteModule y := by
  simp only [infiniteModule, Units.val_mul, adele_fst_mul_apply, norm_mul, mul_pow,
    Finset.prod_mul_distrib]

/- English proof (translation)
Simplify using `only [finiteModule, Units.val_mul, adele_snd_mul_apply, norm_mul]`. Conclude with `finprod_mul_distrib (finite_mulSupport_norm x) (finite_mulSupport_norm y)`.
-/
theorem finiteModule_mul (x y : IdeleGroup K) :
    finiteModule (x * y) = finiteModule x * finiteModule y := by
  simp only [finiteModule, Units.val_mul, adele_snd_mul_apply, norm_mul]
  exact finprod_mul_distrib (finite_mulSupport_norm x) (finite_mulSupport_norm y)

/- English proof (translation)
The claim follows from `Finset.prod_pos fun w _ ↦ pow_pos (norm_pos_iff.2 (infinite_ne_zero x w)) _`.
-/
theorem infiniteModule_pos (x : IdeleGroup K) : 0 < infiniteModule x :=
  Finset.prod_pos fun w _ ↦ pow_pos (norm_pos_iff.2 (infinite_ne_zero x w)) _

/- English proof (translation)
Rewrite using `[finiteModule, finprod_eq_prod _ (finite_mulSupport_norm x)]`. Conclude with `Finset.prod_pos fun v _ ↦ norm_pos_iff.2 (finite_ne_zero x v)`.
-/
theorem finiteModule_pos (x : IdeleGroup K) : 0 < finiteModule x := by
  rw [finiteModule, finprod_eq_prod _ (finite_mulSupport_norm x)]
  exact Finset.prod_pos fun v _ ↦ norm_pos_iff.2 (finite_ne_zero x v)

variable (K) in

def ideleModule : IdeleGroup K →* {r : ℝ // 0 < r} where
  toFun x := ⟨infiniteModule x * finiteModule x, mul_pos (infiniteModule_pos x) (finiteModule_pos x)⟩
  map_one' := by
    ext
    simp [infiniteModule, finiteModule]
  map_mul' x y := by
    ext
    simp only [Positive.val_mul, infiniteModule_mul, finiteModule_mul]
    ring

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem ideleModule_apply (x : IdeleGroup K) :
    (ideleModule K x : ℝ) = infiniteModule x * finiteModule x :=
  rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem ideleModule_eq (x : IdeleGroup K) :
    (ideleModule K x : ℝ) = (∏ w : InfinitePlace K, ‖(x : 𝔸[K]).1 w‖ ^ w.mult) *
      ∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖(x : 𝔸[K]).2 v‖ :=
  rfl

/- English proof (translation)
The claim follows from `continuous_finsetProd _ fun w _ ↦ (continuous_norm.comp (Units.continuous_val.comp (continuous_infiniteProj w))).pow _`.
-/
theorem continuous_infiniteModule : Continuous (infiniteModule (K := K)) :=
  continuous_finsetProd _ fun w _ ↦
    (continuous_norm.comp (Units.continuous_val.comp (continuous_infiniteProj w))).pow _

/- English proof (translation)
The claim follows from `finprod_eq_one_of_forall_eq_one fun v ↦ norm_eq_one_of_mul_eq_one (finite_mul_inv x v) ((mem_standardOpenSubgroup K).1 hx v).1 ((mem_standardOpenSubgroup K).1 hx v).2`.
-/
theorem finiteModule_eq_one_of_mem {x : IdeleGroup K} (hx : x ∈ standardOpenSubgroup K) :
    finiteModule x = 1 :=
  finprod_eq_one_of_forall_eq_one fun v ↦
    norm_eq_one_of_mul_eq_one (finite_mul_inv x v) ((mem_standardOpenSubgroup K).1 hx v).1
      ((mem_standardOpenSubgroup K).1 hx v).2

/- English proof (translation)
Use `continuous_iff_continuousAt.2 fun x ↦ ?_` and prove the remaining obligations. Establish `hU : (fun y ↦ x⁻¹ * y) ⁻¹' (standardOpenSubgroup K : Set (IdeleGroup K)) ∈ 𝓝 x` using `((isOpen_standardOpenSubgroup K).preimage (continuous_const.mul continuous_id)).mem_nhds (by simp [(standardOpenSubgroup K).one_mem])`. Use `(continuousAt_const (y := finiteModule x)).congr ?_` and prove the remaining obligations. Use `filter_upwards [hU] with y hy`. Rewrite using `[← mul_inv_cancel_left x y, finiteModule_mul, finiteModule_eq_one_of_mem hy, mul_one]`.
-/
theorem continuous_finiteModule : Continuous (finiteModule (K := K)) := by
  refine continuous_iff_continuousAt.2 fun x ↦ ?_
  have hU : (fun y ↦ x⁻¹ * y) ⁻¹' (standardOpenSubgroup K : Set (IdeleGroup K)) ∈ 𝓝 x :=
    ((isOpen_standardOpenSubgroup K).preimage (continuous_const.mul continuous_id)).mem_nhds
      (by simp [(standardOpenSubgroup K).one_mem])
  refine (continuousAt_const (y := finiteModule x)).congr ?_
  filter_upwards [hU] with y hy
  rw [← mul_inv_cancel_left x y, finiteModule_mul, finiteModule_eq_one_of_mem hy, mul_one]

/- English proof (translation)
The claim follows from `(continuous_infiniteModule.mul continuous_finiteModule).subtype_mk _`.
-/
theorem continuous_ideleModule : Continuous (ideleModule K) :=
  (continuous_infiniteModule.mul continuous_finiteModule).subtype_mk _

/- English proof (translation)
Rewrite using `[ideleModule_eq, coe_infiniteEmbedding]`. Establish `h1 : ∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖((infiniteAdeleSingle w (z : w.Completion), (1 : FiniteAdeleRing (𝓞 K) K)) : 𝔸[K]).2 v‖ = 1` using `finprod_eq_one_of_forall_eq_one fun v ↦ norm_one`. Rewrite using `[h1, mul_one]`. Use `(Fintype.prod_eq_single w fun u hu ↦ ?_).trans ?_` and prove the remaining obligations. Simplify using `[infiniteAdeleSingle_apply, Pi.mulSingle_eq_of_ne hu]`.

Simplify using `[infiniteAdeleSingle_apply]`.
-/
theorem ideleModule_infiniteEmbedding (w : InfinitePlace K) (z : (w.Completion)ˣ) :
    (ideleModule K (infiniteEmbedding w z) : ℝ) = ‖(z : w.Completion)‖ ^ w.mult := by
  classical
  rw [ideleModule_eq, coe_infiniteEmbedding]
  have h1 : ∏ᶠ v : HeightOneSpectrum (𝓞 K),
      ‖((infiniteAdeleSingle w (z : w.Completion), (1 : FiniteAdeleRing (𝓞 K) K)) : 𝔸[K]).2 v‖
      = 1 :=
    finprod_eq_one_of_forall_eq_one fun v ↦ norm_one
  rw [h1, mul_one]
  refine (Fintype.prod_eq_single w fun u hu ↦ ?_).trans ?_
  · simp [infiniteAdeleSingle_apply, Pi.mulSingle_eq_of_ne hu]
  · simp [infiniteAdeleSingle_apply]

/- English proof (translation)
Rewrite using `[ideleModule_eq, coe_finiteEmbedding]`. Establish `h1 : ∏ w : InfinitePlace K, ‖((1 : InfiniteAdeleRing K), finiteAdeleSingle v (z : v.adicCompletion K)).1 w‖ ^ w.mult = 1` using `Finset.prod_eq_one fun w _ ↦ (by rw [norm_one, one_pow] : ‖(1 : w.Completion)‖ ^ w.mult = 1)`. Rewrite using `[h1, one_mul]`. Use `(finprod_eq_single _ v fun u hu ↦ ?_).trans ?_` and prove the remaining obligations. Simplify using `[finiteAdeleSingle_apply_of_ne hu]`.

Simplify using the standard rewrite rules.
-/
theorem ideleModule_finiteEmbedding (v : HeightOneSpectrum (𝓞 K)) (z : (v.adicCompletion K)ˣ) :
    (ideleModule K (finiteEmbedding v z) : ℝ) = ‖(z : v.adicCompletion K)‖ := by
  rw [ideleModule_eq, coe_finiteEmbedding]
  have h1 : ∏ w : InfinitePlace K,
      ‖((1 : InfiniteAdeleRing K), finiteAdeleSingle v (z : v.adicCompletion K)).1 w‖ ^ w.mult
      = 1 :=
    Finset.prod_eq_one fun w _ ↦ (by rw [norm_one, one_pow] : ‖(1 : w.Completion)‖ ^ w.mult = 1)
  rw [h1, one_mul]
  refine (finprod_eq_single _ v fun u hu ↦ ?_).trans ?_
  · simp [finiteAdeleSingle_apply_of_ne hu]
  · simp

/- English proof (translation)
Take `⟨w⟩ : Nonempty (InfinitePlace K)` from `inferInstance`. Introduce and unpack `⟨t, ht⟩`. Choose the witnesses or unpack the hypotheses as in `⟨z, hz0, hz⟩ : ∃ z : w.Completion, z ≠ 0 ∧ ‖z‖ ^ w.mult = t := by`. Break down `w.isReal_or_isComplex with hw | hw` into its components or cases. Set `e` to `InfinitePlace.Completion.ringEquivRealOfIsReal hw`.

Use `⟨e.symm t, (map_ne_zero_iff _ e.symm.injective).2 ht.ne', ?_⟩` and prove the remaining obligations. Establish `hn : ‖e.symm t‖ = ‖e (e.symm t)‖`. Rewrite using `[InfinitePlace.Completion.ringEquivRealOfIsReal_apply]`. Conclude with `((InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero (map_zero _) _).symm`. Rewrite using `[hn, RingEquiv.apply_symm_apply, Real.norm_of_nonneg ht.le]`.

Simplify using `[InfinitePlace.mult, hw]`. Set `e` to `InfinitePlace.Completion.ringEquivComplexOfIsComplex hw`. Use `⟨e.symm (Real.sqrt t : ℂ), (map_ne_zero_iff _ e.symm.injective).2 (Complex.ofReal_ne_zero.2 (Real.sqrt_ne_zero'.2 ht)), ?_⟩` and prove the remaining obligations. Establish `hn : ‖e.symm (Real.sqrt t : ℂ)‖ = ‖e (e.symm (Real.sqrt t : ℂ))‖`. Rewrite using `[InfinitePlace.Completion.ringEquivComplexOfIsComplex_apply]`.

Conclude with `((InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) _).symm`. Establish `hw' : ¬ w.IsReal` using `InfinitePlace.not_isReal_iff_isComplex.2 hw`. Rewrite using `[hn, RingEquiv.apply_symm_apply, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg t)]`. Simplify using `[InfinitePlace.mult, hw', Real.sq_sqrt ht.le]`. Use `⟨infiniteEmbedding w (Units.mk0 z hz0), Subtype.ext ?_⟩` and prove the remaining obligations.

Rewrite using `[ideleModule_infiniteEmbedding, Units.val_mk0, hz]`.
-/
theorem ideleModule_surjective : Function.Surjective (ideleModule K) := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace K) := inferInstance
  rintro ⟨t, ht⟩
  obtain ⟨z, hz0, hz⟩ : ∃ z : w.Completion, z ≠ 0 ∧ ‖z‖ ^ w.mult = t := by
    rcases w.isReal_or_isComplex with hw | hw
    · let e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
      refine ⟨e.symm t, (map_ne_zero_iff _ e.symm.injective).2 ht.ne', ?_⟩
      have hn : ‖e.symm t‖ = ‖e (e.symm t)‖ := by
        rw [InfinitePlace.Completion.ringEquivRealOfIsReal_apply]
        exact ((InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero
          (map_zero _) _).symm
      rw [hn, RingEquiv.apply_symm_apply, Real.norm_of_nonneg ht.le]
      simp [InfinitePlace.mult, hw]
    · let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex hw
      refine ⟨e.symm (Real.sqrt t : ℂ), (map_ne_zero_iff _ e.symm.injective).2
        (Complex.ofReal_ne_zero.2 (Real.sqrt_ne_zero'.2 ht)), ?_⟩
      have hn : ‖e.symm (Real.sqrt t : ℂ)‖ = ‖e (e.symm (Real.sqrt t : ℂ))‖ := by
        rw [InfinitePlace.Completion.ringEquivComplexOfIsComplex_apply]
        exact ((InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero
          (map_zero _) _).symm
      have hw' : ¬ w.IsReal := InfinitePlace.not_isReal_iff_isComplex.2 hw
      rw [hn, RingEquiv.apply_symm_apply, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg t)]
      simp [InfinitePlace.mult, hw', Real.sq_sqrt ht.le]
  refine ⟨infiniteEmbedding w (Units.mk0 z hz0), Subtype.ext ?_⟩
  rw [ideleModule_infiniteEmbedding, Units.val_mk0, hz]

/- English proof (translation)
Use `Finset.prod_congr rfl fun w _ ↦ ?_` and prove the remaining obligations. Use `congr 1`. Conclude with `InfinitePlace.Completion.norm_coe (K := K) (v := w) _`.
-/
theorem infiniteModule_diagonal (k : Kˣ) :
    infiniteModule (diagonal K k) = ∏ w : InfinitePlace K, w (k : K) ^ w.mult := by
  refine Finset.prod_congr rfl fun w _ ↦ ?_
  congr 1
  exact InfinitePlace.Completion.norm_coe (K := K) (v := w) _

/- English proof (translation)
Rewrite using `[← finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm]`. Simplify using `only [FinitePlace.equivHeightOneSpectrum_symm_apply]`. Both sides reduce to the same expression.
-/
theorem finiteModule_diagonal (k : Kˣ) :
    finiteModule (diagonal K k) = ∏ᶠ w : FinitePlace K, w (k : K) := by
  rw [← finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm]
  simp only [FinitePlace.equivHeightOneSpectrum_symm_apply]
  rfl

/- English proof (translation)
Use `Subtype.ext ?_` and prove the remaining obligations. Rewrite using `[ideleModule_apply, infiniteModule_diagonal, finiteModule_diagonal, Positive.val_one]`. Conclude with `prod_abs_eq_one k.ne_zero`.
-/
theorem ideleModule_diagonal (k : Kˣ) : ideleModule K (diagonal K k) = 1 := by
  refine Subtype.ext ?_
  rw [ideleModule_apply, infiniteModule_diagonal, finiteModule_diagonal, Positive.val_one]
  exact prod_abs_eq_one k.ne_zero

variable (K) in

def normOneSubgroup : Subgroup (IdeleGroup K) := (ideleModule K).ker

/- English proof (translation)
Rewrite using `[normOneSubgroup, MonoidHom.mem_ker]`. Conclude with `⟨fun h ↦ by rw [h, Positive.val_one], fun h ↦ Subtype.ext (h.trans Positive.val_one.symm)⟩`.
-/
theorem mem_normOneSubgroup {x : IdeleGroup K} :
    x ∈ normOneSubgroup K ↔ (ideleModule K x : ℝ) = 1 := by
  rw [normOneSubgroup, MonoidHom.mem_ker]
  exact ⟨fun h ↦ by rw [h, Positive.val_one], fun h ↦ Subtype.ext (h.trans Positive.val_one.symm)⟩

variable (K) in

/- English proof (translation)
Establish `h : (normOneSubgroup K : Set (IdeleGroup K)) = (fun x ↦ (ideleModule K x : ℝ)) ⁻¹' {1}`. Use extensionality with `x`. Conclude with `mem_normOneSubgroup`. Rewrite using `[h]`. Conclude with `isClosed_singleton.preimage (continuous_subtype_val.comp continuous_ideleModule)`.
-/
theorem isClosed_normOneSubgroup : IsClosed (normOneSubgroup K : Set (IdeleGroup K)) := by
  have h : (normOneSubgroup K : Set (IdeleGroup K)) =
      (fun x ↦ (ideleModule K x : ℝ)) ⁻¹' {1} := by
    ext x
    exact mem_normOneSubgroup
  rw [h]
  exact isClosed_singleton.preimage (continuous_subtype_val.comp continuous_ideleModule)

variable (K) in

/- English proof (translation)
Introduce and unpack `_ ⟨k, rfl⟩`. Conclude with `ideleModule_diagonal k`.
-/
theorem range_diagonal_le_normOneSubgroup : (diagonal K).range ≤ normOneSubgroup K := by
  rintro _ ⟨k, rfl⟩
  exact ideleModule_diagonal k

end IdeleGroup

namespace IdeleClassGroup

def ideleModule : IdeleClassGroup K →* {r : ℝ // 0 < r} :=
  QuotientGroup.lift _ (IdeleGroup.ideleModule K) (IdeleGroup.range_diagonal_le_normOneSubgroup K)

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem ideleModule_mk (x : IdeleGroup K) :
    ideleModule K (mk K x) = IdeleGroup.ideleModule K x :=
  rfl

/- English proof (translation)
The claim follows from `(QuotientGroup.isQuotientMap_mk _).continuous_iff.2 (IdeleGroup.continuous_ideleModule (K := K))`.
-/
theorem continuous_ideleModule : Continuous (ideleModule K) :=
  (QuotientGroup.isQuotientMap_mk _).continuous_iff.2 (IdeleGroup.continuous_ideleModule (K := K))

/- English proof (translation)
The claim follows from `fun t ↦ let ⟨x, hx⟩ := IdeleGroup.ideleModule_surjective (K := K) t ⟨mk K x, hx⟩`.
-/
theorem ideleModule_surjective : Function.Surjective (ideleModule K) := fun t ↦
  let ⟨x, hx⟩ := IdeleGroup.ideleModule_surjective (K := K) t
  ⟨mk K x, hx⟩

def normOneSubgroup : Subgroup (IdeleClassGroup K) := (ideleModule K).ker

/- English proof (translation)
Use extensionality with `c`. Take `⟨x, rfl⟩` from `mk_surjective K c`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Conclude with `⟨x, hx, rfl⟩`.

Introduce and unpack `⟨y, hy, hyx⟩`. Express the relevant statement in the definitionally equal form `ideleModule K (mk K x) = 1`. Rewrite using `[← hyx]`. Conclude with `hy`.
-/
theorem normOneSubgroup_eq_map :
    normOneSubgroup K = (IdeleGroup.normOneSubgroup K).map (mk K) := by
  ext c
  obtain ⟨x, rfl⟩ := mk_surjective K c
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    change ideleModule K (mk K x) = 1
    rw [← hyx]
    exact hy

end IdeleClassGroup

end

end GroundTheory.Global
