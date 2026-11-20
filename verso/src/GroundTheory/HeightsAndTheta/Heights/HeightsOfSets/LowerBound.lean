import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.FiniteSupportHeight
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

section Local

variable {K : Type*} [Field K] [NumberField K]

/- English proof (translation)
The claim follows from `fun a b ↦ v.add_le a b`.
-/
theorem finitePlace_isNonarchimedean (v : FinitePlace K) : IsNonarchimedean (⇑v) :=
  fun a b ↦ v.add_le a b

/- English proof (translation)
Establish `h1` using `congrFun h k`. Rewrite `h1` using `[Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply]`. Rewrite using `[← h1, Fintype.sum_sigma]`. Simplify using `only [coordDeg, Pi.smul_apply, smul_eq_mul, Pi.single_apply]`. Rewrite using `[Finset.sum_eq_single k]`.

Simplify using the standard rewrite rules. Introduce `b _ hb`. Simplify using `[Ne.symm hb]`. Simplify using the standard rewrite rules.
-/
theorem sum_block_exponents {m : Coord n →₀ ℕ} {δ : ι → ℕ}
    (h : Finsupp.weight (coordDeg n) m = δ) (k : ι) :
    ∑ i : Fin (n k + 1), m ⟨k, i⟩ = δ k := by
  classical
  have h1 := congrFun h k
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply] at h1
  rw [← h1, Fintype.sum_sigma]
  simp only [coordDeg, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  rw [Finset.sum_eq_single k]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

/- English proof (translation)
Rewrite using `[map_prod]`. Repeatedly rewrite using `[map_pow]`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.prod_le_prod (fun p _ ↦ pow_nonneg (apply_nonneg v _) _) fun p _ ↦ ?_` and prove the remaining obligations. Conclude with `pow_le_pow_left₀ (apply_nonneg v _) (le_ciSup (f := fun i ↦ v (y p.1 i)) (Set.finite_range _).bddAbove p.2) _`.

Use `_ = ∏ p : Coord n, (⨆ i, v (y p.1 i)) ^ m p := by`. Use `Finset.prod_subset (Finset.subset_univ _) fun p _ hp ↦ ?_` and prove the remaining obligations. Rewrite using `[Finsupp.notMem_support_iff.mp hp, pow_zero]`. Use `_ = ∏ k, (⨆ i, v (y k i)) ^ δ k := by`. Rewrite using `[Fintype.prod_sigma]`.

Use `Finset.prod_congr rfl fun k _ ↦ ?_` and prove the remaining obligations. Use `show ∏ i, (⨆ j, v (y k j)) ^ m ⟨k, i⟩ = _`. Rewrite using `[Finset.prod_pow_eq_pow_sum, sum_block_exponents hm k]`.
-/
theorem finitePlace_monomial_le (v : FinitePlace K) (y : Cone n K) {m : Coord n →₀ ℕ} {δ : ι → ℕ}
    (hm : Finsupp.weight (coordDeg n) m = δ) :
    v (∏ p ∈ m.support, y p.1 p.2 ^ m p) ≤ ∏ k, (⨆ i, v (y k i)) ^ δ k := by
  classical
  rw [map_prod]
  simp_rw [map_pow]
  calc ∏ p ∈ m.support, v (y p.1 p.2) ^ m p
      ≤ ∏ p ∈ m.support, (⨆ i, v (y p.1 i)) ^ m p := by
        refine Finset.prod_le_prod (fun p _ ↦ pow_nonneg (apply_nonneg v _) _) fun p _ ↦ ?_
        exact pow_le_pow_left₀ (apply_nonneg v _)
          (le_ciSup (f := fun i ↦ v (y p.1 i)) (Set.finite_range _).bddAbove p.2) _
    _ = ∏ p : Coord n, (⨆ i, v (y p.1 i)) ^ m p := by
        refine Finset.prod_subset (Finset.subset_univ _) fun p _ hp ↦ ?_
        rw [Finsupp.notMem_support_iff.mp hp, pow_zero]
    _ = ∏ k, (⨆ i, v (y k i)) ^ δ k := by
        rw [Fintype.prod_sigma]
        refine Finset.prod_congr rfl fun k _ ↦ ?_
        show ∏ i, (⨆ j, v (y k j)) ^ m ⟨k, i⟩ = _
        rw [Finset.prod_pow_eq_pow_sum, sum_block_exponents hm k]

/- English proof (translation)
Establish `hR : 0 ≤ ∏ k, (⨆ i, v (y k i)) ^ δ k` using `Finset.prod_nonneg fun k _ ↦ pow_nonneg (Real.iSup_nonneg fun i ↦ apply_nonneg v _) _`. Break down `eq_or_ne f 0 with rfl | hf0` into its components or cases. Simplify `hR` using `[evalCone]`. Rewrite using `[evalCone, eval₂_eq]`. Take `⟨m, hm, hle⟩` from `(finitePlace_isNonarchimedean v).finset_image_add_of_nonempty (fun d ↦ (Int.castRingHom K) (coeff d f) * ∏ p ∈ d.support, y p.1 p.2 ^ d p) (support_nonempty.mpr hf0)`.

Use `hle.trans ?_` and prove the remaining obligations. Rewrite using `[map_mul]`. Establish `h1 : v ((Int.castRingHom K) (coeff m f)) ≤ 1`. Rewrite using `[eq_intCast]`. Conclude with `(finitePlace_isNonarchimedean v).apply_intCast_le_one`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem finitePlace_evalCone_le (v : FinitePlace K) (y : Cone n K) {f : MvPolynomial (Coord n) ℤ}
    {δ : ι → ℕ} (hf : IsWeightedHomogeneous (coordDeg n) f δ) :
    v (evalCone y f) ≤ ∏ k, (⨆ i, v (y k i)) ^ δ k := by
  classical
  have hR : 0 ≤ ∏ k, (⨆ i, v (y k i)) ^ δ k :=
    Finset.prod_nonneg fun k _ ↦ pow_nonneg (Real.iSup_nonneg fun i ↦ apply_nonneg v _) _
  rcases eq_or_ne f 0 with rfl | hf0
  · simpa [evalCone] using hR
  rw [evalCone, eval₂_eq]
  obtain ⟨m, hm, hle⟩ := (finitePlace_isNonarchimedean v).finset_image_add_of_nonempty
    (fun d ↦ (Int.castRingHom K) (coeff d f) * ∏ p ∈ d.support, y p.1 p.2 ^ d p)
    (support_nonempty.mpr hf0)
  refine hle.trans ?_
  rw [map_mul]
  have h1 : v ((Int.castRingHom K) (coeff m f)) ≤ 1 := by
    rw [eq_intCast]
    exact (finitePlace_isNonarchimedean v).apply_intCast_le_one
  calc v ((Int.castRingHom K) (coeff m f)) * v (∏ p ∈ m.support, y p.1 p.2 ^ m p)
      ≤ 1 * ∏ k, (⨆ i, v (y k i)) ^ δ k :=
        mul_le_mul h1 (finitePlace_monomial_le v y (hf (mem_support_iff.mp hm)))
          (apply_nonneg v _) zero_le_one
    _ = _ := one_mul _

/- English proof (translation)
Establish `hfin : (Function.mulSupport fun w : FinitePlace K ↦ w t).Finite` using `FinitePlace.hasFiniteMulSupport ht`. Establish `hprod` using `FinitePlace.prod_eq_inv_abs_norm ht`. Rewrite `hprod` using `[finprod_eq_prod_of_mulSupport_subset (s := hfin.toFinset) _ (fun w hw ↦ Finset.mem_coe.mpr (hfin.mem_toFinset.mpr hw))]`. Establish `h1 : (∑ᶠ v : FinitePlace K, Real.log (v t)) = Real.log (|(Algebra.norm ℚ t : ℝ)|⁻¹)`. Rewrite using `[finsum_eq_sum_of_support_subset (s := hfin.toFinset)]`.

Rewrite using `[← Real.log_prod, hprod]`. Simplify using the standard rewrite rules. Introduce `w _`. Conclude with `(FinitePlace.pos_iff.mpr ht).ne'`. Introduce `w hw`.

Establish `h1' : w t ≠ 1` using `fun h ↦ hw (by show Real.log (w t) = 0; rw [h, Real.log_one])`. Conclude with `Finset.mem_coe.mpr (hfin.mem_toFinset.mpr h1')`. Establish `h2 : ∑ σ : K →+* ℂ, Real.log ‖σ t‖ = Real.log |(Algebra.norm ℚ t : ℝ)|`. Rewrite using `[← Real.log_prod (fun σ _ ↦ norm_ne_zero_iff.mpr ((map_ne_zero σ).mpr ht))]`. Use `congr 1`.

Establish `h3` using `Algebra.norm_eq_prod_embeddings ℚ ℂ t`. Establish `h4 : ∏ σ : K →+* ℂ, σ t = ∏ σ : K →ₐ[ℚ] ℂ, σ t` using `Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) _ _ fun σ ↦ rfl`. Rewrite using `[← norm_prod, h4, ← h3, eq_ratCast, Complex.norm_ratCast]`. Rewrite using `[h1, h2, Real.log_inv, neg_add_cancel]`.
-/
theorem sum_log_finitePlace_add_sum_log_embedding {t : K} (ht : t ≠ 0) :
    (∑ᶠ v : FinitePlace K, Real.log (v t)) + ∑ σ : K →+* ℂ, Real.log ‖σ t‖ = 0 := by
  have hfin : (Function.mulSupport fun w : FinitePlace K ↦ w t).Finite :=
    FinitePlace.hasFiniteMulSupport ht
  have hprod := FinitePlace.prod_eq_inv_abs_norm ht
  rw [finprod_eq_prod_of_mulSupport_subset (s := hfin.toFinset) _
    (fun w hw ↦ Finset.mem_coe.mpr (hfin.mem_toFinset.mpr hw))] at hprod
  have h1 : (∑ᶠ v : FinitePlace K, Real.log (v t)) = Real.log (|(Algebra.norm ℚ t : ℝ)|⁻¹) := by
    rw [finsum_eq_sum_of_support_subset (s := hfin.toFinset)]
    · rw [← Real.log_prod, hprod]
      · simp
      · intro w _
        exact (FinitePlace.pos_iff.mpr ht).ne'
    · intro w hw
      have h1' : w t ≠ 1 := fun h ↦ hw (by show Real.log (w t) = 0; rw [h, Real.log_one])
      exact Finset.mem_coe.mpr (hfin.mem_toFinset.mpr h1')
  have h2 : ∑ σ : K →+* ℂ, Real.log ‖σ t‖ = Real.log |(Algebra.norm ℚ t : ℝ)| := by
    rw [← Real.log_prod (fun σ _ ↦ norm_ne_zero_iff.mpr ((map_ne_zero σ).mpr ht))]
    congr 1
    have h3 := Algebra.norm_eq_prod_embeddings ℚ ℂ t
    have h4 : ∏ σ : K →+* ℂ, σ t = ∏ σ : K →ₐ[ℚ] ℂ, σ t :=
      Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) _ _ fun σ ↦ rfl
    rw [← norm_prod, h4, ← h3, eq_ratCast, Complex.norm_ratCast]
  rw [h1, h2, Real.log_inv, neg_add_cancel]

end Local

/- English proof (translation)
Establish `hmem : den * (e * chartMonomial c' d' - e' * chartMonomial c d) ∈ P.ideal`. Establish `: den * (e * chartMonomial c' d' - e' * chartMonomial c d) = (den * e - num * chartMonomial c d) * chartMonomial c' d' - (den * e' - num * chartMonomial c' d') * chartMonomial c d` using `by ring`. Rewrite using `[this]`. Conclude with `P.ideal.sub_mem (P.ideal.mul_mem_right _ he.2) (P.ideal.mul_mem_right _ he'.2)`. Establish `h2` using `(P.isPrime.mem_or_mem hmem).resolve_left hden`.

Establish `h3` using `hz.2 _ h2`. Simplify using `only [evalCone, eval₂_sub, eval₂_mul] at h3 ⊢`. Conclude with `sub_eq_zero.mp h3`.
-/
theorem chartForm_agree {P : ArithVariety n} {a : ι → ℤ} {num den : MvPolynomial (Coord n) ℤ}
    (hden : den ∉ P.ideal) {c c' : (k : ι) → Fin (n k + 1)} {d d' : ι → ℕ}
    {e e' : MvPolynomial (Coord n) ℤ} (he : IsChartForm P a num den c d e)
    (he' : IsChartForm P a num den c' d' e') {F : Type*} [CommRing F] {z : Cone n F}
    (hz : z ∈ P.points F) :
    evalCone z e * evalCone z (chartMonomial c' d') = evalCone z e' * evalCone z (chartMonomial c d) := by
  have hmem : den * (e * chartMonomial c' d' - e' * chartMonomial c d) ∈ P.ideal := by
    have : den * (e * chartMonomial c' d' - e' * chartMonomial c d) =
        (den * e - num * chartMonomial c d) * chartMonomial c' d' -
          (den * e' - num * chartMonomial c' d') * chartMonomial c d := by ring
    rw [this]
    exact P.ideal.sub_mem (P.ideal.mul_mem_right _ he.2) (P.ideal.mul_mem_right _ he'.2)
  have h2 := (P.isPrime.mem_or_mem hmem).resolve_left hden
  have h3 := hz.2 _ h2
  simp only [evalCone, eval₂_sub, eval₂_mul] at h3 ⊢
  exact sub_eq_zero.mp h3

omit [Fintype ι] in

/- English proof (translation)
Establish `hval : ∀ f, (coordField x).val.toRingHom (evalCone (coordVec x) f) = evalCone x f` using `fun f ↦ (evalCone_map (coordField x).val.toRingHom (coordVec x) f).symm`. Use `⟨fun k h ↦ hx.1 k ?_, fun f hf ↦ ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Establish `: coordVec x k i = 0` using `congrFun h i`. Conclude with `congrArg Subtype.val this`.

Apply `(coordField x).val.toRingHom.injective` to reduce the goal to its premises. Rewrite using `[hval, map_zero]`. Conclude with `hx.2 f hf`.
-/
theorem coordVec_mem_points {P : ArithVariety n} {x : Cone n (AlgebraicClosure ℚ)}
    (hx : x ∈ P.points (AlgebraicClosure ℚ)) : coordVec x ∈ P.points (coordField x) := by
  have hval : ∀ f, (coordField x).val.toRingHom (evalCone (coordVec x) f) = evalCone x f :=
    fun f ↦ (evalCone_map (coordField x).val.toRingHom (coordVec x) f).symm
  refine ⟨fun k h ↦ hx.1 k ?_, fun f hf ↦ ?_⟩
  · funext i
    have : coordVec x k i = 0 := congrFun h i
    exact congrArg Subtype.val this
  · apply (coordField x).val.toRingHom.injective
    rw [hval, map_zero]
    exact hx.2 f hf

/- English proof (translation)
Use `set K := coordField x`. Use `set y := coordVec x with hydef`. Establish `hy : y ∈ P.points K` using `coordVec_mem_points hx`. Establish `hval : ∀ f, K.val.toRingHom (evalCone y f) = evalCone x f` using `fun f ↦ (evalCone_map K.val.toRingHom y f).symm`. Establish `hyc : ∀ k, y k (c k) ≠ 0` using `fun k h ↦ hc k (congrArg Subtype.val h)`.

Establish `hey : evalCone y e ≠ 0` using `fun h ↦ hex (by rw [← hval, h, map_zero])`. Establish `hmy : evalCone y (chartMonomial c d) ≠ 0`. Rewrite using `[evalCone_chartMonomial]`. Conclude with `Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hyc k)`. Use `set t : K := evalCone y e / evalCone y (chartMonomial c d) with htdef`.

Establish `ht : t ≠ 0` using `div_ne_zero hey hmy`. Establish `hfin : ∀ v : FinitePlace K, Real.log (v t) ≤ ∑ k, (A.deg k : ℝ) * Real.log (⨆ i, v (y k i))`. Introduce `v`. Establish `hM : ∀ k, ∃ i, v (y k i) = ⨆ i, v (y k i)` using `fun k ↦ exists_eq_ciSup_of_finite`. Use `choose c' hc' using hM`.

Establish `hMpos : ∀ k, 0 < ⨆ i, v (y k i)`. Introduce `k`. Take `⟨i, hi⟩` from `Function.ne_iff.mp (hy.1 k)`. Conclude with `lt_of_lt_of_le (FinitePlace.pos_iff.mpr hi) (le_ciSup (f := fun i ↦ v (y k i)) (Set.finite_range _).bddAbove i)`. Establish `hyc' : ∀ k, y k (c' k) ≠ 0`.

Introduce `k h`. Use `hc' k` as an intermediate fact. Rewrite `this` using `[h, map_zero]`. Conclude with `(hMpos k).ne this`. Establish `hX : ∀ k, (X ⟨k, c' k⟩ : MvPolynomial (Coord n) ℤ) ∉ P.ideal`.

Introduce `k hk`. Apply `hyc' k` to reduce the goal to its premises. Use `hy.2 _ hk` as an intermediate fact. Simplify `this` using `[evalCone]`. Take `⟨d', e', he'⟩` from `s.regular c' hX`.

Establish `hagree` using `chartForm_agree s.den_not_mem he he' hy`. Establish `hm'y : evalCone y (chartMonomial c' d') ≠ 0`. Rewrite using `[evalCone_chartMonomial]`. Conclude with `Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hyc' k)`. Establish `ht' : t = evalCone y e' / evalCone y (chartMonomial c' d')`.

Rewrite using `[htdef, div_eq_div_iff hmy hm'y, hagree]`. Establish `he'y : evalCone y e' ≠ 0`. Introduce `h`. Rewrite `ht` using `[ht', h, zero_div]`. Conclude with `ht rfl`.

Take `⟨⟨δ, hδ, hδa⟩, _⟩` from `he'`. Establish `hvm : v (evalCone y (chartMonomial c' d')) = ∏ k, (⨆ i, v (y k i)) ^ d' k`. Rewrite using `[evalCone_chartMonomial, map_prod]`. Use `Finset.prod_congr rfl fun k _ ↦ ?_` and prove the remaining obligations. Rewrite using `[map_pow, hc' k]`.

Establish `hve` using `finitePlace_evalCone_le v y hδ`. Establish `hpos_e : 0 < v (evalCone y e')` using `FinitePlace.pos_iff.mpr he'y`. Rewrite using `[ht', map_div₀, Real.log_div hpos_e.ne' ((FinitePlace.pos_iff.mpr hm'y).ne'), hvm, Real.log_prod (fun k _ ↦ (pow_pos (hMpos k) _).ne')]`. Establish `hle : Real.log (v (evalCone y e')) ≤ ∑ k, (δ k : ℝ) * Real.log (⨆ i, v (y k i))`. Use `(Real.log_le_log hpos_e hve).trans ?_` and prove the remaining obligations.

Rewrite using `[Real.log_prod (fun k _ ↦ (pow_pos (hMpos k) _).ne')]`. Simplify using `only [Real.log_pow, le_refl]`. Simplify using `only [Real.log_pow]`. Rewrite using `[← sub_nonneg]`. Establish `hsum : ∑ k, (A.deg k : ℝ) * Real.log (⨆ i, v (y k i)) - (Real.log (v (evalCone y e')) - ∑ k, (d' k : ℝ) * Real.log (⨆ i, v (y k i))) = ∑ k, (δ k : ℝ) * Real.log (⨆ i, v (y k i)) - Real.log (v (evalCone y e'))`.

Establish `hd : ∀ k, (δ k : ℝ) = (A.deg k : ℝ) + (d' k : ℝ)` using `fun k ↦ by exact_mod_cast hδa k`. Simplify using `only [hd, add_mul, Finset.sum_add_distrib]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hsum]`. Conclude with `sub_nonneg.mpr hle`.

Establish `harch : ∀ σ : K →+* ℂ, Real.log ‖σ t‖ ≤ C + Real.log (A.metric fun k i ↦ σ (y k i))`. Introduce `σ`. Use `set z : Cone n ℂ := fun k i ↦ σ (y k i)`. Establish `hz : z ∈ P.points ℂ` using `sigma_mem_points P hx σ`. Establish `hzc : ∀ k, z k (c k) ≠ 0` using `fun k ↦ (map_ne_zero σ).mpr (hyc k)`.

Establish `hb` using `hs z hz c d e he hzc`. Establish `hez : evalCone z e = σ (evalCone y e)` using `evalCone_map σ y e`. Establish `hmz : evalCone z (chartMonomial c d) = σ (evalCone y (chartMonomial c d))` using `evalCone_map σ y _`. Establish `hmet : 0 < A.metric z` using `A.metric_pos z hz.1`. Establish `hmn : 0 < ‖σ (evalCone y (chartMonomial c d))‖` using `norm_pos_iff.mpr ((map_ne_zero σ).mpr hmy)`.

Establish `htn : 0 < ‖σ t‖` using `norm_pos_iff.mpr ((map_ne_zero σ).mpr ht)`. Establish `hst : ‖σ t‖ = ‖σ (evalCone y e)‖ / ‖σ (evalCone y (chartMonomial c d))‖`. Rewrite using `[htdef, map_div₀, norm_div]`. Establish `h1 : ‖σ t‖ ≤ Real.exp C * A.metric z`. Rewrite `hb` using `[hez, hmz]`.

Rewrite using `[hst, div_le_iff₀ hmn]`. Rewrite `hb` using `[div_le_iff₀ (mul_pos hmn hmet)]`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the equalities or inequalities in the displayed calculation. Establish `hPF` using `sum_log_finitePlace_add_sum_log_embedding ht`.

Establish `hdeg : (0 : ℝ) < Module.finrank ℚ K` using `by exact_mod_cast Module.finrank_pos (R := ℚ) (M := K)`. Establish `hsupp1 : (Function.support fun v : FinitePlace K ↦ Real.log (v t)).Finite`. Use `(FinitePlace.hasFiniteMulSupport ht).subset fun v hv h1 ↦ hv ?_` and prove the remaining obligations. Establish `h1' : v t = 1` using `h1`. Use `show Real.log (v t) = 0`.

Rewrite using `[h1', Real.log_one]`. Establish `hsupp2` using `finite_support_height A x hx.1`. Establish `hF : (∑ᶠ v : FinitePlace K, Real.log (v t)) ≤ ∑ᶠ v : FinitePlace K, ∑ k, (A.deg k : ℝ) * Real.log (⨆ i, v (y k i))` using `finsum_le_finsum' hsupp1 hsupp2 hfin`. Establish `hA : ∑ σ : K →+* ℂ, Real.log ‖σ t‖ ≤ ∑ σ : K →+* ℂ, (C + Real.log (A.metric fun k i ↦ σ (y k i)))` using `Finset.sum_le_sum fun σ _ ↦ harch σ`. Rewrite `hA` using `[Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, NumberField.Embeddings.card, nsmul_eq_mul]`.

Establish `key : -(Module.finrank ℚ K : ℝ) * C ≤ (∑ᶠ v : FinitePlace K, ∑ k, (A.deg k : ℝ) * Real.log (⨆ i, v (y k i))) + ∑ σ : K →+* ℂ, Real.log (A.metric fun k i ↦ σ (y k i))`. Combine the linear equalities and inequalities to obtain the conclusion. Unfold `height`. Rewrite using `[le_inv_mul_iff₀ hdeg]`. Establish `h2 : (Module.finrank ℚ K : ℝ) * -C = -(Module.finrank ℚ K : ℝ) * C` using `by ring`.

Rewrite using `[h2]`. Conclude with `key`.
-/
theorem neg_le_height_of_chartForm {P : ArithVariety n} {A : HermLine n}
    (s : IntegralSection P A.deg) {C : ℝ} (hs : s.SupNormLE A C) {x : Cone n (AlgebraicClosure ℚ)}
    (hx : x ∈ P.points (AlgebraicClosure ℚ)) {c : (k : ι) → Fin (n k + 1)} {d : ι → ℕ}
    {e : MvPolynomial (Coord n) ℤ} (he : IsChartForm P A.deg s.num s.den c d e)
    (hc : ∀ k, x k (c k) ≠ 0) (hex : evalCone x e ≠ 0) : -C ≤ height A x := by
  set K := coordField x
  set y := coordVec x with hydef
  have hy : y ∈ P.points K := coordVec_mem_points hx
  have hval : ∀ f, K.val.toRingHom (evalCone y f) = evalCone x f :=
    fun f ↦ (evalCone_map K.val.toRingHom y f).symm
  have hyc : ∀ k, y k (c k) ≠ 0 := fun k h ↦ hc k (congrArg Subtype.val h)
  have hey : evalCone y e ≠ 0 := fun h ↦ hex (by rw [← hval, h, map_zero])
  have hmy : evalCone y (chartMonomial c d) ≠ 0 := by
    rw [evalCone_chartMonomial]
    exact Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hyc k)
  set t : K := evalCone y e / evalCone y (chartMonomial c d) with htdef
  have ht : t ≠ 0 := div_ne_zero hey hmy

  have hfin : ∀ v : FinitePlace K, Real.log (v t) ≤
      ∑ k, (A.deg k : ℝ) * Real.log (⨆ i, v (y k i)) := by
    intro v
    have hM : ∀ k, ∃ i, v (y k i) = ⨆ i, v (y k i) := fun k ↦ exists_eq_ciSup_of_finite
    choose c' hc' using hM
    have hMpos : ∀ k, 0 < ⨆ i, v (y k i) := by
      intro k
      obtain ⟨i, hi⟩ := Function.ne_iff.mp (hy.1 k)
      exact lt_of_lt_of_le (FinitePlace.pos_iff.mpr hi)
        (le_ciSup (f := fun i ↦ v (y k i)) (Set.finite_range _).bddAbove i)
    have hyc' : ∀ k, y k (c' k) ≠ 0 := by
      intro k h
      have := hc' k
      rw [h, map_zero] at this
      exact (hMpos k).ne this
    have hX : ∀ k, (X ⟨k, c' k⟩ : MvPolynomial (Coord n) ℤ) ∉ P.ideal := by
      intro k hk
      apply hyc' k
      have := hy.2 _ hk
      simpa [evalCone] using this
    obtain ⟨d', e', he'⟩ := s.regular c' hX
    have hagree := chartForm_agree s.den_not_mem he he' hy
    have hm'y : evalCone y (chartMonomial c' d') ≠ 0 := by
      rw [evalCone_chartMonomial]
      exact Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hyc' k)
    have ht' : t = evalCone y e' / evalCone y (chartMonomial c' d') := by
      rw [htdef, div_eq_div_iff hmy hm'y, hagree]
    have he'y : evalCone y e' ≠ 0 := by
      intro h
      rw [ht', h, zero_div] at ht
      exact ht rfl
    obtain ⟨⟨δ, hδ, hδa⟩, _⟩ := he'
    have hvm : v (evalCone y (chartMonomial c' d')) = ∏ k, (⨆ i, v (y k i)) ^ d' k := by
      rw [evalCone_chartMonomial, map_prod]
      refine Finset.prod_congr rfl fun k _ ↦ ?_
      rw [map_pow, hc' k]
    have hve := finitePlace_evalCone_le v y hδ
    have hpos_e : 0 < v (evalCone y e') := FinitePlace.pos_iff.mpr he'y
    rw [ht', map_div₀, Real.log_div hpos_e.ne'
      ((FinitePlace.pos_iff.mpr hm'y).ne'), hvm,
      Real.log_prod (fun k _ ↦ (pow_pos (hMpos k) _).ne')]
    have hle : Real.log (v (evalCone y e')) ≤ ∑ k, (δ k : ℝ) * Real.log (⨆ i, v (y k i)) := by
      refine (Real.log_le_log hpos_e hve).trans ?_
      rw [Real.log_prod (fun k _ ↦ (pow_pos (hMpos k) _).ne')]
      simp only [Real.log_pow, le_refl]
    simp only [Real.log_pow]
    rw [← sub_nonneg]
    have hsum : ∑ k, (A.deg k : ℝ) * Real.log (⨆ i, v (y k i)) -
        (Real.log (v (evalCone y e')) - ∑ k, (d' k : ℝ) * Real.log (⨆ i, v (y k i))) =
        ∑ k, (δ k : ℝ) * Real.log (⨆ i, v (y k i)) - Real.log (v (evalCone y e')) := by
      have hd : ∀ k, (δ k : ℝ) = (A.deg k : ℝ) + (d' k : ℝ) := fun k ↦ by exact_mod_cast hδa k
      simp only [hd, add_mul, Finset.sum_add_distrib]
      ring
    rw [hsum]
    exact sub_nonneg.mpr hle

  have harch : ∀ σ : K →+* ℂ, Real.log ‖σ t‖ ≤ C + Real.log (A.metric fun k i ↦ σ (y k i)) := by
    intro σ
    set z : Cone n ℂ := fun k i ↦ σ (y k i)
    have hz : z ∈ P.points ℂ := sigma_mem_points P hx σ
    have hzc : ∀ k, z k (c k) ≠ 0 := fun k ↦ (map_ne_zero σ).mpr (hyc k)
    have hb := hs z hz c d e he hzc
    have hez : evalCone z e = σ (evalCone y e) := evalCone_map σ y e
    have hmz : evalCone z (chartMonomial c d) = σ (evalCone y (chartMonomial c d)) :=
      evalCone_map σ y _
    have hmet : 0 < A.metric z := A.metric_pos z hz.1
    have hmn : 0 < ‖σ (evalCone y (chartMonomial c d))‖ := norm_pos_iff.mpr ((map_ne_zero σ).mpr hmy)
    have htn : 0 < ‖σ t‖ := norm_pos_iff.mpr ((map_ne_zero σ).mpr ht)
    have hst : ‖σ t‖ = ‖σ (evalCone y e)‖ / ‖σ (evalCone y (chartMonomial c d))‖ := by
      rw [htdef, map_div₀, norm_div]
    have h1 : ‖σ t‖ ≤ Real.exp C * A.metric z := by
      rw [hez, hmz] at hb
      rw [hst, div_le_iff₀ hmn]
      rw [div_le_iff₀ (mul_pos hmn hmet)] at hb
      linarith
    calc Real.log ‖σ t‖ ≤ Real.log (Real.exp C * A.metric z) := Real.log_le_log htn h1
      _ = C + Real.log (A.metric z) := by rw [Real.log_mul (Real.exp_pos C).ne' hmet.ne', Real.log_exp]

  have hPF := sum_log_finitePlace_add_sum_log_embedding ht
  have hdeg : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos (R := ℚ) (M := K)
  have hsupp1 : (Function.support fun v : FinitePlace K ↦ Real.log (v t)).Finite := by
    refine (FinitePlace.hasFiniteMulSupport ht).subset fun v hv h1 ↦ hv ?_
    have h1' : v t = 1 := h1
    show Real.log (v t) = 0
    rw [h1', Real.log_one]
  have hsupp2 := finite_support_height A x hx.1
  have hF : (∑ᶠ v : FinitePlace K, Real.log (v t)) ≤
      ∑ᶠ v : FinitePlace K, ∑ k, (A.deg k : ℝ) * Real.log (⨆ i, v (y k i)) :=
    finsum_le_finsum' hsupp1 hsupp2 hfin
  have hA : ∑ σ : K →+* ℂ, Real.log ‖σ t‖ ≤
      ∑ σ : K →+* ℂ, (C + Real.log (A.metric fun k i ↦ σ (y k i))) :=
    Finset.sum_le_sum fun σ _ ↦ harch σ
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, NumberField.Embeddings.card,
    nsmul_eq_mul] at hA
  have key : -(Module.finrank ℚ K : ℝ) * C ≤
      (∑ᶠ v : FinitePlace K, ∑ k, (A.deg k : ℝ) * Real.log (⨆ i, v (y k i))) +
        ∑ σ : K →+* ℂ, Real.log (A.metric fun k i ↦ σ (y k i)) := by
    linarith
  unfold height
  rw [le_inv_mul_iff₀ hdeg]
  have h2 : (Module.finrank ℚ K : ℝ) * -C = -(Module.finrank ℚ K : ℝ) * C := by ring
  rw [h2]
  exact key

/- English proof (translation)
Introduce `ι _ _ n P A J _ s C hs hnz x hx`. Take `⟨j, c, d, e, he, hc, hex⟩` from `hnz x hx`. Conclude with `neg_le_height_of_chartForm (s j) (hs j) hx he hc hex`.
-/
theorem heightLowerBound : HeightLowerBound.Statement := by
  intro ι _ _ n P A J _ s C hs hnz x hx
  obtain ⟨j, c, d, e, he, hc, hex⟩ := hnz x hx
  exact neg_le_height_of_chartForm (s j) (hs j) hx he hc hex

end

end GroundTheory.Heights₂.Heights
