import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UnitaryActHalfSpace
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.PosSemidefSubMulConjTranspose
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsLinearIndependentOfRatIndependent
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real

namespace GlobalTheory.SW.EisConv

noncomputable def embAll (E m : Type) [Field E] [NumberField E] :
    (m → 𝓞 E) →ₗ[ℤ] (m → (E →+* ℂ) → ℂ) :=
  AddMonoidHom.toIntLinearMap
    { toFun := fun w j σ => σ (w j : E)
      map_zero' := by ext j σ; simp
      map_add' := fun s t => by ext j σ; simp }

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem embAll_apply {E m : Type} [Field E] [NumberField E] (w : m → 𝓞 E) (j : m)
    (σ : E →+* ℂ) : embAll E m w j σ = σ (w j : E) := rfl

/- English proof (translation)
Take `⟨j, hj⟩` from `Function.ne_iff.1 hw`. Establish `h1 : (w j : E) ≠ 0` using `by simpa using hj`. Establish `h2` using `one_le_house_of_isIntegral (w j).isIntegral_coe h1`. Conclude with `h2.trans (norm_le_pi_norm (embAll E m w) j)`.
-/
theorem one_le_norm_embAll {E m : Type} [Field E] [NumberField E] [Fintype m] {w : m → 𝓞 E}
    (hw : w ≠ 0) : 1 ≤ ‖embAll E m w‖ := by
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hw
  have h1 : (w j : E) ≠ 0 := by simpa using hj
  have h2 := one_le_house_of_isIntegral (w j).isIntegral_coe h1
  exact h2.trans (norm_le_pi_norm (embAll E m w) j)

/- English proof (translation)
Establish `hinj : Function.Injective (embAll E m)`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `w hw`. Assume the negation of the conclusion as `h`. Use `one_le_norm_embAll h` as an intermediate fact.

Rewrite `this` using `[hw, norm_zero]`. Conclude with `absurd this (by norm_num)`. Use `set L := LinearMap.range (embAll E m) with hL`. Establish `: DiscreteTopology L`. Use `discreteTopology_of_isOpen_singleton_zero ?_` and prove the remaining obligations.

Establish `: ({0} : Set L) = Metric.ball 0 1`. Use extensionality with `⟨_, w, rfl⟩`. Distinguish the cases in `h : w = 0`. Substitute `h` using the available equality. Simplify using `[Subtype.ext_iff]`.

Establish `h1` using `one_le_norm_embAll h`. Establish `h2 : embAll E m w ≠ 0` using `fun h2 => h (hinj (h2.trans (map_zero _).symm))`. Simplify using `[Subtype.ext_iff, h2, h1]`. Rewrite using `[this]`. Conclude with `Metric.isOpen_ball`.

Establish `hr : Module.finrank ℤ L < k`. Rewrite using `[hL, LinearMap.finrank_range_of_inj hinj, Module.finrank_pi_fintype]`. Simplify `hk` using `[RingOfIntegers.rank]`. Conclude with `(ZLattice.summable_norm_pow_inv L k hr).comp_injective (i := fun w => (⟨embAll E m w, w, rfl⟩ : L)) fun v w h => hinj (congrArg Subtype.val h)`.
-/
theorem summable_embAll (E m : Type) [Field E] [NumberField E] [Fintype m] (k : ℕ)
    (hk : Fintype.card m * Module.finrank ℚ E < k) :
    Summable fun w : m → 𝓞 E => ‖embAll E m w‖⁻¹ ^ k := by
  have hinj : Function.Injective (embAll E m) := by
    rw [injective_iff_map_eq_zero]
    intro w hw
    by_contra h
    have := one_le_norm_embAll h
    rw [hw, norm_zero] at this
    exact absurd this (by norm_num)
  set L := LinearMap.range (embAll E m) with hL
  have : DiscreteTopology L := by
    refine discreteTopology_of_isOpen_singleton_zero ?_
    have : ({0} : Set L) = Metric.ball 0 1 := by
      ext ⟨_, w, rfl⟩
      by_cases h : w = 0
      · subst h; simp [Subtype.ext_iff]
      · have h1 := one_le_norm_embAll h
        have h2 : embAll E m w ≠ 0 := fun h2 => h (hinj (h2.trans (map_zero _).symm))
        simp [Subtype.ext_iff, h2, h1]
    rw [this]; exact Metric.isOpen_ball
  have hr : Module.finrank ℤ L < k := by
    rw [hL, LinearMap.finrank_range_of_inj hinj, Module.finrank_pi_fintype]
    simpa [RingOfIntegers.rank] using hk
  exact (ZLattice.summable_norm_pow_inv L k hr).comp_injective
    (i := fun w => (⟨embAll E m w, w, rfl⟩ : L)) fun v w h => hinj (congrArg Subtype.val h)

/- English proof (translation)
Proceed by induction on `N with`. Consider the case `zero => exact .of_finite`. Consider the case `succ N ih`. Establish `h` using `hg.mul_of_nonneg ih h0 fun x => Finset.prod_nonneg fun i _ => h0 _`. Rewrite using `[← (Fin.consEquiv fun _ : Fin (N + 1) => α).summable_iff]`.

Use `h.congr fun p => ?_` and prove the remaining obligations. Simplify using `[Fin.prod_univ_succ, Fin.consEquiv]`.
-/
theorem summable_prod_tuple {α : Type} {g : α → ℝ} (hg : Summable g) (h0 : ∀ a, 0 ≤ g a) (N : ℕ) :
    Summable fun x : Fin N → α => ∏ i, g (x i) := by
  induction N with
  | zero => exact .of_finite
  | succ N ih =>
    have h := hg.mul_of_nonneg ih h0 fun x => Finset.prod_nonneg fun i _ => h0 _
    rw [← (Fin.consEquiv fun _ : Fin (N + 1) => α).summable_iff]
    refine h.congr fun p => ?_
    simp [Fin.prod_univ_succ, Fin.consEquiv]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}

/- English proof (translation)
Establish `h1 : LinearIndependent E γ.row` using `linearIndependent_rows_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 (HAct.group_part h).1)`. Conclude with `h1.comp Sum.inr Sum.inr_injective`.
-/
theorem linearIndependent_bot {γ : M2 E N} (h : γ ∈ UU E N) :
    LinearIndependent E fun i => γ.submatrix Sum.inr id i := by
  have h1 : LinearIndependent E γ.row := linearIndependent_rows_iff_isUnit.2
    ((Matrix.isUnit_iff_isUnit_det _).2 (HAct.group_part h).1)
  exact h1.comp Sum.inr Sum.inr_injective

/- English proof (translation)
Establish `e : (γ.submatrix Sum.inr id).map τ * ((γ.submatrix Sum.inr id).map τ)ᴴ = γ.toBlocks₂₁.map τ * (γ.toBlocks₂₁.map τ)ᴴ + γ.toBlocks₂₂.map τ * (γ.toBlocks₂₂.map τ)ᴴ`. Use extensionality with `i j`. Simplify using `[mul_apply, Fintype.sum_sum_type, toBlocks₂₁, toBlocks₂₂]`. Establish `h1` using `HAct.map_mem τ (HAct.group_part h).2.2.1`. Rewrite `h1` using `[HAct.map_ccT, HAct.map_blocks τ γ, fromBlocks_conjTranspose]`.

Establish `h2` using `(HAct.blocks h1).2.2.2`. Simplify using `only [conjTranspose_conjTranspose] at h2`. Establish `h3 : (γ.toBlocks₂₁.map τ * (γ.toBlocks₂₂.map τ)ᴴ).IsHermitian`. Rewrite using `[IsHermitian, conjTranspose_mul, conjTranspose_conjTranspose, h2]`. Establish `h4` using `denom_mul_conjTranspose _ _ 0 h3 isHermitian_zero 1`.

Rewrite using `[e]`. Establish `h5` using `norm_det_mul_conjTranspose (γ.toBlocks₂₁.map τ * (I • (1 : Matrix (Fin N) (Fin N) ℂ)) + γ.toBlocks₂₂.map τ)`. Simplify using `only [ofReal_one, mul_one, zero_add, Matrix.mul_zero, one_pow, one_smul] at h4`. Rewrite `h5` using `[h4, add_comm]`. Rewrite using `[h5, ofReal_re]`.
-/
theorem det_gram_bot {γ : M2 E N} (h : γ ∈ UU E N) (τ : E →+* ℂ) :
    ((γ.submatrix Sum.inr id).map τ * ((γ.submatrix Sum.inr id).map τ)ᴴ).det.re =
      ‖(γ.toBlocks₂₁.map τ * (I • (1 : Matrix (Fin N) (Fin N) ℂ)) + γ.toBlocks₂₂.map τ).det‖ ^ 2 := by
  have e : (γ.submatrix Sum.inr id).map τ * ((γ.submatrix Sum.inr id).map τ)ᴴ =
      γ.toBlocks₂₁.map τ * (γ.toBlocks₂₁.map τ)ᴴ + γ.toBlocks₂₂.map τ * (γ.toBlocks₂₂.map τ)ᴴ := by
    ext i j
    simp [mul_apply, Fintype.sum_sum_type, toBlocks₂₁, toBlocks₂₂]
  have h1 := HAct.map_mem τ (HAct.group_part h).2.2.1
  rw [HAct.map_ccT, HAct.map_blocks τ γ, fromBlocks_conjTranspose] at h1
  have h2 := (HAct.blocks h1).2.2.2
  simp only [conjTranspose_conjTranspose] at h2
  have h3 : (γ.toBlocks₂₁.map τ * (γ.toBlocks₂₂.map τ)ᴴ).IsHermitian := by
    rw [IsHermitian, conjTranspose_mul, conjTranspose_conjTranspose, h2]
  have h4 := denom_mul_conjTranspose _ _ 0 h3 isHermitian_zero 1
  rw [e]
  have h5 := norm_det_mul_conjTranspose
    (γ.toBlocks₂₁.map τ * (I • (1 : Matrix (Fin N) (Fin N) ℂ)) + γ.toBlocks₂₂.map τ)
  simp only [ofReal_one, mul_one, zero_add, Matrix.mul_zero, one_pow, one_smul] at h4
  rw [h4, add_comm] at h5
  rw [h5, ofReal_re]

/- English proof (translation)
Use `(Real.le_sqrt (norm_nonneg _) (by positivity)).1 ?_` and prove the remaining obligations. Use `(pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun j => ?_` and prove the remaining obligations. Use `(pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun σ => ?_` and prove the remaining obligations. Choose the witnesses or unpack the hypotheses as in `⟨τ, hτ⟩ : ∃ τ : Ψ, ‖σ (w j : E)‖ = ‖τ.1 (w j : E)‖ := by`. Distinguish the cases in `h : σ ∈ Ψ`.

Conclude with `⟨⟨σ, h⟩, rfl⟩`. Use `⟨⟨ComplexEmbedding.conjugate σ, ?_⟩, by simp⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hc`. Conclude with `h ((hΨ σ).2 hc)`. Use `Real.le_sqrt_of_sq_le ?_` and prove the remaining obligations.

Rewrite using `[embAll_apply, hτ]`. Use `le_trans ?_ (Finset.single_le_sum (f := fun τ : Ψ => ∑ j, ‖τ.1 (w j : E)‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ τ))` and prove the remaining obligations. Conclude with `Finset.single_le_sum (f := fun j => ‖τ.1 (w j : E)‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ j)`.
-/
theorem norm_embAll_sq_le {m : Type} [Fintype m] {Ψ : Finset (E →+* ℂ)} (hΨ : IsType Ψ)
    (w : m → 𝓞 E) : ‖embAll E m w‖ ^ 2 ≤ ∑ τ : Ψ, ∑ j, ‖τ.1 (w j : E)‖ ^ 2 := by
  refine (Real.le_sqrt (norm_nonneg _) (by positivity)).1 ?_
  refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun j => ?_
  refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun σ => ?_
  obtain ⟨τ, hτ⟩ : ∃ τ : Ψ, ‖σ (w j : E)‖ = ‖τ.1 (w j : E)‖ := by
    by_cases h : σ ∈ Ψ
    · exact ⟨⟨σ, h⟩, rfl⟩
    · refine ⟨⟨ComplexEmbedding.conjugate σ, ?_⟩, by simp⟩
      by_contra hc
      exact h ((hΨ σ).2 hc)
  refine Real.le_sqrt_of_sq_le ?_
  rw [embAll_apply, hτ]
  refine le_trans ?_ (Finset.single_le_sum (f := fun τ : Ψ => ∑ j, ‖τ.1 (w j : E)‖ ^ 2)
    (fun _ _ => by positivity) (Finset.mem_univ τ))
  exact Finset.single_le_sum (f := fun j => ‖τ.1 (w j : E)‖ ^ 2)
    (fun _ _ => by positivity) (Finset.mem_univ j)

omit [NumberField E] [IsCMField E] in

/- English proof (translation)
Establish `key : ∀ (b : Matrix (Fin N) (Fin N) E) (X : Matrix (Fin N) m E), Submodule.span E (Set.range fun i => (b * X) i) ≤ Submodule.span E (Set.range fun i => X i)`. Introduce `b X`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Establish `: (b * X) i = ∑ k, b i k • X k` using `by ext j; simp [mul_apply]`.

Simplify using `only [this]`. Conclude with `Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)`. Use `le_antisymm (key a W) ?_` and prove the remaining obligations. Use `key a⁻¹ (a * W)` as an intermediate fact. Rewrite `this` using `[← Matrix.mul_assoc, nonsing_inv_mul _ (Ne.isUnit ha), Matrix.one_mul]`. Then use the resulting hypothesis.
-/
theorem span_rows_mul {m : Type} (a : Matrix (Fin N) (Fin N) E) (ha : a.det ≠ 0)
    (W : Matrix (Fin N) m E) :
    Submodule.span E (Set.range fun i => (a * W) i) = Submodule.span E (Set.range fun i => W i) := by
  have key : ∀ (b : Matrix (Fin N) (Fin N) E) (X : Matrix (Fin N) m E),
      Submodule.span E (Set.range fun i => (b * X) i) ≤
        Submodule.span E (Set.range fun i => X i) := by
    intro b X
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have : (b * X) i = ∑ k, b i k • X k := by ext j; simp [mul_apply]
    simp only [this]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  refine le_antisymm (key a W) ?_
  have := key a⁻¹ (a * W)
  rwa [← Matrix.mul_assoc, nonsing_inv_mul _ (Ne.isUnit ha), Matrix.one_mul] at this

/- English proof (translation)
Take `⟨C, hC, H⟩` from `exists_short_independent_rows E Ψ hΨ N`. Use `⟨√C * (c : ℝ) ^ (N * Ψ.card), by positivity, fun γ hγ hd => ?_⟩` and prove the remaining obligations. Take `⟨a, hai, ha, hle⟩` from `H _ _ (linearIndependent_bot hγ)`. Establish `hcE : (c : E) ≠ 0` using `by exact_mod_cast hc.ne'`. Establish `hca : ((c : E) • a).det ≠ 0`.

Rewrite using `[det_smul]`. Conclude with `mul_ne_zero (pow_ne_zero _ hcE) ha`. Establish `hint : ∀ i j, IsIntegral ℤ ((((c : E) • a) * γ.submatrix Sum.inr id) i j)` using `fun i j => by`. Rewrite using `[Matrix.smul_mul, ← Matrix.mul_smul, mul_apply]`. Conclude with `IsIntegral.sum _ fun k _ => (hai i k).mul (hd (Sum.inr k) j)`.

Use `set w : Fin N → (Fin N ⊕ Fin N → 𝓞 E) := fun i j => ⟨_, hint i j⟩ with hw`. Establish `hwe : ∀ i j, (w i j : E) = (((c : E) • a) * γ.submatrix Sum.inr id) i j` using `fun _ _ => rfl`. Use `⟨w, span_rows_mul _ hca _, fun i hi => ?_, ?_⟩` and prove the remaining obligations. Establish `h1 : ((c : E) • a) i ᵥ* γ.submatrix Sum.inr id = 0`. Use extensionality with `j`.

Use `hwe i j` as an intermediate fact. Rewrite `this` using `[hi]`. Conclude with `this.symm`. Establish `h2 : ((c : E) • a) i = 0` using `vecMul_injective_iff.2 (linearIndependent_bot hγ) (h1.trans (zero_vecMul _).symm)`. Conclude with `hca (det_eq_zero_of_row_eq_zero i fun j => congrFun h2 j)`.

Use `(pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 ?_` and prove the remaining obligations. Simplify using `only [det_gram_bot hγ] at hle`. Establish `h1 : ∀ i, (‖embAll E _ (w i)‖ ^ Ψ.card) ^ 2 ≤ ((c : ℝ) ^ 2) ^ Ψ.card * (∑ τ : Ψ, ∑ j, ‖τ.1 ((a * γ.submatrix Sum.inr id) i j)‖ ^ 2) ^ Ψ.card` using `fun i => by`. Rewrite using `[← pow_mul, mul_comm, pow_mul, ← mul_pow]`. Use `pow_le_pow_left₀ (by positivity) ((norm_embAll_sq_le hΨ _).trans (le_of_eq ?_)) _` and prove the remaining obligations.

Simplify using `only [hwe, Finset.mul_sum, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul, map_mul, map_natCast, norm_mul, norm_natCast, mul_pow]`. Rewrite using `[← Finset.prod_pow]`. Use `(Finset.prod_le_prod (fun _ _ => by positivity) fun i _ => h1 i).trans ?_` and prove the remaining obligations. Rewrite using `[Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]`. Use `(mul_le_mul_of_nonneg_left hle (by positivity)).trans (le_of_eq ?_)` and prove the remaining obligations.

Rewrite using `[mul_pow, mul_pow, Real.sq_sqrt hC.le, Finset.prod_pow]`. Simplify using `only [hDen]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_short_generators {Ψ : Finset (E →+* ℂ)} (hΨ : IsType Ψ) (N c : ℕ) (hc : 0 < c) :
    ∃ K : ℝ, 0 < K ∧ ∀ γ ∈ UU E N, Den c γ → ∃ w : Fin N → (Fin N ⊕ Fin N → 𝓞 E),
      Submodule.span E (Set.range fun i j => (w i j : E)) = botSpan γ ∧ (∀ i, w i ≠ 0) ∧
      ∏ i, ‖embAll E _ (w i)‖ ^ Ψ.card ≤
        K * ∏ τ : Ψ, ‖(hDen Ψ γ (fun _ => I • (1 : Matrix (Fin N) (Fin N) ℂ)) τ).det‖ := by
  obtain ⟨C, hC, H⟩ := exists_short_independent_rows E Ψ hΨ N
  refine ⟨√C * (c : ℝ) ^ (N * Ψ.card), by positivity, fun γ hγ hd => ?_⟩
  obtain ⟨a, hai, ha, hle⟩ := H _ _ (linearIndependent_bot hγ)
  have hcE : (c : E) ≠ 0 := by exact_mod_cast hc.ne'
  have hca : ((c : E) • a).det ≠ 0 := by
    rw [det_smul]; exact mul_ne_zero (pow_ne_zero _ hcE) ha
  have hint : ∀ i j, IsIntegral ℤ ((((c : E) • a) * γ.submatrix Sum.inr id) i j) := fun i j => by
    rw [Matrix.smul_mul, ← Matrix.mul_smul, mul_apply]
    exact IsIntegral.sum _ fun k _ => (hai i k).mul (hd (Sum.inr k) j)
  set w : Fin N → (Fin N ⊕ Fin N → 𝓞 E) := fun i j => ⟨_, hint i j⟩ with hw
  have hwe : ∀ i j, (w i j : E) = (((c : E) • a) * γ.submatrix Sum.inr id) i j := fun _ _ => rfl
  refine ⟨w, span_rows_mul _ hca _, fun i hi => ?_, ?_⟩
  · have h1 : ((c : E) • a) i ᵥ* γ.submatrix Sum.inr id = 0 := by
      ext j
      have := hwe i j
      rw [hi] at this
      exact this.symm
    have h2 : ((c : E) • a) i = 0 :=
      vecMul_injective_iff.2 (linearIndependent_bot hγ) (h1.trans (zero_vecMul _).symm)
    exact hca (det_eq_zero_of_row_eq_zero i fun j => congrFun h2 j)
  · refine (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 ?_
    simp only [det_gram_bot hγ] at hle
    have h1 : ∀ i, (‖embAll E _ (w i)‖ ^ Ψ.card) ^ 2 ≤ ((c : ℝ) ^ 2) ^ Ψ.card *
        (∑ τ : Ψ, ∑ j, ‖τ.1 ((a * γ.submatrix Sum.inr id) i j)‖ ^ 2) ^ Ψ.card := fun i => by
      rw [← pow_mul, mul_comm, pow_mul, ← mul_pow]
      refine pow_le_pow_left₀ (by positivity) ((norm_embAll_sq_le hΨ _).trans (le_of_eq ?_)) _
      simp only [hwe, Finset.mul_sum, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul, map_mul,
        map_natCast, norm_mul, norm_natCast, mul_pow]
    rw [← Finset.prod_pow]
    refine (Finset.prod_le_prod (fun _ _ => by positivity) fun i _ => h1 i).trans ?_
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    refine (mul_le_mul_of_nonneg_left hle (by positivity)).trans (le_of_eq ?_)
    rw [mul_pow, mul_pow, Real.sq_sqrt hC.le, Finset.prod_pow]
    simp only [hDen]
    ring

end GlobalTheory.SW.EisConv

open GlobalTheory.SW.EisConv in

/- English proof (translation)
Introduce `E _ _ _ Ψ hΨ n N hn c rep hc hrep`. Take `⟨K, hK, H⟩` from `exists_short_generators hΨ N c hc`. Use `choose w hspan hne hle using fun U => H (rep U) (hrep U).1 (hrep U).2.1`. Establish `hinj : Function.Injective w` using `fun U V h => Subtype.ext (by`. Rewrite using `[← (hrep U).2.2, ← (hrep V).2.2, ← hspan, ← hspan, h])`.

Establish `hf : 0 < Ψ.card`. Establish `h1` using `hΨ.finrank_eq`. Establish `h2 : 0 < Module.finrank ℚ E` using `Module.finrank_pos`. Use linear arithmetic over natural numbers and integers. Establish `hs` using `summable_embAll E (Fin N ⊕ Fin N) (Ψ.card * n) (by`.

Rewrite using `[hΨ.finrank_eq, Fintype.card_sum, Fintype.card_fin]`. Use the proof step `nlinarith)`. Establish `hs2` using `((summable_prod_tuple hs (fun _ => by positivity) N).comp_injective hinj).mul_left (K ^ n)`. Use `Summable.of_nonneg_of_le (fun U => by positivity) (fun U => ?_) hs2` and prove the remaining obligations. Establish `hp : 0 < ∏ i, ‖embAll E _ (w U i)‖ ^ Ψ.card` using `Finset.prod_pos fun i _ => pow_pos (one_pos.trans_le (one_le_norm_embAll (hne U i))) _`.

Establish `hP` using `(pos_iff_pos_of_mul_pos (hp.trans_le (hle U))).1 hK`. Simplify using `only [Function.comp, pow_mul, inv_pow]`. Rewrite using `[Finset.prod_inv_distrib, Finset.prod_inv_distrib, Finset.prod_pow, Finset.prod_pow _ n, ← div_eq_mul_inv, ← div_pow, ← inv_pow]`. Use `pow_le_pow_left₀ (by positivity) ?_ n` and prove the remaining obligations. Rewrite using `[inv_eq_one_div, div_le_div_iff₀ hP hp, one_mul]`.

Conclude with `hle U`.
-/
theorem GlobalTheory.SW.summable_eis_majorant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), 4 * N < n → ∀ (c : ℕ) (rep : Lag E N → M2 E N), 0 < c → (∀ U, rep U ∈ UU E N ∧ Den c (rep U) ∧ botSpan (rep U) = U.1) → Summable fun U : Lag E N => ∏ τ : Ψ, (‖(hDen Ψ (rep U) (fun _ => I • (1 : Matrix (Fin N) (Fin N) ℂ)) τ).det‖ ^ n)⁻¹ := by
  intro E _ _ _ Ψ hΨ n N hn c rep hc hrep
  obtain ⟨K, hK, H⟩ := exists_short_generators hΨ N c hc
  choose w hspan hne hle using fun U => H (rep U) (hrep U).1 (hrep U).2.1
  have hinj : Function.Injective w := fun U V h => Subtype.ext (by
    rw [← (hrep U).2.2, ← (hrep V).2.2, ← hspan, ← hspan, h])
  have hf : 0 < Ψ.card := by
    have h1 := hΨ.finrank_eq
    have h2 : 0 < Module.finrank ℚ E := Module.finrank_pos
    omega
  have hs := summable_embAll E (Fin N ⊕ Fin N) (Ψ.card * n) (by
    rw [hΨ.finrank_eq, Fintype.card_sum, Fintype.card_fin]
    nlinarith)
  have hs2 := ((summable_prod_tuple hs (fun _ => by positivity) N).comp_injective hinj).mul_left
    (K ^ n)
  refine Summable.of_nonneg_of_le (fun U => by positivity) (fun U => ?_) hs2
  have hp : 0 < ∏ i, ‖embAll E _ (w U i)‖ ^ Ψ.card := Finset.prod_pos fun i _ =>
    pow_pos (one_pos.trans_le (one_le_norm_embAll (hne U i))) _
  have hP := (pos_iff_pos_of_mul_pos (hp.trans_le (hle U))).1 hK
  simp only [Function.comp, pow_mul, inv_pow]
  rw [Finset.prod_inv_distrib, Finset.prod_inv_distrib, Finset.prod_pow, Finset.prod_pow _ n,
    ← div_eq_mul_inv, ← div_pow, ← inv_pow]
  refine pow_le_pow_left₀ (by positivity) ?_ n
  rw [inv_eq_one_div, div_le_div_iff₀ hP hp, one_mul]
  exact hle U
