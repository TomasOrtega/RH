import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.FiniteSupportHeight
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

/- English proof (translation)
Set `y : 𝓞 K` to `⟨x, hx⟩`. Establish `h` using `FinitePlace.norm_le_one K v.maximalIdeal y`. Rewrite `h` using `[FinitePlace.norm_embedding_eq]`. Conclude with `h`.
-/
theorem finitePlace_le_one_of_isIntegral {K : Type*} [Field K] [NumberField K] (v : FinitePlace K)
    {x : K} (hx : IsIntegral ℤ x) : v x ≤ 1 := by
  let y : 𝓞 K := ⟨x, hx⟩
  have h := FinitePlace.norm_le_one K v.maximalIdeal y
  rw [FinitePlace.norm_embedding_eq] at h
  exact h

/- English proof (translation)
Establish `hne : ((δ : ℕ) : K) ≠ 0` using `by exact_mod_cast hδ.ne'`. Establish `hfin : (Function.mulSupport fun w : FinitePlace K ↦ w (δ : K)).Finite` using `FinitePlace.hasFiniteMulSupport hne`. Establish `hprod` using `FinitePlace.prod_eq_inv_abs_norm hne`. Rewrite `hprod` using `[finprod_eq_prod_of_mulSupport_subset (s := hfin.toFinset) _ (fun x hx ↦ Finset.mem_coe.mpr (hfin.mem_toFinset.mpr hx))]`. Rewrite using `[finsum_eq_sum_of_support_subset (s := hfin.toFinset)]`.

Rewrite using `[← Real.log_prod (fun v _ ↦ (map_ne_zero _).mpr hne), hprod]`. Establish `: Algebra.norm ℚ ((δ : ℕ) : K) = (δ : ℚ) ^ (Module.finrank ℚ K)`. Use `Algebra.norm_algebraMap (S := K) (δ : ℚ)` as an intermediate fact. Simplify using `using this`. Rewrite using `[this]`.

Use `push_cast`. Rewrite using `[abs_pow, Nat.abs_cast, Real.log_inv, Real.log_pow]`. Introduce `v hv`. Establish `h1' : v (δ : K) ≠ 1` using `fun h ↦ hv (by show Real.log (v (δ : K)) = 0; rw [h, Real.log_one])`. Conclude with `Finset.mem_coe.mpr (hfin.mem_toFinset.mpr h1')`.
-/
theorem finsum_log_finitePlace_natCast {K : Type*} [Field K] [NumberField K] {δ : ℕ} (hδ : 0 < δ) :
    ∑ᶠ v : FinitePlace K, Real.log (v (δ : K)) = -(Module.finrank ℚ K * Real.log δ) := by
  have hne : ((δ : ℕ) : K) ≠ 0 := by exact_mod_cast hδ.ne'
  have hfin : (Function.mulSupport fun w : FinitePlace K ↦ w (δ : K)).Finite :=
    FinitePlace.hasFiniteMulSupport hne
  have hprod := FinitePlace.prod_eq_inv_abs_norm hne
  rw [finprod_eq_prod_of_mulSupport_subset (s := hfin.toFinset) _
    (fun x hx ↦ Finset.mem_coe.mpr (hfin.mem_toFinset.mpr hx))] at hprod
  rw [finsum_eq_sum_of_support_subset (s := hfin.toFinset)]
  · rw [← Real.log_prod (fun v _ ↦ (map_ne_zero _).mpr hne), hprod]
    have : Algebra.norm ℚ ((δ : ℕ) : K) = (δ : ℚ) ^ (Module.finrank ℚ K) := by
      have := Algebra.norm_algebraMap (S := K) (δ : ℚ)
      simpa using this
    rw [this]
    push_cast
    rw [abs_pow, Nat.abs_cast, Real.log_inv, Real.log_pow]
  · intro v hv
    have h1' : v (δ : K) ≠ 1 := fun h ↦ hv (by show Real.log (v (δ : K)) = 0; rw [h, Real.log_one])
    exact Finset.mem_coe.mpr (hfin.mem_toFinset.mpr h1')

/- English proof (translation)
Rewrite using `[l2Norm, ← Real.sqrt_sq hR, ← Real.sqrt_mul (Nat.cast_nonneg m)]`. Use `Real.sqrt_le_sqrt ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem vectorL2Norm_le_sqrt_card_mul {m : ℕ} (w : Fin m → ℂ) {R : ℝ} (hR : 0 ≤ R) (hw : ∀ i, ‖w i‖ ≤ R) :
    l2Norm w ≤ Real.sqrt m * R := by
  rw [l2Norm, ← Real.sqrt_sq hR, ← Real.sqrt_mul (Nat.cast_nonneg m)]
  refine Real.sqrt_le_sqrt ?_
  calc ∑ i, ‖w i‖ ^ 2 ≤ ∑ _i : Fin m, R ^ 2 :=
        Finset.sum_le_sum fun i _ ↦ pow_le_pow_left₀ (norm_nonneg _) (hw i) 2
    _ = m * R ^ 2 := by simp

/- English proof (translation)
Use `set K := coordField z`. Use `set d : ℝ := (Module.finrank ℚ K : ℝ) with hd_def`. Establish `hd : 0 < d` using `by rw [hd_def]; exact_mod_cast Module.finrank_pos (R := ℚ) (M := K)`. Establish `hne : ((δ : ℕ) : K) ≠ 0` using `by exact_mod_cast hδ.ne'`. Establish `hloc : ∀ (v : FinitePlace K) (k : ι), Real.log (⨆ i, v (coordVec z k i)) ≤ -Real.log (v (δ : K))`.

Introduce `v k`. Establish `hδv : 0 < v (δ : K)` using `FinitePlace.pos_iff.mpr hne`. Take `⟨i0, hi0⟩` from `Function.ne_iff.mp (hz k)`. Establish `hi0' : coordVec z k i0 ≠ 0` using `fun h ↦ hi0 (congrArg Subtype.val h)`. Establish `hpos : 0 < ⨆ i, v (coordVec z k i)` using `lt_of_lt_of_le (FinitePlace.pos_iff.mpr hi0') (le_ciSup (f := fun i ↦ v (coordVec z k i)) (Set.finite_range _).bddAbove i0)`.

Rewrite using `[← Real.log_inv]`. Use `Real.log_le_log hpos (ciSup_le fun i ↦ ?_)` and prove the remaining obligations. Establish `hI : IsIntegral ℤ ((δ : K) * coordVec z k i)`. Establish `h1` using `hint k i`. Establish `h2 : (K.val : K →+* AlgebraicClosure ℚ) ((δ : K) * coordVec z k i) = (δ : AlgebraicClosure ℚ) * z k i`.

Simplify using `[coordVec]`. Rewrite `h1` using `[← h2]`. Conclude with `(isIntegral_algHom_iff ((K.val : K →+* AlgebraicClosure ℚ).toIntAlgHom) K.val.injective).mp h1`. Establish `h3` using `finitePlace_le_one_of_isIntegral v hI`. Rewrite `h3` using `[map_mul]`.

Combine the equalities or inequalities in the displayed calculation. Clear the denominators using the available nonvanishing facts. Use `_ ≤ (v (δ : K))⁻¹ * 1 := mul_le_mul_of_nonneg_left h3 (inv_pos.mpr hδv).le`. Use `_ = (v (δ : K))⁻¹ := mul_one _`. Establish `hsupp1` using `finite_support_height (HermLine.standard n) z hz`.

Establish `hsupp2 : (Function.support fun v : FinitePlace K ↦ Real.log (v (δ : K))).Finite`. Use `(FinitePlace.hasFiniteMulSupport hne).subset fun v hv h ↦ hv ?_` and prove the remaining obligations. Establish `h' : v (δ : K) = 1` using `h`. Use `show Real.log (v (δ : K)) = 0`. Rewrite using `[h', Real.log_one]`.

Use `set T := (hsupp1.union hsupp2).toFinset`. Establish `hfin : (∑ᶠ v : FinitePlace K, ∑ k, ((HermLine.standard n).deg k : ℝ) * Real.log (⨆ i, v (coordVec z k i))) ≤ Fintype.card ι * (d * Real.log δ)`. Rewrite using `[finsum_eq_sum_of_support_subset (s := T) _ (fun v hv ↦ Finset.mem_coe.mpr ((Set.Finite.mem_toFinset _).mpr (Or.inl hv)))]`. Establish `h2 : ∑ᶠ v : FinitePlace K, Real.log (v (δ : K)) = ∑ v ∈ T, Real.log (v (δ : K))` using `finsum_eq_sum_of_support_subset (s := T) _ (fun v hv ↦ Finset.mem_coe.mpr ((Set.Finite.mem_toFinset _).mpr (Or.inr hv)))`. Establish `h3` using `finsum_log_finitePlace_natCast (K := K) hδ`.

Rewrite `h3` using `[h2]`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_le_sum fun v _ ↦ Finset.sum_le_sum fun k _ ↦ ?_` and prove the remaining obligations. Simplify using `only [HermLine.standard, Int.cast_one, one_mul]`. Conclude with `hloc v k`.

Use `_ = Fintype.card ι * -(∑ v ∈ T, Real.log (v (δ : K))) := by`. Simplify using `[Finset.sum_neg_distrib, Finset.mul_sum]`. Use `_ = Fintype.card ι * (d * Real.log δ) := by rw [h3, neg_neg]`. Establish `: Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ)`. Apply the tactic sequence `convert AlgebraicClosure.isAlgebraic ℚ <;> rfl`.

Establish `: Algebra.IsAlgebraic K (AlgebraicClosure ℚ)` using `Algebra.IsAlgebraic.tower_top (K := ℚ) K`. Establish `harchK : ∀ σ : K →+* ℂ, Real.log ((HermLine.standard n).metric fun k i ↦ σ (coordVec z k i)) ≤ ∑ k, Real.log (Real.sqrt (n k + 1) * R)`. Introduce `σ`. Set `σ' : AlgebraicClosure ℚ →+* ℂ` to `ComplexEmbedding.lift (AlgebraicClosure ℚ) σ`. Establish `hσ : ∀ k i, σ (coordVec z k i) = σ' (z k i)`.

Introduce `k i`. Use `ComplexEmbedding.lift_algebraMap_apply (AlgebraicClosure ℚ) σ (coordVec z k i)` as an intermediate fact. Rewrite using `[← this]`. Both sides reduce to the same expression. Establish `hpos : ∀ k, 0 < l2Norm (fun i ↦ σ (coordVec z k i))`.

Introduce `k`. Take `⟨i0, hi0⟩` from `Function.ne_iff.mp (hz k)`. Use `vectorL2Norm_pos (Function.ne_iff.mpr ⟨i0, ?_⟩)` and prove the remaining obligations. Introduce `h`. Apply `hi0` to reduce the goal to its premises.

Establish `h2` using `(map_eq_zero σ).mp h`. Use `congrArg Subtype.val h2` as an intermediate fact. Simplify `this` using `[coordVec]`. Express the relevant statement in the definitionally equal form `Real.log (∏ k, l2Norm (fun i ↦ σ (coordVec z k i))) ≤ _`. Rewrite using `[Real.log_prod (fun k _ ↦ (hpos k).ne')]`.

Use `Finset.sum_le_sum fun k _ ↦ Real.log_le_log (hpos k) ?_` and prove the remaining obligations. Use `vectorL2Norm_le_sqrt_card_mul (fun i ↦ σ (coordVec z k i)) hR.le (fun i ↦ by rw [hσ]; exact harch σ' k i)` as an intermediate fact. Simplify using `using this`. Establish `harchSum : ∑ σ : K →+* ℂ, Real.log ((HermLine.standard n).metric fun k i ↦ σ (coordVec z k i)) ≤ d * ∑ k, Real.log (Real.sqrt (n k + 1) * R)`. Use `(Finset.sum_le_sum fun σ _ ↦ harchK σ).trans ?_` and prove the remaining obligations.

Rewrite using `[Finset.sum_const, Finset.card_univ, NumberField.Embeddings.card, nsmul_eq_mul]`. Use `set S := ∑ k, Real.log (Real.sqrt (n k + 1) * R) with hS`. Unfold `height`. Rewrite using `[← hd_def]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hS]`. Clear the denominators using the available nonvanishing facts.
-/
theorem height_standard_le (z : Cone n (AlgebraicClosure ℚ)) (hz : BlockNonzero z) {δ : ℕ}
    (hδ : 0 < δ) {R : ℝ} (hR : 0 < R)
    (hint : ∀ k i, IsIntegral ℤ ((δ : AlgebraicClosure ℚ) * z k i))
    (harch : ∀ (σ : AlgebraicClosure ℚ →+* ℂ) k i, ‖σ (z k i)‖ ≤ R) :
    height (HermLine.standard n) z ≤ ∑ k, (Real.log δ + Real.log (Real.sqrt (n k + 1) * R)) := by
  set K := coordField z
  set d : ℝ := (Module.finrank ℚ K : ℝ) with hd_def
  have hd : 0 < d := by rw [hd_def]; exact_mod_cast Module.finrank_pos (R := ℚ) (M := K)
  have hne : ((δ : ℕ) : K) ≠ 0 := by exact_mod_cast hδ.ne'

  have hloc : ∀ (v : FinitePlace K) (k : ι),
      Real.log (⨆ i, v (coordVec z k i)) ≤ -Real.log (v (δ : K)) := by
    intro v k
    have hδv : 0 < v (δ : K) := FinitePlace.pos_iff.mpr hne
    obtain ⟨i0, hi0⟩ := Function.ne_iff.mp (hz k)
    have hi0' : coordVec z k i0 ≠ 0 := fun h ↦ hi0 (congrArg Subtype.val h)
    have hpos : 0 < ⨆ i, v (coordVec z k i) :=
      lt_of_lt_of_le (FinitePlace.pos_iff.mpr hi0')
        (le_ciSup (f := fun i ↦ v (coordVec z k i)) (Set.finite_range _).bddAbove i0)
    rw [← Real.log_inv]
    refine Real.log_le_log hpos (ciSup_le fun i ↦ ?_)
    have hI : IsIntegral ℤ ((δ : K) * coordVec z k i) := by
      have h1 := hint k i
      have h2 : (K.val : K →+* AlgebraicClosure ℚ) ((δ : K) * coordVec z k i) =
          (δ : AlgebraicClosure ℚ) * z k i := by
        simp [coordVec]
      rw [← h2] at h1
      exact (isIntegral_algHom_iff ((K.val : K →+* AlgebraicClosure ℚ).toIntAlgHom)
        K.val.injective).mp h1
    have h3 := finitePlace_le_one_of_isIntegral v hI
    rw [map_mul] at h3
    calc v (coordVec z k i) = (v (δ : K))⁻¹ * (v (δ : K) * v (coordVec z k i)) := by
          field_simp
      _ ≤ (v (δ : K))⁻¹ * 1 := mul_le_mul_of_nonneg_left h3 (inv_pos.mpr hδv).le
      _ = (v (δ : K))⁻¹ := mul_one _
  have hsupp1 := finite_support_height (HermLine.standard n) z hz
  have hsupp2 : (Function.support fun v : FinitePlace K ↦ Real.log (v (δ : K))).Finite := by
    refine (FinitePlace.hasFiniteMulSupport hne).subset fun v hv h ↦ hv ?_
    have h' : v (δ : K) = 1 := h
    show Real.log (v (δ : K)) = 0
    rw [h', Real.log_one]
  set T := (hsupp1.union hsupp2).toFinset
  have hfin : (∑ᶠ v : FinitePlace K, ∑ k, ((HermLine.standard n).deg k : ℝ) *
      Real.log (⨆ i, v (coordVec z k i))) ≤ Fintype.card ι * (d * Real.log δ) := by
    rw [finsum_eq_sum_of_support_subset (s := T) _
      (fun v hv ↦ Finset.mem_coe.mpr ((Set.Finite.mem_toFinset _).mpr (Or.inl hv)))]
    have h2 : ∑ᶠ v : FinitePlace K, Real.log (v (δ : K)) = ∑ v ∈ T, Real.log (v (δ : K)) :=
      finsum_eq_sum_of_support_subset (s := T) _
        (fun v hv ↦ Finset.mem_coe.mpr ((Set.Finite.mem_toFinset _).mpr (Or.inr hv)))
    have h3 := finsum_log_finitePlace_natCast (K := K) hδ
    rw [h2] at h3
    calc ∑ v ∈ T, ∑ k, ((HermLine.standard n).deg k : ℝ) * Real.log (⨆ i, v (coordVec z k i))
        ≤ ∑ v ∈ T, ∑ _k : ι, -Real.log (v (δ : K)) := by
          refine Finset.sum_le_sum fun v _ ↦ Finset.sum_le_sum fun k _ ↦ ?_
          simp only [HermLine.standard, Int.cast_one, one_mul]
          exact hloc v k
      _ = Fintype.card ι * -(∑ v ∈ T, Real.log (v (δ : K))) := by
          simp [Finset.sum_neg_distrib, Finset.mul_sum]
      _ = Fintype.card ι * (d * Real.log δ) := by rw [h3, neg_neg]

  have : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
    convert AlgebraicClosure.isAlgebraic ℚ <;> rfl
  have : Algebra.IsAlgebraic K (AlgebraicClosure ℚ) := Algebra.IsAlgebraic.tower_top (K := ℚ) K
  have harchK : ∀ σ : K →+* ℂ, Real.log ((HermLine.standard n).metric
      fun k i ↦ σ (coordVec z k i)) ≤ ∑ k, Real.log (Real.sqrt (n k + 1) * R) := by
    intro σ
    let σ' : AlgebraicClosure ℚ →+* ℂ := ComplexEmbedding.lift (AlgebraicClosure ℚ) σ
    have hσ : ∀ k i, σ (coordVec z k i) = σ' (z k i) := by
      intro k i
      have := ComplexEmbedding.lift_algebraMap_apply (AlgebraicClosure ℚ) σ (coordVec z k i)
      rw [← this]
      rfl
    have hpos : ∀ k, 0 < l2Norm (fun i ↦ σ (coordVec z k i)) := by
      intro k
      obtain ⟨i0, hi0⟩ := Function.ne_iff.mp (hz k)
      refine vectorL2Norm_pos (Function.ne_iff.mpr ⟨i0, ?_⟩)
      intro h
      apply hi0
      have h2 := (map_eq_zero σ).mp h
      have := congrArg Subtype.val h2
      simpa [coordVec] using this
    change Real.log (∏ k, l2Norm (fun i ↦ σ (coordVec z k i))) ≤ _
    rw [Real.log_prod (fun k _ ↦ (hpos k).ne')]
    refine Finset.sum_le_sum fun k _ ↦ Real.log_le_log (hpos k) ?_
    have := vectorL2Norm_le_sqrt_card_mul (fun i ↦ σ (coordVec z k i)) hR.le (fun i ↦ by rw [hσ]; exact harch σ' k i)
    simpa using this
  have harchSum : ∑ σ : K →+* ℂ, Real.log ((HermLine.standard n).metric
      fun k i ↦ σ (coordVec z k i)) ≤ d * ∑ k, Real.log (Real.sqrt (n k + 1) * R) := by
    refine (Finset.sum_le_sum fun σ _ ↦ harchK σ).trans ?_
    rw [Finset.sum_const, Finset.card_univ, NumberField.Embeddings.card, nsmul_eq_mul]

  set S := ∑ k, Real.log (Real.sqrt (n k + 1) * R) with hS
  unfold height
  rw [← hd_def]
  calc d⁻¹ * (_ + _) ≤ d⁻¹ * (Fintype.card ι * (d * Real.log δ) +
        d * ∑ k, Real.log (Real.sqrt (n k + 1) * R)) :=
        mul_le_mul_of_nonneg_left (add_le_add hfin harchSum) (inv_pos.mpr hd).le
    _ = ∑ k, (Real.log δ + Real.log (Real.sqrt (n k + 1) * R)) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hS]
        field_simp

end

end GroundTheory.Heights₂.Heights
