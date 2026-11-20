import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Metric Module Submodule
open scoped ENNReal Pointwise

namespace LatticePointCount

/- English proof (translation)
Establish `hmp : MeasurePreserving (@WithLp.ofLp 2 (Fin r → ℝ))` using `PiLp.volume_preserving_ofLp (Fin r)`. Combine the equalities or inequalities in the displayed calculation. Apply `measure_mono` to reduce the goal to its premises. Introduce `y hy`. Simplify using `only [Set.mem_preimage, mem_closedBall, dist_zero_right] at hy ⊢`.

Use `(pi_norm_le_iff_of_nonneg hR).2 fun i => ?_` and prove the remaining obligations. Conclude with `(PiLp.norm_apply_le y i).trans hy`. Use `_ = volume (closedBall (0 : Fin r → ℝ) R) := hmp.measure_preimage measurableSet_closedBall.nullMeasurableSet`. Use `_ = ENNReal.ofReal (2 * R) ^ r := by rw [Real.volume_pi_closedBall _ hR, Fintype.card_fin, ENNReal.ofReal_pow (by positivity)]`.
-/
theorem volume_closedBall_le (r : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    volume (closedBall (0 : EuclideanSpace ℝ (Fin r)) R) ≤ ENNReal.ofReal (2 * R) ^ r := by
  have hmp : MeasurePreserving (@WithLp.ofLp 2 (Fin r → ℝ)) := PiLp.volume_preserving_ofLp (Fin r)
  calc volume (closedBall (0 : EuclideanSpace ℝ (Fin r)) R)
      ≤ volume ((@WithLp.ofLp 2 (Fin r → ℝ)) ⁻¹' closedBall (0 : Fin r → ℝ) R) := by
        apply measure_mono
        intro y hy
        simp only [Set.mem_preimage, mem_closedBall, dist_zero_right] at hy ⊢
        refine (pi_norm_le_iff_of_nonneg hR).2 fun i => ?_
        exact (PiLp.norm_apply_le y i).trans hy
    _ = volume (closedBall (0 : Fin r → ℝ) R) :=
        hmp.measure_preimage measurableSet_closedBall.nullMeasurableSet
    _ = ENNReal.ofReal (2 * R) ^ r := by rw [Real.volume_pi_closedBall _ hR, Fintype.card_fin, ENNReal.ofReal_pow (by positivity)]

/- English proof (translation)
Use `set L := (span ℤ (Set.range c)).toAddSubgroup with hL`. Use `set F := ZSpan.fundamentalDomain c with hFdef`. Establish `hLc : Countable L` using `(inferInstance : Countable (span ℤ (Set.range c)))`. Establish `hF : IsAddFundamentalDomain L F volume` using `ZSpan.isAddFundamentalDomain c volume`. Establish `hball : ∀ g : L, g +ᵥ closedBall (0 : EuclideanSpace ℝ (Fin r)) (1 + μ) = closedBall (g : EuclideanSpace ℝ (Fin r)) (1 + μ)`.

Introduce `g`. Use extensionality with `v`. Rewrite using `[Set.mem_vadd_set_iff_neg_vadd_mem]`. Simplify using `only [mem_closedBall, dist_eq_norm]`. Rewrite using `[sub_zero, AddSubgroup.vadd_def, vadd_eq_add, AddSubgroup.coe_neg, neg_add_eq_sub]`.

Establish `hpt : ∀ v, (X.card : ℝ≥0∞) ≤ ∑' g : L, (closedBall (g : EuclideanSpace ℝ (Fin r)) (1 + μ)).indicator 1 v`. Introduce `v`. Take `⟨l, hl, hlv⟩` from `hcov v`. Set `s : Finset L` to `X.attach.map ⟨fun x => ⟨l + x.1, add_mem hl (hX x.1 x.2).1⟩, fun x y h => by`. Apply `Subtype.ext` to reduce the goal to its premises.

Simplify using `using congrArg Subtype.val h⟩`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_map]`. Rewrite using `[Finset.sum_congr rfl (g := fun _ => (1 : ℝ≥0∞))]`. Simplify using the standard rewrite rules.

Introduce `x _`. Rewrite using `[Set.indicator_of_mem]`. Both sides reduce to the same expression. Simplify using `only [mem_closedBall, dist_eq_norm]`. Combine the equalities or inequalities in the displayed calculation.

Use `_ ≤ ∑' g : L, (closedBall (g : EuclideanSpace ℝ (Fin r)) (1 + μ)).indicator 1 v := ENNReal.sum_le_tsum s`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[setLIntegral_const]`. Use `_ ≤ ∫⁻ v in F, ∑' g : L, (closedBall (g : EuclideanSpace ℝ (Fin r)) (1 + μ)).indicator 1 v := lintegral_mono fun v => hpt v`. Use `_ = ∑' g : L, ∫⁻ v in F, (closedBall (g : EuclideanSpace ℝ (Fin r)) (1 + μ)).indicator 1 v := lintegral_tsum fun g => (measurable_one.indicator measurableSet_closedBall).aemeasurable`.

Use `_ = ∑' g : L, volume ((g +ᵥ closedBall (0 : EuclideanSpace ℝ (Fin r)) (1 + μ)) ∩ F) := by`. Use `congr 1`. Use extensionality with `g`. Rewrite using `[lintegral_indicator_one measurableSet_closedBall, Measure.restrict_apply measurableSet_closedBall, hball]`. Use `_ = volume (closedBall (0 : EuclideanSpace ℝ (Fin r)) (1 + μ)) := (hF.measure_eq_tsum _).symm`.
-/
theorem card_mul_volume_le {r : ℕ} (c : Basis (Fin r) ℝ (EuclideanSpace ℝ (Fin r))) {μ : ℝ}
    (hcov : ∀ y, ∃ l ∈ span ℤ (Set.range c), ‖y - l‖ ≤ μ)
    (X : Finset (EuclideanSpace ℝ (Fin r)))
    (hX : ∀ x ∈ X, x ∈ span ℤ (Set.range c) ∧ ‖x‖ ≤ 1) :
    (X.card : ℝ≥0∞) * volume (ZSpan.fundamentalDomain c) ≤
      volume (closedBall (0 : EuclideanSpace ℝ (Fin r)) (1 + μ)) := by
  classical
  set L := (span ℤ (Set.range c)).toAddSubgroup with hL
  set F := ZSpan.fundamentalDomain c with hFdef
  have hLc : Countable L := (inferInstance : Countable (span ℤ (Set.range c)))
  have hF : IsAddFundamentalDomain L F volume := ZSpan.isAddFundamentalDomain c volume
  have hball : ∀ g : L, g +ᵥ closedBall (0 : EuclideanSpace ℝ (Fin r)) (1 + μ) =
      closedBall (g : EuclideanSpace ℝ (Fin r)) (1 + μ) := by
    intro g
    ext v
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    simp only [mem_closedBall, dist_eq_norm]
    rw [sub_zero, AddSubgroup.vadd_def, vadd_eq_add, AddSubgroup.coe_neg, neg_add_eq_sub]
  have hpt : ∀ v, (X.card : ℝ≥0∞) ≤
      ∑' g : L, (closedBall (g : EuclideanSpace ℝ (Fin r)) (1 + μ)).indicator 1 v := by
    intro v
    obtain ⟨l, hl, hlv⟩ := hcov v
    let s : Finset L := X.attach.map ⟨fun x => ⟨l + x.1, add_mem hl (hX x.1 x.2).1⟩, fun x y h => by
      apply Subtype.ext
      simpa using congrArg Subtype.val h⟩
    calc (X.card : ℝ≥0∞) = ∑ g ∈ s, (closedBall (g : EuclideanSpace ℝ (Fin r)) (1 + μ)).indicator 1 v := by
          rw [Finset.sum_map]
          rw [Finset.sum_congr rfl (g := fun _ => (1 : ℝ≥0∞))]
          · simp
          · intro x _
            rw [Set.indicator_of_mem]
            · rfl
            simp only [mem_closedBall, dist_eq_norm]
            calc ‖v - (l + x.1)‖ = ‖(v - l) - x.1‖ := by rw [sub_add_eq_sub_sub]
              _ ≤ ‖v - l‖ + ‖x.1‖ := norm_sub_le _ _
              _ ≤ μ + 1 := add_le_add hlv (hX x.1 x.2).2
              _ = 1 + μ := add_comm _ _
      _ ≤ ∑' g : L, (closedBall (g : EuclideanSpace ℝ (Fin r)) (1 + μ)).indicator 1 v :=
          ENNReal.sum_le_tsum s
  calc (X.card : ℝ≥0∞) * volume F = ∫⁻ _ in F, (X.card : ℝ≥0∞) := by
        rw [setLIntegral_const]
    _ ≤ ∫⁻ v in F, ∑' g : L, (closedBall (g : EuclideanSpace ℝ (Fin r)) (1 + μ)).indicator 1 v :=
        lintegral_mono fun v => hpt v
    _ = ∑' g : L, ∫⁻ v in F, (closedBall (g : EuclideanSpace ℝ (Fin r)) (1 + μ)).indicator 1 v :=
        lintegral_tsum fun g => (measurable_one.indicator measurableSet_closedBall).aemeasurable
    _ = ∑' g : L, volume ((g +ᵥ closedBall (0 : EuclideanSpace ℝ (Fin r)) (1 + μ)) ∩ F) := by
        congr 1
        ext g
        rw [lintegral_indicator_one measurableSet_closedBall,
          Measure.restrict_apply measurableSet_closedBall, hball]
    _ = volume (closedBall (0 : EuclideanSpace ℝ (Fin r)) (1 + μ)) := (hF.measure_eq_tsum _).symm

/- English proof (translation)
Rewrite using `[ZSpan.measure_fundamentalDomain c volume (EuclideanSpace.basisFun (Fin r) ℝ).toBasis, measure_congr (ZSpan.fundamentalDomain_ae_parallelepiped _ volume)]`. Rewrite using `[OrthonormalBasis.coe_toBasis, OrthonormalBasis.volume_parallelepiped, mul_one]`.
-/
theorem volume_fundamentalDomain_eq {r : ℕ} (c : Basis (Fin r) ℝ (EuclideanSpace ℝ (Fin r))) :
    volume (ZSpan.fundamentalDomain c) =
      ENNReal.ofReal |(EuclideanSpace.basisFun (Fin r) ℝ).toBasis.det c| := by
  rw [ZSpan.measure_fundamentalDomain c volume (EuclideanSpace.basisFun (Fin r) ℝ).toBasis,
    measure_congr (ZSpan.fundamentalDomain_ae_parallelepiped _ volume)]
  rw [OrthonormalBasis.coe_toBasis, OrthonormalBasis.volume_parallelepiped, mul_one]

/- English proof (translation)
Establish `h` using `Matrix.gram_eq_conjTranspose_mul (𝕜 := ℝ) (EuclideanSpace.basisFun (Fin r) ℝ) c`. Express the relevant statement in the definitionally equal form `(Matrix.gram ℝ c).det = _`. Rewrite using `[h, Matrix.det_mul, Matrix.det_conjTranspose, Basis.det_apply, sq]`. Simplify using `only [star_trivial]`. Establish `hm : (Matrix.of fun i j => ((EuclideanSpace.basisFun (Fin r) ℝ).repr (c j)).ofLp i) = (EuclideanSpace.basisFun (Fin r) ℝ).toBasis.toMatrix c`.

Use extensionality with `i j`. Simplify using `[Basis.toMatrix_apply]`. Rewrite using `[hm]`.
-/
theorem det_gram_eq_sq {r : ℕ} (c : Fin r → EuclideanSpace ℝ (Fin r)) :
    (Matrix.of fun i j ↦ @inner ℝ _ _ (c i) (c j)).det =
      ((EuclideanSpace.basisFun (Fin r) ℝ).toBasis.det c) ^ 2 := by
  have h := Matrix.gram_eq_conjTranspose_mul (𝕜 := ℝ) (EuclideanSpace.basisFun (Fin r) ℝ) c
  change (Matrix.gram ℝ c).det = _
  rw [h, Matrix.det_mul, Matrix.det_conjTranspose, Basis.det_apply, sq]
  simp only [star_trivial]
  have hm : (Matrix.of fun i j => ((EuclideanSpace.basisFun (Fin r) ℝ).repr (c j)).ofLp i) =
      (EuclideanSpace.basisFun (Fin r) ℝ).toBasis.toMatrix c := by
    ext i j
    simp [Basis.toMatrix_apply]
  rw [hm]

/- English proof (translation)
Establish `hSℤ : ∀ s ∈ S, s ∈ span ℤ (Set.range b)` using `fun s hs => hspan ▸ subset_span hs`. Establish `hle : span ℝ (Set.range b) ≤ span ℝ S`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Establish `: b i ∈ span ℤ S` using `hspan ▸ subset_span ⟨i, rfl⟩`.

Conclude with `Submodule.span_le_restrictScalars ℤ ℝ S this`. Establish `hge : span ℝ S ≤ span ℝ (Set.range b)`. Rewrite using `[Submodule.span_le]`. Introduce `s hs`. Conclude with `Submodule.span_le_restrictScalars ℤ ℝ _ (hSℤ s hs)`.

Take `⟨T, hTS, hTspan, hTli⟩` from `exists_linearIndependent ℝ S`. Establish `hTW : span ℝ T = span ℝ (Set.range b)` using `hTspan.trans (le_antisymm hge hle)`. Establish `hWfin : FiniteDimensional ℝ (span ℝ (Set.range b))` using `FiniteDimensional.span_of_finite ℝ (Set.finite_range b)`. Establish `: FiniteDimensional ℝ (span ℝ (Set.range ((↑) : T → V)))`. Rewrite using `[Subtype.range_coe, hTW]`.

Conclude with `hWfin`. Establish `: Finite T` using `Module.Finite.finite_basis (Basis.span hTli)`. Use `set T' : Finset V := (Set.toFinite T).toFinset with hT'`. Establish `hT'coe : (T' : Set V) = T` using `Set.Finite.coe_toFinset _`. Establish `hcard : T'.card = r`.

Establish `h1` using `finrank_span_finset_eq_card (R := ℝ) (s := T') (by rw [hT'coe]; exact hTli)`. Rewrite `h1` using `[hT'coe, hTW, finrank_span_eq_card hb, Fintype.card_fin]`. Conclude with `h1.symm`. Rewrite `hv` using `[← hTW, ← hT'coe]`. Take `⟨f, -, hf⟩` from `Submodule.mem_span_finset.1 hv`.

Establish `hT'S : ∀ t ∈ T', t ∈ S` using `fun t ht => hTS (hT'coe ▸ ht)`. Use `⟨∑ t ∈ T', (⌊f t⌋ : ℤ) • t, ?_, ?_⟩` and prove the remaining obligations. Conclude with `sum_mem fun t ht => zsmul_mem (hSℤ t (hT'S t ht)) _`. Rewrite using `[← hf, ← Finset.sum_sub_distrib]`. Combine the equalities or inequalities in the displayed calculation.

Use `Finset.sum_le_sum fun t ht => ?_` and prove the remaining obligations. Rewrite using `[← Int.cast_smul_eq_zsmul ℝ, ← sub_smul, norm_smul, Real.norm_eq_abs]`. Establish `h0 : 0 ≤ f t - ⌊f t⌋` using `Int.fract_nonneg (f t)`. Establish `h1 : f t - ⌊f t⌋ < 1` using `Int.fract_lt_one (f t)`. Rewrite using `[abs_of_nonneg h0]`.

Combine the equalities or inequalities in the displayed calculation. Use `_ = r * C := by rw [Finset.sum_const, hcard, nsmul_eq_mul]`.
-/
theorem exists_near {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {r : ℕ} (b : Fin r → V)
    (hb : LinearIndependent ℝ b) (S : Set V) (C : ℝ) (hS : ∀ s ∈ S, ‖s‖ ≤ C)
    (hspan : span ℤ S = span ℤ (Set.range b)) (v : V) (hv : v ∈ span ℝ (Set.range b)) :
    ∃ l ∈ span ℤ (Set.range b), ‖v - l‖ ≤ r * C := by
  classical
  have hSℤ : ∀ s ∈ S, s ∈ span ℤ (Set.range b) := fun s hs => hspan ▸ subset_span hs
  have hle : span ℝ (Set.range b) ≤ span ℝ S := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have : b i ∈ span ℤ S := hspan ▸ subset_span ⟨i, rfl⟩
    exact Submodule.span_le_restrictScalars ℤ ℝ S this
  have hge : span ℝ S ≤ span ℝ (Set.range b) := by
    rw [Submodule.span_le]
    intro s hs
    exact Submodule.span_le_restrictScalars ℤ ℝ _ (hSℤ s hs)
  obtain ⟨T, hTS, hTspan, hTli⟩ := exists_linearIndependent ℝ S
  have hTW : span ℝ T = span ℝ (Set.range b) := hTspan.trans (le_antisymm hge hle)
  have hWfin : FiniteDimensional ℝ (span ℝ (Set.range b)) :=
    FiniteDimensional.span_of_finite ℝ (Set.finite_range b)
  have : FiniteDimensional ℝ (span ℝ (Set.range ((↑) : T → V))) := by
    rw [Subtype.range_coe, hTW]
    exact hWfin
  have : Finite T := Module.Finite.finite_basis (Basis.span hTli)
  set T' : Finset V := (Set.toFinite T).toFinset with hT'
  have hT'coe : (T' : Set V) = T := Set.Finite.coe_toFinset _
  have hcard : T'.card = r := by
    have h1 := finrank_span_finset_eq_card (R := ℝ) (s := T') (by rw [hT'coe]; exact hTli)
    rw [hT'coe, hTW, finrank_span_eq_card hb, Fintype.card_fin] at h1
    exact h1.symm
  rw [← hTW, ← hT'coe] at hv
  obtain ⟨f, -, hf⟩ := Submodule.mem_span_finset.1 hv
  have hT'S : ∀ t ∈ T', t ∈ S := fun t ht => hTS (hT'coe ▸ ht)
  refine ⟨∑ t ∈ T', (⌊f t⌋ : ℤ) • t, ?_, ?_⟩
  · exact sum_mem fun t ht => zsmul_mem (hSℤ t (hT'S t ht)) _
  · rw [← hf, ← Finset.sum_sub_distrib]
    calc ‖∑ t ∈ T', (f t • t - (⌊f t⌋ : ℤ) • t)‖ ≤ ∑ t ∈ T', ‖f t • t - (⌊f t⌋ : ℤ) • t‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _t ∈ T', C := by
          refine Finset.sum_le_sum fun t ht => ?_
          rw [← Int.cast_smul_eq_zsmul ℝ, ← sub_smul, norm_smul, Real.norm_eq_abs]
          have h0 : 0 ≤ f t - ⌊f t⌋ := Int.fract_nonneg (f t)
          have h1 : f t - ⌊f t⌋ < 1 := Int.fract_lt_one (f t)
          rw [abs_of_nonneg h0]
          calc (f t - ⌊f t⌋) * ‖t‖ ≤ 1 * ‖t‖ := by gcongr
            _ ≤ C := by rw [one_mul]; exact hS t (hT'S t ht)
      _ = r * C := by rw [Finset.sum_const, hcard, nsmul_eq_mul]

/- English proof (translation)
Introduce `V _ _ r b hb S C hC hS hspan`. Use `set W := span ℝ (Set.range b) with hWdef`. Establish `: FiniteDimensional ℝ W` using `FiniteDimensional.span_of_finite ℝ (Set.finite_range b)`. Set `bW : Basis (Fin r) ℝ W` to `Basis.span hb`. Establish `hrank : finrank ℝ W = r` using `by rw [finrank_span_eq_card hb, Fintype.card_fin]`.

Set `e : OrthonormalBasis (Fin r) ℝ W` to `(stdOrthonormalBasis ℝ W).reindex (finCongr hrank)`. Set `φ : W ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin r)` to `e.repr`. Set `c : Basis (Fin r) ℝ (EuclideanSpace ℝ (Fin r))` to `bW.map φ.toLinearEquiv`. Set `g : EuclideanSpace ℝ (Fin r) →ₗ[ℝ] V` to `W.subtype ∘ₗ φ.symm.toLinearEquiv.toLinearMap`. Establish `hgc : ∀ i, g (c i) = b i`.

Introduce `i`. Simplify using `[g, c, bW]`. Conclude with `Basis.coe_span_apply hb i`. Establish `hgnorm : ∀ y, ‖g y‖ = ‖y‖`. Introduce `y`.

Conclude with `φ.symm.norm_map y`. Establish `hginj : Function.Injective g`. Introduce `y z h`. Establish `: ‖y - z‖ = 0` using `by rw [← hgnorm, map_sub, h, sub_self, norm_zero]`. Conclude with `sub_eq_zero.1 (norm_eq_zero.1 this)`.

Establish `hgspan : span ℤ (Set.range b) = (span ℤ (Set.range c)).map (g.restrictScalars ℤ)`. Establish `hcomp : (⇑(g.restrictScalars ℤ) ∘ ⇑c) = b` using `funext hgc`. Rewrite using `[Submodule.map_span, ← Set.range_comp, hcomp]`. Establish `hset : {x : V | x ∈ span ℤ (Set.range b) ∧ ‖x‖ ≤ 1} = g '' {y | y ∈ span ℤ (Set.range c) ∧ ‖y‖ ≤ 1}`. Use extensionality with `x`.

Rewrite using `[hgspan]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hx, hx1⟩`. Take `⟨y, hy, rfl⟩` from `Submodule.mem_map.1 hx`. Conclude with `⟨y, ⟨hy, by rw [← hgnorm]; exact hx1⟩, rfl⟩`.

Introduce and unpack `⟨y, ⟨hy, hy1⟩, rfl⟩`. Conclude with `⟨Submodule.mem_map.2 ⟨y, hy, rfl⟩, by rw [hgnorm]; exact hy1⟩`. Establish `hcov : ∀ y, ∃ l ∈ span ℤ (Set.range c), ‖y - l‖ ≤ r * C`. Introduce `y`. Take `⟨l, hl, hly⟩` from `exists_near b hb S C hS hspan (g y) (φ.symm y).2`.

Rewrite `hl` using `[hgspan]`. Take `⟨l', hl', rfl⟩` from `Submodule.mem_map.1 hl`. Use `⟨l', hl', ?_⟩` and prove the remaining obligations. Rewrite using `[← hgnorm, map_sub]`. Conclude with `hly`.

Establish `hgram : (Matrix.of fun i j ↦ @inner ℝ V _ (b i) (b j)) = Matrix.of fun i j ↦ @inner ℝ _ _ (c i) (c j)`. Use extensionality with `i j`. Simplify using `only [Matrix.of_apply]`. Rewrite using `[← hgc i, ← hgc j]`. Conclude with `φ.symm.inner_map_map (c i) (c j)`.

Use `set d := (EuclideanSpace.basisFun (Fin r) ℝ).toBasis.det c with hd`. Establish `hd0 : 0 < |d|` using `abs_pos.2 ((EuclideanSpace.basisFun (Fin r) ℝ).toBasis.isUnit_det c).ne_zero`. Establish `hrC : 0 ≤ (r : ℝ) * C` using `mul_nonneg (Nat.cast_nonneg r) hC`. Establish `hR : 0 ≤ 1 + r * C` using `by linarith`. Establish `hK : 0 < (2 * (1 + r * C)) ^ r` using `pow_pos (by linarith) r`.

Establish `hbound : ∀ X : Finset (EuclideanSpace ℝ (Fin r)), (∀ x ∈ X, x ∈ span ℤ (Set.range c) ∧ ‖x‖ ≤ 1) → (X.card : ℝ) * |d| ≤ (2 * (1 + r * C)) ^ r`. Introduce `X hX`. Establish `h` using `(card_mul_volume_le c hcov X hX).trans (volume_closedBall_le r hR)`. Rewrite `h` using `[volume_fundamentalDomain_eq, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _), ← ENNReal.ofReal_pow (by linarith)]`. Conclude with `(ENNReal.ofReal_le_ofReal_iff hK.le).1 h`.

Establish `hfin : {y | y ∈ span ℤ (Set.range c) ∧ ‖y‖ ≤ 1}.Finite`. Assume the negation of the conclusion as `hinf`. Take `⟨t, ht, htc⟩` from `Set.Infinite.exists_subset_card_eq hinf (⌈(2 * (1 + r * C)) ^ r / |d|⌉₊ + 1)`. Establish `h` using `hbound t (fun x hx => ht hx)`. Rewrite `h` using `[htc]`.

Establish `h2 : (2 * (1 + r * C)) ^ r / |d| < ((⌈(2 * (1 + r * C)) ^ r / |d|⌉₊ + 1 : ℕ) : ℝ)`. Use `push_cast`. Conclude with `(Nat.le_ceil _).trans_lt (lt_add_one _)`. Rewrite `h2` using `[div_lt_iff₀ hd0]`. Combine the linear equalities and inequalities to obtain the conclusion.

Use `⟨hset ▸ hfin.image g, ?_⟩` and prove the remaining obligations. Rewrite using `[hset, Set.ncard_image_of_injective _ hginj, hgram, det_gram_eq_sq, Set.ncard_eq_toFinset_card _ hfin]`. Establish `hN` using `hbound hfin.toFinset (fun x hx => (Set.Finite.mem_toFinset hfin).1 hx)`. Establish `hNpos : (0 : ℝ) < hfin.toFinset.card`. Establish `h0 : (0 : EuclideanSpace ℝ (Fin r)) ∈ hfin.toFinset`.

Rewrite using `[Set.Finite.mem_toFinset]`. Conclude with `⟨zero_mem _, by simp⟩`. Conclude with `Finset.card_pos.2 ⟨0, h0⟩` after adjusting the coercions. Establish `hlog : Real.log hfin.toFinset.card ≤ Real.log ((2 * (1 + r * C)) ^ r / |d|)` using `Real.log_le_log hNpos ((le_div_iff₀ hd0).2 hN)`. Rewrite `hlog` using `[Real.log_div hK.ne' hd0.ne', Real.log_pow, Real.log_abs]`.

Rewrite using `[Real.log_pow]`. Move the coercions through the operations in `at hlog ⊢`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem proof : LatticePointCount.Statement := by
  intro V _ _ r b hb S C hC hS hspan
  classical
  set W := span ℝ (Set.range b) with hWdef
  have : FiniteDimensional ℝ W := FiniteDimensional.span_of_finite ℝ (Set.finite_range b)
  let bW : Basis (Fin r) ℝ W := Basis.span hb
  have hrank : finrank ℝ W = r := by rw [finrank_span_eq_card hb, Fintype.card_fin]
  let e : OrthonormalBasis (Fin r) ℝ W := (stdOrthonormalBasis ℝ W).reindex (finCongr hrank)
  let φ : W ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin r) := e.repr
  let c : Basis (Fin r) ℝ (EuclideanSpace ℝ (Fin r)) := bW.map φ.toLinearEquiv
  let g : EuclideanSpace ℝ (Fin r) →ₗ[ℝ] V := W.subtype ∘ₗ φ.symm.toLinearEquiv.toLinearMap
  have hgc : ∀ i, g (c i) = b i := by
    intro i
    simp [g, c, bW]
    exact Basis.coe_span_apply hb i
  have hgnorm : ∀ y, ‖g y‖ = ‖y‖ := by
    intro y
    exact φ.symm.norm_map y
  have hginj : Function.Injective g := by
    intro y z h
    have : ‖y - z‖ = 0 := by rw [← hgnorm, map_sub, h, sub_self, norm_zero]
    exact sub_eq_zero.1 (norm_eq_zero.1 this)
  have hgspan : span ℤ (Set.range b) = (span ℤ (Set.range c)).map (g.restrictScalars ℤ) := by
    have hcomp : (⇑(g.restrictScalars ℤ) ∘ ⇑c) = b := funext hgc
    rw [Submodule.map_span, ← Set.range_comp, hcomp]
  have hset : {x : V | x ∈ span ℤ (Set.range b) ∧ ‖x‖ ≤ 1} =
      g '' {y | y ∈ span ℤ (Set.range c) ∧ ‖y‖ ≤ 1} := by
    ext x
    rw [hgspan]
    constructor
    · rintro ⟨hx, hx1⟩
      obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hx
      exact ⟨y, ⟨hy, by rw [← hgnorm]; exact hx1⟩, rfl⟩
    · rintro ⟨y, ⟨hy, hy1⟩, rfl⟩
      exact ⟨Submodule.mem_map.2 ⟨y, hy, rfl⟩, by rw [hgnorm]; exact hy1⟩
  have hcov : ∀ y, ∃ l ∈ span ℤ (Set.range c), ‖y - l‖ ≤ r * C := by
    intro y
    obtain ⟨l, hl, hly⟩ := exists_near b hb S C hS hspan (g y) (φ.symm y).2
    rw [hgspan] at hl
    obtain ⟨l', hl', rfl⟩ := Submodule.mem_map.1 hl
    refine ⟨l', hl', ?_⟩
    rw [← hgnorm, map_sub]
    exact hly
  have hgram : (Matrix.of fun i j ↦ @inner ℝ V _ (b i) (b j)) =
      Matrix.of fun i j ↦ @inner ℝ _ _ (c i) (c j) := by
    ext i j
    simp only [Matrix.of_apply]
    rw [← hgc i, ← hgc j]
    exact φ.symm.inner_map_map (c i) (c j)
  set d := (EuclideanSpace.basisFun (Fin r) ℝ).toBasis.det c with hd
  have hd0 : 0 < |d| := abs_pos.2 ((EuclideanSpace.basisFun (Fin r) ℝ).toBasis.isUnit_det c).ne_zero
  have hrC : 0 ≤ (r : ℝ) * C := mul_nonneg (Nat.cast_nonneg r) hC
  have hR : 0 ≤ 1 + r * C := by linarith
  have hK : 0 < (2 * (1 + r * C)) ^ r := pow_pos (by linarith) r
  have hbound : ∀ X : Finset (EuclideanSpace ℝ (Fin r)),
      (∀ x ∈ X, x ∈ span ℤ (Set.range c) ∧ ‖x‖ ≤ 1) → (X.card : ℝ) * |d| ≤ (2 * (1 + r * C)) ^ r := by
    intro X hX
    have h := (card_mul_volume_le c hcov X hX).trans (volume_closedBall_le r hR)
    rw [volume_fundamentalDomain_eq, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
      ← ENNReal.ofReal_pow (by linarith)] at h
    exact (ENNReal.ofReal_le_ofReal_iff hK.le).1 h
  have hfin : {y | y ∈ span ℤ (Set.range c) ∧ ‖y‖ ≤ 1}.Finite := by
    by_contra hinf
    obtain ⟨t, ht, htc⟩ := Set.Infinite.exists_subset_card_eq hinf (⌈(2 * (1 + r * C)) ^ r / |d|⌉₊ + 1)
    have h := hbound t (fun x hx => ht hx)
    rw [htc] at h
    have h2 : (2 * (1 + r * C)) ^ r / |d| < ((⌈(2 * (1 + r * C)) ^ r / |d|⌉₊ + 1 : ℕ) : ℝ) := by
      push_cast
      exact (Nat.le_ceil _).trans_lt (lt_add_one _)
    rw [div_lt_iff₀ hd0] at h2
    linarith
  refine ⟨hset ▸ hfin.image g, ?_⟩
  rw [hset, Set.ncard_image_of_injective _ hginj, hgram, det_gram_eq_sq, Set.ncard_eq_toFinset_card _ hfin]
  have hN := hbound hfin.toFinset (fun x hx => (Set.Finite.mem_toFinset hfin).1 hx)
  have hNpos : (0 : ℝ) < hfin.toFinset.card := by
    have h0 : (0 : EuclideanSpace ℝ (Fin r)) ∈ hfin.toFinset := by
      rw [Set.Finite.mem_toFinset]
      exact ⟨zero_mem _, by simp⟩
    exact_mod_cast Finset.card_pos.2 ⟨0, h0⟩
  have hlog : Real.log hfin.toFinset.card ≤ Real.log ((2 * (1 + r * C)) ^ r / |d|) :=
    Real.log_le_log hNpos ((le_div_iff₀ hd0).2 hN)
  rw [Real.log_div hK.ne' hd0.ne', Real.log_pow, Real.log_abs] at hlog
  rw [Real.log_pow]
  push_cast at hlog ⊢
  linarith

end LatticePointCount

end GroundTheory.Heights₂.Heights
