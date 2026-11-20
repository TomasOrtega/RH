import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLocalGraphMass
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PMassFinite
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLocalGraphProjectionMass
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Function

open scoped ENNReal

noncomputable section

namespace LocalGraphProjectionMass

variable {n : ℕ}

/- English proof (translation)
Establish `hP : ∀ z, frameProj (c.map b.repr) I (b.repr z) = frameProj c I z`. Introduce `z`. Use function extensionality and compare the values at `i`. Simplify using `only [frameProj, OrthonormalBasis.map_apply, LinearIsometryEquiv.inner_map_map]`. Establish `h : {y ∈ b.repr '' A | frameProj (c.map b.repr) I y = x} = b.repr '' {z ∈ A | frameProj c I z = x}`.

Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨z, hz, rfl⟩, hy⟩`. Conclude with `⟨z, ⟨hz, by rwa [hP] at hy⟩, rfl⟩`. Introduce and unpack `⟨z, ⟨hz, hzx⟩, rfl⟩`.

Conclude with `⟨⟨z, hz, rfl⟩, by rw [hP]; exact hzx⟩`. Simplify using `only [frameFibreCount]`. Rewrite using `[h, b.repr.injective.injOn.encard_image]`.
-/
theorem frameFibreCount_image_repr_map (b c : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (I : Finset (Fin n)) (A : Set (EuclideanSpace ℂ (Fin n))) (x : I → ℂ) :
    frameFibreCount (c.map b.repr) I (b.repr '' A) x = frameFibreCount c I A x := by
  have hP : ∀ z, frameProj (c.map b.repr) I (b.repr z) = frameProj c I z := by
    intro z
    funext i
    simp only [frameProj, OrthonormalBasis.map_apply, LinearIsometryEquiv.inner_map_map]
  have h : {y ∈ b.repr '' A | frameProj (c.map b.repr) I y = x} =
      b.repr '' {z ∈ A | frameProj c I z = x} := by
    ext y
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, hy⟩
      exact ⟨z, ⟨hz, by rwa [hP] at hy⟩, rfl⟩
    · rintro ⟨z, ⟨hz, hzx⟩, rfl⟩
      exact ⟨⟨z, hz, rfl⟩, by rw [hP]; exact hzx⟩
  simp only [frameFibreCount]
  rw [h, b.repr.injective.injOn.encard_image]

/- English proof (translation)
Take `⟨m, e, Ω', F, hΩ', hF, himg⟩` from `LocalGraphMass.image_repr_eq_graph b I₀ hd Ω g hΩ hg hfix`. Establish `hT : b.repr '' (g '' Ω ∩ M) = graphPt e F '' Ω' ∩ b.repr '' M`. Rewrite using `[Set.image_inter b.repr.injective, himg]`. Establish `hM' : MeasurableSet (b.repr '' M)` using `b.repr.toHomeomorph.measurableEmbedding.measurableSet_image.2 hM`. Establish `h` using `hPF d m n e Ω' F hΩ' hF (c.map b.repr) _ hM'`.

Rewrite `h` using `[← hT, b.repr.isometry.hausdorffMeasure_image (Or.inr b.repr.surjective)]`. Rewrite using `[h]`. Repeatedly rewrite using `[frameFibreCount_image_repr_map]`.
-/
theorem mass_piece_frame (hPF : ProjectionFormula.Statement)
    (b c : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) (I₀ : Finset (Fin n)) {d : ℕ}
    (hd : I₀.card = d) (Ω : Set (I₀ → ℂ)) (g : (I₀ → ℂ) → EuclideanSpace ℂ (Fin n))
    (hΩ : IsOpen Ω) (hg : DifferentiableOn ℂ g Ω) (hfix : ∀ w ∈ Ω, frameProj b I₀ (g w) = w)
    (M : Set (EuclideanSpace ℂ (Fin n))) (hM : MeasurableSet M) :
    μH[((2 * d : ℕ) : ℝ)] (g '' Ω ∩ M) =
      ∑ I ∈ Finset.univ.powersetCard d, ∫⁻ x : EuclideanSpace ℂ I,
        frameFibreCount c I (g '' Ω ∩ M) (WithLp.ofLp x) ∂(μH[((2 * d : ℕ) : ℝ)]) := by
  obtain ⟨m, e, Ω', F, hΩ', hF, himg⟩ := LocalGraphMass.image_repr_eq_graph b I₀ hd Ω g hΩ hg hfix
  have hT : b.repr '' (g '' Ω ∩ M) = graphPt e F '' Ω' ∩ b.repr '' M := by
    rw [Set.image_inter b.repr.injective, himg]
  have hM' : MeasurableSet (b.repr '' M) :=
    b.repr.toHomeomorph.measurableEmbedding.measurableSet_image.2 hM
  have h := hPF d m n e Ω' F hΩ' hF (c.map b.repr) _ hM'
  rw [← hT, b.repr.isometry.hausdorffMeasure_image (Or.inr b.repr.surjective)] at h
  rw [h]
  simp_rw [frameFibreCount_image_repr_map]

/- English proof (translation)
Use `set e := I.orderIsoOfFin hI`. Use `set s : Fin d → Fin n := ⇑(I.orderEmbOfFin hI) with hs`. Set `φ : EuclideanSpace ℂ I ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin d)` to `LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e.toEquiv.symm`. Establish `hφ : ∀ x k, φ x k = x (e k)` using `fun x k => rfl`. Establish `hrow : ∀ z k, rowsProj U s z k = inner ℂ (c (e k)) z`.

Introduce `z k`. Rewrite using `[hc]`. Simplify using `[rowsProj, Matrix.mulVec, dotProduct, s, e, Finset.coe_orderIsoOfFin_apply]`. Establish `hiff : ∀ x z, frameProj c I z = WithLp.ofLp x ↔ rowsProj U s z = φ x`. Introduce `x z`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Use extensionality with `k`. Rewrite using `[hrow, hφ]`. Conclude with `congrFun h (e k)`.

Introduce `h`. Use function extensionality and compare the values at `i`. Use `congrArg (fun y : EuclideanSpace ℂ (Fin d) => y (e.symm i)) h` as an intermediate fact. Simplify using `only [hrow, hφ, OrderIso.apply_symm_apply] at this`. Conclude with `this`.

Use `set T := rowsProj U s '' A`. Use `set N := ⨆ y : EuclideanSpace ℂ (Fin d), (({z | z ∈ A ∧ rowsProj U s z = y}.encard : ℕ∞) : ℝ≥0∞)`. Establish `hle : ∀ x : EuclideanSpace ℂ I, frameFibreCount c I A (WithLp.ofLp x) ≤ (φ ⁻¹' toMeasurable (μH[((2 * d : ℕ) : ℝ)] : Measure (EuclideanSpace ℂ (Fin d))) T).indicator (fun _ => N) x`. Introduce `x`. Establish `hset : {z ∈ A | frameProj c I z = WithLp.ofLp x} = {z | z ∈ A ∧ rowsProj U s z = φ x}`.

Use extensionality with `z`. Conclude with `and_congr Iff.rfl (hiff x z)`. Distinguish the cases in `hx : φ x ∈ T`. Rewrite using `[Set.indicator_of_mem (show x ∈ φ ⁻¹' toMeasurable (μH[((2 * d : ℕ) : ℝ)] : Measure (EuclideanSpace ℂ (Fin d))) T from subset_toMeasurable _ T hx)]`. Simplify using `only [frameFibreCount]`.

Rewrite using `[hset]`. Conclude with `le_iSup (fun y => (({z | z ∈ A ∧ rowsProj U s z = y}.encard : ℕ∞) : ℝ≥0∞)) (φ x)`. Establish `h0 : {z ∈ A | frameProj c I z = WithLp.ofLp x} = ∅`. Rewrite using `[hset]`. Conclude with `Set.eq_empty_of_forall_notMem fun z hz => hx ⟨z, hz.1, hz.2⟩`.

Simplify using `only [frameFibreCount]`. Rewrite using `[h0]`. Simplify using the standard rewrite rules. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[φ.isometry.hausdorffMeasure_preimage (Or.inr φ.surjective), φ.surjective.range_eq, Set.inter_univ, measure_toMeasurable]`.
-/
theorem lintegral_count_le (U : Matrix (Fin n) (Fin n) ℂ)
    (c : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (hc : ∀ i (z : EuclideanSpace ℂ (Fin n)), inner ℂ (c i) z = ∑ j, U i j * z j)
    {d : ℕ} (I : Finset (Fin n)) (hI : I.card = d) (A : Set (EuclideanSpace ℂ (Fin n))) :
    ∫⁻ x : EuclideanSpace ℂ I, frameFibreCount c I A (WithLp.ofLp x) ∂(μH[((2 * d : ℕ) : ℝ)]) ≤
      (⨆ y : EuclideanSpace ℂ (Fin d),
          (({z | z ∈ A ∧ rowsProj U (I.orderEmbOfFin hI) z = y}.encard : ℕ∞) : ℝ≥0∞)) *
        μH[((2 * d : ℕ) : ℝ)] (rowsProj U (I.orderEmbOfFin hI) '' A) := by
  set e := I.orderIsoOfFin hI
  set s : Fin d → Fin n := ⇑(I.orderEmbOfFin hI) with hs
  let φ : EuclideanSpace ℂ I ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin d) :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e.toEquiv.symm
  have hφ : ∀ x k, φ x k = x (e k) := fun x k => rfl
  have hrow : ∀ z k, rowsProj U s z k = inner ℂ (c (e k)) z := by
    intro z k
    rw [hc]
    simp [rowsProj, Matrix.mulVec, dotProduct, s, e, Finset.coe_orderIsoOfFin_apply]
  have hiff : ∀ x z, frameProj c I z = WithLp.ofLp x ↔ rowsProj U s z = φ x := by
    intro x z
    constructor
    · intro h
      ext k
      rw [hrow, hφ]
      exact congrFun h (e k)
    · intro h
      funext i
      have := congrArg (fun y : EuclideanSpace ℂ (Fin d) => y (e.symm i)) h
      simp only [hrow, hφ, OrderIso.apply_symm_apply] at this
      exact this
  set T := rowsProj U s '' A
  set N := ⨆ y : EuclideanSpace ℂ (Fin d), (({z | z ∈ A ∧ rowsProj U s z = y}.encard : ℕ∞) : ℝ≥0∞)
  have hle : ∀ x : EuclideanSpace ℂ I, frameFibreCount c I A (WithLp.ofLp x) ≤
      (φ ⁻¹' toMeasurable (μH[((2 * d : ℕ) : ℝ)] : Measure (EuclideanSpace ℂ (Fin d))) T).indicator (fun _ => N) x := by
    intro x
    have hset : {z ∈ A | frameProj c I z = WithLp.ofLp x} = {z | z ∈ A ∧ rowsProj U s z = φ x} := by
      ext z
      exact and_congr Iff.rfl (hiff x z)
    by_cases hx : φ x ∈ T
    · rw [Set.indicator_of_mem (show x ∈ φ ⁻¹' toMeasurable (μH[((2 * d : ℕ) : ℝ)] : Measure (EuclideanSpace ℂ (Fin d))) T from
        subset_toMeasurable _ T hx)]
      simp only [frameFibreCount]
      rw [hset]
      exact le_iSup (fun y => (({z | z ∈ A ∧ rowsProj U s z = y}.encard : ℕ∞) : ℝ≥0∞)) (φ x)
    · have h0 : {z ∈ A | frameProj c I z = WithLp.ofLp x} = ∅ := by
        rw [hset]
        exact Set.eq_empty_of_forall_notMem fun z hz => hx ⟨z, hz.1, hz.2⟩
      simp only [frameFibreCount]
      rw [h0]
      simp
  calc _ ≤ ∫⁻ x : EuclideanSpace ℂ I, (φ ⁻¹' toMeasurable (μH[((2 * d : ℕ) : ℝ)] : Measure (EuclideanSpace ℂ (Fin d))) T).indicator (fun _ => N) x ∂(μH[((2 * d : ℕ) : ℝ)]) :=
        lintegral_mono hle
    _ = N * μH[((2 * d : ℕ) : ℝ)] (φ ⁻¹' toMeasurable (μH[((2 * d : ℕ) : ℝ)] : Measure (EuclideanSpace ℂ (Fin d))) T) :=
        lintegral_indicator_const ((measurableSet_toMeasurable _ _).preimage φ.continuous.measurable) _
    _ = N * μH[((2 * d : ℕ) : ℝ)] T := by
        rw [φ.isometry.hausdorffMeasure_preimage (Or.inr φ.surjective), φ.surjective.range_eq,
          Set.inter_univ, measure_toMeasurable]

end LocalGraphProjectionMass

open LocalGraphProjectionMass in

/- English proof (translation)
Introduce `n d b I₀ S hd hS U hU B hB`. Take `⟨c, hc⟩` from `MassFinite.exists_frame U hU`. Break down `S.eq_empty_or_nonempty with rfl | hne` into its components or cases. Simplify using the standard rewrite rules. Establish `hS' : ∀ z : S, ∃ (Ω : Set (I₀ → ℂ)) (V : Set (EuclideanSpace ℂ (Fin n))) (g : (I₀ → ℂ) → EuclideanSpace ℂ (Fin n)), IsOpen Ω ∧ IsOpen V ∧ (z : EuclideanSpace ℂ (Fin n)) ∈ V ∧ DifferentiableOn ℂ g Ω ∧ (∀ w ∈ Ω, frameProj b I₀ (g w) = w) ∧ S ∩ V = g '' Ω` using `fun z => hS z z.2`.

Use `choose Ω V g hΩ hV hzV hg hfix hSV using hS'`. Take `⟨T, hTc, hTU⟩` from `TopologicalSpace.isOpen_iUnion_countable V hV`. Establish `hmemT : ∀ z ∈ S, ∃ i ∈ T, z ∈ V i`. Introduce `z hz`. Establish `: z ∈ ⋃ i ∈ T, V i` using `hTU ▸ Set.mem_iUnion.2 ⟨⟨z, hz⟩, hzV _⟩`.

Take `⟨i, hi, hzi⟩` from `Set.mem_iUnion₂.1 this`. Conclude with `⟨i, hi, hzi⟩`. Establish `hTne : T.Nonempty`. Take `⟨z, hz⟩` from `hne`. Take `⟨i, hi, -⟩` from `hmemT z hz`.

Conclude with `⟨i, hi⟩`. Take `⟨f, hf⟩` from `hTc.exists_eq_range hTne`. Set `W : ℕ → Set (EuclideanSpace ℂ (Fin n))` to `fun k => V (f k)`. Establish `hcover : S ⊆ ⋃ k, disjointed W k`. Introduce `z hz`.

Rewrite using `[iUnion_disjointed]`. Take `⟨i, hi, hzi⟩` from `hmemT z hz`. Rewrite `hi` using `[hf]`. Take `⟨k, rfl⟩` from `hi`. Conclude with `Set.mem_iUnion.2 ⟨k, hzi⟩`.

Establish `hDmeas : ∀ k, MeasurableSet (disjointed W k)` using `MeasurableSet.disjointed fun k => (hV _).measurableSet`. Establish `hpiece : ∀ k, S ∩ B ∩ disjointed W k = g (f k) '' Ω (f k) ∩ (B ∩ disjointed W k)`. Introduce `k`. Rewrite using `[← hSV (f k)]`. Use extensionality with `z`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨hzS, hzB⟩, hzD⟩`. Conclude with `⟨⟨hzS, disjointed_subset W k hzD⟩, hzB, hzD⟩`. Introduce and unpack `⟨⟨hzS, -⟩, hzB, hzD⟩`. Conclude with `⟨⟨hzS, hzB⟩, hzD⟩`.

Establish `hdisj : Pairwise (Disjoint on fun k => S ∩ B ∩ disjointed W k)` using `fun i j hij => (disjoint_disjointed W hij).mono Set.inter_subset_right Set.inter_subset_right`. Set `G : (Fin d → Fin n) → ℝ≥0∞` to `fun s => (⨆ x : EuclideanSpace ℂ (Fin d), (({z | z ∈ S ∩ B ∧ rowsProj U s z = x}.encard : ℕ∞) : ℝ≥0∞)) * μH[((2 * d : ℕ) : ℝ)] (rowsProj U s '' (S ∩ B))`. Combine the equalities or inequalities in the displayed calculation. Use `measure_mono fun z hz => ?_` and prove the remaining obligations. Take `⟨k, hk⟩` from `Set.mem_iUnion.1 (hcover hz.1)`.

Conclude with `Set.mem_iUnion.2 ⟨k, hz, hk⟩`. Use `_ ≤ ∑' k, μH[((2 * d : ℕ) : ℝ)] (S ∩ B ∩ disjointed W k) := measure_iUnion_le _`. Use `_ = ∑' k, ∑ I ∈ Finset.univ.powersetCard d, ∫⁻ x : EuclideanSpace ℂ I, frameFibreCount c I (S ∩ B ∩ disjointed W k) (WithLp.ofLp x) ∂(μH[((2 * d : ℕ) : ℝ)]) := by`. Use `congr 1`. Use function extensionality and compare the values at `k`.

Rewrite using `[hpiece k]`. Conclude with `mass_piece_frame hPF b c I₀ hd _ _ (hΩ _) (hg _) (hfix _) _ (hB.inter (hDmeas k))`. Use `_ = ∑ I ∈ Finset.univ.powersetCard d, ∑' k, ∫⁻ x : EuclideanSpace ℂ I, frameFibreCount c I (S ∩ B ∩ disjointed W k) (WithLp.ofLp x) ∂(μH[((2 * d : ℕ) : ℝ)]) := Summable.tsum_finsetSum fun _ _ => ENNReal.summable`. Use `_ ≤ ∑ I ∈ Finset.univ.powersetCard d, ⨆ hI : I.card = d, G (I.orderEmbOfFin hI) := by`. Use `Finset.sum_le_sum fun I hI => ?_` and prove the remaining obligations.

Establish `hIc` using `(Finset.mem_powersetCard.1 hI).2`. Use `le_trans ?_ (le_iSup (fun h : I.card = d => G (I.orderEmbOfFin h)) hIc)` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Use `_ = ∑ s ∈ Finset.univ.filter (fun s : Fin d → Fin n => StrictMono s), G s := by`. Use `Finset.sum_bij (fun I hI => ⇑(I.orderEmbOfFin (Finset.mem_powersetCard.1 hI).2)) (fun I hI => Finset.mem_filter.2 ⟨Finset.mem_univ _, (I.orderEmbOfFin _).strictMono⟩) (fun I₁ hI₁ I₂ hI₂ h => ?_) (fun t ht => ?_) (fun I hI => ?_)` and prove the remaining obligations.

Use `congrArg Set.range h` as an intermediate fact. Rewrite `this` using `[Finset.range_orderEmbOfFin, Finset.range_orderEmbOfFin]`. Conclude with `Finset.coe_inj.1 this`. Establish `hmono` using `(Finset.mem_filter.1 ht).2`. Establish `hcard : (Finset.univ.image t).card = d`.

Rewrite using `[Finset.card_image_of_injective _ hmono.injective, Finset.card_univ, Fintype.card_fin]`. Use `⟨Finset.univ.image t, Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, hcard⟩, ?_⟩` and prove the remaining obligations. Conclude with `(Finset.orderEmbOfFin_unique hcard (fun x => Finset.mem_image_of_mem t (Finset.mem_univ x)) hmono).symm`. Conclude with `iSup_pos (Finset.mem_powersetCard.1 hI).2`.
-/
theorem LocalGraphProjectionMass.proof (hPF : ProjectionFormula.Statement) :
    LocalGraphProjectionMass.Statement := by
  intro n d b I₀ S hd hS U hU B hB
  classical
  obtain ⟨c, hc⟩ := MassFinite.exists_frame U hU
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp
  have hS' : ∀ z : S, ∃ (Ω : Set (I₀ → ℂ)) (V : Set (EuclideanSpace ℂ (Fin n)))
      (g : (I₀ → ℂ) → EuclideanSpace ℂ (Fin n)), IsOpen Ω ∧ IsOpen V ∧ (z : EuclideanSpace ℂ (Fin n)) ∈ V ∧
        DifferentiableOn ℂ g Ω ∧ (∀ w ∈ Ω, frameProj b I₀ (g w) = w) ∧ S ∩ V = g '' Ω :=
    fun z => hS z z.2
  choose Ω V g hΩ hV hzV hg hfix hSV using hS'
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable V hV
  have hmemT : ∀ z ∈ S, ∃ i ∈ T, z ∈ V i := by
    intro z hz
    have : z ∈ ⋃ i ∈ T, V i := hTU ▸ Set.mem_iUnion.2 ⟨⟨z, hz⟩, hzV _⟩
    obtain ⟨i, hi, hzi⟩ := Set.mem_iUnion₂.1 this
    exact ⟨i, hi, hzi⟩
  have hTne : T.Nonempty := by
    obtain ⟨z, hz⟩ := hne
    obtain ⟨i, hi, -⟩ := hmemT z hz
    exact ⟨i, hi⟩
  obtain ⟨f, hf⟩ := hTc.exists_eq_range hTne
  let W : ℕ → Set (EuclideanSpace ℂ (Fin n)) := fun k => V (f k)
  have hcover : S ⊆ ⋃ k, disjointed W k := by
    intro z hz
    rw [iUnion_disjointed]
    obtain ⟨i, hi, hzi⟩ := hmemT z hz
    rw [hf] at hi
    obtain ⟨k, rfl⟩ := hi
    exact Set.mem_iUnion.2 ⟨k, hzi⟩
  have hDmeas : ∀ k, MeasurableSet (disjointed W k) :=
    MeasurableSet.disjointed fun k => (hV _).measurableSet
  have hpiece : ∀ k, S ∩ B ∩ disjointed W k = g (f k) '' Ω (f k) ∩ (B ∩ disjointed W k) := by
    intro k
    rw [← hSV (f k)]
    ext z
    constructor
    · rintro ⟨⟨hzS, hzB⟩, hzD⟩
      exact ⟨⟨hzS, disjointed_subset W k hzD⟩, hzB, hzD⟩
    · rintro ⟨⟨hzS, -⟩, hzB, hzD⟩
      exact ⟨⟨hzS, hzB⟩, hzD⟩
  have hdisj : Pairwise (Disjoint on fun k => S ∩ B ∩ disjointed W k) :=
    fun i j hij => (disjoint_disjointed W hij).mono Set.inter_subset_right Set.inter_subset_right
  let G : (Fin d → Fin n) → ℝ≥0∞ := fun s =>
    (⨆ x : EuclideanSpace ℂ (Fin d),
        (({z | z ∈ S ∩ B ∧ rowsProj U s z = x}.encard : ℕ∞) : ℝ≥0∞)) *
      μH[((2 * d : ℕ) : ℝ)] (rowsProj U s '' (S ∩ B))
  calc μH[((2 * d : ℕ) : ℝ)] (S ∩ B)
      ≤ μH[((2 * d : ℕ) : ℝ)] (⋃ k, S ∩ B ∩ disjointed W k) := by
        refine measure_mono fun z hz => ?_
        obtain ⟨k, hk⟩ := Set.mem_iUnion.1 (hcover hz.1)
        exact Set.mem_iUnion.2 ⟨k, hz, hk⟩
    _ ≤ ∑' k, μH[((2 * d : ℕ) : ℝ)] (S ∩ B ∩ disjointed W k) := measure_iUnion_le _
    _ = ∑' k, ∑ I ∈ Finset.univ.powersetCard d, ∫⁻ x : EuclideanSpace ℂ I,
          frameFibreCount c I (S ∩ B ∩ disjointed W k) (WithLp.ofLp x) ∂(μH[((2 * d : ℕ) : ℝ)]) := by
        congr 1
        funext k
        rw [hpiece k]
        exact mass_piece_frame hPF b c I₀ hd _ _ (hΩ _) (hg _) (hfix _) _ (hB.inter (hDmeas k))
    _ = ∑ I ∈ Finset.univ.powersetCard d, ∑' k, ∫⁻ x : EuclideanSpace ℂ I,
          frameFibreCount c I (S ∩ B ∩ disjointed W k) (WithLp.ofLp x) ∂(μH[((2 * d : ℕ) : ℝ)]) :=
        Summable.tsum_finsetSum fun _ _ => ENNReal.summable
    _ ≤ ∑ I ∈ Finset.univ.powersetCard d, ⨆ hI : I.card = d, G (I.orderEmbOfFin hI) := by
        refine Finset.sum_le_sum fun I hI => ?_
        have hIc := (Finset.mem_powersetCard.1 hI).2
        refine le_trans ?_ (le_iSup (fun h : I.card = d => G (I.orderEmbOfFin h)) hIc)
        calc _ ≤ ∫⁻ x : EuclideanSpace ℂ I, ∑' k,
              frameFibreCount c I (S ∩ B ∩ disjointed W k) (WithLp.ofLp x) ∂(μH[((2 * d : ℕ) : ℝ)]) :=
              LocalGraphMass.tsum_lintegral_le _ _
          _ ≤ ∫⁻ x : EuclideanSpace ℂ I, frameFibreCount c I (S ∩ B) (WithLp.ofLp x)
                ∂(μH[((2 * d : ℕ) : ℝ)]) :=
              lintegral_mono fun x =>
                LocalGraphMass.tsum_frameFibreCount_le c I _ (fun k => Set.inter_subset_left) hdisj _
          _ ≤ G (I.orderEmbOfFin hIc) := lintegral_count_le U c hc I hIc (S ∩ B)
    _ = ∑ s ∈ Finset.univ.filter (fun s : Fin d → Fin n => StrictMono s), G s := by
        refine Finset.sum_bij (fun I hI => ⇑(I.orderEmbOfFin (Finset.mem_powersetCard.1 hI).2))
          (fun I hI => Finset.mem_filter.2 ⟨Finset.mem_univ _, (I.orderEmbOfFin _).strictMono⟩)
          (fun I₁ hI₁ I₂ hI₂ h => ?_) (fun t ht => ?_) (fun I hI => ?_)
        · have := congrArg Set.range h
          rw [Finset.range_orderEmbOfFin, Finset.range_orderEmbOfFin] at this
          exact Finset.coe_inj.1 this
        · have hmono := (Finset.mem_filter.1 ht).2
          have hcard : (Finset.univ.image t).card = d := by
            rw [Finset.card_image_of_injective _ hmono.injective, Finset.card_univ, Fintype.card_fin]
          refine ⟨Finset.univ.image t, Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, hcard⟩, ?_⟩
          exact (Finset.orderEmbOfFin_unique hcard
            (fun x => Finset.mem_image_of_mem t (Finset.mem_univ x)) hmono).symm
        · exact iSup_pos (Finset.mem_powersetCard.1 hI).2

end

end GroundTheory.Heights₂.Heights
