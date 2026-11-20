import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BorelParam
open MeasureTheory Pointwise

namespace GlobalTheory

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`. Simplify `hy` using `[MulAut.conj_apply, mul_assoc]`. Introduce `h`. Conclude with `⟨g⁻¹ * x * g, h, by simp [MulAut.conj_apply, mul_assoc]⟩`.
-/
theorem mem_map_conj_iff_conj_mem {G : Type} [Group G] (J : Subgroup G) (g x : G) :
    x ∈ J.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ J := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · intro h
    exact ⟨g⁻¹ * x * g, h, by simp [MulAut.conj_apply, mul_assoc]⟩

/- English proof (translation)
Introduce `G _ _ _ _ _ μ _ J hJo hJc g`. Use `set K := J.map (MulAut.conj g).toMonoidHom with hK`. Use `set H : Subgroup J := K.subgroupOf J with hH`. Use `haveI : CompactSpace J := isCompact_iff_compactSpace.1 hJc`. Establish `hKo : IsOpen (K : Set G)`.

Establish `: (K : Set G) = (fun x => g⁻¹ * x * g) ⁻¹' (J : Set G)`. Use extensionality with `x`. Rewrite using `[SetLike.mem_coe, hK, mem_map_conj_iff_conj_mem]`. Both sides reduce to the same expression. Rewrite using `[this]; exact hJo.preimage (by fun_prop)`.

Establish `hHo : IsOpen (H : Set J)`. Establish `: (H : Set J) = Subtype.val ⁻¹' (K : Set G)`. Use extensionality with `x`. Simplify using `[hH, Subgroup.mem_subgroupOf]`. Rewrite using `[this]`.

Conclude with `hKo.preimage continuous_subtype_val`. Use `haveI : Finite (J ⧸ H) := Subgroup.quotient_finite_of_isOpen H hHo`. Use `letI : Fintype (J ⧸ H) := Fintype.ofFinite _`. Set `f : J ⧸ H → Set G` to `fun q => ((q.out : J) * g : G) • (J : Set G)`. Establish `hcover : DoubleCoset.doubleCoset g (J : Set G) (J : Set G) = ⋃ q, f q`.

Use extensionality with `x`. Simplify using `only [DoubleCoset.doubleCoset, Set.mem_mul, Set.mem_singleton_iff, Set.mem_iUnion, f, Set.mem_smul_set, smul_eq_mul, SetLike.mem_coe]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, ⟨j, hj, b, hb, rfl⟩, k, hk, rfl⟩`. Rewrite using `[hb]`.

Use `⟨(QuotientGroup.mk (⟨j, hj⟩ : J) : J ⧸ H), ?_⟩` and prove the remaining obligations. Use `set o := (Quotient.out (QuotientGroup.mk (⟨j, hj⟩ : J) : J ⧸ H) : J) with ho`. Establish `h1 : (QuotientGroup.mk o : J ⧸ H) = QuotientGroup.mk (⟨j, hj⟩ : J)` using `QuotientGroup.out_eq' _`. Rewrite `h1` using `[QuotientGroup.eq]`. Establish `h2 : ((o : G))⁻¹ * j ∈ K`.

Use `Subgroup.mem_subgroupOf.1 (hH ▸ h1)` as an intermediate fact. Simplify using `using this`. Rewrite `h2` using `[hK, mem_map_conj_iff_conj_mem]`. Use `⟨g⁻¹ * ((o : G)⁻¹ * j) * g * k, J.mul_mem h2 hk, ?_⟩` and prove the remaining obligations. Use `group`.

Introduce and unpack `⟨q, y, hy, rfl⟩`. Conclude with `⟨(q.out : J) * g, ⟨(q.out : J), (q.out : J).2, g, rfl, rfl⟩, y, hy, rfl⟩`. Establish `hdisj : Pairwise (Function.onFun Disjoint f)`. Introduce `q q' hqq'`. Use `Set.disjoint_left.2 ?_` and prove the remaining obligations.

Introduce and unpack `x hx hx'`. Simplify using `only [f, Set.mem_smul_set, smul_eq_mul, SetLike.mem_coe] at hx hx'`. Take `⟨y, hy, rfl⟩` from `hx`. Take `⟨y', hy', hxy⟩` from `hx'`. Apply `hqq'` to reduce the goal to its premises.

Establish `e : ((q.out : J) : G) = (q'.out : J) * g * y' * y⁻¹ * g⁻¹`. Rewrite using `[hxy]`. Use `group`. Establish `hmem : (q.out)⁻¹ * q'.out ∈ H`. Express the relevant statement in the definitionally equal form `_ ∈ K.subgroupOf J`.

Rewrite using `[Subgroup.mem_subgroupOf, hK, mem_map_conj_iff_conj_mem]`. Simplify using `only [Subgroup.coe_mul, Subgroup.coe_inv]`. Rewrite using `[e]`. Establish `: g⁻¹ * ((((q'.out : J) : G) * g * y' * y⁻¹ * g⁻¹)⁻¹ * (q'.out : J)) * g = y * y'⁻¹` using `by group`. Rewrite using `[this]`.

Conclude with `J.mul_mem hy (J.inv_mem hy')`. Use `(QuotientGroup.eq (s := H)).2 hmem` as an intermediate fact. Rewrite `this` using `[QuotientGroup.out_eq', QuotientGroup.out_eq']`. Then use the resulting hypothesis. Establish `hmeas : ∀ q, MeasurableSet (f q)` using `fun q => (hJo.smul ((q.out : J) * g : G)).measurableSet`. Establish `hval : ∀ q, μ (f q) = μ (J : Set G)` using `fun q => measure_smul μ _ _`.

Establish `hfin : μ (J : Set G) ≠ ⊤` using `(hJc.measure_lt_top).ne`. Rewrite using `[hcover, measureReal_def, measure_iUnion hdisj hmeas, tsum_fintype]`. Simplify using `only [hval, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]`. Rewrite using `[ENNReal.toReal_mul, ENNReal.toReal_natCast, measureReal_def, Subgroup.relIndex, Subgroup.index_eq_card, Nat.card_eq_fintype_card]`.
-/
theorem measureReal_doubleCoset_eq_relIndex_mul :
    ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (J : Subgroup G), IsOpen (J : Set G) → IsCompact (J : Set G) → ∀ g : G,
    μ.real (DoubleCoset.doubleCoset g (J : Set G) (J : Set G)) =
      ((J.map (MulAut.conj g).toMonoidHom).relIndex J : ℝ) * μ.real (J : Set G) := by
  intro G _ _ _ _ _ μ _ J hJo hJc g
  set K := J.map (MulAut.conj g).toMonoidHom with hK
  set H : Subgroup J := K.subgroupOf J with hH
  haveI : CompactSpace J := isCompact_iff_compactSpace.1 hJc
  have hKo : IsOpen (K : Set G) := by
    have : (K : Set G) = (fun x => g⁻¹ * x * g) ⁻¹' (J : Set G) := by
      ext x; rw [SetLike.mem_coe, hK, mem_map_conj_iff_conj_mem]; rfl
    rw [this]; exact hJo.preimage (by fun_prop)
  have hHo : IsOpen (H : Set J) := by
    have : (H : Set J) = Subtype.val ⁻¹' (K : Set G) := by
      ext x; simp [hH, Subgroup.mem_subgroupOf]
    rw [this]; exact hKo.preimage continuous_subtype_val
  haveI : Finite (J ⧸ H) := Subgroup.quotient_finite_of_isOpen H hHo
  letI : Fintype (J ⧸ H) := Fintype.ofFinite _
  let f : J ⧸ H → Set G := fun q => ((q.out : J) * g : G) • (J : Set G)
  have hcover : DoubleCoset.doubleCoset g (J : Set G) (J : Set G) = ⋃ q, f q := by
    ext x
    simp only [DoubleCoset.doubleCoset, Set.mem_mul, Set.mem_singleton_iff, Set.mem_iUnion, f,
      Set.mem_smul_set, smul_eq_mul, SetLike.mem_coe]
    constructor
    · rintro ⟨a, ⟨j, hj, b, hb, rfl⟩, k, hk, rfl⟩
      rw [hb]
      refine ⟨(QuotientGroup.mk (⟨j, hj⟩ : J) : J ⧸ H), ?_⟩
      set o := (Quotient.out (QuotientGroup.mk (⟨j, hj⟩ : J) : J ⧸ H) : J) with ho
      have h1 : (QuotientGroup.mk o : J ⧸ H) = QuotientGroup.mk (⟨j, hj⟩ : J) := QuotientGroup.out_eq' _
      rw [QuotientGroup.eq] at h1
      have h2 : ((o : G))⁻¹ * j ∈ K := by
        have := Subgroup.mem_subgroupOf.1 (hH ▸ h1)
        simpa using this
      rw [hK, mem_map_conj_iff_conj_mem] at h2
      refine ⟨g⁻¹ * ((o : G)⁻¹ * j) * g * k, J.mul_mem h2 hk, ?_⟩
      group
    · rintro ⟨q, y, hy, rfl⟩
      exact ⟨(q.out : J) * g, ⟨(q.out : J), (q.out : J).2, g, rfl, rfl⟩, y, hy, rfl⟩
  have hdisj : Pairwise (Function.onFun Disjoint f) := by
    intro q q' hqq'
    refine Set.disjoint_left.2 ?_
    rintro x hx hx'
    simp only [f, Set.mem_smul_set, smul_eq_mul, SetLike.mem_coe] at hx hx'
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨y', hy', hxy⟩ := hx'
    apply hqq'
    have e : ((q.out : J) : G) = (q'.out : J) * g * y' * y⁻¹ * g⁻¹ := by
      rw [hxy]; group
    have hmem : (q.out)⁻¹ * q'.out ∈ H := by
      change _ ∈ K.subgroupOf J
      rw [Subgroup.mem_subgroupOf, hK, mem_map_conj_iff_conj_mem]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [e]
      have : g⁻¹ * ((((q'.out : J) : G) * g * y' * y⁻¹ * g⁻¹)⁻¹ * (q'.out : J)) * g = y * y'⁻¹ := by group
      rw [this]
      exact J.mul_mem hy (J.inv_mem hy')
    have := (QuotientGroup.eq (s := H)).2 hmem
    rwa [QuotientGroup.out_eq', QuotientGroup.out_eq'] at this
  have hmeas : ∀ q, MeasurableSet (f q) := fun q =>
    (hJo.smul ((q.out : J) * g : G)).measurableSet
  have hval : ∀ q, μ (f q) = μ (J : Set G) := fun q => measure_smul μ _ _
  have hfin : μ (J : Set G) ≠ ⊤ := (hJc.measure_lt_top).ne
  rw [hcover, measureReal_def, measure_iUnion hdisj hmeas, tsum_fintype]
  simp only [hval, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, measureReal_def, Subgroup.relIndex,
    Subgroup.index_eq_card, Nat.card_eq_fintype_card]

end GlobalTheory
