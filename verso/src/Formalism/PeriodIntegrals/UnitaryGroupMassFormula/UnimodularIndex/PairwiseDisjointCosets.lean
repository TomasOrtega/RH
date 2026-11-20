import Mathlib
import Formalism.PeriodIntegrals.UnimodIdx

open MeasureTheory Measure Topology Pointwise Set Function

noncomputable section

namespace PI.UnimodIdxWork

section Cosets

variable {G : Type} [Group G]

/- English proof (translation)
Use extensionality with `y`. Simplify using `only [Set.mem_iUnion, SetLike.mem_coe]`. Prove the components needed by the constructor for the conclusion. Introduce `hy`. Take `⟨h, hh⟩` from `QuotientGroup.mk_out_eq_mul (A.subgroupOf H) (⟨y, hy⟩ : H)`.

Use `⟨(QuotientGroup.mk (⟨y, hy⟩ : H) : H ⧸ A.subgroupOf H), Set.mem_smul_set.mpr ⟨(((QuotientGroup.mk (⟨y, hy⟩ : H) : H ⧸ A.subgroupOf H).out : H) : G)⁻¹ * y, ?_, by simp [smul_eq_mul]⟩⟩` and prove the remaining obligations. Establish `hG : (((QuotientGroup.mk (⟨y, hy⟩ : H) : H ⧸ A.subgroupOf H).out : H) : G) = y * ((h : H) : G)`. Use `congrArg (fun x : H => (x : G)) hh` as an intermediate fact. Simplify using `using this`. Establish `hA : ((h : H) : G) ∈ A` using `Subgroup.mem_subgroupOf.mp h.2`.

Establish `hH : ((h : H) : G) ∈ H` using `(h : H).2`. Rewrite using `[hG, mul_inv_rev, inv_mul_cancel_right]`. Conclude with `(SetLike.mem_coe).mpr (Subgroup.mem_inf.mpr ⟨A.inv_mem hA, H.inv_mem hH⟩)`. Introduce and unpack `⟨q, hq⟩`. Take `⟨z, hz, rfl⟩` from `Set.mem_smul_set.mp hq`.

Establish `hz' : z ∈ A ⊓ H` using `hz`. Conclude with `H.mul_mem (q.out : H).2 (Subgroup.mem_inf.mp hz').2`.
-/
lemma subgroup_eq_iUnion (A H : Subgroup G) :
    (H : Set G) = ⋃ q : H ⧸ A.subgroupOf H, ((q.out : H) : G) • ((A ⊓ H : Subgroup G) : Set G) := by
  ext y
  simp only [Set.mem_iUnion, SetLike.mem_coe]
  constructor
  · intro hy
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (A.subgroupOf H) (⟨y, hy⟩ : H)
    refine ⟨(QuotientGroup.mk (⟨y, hy⟩ : H) : H ⧸ A.subgroupOf H),
      Set.mem_smul_set.mpr ⟨(((QuotientGroup.mk (⟨y, hy⟩ : H) : H ⧸ A.subgroupOf H).out : H) : G)⁻¹ * y,
        ?_, by simp [smul_eq_mul]⟩⟩
    have hG : (((QuotientGroup.mk (⟨y, hy⟩ : H) : H ⧸ A.subgroupOf H).out : H) : G)
        = y * ((h : H) : G) := by
      have := congrArg (fun x : H => (x : G)) hh
      simpa using this
    have hA : ((h : H) : G) ∈ A := Subgroup.mem_subgroupOf.mp h.2
    have hH : ((h : H) : G) ∈ H := (h : H).2
    rw [hG, mul_inv_rev, inv_mul_cancel_right]
    exact (SetLike.mem_coe).mpr (Subgroup.mem_inf.mpr ⟨A.inv_mem hA, H.inv_mem hH⟩)
  · rintro ⟨q, hq⟩
    obtain ⟨z, hz, rfl⟩ := Set.mem_smul_set.mp hq
    have hz' : z ∈ A ⊓ H := hz
    exact H.mul_mem (q.out : H).2 (Subgroup.mem_inf.mp hz').2

/- English proof (translation)
Introduce `p q hpq`. Use `Set.disjoint_left.mpr ?_` and prove the remaining obligations. Introduce `y hy1 hy2`. Apply `hpq` to reduce the goal to its premises. Take `⟨a, ha, ha'⟩` from `Set.mem_smul_set.mp hy1`.

Take `⟨b, hb, hb'⟩` from `Set.mem_smul_set.mp hy2`. Rewrite `ha'`, `hb'` using `[smul_eq_mul]`. Establish `hpq' : (((p.out : H) : G))⁻¹ * ((q.out : H) : G) = a * b⁻¹`. Rewrite using `[eq_mul_inv_iff_mul_eq, mul_assoc, hb', ← ha', inv_mul_cancel_left]`. Establish `hmem : (p.out : H)⁻¹ * (q.out : H) ∈ A.subgroupOf H`.

Rewrite using `[Subgroup.mem_subgroupOf]`. Use `push_cast`. Rewrite using `[hpq']`. Conclude with `A.mul_mem (Subgroup.mem_inf.mp ha).1 (A.inv_mem (Subgroup.mem_inf.mp hb).1)`. Establish `key : (QuotientGroup.mk (p.out : H) : H ⧸ A.subgroupOf H) = QuotientGroup.mk (q.out : H)` using `QuotientGroup.eq.mpr hmem`.

Rewrite `key` using `[QuotientGroup.out_eq', QuotientGroup.out_eq']`. Then use the resulting hypothesis.
-/
lemma pairwise_disjoint_cosets (A H : Subgroup G) :
    Pairwise (Disjoint on fun q : H ⧸ A.subgroupOf H =>
      ((q.out : H) : G) • ((A ⊓ H : Subgroup G) : Set G)) := by
  intro p q hpq
  refine Set.disjoint_left.mpr ?_
  intro y hy1 hy2
  apply hpq
  obtain ⟨a, ha, ha'⟩ := Set.mem_smul_set.mp hy1
  obtain ⟨b, hb, hb'⟩ := Set.mem_smul_set.mp hy2
  rw [smul_eq_mul] at ha' hb'
  have hpq' : (((p.out : H) : G))⁻¹ * ((q.out : H) : G) = a * b⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq, mul_assoc, hb', ← ha', inv_mul_cancel_left]
  have hmem : (p.out : H)⁻¹ * (q.out : H) ∈ A.subgroupOf H := by
    rw [Subgroup.mem_subgroupOf]
    push_cast
    rw [hpq']
    exact A.mul_mem (Subgroup.mem_inf.mp ha).1 (A.inv_mem (Subgroup.mem_inf.mp hb).1)
  have key : (QuotientGroup.mk (p.out : H) : H ⧸ A.subgroupOf H) = QuotientGroup.mk (q.out : H) :=
    QuotientGroup.eq.mpr hmem
  rwa [QuotientGroup.out_eq', QuotientGroup.out_eq'] at key

/- English proof (translation)
Rewrite using `[Subgroup.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩`. Simplify `hx` using `[mul_assoc]`. Introduce `h`.

Conclude with `⟨g⁻¹ * y * g, h, by simp [mul_assoc]⟩`.
-/
lemma mem_conj_map (K : Subgroup G) (g y : G) :
    y ∈ K.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * y * g ∈ K := by
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa [mul_assoc] using hx
  · intro h
    exact ⟨g⁻¹ * y * g, h, by simp [mul_assoc]⟩

end Cosets

section Measure

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G]

/- English proof (translation)
Establish `hAH : IsOpen ((A ⊓ H : Subgroup G) : Set G)`. Rewrite using `[Subgroup.coe_inf]`. Conclude with `hA.inter hHo`. Establish `hfin : Finite (H ⧸ A.subgroupOf H)`. Take `⟨t, ht⟩` from `hH.elim_finite_subcover (fun q : H ⧸ A.subgroupOf H => ((q.out : H) : G) • ((A ⊓ H : Subgroup G) : Set G)) (fun q => hAH.smul _) (subgroup_eq_iUnion A H).subset`.

Use `Set.finite_univ_iff.mp ((t.finite_toSet).subset fun q _ => ?_)` and prove the remaining obligations. Establish `hq : ((q.out : H) : G) ∈ (H : Set G)` using `(q.out : H).2`. Take `⟨i, hi, hmem⟩` from `Set.mem_iUnion₂.mp (ht hq)`. Establish `hself : ((q.out : H) : G) ∈ ((q.out : H) : G) • ((A ⊓ H : Subgroup G) : Set G)` using `Set.mem_smul_set.mpr ⟨1, (A ⊓ H).one_mem, by simp⟩`. Establish `hiq : i = q`.

Assume the negation of the conclusion as `hne`. Conclude with `Set.disjoint_left.mp (pairwise_disjoint_cosets A H hne) hmem hself`. Rewrite using `[← hiq]`. Conclude with `Finset.mem_coe.mpr hi`. Use `letI := Fintype.ofFinite (H ⧸ A.subgroupOf H)`.

Establish `hcard : A.relIndex H = Fintype.card (H ⧸ A.subgroupOf H)`. Unfold `Subgroup.relIndex Subgroup.index`. Conclude with `Nat.card_eq_fintype_card`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← subgroup_eq_iUnion A H]`.

Use `_ = ∑' q : H ⧸ A.subgroupOf H, μ (((q.out : H) : G) • ((A ⊓ H : Subgroup G) : Set G)) := measure_iUnion (pairwise_disjoint_cosets A H) fun q => (hAH.smul _).measurableSet`. Use `_ = ∑' _q : H ⧸ A.subgroupOf H, μ ((A ⊓ H : Subgroup G) : Set G) := by`. Use `congr 1`. Use function extensionality and compare the values at `q`. Rewrite using `[measure_smul]`.

Use `_ = (A.relIndex H : ENNReal) * μ (A ⊓ H : Subgroup G) := by`. Rewrite using `[tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]`.
-/
lemma measure_subgroup_eq (μ : Measure G) [IsMulLeftInvariant μ] (A H : Subgroup G)
    (hA : IsOpen (A : Set G)) (hH : IsCompact (H : Set G)) (hHo : IsOpen (H : Set G)) :
    μ H = (A.relIndex H : ENNReal) * μ (A ⊓ H : Subgroup G) := by
  have hAH : IsOpen ((A ⊓ H : Subgroup G) : Set G) := by
    rw [Subgroup.coe_inf]; exact hA.inter hHo
  have hfin : Finite (H ⧸ A.subgroupOf H) := by
    obtain ⟨t, ht⟩ := hH.elim_finite_subcover
      (fun q : H ⧸ A.subgroupOf H => ((q.out : H) : G) • ((A ⊓ H : Subgroup G) : Set G))
      (fun q => hAH.smul _) (subgroup_eq_iUnion A H).subset
    refine Set.finite_univ_iff.mp ((t.finite_toSet).subset fun q _ => ?_)
    have hq : ((q.out : H) : G) ∈ (H : Set G) := (q.out : H).2
    obtain ⟨i, hi, hmem⟩ := Set.mem_iUnion₂.mp (ht hq)
    have hself : ((q.out : H) : G) ∈ ((q.out : H) : G) • ((A ⊓ H : Subgroup G) : Set G) :=
      Set.mem_smul_set.mpr ⟨1, (A ⊓ H).one_mem, by simp⟩
    have hiq : i = q := by
      by_contra hne
      exact Set.disjoint_left.mp (pairwise_disjoint_cosets A H hne) hmem hself
    rw [← hiq]
    exact Finset.mem_coe.mpr hi
  letI := Fintype.ofFinite (H ⧸ A.subgroupOf H)
  have hcard : A.relIndex H = Fintype.card (H ⧸ A.subgroupOf H) := by
    unfold Subgroup.relIndex Subgroup.index
    exact Nat.card_eq_fintype_card
  calc μ (H : Set G)
      = μ (⋃ q : H ⧸ A.subgroupOf H, ((q.out : H) : G) • ((A ⊓ H : Subgroup G) : Set G)) := by
        rw [← subgroup_eq_iUnion A H]
    _ = ∑' q : H ⧸ A.subgroupOf H, μ (((q.out : H) : G) • ((A ⊓ H : Subgroup G) : Set G)) :=
        measure_iUnion (pairwise_disjoint_cosets A H) fun q => (hAH.smul _).measurableSet
    _ = ∑' _q : H ⧸ A.subgroupOf H, μ ((A ⊓ H : Subgroup G) : Set G) := by
        congr 1; funext q; rw [measure_smul]
    _ = (A.relIndex H : ENNReal) * μ (A ⊓ H : Subgroup G) := by
        rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]

end Measure

/- English proof (translation)
Use extensionality with `s hs`. Establish `hs' : s = ⋃ i, s ∩ T i` using `by rw [← Set.inter_iUnion, hT, Set.inter_univ]`. Establish `hd' : Pairwise (Disjoint on fun i => s ∩ T i)` using `fun i j hij => (hd hij).mono Set.inter_subset_right Set.inter_subset_right`. Establish `hm' : ∀ i, MeasurableSet (s ∩ T i)` using `fun i => hs.inter (hm i)`. Rewrite using `[hs', measure_iUnion hd' hm', measure_iUnion hd' hm']`.

Conclude with `tsum_congr fun i => h i _ (hm' i) Set.inter_subset_right`.
-/
private theorem measure_eq_of_eq_on_partition {α ι : Type*} [MeasurableSpace α] [Countable ι]
    (μ ν : Measure α) (T : ι → Set α) (hT : ⋃ i, T i = Set.univ) (hd : Pairwise (Disjoint on T))
    (hm : ∀ i, MeasurableSet (T i)) (h : ∀ i s, MeasurableSet s → s ⊆ T i → ν s = μ s) :
    ν = μ := by
  ext s hs
  have hs' : s = ⋃ i, s ∩ T i := by rw [← Set.inter_iUnion, hT, Set.inter_univ]
  have hd' : Pairwise (Disjoint on fun i => s ∩ T i) := fun i j hij =>
    (hd hij).mono Set.inter_subset_right Set.inter_subset_right
  have hm' : ∀ i, MeasurableSet (s ∩ T i) := fun i => hs.inter (hm i)
  rw [hs', measure_iUnion hd' hm', measure_iUnion hd' hm']
  exact tsum_congr fun i => h i _ (hm' i) Set.inter_subset_right

/- English proof (translation)
Establish `hK : (K.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = K`. Use extensionality with `y`. Simplify using `[mul_assoc]`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem relIndex_map_conj_eq_relIndex_map_conj_inv {G : Type} [Group G] (K : Subgroup G) (g : G) :
    K.relIndex (K.map (MulAut.conj g).toMonoidHom)
      = (K.map (MulAut.conj g⁻¹).toMonoidHom).relIndex K := by
  have hK : (K.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = K := by
    ext y
    simp [mul_assoc]
  calc K.relIndex (K.map (MulAut.conj g).toMonoidHom)
      = ((K.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom).relIndex
          (K.map (MulAut.conj g).toMonoidHom) := by rw [hK]
    _ = (K.map (MulAut.conj g⁻¹).toMonoidHom).relIndex K :=
        Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective

/- English proof (translation)
Unfold `PI.UnimodIdx`. Introduce `G _ _ _ _ _ μ _ hμ U hU hUb K hKo hKc hidx`. Establish `: LocallyCompactSpace G` using `hKc.locallyCompactSpace_of_mem_nhds_of_group (hKo.mem_nhds K.one_mem)`. Use `⟨fun g => ?_⟩` and prove the remaining obligations. Establish `hKcl : IsClosed (K : Set G)` using `Subgroup.isClosed_of_isOpen K hKo`.

Establish `hKpos : 0 < μ K` using `hKo.measure_pos μ ⟨1, K.one_mem⟩`. Establish `hKfin : μ K < ⊤` using `hKc.measure_lt_top`. Establish `hinv : IsMulLeftInvariant (map (· * g) μ)`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Combine the equalities or inequalities in the displayed calculation. Use `congr 1`. Use function extensionality and compare the values at `x`. Simplify using `[mul_assoc]`. Use `_ = map (· * g) (map (h * ·) μ) := (map_map (measurable_mul_const g) (measurable_const_mul h)).symm`.

Use `_ = map (· * g) μ := by rw [map_mul_left_eq_self]`. Establish `he : MeasurableEmbedding (fun x : G => x * g)` using `(MeasurableEquiv.mulRight g).measurableEmbedding`. Establish `hfin : IsFiniteMeasureOnCompacts (map (· * g) μ)`. Prove the components needed by the constructor for the conclusion. Introduce `C hC`.

Rewrite using `[he.map_apply]`. Establish `: IsCompact ((fun x : G => x * g) ⁻¹' C)` using `(Homeomorph.mulRight g).isCompact_preimage.mpr hC`. Conclude with `this.measure_lt_top`. Establish `hK'set : ((K.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) = (fun y => g⁻¹ * y * g) ⁻¹' (K : Set G)`. Use extensionality with `y`.

Simplify using `only [SetLike.mem_coe, Set.mem_preimage, mem_conj_map]`. Establish `hK'o : IsOpen ((K.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G)`. Rewrite using `[hK'set]`. Conclude with `hKo.preimage ((continuous_const.mul continuous_id).mul continuous_const)`. Establish `hcont : Continuous (MulAut.conj g).toMonoidHom`.

Establish `: ⇑(MulAut.conj g).toMonoidHom = fun x => g * x * g⁻¹`. Use function extensionality and compare the values at `x`. Simplify using `[MulAut.conj_apply]`. Rewrite using `[this]`. Conclude with `(continuous_const.mul continuous_id).mul continuous_const`.

Establish `hK'c : IsCompact ((K.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G)`. Rewrite using `[Subgroup.coe_map]`. Conclude with `hKc.image hcont`. Establish `hconj : μ ((K.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) = μ K`. Establish `h1` using `measure_subgroup_eq μ K (K.map (MulAut.conj g).toMonoidHom) hKo hK'c hK'o`.

Establish `h2` using `measure_subgroup_eq μ (K.map (MulAut.conj g).toMonoidHom) K hK'o hKc hKo`. Rewrite using `[h1, h2, inf_comm, relIndex_map_conj_eq_relIndex_map_conj_inv, hidx g]`. Establish `hνK : map (· * g) μ K = μ K`. Rewrite using `[he.map_apply]`. Establish `hset : (fun x : G => x * g) ⁻¹' (K : Set G) = g⁻¹ • ((K.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G)`.

Use extensionality with `x`. Simplify using `only [Set.mem_preimage, SetLike.mem_coe, Set.mem_smul_set_iff_inv_smul_mem, inv_inv, smul_eq_mul, mem_conj_map]`. Simplify using the standard rewrite rules. Rewrite using `[hset, measure_smul]`. Conclude with `hconj`.

Establish `hc : haarScalarFactor (map (· * g) μ) μ = 1`. Establish `h` using `measure_isMulInvariant_eq_smul_of_isCompact_closure (map (· * g) μ) μ (s := (K : Set G)) (by rw [hKcl.closure_eq]; exact hKc)`. Rewrite `h` using `[hνK]`. Establish `h' : ((haarScalarFactor (map (· * g) μ) μ : NNReal) : ENNReal) * μ K = 1 * μ K`. Rewrite using `[one_mul]`.

Conclude with `h.symm`. Establish `key : ((haarScalarFactor (map (· * g) μ) μ : NNReal) : ENNReal) = 1`. Conclude with `(ENNReal.mul_left_inj hKpos.ne' hKfin.ne).mp h'`. Conclude with `key` after adjusting the coercions. Establish `hKTo : IsOpen ((K ⊓ ⊤ : Subgroup G) : Set G)` using `by rw [inf_top_eq]; exact hKo`.

Establish `hKTc : IsCompact ((K ⊓ ⊤ : Subgroup G) : Set G)` using `by rw [inf_top_eq]; exact hKc`. Establish `hKTcl : IsClosed ((K ⊓ ⊤ : Subgroup G) : Set G)` using `by rw [inf_top_eq]; exact hKcl`. Establish `hcov : (⋃ q : (⊤ : Subgroup G) ⧸ K.subgroupOf ⊤, ((q.out : (⊤ : Subgroup G)) : G) • ((K ⊓ ⊤ : Subgroup G) : Set G)) = Set.univ`. Rewrite using `[← subgroup_eq_iUnion K ⊤, Subgroup.coe_top]`. Establish `hTpos : ∀ q : (⊤ : Subgroup G) ⧸ K.subgroupOf ⊤, 0 < μ (((q.out : (⊤ : Subgroup G)) : G) • ((K ⊓ ⊤ : Subgroup G) : Set G))`.

Introduce `q`. Rewrite using `[measure_smul]`. Conclude with `hKTo.measure_pos μ ⟨1, (K ⊓ ⊤).one_mem⟩`. Establish `hcount : Countable ((⊤ : Subgroup G) ⧸ K.subgroupOf ⊤)`. Use `Measure.countable_meas_pos_of_disjoint_iUnion (μ := μ) (fun q : (⊤ : Subgroup G) ⧸ K.subgroupOf ⊤ => (hKTo.smul ((q.out : (⊤ : Subgroup G)) : G)).measurableSet) (pairwise_disjoint_cosets K ⊤)` as an intermediate fact.

Conclude with `Set.countable_univ_iff.mp (Set.Countable.mono (fun q _ => hTpos q) this)`. Use `measure_eq_of_eq_on_partition μ (map (· * g) μ) (fun q : (⊤ : Subgroup G) ⧸ K.subgroupOf ⊤ => ((q.out : (⊤ : Subgroup G)) : G) • ((K ⊓ ⊤ : Subgroup G) : Set G)) hcov (pairwise_disjoint_cosets K ⊤) (fun q => (hKTo.smul _).measurableSet) ?_` and prove the remaining obligations. Introduce `q s hs hsub`. Establish `hcl : IsCompact (closure s)` using `(hKTc.smul ((q.out : (⊤ : Subgroup G)) : G)).of_isClosed_subset isClosed_closure (closure_minimal hsub (hKTcl.smul ((q.out : (⊤ : Subgroup G)) : G)))`. Rewrite using `[measure_isMulInvariant_eq_smul_of_isCompact_closure (map (· * g) μ) μ hcl, hc, one_smul]`.
-/
theorem unimodIdx_main : PI.UnimodIdx := by
  unfold PI.UnimodIdx
  intro G _ _ _ _ _ μ _ hμ U hU hUb K hKo hKc hidx
  have : LocallyCompactSpace G :=
    hKc.locallyCompactSpace_of_mem_nhds_of_group (hKo.mem_nhds K.one_mem)
  refine ⟨fun g => ?_⟩
  have hKcl : IsClosed (K : Set G) := Subgroup.isClosed_of_isOpen K hKo
  have hKpos : 0 < μ K := hKo.measure_pos μ ⟨1, K.one_mem⟩
  have hKfin : μ K < ⊤ := hKc.measure_lt_top
  have hinv : IsMulLeftInvariant (map (· * g) μ) := by
    constructor
    intro h
    calc map (h * ·) (map (· * g) μ) = map ((h * ·) ∘ (· * g)) μ :=
          map_map (measurable_const_mul h) (measurable_mul_const g)
      _ = map ((· * g) ∘ (h * ·)) μ := by
          congr 1; funext x; simp [mul_assoc]
      _ = map (· * g) (map (h * ·) μ) :=
          (map_map (measurable_mul_const g) (measurable_const_mul h)).symm
      _ = map (· * g) μ := by rw [map_mul_left_eq_self]
  have he : MeasurableEmbedding (fun x : G => x * g) := (MeasurableEquiv.mulRight g).measurableEmbedding
  have hfin : IsFiniteMeasureOnCompacts (map (· * g) μ) := by
    constructor
    intro C hC
    rw [he.map_apply]
    have : IsCompact ((fun x : G => x * g) ⁻¹' C) := (Homeomorph.mulRight g).isCompact_preimage.mpr hC
    exact this.measure_lt_top
  have hK'set : ((K.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G)
      = (fun y => g⁻¹ * y * g) ⁻¹' (K : Set G) := by
    ext y
    simp only [SetLike.mem_coe, Set.mem_preimage, mem_conj_map]
  have hK'o : IsOpen ((K.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
    rw [hK'set]; exact hKo.preimage ((continuous_const.mul continuous_id).mul continuous_const)
  have hcont : Continuous (MulAut.conj g).toMonoidHom := by
    have : ⇑(MulAut.conj g).toMonoidHom = fun x => g * x * g⁻¹ := by
      funext x; simp [MulAut.conj_apply]
    rw [this]; exact (continuous_const.mul continuous_id).mul continuous_const
  have hK'c : IsCompact ((K.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
    rw [Subgroup.coe_map]; exact hKc.image hcont
  have hconj : μ ((K.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) = μ K := by
    have h1 := measure_subgroup_eq μ K (K.map (MulAut.conj g).toMonoidHom) hKo hK'c hK'o
    have h2 := measure_subgroup_eq μ (K.map (MulAut.conj g).toMonoidHom) K hK'o hKc hKo
    rw [h1, h2, inf_comm, relIndex_map_conj_eq_relIndex_map_conj_inv, hidx g]
  have hνK : map (· * g) μ K = μ K := by
    rw [he.map_apply]
    have hset : (fun x : G => x * g) ⁻¹' (K : Set G)
        = g⁻¹ • ((K.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
      ext x
      simp only [Set.mem_preimage, SetLike.mem_coe, Set.mem_smul_set_iff_inv_smul_mem, inv_inv,
        smul_eq_mul, mem_conj_map]
      simp
    rw [hset, measure_smul]
    exact hconj
  have hc : haarScalarFactor (map (· * g) μ) μ = 1 := by
    have h := measure_isMulInvariant_eq_smul_of_isCompact_closure (map (· * g) μ) μ
      (s := (K : Set G)) (by rw [hKcl.closure_eq]; exact hKc)
    rw [hνK] at h
    have h' : ((haarScalarFactor (map (· * g) μ) μ : NNReal) : ENNReal) * μ K = 1 * μ K := by
      rw [one_mul]
      exact h.symm
    have key : ((haarScalarFactor (map (· * g) μ) μ : NNReal) : ENNReal) = 1 := by
      exact (ENNReal.mul_left_inj hKpos.ne' hKfin.ne).mp h'
    exact_mod_cast key
  have hKTo : IsOpen ((K ⊓ ⊤ : Subgroup G) : Set G) := by rw [inf_top_eq]; exact hKo
  have hKTc : IsCompact ((K ⊓ ⊤ : Subgroup G) : Set G) := by rw [inf_top_eq]; exact hKc
  have hKTcl : IsClosed ((K ⊓ ⊤ : Subgroup G) : Set G) := by rw [inf_top_eq]; exact hKcl
  have hcov : (⋃ q : (⊤ : Subgroup G) ⧸ K.subgroupOf ⊤,
      ((q.out : (⊤ : Subgroup G)) : G) • ((K ⊓ ⊤ : Subgroup G) : Set G)) = Set.univ := by
    rw [← subgroup_eq_iUnion K ⊤, Subgroup.coe_top]
  have hTpos : ∀ q : (⊤ : Subgroup G) ⧸ K.subgroupOf ⊤,
      0 < μ (((q.out : (⊤ : Subgroup G)) : G) • ((K ⊓ ⊤ : Subgroup G) : Set G)) := by
    intro q
    rw [measure_smul]
    exact hKTo.measure_pos μ ⟨1, (K ⊓ ⊤).one_mem⟩
  have hcount : Countable ((⊤ : Subgroup G) ⧸ K.subgroupOf ⊤) := by
    have := Measure.countable_meas_pos_of_disjoint_iUnion (μ := μ)
      (fun q : (⊤ : Subgroup G) ⧸ K.subgroupOf ⊤ => (hKTo.smul ((q.out : (⊤ : Subgroup G)) : G)).measurableSet)
      (pairwise_disjoint_cosets K ⊤)
    exact Set.countable_univ_iff.mp (Set.Countable.mono (fun q _ => hTpos q) this)
  refine measure_eq_of_eq_on_partition μ (map (· * g) μ)
    (fun q : (⊤ : Subgroup G) ⧸ K.subgroupOf ⊤ =>
      ((q.out : (⊤ : Subgroup G)) : G) • ((K ⊓ ⊤ : Subgroup G) : Set G))
    hcov (pairwise_disjoint_cosets K ⊤) (fun q => (hKTo.smul _).measurableSet) ?_
  intro q s hs hsub
  have hcl : IsCompact (closure s) :=
    (hKTc.smul ((q.out : (⊤ : Subgroup G)) : G)).of_isClosed_subset isClosed_closure
      (closure_minimal hsub (hKTcl.smul ((q.out : (⊤ : Subgroup G)) : G)))
  rw [measure_isMulInvariant_eq_smul_of_isCompact_closure (map (· * g) μ) μ hcl, hc, one_smul]

end PI.UnimodIdxWork
