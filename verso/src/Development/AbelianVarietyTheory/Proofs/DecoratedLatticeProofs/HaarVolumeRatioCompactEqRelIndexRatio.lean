import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtXCastAdd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeUnipotentHaarAndModulus
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.VolBridge
open scoped Pointwise ENNReal

namespace GlobalTheory.VolRatio

/- English proof (translation)
Take `⟨s, hs, -⟩` from `(H.subgroupOf L).exists_isComplement_left 1`. Establish `hs' : Finite s` using `hs.finite_left_iff.mpr inferInstance`. Establish `hU : (⋃ a : s, (a.val : L) • (H : Set G)) = (L : Set G)`. Use extensionality with `x`. Simplify using `only [Set.mem_iUnion, Set.mem_smul_set, SetLike.mem_coe]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, h, hh, rfl⟩`. Conclude with `L.mul_mem a.val.2 (hHL hh)`. Introduce `hx`. Take `⟨⟨b, h⟩, hbh, -⟩` from `hs.existsUnique ⟨x, hx⟩`.

Use `⟨b, (h.val : G), Subgroup.mem_subgroupOf.mp h.2, ?_⟩` and prove the remaining obligations. Use `congrArg Subtype.val hbh` as an intermediate fact. Conclude with `this`. Establish `hdisj : Pairwise (Function.onFun Disjoint fun a : s => (a.val : L) • (H : Set G))`. Introduce `a b hab`.

Rewrite using `[Function.onFun, Set.disjoint_left]`. Introduce and unpack `x ⟨h1, hh1, rfl⟩ ⟨h2, hh2, he⟩`. Apply `hab` to reduce the goal to its premises. Establish `hh1' : (⟨h1, hHL hh1⟩ : L) ∈ H.subgroupOf L` using `Subgroup.mem_subgroupOf.mpr hh1`. Establish `hh2' : (⟨h2, hHL hh2⟩ : L) ∈ H.subgroupOf L` using `Subgroup.mem_subgroupOf.mpr hh2`.

Establish `e : (a.val : L) * ⟨h1, hHL hh1⟩ = (b.val : L) * ⟨h2, hHL hh2⟩` using `Subtype.ext he.symm`. Use `(hs.existsUnique ((a.val : L) * ⟨h1, hHL hh1⟩)).unique (y₁ := (a, ⟨_, hh1'⟩)) (y₂ := (b, ⟨_, hh2'⟩)) rfl e.symm` as an intermediate fact. Conclude with `congrArg Prod.fst this`. Combine the equalities or inequalities in the displayed calculation. Simplify using `[measure_smul, hs.encard_left, Subgroup.relIndex]`.

Use `_ = μ (⋃ a : s, (a.val : L) • (H : Set G)) := (measure_iUnion hdisj fun a => hH.const_smul _).symm`. Use `_ = μ L := by rw [hU]`.
-/
theorem relIndex_mul_measure_sub {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (H L : Subgroup G) (hHL : H ≤ L) [(H.subgroupOf L).FiniteIndex]
    (hH : MeasurableSet (H : Set G)) (μ : Measure G) [μ.IsMulLeftInvariant] :
    (H.relIndex L : ENNReal) * μ H = μ L := by
  obtain ⟨s, hs, -⟩ := (H.subgroupOf L).exists_isComplement_left 1
  have hs' : Finite s := hs.finite_left_iff.mpr inferInstance
  have hU : (⋃ a : s, (a.val : L) • (H : Set G)) = (L : Set G) := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_smul_set, SetLike.mem_coe]
    constructor
    · rintro ⟨a, h, hh, rfl⟩
      exact L.mul_mem a.val.2 (hHL hh)
    · intro hx
      obtain ⟨⟨b, h⟩, hbh, -⟩ := hs.existsUnique ⟨x, hx⟩
      refine ⟨b, (h.val : G), Subgroup.mem_subgroupOf.mp h.2, ?_⟩
      have := congrArg Subtype.val hbh
      exact this
  have hdisj : Pairwise (Function.onFun Disjoint fun a : s => (a.val : L) • (H : Set G)) := by
    intro a b hab
    rw [Function.onFun, Set.disjoint_left]
    rintro x ⟨h1, hh1, rfl⟩ ⟨h2, hh2, he⟩
    apply hab
    have hh1' : (⟨h1, hHL hh1⟩ : L) ∈ H.subgroupOf L := Subgroup.mem_subgroupOf.mpr hh1
    have hh2' : (⟨h2, hHL hh2⟩ : L) ∈ H.subgroupOf L := Subgroup.mem_subgroupOf.mpr hh2
    have e : (a.val : L) * ⟨h1, hHL hh1⟩ = (b.val : L) * ⟨h2, hHL hh2⟩ := Subtype.ext he.symm
    have := (hs.existsUnique ((a.val : L) * ⟨h1, hHL hh1⟩)).unique
      (y₁ := (a, ⟨_, hh1'⟩)) (y₂ := (b, ⟨_, hh2'⟩)) rfl e.symm
    exact congrArg Prod.fst this
  calc (H.relIndex L : ENNReal) * μ H = ∑' a : s, μ ((a.val : L) • (H : Set G)) := by
        simp [measure_smul, hs.encard_left, Subgroup.relIndex]
    _ = μ (⋃ a : s, (a.val : L) • (H : Set G)) :=
        (measure_iUnion hdisj fun a => hH.const_smul _).symm
    _ = μ L := by rw [hU]

/- English proof (translation)
Introduce `G _ _ _ _ _ μ _ A B hC hA hB`. Establish `hCA : A ⊓ B ≤ A` using `inf_le_left`. Establish `hCB : A ⊓ B ≤ B` using `inf_le_right`. Use `haveI : CompactSpace A := isCompact_iff_compactSpace.mp hA`. Use `haveI : CompactSpace B := isCompact_iff_compactSpace.mp hB`.

Use `haveI : ((A ⊓ B).subgroupOf A).FiniteIndex := by haveI := Subgroup.quotient_finite_of_isOpen ((A ⊓ B).subgroupOf A) (hC.preimage continuous_subtype_val)`. Conclude with `Subgroup.finiteIndex_of_finite_quotient`. Use `haveI : ((A ⊓ B).subgroupOf B).FiniteIndex := by haveI := Subgroup.quotient_finite_of_isOpen ((A ⊓ B).subgroupOf B) (hC.preimage continuous_subtype_val)`. Conclude with `Subgroup.finiteIndex_of_finite_quotient`. Establish `hCm : MeasurableSet ((A ⊓ B : Subgroup G) : Set G)` using `hC.measurableSet`.

Establish `h1` using `relIndex_mul_measure_sub (A ⊓ B) A hCA hCm μ`. Establish `h2` using `relIndex_mul_measure_sub (A ⊓ B) B hCB hCm μ`. Rewrite `h1` using `[Subgroup.inf_relIndex_left]`. Rewrite `h2` using `[Subgroup.inf_relIndex_right]`. Establish `hpos : 0 < μ ((A ⊓ B : Subgroup G) : Set G)` using `hC.measure_pos μ ⟨1, (A ⊓ B).one_mem⟩`.

Establish `hfin : μ ((A ⊓ B : Subgroup G) : Set G) < ⊤` using `lt_of_le_of_lt (measure_mono hCA) hA.measure_lt_top`. Establish `hr : 0 < (μ ((A ⊓ B : Subgroup G) : Set G)).toReal` using `ENNReal.toReal_pos hpos.ne' hfin.ne`. Rewrite using `[← h1, ← h2, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_natCast, mul_div_mul_right _ _ hr.ne']`.
-/
theorem vol_ratio : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] (μ : MeasureTheory.Measure G) [μ.IsHaarMeasure] (A B : Subgroup G), IsOpen ((A ⊓ B : Subgroup G) : Set G) → IsCompact (A : Set G) → IsCompact (B : Set G) → (μ (A : Set G)).toReal / (μ (B : Set G)).toReal = (B.relIndex A : ℝ) / (A.relIndex B : ℝ) := by
  intro G _ _ _ _ _ μ _ A B hC hA hB
  have hCA : A ⊓ B ≤ A := inf_le_left
  have hCB : A ⊓ B ≤ B := inf_le_right
  haveI : CompactSpace A := isCompact_iff_compactSpace.mp hA
  haveI : CompactSpace B := isCompact_iff_compactSpace.mp hB
  haveI : ((A ⊓ B).subgroupOf A).FiniteIndex := by
    haveI := Subgroup.quotient_finite_of_isOpen ((A ⊓ B).subgroupOf A)
      (hC.preimage continuous_subtype_val)
    exact Subgroup.finiteIndex_of_finite_quotient
  haveI : ((A ⊓ B).subgroupOf B).FiniteIndex := by
    haveI := Subgroup.quotient_finite_of_isOpen ((A ⊓ B).subgroupOf B)
      (hC.preimage continuous_subtype_val)
    exact Subgroup.finiteIndex_of_finite_quotient
  have hCm : MeasurableSet ((A ⊓ B : Subgroup G) : Set G) := hC.measurableSet
  have h1 := relIndex_mul_measure_sub (A ⊓ B) A hCA hCm μ
  have h2 := relIndex_mul_measure_sub (A ⊓ B) B hCB hCm μ
  rw [Subgroup.inf_relIndex_left] at h1
  rw [Subgroup.inf_relIndex_right] at h2
  have hpos : 0 < μ ((A ⊓ B : Subgroup G) : Set G) := hC.measure_pos μ ⟨1, (A ⊓ B).one_mem⟩
  have hfin : μ ((A ⊓ B : Subgroup G) : Set G) < ⊤ :=
    lt_of_le_of_lt (measure_mono hCA) hA.measure_lt_top
  have hr : 0 < (μ ((A ⊓ B : Subgroup G) : Set G)).toReal := ENNReal.toReal_pos hpos.ne' hfin.ne
  rw [← h1, ← h2, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_natCast, mul_div_mul_right _ _ hr.ne']

end GlobalTheory.VolRatio
