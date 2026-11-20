import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.T2SpaceOfIsNonarchimedeanLocalFieldFlagMeasures
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsEqZpowMulUnit

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical NNReal

namespace GlobalTheory.BaseModule

@[to_additive addRelIndex_mul_measure
]
/- English proof (translation)
Take `⟨s, hs, -⟩` from `(H.subgroupOf L).exists_isComplement_left 1`. Establish `hfin : Finite s` using `hs.finite_left_iff.mpr inferInstance`. Establish `hU : (L : Set G) = ⋃ a : s, ((a : L) : G) • (H : Set G)`. Use extensionality with `x`. Simplify using `only [Set.mem_iUnion, SetLike.mem_coe]`.

Prove the components needed by the constructor for the conclusion. Introduce `hx`. Establish `hy : (⟨x, hx⟩ : L) ∈ s * ((H.subgroupOf L : Subgroup L) : Set L)`. Rewrite using `[hs.mul_eq]`. Conclude with `Set.mem_univ _`.

Take `⟨a, ha, h, hh, hah⟩` from `hy`. Use `⟨⟨a, ha⟩, (h : G), Subgroup.mem_subgroupOf.mp hh, ?_⟩` and prove the remaining obligations. Use `congrArg Subtype.val hah` as an intermediate fact. Simplify using `using this`. Introduce and unpack `⟨a, z, hz, rfl⟩`.

Conclude with `L.mul_mem (a : L).2 (hHL hz)`. Establish `hdisj : Pairwise (Function.onFun Disjoint fun a : s => ((a : L) : G) • (H : Set G))`. Introduce `a b hab`. Use `Set.disjoint_left.mpr ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨z₁, hz₁, rfl⟩ ⟨z₂, hz₂, he⟩`.

Apply `hab` to reduce the goal to its premises. Establish `key` using `hs.1 (a₁ := (a, ⟨⟨z₁, hHL hz₁⟩, Subgroup.mem_subgroupOf.mpr hz₁⟩)) (a₂ := (b, ⟨⟨z₂, hHL hz₂⟩, Subgroup.mem_subgroupOf.mpr hz₂⟩)) (Subtype.ext (by simpa using he.symm))`. Conclude with `congrArg Prod.fst key`. Combine the equalities or inequalities in the displayed calculation. Simplify using `[measure_smul, hs.encard_left, Subgroup.relIndex]`.

Use `_ = μ L := by`. Rewrite using `[hU, measure_iUnion hdisj (fun _ => hH.const_smul _)]`.
-/
theorem relIndex_mul_measure' {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (H L : Subgroup G) (hHL : H ≤ L) [(H.subgroupOf L).FiniteIndex]
    (hH : MeasurableSet (H : Set G)) (μ : Measure G) [μ.IsMulLeftInvariant] :
    (H.relIndex L : ENNReal) * μ H = μ L := by
  classical
  obtain ⟨s, hs, -⟩ := (H.subgroupOf L).exists_isComplement_left 1
  have hfin : Finite s := hs.finite_left_iff.mpr inferInstance
  have hU : (L : Set G) = ⋃ a : s, ((a : L) : G) • (H : Set G) := by
    ext x
    simp only [Set.mem_iUnion, SetLike.mem_coe]
    constructor
    · intro hx
      have hy : (⟨x, hx⟩ : L) ∈ s * ((H.subgroupOf L : Subgroup L) : Set L) := by
        rw [hs.mul_eq]; exact Set.mem_univ _
      obtain ⟨a, ha, h, hh, hah⟩ := hy
      refine ⟨⟨a, ha⟩, (h : G), Subgroup.mem_subgroupOf.mp hh, ?_⟩
      have := congrArg Subtype.val hah
      simpa using this
    · rintro ⟨a, z, hz, rfl⟩
      exact L.mul_mem (a : L).2 (hHL hz)
  have hdisj : Pairwise (Function.onFun Disjoint fun a : s => ((a : L) : G) • (H : Set G)) := by
    intro a b hab
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨z₁, hz₁, rfl⟩ ⟨z₂, hz₂, he⟩
    apply hab
    have key := hs.1 (a₁ := (a, ⟨⟨z₁, hHL hz₁⟩, Subgroup.mem_subgroupOf.mpr hz₁⟩))
      (a₂ := (b, ⟨⟨z₂, hHL hz₂⟩, Subgroup.mem_subgroupOf.mpr hz₂⟩)) (Subtype.ext (by simpa using he.symm))
    exact congrArg Prod.fst key
  calc (H.relIndex L : ENNReal) * μ H = ∑' a : s, μ (((a : L) : G) • (H : Set G)) := by
        simp [measure_smul, hs.encard_left, Subgroup.relIndex]
    _ = μ L := by
        rw [hU, measure_iUnion hdisj (fun _ => hH.const_smul _)]

/- English proof (translation)
Introduce `F _ _ _ E _ _ _ _ M hM ϖ hϖ`. Use `hM.loc` as an intermediate fact. Use `hM.char0` as an intermediate fact. Use `hM.borel` as an intermediate fact. Use `hM.haar.haar` as an intermediate fact.

Take `⟨hTR, hT2, hLC, hSC, hCS, -, -, hOc, hOo, -⟩` from `GlobalTheory.SgLoc.Top.model_topology M hM`. Establish `hq2 : 2 ≤ resQ ϖ` using `(GlobalTheory.UnramOrder.order_facts M.L ϖ hϖ).2.2.2.2.2.2.1`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Unfold `GlobalTheory.HL.resQ`. Rewrite using `[← (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ]`.

Both sides reduce to the same expression. Introduce `x hx`. Establish `: IsTopologicalAddGroup E` using `inferInstance`. Establish `: M.mu.Regular` using `inferInstance`. Establish `hsmul : ∀ (a : F) (y : E), a ∈ 𝒪[F] → y ∈ M.L.O → a • y ∈ M.L.O` using `fun a y ha hy => by`.

Rewrite using `[Algebra.smul_def]`. Conclude with `M.L.O.mul_mem ((GlobalTheory.UnramOrder.algebraMap_mem_iff M.L a).mpr ha) hy`. Establish `hO0 : M.mu (M.L.O : Set E) ≠ 0` using `hOo.measure_ne_zero M.mu ⟨0, M.L.O.zero_mem⟩`. Establish `hOT : M.mu (M.L.O : Set E) ≠ ⊤` using `hOc.measure_lt_top.ne`. Establish `hunit : ∀ u : (𝒪[F])ˣ, distribHaarChar E (Units.mk0 ((u : 𝒪[F]) : F) (by simp)) = 1`.

Introduce `u`. Apply `distribHaarChar_eq_of_measure_smul_eq_mul hO0 hOT` to reduce the goal to its premises. Establish `hinv : (((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) : F) = ((u : 𝒪[F]) : F)⁻¹`. Establish `h1 : ((((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) * (u : 𝒪[F]) : 𝒪[F]) : F) = ((1 : 𝒪[F]) : F)`. Rewrite using `[u.inv_mul]`.

Rewrite `h1` using `[MulMemClass.coe_mul, OneMemClass.coe_one]`. Conclude with `eq_inv_of_mul_eq_one_left h1`. Establish `hset : Units.mk0 ((u : 𝒪[F]) : F) (by simp) • (M.L.O : Set E) = M.L.O`. Use extensionality with `y`. Rewrite using `[Set.mem_smul_set_iff_inv_smul_mem]`.

Prove the components needed by the constructor for the conclusion. Introduce `hy`. Establish `h2` using `hsmul ((u : 𝒪[F]) : F) _ (u : 𝒪[F]).2 hy`. Rewrite `h2` using `[Units.smul_def, Units.val_inv_eq_inv_val, Units.val_mk0, smul_inv_smul₀ (by simp)]`. Conclude with `h2`.

Introduce `hy`. Establish `h2` using `hsmul (((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) : F) y (u⁻¹ : (𝒪[F])ˣ).1.2 hy`. Rewrite using `[Units.smul_def, Units.val_inv_eq_inv_val, Units.val_mk0, ← hinv]`. Conclude with `h2`. Rewrite using `[hset]`.

Simplify using the standard rewrite rules. Establish `hϖ0 : (ϖ : F) ≠ 0`. Introduce `h`. Conclude with `hϖ.ne_zero (Subtype.ext h)`. Establish `hwO : algebraMap F E (ϖ : F) ∈ M.L.O` using `(GlobalTheory.UnramOrder.algebraMap_mem_iff M.L _).mpr ϖ.2`.

Establish `hI : Ideal.span {y : M.L.O | (y : E) = algebraMap F E ((ϖ : F) ^ 1)} = Ideal.span {(⟨algebraMap F E (ϖ : F), hwO⟩ : M.L.O)}`. Use `congr 1`. Use extensionality with `y`. Simplify using `[Subtype.ext_iff]`. Establish `hcard : Nat.card (M.L.O ⧸ Ideal.span {(⟨algebraMap F E (ϖ : F), hwO⟩ : M.L.O)}) = resQ ϖ ^ 2`.

Establish `h` using `(GlobalTheory.UnramOrder.order_facts M.L ϖ hϖ).2.2.2.2.2.1 1`. Rewrite `h` using `[hI, mul_one]`. Conclude with `h`. Establish `hfinj : Function.Injective (M.L.O.subtype.toAddMonoidHom)` using `Subtype.val_injective`. Establish `hrange : (⊤ : AddSubgroup M.L.O).map M.L.O.subtype.toAddMonoidHom = M.L.O.toAddSubgroup`.

Use extensionality with `z`. Simplify using the standard rewrite rules. Establish `hrel : ((Ideal.span {(⟨algebraMap F E (ϖ : F), hwO⟩ : M.L.O)}).toAddSubgroup.map M.L.O.subtype.toAddMonoidHom).relIndex M.L.O.toAddSubgroup = resQ ϖ ^ 2`. Rewrite using `[← hrange, AddSubgroup.relIndex_map_map_of_injective _ _ hfinj, AddSubgroup.relIndex_top_right]`. Conclude with `hcard`.

Establish `hHK : (Ideal.span {(⟨algebraMap F E (ϖ : F), hwO⟩ : M.L.O)}).toAddSubgroup.map M.L.O.subtype.toAddMonoidHom ≤ M.L.O.toAddSubgroup`. Introduce and unpack `z ⟨y, -, rfl⟩`. Conclude with `y.2`. Establish `hHset : (((Ideal.span {(⟨algebraMap F E (ϖ : F), hwO⟩ : M.L.O)}).toAddSubgroup.map M.L.O.subtype.toAddMonoidHom : AddSubgroup E) : Set E) = Units.mk0 (ϖ : F) hϖ0 • (M.L.O : Set E)`. Use extensionality with `z`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`. Take `⟨a, rfl⟩` from `Ideal.mem_span_singleton'.mp hy`. Use `⟨(a : E), a.2, ?_⟩` and prove the remaining obligations. Simplify using `[Algebra.smul_def, mul_comm]`.

Introduce and unpack `⟨b, hb, rfl⟩`. Use `⟨⟨b, hb⟩ * ⟨algebraMap F E (ϖ : F), hwO⟩, Ideal.mul_mem_left _ _ (Ideal.subset_span rfl), ?_⟩` and prove the remaining obligations. Simplify using `[Algebra.smul_def, mul_comm]`. Establish `hHm : MeasurableSet (((Ideal.span {(⟨algebraMap F E (ϖ : F), hwO⟩ : M.L.O)}).toAddSubgroup.map M.L.O.subtype.toAddMonoidHom : AddSubgroup E) : Set E)`. Rewrite using `[hHset]`.

Conclude with `(hOo.smul _).measurableSet`. Establish `: (((Ideal.span {(⟨algebraMap F E (ϖ : F), hwO⟩ : M.L.O)}).toAddSubgroup.map M.L.O.subtype.toAddMonoidHom).addSubgroupOf M.L.O.toAddSubgroup).FiniteIndex`. Use `⟨?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `AddSubgroup.relIndex _ _ ≠ 0`. Rewrite using `[hrel]`.

Conclude with `pow_ne_zero _ (by omega)`. Establish `key` using `addRelIndex_mul_measure _ _ hHK hHm M.mu`. Rewrite `key` using `[hrel, hHset]`. Establish `key2 : ((resQ ϖ ^ 2 : ℕ) : ENNReal) * M.mu (Units.mk0 (ϖ : F) hϖ0 • (M.L.O : Set E)) = M.mu (M.L.O : Set E)` using `key`. Establish `hΔp : distribHaarChar E (Units.mk0 (ϖ : F) hϖ0) = ((resQ ϖ : NNReal) ^ 2)⁻¹`.

Apply `distribHaarChar_eq_of_measure_smul_eq_mul hO0 hOT` to reduce the goal to its premises. Establish `h0 : ((resQ ϖ ^ 2 : ℕ) : ENNReal) ≠ 0`. Conclude with `pow_ne_zero _ (by omega)` after adjusting the coercions. Establish `hT : ((resQ ϖ ^ 2 : ℕ) : ENNReal) ≠ ⊤` using `ENNReal.natCast_ne_top _`. Establish `hc : (((((resQ ϖ : NNReal) ^ 2)⁻¹ : NNReal)) : ENNReal) = ((resQ ϖ ^ 2 : ℕ) : ENNReal)⁻¹`.

Rewrite using `[ENNReal.coe_inv (by exact_mod_cast pow_ne_zero _ (by omega))]`. Use `push_cast`. Both sides reduce to the same expression. Rewrite using `[hc]`. Rewrite using `[← key2, ← mul_assoc, ENNReal.inv_mul_cancel h0 hT, one_mul]`.

Take `⟨u, hu⟩` from `(GlobalTheory.UnramVal.vE_valuation M.L ϖ hϖ).2.2.2 x hx`. Establish `hgx : Units.mk0 x hx = Units.mk0 (ϖ : F) hϖ0 ^ (vE M.L ϖ (algebraMap F E x)) * Units.mk0 ((u : 𝒪[F]) : F) (by simp)`. Use `ext`. Rewrite using `[Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_mk0, Units.val_mk0, Units.val_mk0]`. Conclude with `hu`.

Establish `himg : (fun y => algebraMap F E x * y) '' (M.R : Set E) = Units.mk0 x hx • (M.R : Set E)`. Rewrite using `[← Set.image_smul]`. Use `congr 1`. Use function extensionality and compare the values at `y`. Rewrite using `[Units.smul_def, Units.val_mk0, Algebra.smul_def]`.

Unfold `Formalism.MainNotions.S.Loc.Model.modK`. Rewrite using `[himg, ← distribHaarChar_mul M.mu, hM.haar.volR, mul_one, hgx, map_mul, map_zpow, hunit u, mul_one, hΔp, ENNReal.coe_toReal]`. Use `push_cast`. Rewrite using `[← zpow_natCast, ← zpow_neg, ← zpow_mul]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem modK_algebraMap : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ ϖ : 𝒪[F], Irreducible ϖ → Nat.card 𝓀[F] = resQ ϖ ∧ ∀ x : F, x ≠ 0 → M.modK (algebraMap F E x) = (resQ ϖ : ℝ) ^ (-(2 * vE M.L ϖ (algebraMap F E x))) := by
  intro F _ _ _ E _ _ _ _ M hM ϖ hϖ
  have := hM.loc
  have := hM.char0
  have := hM.borel
  have := hM.haar.haar
  obtain ⟨hTR, hT2, hLC, hSC, hCS, -, -, hOc, hOo, -⟩ := GlobalTheory.SgLoc.Top.model_topology M hM
  have hq2 : 2 ≤ resQ ϖ := (GlobalTheory.UnramOrder.order_facts M.L ϖ hϖ).2.2.2.2.2.2.1
  refine ⟨?_, ?_⟩
  · unfold GlobalTheory.HL.resQ
    rw [← (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ]
    rfl
  intro x hx
  have : IsTopologicalAddGroup E := inferInstance
  have : M.mu.Regular := inferInstance
  have hsmul : ∀ (a : F) (y : E), a ∈ 𝒪[F] → y ∈ M.L.O → a • y ∈ M.L.O := fun a y ha hy => by
    rw [Algebra.smul_def]
    exact M.L.O.mul_mem ((GlobalTheory.UnramOrder.algebraMap_mem_iff M.L a).mpr ha) hy
  have hO0 : M.mu (M.L.O : Set E) ≠ 0 := hOo.measure_ne_zero M.mu ⟨0, M.L.O.zero_mem⟩
  have hOT : M.mu (M.L.O : Set E) ≠ ⊤ := hOc.measure_lt_top.ne

  have hunit : ∀ u : (𝒪[F])ˣ, distribHaarChar E (Units.mk0 ((u : 𝒪[F]) : F) (by simp)) = 1 := by
    intro u
    apply distribHaarChar_eq_of_measure_smul_eq_mul hO0 hOT
    have hinv : (((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) : F) = ((u : 𝒪[F]) : F)⁻¹ := by
      have h1 : ((((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) * (u : 𝒪[F]) : 𝒪[F]) : F) = ((1 : 𝒪[F]) : F) := by
        rw [u.inv_mul]
      rw [MulMemClass.coe_mul, OneMemClass.coe_one] at h1
      exact eq_inv_of_mul_eq_one_left h1
    have hset : Units.mk0 ((u : 𝒪[F]) : F) (by simp) • (M.L.O : Set E) = M.L.O := by
      ext y
      rw [Set.mem_smul_set_iff_inv_smul_mem]
      constructor
      · intro hy
        have h2 := hsmul ((u : 𝒪[F]) : F) _ (u : 𝒪[F]).2 hy
        rw [Units.smul_def, Units.val_inv_eq_inv_val, Units.val_mk0, smul_inv_smul₀ (by simp)] at h2
        exact h2
      · intro hy
        have h2 := hsmul (((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) : F) y (u⁻¹ : (𝒪[F])ˣ).1.2 hy
        rw [Units.smul_def, Units.val_inv_eq_inv_val, Units.val_mk0, ← hinv]
        exact h2
    rw [hset]
    simp

  have hϖ0 : (ϖ : F) ≠ 0 := by
    intro h
    exact hϖ.ne_zero (Subtype.ext h)
  have hwO : algebraMap F E (ϖ : F) ∈ M.L.O := (GlobalTheory.UnramOrder.algebraMap_mem_iff M.L _).mpr ϖ.2
  have hI : Ideal.span {y : M.L.O | (y : E) = algebraMap F E ((ϖ : F) ^ 1)} =
      Ideal.span {(⟨algebraMap F E (ϖ : F), hwO⟩ : M.L.O)} := by
    congr 1
    ext y
    simp [Subtype.ext_iff]
  have hcard : Nat.card (M.L.O ⧸ Ideal.span {(⟨algebraMap F E (ϖ : F), hwO⟩ : M.L.O)}) = resQ ϖ ^ 2 := by
    have h := (GlobalTheory.UnramOrder.order_facts M.L ϖ hϖ).2.2.2.2.2.1 1
    rw [hI, mul_one] at h
    exact h
  have hfinj : Function.Injective (M.L.O.subtype.toAddMonoidHom) := Subtype.val_injective
  have hrange : (⊤ : AddSubgroup M.L.O).map M.L.O.subtype.toAddMonoidHom = M.L.O.toAddSubgroup := by
    ext z
    simp
  have hrel : ((Ideal.span {(⟨algebraMap F E (ϖ : F), hwO⟩ : M.L.O)}).toAddSubgroup.map
      M.L.O.subtype.toAddMonoidHom).relIndex M.L.O.toAddSubgroup = resQ ϖ ^ 2 := by
    rw [← hrange, AddSubgroup.relIndex_map_map_of_injective _ _ hfinj, AddSubgroup.relIndex_top_right]
    exact hcard
  have hHK : (Ideal.span {(⟨algebraMap F E (ϖ : F), hwO⟩ : M.L.O)}).toAddSubgroup.map
      M.L.O.subtype.toAddMonoidHom ≤ M.L.O.toAddSubgroup := by
    rintro z ⟨y, -, rfl⟩
    exact y.2
  have hHset : (((Ideal.span {(⟨algebraMap F E (ϖ : F), hwO⟩ : M.L.O)}).toAddSubgroup.map
      M.L.O.subtype.toAddMonoidHom : AddSubgroup E) : Set E) = Units.mk0 (ϖ : F) hϖ0 • (M.L.O : Set E) := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hy
      refine ⟨(a : E), a.2, ?_⟩
      simp [Algebra.smul_def, mul_comm]
    · rintro ⟨b, hb, rfl⟩
      refine ⟨⟨b, hb⟩ * ⟨algebraMap F E (ϖ : F), hwO⟩,
        Ideal.mul_mem_left _ _ (Ideal.subset_span rfl), ?_⟩
      simp [Algebra.smul_def, mul_comm]
  have hHm : MeasurableSet (((Ideal.span {(⟨algebraMap F E (ϖ : F), hwO⟩ : M.L.O)}).toAddSubgroup.map
      M.L.O.subtype.toAddMonoidHom : AddSubgroup E) : Set E) := by
    rw [hHset]
    exact (hOo.smul _).measurableSet
  have : (((Ideal.span {(⟨algebraMap F E (ϖ : F), hwO⟩ : M.L.O)}).toAddSubgroup.map
      M.L.O.subtype.toAddMonoidHom).addSubgroupOf M.L.O.toAddSubgroup).FiniteIndex := by
    refine ⟨?_⟩
    change AddSubgroup.relIndex _ _ ≠ 0
    rw [hrel]
    exact pow_ne_zero _ (by omega)
  have key := addRelIndex_mul_measure _ _ hHK hHm M.mu
  rw [hrel, hHset] at key
  have key2 : ((resQ ϖ ^ 2 : ℕ) : ENNReal) * M.mu (Units.mk0 (ϖ : F) hϖ0 • (M.L.O : Set E)) =
      M.mu (M.L.O : Set E) := key
  have hΔp : distribHaarChar E (Units.mk0 (ϖ : F) hϖ0) = ((resQ ϖ : NNReal) ^ 2)⁻¹ := by
    apply distribHaarChar_eq_of_measure_smul_eq_mul hO0 hOT
    have h0 : ((resQ ϖ ^ 2 : ℕ) : ENNReal) ≠ 0 := by
      exact_mod_cast pow_ne_zero _ (by omega)
    have hT : ((resQ ϖ ^ 2 : ℕ) : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
    have hc : (((((resQ ϖ : NNReal) ^ 2)⁻¹ : NNReal)) : ENNReal) = ((resQ ϖ ^ 2 : ℕ) : ENNReal)⁻¹ := by
      rw [ENNReal.coe_inv (by exact_mod_cast pow_ne_zero _ (by omega))]
      push_cast
      rfl
    rw [hc]
    rw [← key2, ← mul_assoc, ENNReal.inv_mul_cancel h0 hT, one_mul]

  obtain ⟨u, hu⟩ := (GlobalTheory.UnramVal.vE_valuation M.L ϖ hϖ).2.2.2 x hx
  have hgx : Units.mk0 x hx = Units.mk0 (ϖ : F) hϖ0 ^ (vE M.L ϖ (algebraMap F E x)) *
      Units.mk0 ((u : 𝒪[F]) : F) (by simp) := by
    ext
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_mk0, Units.val_mk0, Units.val_mk0]
    exact hu
  have himg : (fun y => algebraMap F E x * y) '' (M.R : Set E) = Units.mk0 x hx • (M.R : Set E) := by
    rw [← Set.image_smul]
    congr 1
    funext y
    rw [Units.smul_def, Units.val_mk0, Algebra.smul_def]
  unfold Formalism.MainNotions.S.Loc.Model.modK
  rw [himg, ← distribHaarChar_mul M.mu, hM.haar.volR, mul_one, hgx, map_mul, map_zpow, hunit u, mul_one,
    hΔp, ENNReal.coe_toReal]
  push_cast
  rw [← zpow_natCast, ← zpow_neg, ← zpow_mul]
  congr 1
  push_cast
  ring

end GlobalTheory.BaseModule
