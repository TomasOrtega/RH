import Mathlib
import GroundTheory.AutomorphicForms.MeasuresModulus
import GroundTheory.AutomorphicForms.MeasuresChart
import GroundTheory.AutomorphicForms.MeasuresGL
import GroundTheory.AutomorphicForms.MeasuresParabolic
import GroundTheory.AutomorphicForms.Iwasawa
set_option maxSynthPendingDepth 1

namespace GroundTheory.Automorphic

open MeasureTheory Measure Topology Filter Set ValuativeRel
open scoped NNReal ENNReal Pointwise

set_option linter.unusedSectionVars false

namespace Measures

section General

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

/- English proof (translation)
Establish `e` using `isMulLeftInvariant_eq_smul (map (· * k) μ) μ`. Establish `h` using `congrArg (fun ν : Measure K => ν univ) e`. Simplify using `only [map_apply (continuous_mul_const k).measurable MeasurableSet.univ, Set.preimage_univ, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h`. Establish `hc : haarScalarFactor (map (· * k) μ) μ = 1`. Use `(ENNReal.mul_eq_right (IsOpen.measure_ne_zero μ isOpen_univ univ_nonempty) (measure_ne_top μ univ)).1 h.symm` as an intermediate fact.

Conclude with `this` after adjusting the coercions. Rewrite using `[e, hc, one_smul]`.
-/
theorem map_mul_right_eq_self_of_compactSpace {K : Type*} [Group K] [TopologicalSpace K]
    [IsTopologicalGroup K] [CompactSpace K] [T2Space K] [SecondCountableTopology K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsHaarMeasure] (k : K) :
    map (· * k) μ = μ := by
  have e := isMulLeftInvariant_eq_smul (map (· * k) μ) μ
  have h := congrArg (fun ν : Measure K => ν univ) e
  simp only [map_apply (continuous_mul_const k).measurable MeasurableSet.univ,
    Set.preimage_univ, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h
  have hc : haarScalarFactor (map (· * k) μ) μ = 1 := by
    have := (ENNReal.mul_eq_right (IsOpen.measure_ne_zero μ isOpen_univ univ_nonempty)
      (measure_ne_top μ univ)).1 h.symm
    exact_mod_cast this
  rw [e, hc, one_smul]

/- English proof (translation)
Take `⟨a, ha, rfl⟩` from `hz`. Use extensionality with `w`. Simplify using `only [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul, SetLike.mem_coe, mul_inv_rev, mul_assoc]`. Conclude with `(N.mul_mem_cancel_left (N.inv_mem ha)).symm`.
-/
theorem smul_coe_eq_of_mem {N : Subgroup G} {x z : G} (hz : z ∈ x • (N : Set G)) :
    x • (N : Set G) = z • (N : Set G) := by
  obtain ⟨a, ha, rfl⟩ := hz
  ext w
  simp only [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul, SetLike.mem_coe, mul_inv_rev,
    mul_assoc]
  exact (N.mul_mem_cancel_left (N.inv_mem ha)).symm

variable (K : Subgroup G)

def IsSmallNormal (N : Subgroup G) : Prop :=
  IsOpen (N : Set G) ∧ N ≤ K ∧ ∀ k ∈ K, ∀ y ∈ N, k * y * k⁻¹ ∈ N

def smallCosets : Set (Set G) :=
  {s | ∃ x : G, ∃ N : Subgroup G, IsSmallNormal K N ∧ s = x • (N : Set G)}

/- English proof (translation)
Introduce and unpack `_ ⟨x, N₁, hN₁, rfl⟩ _ ⟨y, N₂, hN₂, rfl⟩ ⟨z, hz₁, hz₂⟩`. Use `⟨z, N₁ ⊓ N₂, ⟨hN₁.1.inter hN₂.1, inf_le_of_left_le hN₁.2.1, fun k hk w hw => ⟨hN₁.2.2 k hk w hw.1, hN₂.2.2 k hk w hw.2⟩⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_coe_eq_of_mem hz₁, smul_coe_eq_of_mem hz₂, ← Set.smul_set_inter, Subgroup.coe_inf]`.
-/
theorem isPiSystem_smallCosets : IsPiSystem (smallCosets K) := by
  rintro _ ⟨x, N₁, hN₁, rfl⟩ _ ⟨y, N₂, hN₂, rfl⟩ ⟨z, hz₁, hz₂⟩
  refine ⟨z, N₁ ⊓ N₂, ⟨hN₁.1.inter hN₂.1, inf_le_of_left_le hN₁.2.1,
    fun k hk w hw => ⟨hN₁.2.2 k hk w hw.1, hN₂.2.2 k hk w hw.2⟩⟩, ?_⟩
  rw [smul_coe_eq_of_mem hz₁, smul_coe_eq_of_mem hz₂, ← Set.smul_set_inter, Subgroup.coe_inf]

variable {K}

/- English proof (translation)
Use `le_antisymm ?_ (MeasurableSpace.generateFrom_le ?_)` and prove the remaining obligations. Rewrite using `[BorelSpace.measurable_eq (α := G)]`. Use `MeasurableSpace.generateFrom_le fun U hU => ?_` and prove the remaining obligations. Set `ι` to `{q : G × Subgroup G // IsSmallNormal K q.2 ∧ q.1 • (q.2 : Set G) ⊆ U}`. Set `s : ι → Set G` to `fun q => q.1.1 • (q.1.2 : Set G)`.

Establish `hU' : U = ⋃ q, s q`. Use `Subset.antisymm (fun y hy => ?_) (iUnion_subset fun q => q.2.2)` and prove the remaining obligations. Establish `: y⁻¹ • U ∈ 𝓝 (1 : G)`. Use `(hU.smul y⁻¹).mem_nhds ?_` and prove the remaining obligations. Conclude with `⟨y, hy, inv_mul_cancel y⟩`.

Take `⟨N, hN, hNU⟩` from `hN _ this`. Use `mem_iUnion.2 ⟨⟨(y, N), hN, ?_⟩, ⟨1, N.one_mem, mul_one y⟩⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨a, ha, rfl⟩`. Take `⟨u, hu, hua⟩` from `hNU ha`. Rewrite using `[← hua]`.

Use `show y * (y⁻¹ * u) ∈ U`. Rewrite using `[mul_inv_cancel_left]`. Conclude with `hu`. Take `⟨T, hTc, hT⟩` from `TopologicalSpace.isOpen_iUnion_countable s fun q => q.2.1.1.smul _`. Rewrite using `[hU', ← hT]`.

Conclude with `MeasurableSet.biUnion hTc fun q _ => MeasurableSpace.measurableSet_generateFrom ⟨q.1.1, q.1.2, q.2.1, rfl⟩`. Introduce and unpack `_ ⟨x, N, hN, rfl⟩`. Conclude with `(hN.1.smul x).measurableSet`.
-/
theorem borel_eq_generateFrom_smallCosets
    (hN : ∀ U ∈ 𝓝 (1 : G), ∃ N : Subgroup G, IsSmallNormal K N ∧ (N : Set G) ⊆ U) :
    ‹MeasurableSpace G› = MeasurableSpace.generateFrom (smallCosets K) := by
  refine le_antisymm ?_ (MeasurableSpace.generateFrom_le ?_)
  · rw [BorelSpace.measurable_eq (α := G)]
    refine MeasurableSpace.generateFrom_le fun U hU => ?_
    let ι := {q : G × Subgroup G // IsSmallNormal K q.2 ∧ q.1 • (q.2 : Set G) ⊆ U}
    let s : ι → Set G := fun q => q.1.1 • (q.1.2 : Set G)
    have hU' : U = ⋃ q, s q := by
      refine Subset.antisymm (fun y hy => ?_) (iUnion_subset fun q => q.2.2)
      have : y⁻¹ • U ∈ 𝓝 (1 : G) := by
        refine (hU.smul y⁻¹).mem_nhds ?_
        exact ⟨y, hy, inv_mul_cancel y⟩
      obtain ⟨N, hN, hNU⟩ := hN _ this
      refine mem_iUnion.2 ⟨⟨(y, N), hN, ?_⟩, ⟨1, N.one_mem, mul_one y⟩⟩
      rintro _ ⟨a, ha, rfl⟩
      obtain ⟨u, hu, hua⟩ := hNU ha
      rw [← hua]
      show y * (y⁻¹ * u) ∈ U
      rw [mul_inv_cancel_left]
      exact hu
    obtain ⟨T, hTc, hT⟩ := TopologicalSpace.isOpen_iUnion_countable s fun q => q.2.1.1.smul _
    rw [hU', ← hT]
    exact MeasurableSet.biUnion hTc fun q _ =>
      MeasurableSpace.measurableSet_generateFrom ⟨q.1.1, q.1.2, q.2.1, rfl⟩
  · rintro _ ⟨x, N, hN, rfl⟩
    exact (hN.1.smul x).measurableSet

/- English proof (translation)
Establish `hN : ∀ U ∈ 𝓝 (1 : G), ∃ N : Subgroup G, IsSmallNormal K N ∧ (N : Set G) ⊆ U`. Introduce `U hU`. Take `⟨N, -, hNU, hNK⟩` from `exists_compactOpenSubgroup_normalized hKc (inter_mem hU (hKo.mem_nhds K.one_mem))`. Conclude with `⟨N, ⟨N.isOpen, fun x hx => (hNU hx).2, hNK⟩, fun x hx => (hNU hx).1⟩`. Establish `: LocallyCompactSpace P` using `hP.locallyCompactSpace`.

Establish `: CompactSpace K` using `isCompact_iff_compactSpace.1 hKc`. Establish `: SecondCountableTopology P` using `IsEmbedding.subtypeVal.secondCountableTopology`. Establish `: SecondCountableTopology K` using `IsEmbedding.subtypeVal.secondCountableTopology`. Establish `: BorelSpace P` using `Subtype.borelSpace (P : Set G)`. Establish `: BorelSpace K` using `Subtype.borelSpace (K : Set G)`.

Use `set m : P × K → G := fun x => (x.1 : G) * x.2 with hm_def`. Establish `hm : Measurable m` using `(measurable_subtype_coe.comp measurable_fst).mul (measurable_subtype_coe.comp measurable_snd)`. Use `set ν := map m (μP.prod μK) with hν`. Establish `hleft : ∀ p : P, map ((p : G) * ·) ν = ν`. Introduce `p`.

Rewrite using `[hν, map_map (continuous_const_mul _).measurable hm]`. Establish `: ((p : G) * ·) ∘ m = m ∘ Prod.map (p * ·) id`. Use function extensionality and compare the values at `x`. Simplify using `[m, mul_assoc]`. Rewrite using `[this, ← map_map hm ((continuous_const_mul p).measurable.prodMap measurable_id), ← map_prod_map _ _ (continuous_const_mul p).measurable measurable_id, map_mul_left_eq_self, Measure.map_id]`.

Establish `hright : ∀ k : K, map (· * (k : G)) ν = ν`. Introduce `k`. Rewrite using `[hν, map_map (continuous_mul_const _).measurable hm]`. Establish `: (· * (k : G)) ∘ m = m ∘ Prod.map id (· * k)`. Use function extensionality and compare the values at `x`.

Simplify using `[m, mul_assoc]`. Rewrite using `[this, ← map_map hm (measurable_id.prodMap (continuous_mul_const k).measurable), ← map_prod_map _ _ measurable_id (continuous_mul_const k).measurable, map_mul_right_eq_self_of_compactSpace, Measure.map_id]`. Establish `hνK : ν K = μP (Subtype.val ⁻¹' (K : Set G)) * μK univ`. Rewrite using `[hν, map_apply hm hKo.measurableSet]`. Establish `: m ⁻¹' (K : Set G) = (Subtype.val ⁻¹' (K : Set G)) ×ˢ (univ : Set K)`.

Use extensionality with `⟨p, k⟩`. Simplify using `only [Set.mem_preimage, SetLike.mem_coe, Set.mem_prod, Set.mem_univ, and_true, m]`. Conclude with `K.mul_mem_cancel_right k.2`. Rewrite using `[this, prod_prod]`. Establish `hPKc : IsCompact (Subtype.val ⁻¹' (K : Set G) : Set P)` using `hP.isClosedEmbedding_subtypeVal.isCompact_preimage hKc`.

Establish `hνKfin : ν K ≠ ∞`. Rewrite using `[hνK]`. Conclude with `ENNReal.mul_ne_top hPKc.measure_lt_top.ne (measure_ne_top _ _)`. Establish `hcoset : ∀ N, IsSmallNormal K N → ∀ x : G, ν (x • (N : Set G)) = ν N`. Introduce `N hN x`.

Take `⟨p, hp, k, hk, rfl⟩` from `hPK x`. Establish `h1 : ν ((p * k) • (N : Set G)) = ν (k • (N : Set G))`. Use `congrArg (fun μ : Measure G => μ ((p * k) • (N : Set G))) (hleft ⟨p, hp⟩)` as an intermediate fact. Simplify using `only at this`. Rewrite `this` using `[map_apply (continuous_const_mul _).measurable (hN.1.smul _).measurableSet]`.

Rewrite using `[← this]`. Use `congr 1`. Use extensionality with `y`. Simplify using `only [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul]`. Rewrite using `[show (p * k)⁻¹ * (p * y) = k⁻¹ * y by group]`.

Establish `h2 : ν (k • (N : Set G)) = ν N`. Use `congrArg (fun μ : Measure G => μ N) (hright ⟨k⁻¹, K.inv_mem hk⟩)` as an intermediate fact. Simplify using `only at this`. Rewrite `this` using `[map_apply (continuous_mul_const _).measurable hN.1.measurableSet]`. Rewrite using `[← this]`.

Use `congr 1`. Use extensionality with `y`. Simplify using `only [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul, SetLike.mem_coe]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Use `hN.2.2 k hk _ h` as an intermediate fact. Simplify `this` using `[mul_assoc]`. Introduce `h`. Use `hN.2.2 k⁻¹ (K.inv_mem hk) _ h` as an intermediate fact. Simplify `this` using `[mul_assoc]`.

Rewrite using `[h1, h2]`. Establish `hfin : ∀ N, IsSmallNormal K N → ∀ x : G, ν (x • (N : Set G)) ≠ ∞` using `fun N hN x => by`. Rewrite using `[hcoset N hN x]`. Conclude with `ne_top_of_le_ne_top hνKfin (measure_mono hN.2.1)`. Establish `hKsmall : IsSmallNormal K K` using `⟨hKo, le_rfl, fun k hk y hy => K.mul_mem (K.mul_mem hk hy) (K.inv_mem hk)⟩`.

Choose the witnesses or unpack the hypotheses as in `⟨B, hB⟩ : ∃ B : ℕ → G, ⋃ i, B i • (K : Set G) = univ := by`. Take `⟨T, hTc, hT⟩` from `TopologicalSpace.isOpen_iUnion_countable (fun x : G => x • (K : Set G)) fun x => hKo.smul x`. Establish `hU : ⋃ x : G, x • (K : Set G) = univ` using `eq_univ_of_forall fun y => mem_iUnion.2 ⟨y, ⟨1, K.one_mem, mul_one y⟩⟩`. Establish `hTne : T.Nonempty`. Assume the negation of the conclusion as `h`.

Rewrite `h` using `[Set.not_nonempty_iff_eq_empty]`. Rewrite `hT` using `[h, hU]`. Conclude with `Set.empty_ne_univ (by simpa using hT)`. Take `⟨f, rfl⟩` from `hTc.exists_eq_range hTne`. Use `⟨f, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hU, ← hT, Set.biUnion_range]`. Establish `hpre : ∀ (g x : G) (S : Set G), ((g * ·) ⁻¹' (x • S)) = (g⁻¹ * x) • S`. Introduce `g x S`. Use extensionality with `y`. Simplify using `only [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul]`.

Rewrite using `[show x⁻¹ * (g * y) = (g⁻¹ * x)⁻¹ * y by group]`. Establish `hinv : ν.IsMulLeftInvariant` using `⟨fun g => by`. Use `ext_of_generateFrom_of_iUnion (smallCosets K) (fun i => B i • (K : Set G)) (borel_eq_generateFrom_smallCosets hN) (isPiSystem_smallCosets K) hB (fun i => ⟨B i, K, hKsmall, rfl⟩) (fun i => ?_) ?_` and prove the remaining obligations. Rewrite using `[map_apply (continuous_const_mul g).measurable (hKo.smul _).measurableSet, hpre]`. Conclude with `hfin K hKsmall _`.

Introduce and unpack `_ ⟨x, N, hN', rfl⟩`. Rewrite using `[map_apply (continuous_const_mul g).measurable (hN'.1.smul _).measurableSet, hpre, hcoset N hN', hcoset N hN']⟩`. Establish `hfc : IsFiniteMeasureOnCompacts ν` using `⟨fun C hC => by`. Take `⟨t, ht⟩` from `hC.elim_finite_subcover (fun x : G => x • (K : Set G)) (fun x => hKo.smul x) fun y _ => mem_iUnion.2 ⟨y, ⟨1, K.one_mem, mul_one y⟩⟩`. Combine the equalities or inequalities in the displayed calculation.

Establish `e` using `isMulLeftInvariant_eq_smul ν μG`. Rewrite using `[← hνK, e]`. Use extensionality with `s hs`. Simplify using `only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem map_mul_prod_eq_smul [TotallyDisconnectedSpace G] (P K : Subgroup G)
    (hP : IsClosed (P : Set G))
    (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G))
    (hPK : ∀ g : G, ∃ p ∈ P, ∃ k ∈ K, g = p * k)
    (μG : Measure G) [μG.IsHaarMeasure] (μP : Measure P) [μP.IsHaarMeasure] (μK : Measure K)
    [μK.IsHaarMeasure] :
    μG K • map (fun x : P × K => (x.1 : G) * x.2) (μP.prod μK) =
      (μP (Subtype.val ⁻¹' (K : Set G)) * μK univ) • μG := by
  have hN : ∀ U ∈ 𝓝 (1 : G), ∃ N : Subgroup G, IsSmallNormal K N ∧ (N : Set G) ⊆ U := by
    intro U hU
    obtain ⟨N, -, hNU, hNK⟩ :=
      exists_compactOpenSubgroup_normalized hKc (inter_mem hU (hKo.mem_nhds K.one_mem))
    exact ⟨N, ⟨N.isOpen, fun x hx => (hNU hx).2, hNK⟩, fun x hx => (hNU hx).1⟩
  have : LocallyCompactSpace P := hP.locallyCompactSpace
  have : CompactSpace K := isCompact_iff_compactSpace.1 hKc
  have : SecondCountableTopology P := IsEmbedding.subtypeVal.secondCountableTopology
  have : SecondCountableTopology K := IsEmbedding.subtypeVal.secondCountableTopology
  have : BorelSpace P := Subtype.borelSpace (P : Set G)
  have : BorelSpace K := Subtype.borelSpace (K : Set G)
  set m : P × K → G := fun x => (x.1 : G) * x.2 with hm_def
  have hm : Measurable m :=
    (measurable_subtype_coe.comp measurable_fst).mul
      (measurable_subtype_coe.comp measurable_snd)
  set ν := map m (μP.prod μK) with hν
  have hleft : ∀ p : P, map ((p : G) * ·) ν = ν := by
    intro p
    rw [hν, map_map (continuous_const_mul _).measurable hm]
    have : ((p : G) * ·) ∘ m = m ∘ Prod.map (p * ·) id := by
      funext x
      simp [m, mul_assoc]
    rw [this, ← map_map hm ((continuous_const_mul p).measurable.prodMap measurable_id),
      ← map_prod_map _ _ (continuous_const_mul p).measurable measurable_id,
      map_mul_left_eq_self, Measure.map_id]
  have hright : ∀ k : K, map (· * (k : G)) ν = ν := by
    intro k
    rw [hν, map_map (continuous_mul_const _).measurable hm]
    have : (· * (k : G)) ∘ m = m ∘ Prod.map id (· * k) := by
      funext x
      simp [m, mul_assoc]
    rw [this, ← map_map hm (measurable_id.prodMap (continuous_mul_const k).measurable),
      ← map_prod_map _ _ measurable_id (continuous_mul_const k).measurable,
      map_mul_right_eq_self_of_compactSpace, Measure.map_id]
  have hνK : ν K = μP (Subtype.val ⁻¹' (K : Set G)) * μK univ := by
    rw [hν, map_apply hm hKo.measurableSet]
    have : m ⁻¹' (K : Set G) = (Subtype.val ⁻¹' (K : Set G)) ×ˢ (univ : Set K) := by
      ext ⟨p, k⟩
      simp only [Set.mem_preimage, SetLike.mem_coe, Set.mem_prod, Set.mem_univ, and_true, m]
      exact K.mul_mem_cancel_right k.2
    rw [this, prod_prod]
  have hPKc : IsCompact (Subtype.val ⁻¹' (K : Set G) : Set P) :=
    hP.isClosedEmbedding_subtypeVal.isCompact_preimage hKc
  have hνKfin : ν K ≠ ∞ := by
    rw [hνK]
    exact ENNReal.mul_ne_top hPKc.measure_lt_top.ne (measure_ne_top _ _)
  have hcoset : ∀ N, IsSmallNormal K N → ∀ x : G, ν (x • (N : Set G)) = ν N := by
    intro N hN x
    obtain ⟨p, hp, k, hk, rfl⟩ := hPK x
    have h1 : ν ((p * k) • (N : Set G)) = ν (k • (N : Set G)) := by
      have := congrArg (fun μ : Measure G => μ ((p * k) • (N : Set G))) (hleft ⟨p, hp⟩)
      simp only at this
      rw [map_apply (continuous_const_mul _).measurable (hN.1.smul _).measurableSet] at this
      rw [← this]
      congr 1
      ext y
      simp only [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul]
      rw [show (p * k)⁻¹ * (p * y) = k⁻¹ * y by group]
    have h2 : ν (k • (N : Set G)) = ν N := by
      have := congrArg (fun μ : Measure G => μ N) (hright ⟨k⁻¹, K.inv_mem hk⟩)
      simp only at this
      rw [map_apply (continuous_mul_const _).measurable hN.1.measurableSet] at this
      rw [← this]
      congr 1
      ext y
      simp only [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul,
        SetLike.mem_coe]
      constructor
      · intro h
        have := hN.2.2 k hk _ h
        simpa [mul_assoc] using this
      · intro h
        have := hN.2.2 k⁻¹ (K.inv_mem hk) _ h
        simpa [mul_assoc] using this
    rw [h1, h2]
  have hfin : ∀ N, IsSmallNormal K N → ∀ x : G, ν (x • (N : Set G)) ≠ ∞ := fun N hN x => by
    rw [hcoset N hN x]
    exact ne_top_of_le_ne_top hνKfin (measure_mono hN.2.1)
  have hKsmall : IsSmallNormal K K :=
    ⟨hKo, le_rfl, fun k hk y hy => K.mul_mem (K.mul_mem hk hy) (K.inv_mem hk)⟩
  obtain ⟨B, hB⟩ : ∃ B : ℕ → G, ⋃ i, B i • (K : Set G) = univ := by
    obtain ⟨T, hTc, hT⟩ := TopologicalSpace.isOpen_iUnion_countable
      (fun x : G => x • (K : Set G)) fun x => hKo.smul x
    have hU : ⋃ x : G, x • (K : Set G) = univ :=
      eq_univ_of_forall fun y => mem_iUnion.2 ⟨y, ⟨1, K.one_mem, mul_one y⟩⟩
    have hTne : T.Nonempty := by
      by_contra h
      rw [Set.not_nonempty_iff_eq_empty] at h
      rw [h, hU] at hT
      exact Set.empty_ne_univ (by simpa using hT)
    obtain ⟨f, rfl⟩ := hTc.exists_eq_range hTne
    refine ⟨f, ?_⟩
    rw [← hU, ← hT, Set.biUnion_range]
  have hpre : ∀ (g x : G) (S : Set G), ((g * ·) ⁻¹' (x • S)) = (g⁻¹ * x) • S := by
    intro g x S
    ext y
    simp only [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul]
    rw [show x⁻¹ * (g * y) = (g⁻¹ * x)⁻¹ * y by group]
  have hinv : ν.IsMulLeftInvariant := ⟨fun g => by
    refine ext_of_generateFrom_of_iUnion (smallCosets K) (fun i => B i • (K : Set G))
      (borel_eq_generateFrom_smallCosets hN) (isPiSystem_smallCosets K) hB
      (fun i => ⟨B i, K, hKsmall, rfl⟩) (fun i => ?_) ?_
    · rw [map_apply (continuous_const_mul g).measurable (hKo.smul _).measurableSet, hpre]
      exact hfin K hKsmall _
    · rintro _ ⟨x, N, hN', rfl⟩
      rw [map_apply (continuous_const_mul g).measurable (hN'.1.smul _).measurableSet, hpre,
        hcoset N hN', hcoset N hN']⟩
  have hfc : IsFiniteMeasureOnCompacts ν := ⟨fun C hC => by
    obtain ⟨t, ht⟩ := hC.elim_finite_subcover (fun x : G => x • (K : Set G))
      (fun x => hKo.smul x) fun y _ => mem_iUnion.2 ⟨y, ⟨1, K.one_mem, mul_one y⟩⟩
    calc ν C ≤ ν (⋃ x ∈ t, x • (K : Set G)) := measure_mono ht
      _ ≤ ∑ x ∈ t, ν (x • (K : Set G)) := measure_biUnion_finset_le _ _
      _ < ∞ := ENNReal.sum_lt_top.2 fun x _ => (hfin K hKsmall x).lt_top⟩
  have e := isMulLeftInvariant_eq_smul ν μG
  rw [← hνK, e]
  ext s hs
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  ring

/- English proof (translation)
Establish `: LocallyCompactSpace P` using `hP.locallyCompactSpace`. Establish `: CompactSpace K` using `isCompact_iff_compactSpace.1 hKc`. Establish `: SecondCountableTopology P` using `IsEmbedding.subtypeVal.secondCountableTopology`. Establish `: SecondCountableTopology K` using `IsEmbedding.subtypeVal.secondCountableTopology`. Establish `: BorelSpace P` using `Subtype.borelSpace (P : Set G)`.

Establish `: BorelSpace K` using `Subtype.borelSpace (K : Set G)`. Establish `hm : Measurable fun x : P × K => (x.1 : G) * x.2` using `(measurable_subtype_coe.comp measurable_fst).mul (measurable_subtype_coe.comp measurable_snd)`. Establish `h` using `congrArg (fun μ : Measure G => ∫⁻ g, f g ∂μ) (map_mul_prod_eq_smul P K hP hKo hKc hPK μG μP μK)`. Simplify using `only [lintegral_smul_measure, smul_eq_mul] at h`. Rewrite `h` using `[lintegral_map hf hm, lintegral_prod (fun x : P × K => f ((x.1 : G) * x.2)) (hf.comp hm).aemeasurable]`.

Conclude with `h`.
-/
theorem lintegral_mul_prod_eq [TotallyDisconnectedSpace G] (P K : Subgroup G)
    (hP : IsClosed (P : Set G))
    (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G))
    (hPK : ∀ g : G, ∃ p ∈ P, ∃ k ∈ K, g = p * k)
    (μG : Measure G) [μG.IsHaarMeasure] (μP : Measure P) [μP.IsHaarMeasure] (μK : Measure K)
    [μK.IsHaarMeasure] {f : G → ℝ≥0∞} (hf : Measurable f) :
    μG K * ∫⁻ p, ∫⁻ k, f ((p : G) * k) ∂μK ∂μP =
      μP (Subtype.val ⁻¹' (K : Set G)) * μK univ * ∫⁻ g, f g ∂μG := by
  have : LocallyCompactSpace P := hP.locallyCompactSpace
  have : CompactSpace K := isCompact_iff_compactSpace.1 hKc
  have : SecondCountableTopology P := IsEmbedding.subtypeVal.secondCountableTopology
  have : SecondCountableTopology K := IsEmbedding.subtypeVal.secondCountableTopology
  have : BorelSpace P := Subtype.borelSpace (P : Set G)
  have : BorelSpace K := Subtype.borelSpace (K : Set G)
  have hm : Measurable fun x : P × K => (x.1 : G) * x.2 :=
    (measurable_subtype_coe.comp measurable_fst).mul
      (measurable_subtype_coe.comp measurable_snd)
  have h := congrArg (fun μ : Measure G => ∫⁻ g, f g ∂μ)
    (map_mul_prod_eq_smul P K hP hKo hKc hPK μG μP μK)
  simp only [lintegral_smul_measure, smul_eq_mul] at h
  rw [lintegral_map hf hm, lintegral_prod (fun x : P × K => f ((x.1 : G) * x.2))
    (hf.comp hm).aemeasurable] at h
  exact h

/- English proof (translation)
Establish `: LocallyCompactSpace P` using `hP.locallyCompactSpace`. Establish `: CompactSpace K` using `isCompact_iff_compactSpace.1 hKc`. Establish `: SecondCountableTopology P` using `IsEmbedding.subtypeVal.secondCountableTopology`. Establish `: SecondCountableTopology K` using `IsEmbedding.subtypeVal.secondCountableTopology`. Establish `: BorelSpace P` using `Subtype.borelSpace (P : Set G)`.

Establish `: BorelSpace K` using `Subtype.borelSpace (K : Set G)`. Establish `hm : Measurable fun x : P × K => (x.1 : G) * x.2` using `(measurable_subtype_coe.comp measurable_fst).mul (measurable_subtype_coe.comp measurable_snd)`. Establish `key` using `map_mul_prod_eq_smul P K hP hKo hKc hPK μG μP μK`. Use `set ν := map (fun x : P × K => (x.1 : G) * x.2) (μP.prod μK)`. Use `set d : ℝ≥0∞ := μP (Subtype.val ⁻¹' (K : Set G)) * μK univ with hd_def`.

Establish `hc0 : μG K ≠ 0` using `hKo.measure_ne_zero μG ⟨1, K.one_mem⟩`. Establish `hcT : μG K ≠ ∞` using `hKc.measure_lt_top.ne`. Establish `hPKc : IsCompact (Subtype.val ⁻¹' (K : Set G) : Set P)` using `hP.isClosedEmbedding_subtypeVal.isCompact_preimage hKc`. Establish `hdT : d ≠ ∞` using `ENNReal.mul_ne_top hPKc.measure_lt_top.ne (measure_ne_top _ _)`. Establish `hν : ν = ((μG K)⁻¹ * d) • μG`.

Rewrite using `[mul_smul, ← key, smul_smul, ENNReal.inv_mul_cancel hc0 hcT, one_smul]`. Establish `hfν : Integrable f ν`. Rewrite using `[hν]`. Conclude with `hf.smul_measure (ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hc0) hdT)`. Establish `hfm : Integrable (fun x : P × K => f ((x.1 : G) * x.2)) (μP.prod μK)` using `(integrable_map_measure hfν.aestronglyMeasurable hm.aemeasurable).1 hfν`.

Establish `h1 : ∫ g, f g ∂ν = ∫ p, ∫ k, f ((p : G) * k) ∂μK ∂μP`. Rewrite using `[integral_map hm.aemeasurable hfν.aestronglyMeasurable]`. Conclude with `integral_prod _ hfm`. Establish `h2 : ∫ g, f g ∂ν = ((μG K)⁻¹ * d).toReal • ∫ g, f g ∂μG`. Rewrite using `[hν, integral_smul_measure]`.

Rewrite using `[← h1, h2, smul_smul, ENNReal.toReal_mul, ENNReal.toReal_inv, ← mul_assoc, Measure.real, mul_inv_cancel₀ (ENNReal.toReal_ne_zero.2 ⟨hc0, hcT⟩), one_mul, hd_def, ENNReal.toReal_mul]`. Both sides reduce to the same expression.
-/
theorem integral_mul_prod_eq [TotallyDisconnectedSpace G] (P K : Subgroup G)
    (hP : IsClosed (P : Set G))
    (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G))
    (hPK : ∀ g : G, ∃ p ∈ P, ∃ k ∈ K, g = p * k)
    (μG : Measure G) [μG.IsHaarMeasure] (μP : Measure P) [μP.IsHaarMeasure] (μK : Measure K)
    [μK.IsHaarMeasure] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : G → E} (hf : Integrable f μG) :
    μG.real K • ∫ p, ∫ k, f ((p : G) * k) ∂μK ∂μP =
      (μP.real (Subtype.val ⁻¹' (K : Set G)) * μK.real univ) • ∫ g, f g ∂μG := by
  have : LocallyCompactSpace P := hP.locallyCompactSpace
  have : CompactSpace K := isCompact_iff_compactSpace.1 hKc
  have : SecondCountableTopology P := IsEmbedding.subtypeVal.secondCountableTopology
  have : SecondCountableTopology K := IsEmbedding.subtypeVal.secondCountableTopology
  have : BorelSpace P := Subtype.borelSpace (P : Set G)
  have : BorelSpace K := Subtype.borelSpace (K : Set G)
  have hm : Measurable fun x : P × K => (x.1 : G) * x.2 :=
    (measurable_subtype_coe.comp measurable_fst).mul
      (measurable_subtype_coe.comp measurable_snd)
  have key := map_mul_prod_eq_smul P K hP hKo hKc hPK μG μP μK
  set ν := map (fun x : P × K => (x.1 : G) * x.2) (μP.prod μK)
  set d : ℝ≥0∞ := μP (Subtype.val ⁻¹' (K : Set G)) * μK univ with hd_def
  have hc0 : μG K ≠ 0 := hKo.measure_ne_zero μG ⟨1, K.one_mem⟩
  have hcT : μG K ≠ ∞ := hKc.measure_lt_top.ne
  have hPKc : IsCompact (Subtype.val ⁻¹' (K : Set G) : Set P) :=
    hP.isClosedEmbedding_subtypeVal.isCompact_preimage hKc
  have hdT : d ≠ ∞ := ENNReal.mul_ne_top hPKc.measure_lt_top.ne (measure_ne_top _ _)
  have hν : ν = ((μG K)⁻¹ * d) • μG := by
    rw [mul_smul, ← key, smul_smul, ENNReal.inv_mul_cancel hc0 hcT, one_smul]
  have hfν : Integrable f ν := by
    rw [hν]
    exact hf.smul_measure (ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hc0) hdT)
  have hfm : Integrable (fun x : P × K => f ((x.1 : G) * x.2)) (μP.prod μK) :=
    (integrable_map_measure hfν.aestronglyMeasurable hm.aemeasurable).1 hfν
  have h1 : ∫ g, f g ∂ν = ∫ p, ∫ k, f ((p : G) * k) ∂μK ∂μP := by
    rw [integral_map hm.aemeasurable hfν.aestronglyMeasurable]
    exact integral_prod _ hfm
  have h2 : ∫ g, f g ∂ν = ((μG K)⁻¹ * d).toReal • ∫ g, f g ∂μG := by
    rw [hν, integral_smul_measure]
  rw [← h1, h2, smul_smul, ENNReal.toReal_mul, ENNReal.toReal_inv, ← mul_assoc, Measure.real,
    mul_inv_cancel₀ (ENNReal.toReal_ne_zero.2 ⟨hc0, hcT⟩), one_mul, hd_def, ENNReal.toReal_mul]
  rfl

end General

section GeneralLinear

variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (n : ℕ) {α : Type*} [LinearOrder α] {β : Fin n → α}

variable [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]

/- English proof (translation)
The claim follows from `lintegral_mul_prod_eq _ _ (isClosed_blockUpper F n β) (GLnLocal.isOpen_integralGL F n) (GLnLocal.isCompact_integralGL F n) (Iwasawa.exists_blockUpper_mul_integralGL F n hβ) μG μP μK hf`.
-/
theorem lintegral_parabolic_integralGL (hβ : Monotone β) (μG : Measure (GL (Fin n) F))
    [μG.IsHaarMeasure] (μP : Measure (Iwasawa.blockUpper F n β)) [μP.IsHaarMeasure]
    (μK : Measure (GLnLocal.integralGL F n)) [μK.IsHaarMeasure] {f : GL (Fin n) F → ℝ≥0∞}
    (hf : Measurable f) :
    μG (GLnLocal.integralGL F n) * ∫⁻ p, ∫⁻ k, f ((p : GL (Fin n) F) * k) ∂μK ∂μP =
      μP (Subtype.val ⁻¹' (GLnLocal.integralGL F n : Set (GL (Fin n) F))) * μK univ *
        ∫⁻ g, f g ∂μG :=
  lintegral_mul_prod_eq _ _ (isClosed_blockUpper F n β) (GLnLocal.isOpen_integralGL F n)
    (GLnLocal.isCompact_integralGL F n) (Iwasawa.exists_blockUpper_mul_integralGL F n hβ)
    μG μP μK hf

/- English proof (translation)
Establish `h` using `lintegral_parabolic_integralGL F n hβ μG μP μK hf`. Rewrite `h` using `[hG, hP, hK, one_mul, one_mul, one_mul]`. Conclude with `h.symm`.
-/
theorem lintegral_eq_lintegral_parabolic_integralGL (hβ : Monotone β)
    (μG : Measure (GL (Fin n) F)) [μG.IsHaarMeasure] (μP : Measure (Iwasawa.blockUpper F n β))
    [μP.IsHaarMeasure] (μK : Measure (GLnLocal.integralGL F n)) [μK.IsHaarMeasure]
    (hG : μG (GLnLocal.integralGL F n) = 1)
    (hP : μP (Subtype.val ⁻¹' (GLnLocal.integralGL F n : Set (GL (Fin n) F))) = 1)
    (hK : μK univ = 1) {f : GL (Fin n) F → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ g, f g ∂μG = ∫⁻ p, ∫⁻ k, f ((p : GL (Fin n) F) * k) ∂μK ∂μP := by
  have h := lintegral_parabolic_integralGL F n hβ μG μP μK hf
  rw [hG, hP, hK, one_mul, one_mul, one_mul] at h
  exact h.symm

/- English proof (translation)
The claim follows from `integral_mul_prod_eq _ _ (isClosed_blockUpper F n β) (GLnLocal.isOpen_integralGL F n) (GLnLocal.isCompact_integralGL F n) (Iwasawa.exists_blockUpper_mul_integralGL F n hβ) μG μP μK hf`.
-/
theorem integral_parabolic_integralGL (hβ : Monotone β) (μG : Measure (GL (Fin n) F))
    [μG.IsHaarMeasure] (μP : Measure (Iwasawa.blockUpper F n β)) [μP.IsHaarMeasure]
    (μK : Measure (GLnLocal.integralGL F n)) [μK.IsHaarMeasure] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {f : GL (Fin n) F → E}
    (hf : Integrable f μG) :
    μG.real (GLnLocal.integralGL F n) • ∫ p, ∫ k, f ((p : GL (Fin n) F) * k) ∂μK ∂μP =
      (μP.real (Subtype.val ⁻¹' (GLnLocal.integralGL F n : Set (GL (Fin n) F))) * μK.real univ) •
        ∫ g, f g ∂μG :=
  integral_mul_prod_eq _ _ (isClosed_blockUpper F n β) (GLnLocal.isOpen_integralGL F n)
    (GLnLocal.isCompact_integralGL F n) (Iwasawa.exists_blockUpper_mul_integralGL F n hβ)
    μG μP μK hf

/- English proof (translation)
Establish `h` using `integral_parabolic_integralGL F n hβ μG μP μK hf`. Simplify using `only [Measure.real, hG, hP, hK, ENNReal.toReal_one, one_mul, one_smul] at h`. Conclude with `h.symm`.
-/
theorem integral_eq_integral_parabolic_integralGL (hβ : Monotone β)
    (μG : Measure (GL (Fin n) F)) [μG.IsHaarMeasure] (μP : Measure (Iwasawa.blockUpper F n β))
    [μP.IsHaarMeasure] (μK : Measure (GLnLocal.integralGL F n)) [μK.IsHaarMeasure]
    (hG : μG (GLnLocal.integralGL F n) = 1)
    (hP : μP (Subtype.val ⁻¹' (GLnLocal.integralGL F n : Set (GL (Fin n) F))) = 1)
    (hK : μK univ = 1) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : GL (Fin n) F → E} (hf : Integrable f μG) :
    ∫ g, f g ∂μG = ∫ p, ∫ k, f ((p : GL (Fin n) F) * k) ∂μK ∂μP := by
  have h := integral_parabolic_integralGL F n hβ μG μP μK hf
  simp only [Measure.real, hG, hP, hK, ENNReal.toReal_one, one_mul, one_smul] at h
  exact h.symm

end GeneralLinear

end Measures

end GroundTheory.Automorphic
