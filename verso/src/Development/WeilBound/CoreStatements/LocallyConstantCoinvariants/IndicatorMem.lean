import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.RightOnto
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ExistsNhdsInvariant
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.PureEqPureA
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IdeleCongruenceUnitCriterion

noncomputable section

namespace PositivityTheory.KCo

open Filter Topology NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.Ar.RT.Move

/- English proof (translation)
Take `⟨h1, h2⟩` from `h`. Use `⟨?_, h2.mono (fun x hx => ?_)⟩` and prove the remaining obligations. Rewrite using `[IsLocallyConstant.iff_eventually_eq]`. Introduce `x`. Distinguish the cases in `hx : x ∈ U`.

Use `filter_upwards [hU.isOpen.mem_nhds hx, h1.eventually_eq x] with y hy hy'`. Simplify using `[Set.indicator_of_mem hy, Set.indicator_of_mem hx, hy']`. Use `filter_upwards [hU.compl.isOpen.mem_nhds hx] with y hy`. Simplify using `[Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]`. Distinguish the cases in `hxU : x ∈ U`.

Simplify `hx` using `[Function.mem_support, hxU]`. Simplify using `[Function.mem_support, hxU] at hx`.
-/
theorem indicator_mem {X : Type} [TopologicalSpace X] {U : Set X} (hU : IsClopen U) {Φ : X → ℂ} (h : Φ ∈ SB X) :
    U.indicator Φ ∈ SB X := by
  classical
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, h2.mono (fun x hx => ?_)⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    by_cases hx : x ∈ U
    · filter_upwards [hU.isOpen.mem_nhds hx, h1.eventually_eq x] with y hy hy'
      simp [Set.indicator_of_mem hy, Set.indicator_of_mem hx, hy']
    · filter_upwards [hU.compl.isOpen.mem_nhds hx] with y hy
      simp [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]
  · by_cases hxU : x ∈ U
    · simpa [Function.mem_support, hxU] using hx
    · simp [Function.mem_support, hxU] at hx

/- English proof (translation)
Introduce `Φ hΦ hΦ0`. Set `mm : X → X → ℂ` to `fun Y => if hY : Y = Y₁ then 0 else Classical.choose (h Y hY)`. Establish `hmm : ∀ Y, Y ≠ Y₁ → IsLocallyConstant (mm Y) ∧ mm Y Y ≠ mm Y Y₁ ∧ ∀ Φ ∈ SB X, (fun y => (mm Y y - mm Y Y₁) * Φ y) ∈ N`. Introduce `Y hY`. Simplify using `only [mm, dif_neg hY]`.

Conclude with `Classical.choose_spec (h Y hY)`. Set `U : X → Set X` to `fun Y => {y | mm Y y ≠ mm Y Y₁}`. Establish `hUc : ∀ Y, Y ≠ Y₁ → IsClopen (U Y)`. Introduce `Y hY`. Conclude with `((hmm Y hY).1.isClopen_fiber (mm Y Y₁)).compl`.

Establish `key : ∀ (s : Finset X), (∀ Y ∈ s, Y ≠ Y₁) → ∀ Ψ ∈ SB X, Function.support Ψ ⊆ ⋃ Y ∈ s, U Y → Ψ ∈ N`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Introduce `_ Ψ _ hs`.

Establish `h0 : Ψ = 0`. Use extensionality with `x`. Assume the negation of the conclusion as `hx`. Use `hs hx` as an intermediate fact. Simplify using `at this`.

Rewrite using `[h0]`. Conclude with `N.zero_mem`. Consider the case `insert Y s hYs ih`. Introduce `hne Ψ hΨ hs`. Establish `hY : Y ≠ Y₁` using `hne Y (Finset.mem_insert_self _ _)`.

Establish `hsplit : Ψ = (U Y).indicator Ψ + (U Y)ᶜ.indicator Ψ` using `(Set.indicator_self_add_compl _ _).symm`. Rewrite using `[hsplit]`. Use `N.add_mem ?_ ?_` and prove the remaining obligations. Take `⟨hlc, _, hN⟩` from `hmm Y hY`. Establish `hg : IsLocallyConstant (fun y => (mm Y y - mm Y Y₁)⁻¹)` using `hlc.comp (fun a => (a - mm Y Y₁)⁻¹)`.

Establish `hΨg : (Ψ * fun y => (mm Y y - mm Y Y₁)⁻¹) ∈ SB X` using `⟨hΨ.1.mul hg, hΨ.2.mul_right⟩`. Establish `hI` using `hN _ (indicator_mem (hUc Y hY) hΨg)`. Use `hI using 1` and compare the differences between its conclusion and the goal. Use extensionality with `y`. Distinguish the cases in `hy : y ∈ U Y`.

Establish `hy' : mm Y y - mm Y Y₁ ≠ 0` using `sub_ne_zero.mpr hy`. Rewrite using `[Set.indicator_of_mem hy, Set.indicator_of_mem hy]`. Simplify using `only [Pi.mul_apply]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, mul_zero]`.

Use `ih (fun Z hZ => hne Z (Finset.mem_insert_of_mem hZ)) _ (indicator_mem (hUc Y hY).compl hΨ) ?_` and prove the remaining obligations. Introduce `x hx`. Rewrite `hx` using `[Set.support_indicator]`. Take `⟨hx1, hx2⟩` from `hx`. Use `hs hx2` as an intermediate fact.

Simplify using `only [Set.mem_iUnion, Finset.mem_insert, exists_prop] at this ⊢`. Take `⟨Z, hZ, hxZ⟩` from `this`. Break down `hZ with rfl | hZ` into its components or cases. Conclude with `absurd hxZ hx1`. Conclude with `⟨Z, hZ, hxZ⟩`.

Establish `hcl : IsClosed (Function.support Φ)` using `(hΦ.1.isClopen_fiber 0).isOpen.isClosed_compl`. Establish `hS : IsCompact (Function.support Φ)` using `hΦ.2.isCompact.of_isClosed_subset hcl (subset_tsupport Φ)`. Establish `hne : ∀ x ∈ Function.support Φ, x ≠ Y₁`. Introduce and unpack `x hx rfl`. Conclude with `hx hΦ0`.

Establish `hnhds : ∀ x ∈ Function.support Φ, U x ∈ 𝓝 x` using `fun x hx => (hUc x (hne x hx)).isOpen.mem_nhds (hmm x (hne x hx)).2.1`. Take `⟨t, ht, hcov⟩` from `hS.elim_nhds_subcover U hnhds`. Conclude with `key t (fun Y hY => hne Y (ht Y hY)) Φ hΦ hcov`.
-/
theorem kill {X : Type} [TopologicalSpace X] (N : Submodule ℂ (X → ℂ)) (Y₁ : X)
    (h : ∀ Y ≠ Y₁, ∃ m : X → ℂ, IsLocallyConstant m ∧ m Y ≠ m Y₁ ∧ ∀ Φ ∈ SB X, (fun y => (m y - m Y₁) * Φ y) ∈ N) :
    ∀ Φ ∈ SB X, Φ Y₁ = 0 → Φ ∈ N := by
  classical
  intro Φ hΦ hΦ0
  let mm : X → X → ℂ := fun Y => if hY : Y = Y₁ then 0 else Classical.choose (h Y hY)
  have hmm : ∀ Y, Y ≠ Y₁ → IsLocallyConstant (mm Y) ∧ mm Y Y ≠ mm Y Y₁ ∧
      ∀ Φ ∈ SB X, (fun y => (mm Y y - mm Y Y₁) * Φ y) ∈ N := by
    intro Y hY
    simp only [mm, dif_neg hY]
    exact Classical.choose_spec (h Y hY)
  let U : X → Set X := fun Y => {y | mm Y y ≠ mm Y Y₁}
  have hUc : ∀ Y, Y ≠ Y₁ → IsClopen (U Y) := by
    intro Y hY
    exact ((hmm Y hY).1.isClopen_fiber (mm Y Y₁)).compl
  have key : ∀ (s : Finset X), (∀ Y ∈ s, Y ≠ Y₁) → ∀ Ψ ∈ SB X,
      Function.support Ψ ⊆ ⋃ Y ∈ s, U Y → Ψ ∈ N := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _ Ψ _ hs
      have h0 : Ψ = 0 := by
        ext x
        by_contra hx
        have := hs hx
        simp at this
      rw [h0]
      exact N.zero_mem
    | insert Y s hYs ih =>
      intro hne Ψ hΨ hs
      have hY : Y ≠ Y₁ := hne Y (Finset.mem_insert_self _ _)
      have hsplit : Ψ = (U Y).indicator Ψ + (U Y)ᶜ.indicator Ψ :=
        (Set.indicator_self_add_compl _ _).symm
      rw [hsplit]
      refine N.add_mem ?_ ?_
      · obtain ⟨hlc, _, hN⟩ := hmm Y hY
        have hg : IsLocallyConstant (fun y => (mm Y y - mm Y Y₁)⁻¹) :=
          hlc.comp (fun a => (a - mm Y Y₁)⁻¹)
        have hΨg : (Ψ * fun y => (mm Y y - mm Y Y₁)⁻¹) ∈ SB X := ⟨hΨ.1.mul hg, hΨ.2.mul_right⟩
        have hI := hN _ (indicator_mem (hUc Y hY) hΨg)
        convert hI using 1
        ext y
        by_cases hy : y ∈ U Y
        · have hy' : mm Y y - mm Y Y₁ ≠ 0 := sub_ne_zero.mpr hy
          rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]
          simp only [Pi.mul_apply]
          field_simp
        · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, mul_zero]
      · refine ih (fun Z hZ => hne Z (Finset.mem_insert_of_mem hZ)) _
          (indicator_mem (hUc Y hY).compl hΨ) ?_
        intro x hx
        rw [Set.support_indicator] at hx
        obtain ⟨hx1, hx2⟩ := hx
        have := hs hx2
        simp only [Set.mem_iUnion, Finset.mem_insert, exists_prop] at this ⊢
        obtain ⟨Z, hZ, hxZ⟩ := this
        rcases hZ with rfl | hZ
        · exact absurd hxZ hx1
        · exact ⟨Z, hZ, hxZ⟩
  have hcl : IsClosed (Function.support Φ) := (hΦ.1.isClopen_fiber 0).isOpen.isClosed_compl
  have hS : IsCompact (Function.support Φ) := hΦ.2.isCompact.of_isClosed_subset hcl (subset_tsupport Φ)
  have hne : ∀ x ∈ Function.support Φ, x ≠ Y₁ := by
    rintro x hx rfl
    exact hx hΦ0
  have hnhds : ∀ x ∈ Function.support Φ, U x ∈ 𝓝 x := fun x hx =>
    (hUc x (hne x hx)).isOpen.mem_nhds (hmm x (hne x hx)).2.1
  obtain ⟨t, ht, hcov⟩ := hS.elim_nhds_subcover U hnhds
  exact key t (fun Y hY => hne Y (ht Y hY)) Φ hΦ hcov

/- English proof (translation)
Rewrite using `[IsLocallyConstant.iff_eventually_eq]`. Introduce `x`. Take `⟨K, hK, hKx⟩` from `exists_compact_mem_nhds x`. Take `⟨V, hVc, hxV, hVK⟩` from `loc_compact_Haus_tot_disc_of_zero_dim.mem_nhds_iff.1 hKx`. Establish `hVc' : IsClopen V` using `hVc`.

Establish `hVcomp : IsCompact V` using `hK.of_isClosed_subset hVc'.1 hVK`. Establish `hΦ : V.indicator (1 : X → ℂ) ∈ SB X`. Use `⟨?_, HasCompactSupport.intro hVcomp (fun y hy => Set.indicator_of_notMem hy _)⟩` and prove the remaining obligations. Rewrite using `[IsLocallyConstant.iff_eventually_eq]`. Introduce `z`.

Distinguish the cases in `hz : z ∈ V`. Use `filter_upwards [hVc'.isOpen.mem_nhds hz] with y hy`. Simplify using `[Set.indicator_of_mem hy, Set.indicator_of_mem hz]`. Use `filter_upwards [hVc'.compl.isOpen.mem_nhds hz] with y hy`. Simplify using `[Set.indicator_of_notMem hy, Set.indicator_of_notMem hz]`.

Establish `hm` using `(h _ hΦ).1.eventually_eq x`. Use `filter_upwards [hm, hVc'.isOpen.mem_nhds hxV] with y hy hyV`. Simplify `hy` using `[Set.indicator_of_mem hyV, Set.indicator_of_mem hxV]`.
-/
theorem lc_of_mul {X : Type} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [TotallyDisconnectedSpace X] (m : X → ℂ)
    (h : ∀ Φ ∈ SB X, (fun y => m y * Φ y) ∈ SB X) : IsLocallyConstant m := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  obtain ⟨K, hK, hKx⟩ := exists_compact_mem_nhds x
  obtain ⟨V, hVc, hxV, hVK⟩ := loc_compact_Haus_tot_disc_of_zero_dim.mem_nhds_iff.1 hKx
  have hVc' : IsClopen V := hVc
  have hVcomp : IsCompact V := hK.of_isClosed_subset hVc'.1 hVK
  have hΦ : V.indicator (1 : X → ℂ) ∈ SB X := by
    refine ⟨?_, HasCompactSupport.intro hVcomp (fun y hy => Set.indicator_of_notMem hy _)⟩
    rw [IsLocallyConstant.iff_eventually_eq]
    intro z
    by_cases hz : z ∈ V
    · filter_upwards [hVc'.isOpen.mem_nhds hz] with y hy
      simp [Set.indicator_of_mem hy, Set.indicator_of_mem hz]
    · filter_upwards [hVc'.compl.isOpen.mem_nhds hz] with y hy
      simp [Set.indicator_of_notMem hy, Set.indicator_of_notMem hz]
  have hm := (h _ hΦ).1.eventually_eq x
  filter_upwards [hm, hVc'.isOpen.mem_nhds hxV] with y hy hyV
  simpa [Set.indicator_of_mem hyV, Set.indicator_of_mem hxV] using hy

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

def ballAt (M : ℕ) (c : κ → Af F) (v : Pl F) : Set (κ → Fv F v) :=
  {z | ∀ i, Valued.v (z i - evalV F v (c i)) ≤ v.intValuation (M : 𝓞 F)}

/- English proof (translation)
Use `set π : Fv F v := ((M : 𝓞 F) : Fv F v) with hπ`. Establish `hv : Valued.v π = v.intValuation (M : 𝓞 F)`. Rewrite using `[hπ, IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation', IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]`. Establish `hM' : (M : 𝓞 F) ≠ 0` using `Nat.cast_ne_zero.mpr hM`. Establish `hv0 : Valued.v π ≠ 0` using `hv ▸ IsDedekindDomain.HeightOneSpectrum.intValuation_ne_zero v _ hM'`.

Establish `hπ0 : π ≠ 0` using `fun h => hv0 (by rw [h, map_zero])`. Establish `hS : {z : Fv F v | Valued.v (z - a) ≤ v.intValuation (M : 𝓞 F)} = (fun z => (z - a) * π⁻¹) ⁻¹' (v.adicCompletionIntegers F : Set (Fv F v))`. Use extensionality with `z`. Simplify using `only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe, IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, map_inv₀, ← hv]`. Rewrite using `[mul_inv_le_iff₀ (zero_lt_iff.mpr hv0), one_mul]`.

Establish `hO : IsClopen (v.adicCompletionIntegers F : Set (Fv F v))` using `Valued.isClopen_valuationSubring _`. Establish `hcont : Continuous (fun z : Fv F v => (z - a) * π⁻¹)` using `(continuous_id.sub continuous_const).mul continuous_const`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hS]`. Conclude with `hO.preimage hcont`.

Establish `himg : {z : Fv F v | Valued.v (z - a) ≤ v.intValuation (M : 𝓞 F)} = (fun y => a + π * y) '' (v.adicCompletionIntegers F : Set (Fv F v))`. Rewrite using `[hS]`. Use extensionality with `z`. Prove the components needed by the constructor for the conclusion. Introduce `hz`.

Use `⟨(z - a) * π⁻¹, hz, ?_⟩` and prove the remaining obligations. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Introduce and unpack `⟨y, hy, rfl⟩`. Establish `: (a + π * y - a) * π⁻¹ = y` using `by field_simp; ring`.

Use `show (a + π * y - a) * π⁻¹ ∈ (v.adicCompletionIntegers F : Set (Fv F v))`. Rewrite using `[this]`. Conclude with `hy`. Rewrite using `[himg]`. Establish `hc : IsCompact (v.adicCompletionIntegers F : Set (Fv F v))`.

Use `GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v` as an intermediate fact. Conclude with `isCompact_iff_compactSpace.mpr this`. Conclude with `hc.image (continuous_const.add (continuous_const.mul continuous_id))`.
-/
private theorem coord_lemma {M : ℕ} (hM : M ≠ 0) (v : Pl F) (a : Fv F v) :
    IsClopen {z : Fv F v | Valued.v (z - a) ≤ v.intValuation (M : 𝓞 F)} ∧
      IsCompact {z : Fv F v | Valued.v (z - a) ≤ v.intValuation (M : 𝓞 F)} := by
  set π : Fv F v := ((M : 𝓞 F) : Fv F v) with hπ
  have hv : Valued.v π = v.intValuation (M : 𝓞 F) := by
    rw [hπ, IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
      IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
  have hM' : (M : 𝓞 F) ≠ 0 := Nat.cast_ne_zero.mpr hM
  have hv0 : Valued.v π ≠ 0 := hv ▸ IsDedekindDomain.HeightOneSpectrum.intValuation_ne_zero v _ hM'
  have hπ0 : π ≠ 0 := fun h => hv0 (by rw [h, map_zero])
  have hS : {z : Fv F v | Valued.v (z - a) ≤ v.intValuation (M : 𝓞 F)} =
      (fun z => (z - a) * π⁻¹) ⁻¹' (v.adicCompletionIntegers F : Set (Fv F v)) := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe,
      IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, map_inv₀, ← hv]
    rw [mul_inv_le_iff₀ (zero_lt_iff.mpr hv0), one_mul]
  have hO : IsClopen (v.adicCompletionIntegers F : Set (Fv F v)) :=
    Valued.isClopen_valuationSubring _
  have hcont : Continuous (fun z : Fv F v => (z - a) * π⁻¹) :=
    (continuous_id.sub continuous_const).mul continuous_const
  refine ⟨?_, ?_⟩
  · rw [hS]
    exact hO.preimage hcont
  · have himg : {z : Fv F v | Valued.v (z - a) ≤ v.intValuation (M : 𝓞 F)} =
        (fun y => a + π * y) '' (v.adicCompletionIntegers F : Set (Fv F v)) := by
      rw [hS]
      ext z
      constructor
      · intro hz
        refine ⟨(z - a) * π⁻¹, hz, ?_⟩
        field_simp
        ring
      · rintro ⟨y, hy, rfl⟩
        have : (a + π * y - a) * π⁻¹ = y := by field_simp; ring
        show (a + π * y - a) * π⁻¹ ∈ (v.adicCompletionIntegers F : Set (Fv F v))
        rw [this]
        exact hy
    rw [himg]
    have hc : IsCompact (v.adicCompletionIntegers F : Set (Fv F v)) := by
      have := GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v
      exact isCompact_iff_compactSpace.mpr this
    exact hc.image (continuous_const.add (continuous_const.mul continuous_id))

/- English proof (translation)
Establish `hI : ballAt M c v = ⋂ i, (fun z : κ → Fv F v => z i) ⁻¹' {z : Fv F v | Valued.v (z - evalV F v (c i)) ≤ v.intValuation (M : 𝓞 F)}`. Use extensionality with `z`. Simplify using `[ballAt]`. Establish `hP : ballAt M c v = Set.pi Set.univ (fun i => {z : Fv F v | Valued.v (z - evalV F v (c i)) ≤ v.intValuation (M : 𝓞 F)})`. Use extensionality with `z`.

Simplify using `[ballAt]`. Establish `hcl : IsClopen (ballAt M c v)`. Rewrite using `[hI]`. Conclude with `isClopen_iInter_of_finite (fun i => (coord_lemma hM v _).1.preimage (continuous_apply i))`. Establish `hco : IsCompact (ballAt M c v)`.

Rewrite using `[hP]`. Conclude with `isCompact_univ_pi (fun i => (coord_lemma hM v _).2)`. Use `⟨?_, HasCompactSupport.intro hco (fun x hx => Set.indicator_of_notMem hx _)⟩` and prove the remaining obligations. Rewrite using `[IsLocallyConstant.iff_eventually_eq]`. Introduce `x`.

Distinguish the cases in `hx : x ∈ ballAt M c v`. Use `filter_upwards [hcl.isOpen.mem_nhds hx] with y hy`. Simplify using `[Set.indicator_of_mem hy, Set.indicator_of_mem hx]`. Use `filter_upwards [hcl.compl.isOpen.mem_nhds hx] with y hy`. Simplify using `[Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]`.
-/
theorem ball_mem {M : ℕ} (hM : M ≠ 0) (c : κ → Af F) (v : Pl F) : (ballAt M c v).indicator (1 : (κ → Fv F v) → ℂ) ∈ SB (κ → Fv F v) := by
  classical
  have hI : ballAt M c v = ⋂ i, (fun z : κ → Fv F v => z i) ⁻¹'
      {z : Fv F v | Valued.v (z - evalV F v (c i)) ≤ v.intValuation (M : 𝓞 F)} := by
    ext z
    simp [ballAt]
  have hP : ballAt M c v = Set.pi Set.univ (fun i =>
      {z : Fv F v | Valued.v (z - evalV F v (c i)) ≤ v.intValuation (M : 𝓞 F)}) := by
    ext z
    simp [ballAt]
  have hcl : IsClopen (ballAt M c v) := by
    rw [hI]
    exact isClopen_iInter_of_finite (fun i => (coord_lemma hM v _).1.preimage (continuous_apply i))
  have hco : IsCompact (ballAt M c v) := by
    rw [hP]
    exact isCompact_univ_pi (fun i => (coord_lemma hM v _).2)
  refine ⟨?_, HasCompactSupport.intro hco (fun x hx => Set.indicator_of_notMem hx _)⟩
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  by_cases hx : x ∈ ballAt M c v
  · filter_upwards [hcl.isOpen.mem_nhds hx] with y hy
    simp [Set.indicator_of_mem hy, Set.indicator_of_mem hx]
  · filter_upwards [hcl.compl.isOpen.mem_nhds hx] with y hy
    simp [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]

/- English proof (translation)
Establish `h1 : ∀ᶠ v in cofinite, (v : Pl F).intValuation (M : 𝓞 F) = 1`. Establish `hM' : (M : 𝓞 F) ≠ 0` using `Nat.cast_ne_zero.mpr hM`. Establish `hI : Ideal.span {(M : 𝓞 F)} ≠ 0`. Rewrite using `[Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]`. Conclude with `hM'`.

Rewrite using `[Filter.eventually_cofinite]`. Use `(Ideal.finite_factors hI).subset (fun v hv => ?_)` and prove the remaining obligations. Simplify using `only [Set.mem_setOf_eq, IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff, not_not] at hv`. Rewrite using `[Set.mem_setOf_eq, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]`. Conclude with `hv`.

Establish `h2 : ∀ᶠ v in cofinite, ∀ i, evalV F v (c i) ∈ (v : Pl F).adicCompletionIntegers F`. Rewrite using `[Filter.eventually_all]`. Introduce `i`. Conclude with `(c i).2`. Use `filter_upwards [h1, h2] with v hv1 hv2`.

Establish `hset : ballAt M c v = {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F}`. Use extensionality with `z`. Simplify using `only [ballAt, Set.mem_setOf_eq, hv1]`. Use `forall_congr' (fun i => ?_)` and prove the remaining obligations. Establish `hc` using `(IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (hv2 i)`.

Rewrite using `[IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `e : z i = (z i - evalV F v (c i)) + evalV F v (c i)` using `by ring`. Rewrite using `[e]`.

Conclude with `le_trans (Valuation.map_add _ _ _) (max_le h hc)`. Introduce `h`. Conclude with `le_trans (Valuation.map_sub _ _ _) (max_le h hc)`. Rewrite using `[hset]`.
-/
theorem ball_cof {M : ℕ} (hM : M ≠ 0) (c : κ → Af F) :
    ∀ᶠ v in cofinite, (ballAt M c v).indicator (1 : (κ → Fv F v) → ℂ) = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := by
  classical
  have h1 : ∀ᶠ v in cofinite, (v : Pl F).intValuation (M : 𝓞 F) = 1 := by
    have hM' : (M : 𝓞 F) ≠ 0 := Nat.cast_ne_zero.mpr hM
    have hI : Ideal.span {(M : 𝓞 F)} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact hM'
    rw [Filter.eventually_cofinite]
    refine (Ideal.finite_factors hI).subset (fun v hv => ?_)
    simp only [Set.mem_setOf_eq, IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff, not_not] at hv
    rw [Set.mem_setOf_eq, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    exact hv
  have h2 : ∀ᶠ v in cofinite, ∀ i, evalV F v (c i) ∈ (v : Pl F).adicCompletionIntegers F := by
    rw [Filter.eventually_all]
    intro i
    exact (c i).2
  filter_upwards [h1, h2] with v hv1 hv2
  have hset : ballAt M c v = {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} := by
    ext z
    simp only [ballAt, Set.mem_setOf_eq, hv1]
    refine forall_congr' (fun i => ?_)
    have hc := (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (hv2 i)
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
    constructor
    · intro h
      have e : z i = (z i - evalV F v (c i)) + evalV F v (c i) := by ring
      rw [e]
      exact le_trans (Valuation.map_add _ _ _) (max_le h hc)
    · intro h
      exact le_trans (Valuation.map_sub _ _ _) (max_le h hc)
  rw [hset]

def box (M : ℕ) (c : κ → Af F) (y : κ → Af F) : ℂ := ∏ᶠ v, (ballAt M c v).indicator (1 : (κ → Fv F v) → ℂ) fun i => evalV F v (y i)

def Near (M : ℕ) (c y : κ → Af F) : Prop := ∀ v i, Valued.v (evalV F v (y i) - evalV F v (c i)) ≤ v.intValuation (M : 𝓞 F)

/- English proof (translation)
The claim follows from `finprod_eq_one_of_forall_eq_one fun v => Set.indicator_of_mem (show _ ∈ ballAt M c v from h v) _`.
-/
theorem box_of_near {M : ℕ} {c y : κ → Af F} (h : Near M c y) : box M c y = 1 :=
  finprod_eq_one_of_forall_eq_one fun v => Set.indicator_of_mem (show _ ∈ ballAt M c v from h v) _

/- English proof (translation)
Unfold `Near at h`. Use `push_neg at h`. Take `⟨v, i, hvi⟩` from `h`. Unfold `box`. Apply `finprod_eq_zero _ v` to reduce the goal to its premises.

Apply `Set.indicator_of_notMem` to reduce the goal to its premises. Introduce `hm`. Conclude with `absurd (hm i) (not_le.mpr hvi)`. Establish `hcof` using `ball_cof hM c`. Establish `hy : ∀ᶠ w in cofinite, ∀ j, evalV F w (y j) ∈ (w : Pl F).adicCompletionIntegers F`.

Rewrite using `[Filter.eventually_all]`. Introduce `j`. Conclude with `(y j).2`. Establish `hev : ∀ᶠ w in cofinite, (ballAt M c w).indicator (1 : (κ → Fv F w) → ℂ) (fun j => evalV F w (y j)) = 1` using `by filter_upwards [hcof, hy] with w hw hwy`. Rewrite using `[hw]`.

Conclude with `Set.indicator_of_mem (show (fun j => evalV F w (y j)) ∈ {x : κ → Fv F w | ∀ j, x j ∈ w.adicCompletionIntegers F} from hwy) _`. Rewrite `hev` using `[Filter.eventually_cofinite]`. Conclude with `hev`.
-/
theorem box_of_not {M : ℕ} (hM : M ≠ 0) {c y : κ → Af F} (h : ¬ Near M c y) : box M c y = 0 := by
  unfold Near at h
  push_neg at h
  obtain ⟨v, i, hvi⟩ := h
  unfold box
  apply finprod_eq_zero _ v
  · apply Set.indicator_of_notMem
    intro hm
    exact absurd (hm i) (not_le.mpr hvi)
  · have hcof := ball_cof hM c
    have hy : ∀ᶠ w in cofinite, ∀ j, evalV F w (y j) ∈ (w : Pl F).adicCompletionIntegers F := by
      rw [Filter.eventually_all]
      intro j
      exact (y j).2
    have hev : ∀ᶠ w in cofinite,
        (ballAt M c w).indicator (1 : (κ → Fv F w) → ℂ) (fun j => evalV F w (y j)) = 1 := by
      filter_upwards [hcof, hy] with w hw hwy
      rw [hw]
      exact Set.indicator_of_mem (show (fun j => evalV F w (y j)) ∈ {x : κ → Fv F w | ∀ j, x j ∈ w.adicCompletionIntegers F} from hwy) _
    rw [Filter.eventually_cofinite] at hev
    exact hev

/- English proof (translation)
Introduce `v i`. Use `h v i` as an intermediate fact. Rewrite `this` using `[← Valuation.map_neg, neg_sub]`. Then use the resulting hypothesis.
-/
theorem Near.symm {M : ℕ} {c y : κ → Af F} (h : Near M c y) : Near M y c := by
  intro v i
  have := h v i
  rwa [← Valuation.map_neg, neg_sub] at this

/- English proof (translation)
Introduce `v i`. Establish `h1` using `h v i`. Establish `h2` using `h' v i`. Establish `: evalV F v (c i) - evalV F v (a i) = (evalV F v (c i) - evalV F v (b i)) + (evalV F v (b i) - evalV F v (a i))` using `by ring`. Rewrite using `[this]`.

Conclude with `le_trans (Valuation.map_add _ _ _) (max_le h2 h1)`.
-/
theorem Near.trans {M : ℕ} {a b c : κ → Af F} (h : Near M a b) (h' : Near M b c) : Near M a c := by
  intro v i
  have h1 := h v i
  have h2 := h' v i
  have : evalV F v (c i) - evalV F v (a i) = (evalV F v (c i) - evalV F v (b i)) + (evalV F v (b i) - evalV F v (a i)) := by ring
  rw [this]
  exact le_trans (Valuation.map_add _ _ _) (max_le h2 h1)

/- English proof (translation)
Use `set N := Ideal.absNorm v.asIdeal with hNdef`. Establish `hN0 : N ≠ 0`. Rewrite using `[Ne, hNdef, Ideal.absNorm_eq_zero_iff]`. Conclude with `v.ne_bot`. Establish `hNmem : (N : 𝓞 F) ∈ v.asIdeal` using `Ideal.absNorm_mem _`.

Use `set k : ℕ := (-(WithZero.log γ) + 1).toNat with hk`. Use `⟨N ^ k, pow_ne_zero _ hN0, ?_⟩` and prove the remaining obligations. Establish `h1 : v.intValuation ((N ^ k : ℕ) : 𝓞 F) ≤ WithZero.exp (-(k : ℤ))`. Rewrite using `[IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem]`. Use `push_cast`.

Conclude with `Ideal.pow_mem_pow hNmem k`. Use `lt_of_le_of_lt h1 ?_` and prove the remaining obligations. Rewrite using `[← WithZero.exp_log hγ, WithZero.exp_lt_exp]`. Use `Int.self_le_toNat (-(WithZero.log γ) + 1)` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
private theorem exists_natCast_intValuation_lt (v : Pl F) {γ : WithZero (Multiplicative ℤ)} (hγ : γ ≠ 0) :
    ∃ n : ℕ, n ≠ 0 ∧ v.intValuation (n : 𝓞 F) < γ := by
  set N := Ideal.absNorm v.asIdeal with hNdef
  have hN0 : N ≠ 0 := by
    rw [Ne, hNdef, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  have hNmem : (N : 𝓞 F) ∈ v.asIdeal := Ideal.absNorm_mem _
  set k : ℕ := (-(WithZero.log γ) + 1).toNat with hk
  refine ⟨N ^ k, pow_ne_zero _ hN0, ?_⟩
  have h1 : v.intValuation ((N ^ k : ℕ) : 𝓞 F) ≤ WithZero.exp (-(k : ℤ)) := by
    rw [IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem]
    push_cast
    exact Ideal.pow_mem_pow hNmem k
  refine lt_of_le_of_lt h1 ?_
  rw [← WithZero.exp_log hγ, WithZero.exp_lt_exp]
  have := Int.self_le_toNat (-(WithZero.log γ) + 1)
  omega

/- English proof (translation)
Use `forall_congr' (fun v => ?_)` and prove the remaining obligations. Establish `hM' : (M : 𝓞 F) ≠ 0` using `Nat.cast_ne_zero.mpr hM`. Establish `hv0 : v.intValuation (M : 𝓞 F) ≠ 0` using `IsDedekindDomain.HeightOneSpectrum.intValuation_ne_zero v _ hM'`. Establish `hval : Valued.v (((M : F)⁻¹ : F) : Fv F v) = (v.intValuation (M : 𝓞 F))⁻¹`. Rewrite using `[IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation', map_inv₀, ← IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := F)]`.

Use `congr 2`. Establish `happ : (algebraMap F (Af F) ((M : F)⁻¹) * a) v = (((M : F)⁻¹ : F) : Fv F v) * a v` using `rfl`. Rewrite using `[happ, IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, hval, inv_mul_le_iff₀ (zero_lt_iff.mpr hv0), mul_one]`.
-/
private theorem valuation_le_natCast_iff_inv_mul_mem_integers {M : ℕ} (hM : M ≠ 0) (a : Af F) :
    (∀ v : Pl F, Valued.v (a v) ≤ v.intValuation (M : 𝓞 F)) ↔
      (∀ v : Pl F, (algebraMap F (Af F) ((M : F)⁻¹) * a) v ∈ v.adicCompletionIntegers F) := by
  refine forall_congr' (fun v => ?_)
  have hM' : (M : 𝓞 F) ≠ 0 := Nat.cast_ne_zero.mpr hM
  have hv0 : v.intValuation (M : 𝓞 F) ≠ 0 := IsDedekindDomain.HeightOneSpectrum.intValuation_ne_zero v _ hM'
  have hval : Valued.v (((M : F)⁻¹ : F) : Fv F v) = (v.intValuation (M : 𝓞 F))⁻¹ := by
    rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation', map_inv₀,
      ← IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := F)]
    congr 2
  have happ : (algebraMap F (Af F) ((M : F)⁻¹) * a) v = (((M : F)⁻¹ : F) : Fv F v) * a v := rfl
  rw [happ, IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, hval,
    inv_mul_le_iff₀ (zero_lt_iff.mpr hv0), mul_one]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Conclude with `RestrictedProduct.isOpen_forall_mem (fun v => Valued.isOpen_valuationSubring _)`. Establish `hr` using `RestrictedProduct.range_structureMap (fun v : Pl F => Fv F v) (fun v => (v.adicCompletionIntegers F : Set (Fv F v))) (𝓕 := cofinite) haveI : ∀ v : Pl F, CompactSpace (v.adicCompletionIntegers F) := fun v => GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v`. Establish `hc` using `isCompact_range (RestrictedProduct.isEmbedding_structureMap (R := fun v : Pl F => Fv F v) (A := fun v => (v.adicCompletionIntegers F : Set (Fv F v))) (𝓕 := cofinite)).continuous`. Rewrite `hc` using `[hr]`.

Conclude with `hc`.
-/
private theorem isOpen_isCompact_adelic_integers :
    IsOpen {a : Af F | ∀ v : Pl F, a v ∈ v.adicCompletionIntegers F} ∧
      IsCompact {a : Af F | ∀ v : Pl F, a v ∈ v.adicCompletionIntegers F} := by
  constructor
  · exact RestrictedProduct.isOpen_forall_mem (fun v => Valued.isOpen_valuationSubring _)
  · have hr := RestrictedProduct.range_structureMap (fun v : Pl F => Fv F v)
      (fun v => (v.adicCompletionIntegers F : Set (Fv F v))) (𝓕 := cofinite)
    haveI : ∀ v : Pl F, CompactSpace (v.adicCompletionIntegers F) := fun v =>
      GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v
    have hc := isCompact_range (RestrictedProduct.isEmbedding_structureMap (R := fun v : Pl F => Fv F v)
      (A := fun v => (v.adicCompletionIntegers F : Set (Fv F v))) (𝓕 := cofinite)).continuous
    rw [hr] at hc
    exact hc

/- English proof (translation)
Take `⟨W', hW'W, hW'o, h0⟩` from `mem_nhds_iff.mp hW`. Use `haveI : Nonempty {n : ℕ // n ≠ 0} := ⟨⟨1, one_ne_zero⟩⟩`. Set `D : {n : ℕ // n ≠ 0} → Set (Af F)` to `fun n => {a | ∀ v : Pl F, Valued.v (a v) ≤ v.intValuation ((n : ℕ) : 𝓞 F)}`. Establish `hDclosed : ∀ n, IsClosed (D n)`. Introduce `n`.

Establish `hset : D n = (fun a => algebraMap F (Af F) (((n : ℕ) : F)⁻¹) * a) ⁻¹' {a : Af F | ∀ v : Pl F, a v ∈ v.adicCompletionIntegers F}`. Use extensionality with `a`. Conclude with `valuation_le_natCast_iff_inv_mul_mem_integers n.2 a`. Rewrite using `[hset]`. Conclude with `isOpen_isCompact_adelic_integers.2.isClosed.preimage (continuous_const.mul continuous_id)`.

Establish `hDsub : ∀ n, D n ⊆ {a : Af F | ∀ v : Pl F, a v ∈ v.adicCompletionIntegers F}` using `fun n a ha v => (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (le_trans (ha v) (IsDedekindDomain.HeightOneSpectrum.intValuation_le_one _ _))`. Establish `hempty : {a : Af F | ∀ v : Pl F, a v ∈ v.adicCompletionIntegers F} ∩ ⋂ n, (D n ∩ W'ᶜ) = ∅`. Use extensionality with `a`. Simplify using `only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_empty_iff_false, iff_false, not_and]`. Introduce `_ hall`.

Distinguish the cases in `ha0 : a = 0`. Conclude with `(hall ⟨1, one_ne_zero⟩).2 (ha0 ▸ h0)`. Choose the witnesses or unpack the hypotheses as in `⟨v, hv⟩ : ∃ v : Pl F, a v ≠ 0 := by`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`.

Conclude with `ha0 (IsDedekindDomain.FiniteAdeleRing.ext F (fun v => by simpa using hcon v))`. Establish `hγ : Valued.v (a v) ≠ 0` using `by simpa using hv`. Take `⟨m, hm0, hm⟩` from `exists_natCast_intValuation_lt v hγ`. Conclude with `absurd ((hall ⟨m, hm0⟩).1 v) (not_le.mpr hm)`. Establish `hdir : Directed (fun x1 x2 : Set (Af F) => x1 ⊇ x2) (fun n => D n ∩ W'ᶜ)`.

Introduce `n m`. Use `⟨⟨n.1 * m.1, Nat.mul_ne_zero n.2 m.2⟩, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `a ⟨ha, hw⟩`. Use `⟨fun v => le_trans (ha v) ?_, hw⟩` and prove the remaining obligations. Use `push_cast`.

Rewrite using `[map_mul]`. Conclude with `mul_le_of_le_one_right' (IsDedekindDomain.HeightOneSpectrum.intValuation_le_one _ _)`. Introduce and unpack `a ⟨ha, hw⟩`. Use `⟨fun v => le_trans (ha v) ?_, hw⟩` and prove the remaining obligations. Use `push_cast`.

Rewrite using `[map_mul]`. Conclude with `mul_le_of_le_one_left' (IsDedekindDomain.HeightOneSpectrum.intValuation_le_one _ _)`. Take `⟨n, hn⟩` from `isOpen_isCompact_adelic_integers.2.elim_directed_family_closed (fun n => D n ∩ W'ᶜ) (fun n => (hDclosed n).inter hW'o.isClosed_compl) hempty hdir`. Use `⟨n.1, n.2, fun a ha => hW'W ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hna`.

Establish `hmem : a ∈ {a : Af F | ∀ v : Pl F, a v ∈ v.adicCompletionIntegers F} ∩ (D n ∩ W'ᶜ)` using `⟨hDsub n ha, ha, hna⟩`. Rewrite `hmem` using `[hn]`. Conclude with `hmem`.
-/
private theorem exists_nat_valuation_le_subset_of_mem_nhds_zero {W : Set (Af F)} (hW : W ∈ 𝓝 (0 : Af F)) :
    ∃ n : ℕ, n ≠ 0 ∧ ∀ a : Af F, (∀ v : Pl F, Valued.v (a v) ≤ v.intValuation (n : 𝓞 F)) → a ∈ W := by
  obtain ⟨W', hW'W, hW'o, h0⟩ := mem_nhds_iff.mp hW
  haveI : Nonempty {n : ℕ // n ≠ 0} := ⟨⟨1, one_ne_zero⟩⟩
  let D : {n : ℕ // n ≠ 0} → Set (Af F) := fun n =>
    {a | ∀ v : Pl F, Valued.v (a v) ≤ v.intValuation ((n : ℕ) : 𝓞 F)}
  have hDclosed : ∀ n, IsClosed (D n) := by
    intro n
    have hset : D n = (fun a => algebraMap F (Af F) (((n : ℕ) : F)⁻¹) * a) ⁻¹'
        {a : Af F | ∀ v : Pl F, a v ∈ v.adicCompletionIntegers F} := by
      ext a
      exact valuation_le_natCast_iff_inv_mul_mem_integers n.2 a
    rw [hset]
    exact isOpen_isCompact_adelic_integers.2.isClosed.preimage (continuous_const.mul continuous_id)
  have hDsub : ∀ n, D n ⊆ {a : Af F | ∀ v : Pl F, a v ∈ v.adicCompletionIntegers F} :=
    fun n a ha v => (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr
      (le_trans (ha v) (IsDedekindDomain.HeightOneSpectrum.intValuation_le_one _ _))
  have hempty : {a : Af F | ∀ v : Pl F, a v ∈ v.adicCompletionIntegers F} ∩ ⋂ n, (D n ∩ W'ᶜ) = ∅ := by
    ext a
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_empty_iff_false, iff_false, not_and]
    intro _ hall
    by_cases ha0 : a = 0
    · exact (hall ⟨1, one_ne_zero⟩).2 (ha0 ▸ h0)
    · obtain ⟨v, hv⟩ : ∃ v : Pl F, a v ≠ 0 := by
        by_contra hcon
        push_neg at hcon
        exact ha0 (IsDedekindDomain.FiniteAdeleRing.ext F (fun v => by simpa using hcon v))
      have hγ : Valued.v (a v) ≠ 0 := by simpa using hv
      obtain ⟨m, hm0, hm⟩ := exists_natCast_intValuation_lt v hγ
      exact absurd ((hall ⟨m, hm0⟩).1 v) (not_le.mpr hm)
  have hdir : Directed (fun x1 x2 : Set (Af F) => x1 ⊇ x2) (fun n => D n ∩ W'ᶜ) := by
    intro n m
    refine ⟨⟨n.1 * m.1, Nat.mul_ne_zero n.2 m.2⟩, ?_, ?_⟩
    · rintro a ⟨ha, hw⟩
      refine ⟨fun v => le_trans (ha v) ?_, hw⟩
      push_cast
      rw [map_mul]
      exact mul_le_of_le_one_right' (IsDedekindDomain.HeightOneSpectrum.intValuation_le_one _ _)
    · rintro a ⟨ha, hw⟩
      refine ⟨fun v => le_trans (ha v) ?_, hw⟩
      push_cast
      rw [map_mul]
      exact mul_le_of_le_one_left' (IsDedekindDomain.HeightOneSpectrum.intValuation_le_one _ _)
  obtain ⟨n, hn⟩ := isOpen_isCompact_adelic_integers.2.elim_directed_family_closed (fun n => D n ∩ W'ᶜ)
    (fun n => (hDclosed n).inter hW'o.isClosed_compl) hempty hdir
  refine ⟨n.1, n.2, fun a ha => hW'W ?_⟩
  by_contra hna
  have hmem : a ∈ {a : Af F | ∀ v : Pl F, a v ∈ v.adicCompletionIntegers F} ∩ (D n ∩ W'ᶜ) :=
    ⟨hDsub n ha, ha, hna⟩
  rw [hn] at hmem
  exact hmem

/- English proof (translation)
Establish `hset : {y | Near M c y} = ⋂ i, (fun y : κ → Af F => algebraMap F (Af F) ((M : F)⁻¹) * (y i - c i)) ⁻¹' {a : Af F | ∀ v : Pl F, a v ∈ v.adicCompletionIntegers F}`. Use extensionality with `y`. Simplify using `only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, Near]`. Rewrite using `[forall_comm]`. Use `forall_congr' (fun i => ?_)` and prove the remaining obligations.

Rewrite using `[← valuation_le_natCast_iff_inv_mul_mem_integers hM]`. Use `forall_congr' (fun v => ?_)` and prove the remaining obligations. Rewrite using `[← map_sub]`. Both sides reduce to the same expression. Rewrite using `[hset]`.

Conclude with `isOpen_iInter_of_finite (fun i => isOpen_isCompact_adelic_integers.1.preimage (continuous_const.mul ((continuous_apply i).sub continuous_const)))`.
-/
private theorem isOpen_setOf_near {M : ℕ} (hM : M ≠ 0) (c : κ → Af F) : IsOpen {y | Near M c y} := by
  have hset : {y | Near M c y} = ⋂ i, (fun y : κ → Af F => algebraMap F (Af F) ((M : F)⁻¹) * (y i - c i)) ⁻¹'
      {a : Af F | ∀ v : Pl F, a v ∈ v.adicCompletionIntegers F} := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, Near]
    rw [forall_comm]
    refine forall_congr' (fun i => ?_)
    rw [← valuation_le_natCast_iff_inv_mul_mem_integers hM]
    refine forall_congr' (fun v => ?_)
    rw [← map_sub]
    rfl
  rw [hset]
  exact isOpen_iInter_of_finite (fun i => isOpen_isCompact_adelic_integers.1.preimage
    (continuous_const.mul ((continuous_apply i).sub continuous_const)))

/- English proof (translation)
Establish `hV : (fun d => y + d) ⁻¹' U ∈ 𝓝 (0 : κ → Af F)`. Apply `(continuous_const.add continuous_id).continuousAt.preimage_mem_nhds` to reduce the goal to its premises. Simplify using `using hU`. Rewrite `hV` using `[nhds_pi, Filter.mem_pi]`. Take `⟨I, _, t, ht, hsub⟩` from `hV`.

Use `choose n hn0 hn using fun i => exists_nat_valuation_le_subset_of_mem_nhds_zero (ht i)`. Use `⟨∏ i, n i, Finset.prod_ne_zero_iff.mpr (fun i _ => hn0 i), ?_⟩` and prove the remaining obligations. Introduce `z hz`. Establish `hz' : z = y + (z - y)` using `by abel`. Rewrite using `[hz']`.

Apply `hsub` to reduce the goal to its premises. Introduce `i _`. Apply `hn i` to reduce the goal to its premises. Introduce `v`. Establish `h1` using `hz v i`.

Establish `h2 : v.intValuation (((∏ j, n j : ℕ)) : 𝓞 F) ≤ v.intValuation ((n i : ℕ) : 𝓞 F)`. Rewrite using `[Nat.cast_prod, map_prod, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]`. Conclude with `mul_le_of_le_one_right' (Finset.prod_le_one' (fun j _ => IsDedekindDomain.HeightOneSpectrum.intValuation_le_one _ _))`. Establish `e : (z - y) i v = evalV F v (z i) - evalV F v (y i)`. Rewrite using `[Pi.sub_apply, ← map_sub]`.

Both sides reduce to the same expression. Rewrite using `[e]`. Conclude with `le_trans h1 h2`.
-/
private theorem exists_near_subset_of_mem_nhds (y : κ → Af F) {U : Set (κ → Af F)} (hU : U ∈ 𝓝 y) :
    ∃ n : ℕ, n ≠ 0 ∧ {z | Near n y z} ⊆ U := by
  classical
  have hV : (fun d => y + d) ⁻¹' U ∈ 𝓝 (0 : κ → Af F) := by
    apply (continuous_const.add continuous_id).continuousAt.preimage_mem_nhds
    simpa using hU
  rw [nhds_pi, Filter.mem_pi] at hV
  obtain ⟨I, _, t, ht, hsub⟩ := hV
  choose n hn0 hn using fun i => exists_nat_valuation_le_subset_of_mem_nhds_zero (ht i)
  refine ⟨∏ i, n i, Finset.prod_ne_zero_iff.mpr (fun i _ => hn0 i), ?_⟩
  intro z hz
  have hz' : z = y + (z - y) := by abel
  rw [hz']
  apply hsub
  intro i _
  apply hn i
  intro v
  have h1 := hz v i
  have h2 : v.intValuation (((∏ j, n j : ℕ)) : 𝓞 F) ≤ v.intValuation ((n i : ℕ) : 𝓞 F) := by
    rw [Nat.cast_prod, map_prod, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    exact mul_le_of_le_one_right' (Finset.prod_le_one' (fun j _ =>
      IsDedekindDomain.HeightOneSpectrum.intValuation_le_one _ _))
  have e : (z - y) i v = evalV F v (z i) - evalV F v (y i) := by
    rw [Pi.sub_apply, ← map_sub]
    rfl
  rw [e]
  exact le_trans h1 h2

/- English proof (translation)
Introduce `v i`. Use `le_trans (hab v i) ?_` and prove the remaining obligations. Take `⟨k, rfl⟩` from `h`. Use `push_cast`. Rewrite using `[map_mul]`.

Conclude with `mul_le_of_le_one_right' (IsDedekindDomain.HeightOneSpectrum.intValuation_le_one _ _)`.
-/
private theorem near_of_dvd {n M : ℕ} (h : n ∣ M) {a b : κ → Af F} (hab : Near M a b) : Near n a b := by
  intro v i
  refine le_trans (hab v i) ?_
  obtain ⟨k, rfl⟩ := h
  push_cast
  rw [map_mul]
  exact mul_le_of_le_one_right' (IsDedekindDomain.HeightOneSpectrum.intValuation_le_one _ _)

/- English proof (translation)
Establish `hbox : ∀ (f : SInf F κ) {M : ℕ}, M ≠ 0 → ∀ c : κ → Af F, pureA F (⇑f) (fun y => box M c y) ∈ L`. Introduce `f M hM c`. Establish `h` using `hL f (fun v => (ballAt M c v).indicator (1 : (κ → Fv F v) → ℂ)) (fun v => ball_mem hM c v) (ball_cof hM c)`. Use `h using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `x`.

Both sides reduce to the same expression. Establish `hrefl : ∀ (M : ℕ) (y : κ → Af F), Near M y y`. Introduce `M y v i`. Simplify using the standard rewrite rules. Unfold `schA`.

Rewrite using `[Submodule.span_le]`. Introduce and unpack `Φ ⟨f, g, hg, rfl⟩`. Choose the witnesses or unpack the hypotheses as in `⟨M, hM0, hinv, t, hcov⟩ : ∃ M : ℕ, M ≠ 0 ∧ (∀ a b, Near M a b → g a = g b) ∧ ∃ t : Finset (κ → Af F), Function.support g ⊆ ⋃ c ∈ t, {z | Near M c z} := by`. Establish `hK : IsCompact (Function.support g)` using `hg.2.isCompact.of_isClosed_subset (hg.1.isClopen_fiber 0).isOpen.isClosed_compl (subset_tsupport g)`. Establish `hloc : ∀ y, ∃ n : ℕ, n ≠ 0 ∧ {z | Near n y z} ⊆ {z | g z = g y}` using `fun y => exists_near_subset_of_mem_nhds y (hg.1.eventually_eq y)`.

Use `choose n hn0 hn using hloc`. Take `⟨t₁, -, hcov₁⟩` from `hK.elim_nhds_subcover (fun y => {z | Near (n y) y z}) (fun y _ => (isOpen_setOf_near (hn0 y) y).mem_nhds (hrefl _ y))`. Establish `hM0 : (∏ y ∈ t₁, n y) ≠ 0` using `Finset.prod_ne_zero_iff.mpr (fun y _ => hn0 y)`. Establish `hinv1 : ∀ a b, a ∈ Function.support g → Near (∏ y ∈ t₁, n y) a b → g a = g b`. Introduce `a b ha hab`.

Establish `hmem` using `hcov₁ ha`. Simplify using `only [Set.mem_iUnion, exists_prop, Set.mem_setOf_eq] at hmem`. Take `⟨y, hy, hya⟩` from `hmem`. Establish `hab'` using `near_of_dvd (Finset.dvd_prod_of_mem n hy) hab`. Establish `e1 : g a = g y` using `hn y hya`.

Establish `e2 : g b = g y` using `hn y (hya.trans hab')`. Rewrite using `[e1, e2]`. Establish `hinv : ∀ a b, Near (∏ y ∈ t₁, n y) a b → g a = g b`. Introduce `a b hab`. Distinguish the cases in `ha : a ∈ Function.support g`.

Conclude with `hinv1 a b ha hab`. Distinguish the cases in `hb : b ∈ Function.support g`. Conclude with `(hinv1 b a hb hab.symm).symm`. Rewrite using `[Function.notMem_support.mp ha, Function.notMem_support.mp hb]`. Take `⟨t, -, hcov⟩` from `hK.elim_nhds_subcover (fun y => {z | Near (∏ y ∈ t₁, n y) y z}) (fun y _ => (isOpen_setOf_near hM0 y).mem_nhds (hrefl _ y))`.

Conclude with `⟨_, hM0, hinv, t, hcov⟩`. Establish `key : ∀ (s : Finset (κ → Af F)) (h : (κ → Af F) → ℂ), (∀ a b, Near M a b → h a = h b) → Function.support h ⊆ ⋃ c ∈ s, {z | Near M c z} → pureA F (⇑f) h ∈ L`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`.

Introduce `h _ hs`. Establish `h0 : h = 0`. Use function extensionality and compare the values at `x`. Assume the negation of the conclusion as `hx`. Establish `hx'` using `hs hx`.

Simplify using `at hx'`. Rewrite using `[h0]`. Use `L.zero_mem using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `x`. Simplify using `[pureA]`.

Consider the case `insert c s hcs ih`. Introduce `h hh hs`. Establish `hsplit : pureA F (⇑f) h = h c • pureA F (⇑f) (fun y => box M c y) + pureA F (⇑f) (fun y => h y - h c * box M c y)`. Use function extensionality and compare the values at `x`. Simplify using `only [pureA, Pi.add_apply, Pi.smul_apply, smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hsplit]`. Use `L.add_mem (L.smul_mem _ (hbox f hM0 c)) (ih _ ?_ ?_)` and prove the remaining obligations. Introduce `a b hab`. Distinguish the cases in `hca : Near M c a`.

Establish `hcb : Near M c b` using `hca.trans hab`. Rewrite using `[box_of_near hca, box_of_near hcb, hh a b hab]`. Establish `hcb : ¬ Near M c b` using `fun hcb => hca (hcb.trans hab.symm)`. Rewrite using `[box_of_not hM0 hca, box_of_not hM0 hcb, hh a b hab]`. Introduce `z hz`.

Establish `hcz : ¬ Near M c z`. Introduce `hcz`. Apply `hz` to reduce the goal to its premises. Use `show h z - h c * box M c z = 0`. Rewrite using `[box_of_near hcz, hh c z hcz]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hz' : h z ≠ 0`. Introduce `h0`. Apply `hz` to reduce the goal to its premises. Use `show h z - h c * box M c z = 0`.

Rewrite using `[box_of_not hM0 hcz, h0]`. Expand and normalize the polynomial expressions, which then agree. Establish `hmem` using `hs hz'`. Simplify using `only [Set.mem_iUnion, Finset.mem_insert, exists_prop, Set.mem_setOf_eq] at hmem ⊢`. Take `⟨d, hd, hdz⟩` from `hmem`.

Break down `hd with rfl | hd` into its components or cases. Conclude with `absurd hdz hcz`. Conclude with `⟨d, hd, hdz⟩`. Conclude with `key t g hinv hcov`.
-/
theorem schA_le (L : Submodule ℂ ((κ → AF F) → ℂ))
    (hL : ∀ (f : SInf F κ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ), (∀ v, φ v ∈ SB _) →
      (∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ ∈ L) :
    schA F κ ≤ L := by
  classical
  have hbox : ∀ (f : SInf F κ) {M : ℕ}, M ≠ 0 → ∀ c : κ → Af F,
      pureA F (⇑f) (fun y => box M c y) ∈ L := by
    intro f M hM c
    have h := hL f (fun v => (ballAt M c v).indicator (1 : (κ → Fv F v) → ℂ))
      (fun v => ball_mem hM c v) (ball_cof hM c)
    convert h using 1
    funext x
    rfl
  have hrefl : ∀ (M : ℕ) (y : κ → Af F), Near M y y := by
    intro M y v i
    simp
  unfold schA
  rw [Submodule.span_le]
  rintro Φ ⟨f, g, hg, rfl⟩
  obtain ⟨M, hM0, hinv, t, hcov⟩ : ∃ M : ℕ, M ≠ 0 ∧ (∀ a b, Near M a b → g a = g b) ∧
      ∃ t : Finset (κ → Af F), Function.support g ⊆ ⋃ c ∈ t, {z | Near M c z} := by
    have hK : IsCompact (Function.support g) :=
      hg.2.isCompact.of_isClosed_subset (hg.1.isClopen_fiber 0).isOpen.isClosed_compl (subset_tsupport g)
    have hloc : ∀ y, ∃ n : ℕ, n ≠ 0 ∧ {z | Near n y z} ⊆ {z | g z = g y} :=
      fun y => exists_near_subset_of_mem_nhds y (hg.1.eventually_eq y)
    choose n hn0 hn using hloc
    obtain ⟨t₁, -, hcov₁⟩ := hK.elim_nhds_subcover (fun y => {z | Near (n y) y z})
      (fun y _ => (isOpen_setOf_near (hn0 y) y).mem_nhds (hrefl _ y))
    have hM0 : (∏ y ∈ t₁, n y) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun y _ => hn0 y)
    have hinv1 : ∀ a b, a ∈ Function.support g → Near (∏ y ∈ t₁, n y) a b → g a = g b := by
      intro a b ha hab
      have hmem := hcov₁ ha
      simp only [Set.mem_iUnion, exists_prop, Set.mem_setOf_eq] at hmem
      obtain ⟨y, hy, hya⟩ := hmem
      have hab' := near_of_dvd (Finset.dvd_prod_of_mem n hy) hab
      have e1 : g a = g y := hn y hya
      have e2 : g b = g y := hn y (hya.trans hab')
      rw [e1, e2]
    have hinv : ∀ a b, Near (∏ y ∈ t₁, n y) a b → g a = g b := by
      intro a b hab
      by_cases ha : a ∈ Function.support g
      · exact hinv1 a b ha hab
      · by_cases hb : b ∈ Function.support g
        · exact (hinv1 b a hb hab.symm).symm
        · rw [Function.notMem_support.mp ha, Function.notMem_support.mp hb]
    obtain ⟨t, -, hcov⟩ := hK.elim_nhds_subcover (fun y => {z | Near (∏ y ∈ t₁, n y) y z})
      (fun y _ => (isOpen_setOf_near hM0 y).mem_nhds (hrefl _ y))
    exact ⟨_, hM0, hinv, t, hcov⟩
  have key : ∀ (s : Finset (κ → Af F)) (h : (κ → Af F) → ℂ), (∀ a b, Near M a b → h a = h b) →
      Function.support h ⊆ ⋃ c ∈ s, {z | Near M c z} → pureA F (⇑f) h ∈ L := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro h _ hs
      have h0 : h = 0 := by
        funext x
        by_contra hx
        have hx' := hs hx
        simp at hx'
      rw [h0]
      convert L.zero_mem using 1
      funext x
      simp [pureA]
    | insert c s hcs ih =>
      intro h hh hs
      have hsplit : pureA F (⇑f) h = h c • pureA F (⇑f) (fun y => box M c y) +
          pureA F (⇑f) (fun y => h y - h c * box M c y) := by
        funext x
        simp only [pureA, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring
      rw [hsplit]
      refine L.add_mem (L.smul_mem _ (hbox f hM0 c)) (ih _ ?_ ?_)
      · intro a b hab
        by_cases hca : Near M c a
        · have hcb : Near M c b := hca.trans hab
          rw [box_of_near hca, box_of_near hcb, hh a b hab]
        · have hcb : ¬ Near M c b := fun hcb => hca (hcb.trans hab.symm)
          rw [box_of_not hM0 hca, box_of_not hM0 hcb, hh a b hab]
      · intro z hz
        have hcz : ¬ Near M c z := by
          intro hcz
          apply hz
          show h z - h c * box M c z = 0
          rw [box_of_near hcz, hh c z hcz]
          ring
        have hz' : h z ≠ 0 := by
          intro h0
          apply hz
          show h z - h c * box M c z = 0
          rw [box_of_not hM0 hcz, h0]
          ring
        have hmem := hs hz'
        simp only [Set.mem_iUnion, Finset.mem_insert, exists_prop, Set.mem_setOf_eq] at hmem ⊢
        obtain ⟨d, hd, hdz⟩ := hmem
        rcases hd with rfl | hd
        · exact absurd hdz hcz
        · exact ⟨d, hd, hdz⟩
  exact key t g hinv hcov

end PositivityTheory.KCo
