import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.LiftFactorization
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.QuotFubiniHolds

open MeasureTheory PositivityTheory.Rg.Tf.Loc UpperTheory.V.Z.Tf.Orb
open scoped ENNReal

/- English proof (translation)
Introduce `G _ _ _ _ _ _ _ _ μ hμ K hKo hKc hK1 T hTc hTcomm ν hν F hF hFT q`. Use `haveI := hμ`. Use `haveI := hν`. Take `⟨hsf, hinv, hright⟩` from `haarComm_holds G T hTc hTcomm ν hν`. Use `haveI := hsf`.

Use `haveI := hinv`. Use `haveI := hright`. Take `⟨ρ, hρ, -⟩` from `normEx_holds G ⟨K, hKo, hKc⟩ T hTc ν hν hright`. Use `set D : Set G := {g | ∃ t ∈ T, ∃ y ∈ K, g = t * q * y} with hD`. Use `set Hs : Set T := {t : T | q⁻¹ * (t : G) * q ∈ K} with hHs`.

Use `set qK : Set G := {g | q⁻¹ * g ∈ K} with hqK`. Establish `hqKo : IsOpen qK` using `hKo.preimage (continuous_const.mul continuous_id)`. Establish `hDo : IsOpen D`. Establish `: D = ⋃ t : T, (fun g : G => ((t : G) * q)⁻¹ * g) ⁻¹' (K : Set G)`. Use extensionality with `g`.

Simplify using `only [hD, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨t, ht, y, hy, rfl⟩`. Use `⟨⟨t, ht⟩, ?_⟩` and prove the remaining obligations. Simplify `hy` using `[mul_assoc]`.

Introduce and unpack `⟨t, ht⟩`. Conclude with `⟨t, t.2, _, ht, by group⟩`. Rewrite using `[this]`. Conclude with `isOpen_iUnion fun t => hKo.preimage (continuous_const.mul continuous_id)`. Establish `hHo : IsOpen Hs` using `hKo.preimage (((continuous_const.mul continuous_subtype_val).mul continuous_const))`.

Establish `hHc : IsCompact Hs`. Establish `hS : IsCompact ((fun x : G => q * x * q⁻¹) '' (K : Set G))` using `hKc.image (by fun_prop)`. Establish `hpc` using `hTc.isClosedEmbedding_subtypeVal.isCompact_preimage hS`. Establish `e : Hs = Subtype.val ⁻¹' ((fun x : G => q * x * q⁻¹) '' (K : Set G))`. Use extensionality with `t`.

Simplify using `only [hHs, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_image, SetLike.mem_coe]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `⟨_, h, by group⟩`. Introduce and unpack `⟨x, hx, hxt⟩`.

Establish `: q⁻¹ * (t : G) * q = x` using `by rw [← hxt]; group`. Rewrite using `[this]` and apply the resulting hypothesis. Rewrite using `[e]`. Conclude with `hpc`. Establish `h1H : (1 : T) ∈ Hs`.

Simplify `K.one_mem` using `[hHs]`. Use `set v : ℝ≥0∞ := ν Hs with hv`. Establish `hv0 : v ≠ 0` using `hHo.measure_ne_zero ν ⟨1, h1H⟩`. Establish `hvt : v ≠ ∞` using `hHc.measure_lt_top.ne`. Establish `hqKD : qK ⊆ D` using `fun g hg => ⟨1, T.one_mem, q⁻¹ * g, hg, by group⟩`.

Establish `hDT : ∀ h ∈ T, ∀ g, h * g ∈ D ↔ g ∈ D`. Introduce `h hh g`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨t, ht, y, hy, e⟩`. Use `⟨h⁻¹ * t, T.mul_mem (T.inv_mem hh) ht, y, hy, ?_⟩` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation. Introduce and unpack `⟨t, ht, y, hy, rfl⟩`. Conclude with `⟨h * t, T.mul_mem hh ht, y, hy, by group⟩`. Use `set ρ' : G → ℝ≥0∞ := D.piecewise (qK.indicator fun _ => v⁻¹) ρ with hρ'def`. Establish `hρ' : IsQuotNormaliser T ν ρ'`.

Use `⟨Measurable.piecewise hDo.measurableSet (measurable_const.indicator hqKo.measurableSet) hρ.1, fun g => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hg : g ∈ D`. Take `⟨t₀, ht₀, y, hy, rfl⟩` from `hg set A : Set T := (fun h : T => h * (⟨t₀, ht₀⟩ : T)) ⁻¹' Hs with hA`. Establish `hAm : MeasurableSet A` using `(hHo.preimage (continuous_mul_right _)).measurableSet`. Establish `hpt : ∀ h : T, ρ' ((h : G) * (t₀ * q * y)) = A.indicator (fun _ => v⁻¹) h`.

Introduce `h`. Establish `hmem : (h : G) * (t₀ * q * y) ∈ D` using `(hDT _ h.2 _).2 ⟨t₀, ht₀, y, hy, rfl⟩`. Rewrite using `[hρ'def, Set.piecewise_eq_of_mem _ _ _ hmem]`. Establish `hiff : (h : G) * (t₀ * q * y) ∈ qK ↔ h ∈ A`. Establish `e : q⁻¹ * ((h : G) * (t₀ * q * y)) = (q⁻¹ * ((h : G) * t₀) * q) * y` using `by group`.

Simplify using `only [hqK, hA, hHs, Set.mem_setOf_eq, Set.mem_preimage, e, Subgroup.coe_mul]`. Conclude with `Subgroup.mul_mem_cancel_right K hy`. Distinguish the cases in `hh : h ∈ A`. Rewrite using `[Set.indicator_of_mem (hiff.2 hh), Set.indicator_of_mem hh]`. Rewrite using `[Set.indicator_of_notMem (fun c => hh (hiff.1 c)), Set.indicator_of_notMem hh]`.

Repeatedly rewrite using `[hpt]`. Rewrite using `[lintegral_indicator_const hAm, hA, measure_preimage_mul_right, ← hv]`. Conclude with `ENNReal.inv_mul_cancel hv0 hvt`. Establish `hpt : ∀ h : T, ρ' ((h : G) * g) = ρ ((h : G) * g)`. Introduce `h`.

Rewrite using `[hρ'def, Set.piecewise_eq_of_notMem _ _ _ (fun c => hg ((hDT _ h.2 _).1 c))]`. Repeatedly rewrite using `[hpt]`. Conclude with `hρ.2 g`. Establish `hFm : Measurable (D.indicator F)` using `hF.measurable.indicator hDo.measurableSet`. Establish `hFinv : ∀ h ∈ T, ∀ g, D.indicator F (h * g) = D.indicator F g`.

Introduce `h hh g`. Distinguish the cases in `hg : g ∈ D`. Rewrite using `[Set.indicator_of_mem hg, Set.indicator_of_mem ((hDT h hh g).2 hg), hFT h hh]`. Rewrite using `[Set.indicator_of_notMem hg, Set.indicator_of_notMem (fun c => hg ((hDT h hh g).1 c))]`. Rewrite using `[quotIndep_holds G μ hμ T ν hsf hinv _ hFm hFinv ρ' hρ']`.

Establish `hpt : ∀ g, D.indicator F g * ((ρ' g).toReal : ℂ) = qK.indicator (fun g => ((v.toReal : ℝ) : ℂ)⁻¹ * F g) g`. Introduce `g`. Distinguish the cases in `hg : g ∈ D`. Rewrite using `[Set.indicator_of_mem hg, hρ'def, Set.piecewise_eq_of_mem _ _ _ hg]`. Distinguish the cases in `hq : g ∈ qK`.

Rewrite using `[Set.indicator_of_mem hq, Set.indicator_of_mem hq, ENNReal.toReal_inv]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Set.indicator_of_notMem hq, Set.indicator_of_notMem hq]`. Simplify using the standard rewrite rules.

Rewrite using `[Set.indicator_of_notMem hg, Set.indicator_of_notMem (fun c => hg (hqKD c)), zero_mul]`. Repeatedly rewrite using `[hpt]`. Rewrite using `[integral_indicator hqKo.measurableSet, integral_const_mul]`. Establish `hpre : (fun y : G => q * y) ⁻¹' qK = (K : Set G)`. Use extensionality with `y`.

Simplify using `[hqK]`. Use `(measurePreserving_mul_left μ q).setIntegral_preimage_emb (measurableEmbedding_mulLeft q) F qK` as an intermediate fact. Rewrite `this` using `[hpre]`. Rewrite using `[this]`. Both sides reduce to the same expression.
-/
theorem UpperTheory.Gal.InertialTypesAlt.L.oneCoset :
    UpperTheory.Gal.InertialTypesAlt.L.OneCoset := by
  classical
  intro G _ _ _ _ _ _ _ _ μ hμ K hKo hKc hK1 T hTc hTcomm ν hν F hF hFT q
  haveI := hμ
  haveI := hν
  obtain ⟨hsf, hinv, hright⟩ := haarComm_holds G T hTc hTcomm ν hν
  haveI := hsf
  haveI := hinv
  haveI := hright
  obtain ⟨ρ, hρ, -⟩ := normEx_holds G ⟨K, hKo, hKc⟩ T hTc ν hν hright
  set D : Set G := {g | ∃ t ∈ T, ∃ y ∈ K, g = t * q * y} with hD
  set Hs : Set T := {t : T | q⁻¹ * (t : G) * q ∈ K} with hHs
  set qK : Set G := {g | q⁻¹ * g ∈ K} with hqK

  have hqKo : IsOpen qK := hKo.preimage (continuous_const.mul continuous_id)
  have hDo : IsOpen D := by
    have : D = ⋃ t : T, (fun g : G => ((t : G) * q)⁻¹ * g) ⁻¹' (K : Set G) := by
      ext g
      simp only [hD, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe]
      constructor
      · rintro ⟨t, ht, y, hy, rfl⟩
        refine ⟨⟨t, ht⟩, ?_⟩
        simpa [mul_assoc] using hy
      · rintro ⟨t, ht⟩
        exact ⟨t, t.2, _, ht, by group⟩
    rw [this]
    exact isOpen_iUnion fun t => hKo.preimage (continuous_const.mul continuous_id)
  have hHo : IsOpen Hs :=
    hKo.preimage (((continuous_const.mul continuous_subtype_val).mul continuous_const))
  have hHc : IsCompact Hs := by
    have hS : IsCompact ((fun x : G => q * x * q⁻¹) '' (K : Set G)) :=
      hKc.image (by fun_prop)
    have hpc := hTc.isClosedEmbedding_subtypeVal.isCompact_preimage hS
    have e : Hs = Subtype.val ⁻¹' ((fun x : G => q * x * q⁻¹) '' (K : Set G)) := by
      ext t
      simp only [hHs, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_image, SetLike.mem_coe]
      constructor
      · intro h
        exact ⟨_, h, by group⟩
      · rintro ⟨x, hx, hxt⟩
        have : q⁻¹ * (t : G) * q = x := by rw [← hxt]; group
        rwa [this]
    rw [e]
    exact hpc
  have h1H : (1 : T) ∈ Hs := by
    simpa [hHs] using K.one_mem
  set v : ℝ≥0∞ := ν Hs with hv
  have hv0 : v ≠ 0 := hHo.measure_ne_zero ν ⟨1, h1H⟩
  have hvt : v ≠ ∞ := hHc.measure_lt_top.ne
  have hqKD : qK ⊆ D := fun g hg => ⟨1, T.one_mem, q⁻¹ * g, hg, by group⟩
  have hDT : ∀ h ∈ T, ∀ g, h * g ∈ D ↔ g ∈ D := by
    intro h hh g
    constructor
    · rintro ⟨t, ht, y, hy, e⟩
      refine ⟨h⁻¹ * t, T.mul_mem (T.inv_mem hh) ht, y, hy, ?_⟩
      calc g = h⁻¹ * (h * g) := by group
        _ = _ := by rw [e]; group
    · rintro ⟨t, ht, y, hy, rfl⟩
      exact ⟨h * t, T.mul_mem hh ht, y, hy, by group⟩
  set ρ' : G → ℝ≥0∞ := D.piecewise (qK.indicator fun _ => v⁻¹) ρ with hρ'def
  have hρ' : IsQuotNormaliser T ν ρ' := by
    refine ⟨Measurable.piecewise hDo.measurableSet
      (measurable_const.indicator hqKo.measurableSet) hρ.1, fun g => ?_⟩
    by_cases hg : g ∈ D
    · obtain ⟨t₀, ht₀, y, hy, rfl⟩ := hg
      set A : Set T := (fun h : T => h * (⟨t₀, ht₀⟩ : T)) ⁻¹' Hs with hA
      have hAm : MeasurableSet A := (hHo.preimage (continuous_mul_right _)).measurableSet
      have hpt : ∀ h : T, ρ' ((h : G) * (t₀ * q * y)) = A.indicator (fun _ => v⁻¹) h := by
        intro h
        have hmem : (h : G) * (t₀ * q * y) ∈ D :=
          (hDT _ h.2 _).2 ⟨t₀, ht₀, y, hy, rfl⟩
        rw [hρ'def, Set.piecewise_eq_of_mem _ _ _ hmem]
        have hiff : (h : G) * (t₀ * q * y) ∈ qK ↔ h ∈ A := by
          have e : q⁻¹ * ((h : G) * (t₀ * q * y)) = (q⁻¹ * ((h : G) * t₀) * q) * y := by group
          simp only [hqK, hA, hHs, Set.mem_setOf_eq, Set.mem_preimage, e, Subgroup.coe_mul]
          exact Subgroup.mul_mem_cancel_right K hy
        by_cases hh : h ∈ A
        · rw [Set.indicator_of_mem (hiff.2 hh), Set.indicator_of_mem hh]
        · rw [Set.indicator_of_notMem (fun c => hh (hiff.1 c)), Set.indicator_of_notMem hh]
      simp_rw [hpt]
      rw [lintegral_indicator_const hAm, hA, measure_preimage_mul_right, ← hv]
      exact ENNReal.inv_mul_cancel hv0 hvt
    · have hpt : ∀ h : T, ρ' ((h : G) * g) = ρ ((h : G) * g) := by
        intro h
        rw [hρ'def, Set.piecewise_eq_of_notMem _ _ _ (fun c => hg ((hDT _ h.2 _).1 c))]
      simp_rw [hpt]
      exact hρ.2 g
  have hFm : Measurable (D.indicator F) := hF.measurable.indicator hDo.measurableSet
  have hFinv : ∀ h ∈ T, ∀ g, D.indicator F (h * g) = D.indicator F g := by
    intro h hh g
    by_cases hg : g ∈ D
    · rw [Set.indicator_of_mem hg, Set.indicator_of_mem ((hDT h hh g).2 hg), hFT h hh]
    · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (fun c => hg ((hDT h hh g).1 c))]
  rw [quotIndep_holds G μ hμ T ν hsf hinv _ hFm hFinv ρ' hρ']
  have hpt : ∀ g, D.indicator F g * ((ρ' g).toReal : ℂ) =
      qK.indicator (fun g => ((v.toReal : ℝ) : ℂ)⁻¹ * F g) g := by
    intro g
    by_cases hg : g ∈ D
    · rw [Set.indicator_of_mem hg, hρ'def, Set.piecewise_eq_of_mem _ _ _ hg]
      by_cases hq : g ∈ qK
      · rw [Set.indicator_of_mem hq, Set.indicator_of_mem hq, ENNReal.toReal_inv]
        push_cast
        ring
      · rw [Set.indicator_of_notMem hq, Set.indicator_of_notMem hq]
        simp
    · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (fun c => hg (hqKD c)), zero_mul]
  simp_rw [hpt]
  rw [integral_indicator hqKo.measurableSet, integral_const_mul]
  have hpre : (fun y : G => q * y) ⁻¹' qK = (K : Set G) := by
    ext y
    simp [hqK]
  have := (measurePreserving_mul_left μ q).setIntegral_preimage_emb
    (measurableEmbedding_mulLeft q) F qK
  rw [hpre] at this
  rw [this]
  rfl
