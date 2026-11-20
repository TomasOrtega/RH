import Development.AbelianVarietyTheory.Definitions.Divisors.IsLv
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

open scoped Pointwise

namespace GlobalTheory.Packing

/- English proof (translation)
Rewrite using `[Set.mem_smul_set_iff_inv_smul_mem, Set.mem_smul_set_iff_inv_smul_mem]`. Simplify using `[Subgroup.smul_def, smul_eq_mul]`.
-/
theorem mem_smul_smul_iff {G : Type} [Group G] (Λ : Subgroup G) (γ : Λ) (t x : G) (U : Set G) :
    x ∈ γ • (t • U) ↔ t⁻¹ * ((γ : G)⁻¹ * x) ∈ U := by
  rw [Set.mem_smul_set_iff_inv_smul_mem, Set.mem_smul_set_iff_inv_smul_mem]
  simp [Subgroup.smul_def, smul_eq_mul]

/- English proof (translation)
Introduce `G _ _ _ _ _ _ _ _ Γ Λ _ μ D U hΛΓ hdisc hHaar hD hU`. Establish `hUc : IsCompact (U * U⁻¹)` using `hU.mul hU.inv`. Establish `hfin : (U * U⁻¹ ∩ (Γ : Set G)).Finite` using `hdisc _ hUc`. Use `⟨hfin.toFinset.card, ?_⟩` and prove the remaining obligations. Introduce `T S hTΓ hTdist hS hSinv hTS`.

Establish `hUm : MeasurableSet U` using `hU.isClosed.measurableSet`. Establish `hmeasA : ∀ (γ : Λ) (t : G), MeasurableSet (γ • (t • U))`. Introduce `γ t`. Establish `: γ • (t • U) = (fun y => t⁻¹ * ((γ : G)⁻¹ * y)) ⁻¹' U`. Use extensionality with `y`.

Rewrite using `[mem_smul_smul_iff]`. Both sides reduce to the same expression. Rewrite using `[this]`. Conclude with `hUm.preimage (continuous_const.mul (continuous_const.mul continuous_id)).measurable`. Establish `hsubS : ∀ (γ : Λ), ∀ t ∈ T, γ • (t • U) ⊆ S`.

Introduce `γ t ht y hy`. Rewrite `hy` using `[mem_smul_smul_iff]`. Establish `h1` using `hSinv (γ : G) γ.2 _ (hTS t ht _ hy)`. Simplify `h1` using `[mul_assoc]`. Use `set ν := μ.restrict (S ∩ D) with hν`.

Establish `key : ∀ t ∈ T, μ U = ∑' γ : Λ, ∫⁻ x, (γ • (t • U)).indicator 1 x ∂ν`. Introduce `t ht`. Rewrite using `[← measure_smul μ t U, hD.measure_eq_tsum (t • U)]`. Use `tsum_congr fun γ => ?_` and prove the remaining obligations. Rewrite using `[lintegral_indicator_one (hmeasA γ t), hν, Measure.restrict_apply (hmeasA γ t)]`.

Use `congr 1`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Conclude with `⟨h1, hsubS γ t ht h1, h2⟩`.

Introduce and unpack `⟨h1, _, h2⟩`. Conclude with `⟨h1, h2⟩`. Establish `hpt : ∀ x : G, ∑ t ∈ T, ∑' γ : Λ, (γ • (t • U)).indicator (1 : G → ℝ≥0∞) x ≤ (hfin.toFinset.card : ℝ≥0∞)`. Introduce `x`. Establish `hswap : ∑ t ∈ T, ∑' γ : Λ, (γ • (t • U)).indicator (1 : G → ℝ≥0∞) x = ∑' γ : Λ, ∑ t ∈ T, (γ • (t • U)).indicator (1 : G → ℝ≥0∞) x` using `by first`.

Consider the case `exact (Summable.tsum_finsetSum fun _ _ => ENNReal.summable).symm`. Consider the case `exact (tsum_sum fun _ _ => ENNReal.summable).symm`. Consider the case `exact (ENNReal.tsum_finsetSum _ _).symm`. Rewrite using `[hswap, ENNReal.tsum_eq_iSup_sum]`. Use `iSup_le fun s => ?_` and prove the remaining obligations.

Establish `hbool : ∑ γ ∈ s, ∑ t ∈ T, (γ • (t • U)).indicator (1 : G → ℝ≥0∞) x = (((s ×ˢ T).filter (fun p : Λ × G => x ∈ p.1 • (p.2 • U))).card : ℝ≥0∞)`. Rewrite using `[Finset.card_filter, Finset.sum_product]`. Use `push_cast`. Simplify using `only [Set.indicator_apply, Pi.one_apply]`. Rewrite using `[hbool]`.

Establish `hcard : ((s ×ˢ T).filter (fun p : Λ × G => x ∈ p.1 • (p.2 • U))).card ≤ hfin.toFinset.card` using `by set P := (s ×ˢ T).filter (fun p : Λ × G => x ∈ p.1 • (p.2 • U)) with hPdef`. Establish `memP : ∀ p : Λ × G, p ∈ P → p.2 ∈ T ∧ x ∈ p.1 • (p.2 • U)`. Introduce `p hp`. Rewrite `hp` using `[hPdef, Finset.mem_filter, Finset.mem_product]`. Conclude with `⟨hp.1.2, hp.2⟩`.

Break down `P.eq_empty_or_nonempty with hP | ⟨p₀, h₀⟩` into its components or cases. Rewrite using `[hP]`. Conclude with `Nat.zero_le _`. Take `⟨ht₀, hx₀⟩` from `memP p₀ h₀`. Rewrite `hx₀` using `[mem_smul_smul_iff]`.

Use `Finset.card_le_card_of_injOn (fun p : Λ × G => (p₀.2⁻¹ * (p₀.1 : G)⁻¹) * ((p.1 : G) * p.2)) ?_ ?_` and prove the remaining obligations. Introduce `p hp`. Apply the tactic sequence `have hp' : p ∈ P := by first | exact Finset.mem_coe.1 hp | exact hp`. Take `⟨ht, hx⟩` from `memP p hp'`. Rewrite `hx` using `[mem_smul_smul_iff]`.

Use `show _ ∈ (hfin.toFinset : Set G)`. Rewrite using `[Set.Finite.coe_toFinset]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `Set.mem_mul.2 ⟨_, hx₀, (p.2⁻¹ * ((p.1 : G)⁻¹ * x))⁻¹, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Set.mem_inv, inv_inv]`.

Conclude with `hx`. Use `group`. Conclude with `Γ.mul_mem (Γ.mul_mem (Γ.inv_mem (hTΓ _ ht₀)) (Γ.inv_mem (hΛΓ p₀.1.2))) (Γ.mul_mem (hΛΓ p.1.2) (hTΓ _ ht))`. Introduce `p hp q hq hpq`. Apply the tactic sequence `have hp' : p ∈ P := by first | exact Finset.mem_coe.1 hp | exact hp`.

Apply the tactic sequence `have hq' : q ∈ P := by first | exact Finset.mem_coe.1 hq | exact hq`. Establish `hpT` using `(memP p hp').1`. Establish `hqT` using `(memP q hq').1`. Establish `h1 : (p.1 : G) * p.2 = (q.1 : G) * q.2` using `mul_left_cancel hpq`. Establish `e : q.2 * p.2⁻¹ = (q.1 : G)⁻¹ * p.1`.

Rewrite using `[mul_inv_eq_iff_eq_mul, mul_assoc, h1, ← mul_assoc, inv_mul_cancel, one_mul]`. Establish `htt : p.2 = q.2` using `hTdist _ hpT _ hqT (e ▸ Λ.mul_mem (Λ.inv_mem q.1.2) p.1.2)`. Establish `hg : (p.1 : G) = q.1`. Rewrite `h1` using `[htt]`. Conclude with `mul_right_cancel h1`.

Conclude with `Prod.ext (Subtype.ext hg) htt`. Conclude with `hcard` after adjusting the coercions. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[lintegral_finset_sum']`. Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations.

Rewrite using `[lintegral_tsum]`. Conclude with `fun γ => ((measurable_one.indicator (hmeasA γ t))).aemeasurable`. Introduce `t _`. Conclude with `(Measurable.ennreal_tsum fun γ => measurable_one.indicator (hmeasA γ t)).aemeasurable`. Use `_ ≤ ∫⁻ _x, (hfin.toFinset.card : ℝ≥0∞) ∂ν := lintegral_mono hpt`.

Use `_ = (hfin.toFinset.card : ℝ≥0∞) * μ (S ∩ D) := by`. Rewrite using `[lintegral_const, hν, Measure.restrict_apply_univ]`.
-/
theorem packing_count : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (Γ Λ : Subgroup G) [Countable Λ] (μ : Measure G) (D U : Set G), Λ ≤ Γ → (∀ K : Set G, IsCompact K → (K ∩ Γ).Finite) → μ.IsHaarMeasure → IsFundamentalDomain Λ D μ → IsCompact U → ∃ k : ℕ, ∀ (T : Finset G) (S : Set G), (∀ t ∈ T, t ∈ Γ) → (∀ t ∈ T, ∀ t' ∈ T, t' * t⁻¹ ∈ Λ → t = t') → MeasurableSet S → (∀ γ ∈ Λ, ∀ x ∈ S, γ * x ∈ S) → (∀ t ∈ T, ∀ u ∈ U, t * u ∈ S) → T.card * μ U ≤ k * μ (S ∩ D) := by
  intro G _ _ _ _ _ _ _ _ Γ Λ _ μ D U hΛΓ hdisc hHaar hD hU
  have hUc : IsCompact (U * U⁻¹) := hU.mul hU.inv
  have hfin : (U * U⁻¹ ∩ (Γ : Set G)).Finite := hdisc _ hUc
  refine ⟨hfin.toFinset.card, ?_⟩
  intro T S hTΓ hTdist hS hSinv hTS
  have hUm : MeasurableSet U := hU.isClosed.measurableSet
  have hmeasA : ∀ (γ : Λ) (t : G), MeasurableSet (γ • (t • U)) := by
    intro γ t
    have : γ • (t • U) = (fun y => t⁻¹ * ((γ : G)⁻¹ * y)) ⁻¹' U := by
      ext y; rw [mem_smul_smul_iff]; rfl
    rw [this]
    exact hUm.preimage (continuous_const.mul (continuous_const.mul continuous_id)).measurable
  have hsubS : ∀ (γ : Λ), ∀ t ∈ T, γ • (t • U) ⊆ S := by
    intro γ t ht y hy
    rw [mem_smul_smul_iff] at hy
    have h1 := hSinv (γ : G) γ.2 _ (hTS t ht _ hy)
    simpa [mul_assoc] using h1
  set ν := μ.restrict (S ∩ D) with hν
  have key : ∀ t ∈ T, μ U = ∑' γ : Λ, ∫⁻ x, (γ • (t • U)).indicator 1 x ∂ν := by
    intro t ht
    rw [← measure_smul μ t U, hD.measure_eq_tsum (t • U)]
    refine tsum_congr fun γ => ?_
    rw [lintegral_indicator_one (hmeasA γ t), hν, Measure.restrict_apply (hmeasA γ t)]
    congr 1
    ext y
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, hsubS γ t ht h1, h2⟩
    · rintro ⟨h1, _, h2⟩; exact ⟨h1, h2⟩
  have hpt : ∀ x : G, ∑ t ∈ T, ∑' γ : Λ, (γ • (t • U)).indicator (1 : G → ℝ≥0∞) x
      ≤ (hfin.toFinset.card : ℝ≥0∞) := by
    intro x
    classical
    have hswap : ∑ t ∈ T, ∑' γ : Λ, (γ • (t • U)).indicator (1 : G → ℝ≥0∞) x
        = ∑' γ : Λ, ∑ t ∈ T, (γ • (t • U)).indicator (1 : G → ℝ≥0∞) x := by
      first
      | exact (Summable.tsum_finsetSum fun _ _ => ENNReal.summable).symm
      | exact (tsum_sum fun _ _ => ENNReal.summable).symm
      | exact (ENNReal.tsum_finsetSum _ _).symm
    rw [hswap, ENNReal.tsum_eq_iSup_sum]
    refine iSup_le fun s => ?_
    have hbool : ∑ γ ∈ s, ∑ t ∈ T, (γ • (t • U)).indicator (1 : G → ℝ≥0∞) x
        = (((s ×ˢ T).filter (fun p : Λ × G => x ∈ p.1 • (p.2 • U))).card : ℝ≥0∞) := by
      rw [Finset.card_filter, Finset.sum_product]
      push_cast
      simp only [Set.indicator_apply, Pi.one_apply]
    rw [hbool]
    have hcard : ((s ×ˢ T).filter (fun p : Λ × G => x ∈ p.1 • (p.2 • U))).card
        ≤ hfin.toFinset.card := by
      set P := (s ×ˢ T).filter (fun p : Λ × G => x ∈ p.1 • (p.2 • U)) with hPdef
      have memP : ∀ p : Λ × G, p ∈ P → p.2 ∈ T ∧ x ∈ p.1 • (p.2 • U) := by
        intro p hp
        rw [hPdef, Finset.mem_filter, Finset.mem_product] at hp
        exact ⟨hp.1.2, hp.2⟩
      rcases P.eq_empty_or_nonempty with hP | ⟨p₀, h₀⟩
      · rw [hP]; exact Nat.zero_le _
      obtain ⟨ht₀, hx₀⟩ := memP p₀ h₀
      rw [mem_smul_smul_iff] at hx₀
      refine Finset.card_le_card_of_injOn
        (fun p : Λ × G => (p₀.2⁻¹ * (p₀.1 : G)⁻¹) * ((p.1 : G) * p.2)) ?_ ?_
      · intro p hp
        have hp' : p ∈ P := by first | exact Finset.mem_coe.1 hp | exact hp
        obtain ⟨ht, hx⟩ := memP p hp'
        rw [mem_smul_smul_iff] at hx
        show _ ∈ (hfin.toFinset : Set G)
        rw [Set.Finite.coe_toFinset]
        refine ⟨?_, ?_⟩
        · refine Set.mem_mul.2 ⟨_, hx₀, (p.2⁻¹ * ((p.1 : G)⁻¹ * x))⁻¹, ?_, ?_⟩
          · rw [Set.mem_inv, inv_inv]; exact hx
          · group
        · exact Γ.mul_mem (Γ.mul_mem (Γ.inv_mem (hTΓ _ ht₀)) (Γ.inv_mem (hΛΓ p₀.1.2)))
            (Γ.mul_mem (hΛΓ p.1.2) (hTΓ _ ht))
      · intro p hp q hq hpq
        have hp' : p ∈ P := by first | exact Finset.mem_coe.1 hp | exact hp
        have hq' : q ∈ P := by first | exact Finset.mem_coe.1 hq | exact hq
        have hpT := (memP p hp').1
        have hqT := (memP q hq').1
        have h1 : (p.1 : G) * p.2 = (q.1 : G) * q.2 := mul_left_cancel hpq
        have e : q.2 * p.2⁻¹ = (q.1 : G)⁻¹ * p.1 := by
          rw [mul_inv_eq_iff_eq_mul, mul_assoc, h1, ← mul_assoc, inv_mul_cancel, one_mul]
        have htt : p.2 = q.2 := hTdist _ hpT _ hqT (e ▸ Λ.mul_mem (Λ.inv_mem q.1.2) p.1.2)
        have hg : (p.1 : G) = q.1 := by
          rw [htt] at h1; exact mul_right_cancel h1
        exact Prod.ext (Subtype.ext hg) htt
    exact_mod_cast hcard
  calc (T.card : ℝ≥0∞) * μ U = ∑ t ∈ T, μ U := by rw [Finset.sum_const, nsmul_eq_mul]
    _ = ∑ t ∈ T, ∑' γ : Λ, ∫⁻ x, (γ • (t • U)).indicator 1 x ∂ν := Finset.sum_congr rfl key
    _ = ∫⁻ x, ∑ t ∈ T, ∑' γ : Λ, (γ • (t • U)).indicator (1 : G → ℝ≥0∞) x ∂ν := by
      rw [lintegral_finset_sum']
      · refine Finset.sum_congr rfl fun t _ => ?_
        rw [lintegral_tsum]
        exact fun γ => ((measurable_one.indicator (hmeasA γ t))).aemeasurable
      · intro t _
        exact (Measurable.ennreal_tsum fun γ => measurable_one.indicator (hmeasA γ t)).aemeasurable
    _ ≤ ∫⁻ _x, (hfin.toFinset.card : ℝ≥0∞) ∂ν := lintegral_mono hpt
    _ = (hfin.toFinset.card : ℝ≥0∞) * μ (S ∩ D) := by
      rw [lintegral_const, hν, Measure.restrict_apply_univ]

end GlobalTheory.Packing
