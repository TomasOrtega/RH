import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.QuotientIntegralFinitelyManyCellsWeightedSum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.QuotientIntegralFinitelyManyCellsWeightedSumStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.QuotientIntegralVanishOfCommutingProductStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsClosedOfLocallyCompactSpace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.VanCore

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Use `(IsQuotIntL1.zero : IsQuotIntL1 μR μG 0 0) using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `x`. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Consider the case `insert i s hi ih`. Establish `h1` using `(h i (Finset.mem_insert_self i s)).smul (c i)`. Establish `h2` using `ih (fun j hj => h j (Finset.mem_insert_of_mem hj))`. Use `h1.add h2 using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `x`. Simplify using `[Finset.sum_insert hi]`. Simplify using `[Finset.sum_insert hi]`.
-/
theorem quotient_integral_weighted_sum {G : Type} [Group G] [MeasurableSpace G] {R : Subgroup G} {μR : Measure R} {μG : Measure G}
    {ι : Type} (s : Finset ι) (c : ι → ℂ) (f : ι → G → ℂ) (z : ι → ℂ) (h : ∀ i ∈ s, IsQuotIntL1 μR μG (f i) (z i)) :
    IsQuotIntL1 μR μG (fun x => ∑ i ∈ s, c i * f i x) (∑ i ∈ s, c i * z i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    convert (IsQuotIntL1.zero : IsQuotIntL1 μR μG 0 0) using 1
    · funext x; simp
    · simp
  | insert i s hi ih =>
    have h1 := (h i (Finset.mem_insert_self i s)).smul (c i)
    have h2 := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    convert h1.add h2 using 1
    · funext x; simp [Finset.sum_insert hi]
    · simp [Finset.sum_insert hi]

/- English proof (translation)
Introduce `G₁ G₂ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A₁ B₁ R₁ A₂ B₂ R₂ hA₁ hB₁ hR₁ hc₁ he₁ hs₁ hA₂ hB₂ hR₂ hc₂ he₂ hs₂ μR₁ μG₁ ρ₁ μ₁ μR₂ μG₂ ρ₂ μ₂ i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 K C T hKB hKc hKo hCc hCB hTB F₁ F₂ z hF₁ hF₂ hFK hsupp hIter`. Use `haveI : LocallyCompactSpace B₁ := hB₁.locallyCompactSpace`. Use `haveI : LocallyCompactSpace B₂ := hB₂.locallyCompactSpace`. Establish `hR₁B : IsClosed ((R₁.subgroupOf B₁ : Subgroup B₁) : Set B₁)`. Rewrite using `[Subgroup.coe_subgroupOf]`.

Conclude with `hR₁.preimage continuous_subtype_val`. Establish `hR₂B : IsClosed ((R₂.subgroupOf B₂ : Subgroup B₂) : Set B₂)`. Rewrite using `[Subgroup.coe_subgroupOf]`. Conclude with `hR₂.preimage continuous_subtype_val`. Establish `FK : ∀ h, ∀ k ∈ K, F₁ (h * k) = F₁ h` using `fun h k hk => by`.

Establish `h1` using `hF₂ (h * k)`. Rewrite `h1` using `[hFK h k hk]`. Conclude with `(IsQuotIntL1.unique hR₂ (hF₂ h) h1).symm`. Establish `FZ : ∀ h, F₂ h = 0 → F₁ h = 0` using `fun h h0 => by`. Establish `h1` using `hF₂ h`.

Rewrite `h1` using `[h0]`. Conclude with `(GlobalTheory.QuotZero.left_and_zero hR₂ μR₂ μG₂ h1).2 rfl`. Establish `FL` using `(GlobalTheory.QuotZero.left_and_zero hR₁ μR₁ μG₁ hF₁).1`. Establish `hCb : IsCompact (Subtype.val ⁻¹' C : Set B₁)`. Rewrite using `[Subtype.isCompact_iff, Set.image_preimage_eq_of_subset]`.

Conclude with `hCc`. Introduce `x hx`. Conclude with `⟨⟨x, hCB hx⟩, rfl⟩`. Establish `hKbc : IsCompact ((K.subgroupOf B₁ : Subgroup B₁) : Set B₁)`. Rewrite using `[Subgroup.coe_subgroupOf, Subgroup.coe_subtype, Subtype.isCompact_iff, Set.image_preimage_eq_of_subset]`.

Conclude with `hKc`. Introduce `x hx`. Conclude with `⟨⟨x, hKB hx⟩, rfl⟩`. Establish `hKint : (interior ((K.subgroupOf B₁ : Subgroup B₁) : Set B₁)).Nonempty`. Rewrite using `[hKo.interior_eq]`.

Conclude with `⟨1, (K.subgroupOf B₁).one_mem⟩`. Take `⟨S, hS⟩` from `compact_covered_by_mul_left_translates hCb hKint`. Set `T'' : Finset B₁` to `((T.subtype (· ∈ B₁)) ×ˢ S).image (fun p => p.1 * p.2⁻¹)`. Establish `cell : ∀ a ∈ A₁, ∀ q : B₁, F₂ (a * q) ≠ 0 → ∃ q' ∈ T'', ∃ r ∈ R₁.subgroupOf B₁, ∃ k ∈ K.subgroupOf B₁, q = r * q' * k`. Introduce `a ha q hq`.

Take `⟨q₀, hq₀, r, hr, a'', ha'', k, hk, hdec⟩` from `hsupp _ hq`. Take `⟨e, he⟩` from `he₁`. Take `⟨⟨pa, pb⟩, hp⟩ : ∃ p, e.symm r = p` from `⟨_, rfl⟩`. Establish `hrp : r = (pa : G₁) * pb` using `by rw [← he (pa, pb), ← hp, e.apply_symm_apply]`. Substitute `hrp` using the available equality.

Establish `hpR` using `hs₁ _ pa.2 _ pb.2 hr`. Establish `hkB : k ∈ B₁` using `hCB hk`. Establish `hq₀B : q₀ ∈ B₁` using `hTB q₀ hq₀`. Establish `key : e (⟨a, ha⟩, q) = e (pa * ⟨a'', ha''⟩, pb * ⟨q₀, hq₀B⟩ * ⟨k, hkB⟩)`. Rewrite using `[he, he]`.

Use `show a * (q : G₁) = ((pa : G₁) * a'') * ((pb : G₁) * q₀ * k)`. Rewrite using `[hdec, mul_assoc (pa : G₁) pb a'', ← hc₁ a'' ha'' pb pb.2]`. Simplify using `only [mul_assoc]`. Establish `hq' : q = pb * ⟨q₀, hq₀B⟩ * ⟨k, hkB⟩` using `congrArg Prod.snd (e.injective key)`. Take `⟨g, hgS, hg⟩` from `Set.mem_iUnion₂.1 (hS (show (⟨k, hkB⟩ : B₁) ∈ (Subtype.val ⁻¹' C : Set B₁) from hk))`.

Use `⟨⟨q₀, hq₀B⟩ * g⁻¹, ?_, pb, ?_, g * ⟨k, hkB⟩, hg, ?_⟩` and prove the remaining obligations. Conclude with `Finset.mem_image.2 ⟨(⟨q₀, hq₀B⟩, g), Finset.mem_product.2 ⟨Finset.mem_subtype.2 hq₀, hgS⟩, rfl⟩`. Conclude with `Subgroup.mem_subgroupOf.2 hpR.2`. Rewrite using `[hq']`. Use `group`.

Take `⟨T', w, -, hW⟩` from `GlobalTheory.CellInt.quotInt_finiteCells B₁ (R₁.subgroupOf B₁) (K.subgroupOf B₁) hR₁B hKbc hKo ρ₁ μ₁ inferInstance inferInstance inferInstance inferInstance T''`. Use `GlobalTheory.T.quotientIntegral_vanish_of_commutingProduct G₁ A₁ B₁ R₁ hA₁ hB₁ hR₁ hc₁ he₁ hs₁ μR₁ μG₁ ρ₁ μ₁ inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance F₁ z hF₁ ?_` and prove the remaining obligations. Introduce `a ha`. Establish `h1` using `hW (fun b => F₁ (a * b.1)) (fun r hr g => by show F₁ (a * ((r : G₁) * g)) = F₁ (a * g)`. Rewrite using `[← mul_assoc, hc₁ a ha r r.2, mul_assoc]`.

Conclude with `FL _ (Subgroup.mem_subgroupOf.1 hr) _)`. Use the proof step `(fun k hk g => by show F₁ (a * ((g : G₁) * k)) = F₁ (a * g)`. Rewrite using `[← mul_assoc]`. Conclude with `FK _ _ (Subgroup.mem_subgroupOf.1 hk))`. Use the proof step `(fun g hg => cell a ha g (fun h0 => hg (FZ _ h0)))`.

It suffices to establish `hsum : ∑ q ∈ T', w q * F₁ (a * q.1) = 0 by`. Use `h1 using 1` and compare the differences between its conclusion and the goal. Conclude with `hsum.symm`. Use `GlobalTheory.T.quotientIntegral_vanish_of_commutingProduct G₂ A₂ B₂ R₂ hA₂ hB₂ hR₂ hc₂ he₂ hs₂ μR₂ μG₂ ρ₂ μ₂ inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance (fun h₂ => ∑ q ∈ T', w q * F₂ (a * q.1) h₂) _ (quotient_integral_weighted_sum T' w (fun …` and prove the remaining obligations. Introduce `a' ha'`.

Take `⟨f₁, hf₁0, hf₁q⟩` from `hIter a ha a' ha'`. Establish `hs` using `quotient_integral_weighted_sum T' w (fun q (b : B₂) => F₂ (a * q.1) (a' * b.1)) f₁ (fun q _ => hf₁q q)`. Establish `hf₁ : IsQuotIntL1 ρ₁ μ₁ f₁ (∑ q ∈ T', w q * f₁ q)` using `hW f₁ (GlobalTheory.QuotZero.left_and_zero hR₁B ρ₁ μ₁ hf₁0).1 (fun k hk g => by`. Establish `h2 : IsQuotIntL1 ρ₂ μ₂ (fun q₂ : B₂ => F₂ (a * g.1) (a' * q₂.1)) (f₁ (g * k))`. Establish `h3` using `hf₁q (g * k)`.

Establish `e3 : (fun q₂ : B₂ => F₂ (a * (g * k).1) (a' * q₂.1)) = fun q₂ : B₂ => F₂ (a * g.1) (a' * q₂.1)`. Use function extensionality and compare the values at `q₂`. Rewrite using `[Subgroup.coe_mul, ← mul_assoc, hFK _ _ (Subgroup.mem_subgroupOf.1 hk)]`. Conclude with `e3 ▸ h3`. Conclude with `IsQuotIntL1.unique hR₂B h2 (hf₁q g))`.

Use the proof step `(fun g hg => cell a ha g (fun h0 => hg ((GlobalTheory.QuotZero.left_and_zero hR₂B ρ₂ μ₂ (hf₁q g)).2 (by funext q₂; simp [h0]))))`. Establish `hz` using `IsQuotIntL1.unique hR₁B hf₁ hf₁0`. Rewrite `hs` using `[hz]`. Conclude with `hs`.
-/
theorem vanish : ∀ (G₁ G₂ : Type) [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [SecondCountableTopology G₁] [LocallyCompactSpace G₁] [T2Space G₁] [MeasurableSpace G₁] [BorelSpace G₁] [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂] [SecondCountableTopology G₂] [LocallyCompactSpace G₂] [T2Space G₂] [MeasurableSpace G₂] [BorelSpace G₂] (A₁ B₁ R₁ : Subgroup G₁) (A₂ B₂ R₂ : Subgroup G₂), IsClosed (A₁ : Set G₁) → IsClosed (B₁ : Set G₁) → IsClosed (R₁ : Set G₁) → (∀ a ∈ A₁, ∀ b ∈ B₁, a * b = b * a) → (∃ e : (A₁ × B₁) ≃ₜ G₁, ∀ p, e p = p.1 * p.2) → (∀ a ∈ A₁, ∀ b ∈ B₁, a * b ∈ R₁ → a ∈ R₁ ∧ b ∈ R₁) → IsClosed (A₂ : Set G₂) → IsClosed (B₂ : Set G₂) → IsClosed (R₂ : Set G₂) → (∀ a ∈ A₂, ∀ b ∈ B₂, a * b = b * a) → (∃ e : (A₂ × B₂) ≃ₜ G₂, ∀ p, e p = p.1 * p.2) → (∀ a ∈ A₂, ∀ b ∈ B₂, a * b ∈ R₂ → a ∈ R₂ ∧ b ∈ R₂) → ∀ (μR₁ : Measure R₁) (μG₁ : Measure G₁) (ρ₁ : Measure (R₁.subgroupOf B₁)) (μ₁ : Measure B₁) (μR₂ : Measure R₂) (μG₂ : Measure G₂) (ρ₂ : Measure (R₂.subgroupOf B₂)) (μ₂ : Measure B₂), μR₁.IsHaarMeasure → μR₁.IsInvInvariant → μG₁.IsHaarMeasure → ρ₁.IsHaarMeasure → ρ₁.IsInvInvariant → μ₁.IsHaarMeasure → μ₁.IsMulRightInvariant → μR₂.IsHaarMeasure → μR₂.IsInvInvariant → μG₂.IsHaarMeasure → ρ₂.IsHaarMeasure → ρ₂.IsInvInvariant → μ₂.IsHaarMeasure → ∀ (K : Subgroup G₁) (C : Set G₁) (T : Finset G₁), K ≤ B₁ → IsCompact (K : Set G₁) → IsOpen ((K.subgroupOf B₁ : Subgroup B₁) : Set B₁) → IsCompact C → C ⊆ (B₁ : Set G₁) → (∀ q ∈ T, q ∈ B₁) → ∀ (F₁ : G₁ → ℂ) (F₂ : G₁ → G₂ → ℂ) (z : ℂ), IsQuotIntL1 μR₁ μG₁ F₁ z → (∀ h₁, IsQuotIntL1 μR₂ μG₂ (F₂ h₁) (F₁ h₁)) → (∀ h₁, ∀ k ∈ K, F₂ (h₁ * k) = F₂ h₁) → (∀ h₁, F₂ h₁ ≠ 0 → ∃ q ∈ T, ∃ r ∈ R₁, ∃ a ∈ A₁, ∃ k ∈ C, h₁ = r * a * q * k) → (∀ a ∈ A₁, ∀ a' ∈ A₂, Iter2 ρ₁ μ₁ ρ₂ μ₂ (fun (q₁ : B₁) (q₂ : B₂) => F₂ (a * q₁.1) (a' * q₂.1)) 0) → z = 0 := by
  intro G₁ G₂ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A₁ B₁ R₁ A₂ B₂ R₂ hA₁ hB₁ hR₁ hc₁ he₁ hs₁ hA₂ hB₂ hR₂ hc₂ he₂ hs₂
    μR₁ μG₁ ρ₁ μ₁ μR₂ μG₂ ρ₂ μ₂ i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 K C T hKB hKc hKo hCc hCB hTB
    F₁ F₂ z hF₁ hF₂ hFK hsupp hIter
  classical
  haveI : LocallyCompactSpace B₁ := hB₁.locallyCompactSpace
  haveI : LocallyCompactSpace B₂ := hB₂.locallyCompactSpace
  have hR₁B : IsClosed ((R₁.subgroupOf B₁ : Subgroup B₁) : Set B₁) := by
    rw [Subgroup.coe_subgroupOf]; exact hR₁.preimage continuous_subtype_val
  have hR₂B : IsClosed ((R₂.subgroupOf B₂ : Subgroup B₂) : Set B₂) := by
    rw [Subgroup.coe_subgroupOf]; exact hR₂.preimage continuous_subtype_val

  have FK : ∀ h, ∀ k ∈ K, F₁ (h * k) = F₁ h := fun h k hk => by
    have h1 := hF₂ (h * k)
    rw [hFK h k hk] at h1
    exact (IsQuotIntL1.unique hR₂ (hF₂ h) h1).symm
  have FZ : ∀ h, F₂ h = 0 → F₁ h = 0 := fun h h0 => by
    have h1 := hF₂ h
    rw [h0] at h1
    exact (GlobalTheory.QuotZero.left_and_zero hR₂ μR₂ μG₂ h1).2 rfl
  have FL := (GlobalTheory.QuotZero.left_and_zero hR₁ μR₁ μG₁ hF₁).1

  have hCb : IsCompact (Subtype.val ⁻¹' C : Set B₁) := by
    rw [Subtype.isCompact_iff, Set.image_preimage_eq_of_subset]
    · exact hCc
    · intro x hx; exact ⟨⟨x, hCB hx⟩, rfl⟩
  have hKbc : IsCompact ((K.subgroupOf B₁ : Subgroup B₁) : Set B₁) := by
    rw [Subgroup.coe_subgroupOf, Subgroup.coe_subtype, Subtype.isCompact_iff, Set.image_preimage_eq_of_subset]
    · exact hKc
    · intro x hx; exact ⟨⟨x, hKB hx⟩, rfl⟩
  have hKint : (interior ((K.subgroupOf B₁ : Subgroup B₁) : Set B₁)).Nonempty := by
    rw [hKo.interior_eq]; exact ⟨1, (K.subgroupOf B₁).one_mem⟩
  obtain ⟨S, hS⟩ := compact_covered_by_mul_left_translates hCb hKint
  let T'' : Finset B₁ := ((T.subtype (· ∈ B₁)) ×ˢ S).image (fun p => p.1 * p.2⁻¹)

  have cell : ∀ a ∈ A₁, ∀ q : B₁, F₂ (a * q) ≠ 0 →
      ∃ q' ∈ T'', ∃ r ∈ R₁.subgroupOf B₁, ∃ k ∈ K.subgroupOf B₁, q = r * q' * k := by
    intro a ha q hq
    obtain ⟨q₀, hq₀, r, hr, a'', ha'', k, hk, hdec⟩ := hsupp _ hq
    obtain ⟨e, he⟩ := he₁
    obtain ⟨⟨pa, pb⟩, hp⟩ : ∃ p, e.symm r = p := ⟨_, rfl⟩
    have hrp : r = (pa : G₁) * pb := by rw [← he (pa, pb), ← hp, e.apply_symm_apply]
    subst hrp
    have hpR := hs₁ _ pa.2 _ pb.2 hr
    have hkB : k ∈ B₁ := hCB hk
    have hq₀B : q₀ ∈ B₁ := hTB q₀ hq₀
    have key : e (⟨a, ha⟩, q) = e (pa * ⟨a'', ha''⟩, pb * ⟨q₀, hq₀B⟩ * ⟨k, hkB⟩) := by
      rw [he, he]
      show a * (q : G₁) = ((pa : G₁) * a'') * ((pb : G₁) * q₀ * k)
      rw [hdec, mul_assoc (pa : G₁) pb a'', ← hc₁ a'' ha'' pb pb.2]
      simp only [mul_assoc]
    have hq' : q = pb * ⟨q₀, hq₀B⟩ * ⟨k, hkB⟩ := congrArg Prod.snd (e.injective key)
    obtain ⟨g, hgS, hg⟩ := Set.mem_iUnion₂.1 (hS (show (⟨k, hkB⟩ : B₁) ∈ (Subtype.val ⁻¹' C : Set B₁) from hk))
    refine ⟨⟨q₀, hq₀B⟩ * g⁻¹, ?_, pb, ?_, g * ⟨k, hkB⟩, hg, ?_⟩
    · exact Finset.mem_image.2 ⟨(⟨q₀, hq₀B⟩, g), Finset.mem_product.2 ⟨Finset.mem_subtype.2 hq₀, hgS⟩, rfl⟩
    · exact Subgroup.mem_subgroupOf.2 hpR.2
    · rw [hq']; group
  obtain ⟨T', w, -, hW⟩ := GlobalTheory.CellInt.quotInt_finiteCells B₁ (R₁.subgroupOf B₁) (K.subgroupOf B₁) hR₁B hKbc hKo
    ρ₁ μ₁ inferInstance inferInstance inferInstance inferInstance T''
  refine GlobalTheory.T.quotientIntegral_vanish_of_commutingProduct G₁ A₁ B₁ R₁ hA₁ hB₁ hR₁ hc₁ he₁ hs₁ μR₁ μG₁ ρ₁ μ₁ inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance F₁ z hF₁ ?_
  intro a ha
  have h1 := hW (fun b => F₁ (a * b.1))
    (fun r hr g => by
      show F₁ (a * ((r : G₁) * g)) = F₁ (a * g)
      rw [← mul_assoc, hc₁ a ha r r.2, mul_assoc]
      exact FL _ (Subgroup.mem_subgroupOf.1 hr) _)
    (fun k hk g => by
      show F₁ (a * ((g : G₁) * k)) = F₁ (a * g)
      rw [← mul_assoc]
      exact FK _ _ (Subgroup.mem_subgroupOf.1 hk))
    (fun g hg => cell a ha g (fun h0 => hg (FZ _ h0)))
  suffices hsum : ∑ q ∈ T', w q * F₁ (a * q.1) = 0 by
    convert h1 using 1; exact hsum.symm
  refine GlobalTheory.T.quotientIntegral_vanish_of_commutingProduct G₂ A₂ B₂ R₂ hA₂ hB₂ hR₂ hc₂ he₂ hs₂ μR₂ μG₂ ρ₂ μ₂ inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance (fun h₂ => ∑ q ∈ T', w q * F₂ (a * q.1) h₂) _
    (quotient_integral_weighted_sum T' w (fun q => F₂ (a * q.1)) (fun q => F₁ (a * q.1)) (fun q _ => hF₂ _)) ?_
  intro a' ha'
  obtain ⟨f₁, hf₁0, hf₁q⟩ := hIter a ha a' ha'
  have hs := quotient_integral_weighted_sum T' w (fun q (b : B₂) => F₂ (a * q.1) (a' * b.1)) f₁ (fun q _ => hf₁q q)
  have hf₁ : IsQuotIntL1 ρ₁ μ₁ f₁ (∑ q ∈ T', w q * f₁ q) := hW f₁
    (GlobalTheory.QuotZero.left_and_zero hR₁B ρ₁ μ₁ hf₁0).1
    (fun k hk g => by
      have h2 : IsQuotIntL1 ρ₂ μ₂ (fun q₂ : B₂ => F₂ (a * g.1) (a' * q₂.1)) (f₁ (g * k)) := by
        have h3 := hf₁q (g * k)
        have e3 : (fun q₂ : B₂ => F₂ (a * (g * k).1) (a' * q₂.1)) = fun q₂ : B₂ => F₂ (a * g.1) (a' * q₂.1) := by
          funext q₂
          rw [Subgroup.coe_mul, ← mul_assoc, hFK _ _ (Subgroup.mem_subgroupOf.1 hk)]
        exact e3 ▸ h3
      exact IsQuotIntL1.unique hR₂B h2 (hf₁q g))
    (fun g hg => cell a ha g (fun h0 => hg ((GlobalTheory.QuotZero.left_and_zero hR₂B ρ₂ μ₂ (hf₁q g)).2
      (by funext q₂; simp [h0]))))
  have hz := IsQuotIntL1.unique hR₁B hf₁ hf₁0
  rw [hz] at hs
  exact hs

end GlobalTheory.VanCore
