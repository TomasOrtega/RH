import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FourierMatch
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.CosetIntegral

/- English proof (translation)
Establish `hmeas : ∀ q, MeasurableSet ((fun y => y * (r q)⁻¹) ⁻¹' H)` using `fun q => (hH.preimage (continuous_mul_right _)).measurableSet`. Establish `hmq : ∀ q, m ((fun y => y * (r q)⁻¹) ⁻¹' H) = 1` using `fun q => by`. Rewrite using `[measure_preimage_mul_right, hm]`. Rewrite using `[integral_finset_sum]`. Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations.

Rewrite using `[integral_indicator_const _ (hmeas q), measureReal_def, hmq q]`. Simplify using the standard rewrite rules. Introduce `q _`. Conclude with `(integrable_indicator_iff (hmeas q)).2 (integrableOn_const (by rw [hmq q]; simp))`.
-/
theorem integral_sum_indicator_translate {G ι : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] (m : Measure G)
    [m.IsMulRightInvariant] (H : Set G) (hH : IsOpen H) (hm : m H = 1) (T : Finset ι)
    (r : ι → G) (c : ι → ℂ) :
    ∫ x, ∑ q ∈ T, ((fun y => y * (r q)⁻¹) ⁻¹' H).indicator (fun _ => c q) x ∂m
      = ∑ q ∈ T, c q := by
  have hmeas : ∀ q, MeasurableSet ((fun y => y * (r q)⁻¹) ⁻¹' H) := fun q =>
    (hH.preimage (continuous_mul_right _)).measurableSet
  have hmq : ∀ q, m ((fun y => y * (r q)⁻¹) ⁻¹' H) = 1 := fun q => by
    rw [measure_preimage_mul_right, hm]
  rw [integral_finset_sum]
  · refine Finset.sum_congr rfl fun q _ => ?_
    rw [integral_indicator_const _ (hmeas q), measureReal_def, hmq q]
    simp
  · intro q _
    exact (integrable_indicator_iff (hmeas q)).2 (integrableOn_const (by rw [hmq q]; simp))

/- English proof (translation)
Set `S₀ : Subgroup S` to `R₀.comap i`. Establish `hS₀o : IsOpen (i ⁻¹' (R₀ : Set R))` using `hR₀o.preimage hi.continuous`. Establish `hconst : ∀ g r, g * (i r)⁻¹ ∈ R₀ → h (i r) = h g`. Introduce `g r hg`. Use `hinv _ hg (i r)` as an intermediate fact.

Simplify using `using this.symm`. Set `U : S → Set S` to `fun s => (fun x => x * s⁻¹) ⁻¹' (i ⁻¹' (R₀ : Set R))`. Establish `hUo : ∀ s, IsOpen (U s)` using `fun s => hS₀o.preimage (continuous_mul_right _)`. Take `⟨t, ht⟩` from `hcs.isCompact.elim_finite_subcover U hUo (fun x _ => Set.mem_iUnion.2 ⟨x, by simp [U, R₀.one_mem]⟩)`. Set `mk : S → Quotient (QuotientGroup.rightRel S₀)` to `fun s => Quotient.mk _ s`.

Set `T` to `t.image mk`. Establish `hrel : ∀ a b : S, mk a = mk b ↔ i b * (i a)⁻¹ ∈ R₀` using `fun a b => by`. Simplify using `only [mk, Quotient.eq, QuotientGroup.rightRel_apply, S₀, Subgroup.mem_comap, map_mul, map_inv]`. Establish `hout : ∀ q, mk q.out = q` using `fun q => Quotient.out_eq q`. Establish `hsuppT : ∀ x, h (i x) ≠ 0 → mk x ∈ T`.

Introduce `x hx`. Establish `hx' : x ∈ tsupport (fun s => h (i s))` using `subset_tsupport _ hx`. Take `⟨s, hs, hxs⟩` from `Set.mem_iUnion₂.1 (ht hx')`. Use `Finset.mem_image.2 ⟨s, hs, (hrel s x).2 ?_⟩` and prove the remaining obligations. Simplify `hxs` using `[U]`.

Establish `hrep : ∀ x, h (i (mk x).out) = h (i x)`. Introduce `x`. Apply `hconst` to reduce the goal to its premises. Conclude with `(hrel _ x).1 (hout _)`. Establish `hR : (fun g => h g) = fun g => ∑ q ∈ T, ((fun y => y * (i q.out)⁻¹) ⁻¹' (R₀ : Set R)).indicator (fun _ => h (i q.out)) g`.

Use function extensionality and compare the values at `g`. Distinguish the cases in `hg : h g = 0`. Rewrite using `[hg]`. Use `symm`. Use `Finset.sum_eq_zero fun q _ => ?_` and prove the remaining obligations.

Distinguish the cases in `hm : g ∈ ((fun y => y * (i q.out)⁻¹) ⁻¹' (R₀ : Set R))`. Rewrite using `[Set.indicator_of_mem hm, hconst g _ hm, hg]`. Rewrite using `[Set.indicator_of_notMem hm]`. Take `⟨k, hk, s, rfl⟩` from `hsupp g hg`. Establish `hs : h (i s) ≠ 0` using `by rwa [hinv k hk] at hg`.

Establish `hmem : ∀ q, (k * i s ∈ ((fun y => y * (i q.out)⁻¹) ⁻¹' (R₀ : Set R))) ↔ mk s = q`. Introduce `q`. Establish `e : mk s = q ↔ i s * (i q.out)⁻¹ ∈ R₀` using `by rw [← hrel q.out s, hout q, eq_comm]`. Rewrite using `[e]`. Simplify using `only [Set.mem_preimage, SetLike.mem_coe, mul_assoc]`.

Conclude with `Subgroup.mul_mem_cancel_left R₀ hk`. Simplify using `only [Set.indicator, hmem, Finset.sum_ite_eq, if_pos (hsuppT s hs), hrep, hinv k hk]`. Establish `hS : (fun x => h (i x)) = fun x => ∑ q ∈ T, ((fun y => y * q.out⁻¹) ⁻¹' (i ⁻¹' (R₀ : Set R))).indicator (fun _ => h (i q.out)) x`. Use function extensionality and compare the values at `x`. Establish `hmem : ∀ q, x ∈ ((fun y => y * q.out⁻¹) ⁻¹' (i ⁻¹' (R₀ : Set R))) ↔ mk x = q`.

Introduce `q`. Establish `e : mk x = q ↔ i x * (i q.out)⁻¹ ∈ R₀` using `by rw [← hrel q.out x, hout q, eq_comm]`. Rewrite using `[e]`. Simplify using the standard rewrite rules. Simplify using `only [Set.indicator, hmem, Finset.sum_ite_eq]`.

Use `split_ifs with hx`. Rewrite using `[hrep]`. Assume the negation of the conclusion as `hne`. Conclude with `hx (hsuppT x hne)`. Rewrite using `[hR, hS, integral_sum_indicator_translate μ _ hR₀o hμ, integral_sum_indicator_translate ν _ hS₀o hν]`.
-/
theorem integral_eq_of_coset_support
    (R S : Type) [Group R] [TopologicalSpace R] [IsTopologicalGroup R] [LocallyCompactSpace R]
    [T2Space R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R] [Group S]
    [TopologicalSpace S] [IsTopologicalGroup S] [MeasurableSpace S] [BorelSpace S]
    (i : S →* R) (hi : Topology.IsClosedEmbedding i) (μ : Measure R) (ν : Measure S)
    [μ.IsHaarMeasure] [μ.IsMulRightInvariant] [ν.IsHaarMeasure] [ν.IsMulRightInvariant]
    (R₀ : Subgroup R) (hR₀o : IsOpen (R₀ : Set R)) (_hR₀c : IsCompact (R₀ : Set R))
    (hμ : μ R₀ = 1) (hν : ν (i ⁻¹' R₀) = 1) (h : R → ℂ)
    (hinv : ∀ k ∈ R₀, ∀ g, h (k * g) = h g)
    (hsupp : ∀ g, h g ≠ 0 → ∃ k ∈ R₀, ∃ s, g = k * i s)
    (hcs : HasCompactSupport (fun s => h (i s))) :
    ∫ g, h g ∂μ = ∫ s, h (i s) ∂ν := by
  classical
  let S₀ : Subgroup S := R₀.comap i
  have hS₀o : IsOpen (i ⁻¹' (R₀ : Set R)) := hR₀o.preimage hi.continuous
  have hconst : ∀ g r, g * (i r)⁻¹ ∈ R₀ → h (i r) = h g := by
    intro g r hg
    have := hinv _ hg (i r)
    simpa using this.symm
  let U : S → Set S := fun s => (fun x => x * s⁻¹) ⁻¹' (i ⁻¹' (R₀ : Set R))
  have hUo : ∀ s, IsOpen (U s) := fun s => hS₀o.preimage (continuous_mul_right _)
  obtain ⟨t, ht⟩ := hcs.isCompact.elim_finite_subcover U hUo
    (fun x _ => Set.mem_iUnion.2 ⟨x, by simp [U, R₀.one_mem]⟩)
  let mk : S → Quotient (QuotientGroup.rightRel S₀) := fun s => Quotient.mk _ s
  let T := t.image mk
  have hrel : ∀ a b : S, mk a = mk b ↔ i b * (i a)⁻¹ ∈ R₀ := fun a b => by
    simp only [mk, Quotient.eq, QuotientGroup.rightRel_apply, S₀, Subgroup.mem_comap,
      map_mul, map_inv]
  have hout : ∀ q, mk q.out = q := fun q => Quotient.out_eq q
  have hsuppT : ∀ x, h (i x) ≠ 0 → mk x ∈ T := by
    intro x hx
    have hx' : x ∈ tsupport (fun s => h (i s)) := subset_tsupport _ hx
    obtain ⟨s, hs, hxs⟩ := Set.mem_iUnion₂.1 (ht hx')
    refine Finset.mem_image.2 ⟨s, hs, (hrel s x).2 ?_⟩
    simpa [U] using hxs
  have hrep : ∀ x, h (i (mk x).out) = h (i x) := by
    intro x
    apply hconst
    exact (hrel _ x).1 (hout _)

  have hR : (fun g => h g) = fun g => ∑ q ∈ T,
      ((fun y => y * (i q.out)⁻¹) ⁻¹' (R₀ : Set R)).indicator (fun _ => h (i q.out)) g := by
    funext g
    by_cases hg : h g = 0
    · rw [hg]
      symm
      refine Finset.sum_eq_zero fun q _ => ?_
      by_cases hm : g ∈ ((fun y => y * (i q.out)⁻¹) ⁻¹' (R₀ : Set R))
      · rw [Set.indicator_of_mem hm, hconst g _ hm, hg]
      · rw [Set.indicator_of_notMem hm]
    · obtain ⟨k, hk, s, rfl⟩ := hsupp g hg
      have hs : h (i s) ≠ 0 := by rwa [hinv k hk] at hg
      have hmem : ∀ q, (k * i s ∈ ((fun y => y * (i q.out)⁻¹) ⁻¹' (R₀ : Set R))) ↔ mk s = q := by
        intro q
        have e : mk s = q ↔ i s * (i q.out)⁻¹ ∈ R₀ := by rw [← hrel q.out s, hout q, eq_comm]
        rw [e]
        simp only [Set.mem_preimage, SetLike.mem_coe, mul_assoc]
        exact Subgroup.mul_mem_cancel_left R₀ hk
      simp only [Set.indicator, hmem, Finset.sum_ite_eq, if_pos (hsuppT s hs), hrep, hinv k hk]
  have hS : (fun x => h (i x)) = fun x => ∑ q ∈ T,
      ((fun y => y * q.out⁻¹) ⁻¹' (i ⁻¹' (R₀ : Set R))).indicator (fun _ => h (i q.out)) x := by
    funext x
    have hmem : ∀ q, x ∈ ((fun y => y * q.out⁻¹) ⁻¹' (i ⁻¹' (R₀ : Set R))) ↔ mk x = q := by
      intro q
      have e : mk x = q ↔ i x * (i q.out)⁻¹ ∈ R₀ := by rw [← hrel q.out x, hout q, eq_comm]
      rw [e]
      simp
    simp only [Set.indicator, hmem, Finset.sum_ite_eq]
    split_ifs with hx
    · rw [hrep]
    · by_contra hne
      exact hx (hsuppT x hne)
  rw [hR, hS, integral_sum_indicator_translate μ _ hR₀o hμ,
    integral_sum_indicator_translate ν _ hS₀o hν]

end GlobalTheory.CosetIntegral
