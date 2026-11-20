import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactSpaceAxis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnimodularAndLintegralUnfoldOfLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralConjEqOfSemidirectLatticeDatumStatement

open MeasureTheory Filter Topology GlobalTheory.ResLine
open scoped ENNReal

namespace GlobalTheory.ResLine

/- English proof (translation)
Use `Function.Injective.countable (f := fun δ : Λ.subgroupOf M => (⟨δ.1.1, δ.2⟩ : Λ)) ?_` and prove the remaining obligations. Introduce `a b h`. Conclude with `Subtype.ext (Subtype.ext (congrArg (fun l : Λ => (l : G)) h))`.
-/
theorem countable_subgroupOf_of_countable {G : Type} [Group G] (Λ M : Subgroup G) [Countable Λ] :
    Countable (Λ.subgroupOf M) := by
  refine Function.Injective.countable (f := fun δ : Λ.subgroupOf M => (⟨δ.1.1, δ.2⟩ : Λ)) ?_
  intro a b h
  exact Subtype.ext (Subtype.ext (congrArg (fun l : Λ => (l : G)) h))

/- English proof (translation)
Set `p : Λ.subgroupOf M × Λ.subgroupOf N → Λ` to `fun z => ⟨(z.2.1 : G) * (z.1.1 : G), Λ.mul_mem z.2.2 z.1.2⟩`. Establish `hb : Function.Bijective p`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨δ, γ⟩ ⟨δ', γ'⟩ h`. Establish `h1 : (γ.1 : G) * (δ.1 : G) = (γ'.1 : G) * (δ'.1 : G)` using `congrArg Subtype.val h`.

Establish `h2 : (γ'.1 : G)⁻¹ * γ.1 = (δ'.1 : G) * (δ.1 : G)⁻¹`. Rewrite using `[inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h1, mul_inv_cancel_right]`. Establish `h3 : (γ'.1 : G)⁻¹ * γ.1 = 1` using `disj _ (N.mul_mem (N.inv_mem γ'.1.2) γ.1.2) (h2 ▸ M.mul_mem δ'.1.2 (M.inv_mem δ.1.2))`. Establish `h4 : (γ'.1 : G) = γ.1` using `inv_mul_eq_one.1 h3`. Establish `h5 : (δ.1 : G) = δ'.1` using `by rw [h4] at h1; exact mul_left_cancel h1`.

Conclude with `Prod.ext (Subtype.ext (Subtype.ext h5)) (Subtype.ext (Subtype.ext h4.symm))`. Introduce and unpack `⟨l, hl⟩`. Take `⟨u, hu, m, hm, hu', hm', e⟩` from `dec l hl`. Conclude with `⟨(⟨⟨m, hm⟩, hm'⟩, ⟨⟨u, hu⟩, hu'⟩), Subtype.ext e.symm⟩`. Rewrite using `[← ENNReal.tsum_prod, ← (Equiv.ofBijective p hb).tsum_eq]`.

Both sides reduce to the same expression.
-/
theorem tsum_split_lattice {G : Type} [Group G] (N M Λ : Subgroup G) (disj : ∀ g ∈ N, g ∈ M → g = 1)
    (dec : ∀ γ ∈ Λ, ∃ u ∈ N, ∃ m ∈ M, u ∈ Λ ∧ m ∈ Λ ∧ γ = u * m) (f : G → ℝ≥0∞) :
    ∑' δ : Λ.subgroupOf M, ∑' γ : Λ.subgroupOf N, f ((γ.1 : G) * (δ.1 : G)) = ∑' l : Λ, f l := by
  let p : Λ.subgroupOf M × Λ.subgroupOf N → Λ := fun z => ⟨(z.2.1 : G) * (z.1.1 : G), Λ.mul_mem z.2.2 z.1.2⟩
  have hb : Function.Bijective p := by
    constructor
    · rintro ⟨δ, γ⟩ ⟨δ', γ'⟩ h
      have h1 : (γ.1 : G) * (δ.1 : G) = (γ'.1 : G) * (δ'.1 : G) := congrArg Subtype.val h
      have h2 : (γ'.1 : G)⁻¹ * γ.1 = (δ'.1 : G) * (δ.1 : G)⁻¹ := by
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h1, mul_inv_cancel_right]
      have h3 : (γ'.1 : G)⁻¹ * γ.1 = 1 :=
        disj _ (N.mul_mem (N.inv_mem γ'.1.2) γ.1.2) (h2 ▸ M.mul_mem δ'.1.2 (M.inv_mem δ.1.2))
      have h4 : (γ'.1 : G) = γ.1 := inv_mul_eq_one.1 h3
      have h5 : (δ.1 : G) = δ'.1 := by rw [h4] at h1; exact mul_left_cancel h1
      exact Prod.ext (Subtype.ext (Subtype.ext h5)) (Subtype.ext (Subtype.ext h4.symm))
    · rintro ⟨l, hl⟩
      obtain ⟨u, hu, m, hm, hu', hm', e⟩ := dec l hl
      exact ⟨(⟨⟨m, hm⟩, hm'⟩, ⟨⟨u, hu⟩, hu'⟩), Subtype.ext e.symm⟩
  rw [← ENNReal.tsum_prod, ← (Equiv.ofBijective p hb).tsum_eq]
  rfl

/- English proof (translation)
Introduce `G _ _ _ _ _ _ _ _ N M Λ _ ν π DN DM S μ D hμ hD φ hφ`. Use `haveI := countable_subgroupOf_of_countable Λ M`. Use `haveI := countable_subgroupOf_of_countable Λ N`. Use `haveI : LocallyCompactSpace N := S.closedN.isClosedEmbedding_subtypeVal.locallyCompactSpace`. Use `haveI : LocallyCompactSpace M := S.closedM.isClosedEmbedding_subtypeVal.locallyCompactSpace`.

Use `haveI := S.haarN`. Use `haveI := S.haarM`. Establish `hN` using `(GlobalTheory.T.unimodular_and_lintegral_unfold_of_lattice N ν (Λ.subgroupOf N) DN S.haarN S.domN S.finN).2`. Establish `hM` using `(GlobalTheory.T.unimodular_and_lintegral_unfold_of_lattice M π (Λ.subgroupOf M) DM S.haarM S.domM S.finM).2`. Establish `hC` using `GlobalTheory.T.lintegral_conj_eq_of_semidirectLatticeDatum G N M Λ ν π DN DM S`.

Establish `A : ∀ x : G, ∫⁻ m : M, ∫⁻ u : N, φ (u * m * x) ∂ν ∂π = ∫⁻ b in DM, ∫⁻ c in DN, ∑' l : Λ, φ ((b : G)⁻¹ * (c : G)⁻¹ * (l * x)) ∂ν ∂π`. Introduce `x`. Rewrite using `[hM _ (Measurable.lintegral_prod_right' (f := fun z : M × N => φ (z.2 * z.1 * x)) (hφ.comp (by fun_prop)))]`. Use `lintegral_congr fun b => ?_` and prove the remaining obligations. Establish `h1 : ∀ δ : Λ.subgroupOf M, ∫⁻ u : N, φ (u * ((b⁻¹ * δ : M) : G) * x) ∂ν = ∫⁻ c in DN, ∑' γ : Λ.subgroupOf N, φ ((b : G)⁻¹ * (c : G)⁻¹ * ((γ.1 : G) * (δ.1 : G) * x)) ∂ν`.

Introduce `δ`. Establish `h2` using `hC b b.2 (fun g => φ ((b : G)⁻¹ * g * δ.1 * x)) (hφ.comp (by fun_prop))`. Establish `h3` using `hN (fun u : N => φ ((b : G)⁻¹ * u * δ.1 * x)) (hφ.comp (by fun_prop))`. Simplify using `only [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc, inv_mul_cancel_left] at h2 h3 ⊢`. Rewrite using `[h2, h3]`.

Simplify using `only [h1]`. Rewrite using `[← lintegral_tsum]`. Use `swap`. Conclude with `fun δ => (Measurable.ennreal_tsum fun γ => hφ.comp (by fun_prop)).aemeasurable`. Use `lintegral_congr fun c => ?_` and prove the remaining obligations.

Conclude with `tsum_split_lattice N M Λ S.disj S.dec fun g => φ ((b : G)⁻¹ * (c : G)⁻¹ * (g * x))`. Simplify using `only [A]`. Establish `B : ∀ y : G, ∫⁻ x in D, ∑' l : Λ, φ (y * (l * x)) ∂μ = ∫⁻ x, φ x ∂μ`. Introduce `y`. Rewrite using `[lintegral_tsum, ← lintegral_mul_left_eq_self φ y, hD.lintegral_eq_tsum'' fun x => φ (y * x)]`.

Both sides reduce to the same expression. Conclude with `fun l => (hφ.comp (by fun_prop)).aemeasurable`. Rewrite using `[lintegral_lintegral_swap (Measurable.aemeasurable (Measurable.lintegral_prod_right' (f := fun z : (G × M) × N => ∑' l : Λ, φ ((z.1.2 : G)⁻¹ * (z.2 : G)⁻¹ * (l * z.1.1))) (Measurable.ennreal_tsum fun γ => hφ.comp (by fun_prop))))]`. Establish `C : ∀ b : M, ∫⁻ x in D, ∫⁻ c in DN, ∑' l : Λ, φ ((b : G)⁻¹ * (c : G)⁻¹ * (l * x)) ∂ν ∂μ = ν DN * ∫⁻ x, φ x ∂μ`. Introduce `b`.

Rewrite using `[lintegral_lintegral_swap (Measurable.aemeasurable (f := fun z : G × N => ∑' l : Λ, φ ((b : G)⁻¹ * (z.2 : G)⁻¹ * (l * z.1))) (Measurable.ennreal_tsum fun γ => hφ.comp (by fun_prop)))]`. Simplify using `only [B]`. Rewrite using `[setLIntegral_const, mul_comm]`. Simplify using `only [C]`. Rewrite using `[setLIntegral_const]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem lintegral_two_step_unfolding : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (N M Λ : Subgroup G) [Countable Λ] (ν : Measure N) (π : Measure M) (DN : Set N) (DM : Set M), SemiLat N M Λ ν π DN DM → ∀ (μ : Measure G) (D : Set G), μ.IsHaarMeasure → IsFundamentalDomain Λ D μ → ∀ φ : G → ℝ≥0∞, Measurable φ → ∫⁻ x in D, ∫⁻ m : M, ∫⁻ u : N, φ (u * m * x) ∂ν ∂π ∂μ = ν DN * π DM * ∫⁻ x, φ x ∂μ := by
  intro G _ _ _ _ _ _ _ _ N M Λ _ ν π DN DM S μ D hμ hD φ hφ
  haveI := countable_subgroupOf_of_countable Λ M
  haveI := countable_subgroupOf_of_countable Λ N
  haveI : LocallyCompactSpace N := S.closedN.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : LocallyCompactSpace M := S.closedM.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI := S.haarN
  haveI := S.haarM
  have hN := (GlobalTheory.T.unimodular_and_lintegral_unfold_of_lattice N ν (Λ.subgroupOf N) DN S.haarN S.domN S.finN).2
  have hM := (GlobalTheory.T.unimodular_and_lintegral_unfold_of_lattice M π (Λ.subgroupOf M) DM S.haarM S.domM S.finM).2
  have hC := GlobalTheory.T.lintegral_conj_eq_of_semidirectLatticeDatum G N M Λ ν π DN DM S
  have A : ∀ x : G, ∫⁻ m : M, ∫⁻ u : N, φ (u * m * x) ∂ν ∂π =
      ∫⁻ b in DM, ∫⁻ c in DN, ∑' l : Λ, φ ((b : G)⁻¹ * (c : G)⁻¹ * (l * x)) ∂ν ∂π := by
    intro x
    rw [hM _ (Measurable.lintegral_prod_right' (f := fun z : M × N => φ (z.2 * z.1 * x)) (hφ.comp (by fun_prop)))]
    refine lintegral_congr fun b => ?_
    have h1 : ∀ δ : Λ.subgroupOf M, ∫⁻ u : N, φ (u * ((b⁻¹ * δ : M) : G) * x) ∂ν =
        ∫⁻ c in DN, ∑' γ : Λ.subgroupOf N, φ ((b : G)⁻¹ * (c : G)⁻¹ * ((γ.1 : G) * (δ.1 : G) * x)) ∂ν := by
      intro δ
      have h2 := hC b b.2 (fun g => φ ((b : G)⁻¹ * g * δ.1 * x)) (hφ.comp (by fun_prop))
      have h3 := hN (fun u : N => φ ((b : G)⁻¹ * u * δ.1 * x)) (hφ.comp (by fun_prop))
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc, inv_mul_cancel_left] at h2 h3 ⊢
      rw [h2, h3]
    simp only [h1]
    rw [← lintegral_tsum]
    swap
    · exact fun δ => (Measurable.ennreal_tsum fun γ => hφ.comp (by fun_prop)).aemeasurable
    refine lintegral_congr fun c => ?_
    exact tsum_split_lattice N M Λ S.disj S.dec fun g => φ ((b : G)⁻¹ * (c : G)⁻¹ * (g * x))
  simp only [A]
  have B : ∀ y : G, ∫⁻ x in D, ∑' l : Λ, φ (y * (l * x)) ∂μ = ∫⁻ x, φ x ∂μ := by
    intro y
    rw [lintegral_tsum, ← lintegral_mul_left_eq_self φ y,
      hD.lintegral_eq_tsum'' fun x => φ (y * x)]
    · rfl
    · exact fun l => (hφ.comp (by fun_prop)).aemeasurable
  rw [lintegral_lintegral_swap (Measurable.aemeasurable (Measurable.lintegral_prod_right'
    (f := fun z : (G × M) × N => ∑' l : Λ, φ ((z.1.2 : G)⁻¹ * (z.2 : G)⁻¹ * (l * z.1.1)))
    (Measurable.ennreal_tsum fun γ => hφ.comp (by fun_prop))))]
  have C : ∀ b : M, ∫⁻ x in D, ∫⁻ c in DN, ∑' l : Λ, φ ((b : G)⁻¹ * (c : G)⁻¹ * (l * x)) ∂ν ∂μ =
      ν DN * ∫⁻ x, φ x ∂μ := by
    intro b
    rw [lintegral_lintegral_swap (Measurable.aemeasurable
      (f := fun z : G × N => ∑' l : Λ, φ ((b : G)⁻¹ * (z.2 : G)⁻¹ * (l * z.1)))
      (Measurable.ennreal_tsum fun γ => hφ.comp (by fun_prop)))]
    simp only [B]
    rw [setLIntegral_const, mul_comm]
  simp only [C]
  rw [setLIntegral_const]
  ring

end GlobalTheory.ResLine
