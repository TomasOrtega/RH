import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.ProjRows
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RightRegularIsometricMultiplicative

noncomputable section

namespace Formalism.L2.SG.Pf

open MeasureTheory Set Filter Topology NumberField
open scoped ENNReal InnerProductSpace symmDiff
open Formalism.MainNotions.S Formalism.MainNotions.LeviCoordinates

section Abs

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
  {μ : Measure G} {Γ : Subgroup G} {D : Set G}

def RPres (μ : Measure G) (g : G) : Prop := MeasurePreserving (fun x => x * g) μ μ

/- English proof (translation)
Establish `h' : MeasurePreserving (MeasurableEquiv.mulRight g) μ μ` using `hg`. Conclude with `h'.measure_preimage_equiv s`.
-/
theorem rp_pre {g : G} (hg : RPres μ g) (s : Set G) : μ ((fun x => x * g) ⁻¹' s) = μ s := by
  have h' : MeasurePreserving (MeasurableEquiv.mulRight g) μ μ := hg
  exact h'.measure_preimage_equiv s

/- English proof (translation)
Rewrite using `[rp_pre hg]`. Establish `key : ∀ γ₁ ∈ Γ, ∀ γ₂ ∈ Γ, γ₁ ≠ γ₂ → μ {y | γ₁ * y ∈ D ∧ γ₂ * y ∈ D} = 0`. Introduce `γ₁ h₁ γ₂ h₂ hne`. Establish `hγ : γ₁ * γ₂⁻¹ ∈ (Γ : Set G)` using `Γ.mul_mem h₁ (Γ.inv_mem h₂)`. Establish `hne' : γ₁ * γ₂⁻¹ ≠ 1` using `fun h1 => hne (mul_inv_eq_one.mp h1)`.

Establish `h0` using `h.disj _ hγ hne'`. Establish `hsub : {y | γ₁ * y ∈ D ∧ γ₂ * y ∈ D} ⊆ (fun y => γ₁ * y) ⁻¹' ((fun z => γ₁ * γ₂⁻¹ * z) '' D ∩ D)`. Introduce and unpack `y ⟨hy1, hy2⟩`. Conclude with `⟨⟨γ₂ * y, hy2, by simp [mul_assoc]⟩, hy1⟩`. Use `measure_mono_null hsub ?_` and prove the remaining obligations.

Rewrite using `[measure_preimage_mul]`. Conclude with `h0`. Establish `hN : rr_N Γ D ⊆ ⋃ (p : Γ × Γ) (_ : p.1 ≠ p.2), {y | (p.1 : G) * y ∈ D ∧ (p.2 : G) * y ∈ D}`. Introduce `y hy`. Simplify using `only [rr_N, Set.mem_setOf_eq] at hy`.

Take `⟨γ₁, h₁, γ₂, h₂, hne, hy1, hy2⟩` from `hy`. Conclude with `Set.mem_iUnion₂.mpr ⟨(⟨γ₁, h₁⟩, ⟨γ₂, h₂⟩), fun heq => hne (congrArg Subtype.val heq), hy1, hy2⟩`. Use `measure_mono_null hN ?_` and prove the remaining obligations. Conclude with `measure_iUnion_null fun p => measure_iUnion_null fun hp => key p.1 p.1.2 p.2 p.2.2 (fun heq => hp (Subtype.ext heq))`.
-/
theorem rp_N_pre [μ.IsMulLeftInvariant] [Countable Γ] (h : rr_FD μ Γ D) {g : G} (hg : RPres μ g) :
    μ ((fun x => x * g) ⁻¹' rr_N Γ D) = 0 := by
  rw [rp_pre hg]
  have key : ∀ γ₁ ∈ Γ, ∀ γ₂ ∈ Γ, γ₁ ≠ γ₂ → μ {y | γ₁ * y ∈ D ∧ γ₂ * y ∈ D} = 0 := by
    intro γ₁ h₁ γ₂ h₂ hne
    have hγ : γ₁ * γ₂⁻¹ ∈ (Γ : Set G) := Γ.mul_mem h₁ (Γ.inv_mem h₂)
    have hne' : γ₁ * γ₂⁻¹ ≠ 1 := fun h1 => hne (mul_inv_eq_one.mp h1)
    have h0 := h.disj _ hγ hne'
    have hsub : {y | γ₁ * y ∈ D ∧ γ₂ * y ∈ D} ⊆
        (fun y => γ₁ * y) ⁻¹' ((fun z => γ₁ * γ₂⁻¹ * z) '' D ∩ D) := by
      rintro y ⟨hy1, hy2⟩
      exact ⟨⟨γ₂ * y, hy2, by simp [mul_assoc]⟩, hy1⟩
    refine measure_mono_null hsub ?_
    rw [measure_preimage_mul]
    exact h0
  have hN : rr_N Γ D ⊆ ⋃ (p : Γ × Γ) (_ : p.1 ≠ p.2), {y | (p.1 : G) * y ∈ D ∧ (p.2 : G) * y ∈ D} := by
    intro y hy
    simp only [rr_N, Set.mem_setOf_eq] at hy
    obtain ⟨γ₁, h₁, γ₂, h₂, hne, hy1, hy2⟩ := hy
    exact Set.mem_iUnion₂.mpr ⟨(⟨γ₁, h₁⟩, ⟨γ₂, h₂⟩), fun heq => hne (congrArg Subtype.val heq), hy1, hy2⟩
  refine measure_mono_null hN ?_
  exact measure_iUnion_null fun p => measure_iUnion_null fun hp =>
    key p.1 p.1.2 p.2 p.2.2 (fun heq => hp (Subtype.ext heq))

/- English proof (translation)
Establish `hnull` using `rp_N_pre h hg`. Rewrite using `[ae_iff]`. Use `measure_mono_null (fun x hx => ?_) hnull` and prove the remaining obligations. Simplify using `only [Set.mem_setOf_eq] at hx`. Use `show x * g ∈ rr_N Γ D`.

Establish `hex : ∃ γ ∈ (Γ : Set G), γ * (x * g) ∈ D` using `h.cov (x * g)`. Take `⟨γ, hγ, hr', hD⟩` from `hr (x * g)`. Establish `e : rr_rep (Γ : Set G) D (x * g) = hex.choose * (x * g)`. Unfold `rr_rep`. Use `first`.

Consider the case `exact dif_pos hex`. Consider the case `rw [dif_pos hex]`. Consider the case `simp only [dif_pos hex]`. Rewrite `hx` using `[e, hr']`. Use `show ∃ γ₁ ∈ Γ, ∃ γ₂ ∈ Γ, γ₁ ≠ γ₂ ∧ γ₁ * (x * g) ∈ D ∧ γ₂ * (x * g) ∈ D`.

Conclude with `⟨hex.choose, hex.choose_spec.1, γ, hγ, fun heq => hx (by rw [heq]), hex.choose_spec.2, hD⟩`.
-/
theorem rp_rep_ae_eq [μ.IsMulLeftInvariant] [Countable Γ] (h : rr_FD μ Γ D) {r : G → G}
    (hr : ∀ y, ∃ γ ∈ Γ, r y = γ * y ∧ γ * y ∈ D) {g : G} (hg : RPres μ g) :
    ∀ᵐ x ∂μ, rr_rep (Γ : Set G) D (x * g) = r (x * g) := by
  classical
  have hnull := rp_N_pre h hg
  rw [ae_iff]
  refine measure_mono_null (fun x hx => ?_) hnull
  simp only [Set.mem_setOf_eq] at hx
  show x * g ∈ rr_N Γ D
  have hex : ∃ γ ∈ (Γ : Set G), γ * (x * g) ∈ D := h.cov (x * g)
  obtain ⟨γ, hγ, hr', hD⟩ := hr (x * g)
  have e : rr_rep (Γ : Set G) D (x * g) = hex.choose * (x * g) := by
    unfold rr_rep
    first
    | exact dif_pos hex
    | rw [dif_pos hex]
    | simp only [dif_pos hex]
  rw [e, hr'] at hx
  show ∃ γ₁ ∈ Γ, ∃ γ₂ ∈ Γ, γ₁ ≠ γ₂ ∧ γ₁ * (x * g) ∈ D ∧ γ₂ * (x * g) ∈ D
  exact ⟨hex.choose, hex.choose_spec.1, γ, hγ, fun heq => hx (by rw [heq]), hex.choose_spec.2, hD⟩

/- English proof (translation)
Use `set B : Γ → Set G := fun γ => D ∩ (fun x => (γ : G) * x * g) ⁻¹' (D ∩ A) with hB`. Use `set C : Γ → Set G := fun γ => (D ∩ A) ∩ (fun z => (γ : G)⁻¹ * z * g⁻¹) ⁻¹' D with hC`. Establish `hBm : ∀ γ, MeasurableSet (B γ)` using `fun γ => by`. Rewrite using `[hB]`. Conclude with `h.meas.inter ((h.meas.inter hA).preimage ((measurable_const_mul (γ : G)).mul_const g))`.

Establish `hCm : ∀ γ, MeasurableSet (C γ)` using `fun γ => by`. Rewrite using `[hC]`. Conclude with `(h.meas.inter hA).inter (h.meas.preimage ((measurable_const_mul ((γ : G)⁻¹)).mul_const g⁻¹))`. Establish `hBC : ∀ γ : Γ, μ (B γ) = μ (C γ)`. Introduce `γ`.

Establish `hset : B γ = (fun x => x * g) ⁻¹' ((fun y => (γ : G) * y) ⁻¹' C γ)`. Use extensionality with `x`. Simplify using `only [hB, hC, Set.mem_inter_iff, Set.mem_preimage]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hx, h1, h2⟩`.

Use `⟨⟨by simpa [mul_assoc] using h1, by simpa [mul_assoc] using h2⟩, ?_⟩` and prove the remaining obligations. Simplify `hx` using `[mul_assoc]`. Introduce and unpack `⟨⟨h1, h2⟩, h3⟩`. Use `⟨by simpa [mul_assoc] using h3, by simpa [mul_assoc] using h1, by simpa [mul_assoc] using h2⟩` and prove the remaining obligations. Rewrite using `[hset, rp_pre hg, measure_preimage_mul]`.

Establish `hCU : (⋃ γ : Γ, C γ) = A ∩ D`. Use extensionality with `z`. Simplify using `only [hC, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨γ, ⟨hz1, hz2⟩, -⟩`.

Conclude with `⟨hz2, hz1⟩`. Introduce and unpack `⟨hz2, hz1⟩`. Take `⟨γ', hγ', hy⟩` from `h.cov (z * g⁻¹)`. Use `⟨⟨γ'⁻¹, Γ.inv_mem hγ'⟩, ⟨hz1, hz2⟩, ?_⟩` and prove the remaining obligations. Simplify `hy` using `[mul_assoc]`.

Establish `hCd : Pairwise (fun γ γ' : Γ => AEDisjoint μ (C γ) (C γ'))`. Introduce `γ γ' hne`. Use `measure_mono_null ?_ (rp_N_pre h hgi)` and prove the remaining obligations. Introduce `z hz`. Simplify using `only [hC, Set.mem_inter_iff, Set.mem_preimage] at hz`.

Take `⟨⟨-, h1⟩, ⟨-, h2⟩⟩` from `hz`. Use `show ∃ γ₁ ∈ Γ, ∃ γ₂ ∈ Γ, γ₁ ≠ γ₂ ∧ γ₁ * (z * g⁻¹) ∈ D ∧ γ₂ * (z * g⁻¹) ∈ D`. Use `⟨(γ : G)⁻¹, Γ.inv_mem γ.2, (γ' : G)⁻¹, Γ.inv_mem γ'.2, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `heq`. Conclude with `hne (Subtype.ext (inv_injective heq))`.

Simplify `h1` using `[mul_assoc]`. Simplify `h2` using `[mul_assoc]`. Establish `hBd : Pairwise (fun γ γ' : Γ => AEDisjoint μ (B γ) (B γ'))`. Introduce `γ γ' hne`. Use `measure_mono_null ?_ (rp_N_pre h hg)` and prove the remaining obligations.

Introduce `x hx`. Simplify using `only [hB, Set.mem_inter_iff, Set.mem_preimage] at hx`. Take `⟨⟨-, h1, -⟩, -, h2, -⟩` from `hx`. Use `show ∃ γ₁ ∈ Γ, ∃ γ₂ ∈ Γ, γ₁ ≠ γ₂ ∧ γ₁ * (x * g) ∈ D ∧ γ₂ * (x * g) ∈ D`. Use `⟨γ, γ.2, γ', γ'.2, fun heq => hne (Subtype.ext heq), ?_, ?_⟩` and prove the remaining obligations.

Simplify `h1` using `[mul_assoc]`. Simplify `h2` using `[mul_assoc]`. Establish `hΦ : ((fun x => r (x * g)) ⁻¹' A ∩ D : Set G) =ᵐ[μ] (⋃ γ : Γ, B γ)`. Rewrite using `[Filter.eventuallyEq_set]`. Use `filter_upwards [compl_mem_ae_iff.mpr (rp_N_pre h hg)] with x hx`.

Establish `hx' : ¬ ∃ γ₁ ∈ Γ, ∃ γ₂ ∈ Γ, γ₁ ≠ γ₂ ∧ γ₁ * (x * g) ∈ D ∧ γ₂ * (x * g) ∈ D` using `hx`. Take `⟨γ₀, hγ₀, hr0, hD0⟩` from `hr (x * g)`. Simplify using `only [hB, Set.mem_inter_iff, Set.mem_preimage, Set.mem_iUnion]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hxA, hxD⟩`.

Use `⟨⟨γ₀, hγ₀⟩, hxD, ?_, ?_⟩` and prove the remaining obligations. Simplify `hD0` using `[mul_assoc]`. Rewrite `hxA` using `[hr0]`. Simplify `hxA` using `[mul_assoc]`. Introduce and unpack `⟨γ, hxD, h1, h2⟩`.

Use `⟨?_, hxD⟩` and prove the remaining obligations. Establish `hγ : (γ : G) = γ₀`. Assume the negation of the conclusion as `hne`. Conclude with `hx' ⟨(γ : G), γ.2, γ₀, hγ₀, hne, by simpa [mul_assoc] using h1, hD0⟩`. Rewrite using `[hr0, ← hγ]`.

Simplify `h2` using `[mul_assoc]`. Rewrite using `[measure_congr hΦ, measure_iUnion₀ hBd (fun γ => (hBm γ).nullMeasurableSet), ← hCU, measure_iUnion₀ hCd (fun γ => (hCm γ).nullMeasurableSet)]`. Conclude with `tsum_congr hBC`.
-/
theorem rp_meas_pre [μ.IsMulLeftInvariant] [Countable Γ] (h : rr_FD μ Γ D) {r : G → G}
    (hr : ∀ y, ∃ γ ∈ Γ, r y = γ * y ∧ γ * y ∈ D) {g : G} (hg : RPres μ g) (hgi : RPres μ g⁻¹)
    {A : Set G} (hA : MeasurableSet A) :
    μ ((fun x => r (x * g)) ⁻¹' A ∩ D) = μ (A ∩ D) := by
  classical
  set B : Γ → Set G := fun γ => D ∩ (fun x => (γ : G) * x * g) ⁻¹' (D ∩ A) with hB
  set C : Γ → Set G := fun γ => (D ∩ A) ∩ (fun z => (γ : G)⁻¹ * z * g⁻¹) ⁻¹' D with hC
  have hBm : ∀ γ, MeasurableSet (B γ) := fun γ => by
    rw [hB]
    exact h.meas.inter ((h.meas.inter hA).preimage ((measurable_const_mul (γ : G)).mul_const g))
  have hCm : ∀ γ, MeasurableSet (C γ) := fun γ => by
    rw [hC]
    exact (h.meas.inter hA).inter (h.meas.preimage ((measurable_const_mul ((γ : G)⁻¹)).mul_const g⁻¹))
  have hBC : ∀ γ : Γ, μ (B γ) = μ (C γ) := by
    intro γ
    have hset : B γ = (fun x => x * g) ⁻¹' ((fun y => (γ : G) * y) ⁻¹' C γ) := by
      ext x
      simp only [hB, hC, Set.mem_inter_iff, Set.mem_preimage]
      constructor
      · rintro ⟨hx, h1, h2⟩
        refine ⟨⟨by simpa [mul_assoc] using h1, by simpa [mul_assoc] using h2⟩, ?_⟩
        simpa [mul_assoc] using hx
      · rintro ⟨⟨h1, h2⟩, h3⟩
        refine ⟨by simpa [mul_assoc] using h3, by simpa [mul_assoc] using h1,
          by simpa [mul_assoc] using h2⟩
    rw [hset, rp_pre hg, measure_preimage_mul]
  have hCU : (⋃ γ : Γ, C γ) = A ∩ D := by
    ext z
    simp only [hC, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage]
    constructor
    · rintro ⟨γ, ⟨hz1, hz2⟩, -⟩
      exact ⟨hz2, hz1⟩
    · rintro ⟨hz2, hz1⟩
      obtain ⟨γ', hγ', hy⟩ := h.cov (z * g⁻¹)
      refine ⟨⟨γ'⁻¹, Γ.inv_mem hγ'⟩, ⟨hz1, hz2⟩, ?_⟩
      simpa [mul_assoc] using hy
  have hCd : Pairwise (fun γ γ' : Γ => AEDisjoint μ (C γ) (C γ')) := by
    intro γ γ' hne
    refine measure_mono_null ?_ (rp_N_pre h hgi)
    intro z hz
    simp only [hC, Set.mem_inter_iff, Set.mem_preimage] at hz
    obtain ⟨⟨-, h1⟩, ⟨-, h2⟩⟩ := hz
    show ∃ γ₁ ∈ Γ, ∃ γ₂ ∈ Γ, γ₁ ≠ γ₂ ∧ γ₁ * (z * g⁻¹) ∈ D ∧ γ₂ * (z * g⁻¹) ∈ D
    refine ⟨(γ : G)⁻¹, Γ.inv_mem γ.2, (γ' : G)⁻¹, Γ.inv_mem γ'.2, ?_, ?_, ?_⟩
    · intro heq
      exact hne (Subtype.ext (inv_injective heq))
    · simpa [mul_assoc] using h1
    · simpa [mul_assoc] using h2
  have hBd : Pairwise (fun γ γ' : Γ => AEDisjoint μ (B γ) (B γ')) := by
    intro γ γ' hne
    refine measure_mono_null ?_ (rp_N_pre h hg)
    intro x hx
    simp only [hB, Set.mem_inter_iff, Set.mem_preimage] at hx
    obtain ⟨⟨-, h1, -⟩, -, h2, -⟩ := hx
    show ∃ γ₁ ∈ Γ, ∃ γ₂ ∈ Γ, γ₁ ≠ γ₂ ∧ γ₁ * (x * g) ∈ D ∧ γ₂ * (x * g) ∈ D
    refine ⟨γ, γ.2, γ', γ'.2, fun heq => hne (Subtype.ext heq), ?_, ?_⟩
    · simpa [mul_assoc] using h1
    · simpa [mul_assoc] using h2
  have hΦ : ((fun x => r (x * g)) ⁻¹' A ∩ D : Set G) =ᵐ[μ] (⋃ γ : Γ, B γ) := by
    rw [Filter.eventuallyEq_set]
    filter_upwards [compl_mem_ae_iff.mpr (rp_N_pre h hg)] with x hx
    have hx' : ¬ ∃ γ₁ ∈ Γ, ∃ γ₂ ∈ Γ, γ₁ ≠ γ₂ ∧ γ₁ * (x * g) ∈ D ∧ γ₂ * (x * g) ∈ D := hx
    obtain ⟨γ₀, hγ₀, hr0, hD0⟩ := hr (x * g)
    simp only [hB, Set.mem_inter_iff, Set.mem_preimage, Set.mem_iUnion]
    constructor
    · rintro ⟨hxA, hxD⟩
      refine ⟨⟨γ₀, hγ₀⟩, hxD, ?_, ?_⟩
      · simpa [mul_assoc] using hD0
      · rw [hr0] at hxA
        simpa [mul_assoc] using hxA
    · rintro ⟨γ, hxD, h1, h2⟩
      refine ⟨?_, hxD⟩
      have hγ : (γ : G) = γ₀ := by
        by_contra hne
        exact hx' ⟨(γ : G), γ.2, γ₀, hγ₀, hne, by simpa [mul_assoc] using h1, hD0⟩
      rw [hr0, ← hγ]
      simpa [mul_assoc] using h2
  rw [measure_congr hΦ, measure_iUnion₀ hBd (fun γ => (hBm γ).nullMeasurableSet), ← hCU,
    measure_iUnion₀ hCd (fun γ => (hCm γ).nullMeasurableSet)]
  exact tsum_congr hBC

/- English proof (translation)
Establish `hrep : ∀ y : G, ∃ γ ∈ Γ, rr_rep (Γ : Set G) D y = γ * y ∧ γ * y ∈ D`. Introduce `y`. Establish `hex : ∃ γ ∈ (Γ : Set G), γ * y ∈ D` using `h.cov y`. Use `⟨hex.choose, hex.choose_spec.1, ?_, hex.choose_spec.2⟩` and prove the remaining obligations. Unfold `rr_rep`.

Use `first`. Consider the case `exact dif_pos hex`. Consider the case `rw [dif_pos hex]`. Consider the case `simp only [dif_pos hex]`. Use `haveI : Nonempty Γ := ⟨1⟩`.

Take `⟨e, he⟩` from `exists_surjective_nat Γ`. Establish `hp : ∀ y : G, ∃ n, (e n : G) * y ∈ D` using `fun y => by`. Take `⟨γ, hγ, hy⟩` from `h.cov y`. Take `⟨n, hn⟩` from `he ⟨γ, hγ⟩`. Conclude with `⟨n, by rw [hn]; exact hy⟩`.

Establish `hrm : Measurable fun y : G => (e (Nat.find (hp y)) : G) * y` using `Measurable.find (f := fun n y => (e n : G) * y) (p := fun n y => (e n : G) * y ∈ D) (fun n => measurable_const_mul _) (fun n => h.meas.preimage (measurable_const_mul _)) hp`. Establish `hr : ∀ y, ∃ γ ∈ Γ, (e (Nat.find (hp y)) : G) * y = γ * y ∧ γ * y ∈ D` using `fun y => ⟨_, (e (Nat.find (hp y))).2, rfl, Nat.find_spec (hp y)⟩`. Establish `hae : (fun x => rr_rep (Γ : Set G) D (x * g)) =ᵐ[μ.restrict D] fun x => (e (Nat.find (hp (x * g))) : G) * (x * g)` using `ae_restrict_of_ae (rp_rep_ae_eq h hr hg)`. Establish `hmeas : AEMeasurable (fun x => rr_rep (Γ : Set G) D (x * g)) (μ.restrict D)` using `((hrm.comp (measurable_mul_const g)).aemeasurable).congr hae.symm`. Use `⟨hmeas, ?_⟩` and prove the remaining obligations.

Use extensionality with `A hA`. Rewrite using `[Measure.map_apply_of_aemeasurable hmeas hA, Measure.restrict_apply' h.meas, Measure.restrict_apply' h.meas]`. Conclude with `rp_meas_pre h hrep hg hgi hA`.
-/
theorem rp_map [μ.IsMulLeftInvariant] [Countable Γ] (h : rr_FD μ Γ D) {g : G} (hg : RPres μ g)
    (hgi : RPres μ g⁻¹) :
    AEMeasurable (fun x => rr_rep (Γ : Set G) D (x * g)) (μ.restrict D) ∧
      Measure.map (fun x => rr_rep (Γ : Set G) D (x * g)) (μ.restrict D) = μ.restrict D := by
  classical
  have hrep : ∀ y : G, ∃ γ ∈ Γ, rr_rep (Γ : Set G) D y = γ * y ∧ γ * y ∈ D := by
    intro y
    have hex : ∃ γ ∈ (Γ : Set G), γ * y ∈ D := h.cov y
    refine ⟨hex.choose, hex.choose_spec.1, ?_, hex.choose_spec.2⟩
    unfold rr_rep
    first
    | exact dif_pos hex
    | rw [dif_pos hex]
    | simp only [dif_pos hex]
  haveI : Nonempty Γ := ⟨1⟩
  obtain ⟨e, he⟩ := exists_surjective_nat Γ
  have hp : ∀ y : G, ∃ n, (e n : G) * y ∈ D := fun y => by
    obtain ⟨γ, hγ, hy⟩ := h.cov y
    obtain ⟨n, hn⟩ := he ⟨γ, hγ⟩
    exact ⟨n, by rw [hn]; exact hy⟩
  have hrm : Measurable fun y : G => (e (Nat.find (hp y)) : G) * y :=
    Measurable.find (f := fun n y => (e n : G) * y) (p := fun n y => (e n : G) * y ∈ D)
      (fun n => measurable_const_mul _) (fun n => h.meas.preimage (measurable_const_mul _)) hp
  have hr : ∀ y, ∃ γ ∈ Γ, (e (Nat.find (hp y)) : G) * y = γ * y ∧ γ * y ∈ D :=
    fun y => ⟨_, (e (Nat.find (hp y))).2, rfl, Nat.find_spec (hp y)⟩
  have hae : (fun x => rr_rep (Γ : Set G) D (x * g)) =ᵐ[μ.restrict D]
      fun x => (e (Nat.find (hp (x * g))) : G) * (x * g) :=
    ae_restrict_of_ae (rp_rep_ae_eq h hr hg)
  have hmeas : AEMeasurable (fun x => rr_rep (Γ : Set G) D (x * g)) (μ.restrict D) :=
    ((hrm.comp (measurable_mul_const g)).aemeasurable).congr hae.symm
  refine ⟨hmeas, ?_⟩
  ext A hA
  rw [Measure.map_apply_of_aemeasurable hmeas hA, Measure.restrict_apply' h.meas,
    Measure.restrict_apply' h.meas]
  exact rp_meas_pre h hrep hg hgi hA

/- English proof (translation)
Establish `hnull` using `rp_N_pre h hgk`. Establish `hc : ∀ y : G, ∃ c ∈ (Γ : Set G), rr_rep (Γ : Set G) D y = c * y ∧ c * y ∈ D`. Introduce `y`. Establish `hex : ∃ γ ∈ (Γ : Set G), γ * y ∈ D` using `h.cov y`. Use `⟨hex.choose, hex.choose_spec.1, ?_, hex.choose_spec.2⟩` and prove the remaining obligations.

Unfold `rr_rep`. Use `first`. Consider the case `exact dif_pos hex`. Consider the case `rw [dif_pos hex]`. Consider the case `simp only [dif_pos hex]`.

Rewrite using `[ae_iff]`. Use `measure_mono_null (fun x hx => ?_) hnull` and prove the remaining obligations. Simplify using `only [Set.mem_setOf_eq] at hx`. Take `⟨c₁, hc₁, e₁, -⟩` from `hc (x * g)`. Take `⟨c₂, hc₂, e₂, d₂⟩` from `hc (rr_rep (Γ : Set G) D (x * g) * k)`.

Take `⟨c₃, hc₃, e₃, d₃⟩` from `hc (x * (g * k))`. Rewrite `hx` using `[e₂, e₃]`. Rewrite `d₂`, `hx` using `[e₁]`. Use `show ∃ γ₁ ∈ Γ, ∃ γ₂ ∈ Γ, γ₁ ≠ γ₂ ∧ γ₁ * (x * (g * k)) ∈ D ∧ γ₂ * (x * (g * k)) ∈ D`. Use `⟨c₂ * c₁, Γ.mul_mem hc₂ hc₁, c₃, hc₃, ?_, ?_, d₃⟩` and prove the remaining obligations.

Introduce `heq`. Apply `hx` to reduce the goal to its premises. Rewrite using `[← heq]`. Simplify using `only [mul_assoc]`. Simplify `d₂` using `only [mul_assoc]`.
-/
theorem rp_rep_comp [μ.IsMulLeftInvariant] [Countable Γ] (h : rr_FD μ Γ D) (g k : G)
    (hgk : RPres μ (g * k)) :
    ∀ᵐ x ∂μ, rr_rep (Γ : Set G) D (rr_rep (Γ : Set G) D (x * g) * k) = rr_rep (Γ : Set G) D (x * (g * k)) := by
  classical
  have hnull := rp_N_pre h hgk
  have hc : ∀ y : G, ∃ c ∈ (Γ : Set G), rr_rep (Γ : Set G) D y = c * y ∧ c * y ∈ D := by
    intro y
    have hex : ∃ γ ∈ (Γ : Set G), γ * y ∈ D := h.cov y
    refine ⟨hex.choose, hex.choose_spec.1, ?_, hex.choose_spec.2⟩
    unfold rr_rep
    first
    | exact dif_pos hex
    | rw [dif_pos hex]
    | simp only [dif_pos hex]
  rw [ae_iff]
  refine measure_mono_null (fun x hx => ?_) hnull
  simp only [Set.mem_setOf_eq] at hx
  obtain ⟨c₁, hc₁, e₁, -⟩ := hc (x * g)
  obtain ⟨c₂, hc₂, e₂, d₂⟩ := hc (rr_rep (Γ : Set G) D (x * g) * k)
  obtain ⟨c₃, hc₃, e₃, d₃⟩ := hc (x * (g * k))
  rw [e₂, e₃] at hx
  rw [e₁] at d₂ hx
  show ∃ γ₁ ∈ Γ, ∃ γ₂ ∈ Γ, γ₁ ≠ γ₂ ∧ γ₁ * (x * (g * k)) ∈ D ∧ γ₂ * (x * (g * k)) ∈ D
  refine ⟨c₂ * c₁, Γ.mul_mem hc₂ hc₁, c₃, hc₃, ?_, ?_, d₃⟩
  · intro heq
    apply hx
    rw [← heq]
    simp only [mul_assoc]
  · simpa only [mul_assoc] using d₂

variable {R : G → (Lp ℂ 2 (μ.restrict D) →L[ℂ] Lp ℂ 2 (μ.restrict D))}

/- English proof (translation)
Take `⟨hmeas, hmap⟩` from `rp_map h hg hgi`. Establish `h1 : eLpNorm ((R g F : Lp ℂ 2 (μ.restrict D)) : G → ℂ) 2 (μ.restrict D) = eLpNorm (F : G → ℂ) 2 (μ.restrict D)`. Rewrite using `[eLpNorm_congr_ae (hR g F)]`. Establish `hF : AEStronglyMeasurable (F : G → ℂ) (Measure.map (fun x => rr_rep (Γ : Set G) D (x * g)) (μ.restrict D))`. Rewrite using `[hmap]`.

Conclude with `Lp.aestronglyMeasurable F`. Establish `key : eLpNorm (F : G → ℂ) 2 (Measure.map (fun x => rr_rep (Γ : Set G) D (x * g)) (μ.restrict D)) = eLpNorm ((F : G → ℂ) ∘ fun x => rr_rep (Γ : Set G) D (x * g)) 2 (μ.restrict D)` using `eLpNorm_map_measure hF hmeas`. Rewrite `key` using `[hmap]`. Conclude with `key.symm`. Rewrite using `[Lp.norm_def, Lp.norm_def, h1]`.
-/
theorem rp_norm [μ.IsMulLeftInvariant] [Countable Γ] (h : rr_FD μ Γ D)
    (hR : rr_IsReg μ Γ D R) {g : G} (hg : RPres μ g) (hgi : RPres μ g⁻¹) (F : Lp ℂ 2 (μ.restrict D)) :
    ‖R g F‖ = ‖F‖ := by
  obtain ⟨hmeas, hmap⟩ := rp_map h hg hgi
  have h1 : eLpNorm ((R g F : Lp ℂ 2 (μ.restrict D)) : G → ℂ) 2 (μ.restrict D)
      = eLpNorm (F : G → ℂ) 2 (μ.restrict D) := by
    rw [eLpNorm_congr_ae (hR g F)]
    have hF : AEStronglyMeasurable (F : G → ℂ)
        (Measure.map (fun x => rr_rep (Γ : Set G) D (x * g)) (μ.restrict D)) := by
      rw [hmap]
      exact Lp.aestronglyMeasurable F
    have key : eLpNorm (F : G → ℂ) 2 (Measure.map (fun x => rr_rep (Γ : Set G) D (x * g)) (μ.restrict D))
        = eLpNorm ((F : G → ℂ) ∘ fun x => rr_rep (Γ : Set G) D (x * g)) 2 (μ.restrict D) :=
      eLpNorm_map_measure hF hmeas
    rw [hmap] at key
    exact key.symm
  rw [Lp.norm_def, Lp.norm_def, h1]

/- English proof (translation)
Take `⟨hmeas, hmap⟩` from `rp_map h hg hgi`. Use `ext1 F`. Apply `Lp.ext` to reduce the goal to its premises. Establish `e1` using `hR (g * k) F`. Establish `e2` using `hR g (R k F)`.

Establish `e3 : ∀ᵐ x ∂(μ.restrict D), ((R k F : Lp ℂ 2 (μ.restrict D)) : G → ℂ) (rr_rep (Γ : Set G) D (x * g)) = (F : G → ℂ) (rr_rep (Γ : Set G) D (rr_rep (Γ : Set G) D (x * g) * k))` using `ae_of_ae_map (p := fun y => ((R k F : Lp ℂ 2 (μ.restrict D)) : G → ℂ) y = (F : G → ℂ) (rr_rep (Γ : Set G) D (y * k))) hmeas (by rw [hmap]; exact hR k F)`. Establish `e4 : ∀ᵐ x ∂(μ.restrict D), rr_rep (Γ : Set G) D (rr_rep (Γ : Set G) D (x * g) * k) = rr_rep (Γ : Set G) D (x * (g * k))` using `ae_restrict_of_ae (rp_rep_comp h g k hgk)`. Use `filter_upwards [e1, e2, e3, e4] with x h1 h2 h3 h4`. Rewrite using `[ContinuousLinearMap.comp_apply, h2, h3, h4, h1]`.
-/
theorem rp_mul [μ.IsMulLeftInvariant] [Countable Γ] (h : rr_FD μ Γ D)
    (hR : rr_IsReg μ Γ D R) {g k : G} (hg : RPres μ g) (hgi : RPres μ g⁻¹) (hgk : RPres μ (g * k)) :
    R (g * k) = R g ∘L R k := by
  obtain ⟨hmeas, hmap⟩ := rp_map h hg hgi
  ext1 F
  apply Lp.ext
  have e1 := hR (g * k) F
  have e2 := hR g (R k F)
  have e3 : ∀ᵐ x ∂(μ.restrict D), ((R k F : Lp ℂ 2 (μ.restrict D)) : G → ℂ) (rr_rep (Γ : Set G) D (x * g))
      = (F : G → ℂ) (rr_rep (Γ : Set G) D (rr_rep (Γ : Set G) D (x * g) * k)) :=
    ae_of_ae_map (p := fun y => ((R k F : Lp ℂ 2 (μ.restrict D)) : G → ℂ) y
      = (F : G → ℂ) (rr_rep (Γ : Set G) D (y * k))) hmeas (by rw [hmap]; exact hR k F)
  have e4 : ∀ᵐ x ∂(μ.restrict D), rr_rep (Γ : Set G) D (rr_rep (Γ : Set G) D (x * g) * k)
      = rr_rep (Γ : Set G) D (x * (g * k)) :=
    ae_restrict_of_ae (rp_rep_comp h g k hgk)
  filter_upwards [e1, e2, e3, e4] with x h1 h2 h3 h4
  rw [ContinuousLinearMap.comp_apply, h2, h3, h4, h1]

end Abs

section Inst

variable (I : AutInst)

/- English proof (translation)
Use `first`. Consider the case `infer_instance`. Consider the case `(unfold ProjRows.muInf; infer_instance)`. Consider the case `(unfold Formalism.L2.SG.ProjRows.muInf Formalism.REAL.muG; infer_instance)`.
-/
theorem muInf_right : (ProjRows.muInf I).IsMulRightInvariant := by
  first
  | infer_instance
  | (unfold ProjRows.muInf; infer_instance)
  | (unfold Formalism.L2.SG.ProjRows.muInf Formalism.REAL.muG; infer_instance)

/- English proof (translation)
Establish `h1 : MeasurePreserving (fun x : I.Ginf => x * g) (ProjRows.muInf I) (ProjRows.muInf I)` using `by haveI := muInf_right I`. Conclude with `measurePreserving_mul_right (ProjRows.muInf I) g`. Establish `h3 : (fun x : I.GA => x * ((g, 1) : I.GA)) = Prod.map (fun x : I.Ginf => x * g) id`. Use function extensionality and compare the values at `x`. Conclude with `Prod.ext (by simp) (by simp)`.

Unfold `RPres`. Rewrite using `[h3]`. Conclude with `h1.prod (MeasurePreserving.id μf)`.
-/
theorem rp_inst (μf : Measure I.Gf) [SigmaFinite μf] (g : I.Ginf) :
    RPres (I.muA μf) ((g, 1) : I.GA) := by
  have h1 : MeasurePreserving (fun x : I.Ginf => x * g) (ProjRows.muInf I) (ProjRows.muInf I) := by
    haveI := muInf_right I
    exact measurePreserving_mul_right (ProjRows.muInf I) g
  have h3 : (fun x : I.GA => x * ((g, 1) : I.GA)) = Prod.map (fun x : I.Ginf => x * g) id := by
    funext x
    exact Prod.ext (by simp) (by simp)
  unfold RPres
  rw [h3]
  exact h1.prod (MeasurePreserving.id μf)

/- English proof (translation)
Establish `e : ((g, 1) : I.GA)⁻¹ = ((g⁻¹, 1) : I.GA)` using `Prod.ext (by simp) (by simp)`. Rewrite using `[e]`. Conclude with `rp_inst I μf g⁻¹`.
-/
theorem rp_inst_inv (μf : Measure I.Gf) [SigmaFinite μf] (g : I.Ginf) :
    RPres (I.muA μf) (((g, 1) : I.GA)⁻¹) := by
  have e : ((g, 1) : I.GA)⁻¹ = ((g⁻¹, 1) : I.GA) := Prod.ext (by simp) (by simp)
  rw [e]
  exact rp_inst I μf g⁻¹

/- English proof (translation)
Use `haveI := muInf_right I`. Set `F : C(I.Ginf, C(I.Ginf, I.Ginf))` to `ContinuousMap.curry ⟨fun p : I.Ginf × I.Ginf => p.2 * p.1, continuous_snd.mul continuous_fst⟩`. Establish `hF : ∀ a x : I.Ginf, F a x = x * a` using `fun a x => rfl`. Establish `hmp : ∀ a : I.Ginf, MeasurePreserving (F a) (ProjRows.muInf I) (ProjRows.muInf I)` using `fun a => measurePreserving_mul_right (ProjRows.muInf I) a`. Establish `key` using `tendsto_measure_symmDiff_preimage_nhds_zero (F.continuous.tendsto 1) (by filter_upwards with a; exact hmp a) (hmp 1) hC.nullMeasurableSet hfin`.

Use `tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds key (fun _ => zero_le) (fun g => measure_mono ?_)` and prove the remaining obligations. Introduce `x hx`. Rewrite using `[Set.mem_symmDiff]`. Use `Or.inr ⟨?_, ?_⟩` and prove the remaining obligations. Use `show F 1 x ∈ C`.

Rewrite using `[hF, mul_one]`. Conclude with `hx.1`. Use `show ¬ F g x ∈ C`. Rewrite using `[hF]`. Conclude with `hx.2`.
-/
theorem inf_tendsto {C : Set I.Ginf} (hC : MeasurableSet C) (hfin : ProjRows.muInf I C ≠ ∞) :
    Tendsto (fun g : I.Ginf => ProjRows.muInf I (C \ (fun x => x * g) ⁻¹' C)) (𝓝 1) (𝓝 0) := by
  haveI := muInf_right I
  let F : C(I.Ginf, C(I.Ginf, I.Ginf)) :=
    ContinuousMap.curry ⟨fun p : I.Ginf × I.Ginf => p.2 * p.1, continuous_snd.mul continuous_fst⟩
  have hF : ∀ a x : I.Ginf, F a x = x * a := fun a x => rfl
  have hmp : ∀ a : I.Ginf, MeasurePreserving (F a) (ProjRows.muInf I) (ProjRows.muInf I) := fun a =>
    measurePreserving_mul_right (ProjRows.muInf I) a
  have key := tendsto_measure_symmDiff_preimage_nhds_zero (F.continuous.tendsto 1)
    (by filter_upwards with a; exact hmp a) (hmp 1) hC.nullMeasurableSet hfin
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds key (fun _ => zero_le)
    (fun g => measure_mono ?_)
  intro x hx
  rw [Set.mem_symmDiff]
  refine Or.inr ⟨?_, ?_⟩
  · show F 1 x ∈ C
    rw [hF, mul_one]
    exact hx.1
  · show ¬ F g x ∈ C
    rw [hF]
    exact hx.2

/- English proof (translation)
Establish `hslice : ∀ (g : I.Ginf) (y : I.Gf), (fun x : I.Ginf => (x, y)) ⁻¹' (A \ (fun x => x * ((g, 1) : I.GA)) ⁻¹' A) = (fun x : I.Ginf => (x, y)) ⁻¹' A \ (fun x => x * g) ⁻¹' ((fun x : I.Ginf => (x, y)) ⁻¹' A)`. Introduce `g y`. Use extensionality with `x`. Simplify using `[Set.mem_diff]`. Establish `hmA : ∀ y : I.Gf, MeasurableSet ((fun x : I.Ginf => (x, y)) ⁻¹' A)` using `fun y => by first`.

Consider the case `exact hA.preimage measurable_prod_mk_right`. Consider the case `exact hA.preimage measurable_prodMk_right`. Consider the case `exact hA.preimage (measurable_id.prodMk measurable_const)`. Consider the case `exact hA.preimage (measurable_id.prod_mk measurable_const)`. Establish `hB : ∀ g : I.Ginf, MeasurableSet (A \ (fun x => x * ((g, 1) : I.GA)) ⁻¹' A)` using `fun g => hA.diff (hA.preimage (measurable_mul_const _))`.

Establish `hF : ∀ g : I.Ginf, I.muA μf (A \ (fun x => x * ((g, 1) : I.GA)) ⁻¹' A) = ∫⁻ y, ProjRows.muInf I ((fun x : I.Ginf => (x, y)) ⁻¹' (A \ (fun x => x * ((g, 1) : I.GA)) ⁻¹' A)) ∂μf`. Introduce `g`. Unfold `AutInst.muA`. Conclude with `Measure.prod_apply_symm (hB g)`. Establish `hAint : ∫⁻ y, ProjRows.muInf I ((fun x : I.Ginf => (x, y)) ⁻¹' A) ∂μf ≠ ∞`.

Establish `e : I.muA μf A = ∫⁻ y, ProjRows.muInf I ((fun x : I.Ginf => (x, y)) ⁻¹' A) ∂μf`. Unfold `AutInst.muA`. Conclude with `Measure.prod_apply_symm hA`. Rewrite using `[← e]`. Conclude with `hfin`.

Establish `hmeasA : Measurable fun y : I.Gf => ProjRows.muInf I ((fun x : I.Ginf => (x, y)) ⁻¹' A)` using `by first`. Consider the case `exact measurable_measure_prod_mk_right hA`. Consider the case `exact measurable_measure_prodMk_right hA`. Repeatedly rewrite using `[hF]`. Rewrite using `[show (0 : ℝ≥0∞) = ∫⁻ _ : I.Gf, (0 : ℝ≥0∞) ∂μf by simp]`.

Use `tendsto_lintegral_filter_of_dominated_convergence (fun y => ProjRows.muInf I ((fun x : I.Ginf => (x, y)) ⁻¹' A)) ?_ ?_ hAint ?_` and prove the remaining obligations. Use `filter_upwards with g first`. Consider the case `exact measurable_measure_prod_mk_right (hB g)`. Consider the case `exact measurable_measure_prodMk_right (hB g)`. Use `filter_upwards with g filter_upwards with y`.

Conclude with `measure_mono (fun x hx => hx.1)`. Use `filter_upwards [ae_lt_top hmeasA hAint] with y hy`. Establish `e : (fun g : I.Ginf => ProjRows.muInf I ((fun x : I.Ginf => (x, y)) ⁻¹' (A \ (fun x => x * ((g, 1) : I.GA)) ⁻¹' A))) = fun g : I.Ginf => ProjRows.muInf I ((fun x : I.Ginf => (x, y)) ⁻¹' A \ (fun x => x * g) ⁻¹' ((fun x : I.Ginf => (x, y)) ⁻¹' A))`. Use function extensionality and compare the values at `fun g => by rw [hslice g y]`. Rewrite using `[e]`.

Conclude with `inf_tendsto I (hmA y) hy.ne`.
-/
theorem adele_tendsto (μf : Measure I.Gf) [SigmaFinite μf] {A : Set I.GA} (hA : MeasurableSet A)
    (hfin : I.muA μf A ≠ ∞) :
    Tendsto (fun g : I.Ginf => I.muA μf (A \ (fun x => x * ((g, 1) : I.GA)) ⁻¹' A)) (𝓝 1) (𝓝 0) := by
  have hslice : ∀ (g : I.Ginf) (y : I.Gf),
      (fun x : I.Ginf => (x, y)) ⁻¹' (A \ (fun x => x * ((g, 1) : I.GA)) ⁻¹' A)
        = (fun x : I.Ginf => (x, y)) ⁻¹' A \ (fun x => x * g) ⁻¹' ((fun x : I.Ginf => (x, y)) ⁻¹' A) := by
    intro g y
    ext x
    simp [Set.mem_diff]
  have hmA : ∀ y : I.Gf, MeasurableSet ((fun x : I.Ginf => (x, y)) ⁻¹' A) := fun y => by
    first
    | exact hA.preimage measurable_prod_mk_right
    | exact hA.preimage measurable_prodMk_right
    | exact hA.preimage (measurable_id.prodMk measurable_const)
    | exact hA.preimage (measurable_id.prod_mk measurable_const)
  have hB : ∀ g : I.Ginf, MeasurableSet (A \ (fun x => x * ((g, 1) : I.GA)) ⁻¹' A) := fun g =>
    hA.diff (hA.preimage (measurable_mul_const _))
  have hF : ∀ g : I.Ginf, I.muA μf (A \ (fun x => x * ((g, 1) : I.GA)) ⁻¹' A)
      = ∫⁻ y, ProjRows.muInf I ((fun x : I.Ginf => (x, y)) ⁻¹' (A \ (fun x => x * ((g, 1) : I.GA)) ⁻¹' A)) ∂μf := by
    intro g
    unfold AutInst.muA
    exact Measure.prod_apply_symm (hB g)
  have hAint : ∫⁻ y, ProjRows.muInf I ((fun x : I.Ginf => (x, y)) ⁻¹' A) ∂μf ≠ ∞ := by
    have e : I.muA μf A = ∫⁻ y, ProjRows.muInf I ((fun x : I.Ginf => (x, y)) ⁻¹' A) ∂μf := by
      unfold AutInst.muA
      exact Measure.prod_apply_symm hA
    rw [← e]
    exact hfin
  have hmeasA : Measurable fun y : I.Gf => ProjRows.muInf I ((fun x : I.Ginf => (x, y)) ⁻¹' A) := by
    first
    | exact measurable_measure_prod_mk_right hA
    | exact measurable_measure_prodMk_right hA
  simp_rw [hF]
  rw [show (0 : ℝ≥0∞) = ∫⁻ _ : I.Gf, (0 : ℝ≥0∞) ∂μf by simp]
  refine tendsto_lintegral_filter_of_dominated_convergence
    (fun y => ProjRows.muInf I ((fun x : I.Ginf => (x, y)) ⁻¹' A)) ?_ ?_ hAint ?_
  · filter_upwards with g
    first
    | exact measurable_measure_prod_mk_right (hB g)
    | exact measurable_measure_prodMk_right (hB g)
  · filter_upwards with g
    filter_upwards with y
    exact measure_mono (fun x hx => hx.1)
  · filter_upwards [ae_lt_top hmeasA hAint] with y hy
    have e : (fun g : I.Ginf => ProjRows.muInf I
        ((fun x : I.Ginf => (x, y)) ⁻¹' (A \ (fun x => x * ((g, 1) : I.GA)) ⁻¹' A)))
        = fun g : I.Ginf => ProjRows.muInf I ((fun x : I.Ginf => (x, y)) ⁻¹' A \
            (fun x => x * g) ⁻¹' ((fun x : I.Ginf => (x, y)) ⁻¹' A)) :=
      funext fun g => by rw [hslice g y]
    rw [e]
    exact inf_tendsto I (hmA y) hy.ne

end Inst

section Main

variable (I : AutInst) (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsHaarMeasure] (fund : Set I.GA)
  (hfd : I.IsFundDom (I.muA μf) fund) (R : I.GA → (I.L2 μf fund →L[ℂ] I.L2 μf fund))
  (hR : I.IsRightReg μf fund R)

include hfd hR in
/- English proof (translation)
Establish `hdet : ∀ v, IsUnit (I.P v).det` using `fun v => (Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit v)`. Establish `key : ∀ (P A B : Matrix (Fin I.n) (Fin I.n) ℂ), IsUnit P.det → P⁻¹ * A * P * (P⁻¹ * B * P) = P⁻¹ * (A * B) * P`. Introduce `P A B hP`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.mul_nonsing_inv _ hP, Matrix.mul_one, Matrix.mul_assoc (P⁻¹) A B]`.

Establish `h1 : (1 : I.GA) ∈ I.GFset`. Simplify using `only [AutInst.GFset, Set.mem_setOf_eq]`. Use `⟨1, (Formalism.UG.UJ (starRingEnd I.E) I.J).one_mem, fun v => ?_, ?_⟩` and prove the remaining obligations. Simplify using `[uMat, Matrix.nonsing_inv_mul _ (hdet v)]`. Simplify using `[AutInst.fmat]`.

Establish `hmul : ∀ {a b : I.GA}, a ∈ I.GFset → b ∈ I.GFset → a * b ∈ I.GFset`. Introduce `a b ha hb`. Simplify using `only [AutInst.GFset, Set.mem_setOf_eq] at ha hb ⊢`. Take `⟨γ₁, hγ₁, hu₁, hf₁⟩` from `ha`. Take `⟨γ₂, hγ₂, hu₂, hf₂⟩` from `hb`.

Use `⟨γ₁ * γ₂, (Formalism.UG.UJ (starRingEnd I.E) I.J).mul_mem hγ₁ hγ₂, fun v => ?_, ?_⟩` and prove the remaining obligations. Establish `e : uMat ((a * b).1 v) = uMat (a.1 v) * uMat (b.1 v)` using `by simp [uMat]`. Rewrite using `[e, hu₁ v, hu₂ v, key _ _ _ (hdet v), Units.val_mul, Matrix.map_mul]`. Establish `e : I.fmat (a * b).2 = I.fmat a.2 * I.fmat b.2` using `by simp [AutInst.fmat]`. Rewrite using `[e, hf₁, hf₂, Units.val_mul, Matrix.map_mul]`.

Establish `hinv : ∀ {a : I.GA}, a ∈ I.GFset → a⁻¹ ∈ I.GFset`. Introduce `a ha`. Simplify using `only [AutInst.GFset, Set.mem_setOf_eq] at ha ⊢`. Take `⟨γ, hγ, hu, hf⟩` from `ha`. Use `⟨γ⁻¹, (Formalism.UG.UJ (starRingEnd I.E) I.J).inv_mem hγ, fun v => ?_, ?_⟩` and prove the remaining obligations.

Establish `hM : uMat (a.1 v) * uMat (a⁻¹.1 v) = 1` using `by simp [uMat]`. Rewrite using `[← Matrix.inv_eq_right_inv hM]`. Apply `Matrix.inv_eq_right_inv` to reduce the goal to its premises. Rewrite using `[hu v, key _ _ _ (hdet v), ← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one, Matrix.nonsing_inv_mul _ (hdet v)]`. Establish `hM : I.fmat a.2 * I.fmat a⁻¹.2 = 1` using `by simp [AutInst.fmat]`.

Rewrite using `[← Matrix.inv_eq_right_inv hM]`. Apply `Matrix.inv_eq_right_inv` to reduce the goal to its premises. Rewrite using `[hf, ← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]`. Set `Γ : Subgroup I.GA` to `{ carrier := I.GFset mul_mem' := hmul one_mem' := h1 inv_mem' := hinv }`. Use `haveI hEc : Countable I.E := (Module.finBasis ℚ I.E).equivFun.injective.countable`.

Use `haveI hGLc : Countable (GL (Fin I.n) I.E) := by`. Use `Function.Injective.countable (f := fun u : GL (Fin I.n) I.E => fun i j => (u : Matrix (Fin I.n) (Fin I.n) I.E) i j) ?_` and prove the remaining obligations. Introduce `u w huw`. Conclude with `Units.ext (Matrix.ext fun i j => congrFun (congrFun huw i) j)`. Use `haveI hΓc : Countable Γ := by`.

Use `Function.Injective.countable (f := fun x : Γ => Classical.choose x.2) ?_` and prove the remaining obligations. Introduce `x y hxy`. Establish `hxy' : Classical.choose x.2 = Classical.choose y.2` using `hxy`. Establish `sx` using `Classical.choose_spec x.2`. Establish `sy` using `Classical.choose_spec y.2`.

Rewrite `sx` using `[hxy']`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Prod.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `v`. Apply `Subtype.ext` to reduce the goal to its premises.

Apply `Units.ext` to reduce the goal to its premises. Conclude with `(sx.2.1 v).trans (sy.2.1 v).symm`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Conclude with `sx.2.2.trans sy.2.2.symm`.

Use `haveI hli : (I.muA μf).IsMulLeftInvariant := by`. Unfold `AutInst.muA`. Use `first`. Consider the case `infer_instance`. Consider the case `(unfold Formalism.REAL.muG; infer_instance)`.

Establish `hFD : rr_FD (I.muA μf) Γ fund` using `⟨hfd.1, hfd.2.1, hfd.2.2⟩`. Establish `hReg : rr_IsReg (I.muA μf) Γ fund R`. Introduce `g' F'`. Use `first`. Consider the case `exact hR g' F'`.

Consider the case `(filter_upwards [hR g' F'] with x hx; rw [hx]; rfl)`. Conclude with `rp_norm hFD hReg (rp_inst I μf g) (rp_inst_inv I μf g) F`.
-/
theorem reg_norm (g : I.Ginf) (F : I.L2 μf fund) : ‖R (g, 1) F‖ = ‖F‖ := by
  have hdet : ∀ v, IsUnit (I.P v).det := fun v => (Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit v)
  have key : ∀ (P A B : Matrix (Fin I.n) (Fin I.n) ℂ), IsUnit P.det →
      P⁻¹ * A * P * (P⁻¹ * B * P) = P⁻¹ * (A * B) * P := by
    intro P A B hP
    calc P⁻¹ * A * P * (P⁻¹ * B * P) = P⁻¹ * A * (P * P⁻¹) * B * P := by simp only [Matrix.mul_assoc]
      _ = P⁻¹ * (A * B) * P := by
        rw [Matrix.mul_nonsing_inv _ hP, Matrix.mul_one, Matrix.mul_assoc (P⁻¹) A B]
  have h1 : (1 : I.GA) ∈ I.GFset := by
    simp only [AutInst.GFset, Set.mem_setOf_eq]
    refine ⟨1, (Formalism.UG.UJ (starRingEnd I.E) I.J).one_mem, fun v => ?_, ?_⟩
    · simp [uMat, Matrix.nonsing_inv_mul _ (hdet v)]
    · simp [AutInst.fmat]
  have hmul : ∀ {a b : I.GA}, a ∈ I.GFset → b ∈ I.GFset → a * b ∈ I.GFset := by
    intro a b ha hb
    simp only [AutInst.GFset, Set.mem_setOf_eq] at ha hb ⊢
    obtain ⟨γ₁, hγ₁, hu₁, hf₁⟩ := ha
    obtain ⟨γ₂, hγ₂, hu₂, hf₂⟩ := hb
    refine ⟨γ₁ * γ₂, (Formalism.UG.UJ (starRingEnd I.E) I.J).mul_mem hγ₁ hγ₂, fun v => ?_, ?_⟩
    · have e : uMat ((a * b).1 v) = uMat (a.1 v) * uMat (b.1 v) := by simp [uMat]
      rw [e, hu₁ v, hu₂ v, key _ _ _ (hdet v), Units.val_mul, Matrix.map_mul]
    · have e : I.fmat (a * b).2 = I.fmat a.2 * I.fmat b.2 := by simp [AutInst.fmat]
      rw [e, hf₁, hf₂, Units.val_mul, Matrix.map_mul]
  have hinv : ∀ {a : I.GA}, a ∈ I.GFset → a⁻¹ ∈ I.GFset := by
    intro a ha
    simp only [AutInst.GFset, Set.mem_setOf_eq] at ha ⊢
    obtain ⟨γ, hγ, hu, hf⟩ := ha
    refine ⟨γ⁻¹, (Formalism.UG.UJ (starRingEnd I.E) I.J).inv_mem hγ, fun v => ?_, ?_⟩
    · have hM : uMat (a.1 v) * uMat (a⁻¹.1 v) = 1 := by simp [uMat]
      rw [← Matrix.inv_eq_right_inv hM]
      apply Matrix.inv_eq_right_inv
      rw [hu v, key _ _ _ (hdet v), ← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one, Matrix.nonsing_inv_mul _ (hdet v)]
    · have hM : I.fmat a.2 * I.fmat a⁻¹.2 = 1 := by simp [AutInst.fmat]
      rw [← Matrix.inv_eq_right_inv hM]
      apply Matrix.inv_eq_right_inv
      rw [hf, ← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.map_one _ (map_zero _) (map_one _)]
  let Γ : Subgroup I.GA :=
    { carrier := I.GFset
      mul_mem' := hmul
      one_mem' := h1
      inv_mem' := hinv }
  haveI hEc : Countable I.E := (Module.finBasis ℚ I.E).equivFun.injective.countable
  haveI hGLc : Countable (GL (Fin I.n) I.E) := by
    refine Function.Injective.countable
      (f := fun u : GL (Fin I.n) I.E => fun i j => (u : Matrix (Fin I.n) (Fin I.n) I.E) i j) ?_
    intro u w huw
    exact Units.ext (Matrix.ext fun i j => congrFun (congrFun huw i) j)
  haveI hΓc : Countable Γ := by
    refine Function.Injective.countable (f := fun x : Γ => Classical.choose x.2) ?_
    intro x y hxy
    have hxy' : Classical.choose x.2 = Classical.choose y.2 := hxy
    have sx := Classical.choose_spec x.2
    have sy := Classical.choose_spec y.2
    rw [hxy'] at sx
    apply Subtype.ext
    apply Prod.ext
    · funext v
      apply Subtype.ext
      apply Units.ext
      exact (sx.2.1 v).trans (sy.2.1 v).symm
    · apply Subtype.ext
      apply Units.ext
      exact sx.2.2.trans sy.2.2.symm
  haveI hli : (I.muA μf).IsMulLeftInvariant := by
    unfold AutInst.muA
    first
    | infer_instance
    | (unfold Formalism.REAL.muG; infer_instance)
  have hFD : rr_FD (I.muA μf) Γ fund := ⟨hfd.1, hfd.2.1, hfd.2.2⟩
  have hReg : rr_IsReg (I.muA μf) Γ fund R := by
    intro g' F'
    first
    | exact hR g' F'
    | (filter_upwards [hR g' F'] with x hx; rw [hx]; rfl)
  exact rp_norm hFD hReg (rp_inst I μf g) (rp_inst_inv I μf g) F

include hfd hR in
/- English proof (translation)
Establish `hdet : ∀ v, IsUnit (I.P v).det` using `fun v => (Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit v)`. Establish `key : ∀ (P A B : Matrix (Fin I.n) (Fin I.n) ℂ), IsUnit P.det → P⁻¹ * A * P * (P⁻¹ * B * P) = P⁻¹ * (A * B) * P`. Introduce `P A B hP`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.mul_nonsing_inv _ hP, Matrix.mul_one, Matrix.mul_assoc (P⁻¹) A B]`.

Establish `h1 : (1 : I.GA) ∈ I.GFset`. Simplify using `only [AutInst.GFset, Set.mem_setOf_eq]`. Use `⟨1, (Formalism.UG.UJ (starRingEnd I.E) I.J).one_mem, fun v => ?_, ?_⟩` and prove the remaining obligations. Simplify using `[uMat, Matrix.nonsing_inv_mul _ (hdet v)]`. Simplify using `[AutInst.fmat]`.

Establish `hmul : ∀ {a b : I.GA}, a ∈ I.GFset → b ∈ I.GFset → a * b ∈ I.GFset`. Introduce `a b ha hb`. Simplify using `only [AutInst.GFset, Set.mem_setOf_eq] at ha hb ⊢`. Take `⟨γ₁, hγ₁, hu₁, hf₁⟩` from `ha`. Take `⟨γ₂, hγ₂, hu₂, hf₂⟩` from `hb`.

Use `⟨γ₁ * γ₂, (Formalism.UG.UJ (starRingEnd I.E) I.J).mul_mem hγ₁ hγ₂, fun v => ?_, ?_⟩` and prove the remaining obligations. Establish `e : uMat ((a * b).1 v) = uMat (a.1 v) * uMat (b.1 v)` using `by simp [uMat]`. Rewrite using `[e, hu₁ v, hu₂ v, key _ _ _ (hdet v), Units.val_mul, Matrix.map_mul]`. Establish `e : I.fmat (a * b).2 = I.fmat a.2 * I.fmat b.2` using `by simp [AutInst.fmat]`. Rewrite using `[e, hf₁, hf₂, Units.val_mul, Matrix.map_mul]`.

Establish `hinv : ∀ {a : I.GA}, a ∈ I.GFset → a⁻¹ ∈ I.GFset`. Introduce `a ha`. Simplify using `only [AutInst.GFset, Set.mem_setOf_eq] at ha ⊢`. Take `⟨γ, hγ, hu, hf⟩` from `ha`. Use `⟨γ⁻¹, (Formalism.UG.UJ (starRingEnd I.E) I.J).inv_mem hγ, fun v => ?_, ?_⟩` and prove the remaining obligations.

Establish `hM : uMat (a.1 v) * uMat (a⁻¹.1 v) = 1` using `by simp [uMat]`. Rewrite using `[← Matrix.inv_eq_right_inv hM]`. Apply `Matrix.inv_eq_right_inv` to reduce the goal to its premises. Rewrite using `[hu v, key _ _ _ (hdet v), ← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one, Matrix.nonsing_inv_mul _ (hdet v)]`. Establish `hM : I.fmat a.2 * I.fmat a⁻¹.2 = 1` using `by simp [AutInst.fmat]`.

Rewrite using `[← Matrix.inv_eq_right_inv hM]`. Apply `Matrix.inv_eq_right_inv` to reduce the goal to its premises. Rewrite using `[hf, ← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]`. Set `Γ : Subgroup I.GA` to `{ carrier := I.GFset mul_mem' := hmul one_mem' := h1 inv_mem' := hinv }`. Use `haveI hEc : Countable I.E := (Module.finBasis ℚ I.E).equivFun.injective.countable`.

Use `haveI hGLc : Countable (GL (Fin I.n) I.E) := by`. Use `Function.Injective.countable (f := fun u : GL (Fin I.n) I.E => fun i j => (u : Matrix (Fin I.n) (Fin I.n) I.E) i j) ?_` and prove the remaining obligations. Introduce `u w huw`. Conclude with `Units.ext (Matrix.ext fun i j => congrFun (congrFun huw i) j)`. Use `haveI hΓc : Countable Γ := by`.

Use `Function.Injective.countable (f := fun x : Γ => Classical.choose x.2) ?_` and prove the remaining obligations. Introduce `x y hxy`. Establish `hxy' : Classical.choose x.2 = Classical.choose y.2` using `hxy`. Establish `sx` using `Classical.choose_spec x.2`. Establish `sy` using `Classical.choose_spec y.2`.

Rewrite `sx` using `[hxy']`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Prod.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `v`. Apply `Subtype.ext` to reduce the goal to its premises.

Apply `Units.ext` to reduce the goal to its premises. Conclude with `(sx.2.1 v).trans (sy.2.1 v).symm`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Conclude with `sx.2.2.trans sy.2.2.symm`.

Use `haveI hli : (I.muA μf).IsMulLeftInvariant := by`. Unfold `AutInst.muA`. Use `first`. Consider the case `infer_instance`. Consider the case `(unfold Formalism.REAL.muG; infer_instance)`.

Establish `hFD : rr_FD (I.muA μf) Γ fund` using `⟨hfd.1, hfd.2.1, hfd.2.2⟩`. Establish `hReg : rr_IsReg (I.muA μf) Γ fund R`. Introduce `g' F'`. Use `first`. Consider the case `exact hR g' F'`.

Consider the case `(filter_upwards [hR g' F'] with x hx; rw [hx]; rfl)`. Establish `e : ((a * b, 1) : I.GA) = ((a, 1) : I.GA) * ((b, 1) : I.GA)` using `Prod.ext (by simp) (by simp)`. Rewrite using `[e]`. Conclude with `rp_mul hFD hReg (rp_inst I μf a) (rp_inst_inv I μf a) (by rw [← e]; exact rp_inst I μf (a * b))`.
-/
theorem reg_mul (a b : I.Ginf) : R (a * b, 1) = (R (a, 1)).comp (R (b, 1)) := by
  have hdet : ∀ v, IsUnit (I.P v).det := fun v => (Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit v)
  have key : ∀ (P A B : Matrix (Fin I.n) (Fin I.n) ℂ), IsUnit P.det →
      P⁻¹ * A * P * (P⁻¹ * B * P) = P⁻¹ * (A * B) * P := by
    intro P A B hP
    calc P⁻¹ * A * P * (P⁻¹ * B * P) = P⁻¹ * A * (P * P⁻¹) * B * P := by simp only [Matrix.mul_assoc]
      _ = P⁻¹ * (A * B) * P := by
        rw [Matrix.mul_nonsing_inv _ hP, Matrix.mul_one, Matrix.mul_assoc (P⁻¹) A B]
  have h1 : (1 : I.GA) ∈ I.GFset := by
    simp only [AutInst.GFset, Set.mem_setOf_eq]
    refine ⟨1, (Formalism.UG.UJ (starRingEnd I.E) I.J).one_mem, fun v => ?_, ?_⟩
    · simp [uMat, Matrix.nonsing_inv_mul _ (hdet v)]
    · simp [AutInst.fmat]
  have hmul : ∀ {a b : I.GA}, a ∈ I.GFset → b ∈ I.GFset → a * b ∈ I.GFset := by
    intro a b ha hb
    simp only [AutInst.GFset, Set.mem_setOf_eq] at ha hb ⊢
    obtain ⟨γ₁, hγ₁, hu₁, hf₁⟩ := ha
    obtain ⟨γ₂, hγ₂, hu₂, hf₂⟩ := hb
    refine ⟨γ₁ * γ₂, (Formalism.UG.UJ (starRingEnd I.E) I.J).mul_mem hγ₁ hγ₂, fun v => ?_, ?_⟩
    · have e : uMat ((a * b).1 v) = uMat (a.1 v) * uMat (b.1 v) := by simp [uMat]
      rw [e, hu₁ v, hu₂ v, key _ _ _ (hdet v), Units.val_mul, Matrix.map_mul]
    · have e : I.fmat (a * b).2 = I.fmat a.2 * I.fmat b.2 := by simp [AutInst.fmat]
      rw [e, hf₁, hf₂, Units.val_mul, Matrix.map_mul]
  have hinv : ∀ {a : I.GA}, a ∈ I.GFset → a⁻¹ ∈ I.GFset := by
    intro a ha
    simp only [AutInst.GFset, Set.mem_setOf_eq] at ha ⊢
    obtain ⟨γ, hγ, hu, hf⟩ := ha
    refine ⟨γ⁻¹, (Formalism.UG.UJ (starRingEnd I.E) I.J).inv_mem hγ, fun v => ?_, ?_⟩
    · have hM : uMat (a.1 v) * uMat (a⁻¹.1 v) = 1 := by simp [uMat]
      rw [← Matrix.inv_eq_right_inv hM]
      apply Matrix.inv_eq_right_inv
      rw [hu v, key _ _ _ (hdet v), ← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one, Matrix.nonsing_inv_mul _ (hdet v)]
    · have hM : I.fmat a.2 * I.fmat a⁻¹.2 = 1 := by simp [AutInst.fmat]
      rw [← Matrix.inv_eq_right_inv hM]
      apply Matrix.inv_eq_right_inv
      rw [hf, ← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.map_one _ (map_zero _) (map_one _)]
  let Γ : Subgroup I.GA :=
    { carrier := I.GFset
      mul_mem' := hmul
      one_mem' := h1
      inv_mem' := hinv }
  haveI hEc : Countable I.E := (Module.finBasis ℚ I.E).equivFun.injective.countable
  haveI hGLc : Countable (GL (Fin I.n) I.E) := by
    refine Function.Injective.countable
      (f := fun u : GL (Fin I.n) I.E => fun i j => (u : Matrix (Fin I.n) (Fin I.n) I.E) i j) ?_
    intro u w huw
    exact Units.ext (Matrix.ext fun i j => congrFun (congrFun huw i) j)
  haveI hΓc : Countable Γ := by
    refine Function.Injective.countable (f := fun x : Γ => Classical.choose x.2) ?_
    intro x y hxy
    have hxy' : Classical.choose x.2 = Classical.choose y.2 := hxy
    have sx := Classical.choose_spec x.2
    have sy := Classical.choose_spec y.2
    rw [hxy'] at sx
    apply Subtype.ext
    apply Prod.ext
    · funext v
      apply Subtype.ext
      apply Units.ext
      exact (sx.2.1 v).trans (sy.2.1 v).symm
    · apply Subtype.ext
      apply Units.ext
      exact sx.2.2.trans sy.2.2.symm
  haveI hli : (I.muA μf).IsMulLeftInvariant := by
    unfold AutInst.muA
    first
    | infer_instance
    | (unfold Formalism.REAL.muG; infer_instance)
  have hFD : rr_FD (I.muA μf) Γ fund := ⟨hfd.1, hfd.2.1, hfd.2.2⟩
  have hReg : rr_IsReg (I.muA μf) Γ fund R := by
    intro g' F'
    first
    | exact hR g' F'
    | (filter_upwards [hR g' F'] with x hx; rw [hx]; rfl)
  have e : ((a * b, 1) : I.GA) = ((a, 1) : I.GA) * ((b, 1) : I.GA) := Prod.ext (by simp) (by simp)
  rw [e]
  exact rp_mul hFD hReg (rp_inst I μf a) (rp_inst_inv I μf a) (by rw [← e]; exact rp_inst I μf (a * b))

include hfd hR in

/- English proof (translation)
Establish `hdet : ∀ v, IsUnit (I.P v).det` using `fun v => (Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit v)`. Establish `key : ∀ (P A B : Matrix (Fin I.n) (Fin I.n) ℂ), IsUnit P.det → P⁻¹ * A * P * (P⁻¹ * B * P) = P⁻¹ * (A * B) * P`. Introduce `P A B hP`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.mul_nonsing_inv _ hP, Matrix.mul_one, Matrix.mul_assoc (P⁻¹) A B]`.

Establish `h1 : (1 : I.GA) ∈ I.GFset`. Simplify using `only [AutInst.GFset, Set.mem_setOf_eq]`. Use `⟨1, (Formalism.UG.UJ (starRingEnd I.E) I.J).one_mem, fun v => ?_, ?_⟩` and prove the remaining obligations. Simplify using `[uMat, Matrix.nonsing_inv_mul _ (hdet v)]`. Simplify using `[AutInst.fmat]`.

Establish `hmul : ∀ {a b : I.GA}, a ∈ I.GFset → b ∈ I.GFset → a * b ∈ I.GFset`. Introduce `a b ha hb`. Simplify using `only [AutInst.GFset, Set.mem_setOf_eq] at ha hb ⊢`. Take `⟨γ₁, hγ₁, hu₁, hf₁⟩` from `ha`. Take `⟨γ₂, hγ₂, hu₂, hf₂⟩` from `hb`.

Use `⟨γ₁ * γ₂, (Formalism.UG.UJ (starRingEnd I.E) I.J).mul_mem hγ₁ hγ₂, fun v => ?_, ?_⟩` and prove the remaining obligations. Establish `e : uMat ((a * b).1 v) = uMat (a.1 v) * uMat (b.1 v)` using `by simp [uMat]`. Rewrite using `[e, hu₁ v, hu₂ v, key _ _ _ (hdet v), Units.val_mul, Matrix.map_mul]`. Establish `e : I.fmat (a * b).2 = I.fmat a.2 * I.fmat b.2` using `by simp [AutInst.fmat]`. Rewrite using `[e, hf₁, hf₂, Units.val_mul, Matrix.map_mul]`.

Establish `hinv : ∀ {a : I.GA}, a ∈ I.GFset → a⁻¹ ∈ I.GFset`. Introduce `a ha`. Simplify using `only [AutInst.GFset, Set.mem_setOf_eq] at ha ⊢`. Take `⟨γ, hγ, hu, hf⟩` from `ha`. Use `⟨γ⁻¹, (Formalism.UG.UJ (starRingEnd I.E) I.J).inv_mem hγ, fun v => ?_, ?_⟩` and prove the remaining obligations.

Establish `hM : uMat (a.1 v) * uMat (a⁻¹.1 v) = 1` using `by simp [uMat]`. Rewrite using `[← Matrix.inv_eq_right_inv hM]`. Apply `Matrix.inv_eq_right_inv` to reduce the goal to its premises. Rewrite using `[hu v, key _ _ _ (hdet v), ← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one, Matrix.nonsing_inv_mul _ (hdet v)]`. Establish `hM : I.fmat a.2 * I.fmat a⁻¹.2 = 1` using `by simp [AutInst.fmat]`.

Rewrite using `[← Matrix.inv_eq_right_inv hM]`. Apply `Matrix.inv_eq_right_inv` to reduce the goal to its premises. Rewrite using `[hf, ← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]`. Set `Γ : Subgroup I.GA` to `{ carrier := I.GFset mul_mem' := hmul one_mem' := h1 inv_mem' := hinv }`. Use `haveI hEc : Countable I.E := (Module.finBasis ℚ I.E).equivFun.injective.countable`.

Use `haveI hGLc : Countable (GL (Fin I.n) I.E) := by`. Use `Function.Injective.countable (f := fun u : GL (Fin I.n) I.E => fun i j => (u : Matrix (Fin I.n) (Fin I.n) I.E) i j) ?_` and prove the remaining obligations. Introduce `u w huw`. Conclude with `Units.ext (Matrix.ext fun i j => congrFun (congrFun huw i) j)`. Use `haveI hΓc : Countable Γ := by`.

Use `Function.Injective.countable (f := fun x : Γ => Classical.choose x.2) ?_` and prove the remaining obligations. Introduce `x y hxy`. Establish `hxy' : Classical.choose x.2 = Classical.choose y.2` using `hxy`. Establish `sx` using `Classical.choose_spec x.2`. Establish `sy` using `Classical.choose_spec y.2`.

Rewrite `sx` using `[hxy']`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Prod.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `v`. Apply `Subtype.ext` to reduce the goal to its premises.

Apply `Units.ext` to reduce the goal to its premises. Conclude with `(sx.2.1 v).trans (sy.2.1 v).symm`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Conclude with `sx.2.2.trans sy.2.2.symm`.

Use `haveI hli : (I.muA μf).IsMulLeftInvariant := by`. Unfold `AutInst.muA`. Use `first`. Consider the case `infer_instance`. Consider the case `(unfold Formalism.REAL.muG; infer_instance)`.

Establish `hFD : rr_FD (I.muA μf) Γ fund` using `⟨hfd.1, hfd.2.1, hfd.2.2⟩`. Establish `hReg : rr_IsReg (I.muA μf) Γ fund R`. Introduce `g' F'`. Use `first`. Consider the case `exact hR g' F'`.

Consider the case `(filter_upwards [hR g' F'] with x hx; rw [hx]; rfl)`. Establish `hrep : ∀ y : I.GA, ∃ c ∈ Γ, rr_rep (Γ : Set I.GA) fund y = c * y ∧ c * y ∈ fund`. Introduce `y`. Establish `hex : ∃ γ ∈ (Γ : Set I.GA), γ * y ∈ fund` using `hFD.cov y`. Use `⟨hex.choose, hex.choose_spec.1, ?_, hex.choose_spec.2⟩` and prove the remaining obligations.

Unfold `rr_rep`. Use `first`. Consider the case `exact dif_pos hex`. Consider the case `rw [dif_pos hex]`. Consider the case `simp only [dif_pos hex]`.

Establish `hN0 : I.muA μf (rr_N Γ fund) = 0`. Establish `h0` using `rp_N_pre hFD (rp_inst I μf 1)`. Establish `e1 : (fun x : I.GA => x * (((1 : I.Ginf), (1 : I.Gf)) : I.GA)) = id`. Use function extensionality and compare the values at `fun x => mul_one x`. Use `first`.

Consider the case `(rw [e1, Set.preimage_id] at h0; exact h0)`. Consider the case `simpa using h0`. Establish `hs' : MeasurableSet (s ∩ fund)` using `hs.inter hfd.1`. Establish `hs'f : I.muA μf (s ∩ fund) ≠ ∞`. Rewrite using `[← Measure.restrict_apply hs]`.

Conclude with `hμs`. Use `set A : Set I.GA := ⋃ γ : Γ, (fun z => (γ : I.GA) * z) ⁻¹' (s ∩ fund) with hA`. Use `set X : I.L2 μf fund := indicatorConstLp 2 hs hμs (1 : ℂ) with hX`. Use `set E : I.Ginf → Set I.GA := fun g => ((fun z => z * ((g, 1) : I.GA)) ⁻¹' A) ∆ A with hE`. Use `set T : I.Ginf → Set I.GA := fun g => (s ∩ fund) ∆ ((fun z => z * ((g, 1) : I.GA)) ⁻¹' (s ∩ fund)) with hT`.

Establish `hTm : ∀ g : I.Ginf, MeasurableSet (T g)` using `fun g => by`. Rewrite using `[hT]`. Conclude with `hs'.symmDiff (hs'.preimage (measurable_mul_const _))`. Establish `hpt : ∀ g : I.Ginf, ∀ᵐ x ∂(I.muA μf).restrict fund, ‖((R (g, 1) X - X : I.L2 μf fund) : I.GA → ℂ) x‖ ≤ ‖(E g).indicator (fun _ => (1 : ℂ)) x‖`. Introduce `g`.

Take `⟨hmeas, hmap⟩` from `rp_map hFD (rp_inst I μf g) (rp_inst_inv I μf g)`. Establish `hXs : ⇑X =ᵐ[(I.muA μf).restrict fund] s.indicator fun _ => (1 : ℂ)`. Rewrite using `[hX]`. Conclude with `indicatorConstLp_coeFn`. Establish `F3 : ∀ᵐ x ∂(I.muA μf).restrict fund, X (rr_rep (Γ : Set I.GA) fund (x * ((g, 1) : I.GA))) = s.indicator (fun _ => (1 : ℂ)) (rr_rep (Γ : Set I.GA) fund (x * ((g, 1) : I.GA)))` using `ae_of_ae_map (p := fun y => X y = s.indicator (fun _ => (1 : ℂ)) y) hmeas (by rw [hmap]; exact hXs)`.

Establish `F7 : ∀ᵐ x ∂(I.muA μf).restrict fund, x * ((g, 1) : I.GA) ∉ rr_N Γ fund`. Use `ae_restrict_of_ae ?_` and prove the remaining obligations. Use `filter_upwards [compl_mem_ae_iff.mpr (rp_N_pre hFD (rp_inst I μf g))] with x hx`. Use `first`. Consider the case `simpa only [Set.mem_compl_iff, Set.mem_preimage] using hx`.

Consider the case `exact hx`. Establish `F6 : ∀ᵐ x ∂(I.muA μf).restrict fund, x ∉ rr_N Γ fund`. Use `ae_restrict_of_ae ?_` and prove the remaining obligations. Use `filter_upwards [compl_mem_ae_iff.mpr hN0] with x hx`. Use `first`.

Consider the case `simpa only [Set.mem_compl_iff] using hx`. Consider the case `exact hx`. Use `filter_upwards [Lp.coeFn_sub (R (g, 1) X) X, hReg (g, 1) X, F3, hXs, ae_restrict_mem hfd.1, F6, F7] with x e1 e2 e3 e4 hxD hx6 hx7`. Rewrite using `[e1]`. Use `first`.

Consider the case `rw [Pi.sub_apply]`. Consider the case `skip`. Rewrite using `[e2, e3, e4]`. Take `⟨c, hc, hcy, hcD⟩` from `hrep (x * ((g, 1) : I.GA))`. Rewrite using `[hcy]`.

Establish `hP1 : c * (x * ((g, 1) : I.GA)) ∈ s ↔ x * ((g, 1) : I.GA) ∈ A`. Rewrite using `[hA, Set.mem_iUnion]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `⟨⟨c, hc⟩, h, hcD⟩`.

Introduce and unpack `⟨γ, hγs, hγD⟩`. Establish `hγ : (γ : I.GA) = c`. Assume the negation of the conclusion as `hne`. Conclude with `hx7 (show ∃ γ₁ ∈ Γ, ∃ γ₂ ∈ Γ, γ₁ ≠ γ₂ ∧ γ₁ * (x * ((g, 1) : I.GA)) ∈ fund ∧ γ₂ * (x * ((g, 1) : I.GA)) ∈ fund from ⟨(γ : I.GA), γ.2, c, hc, hne, hγD, hcD⟩)`. Rewrite using `[← hγ]`.

Conclude with `hγs`. Establish `hP0 : x ∈ s ↔ x ∈ A`. Rewrite using `[hA, Set.mem_iUnion]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Use `⟨1, ?_, ?_⟩` and prove the remaining obligations. Use `show (1 : I.GA) * x ∈ s`. Rewrite using `[one_mul]`. Conclude with `h`. Use `show (1 : I.GA) * x ∈ fund`.

Rewrite using `[one_mul]`. Conclude with `hxD`. Introduce and unpack `⟨γ, hγs, hγD⟩`. Establish `hγ : (γ : I.GA) = 1`. Assume the negation of the conclusion as `hne`.

Conclude with `hx6 (show ∃ γ₁ ∈ Γ, ∃ γ₂ ∈ Γ, γ₁ ≠ γ₂ ∧ γ₁ * x ∈ fund ∧ γ₂ * x ∈ fund from ⟨(γ : I.GA), γ.2, 1, Γ.one_mem, hne, hγD, by rw [one_mul]; exact hxD⟩)`. Establish `hγs' : (γ : I.GA) * x ∈ s` using `hγs`. Rewrite `hγs'` using `[hγ, one_mul]`. Conclude with `hγs'`. Establish `hEx : x ∈ E g ↔ (x * ((g, 1) : I.GA) ∈ A ∧ x ∉ A ∨ x ∈ A ∧ x * ((g, 1) : I.GA) ∉ A)`.

Rewrite using `[hE]`. Simplify using `only [Set.mem_symmDiff, Set.mem_preimage]`. Apply the tactic sequence `by_cases h1 : c * (x * ((g, 1) : I.GA)) ∈ s <;> by_cases h0 : x ∈ s`. Simplify using `[Set.indicator_apply, h1, h0]`. Establish `hxE : x ∈ E g` using `hEx.mpr (Or.inl ⟨hP1.mp h1, fun h => h0 (hP0.mpr h)⟩)`.

Simplify using `[Set.indicator_apply, h1, h0, hxE]`. Establish `hxE : x ∈ E g` using `hEx.mpr (Or.inr ⟨hP0.mp h0, fun h => h1 (hP1.mpr h)⟩)`. Simplify using `[Set.indicator_apply, h1, h0, hxE]`. Simplify using `[Set.indicator_apply, h1, h0]`. Establish `hET : ∀ g : I.Ginf, (I.muA μf).restrict fund (E g) ≤ I.muA μf (T g)`.

Introduce `g`. Rewrite using `[Measure.restrict_apply' hfd.1]`. Establish `hsub : E g ∩ fund ⊆ ⋃ γ : Γ, fund ∩ (fun z => (γ : I.GA) * z) ⁻¹' T g`. Introduce and unpack `x ⟨hxE, hxD⟩`. Simplify using `only [hE, hA, hT, Set.mem_symmDiff, Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff] at hxE ⊢`.

Break down `hxE with ⟨⟨γ, hγs, hγD⟩, hno⟩ | ⟨⟨γ, hγs, hγD⟩, hno⟩` into its components or cases. Use `⟨γ, hxD, Or.inr ⟨⟨?_, ?_⟩, fun h => hno ⟨γ, h.1, h.2⟩⟩⟩` and prove the remaining obligations. Simplify `hγs` using `[mul_assoc]`. Simplify `hγD` using `[mul_assoc]`. Use `⟨γ, hxD, Or.inl ⟨⟨hγs, hγD⟩, fun h => hno ⟨γ, ?_, ?_⟩⟩⟩` and prove the remaining obligations.

Simplify `h.1` using `[mul_assoc]`. Simplify `h.2` using `[mul_assoc]`. Establish `heq : ∀ γ : Γ, I.muA μf (fund ∩ (fun z => (γ : I.GA) * z) ⁻¹' T g) = I.muA μf ((fun z => (γ : I.GA)⁻¹ * z) ⁻¹' fund ∩ T g)`. Introduce `γ`. Establish `hset : fund ∩ (fun z => (γ : I.GA) * z) ⁻¹' T g = (fun z => (γ : I.GA) * z) ⁻¹' ((fun z => (γ : I.GA)⁻¹ * z) ⁻¹' fund ∩ T g)`.

Use extensionality with `z`. Simplify using `only [Set.mem_inter_iff, Set.mem_preimage, inv_mul_cancel_left]`. Rewrite using `[hset, measure_preimage_mul]`. Establish `hd : Pairwise (fun γ γ' : Γ => AEDisjoint (I.muA μf) ((fun z => (γ : I.GA)⁻¹ * z) ⁻¹' fund ∩ T g) ((fun z => (γ' : I.GA)⁻¹ * z) ⁻¹' fund ∩ T g))`. Introduce `γ γ' hne`.

Use `measure_mono_null ?_ hN0` and prove the remaining obligations. Introduce and unpack `z ⟨⟨h1, -⟩, ⟨h2, -⟩⟩`. Use `show ∃ γ₁ ∈ Γ, ∃ γ₂ ∈ Γ, γ₁ ≠ γ₂ ∧ γ₁ * z ∈ fund ∧ γ₂ * z ∈ fund`. Conclude with `⟨(γ : I.GA)⁻¹, Γ.inv_mem γ.2, (γ' : I.GA)⁻¹, Γ.inv_mem γ'.2, fun heq => hne (Subtype.ext (inv_injective heq)), h1, h2⟩`. Establish `hm : ∀ γ : Γ, NullMeasurableSet ((fun z => (γ : I.GA)⁻¹ * z) ⁻¹' fund ∩ T g) (I.muA μf)` using `fun γ => ((hfd.1.preimage (measurable_const_mul _)).inter (hTm g)).nullMeasurableSet`.

Combine the equalities or inequalities in the displayed calculation. Establish `hTle : ∀ g : I.Ginf, I.muA μf (T g) ≤ I.muA μf ((s ∩ fund) \ (fun x => x * ((g, 1) : I.GA)) ⁻¹' (s ∩ fund)) + I.muA μf ((s ∩ fund) \ (fun x => x * ((g⁻¹, 1) : I.GA)) ⁻¹' (s ∩ fund))`. Introduce `g`. Rewrite using `[hT]`. Simplify using `only [Set.symmDiff_def]`.

Use `(measure_union_le _ _).trans (add_le_add le_rfl (le_of_eq ?_))` and prove the remaining obligations. Establish `hset : (fun x => x * ((g, 1) : I.GA)) ⁻¹' (s ∩ fund) \ (s ∩ fund) = (fun x => x * ((g, 1) : I.GA)) ⁻¹' ((s ∩ fund) \ (fun x => x * ((g⁻¹, 1) : I.GA)) ⁻¹' (s ∩ fund))`. Use extensionality with `x`. Establish `e : x * ((g, 1) : I.GA) * ((g⁻¹, 1) : I.GA) = x`. Establish `hgg : ((g, 1) : I.GA) * ((g⁻¹, 1) : I.GA) = 1` using `Prod.ext (by simp) (by simp)`.

Rewrite using `[mul_assoc, hgg, mul_one]`. Simplify using `only [Set.mem_diff, Set.mem_preimage, e]`. Rewrite using `[hset, rp_pre (rp_inst I μf g)]`. Establish `hδ` using `adele_tendsto I μf hs' hs'f`. Establish `hδ' : Tendsto (fun g : I.Ginf => I.muA μf ((s ∩ fund) \ (fun x => x * ((g⁻¹, 1) : I.GA)) ⁻¹' (s ∩ fund))) (𝓝 1) (𝓝 0)`.

Establish `hinv : Tendsto (fun g : I.Ginf => g⁻¹) (𝓝 1) (𝓝 1)`. Simplify using `using (continuous_inv.tendsto (1 : I.Ginf))`. Conclude with `hδ.comp hinv`. Establish `hf` using `hδ.add hδ'`. Rewrite `hf` using `[add_zero]`.

Establish `hE0 : Tendsto (fun g : I.Ginf => (I.muA μf).restrict fund (E g)) (𝓝 1) (𝓝 0)` using `tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hf (fun _ => zero_le) (fun g => (hET g).trans (hTle g))`. Establish `hr : (0 : ℝ) < 1 / (2 : ℝ≥0∞).toReal` using `by norm_num`. Establish `hpow : Tendsto (fun g : I.Ginf => ((I.muA μf).restrict fund (E g)) ^ (1 / (2 : ℝ≥0∞).toReal)) (𝓝 1) (𝓝 0)`. Establish `h0` using `(ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ≥0∞).toReal)).tendsto 0`. Rewrite `h0` using `[ENNReal.zero_rpow_of_pos hr]`.

Conclude with `h0.comp hE0`. Establish `hind : ∀ g : I.Ginf, eLpNorm ((E g).indicator fun _ => (1 : ℂ)) 2 ((I.muA μf).restrict fund) ≤ ((I.muA μf).restrict fund (E g)) ^ (1 / (2 : ℝ≥0∞).toReal)` using `fun g => (eLpNorm_indicator_const_le (1 : ℂ) 2).trans (by simp)`. Establish `he : Tendsto (fun g : I.Ginf => eLpNorm ⇑(R (g, 1) X - X) 2 ((I.muA μf).restrict fund)) (𝓝 1) (𝓝 0)` using `tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hpow (fun _ => zero_le) (fun g => (eLpNorm_mono_ae (hpt g)).trans (hind g))`. Rewrite using `[tendsto_iff_norm_sub_tendsto_zero]`. Establish `h2 : Tendsto (fun g : I.Ginf => (eLpNorm ⇑(R (g, 1) X - X) 2 ((I.muA μf).restrict fund)).toReal) (𝓝 1) (𝓝 0)`.

Establish `h3` using `(ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp he`. Use `first`. Consider the case `rw [ENNReal.zero_toReal] at h3`. Consider the case `rw [ENNReal.toReal_zero] at h3`. Consider the case `simp only [ENNReal.zero_toReal] at h3`.

Conclude with `h3`. Use `h2.congr (fun g => ?_)` and prove the remaining obligations. Conclude with `(Lp.norm_def _).symm`.
-/
theorem ind_tendsto {s : Set I.GA} (hs : MeasurableSet s) (hμs : (I.muA μf).restrict fund s ≠ ∞) :
    Tendsto (fun g : I.Ginf => R (g, 1) (indicatorConstLp 2 hs hμs (1 : ℂ))) (𝓝 1)
      (𝓝 (indicatorConstLp 2 hs hμs (1 : ℂ))) := by
  have hdet : ∀ v, IsUnit (I.P v).det := fun v => (Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit v)
  have key : ∀ (P A B : Matrix (Fin I.n) (Fin I.n) ℂ), IsUnit P.det →
      P⁻¹ * A * P * (P⁻¹ * B * P) = P⁻¹ * (A * B) * P := by
    intro P A B hP
    calc P⁻¹ * A * P * (P⁻¹ * B * P) = P⁻¹ * A * (P * P⁻¹) * B * P := by simp only [Matrix.mul_assoc]
      _ = P⁻¹ * (A * B) * P := by
        rw [Matrix.mul_nonsing_inv _ hP, Matrix.mul_one, Matrix.mul_assoc (P⁻¹) A B]
  have h1 : (1 : I.GA) ∈ I.GFset := by
    simp only [AutInst.GFset, Set.mem_setOf_eq]
    refine ⟨1, (Formalism.UG.UJ (starRingEnd I.E) I.J).one_mem, fun v => ?_, ?_⟩
    · simp [uMat, Matrix.nonsing_inv_mul _ (hdet v)]
    · simp [AutInst.fmat]
  have hmul : ∀ {a b : I.GA}, a ∈ I.GFset → b ∈ I.GFset → a * b ∈ I.GFset := by
    intro a b ha hb
    simp only [AutInst.GFset, Set.mem_setOf_eq] at ha hb ⊢
    obtain ⟨γ₁, hγ₁, hu₁, hf₁⟩ := ha
    obtain ⟨γ₂, hγ₂, hu₂, hf₂⟩ := hb
    refine ⟨γ₁ * γ₂, (Formalism.UG.UJ (starRingEnd I.E) I.J).mul_mem hγ₁ hγ₂, fun v => ?_, ?_⟩
    · have e : uMat ((a * b).1 v) = uMat (a.1 v) * uMat (b.1 v) := by simp [uMat]
      rw [e, hu₁ v, hu₂ v, key _ _ _ (hdet v), Units.val_mul, Matrix.map_mul]
    · have e : I.fmat (a * b).2 = I.fmat a.2 * I.fmat b.2 := by simp [AutInst.fmat]
      rw [e, hf₁, hf₂, Units.val_mul, Matrix.map_mul]
  have hinv : ∀ {a : I.GA}, a ∈ I.GFset → a⁻¹ ∈ I.GFset := by
    intro a ha
    simp only [AutInst.GFset, Set.mem_setOf_eq] at ha ⊢
    obtain ⟨γ, hγ, hu, hf⟩ := ha
    refine ⟨γ⁻¹, (Formalism.UG.UJ (starRingEnd I.E) I.J).inv_mem hγ, fun v => ?_, ?_⟩
    · have hM : uMat (a.1 v) * uMat (a⁻¹.1 v) = 1 := by simp [uMat]
      rw [← Matrix.inv_eq_right_inv hM]
      apply Matrix.inv_eq_right_inv
      rw [hu v, key _ _ _ (hdet v), ← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one, Matrix.nonsing_inv_mul _ (hdet v)]
    · have hM : I.fmat a.2 * I.fmat a⁻¹.2 = 1 := by simp [AutInst.fmat]
      rw [← Matrix.inv_eq_right_inv hM]
      apply Matrix.inv_eq_right_inv
      rw [hf, ← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.map_one _ (map_zero _) (map_one _)]
  let Γ : Subgroup I.GA :=
    { carrier := I.GFset
      mul_mem' := hmul
      one_mem' := h1
      inv_mem' := hinv }
  haveI hEc : Countable I.E := (Module.finBasis ℚ I.E).equivFun.injective.countable
  haveI hGLc : Countable (GL (Fin I.n) I.E) := by
    refine Function.Injective.countable
      (f := fun u : GL (Fin I.n) I.E => fun i j => (u : Matrix (Fin I.n) (Fin I.n) I.E) i j) ?_
    intro u w huw
    exact Units.ext (Matrix.ext fun i j => congrFun (congrFun huw i) j)
  haveI hΓc : Countable Γ := by
    refine Function.Injective.countable (f := fun x : Γ => Classical.choose x.2) ?_
    intro x y hxy
    have hxy' : Classical.choose x.2 = Classical.choose y.2 := hxy
    have sx := Classical.choose_spec x.2
    have sy := Classical.choose_spec y.2
    rw [hxy'] at sx
    apply Subtype.ext
    apply Prod.ext
    · funext v
      apply Subtype.ext
      apply Units.ext
      exact (sx.2.1 v).trans (sy.2.1 v).symm
    · apply Subtype.ext
      apply Units.ext
      exact sx.2.2.trans sy.2.2.symm
  haveI hli : (I.muA μf).IsMulLeftInvariant := by
    unfold AutInst.muA
    first
    | infer_instance
    | (unfold Formalism.REAL.muG; infer_instance)
  have hFD : rr_FD (I.muA μf) Γ fund := ⟨hfd.1, hfd.2.1, hfd.2.2⟩
  have hReg : rr_IsReg (I.muA μf) Γ fund R := by
    intro g' F'
    first
    | exact hR g' F'
    | (filter_upwards [hR g' F'] with x hx; rw [hx]; rfl)
  classical
  have hrep : ∀ y : I.GA, ∃ c ∈ Γ, rr_rep (Γ : Set I.GA) fund y = c * y ∧ c * y ∈ fund := by
    intro y
    have hex : ∃ γ ∈ (Γ : Set I.GA), γ * y ∈ fund := hFD.cov y
    refine ⟨hex.choose, hex.choose_spec.1, ?_, hex.choose_spec.2⟩
    unfold rr_rep
    first
    | exact dif_pos hex
    | rw [dif_pos hex]
    | simp only [dif_pos hex]
  have hN0 : I.muA μf (rr_N Γ fund) = 0 := by
    have h0 := rp_N_pre hFD (rp_inst I μf 1)
    have e1 : (fun x : I.GA => x * (((1 : I.Ginf), (1 : I.Gf)) : I.GA)) = id :=
      funext fun x => mul_one x
    first
    | (rw [e1, Set.preimage_id] at h0; exact h0)
    | simpa using h0
  have hs' : MeasurableSet (s ∩ fund) := hs.inter hfd.1
  have hs'f : I.muA μf (s ∩ fund) ≠ ∞ := by
    rw [← Measure.restrict_apply hs]
    exact hμs
  set A : Set I.GA := ⋃ γ : Γ, (fun z => (γ : I.GA) * z) ⁻¹' (s ∩ fund) with hA
  set X : I.L2 μf fund := indicatorConstLp 2 hs hμs (1 : ℂ) with hX
  set E : I.Ginf → Set I.GA := fun g => ((fun z => z * ((g, 1) : I.GA)) ⁻¹' A) ∆ A with hE
  set T : I.Ginf → Set I.GA :=
    fun g => (s ∩ fund) ∆ ((fun z => z * ((g, 1) : I.GA)) ⁻¹' (s ∩ fund)) with hT
  have hTm : ∀ g : I.Ginf, MeasurableSet (T g) := fun g => by
    rw [hT]
    exact hs'.symmDiff (hs'.preimage (measurable_mul_const _))
  have hpt : ∀ g : I.Ginf, ∀ᵐ x ∂(I.muA μf).restrict fund,
      ‖((R (g, 1) X - X : I.L2 μf fund) : I.GA → ℂ) x‖ ≤ ‖(E g).indicator (fun _ => (1 : ℂ)) x‖ := by
    intro g
    obtain ⟨hmeas, hmap⟩ := rp_map hFD (rp_inst I μf g) (rp_inst_inv I μf g)
    have hXs : ⇑X =ᵐ[(I.muA μf).restrict fund] s.indicator fun _ => (1 : ℂ) := by
      rw [hX]
      exact indicatorConstLp_coeFn
    have F3 : ∀ᵐ x ∂(I.muA μf).restrict fund,
        X (rr_rep (Γ : Set I.GA) fund (x * ((g, 1) : I.GA))) =
          s.indicator (fun _ => (1 : ℂ)) (rr_rep (Γ : Set I.GA) fund (x * ((g, 1) : I.GA))) :=
      ae_of_ae_map (p := fun y => X y = s.indicator (fun _ => (1 : ℂ)) y) hmeas
        (by rw [hmap]; exact hXs)
    have F7 : ∀ᵐ x ∂(I.muA μf).restrict fund, x * ((g, 1) : I.GA) ∉ rr_N Γ fund := by
      refine ae_restrict_of_ae ?_
      filter_upwards [compl_mem_ae_iff.mpr (rp_N_pre hFD (rp_inst I μf g))] with x hx
      first
      | simpa only [Set.mem_compl_iff, Set.mem_preimage] using hx
      | exact hx
    have F6 : ∀ᵐ x ∂(I.muA μf).restrict fund, x ∉ rr_N Γ fund := by
      refine ae_restrict_of_ae ?_
      filter_upwards [compl_mem_ae_iff.mpr hN0] with x hx
      first
      | simpa only [Set.mem_compl_iff] using hx
      | exact hx
    filter_upwards [Lp.coeFn_sub (R (g, 1) X) X, hReg (g, 1) X, F3, hXs, ae_restrict_mem hfd.1, F6, F7]
      with x e1 e2 e3 e4 hxD hx6 hx7
    rw [e1]
    first
    | rw [Pi.sub_apply]
    | skip
    rw [e2, e3, e4]
    obtain ⟨c, hc, hcy, hcD⟩ := hrep (x * ((g, 1) : I.GA))
    rw [hcy]
    have hP1 : c * (x * ((g, 1) : I.GA)) ∈ s ↔ x * ((g, 1) : I.GA) ∈ A := by
      rw [hA, Set.mem_iUnion]
      constructor
      · intro h
        exact ⟨⟨c, hc⟩, h, hcD⟩
      · rintro ⟨γ, hγs, hγD⟩
        have hγ : (γ : I.GA) = c := by
          by_contra hne
          exact hx7 (show ∃ γ₁ ∈ Γ, ∃ γ₂ ∈ Γ, γ₁ ≠ γ₂ ∧ γ₁ * (x * ((g, 1) : I.GA)) ∈ fund ∧
            γ₂ * (x * ((g, 1) : I.GA)) ∈ fund from ⟨(γ : I.GA), γ.2, c, hc, hne, hγD, hcD⟩)
        rw [← hγ]
        exact hγs
    have hP0 : x ∈ s ↔ x ∈ A := by
      rw [hA, Set.mem_iUnion]
      constructor
      · intro h
        refine ⟨1, ?_, ?_⟩
        · show (1 : I.GA) * x ∈ s
          rw [one_mul]
          exact h
        · show (1 : I.GA) * x ∈ fund
          rw [one_mul]
          exact hxD
      · rintro ⟨γ, hγs, hγD⟩
        have hγ : (γ : I.GA) = 1 := by
          by_contra hne
          exact hx6 (show ∃ γ₁ ∈ Γ, ∃ γ₂ ∈ Γ, γ₁ ≠ γ₂ ∧ γ₁ * x ∈ fund ∧ γ₂ * x ∈ fund from
            ⟨(γ : I.GA), γ.2, 1, Γ.one_mem, hne, hγD, by rw [one_mul]; exact hxD⟩)
        have hγs' : (γ : I.GA) * x ∈ s := hγs
        rw [hγ, one_mul] at hγs'
        exact hγs'
    have hEx : x ∈ E g ↔ (x * ((g, 1) : I.GA) ∈ A ∧ x ∉ A ∨ x ∈ A ∧ x * ((g, 1) : I.GA) ∉ A) := by
      rw [hE]
      simp only [Set.mem_symmDiff, Set.mem_preimage]
    by_cases h1 : c * (x * ((g, 1) : I.GA)) ∈ s <;> by_cases h0 : x ∈ s
    · simp [Set.indicator_apply, h1, h0]
    · have hxE : x ∈ E g := hEx.mpr (Or.inl ⟨hP1.mp h1, fun h => h0 (hP0.mpr h)⟩)
      simp [Set.indicator_apply, h1, h0, hxE]
    · have hxE : x ∈ E g := hEx.mpr (Or.inr ⟨hP0.mp h0, fun h => h1 (hP1.mpr h)⟩)
      simp [Set.indicator_apply, h1, h0, hxE]
    · simp [Set.indicator_apply, h1, h0]
  have hET : ∀ g : I.Ginf, (I.muA μf).restrict fund (E g) ≤ I.muA μf (T g) := by
    intro g
    rw [Measure.restrict_apply' hfd.1]
    have hsub : E g ∩ fund ⊆ ⋃ γ : Γ, fund ∩ (fun z => (γ : I.GA) * z) ⁻¹' T g := by
      rintro x ⟨hxE, hxD⟩
      simp only [hE, hA, hT, Set.mem_symmDiff, Set.mem_preimage, Set.mem_iUnion,
        Set.mem_inter_iff] at hxE ⊢
      rcases hxE with ⟨⟨γ, hγs, hγD⟩, hno⟩ | ⟨⟨γ, hγs, hγD⟩, hno⟩
      · refine ⟨γ, hxD, Or.inr ⟨⟨?_, ?_⟩, fun h => hno ⟨γ, h.1, h.2⟩⟩⟩
        · simpa [mul_assoc] using hγs
        · simpa [mul_assoc] using hγD
      · refine ⟨γ, hxD, Or.inl ⟨⟨hγs, hγD⟩, fun h => hno ⟨γ, ?_, ?_⟩⟩⟩
        · simpa [mul_assoc] using h.1
        · simpa [mul_assoc] using h.2
    have heq : ∀ γ : Γ, I.muA μf (fund ∩ (fun z => (γ : I.GA) * z) ⁻¹' T g)
        = I.muA μf ((fun z => (γ : I.GA)⁻¹ * z) ⁻¹' fund ∩ T g) := by
      intro γ
      have hset : fund ∩ (fun z => (γ : I.GA) * z) ⁻¹' T g
          = (fun z => (γ : I.GA) * z) ⁻¹' ((fun z => (γ : I.GA)⁻¹ * z) ⁻¹' fund ∩ T g) := by
        ext z
        simp only [Set.mem_inter_iff, Set.mem_preimage, inv_mul_cancel_left]
      rw [hset, measure_preimage_mul]
    have hd : Pairwise (fun γ γ' : Γ => AEDisjoint (I.muA μf)
        ((fun z => (γ : I.GA)⁻¹ * z) ⁻¹' fund ∩ T g) ((fun z => (γ' : I.GA)⁻¹ * z) ⁻¹' fund ∩ T g)) := by
      intro γ γ' hne
      refine measure_mono_null ?_ hN0
      rintro z ⟨⟨h1, -⟩, ⟨h2, -⟩⟩
      show ∃ γ₁ ∈ Γ, ∃ γ₂ ∈ Γ, γ₁ ≠ γ₂ ∧ γ₁ * z ∈ fund ∧ γ₂ * z ∈ fund
      exact ⟨(γ : I.GA)⁻¹, Γ.inv_mem γ.2, (γ' : I.GA)⁻¹, Γ.inv_mem γ'.2,
        fun heq => hne (Subtype.ext (inv_injective heq)), h1, h2⟩
    have hm : ∀ γ : Γ, NullMeasurableSet ((fun z => (γ : I.GA)⁻¹ * z) ⁻¹' fund ∩ T g) (I.muA μf) :=
      fun γ => ((hfd.1.preimage (measurable_const_mul _)).inter (hTm g)).nullMeasurableSet
    calc I.muA μf (E g ∩ fund)
        ≤ I.muA μf (⋃ γ : Γ, fund ∩ (fun z => (γ : I.GA) * z) ⁻¹' T g) := measure_mono hsub
      _ ≤ ∑' γ : Γ, I.muA μf (fund ∩ (fun z => (γ : I.GA) * z) ⁻¹' T g) := measure_iUnion_le _
      _ = ∑' γ : Γ, I.muA μf ((fun z => (γ : I.GA)⁻¹ * z) ⁻¹' fund ∩ T g) := tsum_congr heq
      _ = I.muA μf (⋃ γ : Γ, (fun z => (γ : I.GA)⁻¹ * z) ⁻¹' fund ∩ T g) := (measure_iUnion₀ hd hm).symm
      _ ≤ I.muA μf (T g) := measure_mono (Set.iUnion_subset fun γ x hx => hx.2)
  have hTle : ∀ g : I.Ginf, I.muA μf (T g) ≤
      I.muA μf ((s ∩ fund) \ (fun x => x * ((g, 1) : I.GA)) ⁻¹' (s ∩ fund)) +
      I.muA μf ((s ∩ fund) \ (fun x => x * ((g⁻¹, 1) : I.GA)) ⁻¹' (s ∩ fund)) := by
    intro g
    rw [hT]
    simp only [Set.symmDiff_def]
    refine (measure_union_le _ _).trans (add_le_add le_rfl (le_of_eq ?_))
    have hset : (fun x => x * ((g, 1) : I.GA)) ⁻¹' (s ∩ fund) \ (s ∩ fund)
        = (fun x => x * ((g, 1) : I.GA)) ⁻¹'
            ((s ∩ fund) \ (fun x => x * ((g⁻¹, 1) : I.GA)) ⁻¹' (s ∩ fund)) := by
      ext x
      have e : x * ((g, 1) : I.GA) * ((g⁻¹, 1) : I.GA) = x := by
        have hgg : ((g, 1) : I.GA) * ((g⁻¹, 1) : I.GA) = 1 := Prod.ext (by simp) (by simp)
        rw [mul_assoc, hgg, mul_one]
      simp only [Set.mem_diff, Set.mem_preimage, e]
    rw [hset, rp_pre (rp_inst I μf g)]
  have hδ := adele_tendsto I μf hs' hs'f
  have hδ' : Tendsto (fun g : I.Ginf =>
      I.muA μf ((s ∩ fund) \ (fun x => x * ((g⁻¹, 1) : I.GA)) ⁻¹' (s ∩ fund))) (𝓝 1) (𝓝 0) := by
    have hinv : Tendsto (fun g : I.Ginf => g⁻¹) (𝓝 1) (𝓝 1) := by
      simpa using (continuous_inv.tendsto (1 : I.Ginf))
    exact hδ.comp hinv
  have hf := hδ.add hδ'
  rw [add_zero] at hf
  have hE0 : Tendsto (fun g : I.Ginf => (I.muA μf).restrict fund (E g)) (𝓝 1) (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hf (fun _ => zero_le)
      (fun g => (hET g).trans (hTle g))
  have hr : (0 : ℝ) < 1 / (2 : ℝ≥0∞).toReal := by norm_num
  have hpow : Tendsto (fun g : I.Ginf =>
      ((I.muA μf).restrict fund (E g)) ^ (1 / (2 : ℝ≥0∞).toReal)) (𝓝 1) (𝓝 0) := by
    have h0 := (ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ≥0∞).toReal)).tendsto 0
    rw [ENNReal.zero_rpow_of_pos hr] at h0
    exact h0.comp hE0
  have hind : ∀ g : I.Ginf, eLpNorm ((E g).indicator fun _ => (1 : ℂ)) 2 ((I.muA μf).restrict fund)
      ≤ ((I.muA μf).restrict fund (E g)) ^ (1 / (2 : ℝ≥0∞).toReal) := fun g =>
    (eLpNorm_indicator_const_le (1 : ℂ) 2).trans (by simp)
  have he : Tendsto (fun g : I.Ginf =>
      eLpNorm ⇑(R (g, 1) X - X) 2 ((I.muA μf).restrict fund)) (𝓝 1) (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hpow (fun _ => zero_le)
      (fun g => (eLpNorm_mono_ae (hpt g)).trans (hind g))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h2 : Tendsto (fun g : I.Ginf =>
      (eLpNorm ⇑(R (g, 1) X - X) 2 ((I.muA μf).restrict fund)).toReal) (𝓝 1) (𝓝 0) := by
    have h3 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp he
    first
    | rw [ENNReal.zero_toReal] at h3
    | rw [ENNReal.toReal_zero] at h3
    | simp only [ENNReal.zero_toReal] at h3
    exact h3
  refine h2.congr (fun g => ?_)
  exact (Lp.norm_def _).symm

include hfd hR in

/- English proof (translation)
Establish `hiso : ∀ (g : I.Ginf) (H : I.L2 μf fund), ‖R (g, 1) H‖ = ‖H‖` using `fun g H => reg_norm I μf fund hfd R hR g H`. Establish `hsm : ∀ (c : ℂ) (H : I.L2 μf fund), Tendsto (fun g : I.Ginf => R (g, 1) H) (𝓝 1) (𝓝 H) → Tendsto (fun g : I.Ginf => R (g, 1) (c • H)) (𝓝 1) (𝓝 (c • H))`. Introduce `c H hH`. Simplify using `only [map_smul]`. Conclude with `hH.const_smul c`.

Use `Lp.induction (p := 2) (by simp) (fun H => Tendsto (fun g : I.Ginf => R (g, 1) H) (𝓝 1) (𝓝 H)) ?_ ?_ ?_ F` and prove the remaining obligations. Introduce `c s hs hμs`. Establish `hμs' : (I.muA μf).restrict fund s ≠ ∞` using `hμs.ne`. Establish `hX : indicatorConstLp 2 hs hμs' c = c • indicatorConstLp 2 hs hμs' (1 : ℂ)`. Apply `Lp.ext` to reduce the goal to its premises.

Establish `h1 : ⇑(indicatorConstLp 2 hs hμs' c) =ᵐ[(I.muA μf).restrict fund] s.indicator fun _ => c` using `indicatorConstLp_coeFn`. Establish `h2` using `Lp.coeFn_smul c (indicatorConstLp 2 hs hμs' (1 : ℂ))`. Establish `h3 : ⇑(indicatorConstLp 2 hs hμs' (1 : ℂ)) =ᵐ[(I.muA μf).restrict fund] s.indicator fun _ => (1 : ℂ)` using `indicatorConstLp_coeFn`. Use `filter_upwards [h1, h2, h3] with x e1 e2 e3`. Rewrite using `[e1, e2]`.

Apply the tactic sequence `by_cases hx : x ∈ s <;> simp [hx, e3]`. Establish `key` using `hsm c _ (ind_tendsto I μf fund hfd R hR hs hμs')`. Rewrite `key` using `[← hX]`. Conclude with `key`. Introduce `f₁ f₂ hf₁ hf₂ _ hP₁ hP₂`.

Establish `t₁ : Tendsto (fun g : I.Ginf => R (g, 1) (hf₁.toLp f₁)) (𝓝 1) (𝓝 (hf₁.toLp f₁))` using `hP₁`. Establish `t₂ : Tendsto (fun g : I.Ginf => R (g, 1) (hf₂.toLp f₂)) (𝓝 1) (𝓝 (hf₂.toLp f₂))` using `hP₂`. Use `show Tendsto (fun g : I.Ginf => R (g, 1) (hf₁.toLp f₁ + hf₂.toLp f₂)) (𝓝 1) (𝓝 (hf₁.toLp f₁ + hf₂.toLp f₂))`. Simplify using `only [map_add]`. Conclude with `t₁.add t₂`.

Apply `isClosed_of_closure_subset` to reduce the goal to its premises. Introduce `H hH`. Rewrite `hH` using `[Metric.mem_closure_iff]`. Use `show Tendsto (fun g : I.Ginf => R (g, 1) H) (𝓝 1) (𝓝 H)`. Rewrite using `[Metric.tendsto_nhds]`.

Introduce `ε hε`. Take `⟨H', hH', hd⟩` from `hH (ε / 3) (by positivity)`. Establish `t : Tendsto (fun g : I.Ginf => R (g, 1) H') (𝓝 1) (𝓝 H')` using `hH'`. Use `filter_upwards [Metric.tendsto_nhds.mp t (ε / 3) (by positivity)] with g hg`. Establish `hR' : dist (R (g, 1) H) (R (g, 1) H') = dist H H'`.

Rewrite using `[dist_eq_norm, dist_eq_norm, ← map_sub, hiso]`. Establish `h3` using `dist_triangle4 (R (g, 1) H) (R (g, 1) H') H' H`. Rewrite `h3` using `[hR', dist_comm H' H]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem all_tendsto (F : I.L2 μf fund) : Tendsto (fun g : I.Ginf => R (g, 1) F) (𝓝 1) (𝓝 F) := by
  have hiso : ∀ (g : I.Ginf) (H : I.L2 μf fund), ‖R (g, 1) H‖ = ‖H‖ :=
    fun g H => reg_norm I μf fund hfd R hR g H
  have hsm : ∀ (c : ℂ) (H : I.L2 μf fund), Tendsto (fun g : I.Ginf => R (g, 1) H) (𝓝 1) (𝓝 H) →
      Tendsto (fun g : I.Ginf => R (g, 1) (c • H)) (𝓝 1) (𝓝 (c • H)) := by
    intro c H hH
    simp only [map_smul]
    exact hH.const_smul c
  refine Lp.induction (p := 2) (by simp)
    (fun H => Tendsto (fun g : I.Ginf => R (g, 1) H) (𝓝 1) (𝓝 H)) ?_ ?_ ?_ F
  · intro c s hs hμs
    have hμs' : (I.muA μf).restrict fund s ≠ ∞ := hμs.ne
    have hX : indicatorConstLp 2 hs hμs' c = c • indicatorConstLp 2 hs hμs' (1 : ℂ) := by
      apply Lp.ext
      have h1 : ⇑(indicatorConstLp 2 hs hμs' c) =ᵐ[(I.muA μf).restrict fund] s.indicator fun _ => c :=
        indicatorConstLp_coeFn
      have h2 := Lp.coeFn_smul c (indicatorConstLp 2 hs hμs' (1 : ℂ))
      have h3 : ⇑(indicatorConstLp 2 hs hμs' (1 : ℂ)) =ᵐ[(I.muA μf).restrict fund]
          s.indicator fun _ => (1 : ℂ) :=
        indicatorConstLp_coeFn
      filter_upwards [h1, h2, h3] with x e1 e2 e3
      rw [e1, e2]
      by_cases hx : x ∈ s <;> simp [hx, e3]
    have key := hsm c _ (ind_tendsto I μf fund hfd R hR hs hμs')
    rw [← hX] at key
    exact key
  · intro f₁ f₂ hf₁ hf₂ _ hP₁ hP₂
    have t₁ : Tendsto (fun g : I.Ginf => R (g, 1) (hf₁.toLp f₁)) (𝓝 1) (𝓝 (hf₁.toLp f₁)) := hP₁
    have t₂ : Tendsto (fun g : I.Ginf => R (g, 1) (hf₂.toLp f₂)) (𝓝 1) (𝓝 (hf₂.toLp f₂)) := hP₂
    show Tendsto (fun g : I.Ginf => R (g, 1) (hf₁.toLp f₁ + hf₂.toLp f₂)) (𝓝 1)
      (𝓝 (hf₁.toLp f₁ + hf₂.toLp f₂))
    simp only [map_add]
    exact t₁.add t₂
  · apply isClosed_of_closure_subset
    intro H hH
    rw [Metric.mem_closure_iff] at hH
    show Tendsto (fun g : I.Ginf => R (g, 1) H) (𝓝 1) (𝓝 H)
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨H', hH', hd⟩ := hH (ε / 3) (by positivity)
    have t : Tendsto (fun g : I.Ginf => R (g, 1) H') (𝓝 1) (𝓝 H') := hH'
    filter_upwards [Metric.tendsto_nhds.mp t (ε / 3) (by positivity)] with g hg
    have hR' : dist (R (g, 1) H) (R (g, 1) H') = dist H H' := by
      rw [dist_eq_norm, dist_eq_norm, ← map_sub, hiso]
    have h3 := dist_triangle4 (R (g, 1) H) (R (g, 1) H') H' H
    rw [hR', dist_comm H' H] at h3
    linarith

end Main

/- English proof (translation)
Unfold `Formalism.L2.SG.ProjRows.RegUnitary`. Introduce `I μf _ _ fund hfd R hR`. Unfold `Formalism.L2.SG.ProjRows.IsURep`. Use `⟨?_, fun a b => reg_mul I μf fund hfd R hR a b, fun g v => reg_norm I μf fund hfd R hR g v, fun v => ?_⟩` and prove the remaining obligations. Establish `hmul` using `reg_mul I μf fund hfd R hR 1 1`.

Rewrite `hmul` using `[one_mul]`. Use `ext1 F`. Establish `h0 : R (1, 1) (R (1, 1) F - F) = 0`. Rewrite using `[map_sub, ← ContinuousLinearMap.comp_apply, ← hmul, sub_self]`. Establish `hn` using `reg_norm I μf fund hfd R hR 1 (R (1, 1) F - F)`.

Rewrite `hn` using `[h0, norm_zero]`. Establish `hz : R (1, 1) F - F = 0` using `norm_eq_zero.mp hn.symm`. Conclude with `sub_eq_zero.mp hz`. Use `show Continuous fun g => R (g, 1) v`. Rewrite using `[continuous_iff_continuousAt]`.

Introduce `g₀`. Establish `h1 : Tendsto (fun g : I.Ginf => g₀⁻¹ * g) (𝓝 g₀) (𝓝 1)`. Simplify using `using (continuous_mul_left g₀⁻¹).tendsto g₀`. Establish `h4` using `((R (g₀, 1)).continuous.tendsto v).comp ((all_tendsto I μf fund hfd R hR v).comp h1)`. Use `show Tendsto (fun g => R (g, 1) v) (𝓝 g₀) (𝓝 (R (g₀, 1) v))`.

Use `h4.congr (fun g => ?_)` and prove the remaining obligations. Simplify using `only [Function.comp_apply]`. Rewrite using `[← ContinuousLinearMap.comp_apply, ← reg_mul I μf fund hfd R hR, mul_inv_cancel_left]`.
-/
theorem regular_representation_unitary : Formalism.L2.SG.ProjRows.RegUnitary := by
  unfold Formalism.L2.SG.ProjRows.RegUnitary
  intro I μf _ _ fund hfd R hR
  unfold Formalism.L2.SG.ProjRows.IsURep
  refine ⟨?_, fun a b => reg_mul I μf fund hfd R hR a b, fun g v => reg_norm I μf fund hfd R hR g v,
    fun v => ?_⟩
  · have hmul := reg_mul I μf fund hfd R hR 1 1
    rw [one_mul] at hmul
    ext1 F
    have h0 : R (1, 1) (R (1, 1) F - F) = 0 := by
      rw [map_sub, ← ContinuousLinearMap.comp_apply, ← hmul, sub_self]
    have hn := reg_norm I μf fund hfd R hR 1 (R (1, 1) F - F)
    rw [h0, norm_zero] at hn
    have hz : R (1, 1) F - F = 0 := norm_eq_zero.mp hn.symm
    exact sub_eq_zero.mp hz
  · show Continuous fun g => R (g, 1) v
    rw [continuous_iff_continuousAt]
    intro g₀
    have h1 : Tendsto (fun g : I.Ginf => g₀⁻¹ * g) (𝓝 g₀) (𝓝 1) := by
      simpa using (continuous_mul_left g₀⁻¹).tendsto g₀
    have h4 := ((R (g₀, 1)).continuous.tendsto v).comp ((all_tendsto I μf fund hfd R hR v).comp h1)
    show Tendsto (fun g => R (g, 1) v) (𝓝 g₀) (𝓝 (R (g₀, 1) v))
    refine h4.congr (fun g => ?_)
    simp only [Function.comp_apply]
    rw [← ContinuousLinearMap.comp_apply, ← reg_mul I μf fund hfd R hR, mul_inv_cancel_left]

end Formalism.L2.SG.Pf
