import Mathlib

namespace GlobalTheory

/- English proof (translation)
Set `c : G → Set G` to `fun δ => {δ' | IsConj δ δ'}`. Establish `hsum : HasSum g (∑' δ, g δ)` using `(summable_of_finite_support hg).hasSum`. Establish `h1` using `hsum.tsum_fiberwise c`. Establish `hfib : ∀ γ : G, c ⁻¹' {c γ} = c γ`. Introduce `γ`.

Use extensionality with `b`. Simplify using `only [c, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `: b ∈ {δ' | IsConj b δ'}` using `IsConj.refl b`.

Rewrite `this` using `[h]`. Conclude with `this`. Introduce `h`. Use extensionality with `x`. Simplify using `only [Set.mem_setOf_eq]`.

Conclude with `⟨fun hx => h.trans hx, fun hx => h.symm.trans hx⟩`. Establish `hsupp : Function.support (fun s : Set G => ∑' b : c ⁻¹' {s}, g b) ⊆ {s | ∃ γ, R γ ∧ s = {δ | IsConj γ δ}}`. Introduce `s hs`. Assume the negation of the conclusion as `hns`. Apply `hs` to reduce the goal to its premises.

Establish `: ∀ b : c ⁻¹' {s}, g b = 0`. Introduce `⟨b, hb⟩`. Assume the negation of the conclusion as `hgb`. Conclude with `hns ⟨b, hR b hgb, (hb : c b = s).symm⟩`. Simplify using `[this]`.

Rewrite `h1` using `[← hasSum_subtype_iff_of_support_subset hsupp]`. Establish `key : (fun i : {𝔬 : Set G // ∃ γ, R γ ∧ 𝔬 = {δ | IsConj γ δ}} => ∑' δ : i.1, g δ) = fun i => (fun s : Set G => ∑' b : c ⁻¹' {s}, g b) i.1`. Use function extensionality and compare the values at `i`. Take `⟨s, γ, _, hs⟩` from `i`. Substitute `hs` using the available equality.

Simplify using `only`. Rewrite using `[show c ⁻¹' {{δ | IsConj γ δ}} = {δ | IsConj γ δ} from hfib γ]`. Rewrite using `[key]`. Conclude with `h1`.
-/
theorem hasSum_conjClasses_tsum_of_finite_support {G : Type} [Group G] (g : G → ℂ) (hg : (Function.support g).Finite)
    (R : G → Prop) (hR : ∀ δ, g δ ≠ 0 → R δ) :
    HasSum (fun i : {𝔬 : Set G // ∃ γ, R γ ∧ 𝔬 = {δ | IsConj γ δ}} => ∑' δ : i.1, g δ)
      (∑' δ, g δ) := by
  classical
  let c : G → Set G := fun δ => {δ' | IsConj δ δ'}
  have hsum : HasSum g (∑' δ, g δ) := (summable_of_finite_support hg).hasSum
  have h1 := hsum.tsum_fiberwise c
  have hfib : ∀ γ : G, c ⁻¹' {c γ} = c γ := by
    intro γ; ext b
    simp only [c, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]
    constructor
    · intro h
      have : b ∈ {δ' | IsConj b δ'} := IsConj.refl b
      rw [h] at this; exact this
    · intro h; ext x; simp only [Set.mem_setOf_eq]
      exact ⟨fun hx => h.trans hx, fun hx => h.symm.trans hx⟩
  have hsupp : Function.support (fun s : Set G => ∑' b : c ⁻¹' {s}, g b)
      ⊆ {s | ∃ γ, R γ ∧ s = {δ | IsConj γ δ}} := by
    intro s hs
    by_contra hns
    apply hs
    have : ∀ b : c ⁻¹' {s}, g b = 0 := by
      intro ⟨b, hb⟩
      by_contra hgb
      exact hns ⟨b, hR b hgb, (hb : c b = s).symm⟩
    simp [this]
  rw [← hasSum_subtype_iff_of_support_subset hsupp] at h1
  have key : (fun i : {𝔬 : Set G // ∃ γ, R γ ∧ 𝔬 = {δ | IsConj γ δ}} => ∑' δ : i.1, g δ)
      = fun i => (fun s : Set G => ∑' b : c ⁻¹' {s}, g b) i.1 := by
    funext i
    obtain ⟨s, γ, _, hs⟩ := i
    subst hs
    dsimp only
    rw [show c ⁻¹' {{δ | IsConj γ δ}} = {δ | IsConj γ δ} from hfib γ]
  rw [key]; exact h1

/- English proof (translation)
Introduce `G _ g hg R P hR hP`. Use `⟨hasSum_conjClasses_tsum_of_finite_support g hg R hR, ?_⟩` and prove the remaining obligations. Set `g' : G → ℂ` to `fun δ => if P δ then g δ else 0`. Establish `hg' : (Function.support g').Finite`. Use `hg.subset ?_` and prove the remaining obligations.

Introduce `δ h`. Apply the tactic sequence `by_cases hp : P δ <;> simp_all [g']`. Establish `hR' : ∀ δ, g' δ ≠ 0 → R δ`. Apply the tactic sequence `intro δ h; apply hR; by_cases hp : P δ <;> simp_all [g']`. Establish `H` using `hasSum_conjClasses_tsum_of_finite_support g' hg' R hR'`.

Establish `htot : ∑' δ, g' δ = ∑' δ : {δ // P δ}, g δ`. Rewrite using `[show (∑' δ : {δ // P δ}, g δ) = ∑' δ : ({δ | P δ} : Set G), g δ from rfl, tsum_subtype]`. Use `congr 1`. Rewrite `H` using `[htot]`. Use `H using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `i`. Take `⟨s, γ, hγ, rfl⟩` from `i`. Rewrite using `[Set.indicator_apply]`. Use `split_ifs with hall`. Use `congr 1`.

Use function extensionality and compare the values at `δ`. Take `⟨δ, hδ⟩` from `δ`. Simplify using `[g', hall δ hδ]`. Establish `hall' : ¬ ∀ δ ∈ ({δ | IsConj γ δ} : Set G), P δ` using `hall push_neg at hall'`. Take `⟨δ0, hδ0, hnP⟩` from `hall'`.

Use `symm`. Establish `: ∀ δ : ({δ | IsConj γ δ} : Set G), g' δ = 0`. Introduce `⟨δ, hδ⟩`. Establish `hnδ : ¬ P δ` using `fun h => hnP (hP δ δ0 ((hδ : IsConj γ δ).symm.trans hδ0) h)`. Simplify using `[g', hnδ]`.

Simplify using `[this]`.
-/
theorem classSum_regroup : ∀ {G : Type} [Group G] (g : G → ℂ), (Function.support g).Finite →
    ∀ (R P : G → Prop), (∀ δ, g δ ≠ 0 → R δ) → (∀ a b, IsConj a b → P a → P b) →
    HasSum (fun i : {𝔬 : Set G // ∃ γ, R γ ∧ 𝔬 = {δ | IsConj γ δ}} => ∑' δ : i.1, g δ) (∑' δ, g δ) ∧
    HasSum (fun i : {𝔬 : Set G // ∃ γ, R γ ∧ 𝔬 = {δ | IsConj γ δ}} =>
      {i : {𝔬 : Set G // ∃ γ, R γ ∧ 𝔬 = {δ | IsConj γ δ}} | ∀ δ ∈ i.1, P δ}.indicator
        (fun i => ∑' δ : i.1, g δ) i) (∑' δ : {δ // P δ}, g δ) := by
  classical
  intro G _ g hg R P hR hP
  refine ⟨hasSum_conjClasses_tsum_of_finite_support g hg R hR, ?_⟩
  let g' : G → ℂ := fun δ => if P δ then g δ else 0
  have hg' : (Function.support g').Finite := by
    refine hg.subset ?_
    intro δ h
    by_cases hp : P δ <;> simp_all [g']
  have hR' : ∀ δ, g' δ ≠ 0 → R δ := by
    intro δ h; apply hR; by_cases hp : P δ <;> simp_all [g']
  have H := hasSum_conjClasses_tsum_of_finite_support g' hg' R hR'
  have htot : ∑' δ, g' δ = ∑' δ : {δ // P δ}, g δ := by
    rw [show (∑' δ : {δ // P δ}, g δ) = ∑' δ : ({δ | P δ} : Set G), g δ from rfl, tsum_subtype]
    congr 1
  rw [htot] at H
  convert H using 1
  funext i
  obtain ⟨s, γ, hγ, rfl⟩ := i
  rw [Set.indicator_apply]
  split_ifs with hall
  · congr 1; funext δ
    obtain ⟨δ, hδ⟩ := δ
    simp [g', hall δ hδ]
  · have hall' : ¬ ∀ δ ∈ ({δ | IsConj γ δ} : Set G), P δ := hall
    push_neg at hall'
    obtain ⟨δ0, hδ0, hnP⟩ := hall'
    symm
    have : ∀ δ : ({δ | IsConj γ δ} : Set G), g' δ = 0 := by
      intro ⟨δ, hδ⟩
      have hnδ : ¬ P δ := fun h => hnP (hP δ δ0 ((hδ : IsConj γ δ).symm.trans hδ0) h)
      simp [g', hnδ]
    simp [this]

end GlobalTheory
