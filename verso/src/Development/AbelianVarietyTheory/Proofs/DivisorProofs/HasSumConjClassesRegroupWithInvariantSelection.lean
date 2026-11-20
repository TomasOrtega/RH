import Mathlib

namespace GlobalTheory

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Supply the required witnesses or components.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Apply function extensionality and compare values at an arbitrary argument. Extract witnesses or component facts from the available result. Substitute using the available equality. Simplify by unfolding definitions. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Introduce a local definition for the expression. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Apply the first step, then apply the next step to every resulting obligation. Establish an intermediate fact. Apply the first step, then apply the next step to every resulting obligation. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Rewrite the indicated hypotheses using the stated equalities. Apply an available result and prove the equalities needed to match it to the conclusion.

Apply function extensionality and compare values at an arbitrary argument. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument.

Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules. Establish an intermediate fact. Extract witnesses or component facts from the available result. Use symmetry to reverse the relation.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
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
