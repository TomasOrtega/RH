import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldMapCompConstFn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NadelVanishingCanonicalAddBoundary
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
open Polynomial

namespace GlobalTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Equip the data with the indicated structure. Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Proceed by induction. Treat this case separately. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components.

Treat this case separately. Reduce the claim to the hypotheses of an applicable result. Supply the required witnesses or components. Treat this case separately. Simplify to obtain the desired conclusion from the available facts.

Treat this case separately. Simplify to obtain the desired conclusion from the available facts. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem valuationSubring_fractions_of_essFiniteType : ∀ (L : Type) [Field L] (ψ : ℂ →+* L) (V : ValuationSubring L) (hψ : ∀ a, ψ a ∈ V), (ψ.codRestrict V hψ).EssFiniteType → ∃ s₀ : Finset L, (∀ x ∈ s₀, x ∈ V) ∧ ∀ s ∈ V, ∃ b ∈ Subring.closure (Set.range ψ ∪ ↑s₀), ∃ d ∈ Subring.closure (Set.range ψ ∪ ↑s₀), d ≠ 0 ∧ d⁻¹ ∈ V ∧ s = b / d := by
  classical
  intro L _ ψ V hψ h
  letI : Algebra ℂ V := (ψ.codRestrict V hψ).toAlgebra
  have h' : Algebra.EssFiniteType ℂ V := h
  obtain ⟨s, hs⟩ := h'.cond
  refine ⟨s.image (fun x : V => (x : L)), ?_, ?_⟩
  · intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨y, -, rfl⟩ := hx
    exact y.2
  have key : ∀ x ∈ Algebra.adjoin ℂ (s : Set V),
      ((x : V) : L) ∈ Subring.closure (Set.range ψ ∪ ↑(s.image (fun x : V => (x : L)))) := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      apply Subring.subset_closure
      right
      rw [Finset.coe_image]
      exact ⟨x, hx, rfl⟩
    | algebraMap r =>
      apply Subring.subset_closure
      left
      exact ⟨r, rfl⟩
    | add x y _ _ hx hy =>
      simpa using Subring.add_mem _ hx hy
    | mul x y _ _ hx hy =>
      simpa using Subring.mul_mem _ hx hy
  intro v hv
  obtain ⟨⟨a, m⟩, hm⟩ := IsLocalization.surj
    (Submonoid.comap (algebraMap (↥(Algebra.adjoin ℂ (s : Set V))) V) (IsUnit.submonoid V)) (⟨v, hv⟩ : V)
  have hu : IsUnit ((m : Algebra.adjoin ℂ (s : Set V)) : V) := m.2
  obtain ⟨u, hu'⟩ := hu
  have hinv : (((m : Algebra.adjoin ℂ (s : Set V)) : V) : L) * (((u⁻¹ : Vˣ) : V) : L) = 1 := by
    rw [← hu']
    change (((u : V) * ((u⁻¹ : Vˣ) : V) : V) : L) = ((1 : V) : L)
    rw [u.mul_inv]
  have hd0 : (((m : Algebra.adjoin ℂ (s : Set V)) : V) : L) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hinv
    exact zero_ne_one hinv
  have hmL := congrArg (fun z : V => (z : L)) hm
  simp only at hmL
  refine ⟨((a : V) : L), key _ a.2, (((m : Algebra.adjoin ℂ (s : Set V)) : V) : L),
    key _ (m : Algebra.adjoin ℂ (s : Set V)).2, hd0, ?_, ?_⟩
  · rw [inv_eq_of_mul_eq_one_right hinv]
    exact ((u⁻¹ : Vˣ) : V).2
  · rw [eq_div_iff hd0]
    simpa using hmL

end GlobalTheory
