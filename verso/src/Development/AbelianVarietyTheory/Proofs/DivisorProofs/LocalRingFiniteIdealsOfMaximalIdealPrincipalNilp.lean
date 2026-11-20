import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainFibFinite
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (RingAct)
open scoped CategoryTheory.Obj NumberField
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.IwLevel

namespace GlobalTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails.

Supply the required witnesses or components. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction.

Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components. Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. A detailed English derivation is pending.
-/
theorem localRing_finite_ideals_of_maximalIdeal_principal_nilpotent :
    ∀ (S : Type) [CommRing S] [IsLocalRing S], (IsLocalRing.maximalIdeal S).IsPrincipal →
    IsNilpotent (IsLocalRing.maximalIdeal S) → (Set.univ : Set (Ideal S)).Finite := by
  intro S _ _ hprin hnil
  classical
  obtain ⟨x, hx⟩ := hprin.principal
  obtain ⟨M, hM⟩ := hnil
  set m := IsLocalRing.maximalIdeal S with hm
  have hM' : m ^ M = ⊥ := hM
  have hpow : ∀ n : ℕ, m ^ n = Ideal.span {x ^ n} := by
    intro n
    rw [hx]
    exact Ideal.span_singleton_pow x n
  apply ((Set.finite_Iic M).image fun n => m ^ n).subset
  intro I _
  by_cases hI : I = ⊥
  · exact ⟨M, Set.mem_Iic.mpr le_rfl, by simp only [hM', hI]⟩
  · have hnot : ¬ I ≤ m ^ M := by
      rw [hM']; exact fun h => hI (le_bot_iff.mp h)
    have hex : ∃ k, ¬ I ≤ m ^ k := ⟨M, hnot⟩
    have hk := Nat.find_spec hex
    have hkM : Nat.find hex ≤ M := Nat.find_min' hex hnot
    have hk0 : Nat.find hex ≠ 0 := by
      intro h; apply hk; rw [h, pow_zero]; rw [Ideal.one_eq_top]; exact le_top
    obtain ⟨n, hn⟩ : ∃ n, Nat.find hex = n + 1 := Nat.exists_eq_succ_of_ne_zero hk0
    have hIn : I ≤ m ^ n := by
      by_contra h
      exact Nat.find_min hex (show n < Nat.find hex by omega) h
    rw [hn] at hk
    obtain ⟨a, haI, ha⟩ := SetLike.not_le_iff_exists.mp hk
    have ha' : a ∈ m ^ n := hIn haI
    rw [hpow, Ideal.mem_span_singleton'] at ha'
    obtain ⟨y, rfl⟩ := ha'
    have hy : IsUnit y := by
      by_contra hy
      apply ha
      have hym : y ∈ m := (IsLocalRing.mem_maximalIdeal y).mpr hy
      rw [hx, Ideal.mem_span_singleton'] at hym
      obtain ⟨z, rfl⟩ := hym
      rw [hpow, Ideal.mem_span_singleton']
      exact ⟨z, by ring⟩
    refine ⟨n, Set.mem_Iic.mpr (by omega), ?_⟩
    show m ^ n = I
    apply le_antisymm _ hIn
    rw [hpow, Ideal.span_le, Set.singleton_subset_iff]
    have := I.mul_mem_left ((hy.unit⁻¹ : Sˣ) : S) haI
    rwa [← _root_.mul_assoc, IsUnit.val_inv_mul, _root_.one_mul] at this

end GlobalTheory
