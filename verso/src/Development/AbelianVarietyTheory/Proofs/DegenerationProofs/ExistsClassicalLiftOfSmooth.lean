import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompletionPointClosedPointMemOfSmooth

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result.

Assume the negation of the conclusion and derive a contradiction. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Assume the hypotheses and unpack their components. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem henselianLocalRing_valuationSubring_of_isAlgClosed {K : Type*} [Field K] [IsAlgClosed K]
    (V : ValuationSubring K) : HenselianLocalRing V where
  is_henselian f hf a₀ h₁ _ := by
    classical
    have hg : (f.map (algebraMap V K)).Monic := hf.map _
    have hsplit : (f.map (algebraMap V K)).Splits := IsAlgClosed.splits _

    have hev : ((f.eval a₀ : V) : K) =
        ((f.map (algebraMap V K)).roots.map fun r => (a₀ : K) - r).prod := by
      have h1 : ((f.eval a₀ : V) : K) = (f.map (algebraMap V K)).eval (a₀ : K) := by
        rw [Polynomial.eval_map]
        exact (Polynomial.eval₂_at_apply (algebraMap V K) a₀).symm
      rw [h1]
      exact hsplit.eval_eq_prod_roots_of_monic hg _
    have hlt : V.valuation (((f.map (algebraMap V K)).roots.map fun r => (a₀ : K) - r).prod) < 1 := by
      rw [← hev]
      exact (ValuationSubring.valuation_lt_one_iff V _).mp h₁
    rw [map_multiset_prod, Multiset.map_map] at hlt

    obtain ⟨r, hr, hrlt⟩ : ∃ r ∈ (f.map (algebraMap V K)).roots, V.valuation ((a₀ : K) - r) < 1 := by
      by_contra hcon
      push Not at hcon
      refine absurd hlt (not_lt.mpr (Multiset.one_le_prod_of_one_le ?_))
      simp only [Multiset.mem_map, Function.comp_apply]
      rintro _ ⟨s, hs, rfl⟩
      exact hcon s hs
    have hrV : r ∈ V := by
      rw [← V.valuation_le_one_iff]
      have h2 : r = (a₀ : K) - ((a₀ : K) - r) := by ring
      rw [h2]
      exact (Valuation.map_sub _ _ _).trans (max_le (V.valuation_le_one a₀) hrlt.le)
    refine ⟨⟨r, hrV⟩, ?_, ?_⟩
    · have hroot := (Polynomial.mem_roots hg.ne_zero).mp hr
      show Polynomial.eval _ f = 0
      apply Subtype.ext
      have h3 := Polynomial.eval₂_at_apply (p := f) (algebraMap V K) (⟨r, hrV⟩ : V)
      rw [← Polynomial.eval_map] at h3
      simpa using h3.symm.trans hroot
    · rw [ValuationSubring.valuation_lt_one_iff]
      have h4 : ((((⟨r, hrV⟩ : V) - a₀ : V)) : K) = r - a₀ := rfl
      rw [h4, Valuation.map_sub_swap]
      exact hrlt

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem ZJ.exists_classical_lift_of_smooth :
    ∀ (p : ℕ) [Fact p.Prime] (X S : Scheme.{0}) (f : X ⟶ S) [Smooth f] (y : Sp (OO p) ⟶ S) (x : Sp (kb p) ⟶ X), x ≫ f = rPt p ≫ y → ∃ b : Sp (OO p) ⟶ X, b ≫ f = y ∧ rPt p ≫ b = x := by
  intro p _ X S f _ y x hx
  have : HenselianLocalRing (OO p) := henselianLocalRing_valuationSubring_of_isAlgClosed _
  obtain ⟨⟨b, hb⟩, hb'⟩ := reducePoint_residue_surjective f (OO p) y ⟨x, hx⟩
  exact ⟨b, hb, congrArg Subtype.val hb'⟩

end GlobalTheory
