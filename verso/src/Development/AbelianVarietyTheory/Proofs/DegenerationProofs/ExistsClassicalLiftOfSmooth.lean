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
Establish `hg : (f.map (algebraMap V K)).Monic` using `hf.map _`. Establish `hsplit : (f.map (algebraMap V K)).Splits` using `IsAlgClosed.splits _`. Establish `hev : ((f.eval a₀ : V) : K) = ((f.map (algebraMap V K)).roots.map fun r => (a₀ : K) - r).prod`. Establish `h1 : ((f.eval a₀ : V) : K) = (f.map (algebraMap V K)).eval (a₀ : K)`. Rewrite using `[Polynomial.eval_map]`.

Conclude with `(Polynomial.eval₂_at_apply (algebraMap V K) a₀).symm`. Rewrite using `[h1]`. Conclude with `hsplit.eval_eq_prod_roots_of_monic hg _`. Establish `hlt : V.valuation (((f.map (algebraMap V K)).roots.map fun r => (a₀ : K) - r).prod) < 1`. Rewrite using `[← hev]`.

Conclude with `(ValuationSubring.valuation_lt_one_iff V _).mp h₁`. Rewrite `hlt` using `[map_multiset_prod, Multiset.map_map]`. Choose the witnesses or unpack the hypotheses as in `⟨r, hr, hrlt⟩ : ∃ r ∈ (f.map (algebraMap V K)).roots, V.valuation ((a₀ : K) - r) < 1 := by`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`.

Use `absurd hlt (not_lt.mpr (Multiset.one_le_prod_of_one_le ?_))` and prove the remaining obligations. Simplify using `only [Multiset.mem_map, Function.comp_apply]`. Introduce and unpack `_ ⟨s, hs, rfl⟩`. Conclude with `hcon s hs`. Establish `hrV : r ∈ V`.

Rewrite using `[← V.valuation_le_one_iff]`. Establish `h2 : r = (a₀ : K) - ((a₀ : K) - r)` using `by ring`. Rewrite using `[h2]`. Conclude with `(Valuation.map_sub _ _ _).trans (max_le (V.valuation_le_one a₀) hrlt.le)`. Use `⟨⟨r, hrV⟩, ?_, ?_⟩` and prove the remaining obligations.

Establish `hroot` using `(Polynomial.mem_roots hg.ne_zero).mp hr show Polynomial.eval _ f = 0`. Apply `Subtype.ext` to reduce the goal to its premises. Establish `h3` using `Polynomial.eval₂_at_apply (p := f) (algebraMap V K) (⟨r, hrV⟩ : V)`. Rewrite `h3` using `[← Polynomial.eval_map]`. Simplify using `using h3.symm.trans hroot`.

Rewrite using `[ValuationSubring.valuation_lt_one_iff]`. Establish `h4 : ((((⟨r, hrV⟩ : V) - a₀ : V)) : K) = r - a₀` using `rfl`. Rewrite using `[h4, Valuation.map_sub_swap]`. Conclude with `hrlt`.
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
Introduce `p _ X S f _ y x hx`. Establish `: HenselianLocalRing (OO p)` using `henselianLocalRing_valuationSubring_of_isAlgClosed _`. Take `⟨⟨b, hb⟩, hb'⟩` from `reducePoint_residue_surjective f (OO p) y ⟨x, hx⟩`. Conclude with `⟨b, hb, congrArg Subtype.val hb'⟩`.
-/
theorem ZJ.exists_classical_lift_of_smooth :
    ∀ (p : ℕ) [Fact p.Prime] (X S : Scheme.{0}) (f : X ⟶ S) [Smooth f] (y : Sp (OO p) ⟶ S) (x : Sp (kb p) ⟶ X), x ≫ f = rPt p ≫ y → ∃ b : Sp (OO p) ⟶ X, b ≫ f = y ∧ rPt p ≫ b = x := by
  intro p _ X S f _ y x hx
  have : HenselianLocalRing (OO p) := henselianLocalRing_valuationSubring_of_isAlgClosed _
  obtain ⟨⟨b, hb⟩, hb'⟩ := reducePoint_residue_surjective f (OO p) y ⟨x, hx⟩
  exact ⟨b, hb, congrArg Subtype.val hb'⟩

end GlobalTheory
