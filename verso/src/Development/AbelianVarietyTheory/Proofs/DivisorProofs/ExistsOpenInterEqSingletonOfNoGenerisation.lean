import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PointSeparationPair
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Consider separately whether the proposition holds or fails.

Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Assume the hypotheses and unpack their components.

A detailed English derivation is pending.
-/
theorem GlobalTheory.exists_open_inter_eq_singleton_of_no_generisation :
    ∀ (X : Scheme.{0}) [AlgebraicGeometry.IsNoetherian X] (T : Set X) (x : X), IsClosed T → IsClosed ({x} : Set X) → x ∈ T → (∀ z ∈ T, z ⤳ x → z = x) → ∃ U : X.Opens, x ∈ U ∧ ∀ y ∈ U, y ∈ T ↔ y = x := by
  intro X _ T x hT hx hxT hgen
  obtain ⟨S, hSf, hScl, hSirr, hTS⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible hT
  let S' : Set (Set X) := {t | t ∈ S ∧ x ∉ t}
  have hS'f : S'.Finite := hSf.subset (fun t ht => ht.1)
  have hcl : IsClosed (⋃₀ S') := by
    rw [Set.sUnion_eq_biUnion]
    exact hS'f.isClosed_biUnion (fun t ht => hScl t ht.1)
  refine ⟨⟨(⋃₀ S')ᶜ, hcl.isOpen_compl⟩, ?_, ?_⟩
  · show x ∈ (⋃₀ S')ᶜ
    rintro ⟨t, ht, hxt⟩
    exact ht.2 hxt
  · intro y hy
    have hy' : y ∈ (⋃₀ S')ᶜ := hy
    constructor
    · intro hyT
      rw [hTS] at hyT
      obtain ⟨t, htS, hyt⟩ := hyT
      by_cases hxt : x ∈ t
      · have hirr := hSirr t htS
        have hclt := hScl t htS
        obtain ⟨η, hηg⟩ := QuasiSober.sober hirr hclt
        have hgp : closure ({η} : Set X) = t := hηg.def
        have hη : η ∈ t := by
          rw [← hgp]; exact subset_closure rfl
        have hηT : η ∈ T := by
          rw [hTS]; exact ⟨t, htS, hη⟩
        have hsp : η ⤳ x := by
          rw [specializes_iff_mem_closure, hgp]; exact hxt
        have heq := hgen _ hηT hsp
        rw [heq, hx.closure_eq] at hgp
        rw [← hgp] at hyt
        exact hyt
      · exact absurd (Set.mem_sUnion.mpr ⟨t, (⟨htS, hxt⟩ : t ∈ S'), hyt⟩) hy'
    · rintro rfl; exact hxT
