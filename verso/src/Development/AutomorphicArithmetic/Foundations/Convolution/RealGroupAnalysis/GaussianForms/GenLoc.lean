import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.NApply

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

/- English proof (translation)
Introduce `R _ _ s hs hcard`. Set `f : R × R → IsLocalRing.ResidueField R` to `fun p => -(IsLocalRing.residue R p.1) / (IsLocalRing.residue R p.2)`. Establish `hex : ∃ u : IsLocalRing.ResidueField R, u ∉ s.image f`. Assume the negation of the conclusion as `hall`. Establish `hall' : ∀ u : IsLocalRing.ResidueField R, u ∈ s.image f`.

Introduce `u`. Assume the negation of the conclusion as `hu`. Conclude with `hall ⟨u, hu⟩`. Establish `hsub : (Set.univ : Set (IsLocalRing.ResidueField R)) ⊆ ((s.image f : Finset _) : Set _)` using `fun u _ => by simpa using hall' u`. Establish `h1 : ENat.card (IsLocalRing.ResidueField R) ≤ ((s.image f).card : ℕ∞)`.

Establish `h2` using `Set.encard_le_encard hsub`. Rewrite `h2` using `[Set.encard_univ, Set.encard_coe_eq_coe_finsetCard]`. Then use the resulting hypothesis. Establish `h3 : ((s.image f).card : ℕ∞) ≤ (s.card : ℕ∞)`. Conclude with `Finset.card_image_le` after adjusting the coercions. Conclude with `absurd (lt_of_le_of_lt (h1.trans h3) hcard) (lt_irrefl _)`.

Take `⟨u, hu⟩` from `hex`. Take `⟨t, rfl⟩` from `IsLocalRing.residue_surjective u`. Use `⟨t, fun p hp => ?_⟩` and prove the remaining obligations. Rewrite using `[← IsLocalRing.residue_ne_zero_iff_isUnit, map_add, map_mul]`. Introduce `h0`.

Distinguish the cases in `hb : IsLocalRing.residue R p.2 = 0`. Rewrite `h0` using `[hb, zero_mul, add_zero]`. Break down `hs p hp with h | h` into its components or cases. Conclude with `(IsLocalRing.residue_ne_zero_iff_isUnit _).2 h h0`. Conclude with `(IsLocalRing.residue_ne_zero_iff_isUnit _).2 h hb`.

Apply `hu` to reduce the goal to its premises. Use `Finset.mem_image.2 ⟨p, hp, ?_⟩` and prove the remaining obligations. Use `show -(IsLocalRing.residue R p.1) / (IsLocalRing.residue R p.2) = _`. Rewrite using `[div_eq_iff hb]`. Take the linear combination `-h0`.
-/
theorem UpperTheory.ConvolutionTheory.R2.C.genLoc :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] (s : Finset (R × R)), (∀ p ∈ s, IsUnit p.1 ∨ IsUnit p.2) →
    (s.card : ℕ∞) < ENat.card (IsLocalRing.ResidueField R) → ∃ t : R, ∀ p ∈ s, IsUnit (p.1 + p.2 * t) := by
  intro R _ _ s hs hcard
  let f : R × R → IsLocalRing.ResidueField R := fun p =>
    -(IsLocalRing.residue R p.1) / (IsLocalRing.residue R p.2)
  have hex : ∃ u : IsLocalRing.ResidueField R, u ∉ s.image f := by
    by_contra hall
    have hall' : ∀ u : IsLocalRing.ResidueField R, u ∈ s.image f := by
      intro u
      by_contra hu
      exact hall ⟨u, hu⟩
    have hsub : (Set.univ : Set (IsLocalRing.ResidueField R)) ⊆ ((s.image f : Finset _) : Set _) :=
      fun u _ => by simpa using hall' u
    have h1 : ENat.card (IsLocalRing.ResidueField R) ≤ ((s.image f).card : ℕ∞) := by
      have h2 := Set.encard_le_encard hsub
      rwa [Set.encard_univ, Set.encard_coe_eq_coe_finsetCard] at h2
    have h3 : ((s.image f).card : ℕ∞) ≤ (s.card : ℕ∞) := by
      exact_mod_cast Finset.card_image_le
    exact absurd (lt_of_le_of_lt (h1.trans h3) hcard) (lt_irrefl _)
  obtain ⟨u, hu⟩ := hex
  obtain ⟨t, rfl⟩ := IsLocalRing.residue_surjective u
  refine ⟨t, fun p hp => ?_⟩
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, map_add, map_mul]
  intro h0
  by_cases hb : IsLocalRing.residue R p.2 = 0
  · rw [hb, zero_mul, add_zero] at h0
    rcases hs p hp with h | h
    · exact (IsLocalRing.residue_ne_zero_iff_isUnit _).2 h h0
    · exact (IsLocalRing.residue_ne_zero_iff_isUnit _).2 h hb
  · apply hu
    refine Finset.mem_image.2 ⟨p, hp, ?_⟩
    show -(IsLocalRing.residue R p.1) / (IsLocalRing.residue R p.2) = _
    rw [div_eq_iff hb]
    linear_combination -h0
