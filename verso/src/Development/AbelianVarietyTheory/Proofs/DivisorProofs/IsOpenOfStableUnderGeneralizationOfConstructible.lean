import Mathlib

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

def ultrafilterPrime {A : Type} [CommRing A] (U : Ultrafilter (PrimeSpectrum A)) :
    PrimeSpectrum A where
  asIdeal :=
    { carrier := {c | ∀ᶠ t in (U : Filter (PrimeSpectrum A)), c ∈ t.asIdeal}
      add_mem' := fun {a b} ha hb => by
        have ha' : ∀ᶠ t in (U : Filter (PrimeSpectrum A)), a ∈ t.asIdeal := ha
        have hb' : ∀ᶠ t in (U : Filter (PrimeSpectrum A)), b ∈ t.asIdeal := hb
        exact (ha'.and hb').mono fun t ht => t.asIdeal.add_mem ht.1 ht.2
      zero_mem' := Filter.Eventually.of_forall fun t => t.asIdeal.zero_mem
      smul_mem' := fun r a ha => by
        have ha' : ∀ᶠ t in (U : Filter (PrimeSpectrum A)), a ∈ t.asIdeal := ha
        exact ha'.mono fun t ht => t.asIdeal.mul_mem_left r ht }
  isPrime :=
    { ne_top' := fun h => by
        have h1 : ∀ᶠ t in (U : Filter (PrimeSpectrum A)), (1 : A) ∈ t.asIdeal :=
          (Ideal.eq_top_iff_one _).1 h
        obtain ⟨t, ht⟩ := h1.exists
        exact t.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ht)
      mem_or_mem' := fun {a b} hab => by
        have h : ∀ᶠ t in (U : Filter (PrimeSpectrum A)), a * b ∈ t.asIdeal := hab
        exact Ultrafilter.eventually_or.1 (h.mono fun t ht => t.isPrime.mem_or_mem ht) }

/- English proof (translation)
Introduce `A _ Z hZ hpc`. Rewrite using `[isOpen_iff_mem_nhds]`. Introduce `p hp`. Assume the negation of the conclusion as `hn`. Establish `hne : (nhds p ⊓ Filter.principal Zᶜ).NeBot`.

Rewrite using `[Filter.neBot_iff, Ne, Filter.inf_principal_eq_bot, compl_compl]`. Conclude with `hn`. Take `⟨U, hU⟩` from `Ultrafilter.exists_le (nhds p ⊓ Filter.principal Zᶜ)`. Establish `hU1 : (U : Filter (PrimeSpectrum A)) ≤ nhds p` using `hU.trans inf_le_left`. Establish `hU2 : ∀ᶠ t in (U : Filter (PrimeSpectrum A)), t ∉ Z` using `Filter.le_principal_iff.1 (hU.trans inf_le_right)`.

Establish `hle : ultrafilterPrime U ≤ p`. Introduce `c hc`. Assume the negation of the conclusion as `hcp`. Establish `h1 : ∀ᶠ t in (U : Filter (PrimeSpectrum A)), c ∈ t.asIdeal` using `hc`. Establish `h2 : ∀ᶠ t in (U : Filter (PrimeSpectrum A)), c ∉ t.asIdeal` using `hU1 ((PrimeSpectrum.basicOpen c).isOpen.mem_nhds hcp)`.

Take `⟨t, ht1, ht2⟩` from `(h1.and h2).exists`. Conclude with `ht2 ht1`. Establish `hq : ultrafilterPrime U ∈ Z` using `hZ ((PrimeSpectrum.le_iff_specializes _ _).1 hle |> fun h => by simpa using h) hp`. Take `⟨a, I, ha, hI, hsub⟩` from `hpc _ hq`. Establish `h1 : ∀ᶠ t in (U : Filter (PrimeSpectrum A)), a ∉ t.asIdeal` using `Ultrafilter.eventually_not.2 ha`.

Establish `h2 : ∀ᶠ t in (U : Filter (PrimeSpectrum A)), ∀ c ∈ I, c ∈ t.asIdeal` using `(Filter.eventually_all_finset I).2 fun c hc => hI c hc`. Take `⟨t, ⟨ht1, ht2⟩, ht3⟩` from `((h1.and h2).and hU2).exists`. Conclude with `ht3 (hsub t ht1 ht2)`.
-/
theorem isOpen_of_stableUnderGeneralization_of_constructible_pieces :
    ∀ (A : Type) [CommRing A] (Z : Set (PrimeSpectrum A)), StableUnderGeneralization Z → (∀ p ∈ Z, ∃ (a : A) (I : Finset A), a ∉ p.asIdeal ∧ (∀ c ∈ I, c ∈ p.asIdeal) ∧ ∀ t : PrimeSpectrum A, a ∉ t.asIdeal → (∀ c ∈ I, c ∈ t.asIdeal) → t ∈ Z) → IsOpen Z := by
  intro A _ Z hZ hpc
  rw [isOpen_iff_mem_nhds]
  intro p hp
  by_contra hn
  have hne : (nhds p ⊓ Filter.principal Zᶜ).NeBot := by
    rw [Filter.neBot_iff, Ne, Filter.inf_principal_eq_bot, compl_compl]
    exact hn
  obtain ⟨U, hU⟩ := Ultrafilter.exists_le (nhds p ⊓ Filter.principal Zᶜ)
  have hU1 : (U : Filter (PrimeSpectrum A)) ≤ nhds p := hU.trans inf_le_left
  have hU2 : ∀ᶠ t in (U : Filter (PrimeSpectrum A)), t ∉ Z :=
    Filter.le_principal_iff.1 (hU.trans inf_le_right)
  have hle : ultrafilterPrime U ≤ p := by
    intro c hc
    by_contra hcp
    have h1 : ∀ᶠ t in (U : Filter (PrimeSpectrum A)), c ∈ t.asIdeal := hc
    have h2 : ∀ᶠ t in (U : Filter (PrimeSpectrum A)), c ∉ t.asIdeal :=
      hU1 ((PrimeSpectrum.basicOpen c).isOpen.mem_nhds hcp)
    obtain ⟨t, ht1, ht2⟩ := (h1.and h2).exists
    exact ht2 ht1
  have hq : ultrafilterPrime U ∈ Z :=
    hZ ((PrimeSpectrum.le_iff_specializes _ _).1 hle |> fun h => by simpa using h) hp
  obtain ⟨a, I, ha, hI, hsub⟩ := hpc _ hq
  have h1 : ∀ᶠ t in (U : Filter (PrimeSpectrum A)), a ∉ t.asIdeal :=
    Ultrafilter.eventually_not.2 ha
  have h2 : ∀ᶠ t in (U : Filter (PrimeSpectrum A)), ∀ c ∈ I, c ∈ t.asIdeal :=
    (Filter.eventually_all_finset I).2 fun c hc => hI c hc
  obtain ⟨t, ⟨ht1, ht2⟩, ht3⟩ := ((h1.and h2).and hU2).exists
  exact ht3 (hsub t ht1 ht2)

end GlobalTheory
