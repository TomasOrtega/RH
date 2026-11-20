import Mathlib
import Development.EtaleCohomology.EtaleSheaves.BuildCut

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace LateralTheory.E.BuildCut

/- English proof (translation)
Introduce `W _ hW V hV`. Establish `key : ∀ s : Finset W, ∃ e : W, IsIdempotentElem e ∧ ∀ p : PrimeSpectrum W, ((s : Set W) ⊆ (p.asIdeal : Set W) ↔ e ∈ p.asIdeal)`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => exact ⟨0, IsIdempotentElem.zero, fun p => by simp [p.asIdeal.zero_mem]⟩`.

Consider the case `insert a s ha ih`. Take `⟨f, hf, hfs⟩` from `ih`. Take `⟨e, u, he, hu, rfl⟩` from `hW.2 a`. Establish `he' : e * e = e` using `he`. Establish `hf' : f * f = f` using `hf`.

Use `⟨e + f - e * f, ?_, fun p => ?_⟩` and prove the remaining obligations. Use `show (e + f - e * f) * (e + f - e * f) = e + f - e * f`. Take the linear combination `(1 - f + f * f - f) * he' + (1 - e) * hf'`. Rewrite using `[Finset.coe_insert, Set.insert_subset_iff, hfs p, SetLike.mem_coe, Ideal.mul_unit_mem_iff_mem _ hu]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨h1, h2⟩`. Conclude with `p.asIdeal.sub_mem (p.asIdeal.add_mem h1 h2) (p.asIdeal.mul_mem_right _ h1)`. Introduce `h`. Establish `h1 : e * (e + f - e * f) = e` using `by linear_combination (1 - f) * he'`. Establish `h2 : f * (e + f - e * f) = f` using `by linear_combination (1 - e) * hf'`.

Conclude with `⟨h1 ▸ p.asIdeal.mul_mem_left _ h, h2 ▸ p.asIdeal.mul_mem_left _ h⟩`. Take `⟨t, ht⟩` from `PrimeSpectrum.isCompact_isOpen_iff.mp ⟨hV, V.isOpen⟩`. Take `⟨e, he, hte⟩` from `key t`. Use `⟨e, he, ?_⟩` and prove the remaining obligations. Rewrite using `[← ht]`.

Use extensionality with `p`. Simplify using `[PrimeSpectrum.mem_zeroLocus, hte p]`.
-/
theorem UpperTheory.isCompact_open_eq_basicOpen_idempotent_of_prodACF :
    ∀ {W : Type} [CommRing W], ProdACF W → ∀ (V : Opens (PrimeSpectrum W)), IsCompact (V : Set (PrimeSpectrum W)) →
        ∃ e : W, IsIdempotentElem e ∧ (V : Set (PrimeSpectrum W)) = (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum W)) := by
  classical
  intro W _ hW V hV
  have key : ∀ s : Finset W, ∃ e : W, IsIdempotentElem e ∧
      ∀ p : PrimeSpectrum W, ((s : Set W) ⊆ (p.asIdeal : Set W) ↔ e ∈ p.asIdeal) := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨0, IsIdempotentElem.zero, fun p => by simp [p.asIdeal.zero_mem]⟩
    | insert a s ha ih =>
      obtain ⟨f, hf, hfs⟩ := ih
      obtain ⟨e, u, he, hu, rfl⟩ := hW.2 a
      have he' : e * e = e := he
      have hf' : f * f = f := hf
      refine ⟨e + f - e * f, ?_, fun p => ?_⟩
      · show (e + f - e * f) * (e + f - e * f) = e + f - e * f
        linear_combination (1 - f + f * f - f) * he' + (1 - e) * hf'
      · rw [Finset.coe_insert, Set.insert_subset_iff, hfs p, SetLike.mem_coe,
          Ideal.mul_unit_mem_iff_mem _ hu]
        constructor
        · rintro ⟨h1, h2⟩
          exact p.asIdeal.sub_mem (p.asIdeal.add_mem h1 h2) (p.asIdeal.mul_mem_right _ h1)
        · intro h
          have h1 : e * (e + f - e * f) = e := by linear_combination (1 - f) * he'
          have h2 : f * (e + f - e * f) = f := by linear_combination (1 - e) * hf'
          exact ⟨h1 ▸ p.asIdeal.mul_mem_left _ h, h2 ▸ p.asIdeal.mul_mem_left _ h⟩
  obtain ⟨t, ht⟩ := PrimeSpectrum.isCompact_isOpen_iff.mp ⟨hV, V.isOpen⟩
  obtain ⟨e, he, hte⟩ := key t
  refine ⟨e, he, ?_⟩
  rw [← ht]
  ext p
  simp [PrimeSpectrum.mem_zeroLocus, hte p]
