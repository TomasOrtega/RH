import Development.EtaleCohomology.EtaleSheaves.FMrangePf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.BuildCut LateralTheory.E.SysFMPf LateralTheory.E.FMrangePf

namespace LateralTheory.E.FMrangePfQc

/- English proof (translation)
Proceed by induction on `t using Finset.induction_on with`. Consider the case `empty => exact ⟨0, IsIdempotentElem.zero, fun p => by simp⟩`. Consider the case `insert a t _ ih`. Take `⟨e, he, hpe⟩` from `ih`. Take `⟨f, u, hf, hu, rfl⟩` from `hW.2 a`.

Use `⟨f + e - f * e, ?_, fun p => ?_⟩` and prove the remaining obligations. Unfold `IsIdempotentElem at *`. Take the linear combination `(1 - e + (e * e - e)) * hf + (1 - f) * he`. Establish `hfe : f * (f + e - f * e) = f`. Use `hf.eq` as an intermediate fact.

Take the linear combination `(1 - e) * this`. Establish `hef : e * (f + e - f * e) = e`. Use `he.eq` as an intermediate fact. Take the linear combination `(1 - f) * this`. Establish `key : f + e - f * e ∈ p.asIdeal ↔ f ∈ p.asIdeal ∧ e ∈ p.asIdeal`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `⟨hfe ▸ p.asIdeal.mul_mem_left f h, hef ▸ p.asIdeal.mul_mem_left e h⟩`. Introduce and unpack `⟨h1, h2⟩`. Conclude with `p.asIdeal.sub_mem (p.asIdeal.add_mem h1 h2) (p.asIdeal.mul_mem_right e h1)`.

Establish `hfu : f * u ∈ p.asIdeal ↔ f ∈ p.asIdeal`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Take `⟨v, hv⟩` from `hu.exists_right_inv`. Use `p.asIdeal.mul_mem_right v h` as an intermediate fact.

Rewrite `this` using `[mul_assoc, hv, mul_one]`. Then use the resulting hypothesis. Conclude with `fun h => p.asIdeal.mul_mem_right u h`. Establish `h1` using `hpe p`. Simplify using `only [Set.mem_compl_iff, PrimeSpectrum.mem_zeroLocus, Finset.coe_insert, Set.insert_subset_iff] at h1 ⊢`. Rewrite using `[key]`.

Simplify using `only [SetLike.mem_coe, hfu, not_iff_not.mp h1]`.
-/
theorem finset_idem {W : Type} [CommRing W] (hW : ProdACF W) (t : Finset W) :
    ∃ e : W, IsIdempotentElem e ∧ ∀ p : PrimeSpectrum W, p ∈ (PrimeSpectrum.zeroLocus (t : Set W))ᶜ ↔ e ∉ p.asIdeal := by
  classical
  induction t using Finset.induction_on with
  | empty => exact ⟨0, IsIdempotentElem.zero, fun p => by simp⟩
  | insert a t _ ih =>
    obtain ⟨e, he, hpe⟩ := ih
    obtain ⟨f, u, hf, hu, rfl⟩ := hW.2 a
    refine ⟨f + e - f * e, ?_, fun p => ?_⟩
    · unfold IsIdempotentElem at *
      linear_combination (1 - e + (e * e - e)) * hf + (1 - f) * he
    · have hfe : f * (f + e - f * e) = f := by
        have := hf.eq; linear_combination (1 - e) * this
      have hef : e * (f + e - f * e) = e := by
        have := he.eq; linear_combination (1 - f) * this
      have key : f + e - f * e ∈ p.asIdeal ↔ f ∈ p.asIdeal ∧ e ∈ p.asIdeal := by
        constructor
        · intro h
          exact ⟨hfe ▸ p.asIdeal.mul_mem_left f h, hef ▸ p.asIdeal.mul_mem_left e h⟩
        · rintro ⟨h1, h2⟩
          exact p.asIdeal.sub_mem (p.asIdeal.add_mem h1 h2) (p.asIdeal.mul_mem_right e h1)
      have hfu : f * u ∈ p.asIdeal ↔ f ∈ p.asIdeal := by
        constructor
        · intro h
          obtain ⟨v, hv⟩ := hu.exists_right_inv
          have := p.asIdeal.mul_mem_right v h
          rwa [mul_assoc, hv, mul_one] at this
        · exact fun h => p.asIdeal.mul_mem_right u h
      have h1 := hpe p
      simp only [Set.mem_compl_iff, PrimeSpectrum.mem_zeroLocus, Finset.coe_insert, Set.insert_subset_iff] at h1 ⊢
      rw [key]
      simp only [SetLike.mem_coe, hfu, not_iff_not.mp h1]

/- English proof (translation)
Introduce `W _ hW U hU`. Take `⟨t, ht⟩` from `(@PrimeSpectrum.isCompact_isOpen_iff W _ (U : Set (Spec (CommRingCat.of W)))).1 ⟨hU, U.isOpen⟩`. Take `⟨e, he, hpe⟩` from `finset_idem hW t`. Use `⟨e, he, fun p => ?_⟩` and prove the remaining obligations. Rewrite using `[← hpe p, ht]`.

Both sides reduce to the same expression.
-/
theorem QcIdem_pf : QcIdem := by
  intro W _ hW U hU
  obtain ⟨t, ht⟩ := (@PrimeSpectrum.isCompact_isOpen_iff W _ (U : Set (Spec (CommRingCat.of W)))).1 ⟨hU, U.isOpen⟩
  obtain ⟨e, he, hpe⟩ := finset_idem hW t
  refine ⟨e, he, fun p => ?_⟩
  rw [← hpe p, ht]
  rfl

/- English proof (translation)
The claim follows from `FMrange_of_leaves hI QcIdem_pf`.
-/
theorem FMrange_of (hI : IdemLift) : FMrange :=
  FMrange_of_leaves hI QcIdem_pf

end LateralTheory.E.FMrangePfQc
