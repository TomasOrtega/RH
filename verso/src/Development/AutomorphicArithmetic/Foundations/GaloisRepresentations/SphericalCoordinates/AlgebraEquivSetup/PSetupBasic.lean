import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.CodiffUnit
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

/- English proof (translation)
Introduce `E _ _ _ A n p _ S`. Establish `key : ∀ v : InfinitePlace E, sigPosH (S.G.gram_herm v) = 1 ↔ v = InfinitePlace.mk A.τ₀`. Introduce `v`. Use `show sigPos (A.herm n) v.embedding = 1 ↔ _`. Establish `h` using `S.sig v.embedding`.

Rewrite `h` using `[InfinitePlace.mk_embedding]`. Prove the components needed by the constructor for the conclusion. Introduce `h1`. Assume the negation of the conclusion as `hne`. Establish `h0` using `(h.2 hne).1`.

Use linear arithmetic over natural numbers and integers. Introduce `hv`. Conclude with `(h.1 hv).1`. Use `⟨?_, (key _).2 rfl, fun h => ?_⟩` and prove the remaining obligations. Conclude with `Fintype.card_eq_one_iff.2 ⟨⟨InfinitePlace.mk A.τ₀, (key _).2 rfl⟩, fun w => Subtype.ext ((key w.1).1 w.2)⟩`.

Establish `h2 : 2 * 1 < Module.finrank ℚ E` using `by simpa using h`. Conclude with `⟨Or.inl h2, Or.inl h2⟩`.
-/
theorem UpperTheory.Gal.W2.Seed.pSetupBasic :
    SetupBasic := by
  intro E _ _ _ A n p _ S
  have key : ∀ v : InfinitePlace E, sigPosH (S.G.gram_herm v) = 1 ↔ v = InfinitePlace.mk A.τ₀ := by
    intro v
    show sigPos (A.herm n) v.embedding = 1 ↔ _
    have h := S.sig v.embedding
    rw [InfinitePlace.mk_embedding] at h
    constructor
    · intro h1
      by_contra hne
      have h0 := (h.2 hne).1
      omega
    · intro hv
      exact (h.1 hv).1
  refine ⟨?_, (key _).2 rfl, fun h => ?_⟩
  · exact Fintype.card_eq_one_iff.2 ⟨⟨InfinitePlace.mk A.τ₀, (key _).2 rfl⟩,
      fun w => Subtype.ext ((key w.1).1 w.2)⟩
  · have h2 : 2 * 1 < Module.finrank ℚ E := by simpa using h
    exact ⟨Or.inl h2, Or.inl h2⟩
