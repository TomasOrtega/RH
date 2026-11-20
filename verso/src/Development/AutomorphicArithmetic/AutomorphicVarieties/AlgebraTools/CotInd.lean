import Mathlib

open IsLocalRing

namespace UpperTheory.V.AlgebraTools

structure CotInd (R : Type) [CommRing R] [IsLocalRing R] {κ : Type} [Fintype κ] (x : κ → R) : Prop where
  mem : ∀ k, x k ∈ maximalIdeal R
  indep : ∀ a : κ → R, ∑ k, a k * x k ∈ maximalIdeal R ^ 2 → ∀ k, a k ∈ maximalIdeal R

/- English proof (translation)
Establish `key : ∀ (h : ∀ k, x k ∈ maximalIdeal R) (a : κ → R), (∑ k, residue R (a k) • ((maximalIdeal R).toCotangent ⟨x k, h k⟩ : CotangentSpace R) = 0) ↔ ∑ k, a k * x k ∈ maximalIdeal R ^ 2`. Introduce `h a`. Establish `h1 : ∑ k, residue R (a k) • ((maximalIdeal R).toCotangent ⟨x k, h k⟩ : CotangentSpace R) = (maximalIdeal R).toCotangent (∑ k, a k • (⟨x k, h k⟩ : maximalIdeal R))`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[map_smul]`. Conclude with `algebraMap_smul (ResidueField R) (a k) _`. Rewrite using `[h1, Ideal.toCotangent_eq_zero]`. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨h, hi⟩`. Use `⟨h, Fintype.linearIndependent_iff.2 fun g hg k => ?_⟩` and prove the remaining obligations. Use `choose a ha using fun k => residue_surjective (g k)`. Rewrite using `[← ha k, residue_eq_zero_iff]`. Use `hi a ((key h a).1 ?_) k` and prove the remaining obligations.

Simplify `hg` using `[ha]`. Introduce and unpack `⟨h, hi⟩`. Use `⟨h, fun a ha k => ?_⟩` and prove the remaining obligations. Use `Fintype.linearIndependent_iff.1 hi (fun k => residue R (a k)) ((key h a).2 ha) k` as an intermediate fact. Conclude with `(residue_eq_zero_iff _).1 this`.
-/
theorem cotInd_iff (R : Type) [CommRing R] [IsLocalRing R] {κ : Type} [Fintype κ] (x : κ → R) :
    CotInd R x ↔ ∃ h : ∀ k, x k ∈ maximalIdeal R,
      LinearIndependent (ResidueField R)
        (fun k => ((maximalIdeal R).toCotangent ⟨x k, h k⟩ : CotangentSpace R)) := by
  have key : ∀ (h : ∀ k, x k ∈ maximalIdeal R) (a : κ → R),
      (∑ k, residue R (a k) • ((maximalIdeal R).toCotangent ⟨x k, h k⟩ : CotangentSpace R) = 0) ↔
        ∑ k, a k * x k ∈ maximalIdeal R ^ 2 := by
    intro h a
    have h1 : ∑ k, residue R (a k) • ((maximalIdeal R).toCotangent ⟨x k, h k⟩ : CotangentSpace R)
        = (maximalIdeal R).toCotangent (∑ k, a k • (⟨x k, h k⟩ : maximalIdeal R)) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_smul]
      exact algebraMap_smul (ResidueField R) (a k) _
    rw [h1, Ideal.toCotangent_eq_zero]
    simp
  constructor
  · rintro ⟨h, hi⟩
    refine ⟨h, Fintype.linearIndependent_iff.2 fun g hg k => ?_⟩
    choose a ha using fun k => residue_surjective (g k)
    rw [← ha k, residue_eq_zero_iff]
    refine hi a ((key h a).1 ?_) k
    simpa [ha] using hg
  · rintro ⟨h, hi⟩
    refine ⟨h, fun a ha k => ?_⟩
    have := Fintype.linearIndependent_iff.1 hi (fun k => residue R (a k)) ((key h a).2 ha) k
    exact (residue_eq_zero_iff _).1 this

/- English proof (translation)
Take `⟨h1, h2⟩` from `(cotInd_iff R x).1 h`. Conclude with `(cotInd_iff R _).2 ⟨fun i => h1 (e i), h2.comp e he⟩`.
-/
theorem CotInd.comp {R : Type} [CommRing R] [IsLocalRing R] {κ ι : Type} [Fintype κ] [Fintype ι]
    {x : κ → R} (h : CotInd R x) (e : ι → κ) (he : Function.Injective e) : CotInd R (x ∘ e) := by
  obtain ⟨h1, h2⟩ := (cotInd_iff R x).1 h
  exact (cotInd_iff R _).2 ⟨fun i => h1 (e i), h2.comp e he⟩

end UpperTheory.V.AlgebraTools
