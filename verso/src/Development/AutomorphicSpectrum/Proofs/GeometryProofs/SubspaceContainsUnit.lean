import Mathlib
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.FiniteAlgebraUnit

/- English proof (translation)
Introduce `k _ _ R _ _ _ U hU`. Use `haveI : IsArtinianRing R := IsArtinianRing.of_finite k R`. Use `haveI : Infinite k := IsAlgClosed.instInfinite`. Establish `hpt : ∀ m : Ideal R, m.IsMaximal → ∃ x : R →ₐ[k] k, ∀ r ∈ m, x r = 0`. Introduce `m hm`.

Use `letI : Field (R ⧸ m) := Ideal.Quotient.field m`. Use `haveI : Module.Finite k (R ⧸ m) := Module.Finite.of_surjective (Ideal.Quotient.mkₐ k m).toLinearMap (Ideal.Quotient.mkₐ_surjective k m)`. Set `e : k ≃ₐ[k] (R ⧸ m)` to `AlgEquiv.ofBijective (Algebra.ofId k (R ⧸ m)) IsAlgClosed.algebraMap_bijective_of_isIntegral`. Use `⟨(e.symm : (R ⧸ m) →ₐ[k] k).comp (Ideal.Quotient.mkₐ k m), fun r hr => ?_⟩` and prove the remaining obligations. Establish `h0 : Ideal.Quotient.mkₐ k m r = 0` using `Ideal.Quotient.eq_zero_iff_mem.mpr hr`.

Express the relevant statement in the definitionally equal form `e.symm (Ideal.Quotient.mkₐ k m r) = 0`. Rewrite using `[h0, map_zero]`. Set `f : Ideal R → Submodule k U` to `fun m => (m.restrictScalars k).comap U.subtype`. Establish `hfin : (f '' {m : Ideal R | m.IsMaximal}).Finite` using `(IsArtinianRing.setOfPred_isMaximal_finite R).image f`. Set `s : Finset (Submodule k U)` to `hfin.toFinset`.

Establish `htop : (⊤ : Submodule k U) ∉ s`. Introduce `h`. Take `⟨m, hm, hfm⟩` from `(Set.Finite.mem_toFinset hfin).mp h`. Take `⟨x, hx⟩` from `hpt m hm`. Take `⟨t, htU, ht⟩` from `hU x`.

Establish `: (⟨t, htU⟩ : U) ∈ f m` using `by rw [hfm]; trivial`. Conclude with `ht (hx t this)`. Establish `hne` using `Subspace.biUnion_ne_univ_of_top_notMem (k := k) (s := s) htop`. Choose the witnesses or unpack the hypotheses as in `⟨w, hw⟩ : ∃ w : U, w ∉ ⋃ p ∈ s, (p : Set U) := by`. Assume the negation of the conclusion as `hcon`.

Use `push_neg at hcon`. Conclude with `hne (Set.eq_univ_of_forall hcon)`. Use `⟨w, w.2, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hnu`. Take `⟨m, hm, hwm⟩` from `exists_max_ideal_of_mem_nonunits (show (w : R) ∈ nonunits R from hnu)`.

Apply `hw` to reduce the goal to its premises. Simplify using `only [Set.mem_iUnion]`. Conclude with `⟨f m, (Set.Finite.mem_toFinset hfin).mpr ⟨m, hm, rfl⟩, hwm⟩`.
-/
theorem exists_isUnit_mem_of_forall_point :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (R : Type) [CommRing R] [Algebra k R] [Module.Finite k R]
    (U : Submodule k R), (∀ x : R →ₐ[k] k, ∃ t ∈ U, x t ≠ 0) → ∃ w ∈ U, IsUnit w := by
  intro k _ _ R _ _ _ U hU
  haveI : IsArtinianRing R := IsArtinianRing.of_finite k R
  haveI : Infinite k := IsAlgClosed.instInfinite

  have hpt : ∀ m : Ideal R, m.IsMaximal → ∃ x : R →ₐ[k] k, ∀ r ∈ m, x r = 0 := by
    intro m hm
    letI : Field (R ⧸ m) := Ideal.Quotient.field m
    haveI : Module.Finite k (R ⧸ m) :=
      Module.Finite.of_surjective (Ideal.Quotient.mkₐ k m).toLinearMap
        (Ideal.Quotient.mkₐ_surjective k m)
    let e : k ≃ₐ[k] (R ⧸ m) :=
      AlgEquiv.ofBijective (Algebra.ofId k (R ⧸ m))
        IsAlgClosed.algebraMap_bijective_of_isIntegral
    refine ⟨(e.symm : (R ⧸ m) →ₐ[k] k).comp (Ideal.Quotient.mkₐ k m), fun r hr => ?_⟩
    have h0 : Ideal.Quotient.mkₐ k m r = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hr
    change e.symm (Ideal.Quotient.mkₐ k m r) = 0
    rw [h0, map_zero]

  let f : Ideal R → Submodule k U := fun m => (m.restrictScalars k).comap U.subtype
  have hfin : (f '' {m : Ideal R | m.IsMaximal}).Finite :=
    (IsArtinianRing.setOfPred_isMaximal_finite R).image f
  let s : Finset (Submodule k U) := hfin.toFinset
  have htop : (⊤ : Submodule k U) ∉ s := by
    intro h
    obtain ⟨m, hm, hfm⟩ := (Set.Finite.mem_toFinset hfin).mp h
    obtain ⟨x, hx⟩ := hpt m hm
    obtain ⟨t, htU, ht⟩ := hU x
    have : (⟨t, htU⟩ : U) ∈ f m := by rw [hfm]; trivial
    exact ht (hx t this)
  have hne := Subspace.biUnion_ne_univ_of_top_notMem (k := k) (s := s) htop
  obtain ⟨w, hw⟩ : ∃ w : U, w ∉ ⋃ p ∈ s, (p : Set U) := by
    by_contra hcon
    push_neg at hcon
    exact hne (Set.eq_univ_of_forall hcon)
  refine ⟨w, w.2, ?_⟩
  by_contra hnu
  obtain ⟨m, hm, hwm⟩ := exists_max_ideal_of_mem_nonunits (show (w : R) ∈ nonunits R from hnu)
  apply hw
  simp only [Set.mem_iUnion]
  exact ⟨f m, (Set.Finite.mem_toFinset hfin).mpr ⟨m, hm, rfl⟩, hwm⟩

end GlobalTheory.CompanionTheory.FiniteAlgebraUnit
