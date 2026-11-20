import Mathlib

namespace GlobalTheory.CompanionTheory.SemistableSpecial

open MvPolynomial

/- English proof (translation)
Establish `key : ∀ (t : Finset σ) (y : MvPolynomial σ k), (∀ i ∈ t, (X i : MvPolynomial σ k) ∣ y) → (∏ i ∈ t, (X i : MvPolynomial σ k)) ∣ y`. Introduce `t`. Proceed by induction on `t using Finset.induction_on with`. Consider the case `empty => intro y _`. Simplify using the standard rewrite rules.

Consider the case `@insert a t ha ih`. Introduce `y hy`. Take `⟨z, rfl⟩` from `hy a (Finset.mem_insert_self a t)`. Rewrite using `[Finset.prod_insert ha]`. Use `mul_dvd_mul_left _ (ih z ?_)` and prove the remaining obligations.

Introduce `i hi`. Establish `hXi : Prime (X i : MvPolynomial σ k)` using `MvPolynomial.X_prime`. Break down `hXi.dvd_or_dvd (hy i (Finset.mem_insert_of_mem hi)) with h | h` into its components or cases. It suffices to derive a contradiction. Rewrite `h` using `[MvPolynomial.X_dvd_X]`.

Conclude with `ha (h ▸ hi)`. Conclude with `h`. Introduce `n y hy`. Apply `key` to reduce the goal to its premises. Introduce `i hi`.

Establish `hXi : Prime (X i : MvPolynomial σ k)` using `MvPolynomial.X_prime`. Conclude with `hXi.dvd_of_dvd_pow (dvd_trans (Finset.dvd_prod_of_mem (fun j => (X j : MvPolynomial σ k)) hi) hy)`.
-/
theorem isRadical_prod_X {k σ : Type} [CommRing k] [IsDomain k] [UniqueFactorizationMonoid k]
    (s : Finset σ) : IsRadical (∏ i ∈ s, (X i : MvPolynomial σ k)) := by
  classical
  have key : ∀ (t : Finset σ) (y : MvPolynomial σ k),
      (∀ i ∈ t, (X i : MvPolynomial σ k) ∣ y) → (∏ i ∈ t, (X i : MvPolynomial σ k)) ∣ y := by
    intro t
    induction t using Finset.induction_on with
    | empty => intro y _; simp
    | @insert a t ha ih =>
      intro y hy
      obtain ⟨z, rfl⟩ := hy a (Finset.mem_insert_self a t)
      rw [Finset.prod_insert ha]
      refine mul_dvd_mul_left _ (ih z ?_)
      intro i hi
      have hXi : Prime (X i : MvPolynomial σ k) := MvPolynomial.X_prime
      rcases hXi.dvd_or_dvd (hy i (Finset.mem_insert_of_mem hi)) with h | h
      · exfalso
        rw [MvPolynomial.X_dvd_X] at h
        exact ha (h ▸ hi)
      · exact h
  intro n y hy
  apply key
  intro i hi
  have hXi : Prime (X i : MvPolynomial σ k) := MvPolynomial.X_prime
  exact hXi.dvd_of_dvd_pow
    (dvd_trans (Finset.dvd_prod_of_mem (fun j => (X j : MvPolynomial σ k)) hi) hy)

/- English proof (translation)
Use `set P : MvPolynomial σ O := ∏ i ∈ s, X i with hP`. Use `set φ : MvPolynomial σ O →+* MvPolynomial σ (IsLocalRing.ResidueField O) := MvPolynomial.map (IsLocalRing.residue O) with hφ`. Establish `hker : RingHom.ker φ = Ideal.span {C ϖ}`. Rewrite using `[hφ, MvPolynomial.ker_map, IsLocalRing.ker_residue, (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ, Ideal.map_span, Set.image_singleton]`. Establish `hφP : φ P = ∏ i ∈ s, (X i : MvPolynomial σ (IsLocalRing.ResidueField O))`.

Rewrite using `[hP, hφ, map_prod]`. Simplify using `only [MvPolynomial.map_X]`. Establish `hCϖ : φ (C ϖ) = 0`. Rewrite using `[← RingHom.mem_ker, hker]`. Conclude with `Ideal.mem_span_singleton_self _`.

Establish `hPmem : P ∈ Ideal.span {P - C ϖ} ⊔ Ideal.span {(C ϖ : MvPolynomial σ O)}`. Establish `h` using `Ideal.add_mem (Ideal.span {P - C ϖ} ⊔ Ideal.span {(C ϖ : MvPolynomial σ O)}) (Ideal.mem_sup_left (Ideal.mem_span_singleton_self (P - C ϖ))) (Ideal.mem_sup_right (Ideal.mem_span_singleton_self (C ϖ : MvPolynomial σ O)))`. Rewrite `h` using `[sub_add_cancel]`. Then use the resulting hypothesis. Establish `hmem : ∀ x, x ∈ Ideal.span {P - C ϖ} ⊔ Ideal.span {(C ϖ : MvPolynomial σ O)} ↔ φ P ∣ φ x`. Introduce `x`.

Prove the components needed by the constructor for the conclusion. Introduce `hx`. Establish `hle : Ideal.span {P - C ϖ} ⊔ Ideal.span {(C ϖ : MvPolynomial σ O)} ≤ Ideal.comap φ (Ideal.span {φ P})`. Use `sup_le ?_ ?_` and prove the remaining obligations. Rewrite using `[Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_sub, hCϖ, sub_zero]`.

Conclude with `Ideal.mem_span_singleton_self _`. Rewrite using `[Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, hCϖ]`. Conclude with `Ideal.zero_mem _`. Conclude with `Ideal.mem_span_singleton.mp (Ideal.mem_comap.mp (hle hx))`. Introduce and unpack `⟨g, hg⟩`.

Take `⟨g', rfl⟩` from `MvPolynomial.map_surjective _ IsLocalRing.residue_surjective g`. Establish `hdiff : x - P * g' ∈ RingHom.ker φ`. Rewrite using `[RingHom.mem_ker, map_sub, map_mul, hg, hφ]`. Conclude with `sub_self _`. Rewrite `hdiff` using `[hker]`.

Establish `hx : x = (x - P * g') + P * g'` using `by ring`. Rewrite using `[hx]`. Conclude with `Ideal.add_mem _ (Ideal.mem_sup_right hdiff) (Ideal.mul_mem_right _ _ hPmem)`. Unfold `Ideal.IsRadical`. Introduce `x hx`.

Rewrite `hx` using `[Ideal.mem_radical_iff]`. Take `⟨n, hn⟩` from `hx`. Rewrite `hn` using `[hmem]`. Rewrite using `[hmem]`. Rewrite `hn` using `[map_pow, hφP]`.

Rewrite using `[hφP]`. Conclude with `isRadical_prod_X s n (φ x) hn`.
-/
theorem isRadical_span_sup {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {ϖ : O} (hϖ : Irreducible ϖ) {σ : Type} (s : Finset σ) :
    (Ideal.span {(∏ i ∈ s, (X i : MvPolynomial σ O)) - C ϖ} ⊔
      Ideal.span {(C ϖ : MvPolynomial σ O)}).IsRadical := by
  classical
  set P : MvPolynomial σ O := ∏ i ∈ s, X i with hP
  set φ : MvPolynomial σ O →+* MvPolynomial σ (IsLocalRing.ResidueField O) :=
    MvPolynomial.map (IsLocalRing.residue O) with hφ
  have hker : RingHom.ker φ = Ideal.span {C ϖ} := by
    rw [hφ, MvPolynomial.ker_map, IsLocalRing.ker_residue,
      (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ, Ideal.map_span,
      Set.image_singleton]
  have hφP : φ P = ∏ i ∈ s, (X i : MvPolynomial σ (IsLocalRing.ResidueField O)) := by
    rw [hP, hφ, map_prod]
    simp only [MvPolynomial.map_X]
  have hCϖ : φ (C ϖ) = 0 := by
    rw [← RingHom.mem_ker, hker]
    exact Ideal.mem_span_singleton_self _
  have hPmem : P ∈ Ideal.span {P - C ϖ} ⊔ Ideal.span {(C ϖ : MvPolynomial σ O)} := by
    have h := Ideal.add_mem (Ideal.span {P - C ϖ} ⊔ Ideal.span {(C ϖ : MvPolynomial σ O)})
      (Ideal.mem_sup_left (Ideal.mem_span_singleton_self (P - C ϖ)))
      (Ideal.mem_sup_right (Ideal.mem_span_singleton_self (C ϖ : MvPolynomial σ O)))
    rwa [sub_add_cancel] at h
  have hmem : ∀ x, x ∈ Ideal.span {P - C ϖ} ⊔ Ideal.span {(C ϖ : MvPolynomial σ O)} ↔
      φ P ∣ φ x := by
    intro x
    constructor
    · intro hx
      have hle : Ideal.span {P - C ϖ} ⊔ Ideal.span {(C ϖ : MvPolynomial σ O)} ≤
          Ideal.comap φ (Ideal.span {φ P}) := by
        refine sup_le ?_ ?_
        · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap,
            map_sub, hCϖ, sub_zero]
          exact Ideal.mem_span_singleton_self _
        · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, hCϖ]
          exact Ideal.zero_mem _
      exact Ideal.mem_span_singleton.mp (Ideal.mem_comap.mp (hle hx))
    · rintro ⟨g, hg⟩
      obtain ⟨g', rfl⟩ := MvPolynomial.map_surjective _ IsLocalRing.residue_surjective g
      have hdiff : x - P * g' ∈ RingHom.ker φ := by
        rw [RingHom.mem_ker, map_sub, map_mul, hg, hφ]
        exact sub_self _
      rw [hker] at hdiff
      have hx : x = (x - P * g') + P * g' := by ring
      rw [hx]
      exact Ideal.add_mem _ (Ideal.mem_sup_right hdiff) (Ideal.mul_mem_right _ _ hPmem)
  unfold Ideal.IsRadical
  intro x hx
  rw [Ideal.mem_radical_iff] at hx
  obtain ⟨n, hn⟩ := hx
  rw [hmem] at hn
  rw [hmem]
  rw [map_pow, hφP] at hn
  rw [hφP]
  exact isRadical_prod_X s n (φ x) hn

/- English proof (translation)
Introduce `O _ _ _ ϖ hϖ m r _ _`. Use `set J : Ideal (MvPolynomial (Fin m) O) := Ideal.span {(∏ i ∈ Finset.univ.filter (fun i : Fin m => (i : ℕ) < r), MvPolynomial.X i) - MvPolynomial.C ϖ} with hJ`. Establish `e : Ideal.span {algebraMap O (MvPolynomial (Fin m) O ⧸ J) ϖ} = Ideal.map (Ideal.Quotient.mk J) (Ideal.span {(MvPolynomial.C ϖ : MvPolynomial (Fin m) O)})`. Rewrite using `[Ideal.map_span, Set.image_singleton, ← Ideal.Quotient.mk_algebraMap, MvPolynomial.algebraMap_eq]`. Rewrite using `[e]`.

Establish `: IsReduced (MvPolynomial (Fin m) O ⧸ (J ⊔ Ideal.span {(MvPolynomial.C ϖ : MvPolynomial (Fin m) O)}))`. Rewrite using `[← Ideal.isRadical_iff_quotient_reduced]`. Conclude with `isRadical_span_sup hϖ (Finset.univ.filter (fun i : Fin m => (i : ℕ) < r))`. Conclude with `isReduced_of_injective (DoubleQuot.quotQuotEquivQuotSup J (Ideal.span {(MvPolynomial.C ϖ : MvPolynomial (Fin m) O)})) (RingEquiv.injective _)`.
-/
theorem special_fibre_isReduced : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (ϖ : O), Irreducible ϖ → ∀ (m r : ℕ), 1 ≤ r → r ≤ m →
    IsReduced ((MvPolynomial (Fin m) O ⧸ Ideal.span {(∏ i ∈ Finset.univ.filter (fun i : Fin m => (i : ℕ) < r), MvPolynomial.X i) - MvPolynomial.C ϖ}) ⧸ Ideal.span {algebraMap O (MvPolynomial (Fin m) O ⧸ Ideal.span {(∏ i ∈ Finset.univ.filter (fun i : Fin m => (i : ℕ) < r), MvPolynomial.X i) - MvPolynomial.C ϖ}) ϖ}) := by
  intro O _ _ _ ϖ hϖ m r _ _
  set J : Ideal (MvPolynomial (Fin m) O) := Ideal.span {(∏ i ∈ Finset.univ.filter
    (fun i : Fin m => (i : ℕ) < r), MvPolynomial.X i) - MvPolynomial.C ϖ} with hJ
  have e : Ideal.span {algebraMap O (MvPolynomial (Fin m) O ⧸ J) ϖ} =
      Ideal.map (Ideal.Quotient.mk J) (Ideal.span {(MvPolynomial.C ϖ : MvPolynomial (Fin m) O)}) := by
    rw [Ideal.map_span, Set.image_singleton, ← Ideal.Quotient.mk_algebraMap,
      MvPolynomial.algebraMap_eq]
  rw [e]
  have : IsReduced (MvPolynomial (Fin m) O ⧸
      (J ⊔ Ideal.span {(MvPolynomial.C ϖ : MvPolynomial (Fin m) O)})) := by
    rw [← Ideal.isRadical_iff_quotient_reduced]
    exact isRadical_span_sup hϖ (Finset.univ.filter (fun i : Fin m => (i : ℕ) < r))
  exact isReduced_of_injective
    (DoubleQuot.quotQuotEquivQuotSup J (Ideal.span {(MvPolynomial.C ϖ : MvPolynomial (Fin m) O)}))
    (RingEquiv.injective _)

end GlobalTheory.CompanionTheory.SemistableSpecial
