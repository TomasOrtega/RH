import Mathlib

open Polynomial Matrix IsLocalRing TensorProduct

/- English proof (translation)
Take `⟨I, hI, ⟨e⟩⟩` from `isSimpleModule_iff_quot_maximal.mp (inferInstance : IsSimpleModule A X)`. Establish `: I = maximalIdeal A` using `IsLocalRing.eq_maximalIdeal hI`. Substitute `this` using the available equality. Conclude with `⟨e.toEquiv⟩`.
-/
private theorem UpperTheory.V.AlgebraTools.simple_module_equiv_residue_field {A X : Type} [CommRing A] [IsLocalRing A] [AddCommGroup X] [Module A X] [IsSimpleModule A X] : Nonempty (X ≃ ResidueField A) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp (inferInstance : IsSimpleModule A X)
  have : I = maximalIdeal A := IsLocalRing.eq_maximalIdeal hI
  subst this
  exact ⟨e.toEquiv⟩

/- English proof (translation)
Proceed by induction on `h with`. Consider the case `@of_subsingleton M _ _ _`. Use `⟨Finite.of_subsingleton, ?_⟩` and prove the remaining obligations. Rewrite using `[Module.length_eq_zero]`. Simplify using `[Nat.card_eq_one_iff_unique]`.

Consider the case `@of_simple_quotient M _ _ N _ hN ih`. Take `⟨hfin, hcard⟩` from `ih`. Take `⟨e⟩` from `UpperTheory.V.AlgebraTools.simple_module_equiv_residue_field (A := A) (X := M ⧸ N)`. Establish `hq : Nat.card (M ⧸ N) = Nat.card (ResidueField A)` using `Nat.card_congr e`. Establish `hNt : Module.length A N ≠ ⊤` using `Module.length_ne_top_iff.mpr hN`.

Establish `hlen : Module.length A M = Module.length A N + 1`. Rewrite using `[Module.length_eq_add_of_exact N.subtype N.mkQ N.injective_subtype N.mkQ_surjective (LinearMap.exact_subtype_mkQ N), Module.length_eq_one A (M ⧸ N)]`. Establish `hc : Nat.card M = Nat.card (M ⧸ N) * Nat.card N` using `AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup N.toAddSubgroup`. Establish `hq0 : Nat.card (ResidueField A) ≠ 0` using `Nat.card_pos.ne'`. Establish `hM : Nat.card M = Nat.card (ResidueField A) ^ ((Module.length A N).toNat + 1)`.

Rewrite using `[hc, hq, hcard, pow_succ, mul_comm]`. Use `⟨Nat.finite_of_card_ne_zero (by rw [hM]; exact pow_ne_zero _ hq0), ?_⟩` and prove the remaining obligations. Rewrite using `[hM, hlen, ENat.toNat_add hNt ENat.one_ne_top]`. Simplify using the standard rewrite rules.
-/
private theorem UpperTheory.V.AlgebraTools.card_finite_length_module {A : Type} [CommRing A] [IsLocalRing A] [Finite (ResidueField A)] {X : Type} [AddCommGroup X] [Module A X] (h : IsFiniteLength A X) :
    Finite X ∧ Nat.card X = Nat.card (ResidueField A) ^ (Module.length A X).toNat := by
  induction h with
  | @of_subsingleton M _ _ _ =>
    refine ⟨Finite.of_subsingleton, ?_⟩
    rw [Module.length_eq_zero]
    simp [Nat.card_eq_one_iff_unique]
  | @of_simple_quotient M _ _ N _ hN ih =>
    obtain ⟨hfin, hcard⟩ := ih
    obtain ⟨e⟩ := UpperTheory.V.AlgebraTools.simple_module_equiv_residue_field (A := A) (X := M ⧸ N)
    have hq : Nat.card (M ⧸ N) = Nat.card (ResidueField A) := Nat.card_congr e
    have hNt : Module.length A N ≠ ⊤ := Module.length_ne_top_iff.mpr hN
    have hlen : Module.length A M = Module.length A N + 1 := by
      rw [Module.length_eq_add_of_exact N.subtype N.mkQ N.injective_subtype N.mkQ_surjective
        (LinearMap.exact_subtype_mkQ N), Module.length_eq_one A (M ⧸ N)]
    have hc : Nat.card M = Nat.card (M ⧸ N) * Nat.card N :=
      AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup N.toAddSubgroup
    have hq0 : Nat.card (ResidueField A) ≠ 0 := Nat.card_pos.ne'
    have hM : Nat.card M = Nat.card (ResidueField A) ^ ((Module.length A N).toNat + 1) := by
      rw [hc, hq, hcard, pow_succ, mul_comm]
    refine ⟨Nat.finite_of_card_ne_zero (by rw [hM]; exact pow_ne_zero _ hq0), ?_⟩
    rw [hM, hlen, ENat.toNat_add hNt ENat.one_ne_top]
    simp

/- English proof (translation)
Introduce `A X _ _ _ _ _`. Establish `key : Finite X → Module.length A X ≠ ⊤` using `fun h => by haveI := h`. Conclude with `Module.length_ne_top_iff.mpr (isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, isArtinian_of_finite⟩)`. Use `⟨⟨key, fun h => (UpperTheory.V.AlgebraTools.card_finite_length_module (Module.length_ne_top_iff.mp h)).1⟩, fun h => ?_⟩` and prove the remaining obligations. Conclude with `(UpperTheory.V.AlgebraTools.card_finite_length_module (Module.length_ne_top_iff.mp (key h))).2`.
-/
theorem UpperTheory.V.AlgebraTools.card_eq_pow_length :
    ∀ {A X : Type} [CommRing A] [IsLocalRing A] [Finite (ResidueField A)] [AddCommGroup X] [Module A X], (Finite X ↔ Module.length A X ≠ ⊤) ∧ (Finite X → Nat.card X = Nat.card (ResidueField A) ^ (Module.length A X).toNat) := by
  intro A X _ _ _ _ _
  have key : Finite X → Module.length A X ≠ ⊤ := fun h => by
    haveI := h
    exact Module.length_ne_top_iff.mpr
      (isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, isArtinian_of_finite⟩)
  refine ⟨⟨key, fun h => (UpperTheory.V.AlgebraTools.card_finite_length_module (Module.length_ne_top_iff.mp h)).1⟩, fun h => ?_⟩
  exact (UpperTheory.V.AlgebraTools.card_finite_length_module (Module.length_ne_top_iff.mp (key h))).2
