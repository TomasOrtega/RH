import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerElements.SamePrimesMulPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.StickelbergerAt
import Development.AutomorphicArithmetic.AutomorphicVarieties.StmtFields
import Mathlib.RingTheory.Ideal.Norm.RelNorm

open NumberField UpperTheory.V UpperTheory.V.Kum UpperTheory.V.Stick UpperTheory.V.Stk

/- English proof (translation)
Rewrite using `[Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]`. Conclude with `(Nat.card_congr (Ideal.quotientEquiv I (I.map e) e rfl).toEquiv).symm`.
-/
private theorem absNorm_map_equiv {C : Type} [Field C] [NumberField C] (e : 𝓞 C ≃+* 𝓞 C) (I : Ideal (𝓞 C)) :
    Ideal.absNorm (I.map e) = Ideal.absNorm I := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr (Ideal.quotientEquiv I (I.map e) e rfl).toEquiv).symm

/- English proof (translation)
Establish `hle : (Ideal.relNorm ℤ I).map (algebraMap ℤ (𝓞 C)) ≤ ∏ g : Gal(C/ℚ), I.map (RingOfIntegers.mapRingEquiv g.toRingEquiv)`. Rewrite using `[Ideal.map_le_iff_le_comap, Ideal.relNorm_apply, Ideal.span_le]`. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Establish `h1 : algebraMap ℤ (𝓞 C) (Algebra.intNorm ℤ (𝓞 C) x) = ∏ g : Gal(C/ℚ), RingOfIntegers.mapRingEquiv g.toRingEquiv x`. Apply `IsFractionRing.injective (𝓞 C) C` to reduce the goal to its premises.

Rewrite using `[← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply ℤ ℚ C, Algebra.algebraMap_intNorm (L := C), Algebra.norm_eq_prod_automorphisms, map_prod]`. Both sides reduce to the same expression. Express the relevant statement in the definitionally equal form `algebraMap ℤ (𝓞 C) (Algebra.intNorm ℤ (𝓞 C) x) ∈ (∏ g : Gal(C/ℚ), I.map (RingOfIntegers.mapRingEquiv g.toRingEquiv) : Ideal (𝓞 C))`. Rewrite using `[h1]`. Conclude with `Ideal.prod_mem_prod fun g _ => Ideal.mem_map_of_mem _ hx`.

Take `⟨J, hJ⟩` from `Ideal.dvd_iff_le.2 hle`. Establish `hn` using `congrArg Ideal.absNorm hJ`. Rewrite `hn` using `[map_mul, map_prod, Ideal.absNorm_algebraMap, Ideal.absNorm_relNorm]`. Simplify using `only [absNorm_map_equiv, Finset.prod_const, Finset.card_univ] at hn`. Rewrite `hn` using `[RingOfIntegers.rank, ← IsGalois.card_aut_eq_finrank, Nat.card_eq_fintype_card]`.

Establish `h0 : Ideal.absNorm I ^ Fintype.card Gal(C/ℚ) ≠ 0` using `pow_ne_zero _ fun h => hI (Ideal.absNorm_eq_zero_iff.1 h)`. Establish `hJ1 : Ideal.absNorm J = 1` using `(mul_left_cancel₀ h0 ((mul_one _).trans hn)).symm`. Rewrite using `[hJ, Ideal.absNorm_eq_one_iff.1 hJ1, Ideal.mul_top]`.
-/
private theorem prod_conj {C : Type} [Field C] [NumberField C] [IsGalois ℚ C] (I : Ideal (𝓞 C)) (hI : I ≠ ⊥) :
    ∏ g : Gal(C/ℚ), I.map (RingOfIntegers.mapRingEquiv g.toRingEquiv) =
      (Ideal.relNorm ℤ I).map (algebraMap ℤ (𝓞 C)) := by
  have hle : (Ideal.relNorm ℤ I).map (algebraMap ℤ (𝓞 C)) ≤
      ∏ g : Gal(C/ℚ), I.map (RingOfIntegers.mapRingEquiv g.toRingEquiv) := by
    rw [Ideal.map_le_iff_le_comap, Ideal.relNorm_apply, Ideal.span_le]
    rintro _ ⟨x, hx, rfl⟩
    have h1 : algebraMap ℤ (𝓞 C) (Algebra.intNorm ℤ (𝓞 C) x) =
        ∏ g : Gal(C/ℚ), RingOfIntegers.mapRingEquiv g.toRingEquiv x := by
      apply IsFractionRing.injective (𝓞 C) C
      rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply ℤ ℚ C,
        Algebra.algebraMap_intNorm (L := C), Algebra.norm_eq_prod_automorphisms, map_prod]
      rfl
    change algebraMap ℤ (𝓞 C) (Algebra.intNorm ℤ (𝓞 C) x) ∈
      (∏ g : Gal(C/ℚ), I.map (RingOfIntegers.mapRingEquiv g.toRingEquiv) : Ideal (𝓞 C))
    rw [h1]
    exact Ideal.prod_mem_prod fun g _ => Ideal.mem_map_of_mem _ hx
  obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.2 hle
  have hn := congrArg Ideal.absNorm hJ
  rw [map_mul, map_prod, Ideal.absNorm_algebraMap, Ideal.absNorm_relNorm] at hn
  simp only [absNorm_map_equiv, Finset.prod_const, Finset.card_univ] at hn
  rw [RingOfIntegers.rank, ← IsGalois.card_aut_eq_finrank, Nat.card_eq_fintype_card] at hn
  have h0 : Ideal.absNorm I ^ Fintype.card Gal(C/ℚ) ≠ 0 :=
    pow_ne_zero _ fun h => hI (Ideal.absNorm_eq_zero_iff.1 h)
  have hJ1 : Ideal.absNorm J = 1 := (mul_left_cancel₀ h0 ((mul_one _).trans hn)).symm
  rw [hJ, Ideal.absNorm_eq_one_iff.1 hJ1, Ideal.mul_top]

/- English proof (translation)
Introduce `C _ _ _ c`. Take `⟨I, rfl⟩` from `ClassGroup.mk0_surjective c`. Simplify using `only [class_map_mk0]`. Rewrite using `[← map_prod]`. Use `set J := ∏ g : Gal(C/ℚ), idMap g.toRingEquiv I with hJ`.

Establish `hv : (J : Ideal (𝓞 C)) = (Ideal.relNorm ℤ I.1).map (algebraMap ℤ (𝓞 C))`. Rewrite using `[← prod_conj I.1 (nonZeroDivisors.ne_zero I.2), hJ, Submonoid.coe_finset_prod]`. Both sides reduce to the same expression. Use `(ClassGroup.mk0_eq_one_iff J.2).2 ?_` and prove the remaining obligations. Rewrite using `[hv, Ideal.relNorm_int, Ideal.map_span, Set.image_singleton]`.

Conclude with `⟨⟨_, rfl⟩⟩`.
-/
theorem UpperTheory.V.Stk.prod_galois_classGroup_map_eq_one :
    ∀ (C : Type) [Field C] [NumberField C] [IsGalois ℚ C] (c : ClassGroup (𝓞 C)),
      ∏ g : Gal(C/ℚ), clMap g.toRingEquiv c = 1 := by
  intro C _ _ _ c
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective c
  simp only [class_map_mk0]
  rw [← map_prod]
  set J := ∏ g : Gal(C/ℚ), idMap g.toRingEquiv I with hJ
  have hv : (J : Ideal (𝓞 C)) = (Ideal.relNorm ℤ I.1).map (algebraMap ℤ (𝓞 C)) := by
    rw [← prod_conj I.1 (nonZeroDivisors.ne_zero I.2), hJ, Submonoid.coe_finset_prod]
    rfl
  refine (ClassGroup.mk0_eq_one_iff J.2).2 ?_
  rw [hv, Ideal.relNorm_int, Ideal.map_span, Set.image_singleton]
  exact ⟨⟨_, rfl⟩⟩
