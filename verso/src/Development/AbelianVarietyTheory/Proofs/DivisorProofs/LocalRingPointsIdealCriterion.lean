import Mathlib
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace GlobalTheory

/- English proof (translation)
Take `⟨I, e, hf⟩` from `(IsClosedImmersion.Spec_iff (f := pullback.snd j a)).mp inferInstance`. Use `⟨I, fun R _ ψ => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Introduce and unpack `⟨y, hy⟩`. Set `z : Spec (CommRingCat.of R) ⟶ pullback j a` to `pullback.lift y (Spec.map (CommRingCat.ofHom ψ)) hy`. Establish `hz : z ≫ pullback.snd j a = Spec.map (CommRingCat.ofHom ψ)` using `pullback.lift_snd _ _ _`.

Take `⟨χ, hχ⟩` from `Spec.map_surjective (z ≫ e.hom)`. Establish `h1 : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I) ≫ χ) = Spec.map (CommRingCat.ofHom ψ)`. Rewrite using `[Spec.map_comp, hχ, Category.assoc, ← hf, hz]`. Establish `h2` using `Spec.map_injective h1`. Introduce `x hx`.

Use `congrArg (fun g => g.hom x) h2` as an intermediate fact. Simplify using `only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply] at this`. Rewrite using `[RingHom.mem_ker, ← this, Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]`. Introduce `h`. Use `⟨Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift I ψ (fun x hx => h hx))) ≫ e.inv ≫ pullback.fst j a, ?_⟩` and prove the remaining obligations.

Rewrite using `[Category.assoc, Category.assoc, pullback.condition, hf, Category.assoc, Iso.inv_hom_id_assoc, ← Spec.map_comp_assoc]`. Use `congr 2`.
-/
theorem exists_ideal_factor_closedImmersion_iff (A : Type) [CommRing A] (X Y : Scheme.{0})
    (a : Spec (CommRingCat.of A) ⟶ X) (j : Y ⟶ X) [IsClosedImmersion j] :
    ∃ I : Ideal A, ∀ (R : Type) [CommRing R] (ψ : A →+* R),
      (∃ y : Spec (CommRingCat.of R) ⟶ Y, y ≫ j = Spec.map (CommRingCat.ofHom ψ) ≫ a) ↔
        I ≤ RingHom.ker ψ := by
  obtain ⟨I, e, hf⟩ := (IsClosedImmersion.Spec_iff (f := pullback.snd j a)).mp inferInstance
  refine ⟨I, fun R _ ψ => ⟨?_, ?_⟩⟩
  · rintro ⟨y, hy⟩
    let z : Spec (CommRingCat.of R) ⟶ pullback j a := pullback.lift y (Spec.map (CommRingCat.ofHom ψ)) hy
    have hz : z ≫ pullback.snd j a = Spec.map (CommRingCat.ofHom ψ) := pullback.lift_snd _ _ _
    obtain ⟨χ, hχ⟩ := Spec.map_surjective (z ≫ e.hom)
    have h1 : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I) ≫ χ) = Spec.map (CommRingCat.ofHom ψ) := by
      rw [Spec.map_comp, hχ, Category.assoc, ← hf, hz]
    have h2 := Spec.map_injective h1
    intro x hx
    have := congrArg (fun g => g.hom x) h2
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply] at this
    rw [RingHom.mem_ker, ← this, Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]
  · intro h
    refine ⟨Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift I ψ (fun x hx => h hx))) ≫ e.inv ≫ pullback.fst j a, ?_⟩
    rw [Category.assoc, Category.assoc, pullback.condition, hf, Category.assoc, Iso.inv_hom_id_assoc,
      ← Spec.map_comp_assoc]
    congr 2

/- English proof (translation)
Introduce `A _ _ X Y a j hj J H`. Take `⟨I, hI⟩` from `exists_ideal_factor_closedImmersion_iff A X Y a j`. Establish `key : ∀ (K : Ideal A), K ≠ ⊤ → (I ≤ K ↔ J ≤ K)`. Introduce `K hK`. Use `haveI : Nontrivial (A ⧸ K) := Ideal.Quotient.nontrivial_iff.mpr hK`.

Use `haveI : IsLocalRing (A ⧸ K) := IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective`. Use `(hI (A ⧸ K) (Ideal.Quotient.mk K)).symm.trans (H (A ⧸ K) (Ideal.Quotient.mk K))` as an intermediate fact. Simplify `this` using `[Ideal.mk_ker]`. Establish `hIJ : I = J`. Apply `le_antisymm` to reduce the goal to its premises.

Distinguish the cases in `hJ : J = ⊤`. Rewrite using `[hJ]`. Conclude with `le_top`. Conclude with `(key J hJ).mpr le_rfl`. Distinguish the cases in `hI' : I = ⊤`.

Rewrite using `[hI']`. Conclude with `le_top`. Conclude with `(key I hI').mp le_rfl`. Introduce `R _ ψ`. Rewrite using `[← hIJ]`.

Conclude with `hI R ψ`.
-/
theorem factor_closedImmersion_iff_of_local : ∀ (A : Type) [CommRing A] [IsLocalRing A] (X Y : Scheme.{0}) (a : Spec (CommRingCat.of A) ⟶ X) (j : Y ⟶ X), IsClosedImmersion j → ∀ J : Ideal A, (∀ (R : Type) [CommRing R] [IsLocalRing R] (ψ : A →+* R), (∃ y : Spec (CommRingCat.of R) ⟶ Y, y ≫ j = Spec.map (CommRingCat.ofHom ψ) ≫ a) ↔ J ≤ RingHom.ker ψ) → ∀ (R : Type) [CommRing R] (ψ : A →+* R), (∃ y : Spec (CommRingCat.of R) ⟶ Y, y ≫ j = Spec.map (CommRingCat.ofHom ψ) ≫ a) ↔ J ≤ RingHom.ker ψ := by
  intro A _ _ X Y a j hj J H
  obtain ⟨I, hI⟩ := exists_ideal_factor_closedImmersion_iff A X Y a j
  have key : ∀ (K : Ideal A), K ≠ ⊤ → (I ≤ K ↔ J ≤ K) := by
    intro K hK
    haveI : Nontrivial (A ⧸ K) := Ideal.Quotient.nontrivial_iff.mpr hK
    haveI : IsLocalRing (A ⧸ K) := IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
    have := (hI (A ⧸ K) (Ideal.Quotient.mk K)).symm.trans (H (A ⧸ K) (Ideal.Quotient.mk K))
    simpa [Ideal.mk_ker] using this
  have hIJ : I = J := by
    apply le_antisymm
    · by_cases hJ : J = ⊤
      · rw [hJ]; exact le_top
      · exact (key J hJ).mpr le_rfl
    · by_cases hI' : I = ⊤
      · rw [hI']; exact le_top
      · exact (key I hI').mp le_rfl
  intro R _ ψ
  rw [← hIJ]
  exact hI R ψ

end GlobalTheory
