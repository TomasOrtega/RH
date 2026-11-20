import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace GlobalTheory.IdealSectionsFactorization

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Assume the hypotheses and unpack their components. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem comp_eq_iff_factors {S X B W : Scheme.{0}} (p : X ⟶ B) (x y : S ⟶ X)
    (h : x ≫ p = y ≫ p) (g : W ⟶ S) :
    g ≫ x = g ≫ y ↔
      ∃ l : W ⟶ pullback (pullback.lift x y h) (pullback.diagonal p),
        l ≫ pullback.fst _ _ = g := by
  constructor
  · intro hg
    refine ⟨pullback.lift g (g ≫ x) ?_, pullback.lift_fst _ _ _⟩
    apply pullback.hom_ext
    · simp [pullback.diagonal_fst, pullback.lift_fst]
    · simp [pullback.diagonal_snd, pullback.lift_snd, hg]
  · rintro ⟨l, rfl⟩
    have hc := pullback.condition (f := pullback.lift x y h) (g := pullback.diagonal p)
    have h1 := congrArg (· ≫ pullback.fst p p) hc
    have h2 := congrArg (· ≫ pullback.snd p p) hc
    simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.diagonal_fst,
      pullback.diagonal_snd, Category.comp_id] at h1 h2
    rw [Category.assoc, Category.assoc, h1, h2]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Reduce the equality to equality of the corresponding arguments.
-/
theorem factors_iff_kills {R T : Type} [CommRing R] [CommRing T] (I : Ideal R) (ψ : R →+* T) :
    (∃ l : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of (R ⧸ I)),
      l ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) = Spec.map (CommRingCat.ofHom ψ)) ↔
      ∀ r ∈ I, ψ r = 0 := by
  constructor
  · rintro ⟨l, hl⟩ r hr
    obtain ⟨φ, rfl⟩ := Spec.map_surjective l
    rw [← Spec.map_comp] at hl
    have h := Spec.map_injective hl
    have h' : φ.hom (Ideal.Quotient.mk I r) = ψ r :=
      congrArg (fun k : CommRingCat.of R ⟶ CommRingCat.of T => k.hom r) h
    rw [← h', Ideal.Quotient.eq_zero_iff_mem.mpr hr, map_zero]
  · intro h
    refine ⟨Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift I ψ h)), ?_⟩
    rw [← Spec.map_comp]
    congr 1

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Supply the required witnesses or components. Assume the hypotheses and unpack their components. Supply the required witnesses or components.
-/
theorem exists_ideal_sections_eq (R : Type) [CommRing R]
    (X : Over (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R)) (hX : IsSeparated X.hom)
    (x y : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R ⟶ X.left)
    (hx : x ≫ X.hom = 𝟙 (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R))
    (hy : y ≫ X.hom = 𝟙 (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R)) :
    ∃ I : Ideal R, ∀ (T : Type) [CommRing T] (ψ : R →+* T),
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap ψ ≫ x = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap ψ ≫ y ↔
        ∀ r ∈ I, ψ r = 0 := by
  have h : x ≫ X.hom = y ≫ X.hom := hx.trans hy.symm
  have hc : IsClosedImmersion
      (pullback.fst (pullback.lift x y h) (pullback.diagonal X.hom)) :=
    IsClosedImmersion.isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback _ _).flip hX.isClosedImmersion_diagonal
  obtain ⟨I, e, he⟩ := IsClosedImmersion.Spec_iff.mp hc
  refine ⟨I, fun T _ ψ => ?_⟩
  rw [comp_eq_iff_factors X.hom x y h, ← factors_iff_kills I ψ, he]
  constructor
  · rintro ⟨l, hl⟩
    exact ⟨l ≫ e.hom, by rw [Category.assoc]; exact hl⟩
  · rintro ⟨l, hl⟩
    exact ⟨l ≫ e.inv, by rw [Category.assoc, e.inv_hom_id_assoc]; exact hl⟩

end GlobalTheory.IdealSectionsFactorization
