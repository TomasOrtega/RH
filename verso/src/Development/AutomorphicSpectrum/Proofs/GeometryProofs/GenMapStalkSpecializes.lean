import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCptGen

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.RegAtMono

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

/- English proof (translation)
Establish `e` using `X.presheaf.stalkSpecializes_comp q.2 h`. Conclude with `congrArg (Scheme.stalkClosedPointTo ξ).hom (congrArg (fun φ => φ.hom x) e)`.
-/
theorem genMap_stalkSpecializes (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p q : Cpt ξ) (h : q.1 ⤳ p.1)
    (x : X.presheaf.stalk p.1) :
    genMap ξ q ((X.presheaf.stalkSpecializes h).hom x) = genMap ξ p x := by
  have e := X.presheaf.stalkSpecializes_comp q.2 h
  exact congrArg (Scheme.stalkClosedPointTo ξ).hom (congrArg (fun φ => φ.hom x) e)

/- English proof (translation)
Rewrite using `[← genMap_stalkSpecializes ξ p q h, ← CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes]`.
-/
theorem genMap_germ_eq (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p q : Cpt ξ) (h : q.1 ⤳ p.1)
    (U : X.Opens) (hp : p.1 ∈ U) (hq : q.1 ∈ U) (t : Γ(X, U)) :
    genMap ξ q ((X.presheaf.germ U q.1 hq).hom t) = genMap ξ p ((X.presheaf.germ U p.1 hp).hom t) := by
  rw [← genMap_stalkSpecializes ξ p q h, ← CommRingCat.comp_apply,
    TopCat.Presheaf.germ_stalkSpecializes]

/- English proof (translation)
Take `⟨u, rfl⟩` from `hx`. Use `⟨(u.isUnit.map (genMap ξ q)).ne_zero, ⟨_, rfl⟩, ⟨(u⁻¹ : (X.presheaf.stalk q.1)ˣ), ?_⟩⟩` and prove the remaining obligations. Conclude with `map_units_inv (genMap ξ q) u`.
-/
theorem unitAt_of_isUnit (ξ : Spec (CommRingCat.of Ω) ⟶ X) (q : Cpt ξ) {x : X.presheaf.stalk q.1}
    (hx : IsUnit x) : unitAt ξ q (genMap ξ q x) := by
  obtain ⟨u, rfl⟩ := hx
  refine ⟨(u.isUnit.map (genMap ξ q)).ne_zero, ⟨_, rfl⟩, ⟨(u⁻¹ : (X.presheaf.stalk q.1)ˣ), ?_⟩⟩
  exact map_units_inv (genMap ξ q) u

/- English proof (translation)
Introduce `X Ω _ ξ p q h`. Use `⟨?_, fun _ => ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨x, rfl⟩`. Conclude with `⟨_, genMap_stalkSpecializes ξ p q h x⟩`. Introduce and unpack `_ ⟨x, rfl⟩`.

Take `⟨_, ⟨U, hU, rfl⟩, hp, -⟩` from `X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ p.1) isOpen_univ`. Establish `hU : IsAffineOpen U` using `hU`. Establish `hq : q.1 ∈ U` using `h.mem_open U.2 hp`. Use `letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨q.1, hq⟩ : U)`. Establish `hloc` using `hU.isLocalization_stalk ⟨q.1, hq⟩`.

Take `⟨⟨r, t⟩, e⟩` from `IsLocalization.surj (hU.primeIdealOf ⟨q.1, hq⟩).asIdeal.primeCompl (S := X.presheaf.stalk q.1) x`. Establish `hu : IsUnit ((X.presheaf.germ U q.1 hq).hom t.1)` using `IsLocalization.map_units (X.presheaf.stalk q.1) t`. Establish `e' : x * (X.presheaf.germ U q.1 hq).hom t.1 = (X.presheaf.germ U q.1 hq).hom r` using `e`. Use `⟨genMap ξ q ((X.presheaf.germ U q.1 hq).hom t.1), ?_, unitAt_of_isUnit ξ q hu, ?_⟩` and prove the remaining obligations. Conclude with `⟨_, (genMap_germ_eq ξ p q h U hp hq _).symm⟩`.

Rewrite using `[mul_comm, ← map_mul, e']`. Conclude with `⟨_, (genMap_germ_eq ξ p q h U hp hq _).symm⟩`.
-/
theorem regAt_mono :
    ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p q : Cpt ξ), q.1 ⤳ p.1 →
      regAt ξ p ≤ regAt ξ q ∧
        (IsCptGen ξ → ∀ a ∈ regAt ξ q, ∃ s ∈ regAt ξ p, unitAt ξ q s ∧ s * a ∈ regAt ξ p) := by
  intro X Ω _ ξ p q h
  refine ⟨?_, fun _ => ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact ⟨_, genMap_stalkSpecializes ξ p q h x⟩
  · rintro _ ⟨x, rfl⟩
    obtain ⟨_, ⟨U, hU, rfl⟩, hp, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ p.1) isOpen_univ
    have hU : IsAffineOpen U := hU
    have hq : q.1 ∈ U := h.mem_open U.2 hp
    letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨q.1, hq⟩ : U)
    have hloc := hU.isLocalization_stalk ⟨q.1, hq⟩
    obtain ⟨⟨r, t⟩, e⟩ := IsLocalization.surj (hU.primeIdealOf ⟨q.1, hq⟩).asIdeal.primeCompl
      (S := X.presheaf.stalk q.1) x
    have hu : IsUnit ((X.presheaf.germ U q.1 hq).hom t.1) :=
      IsLocalization.map_units (X.presheaf.stalk q.1) t
    have e' : x * (X.presheaf.germ U q.1 hq).hom t.1 = (X.presheaf.germ U q.1 hq).hom r := e
    refine ⟨genMap ξ q ((X.presheaf.germ U q.1 hq).hom t.1), ?_, unitAt_of_isUnit ξ q hu, ?_⟩
    · exact ⟨_, (genMap_germ_eq ξ p q h U hp hq _).symm⟩
    · rw [mul_comm, ← map_mul, e']
      exact ⟨_, (genMap_germ_eq ξ p q h U hp hq _).symm⟩

end GlobalTheory.CompanionTheory.Ar.RegAtMono
