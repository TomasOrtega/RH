import Development.EtaleCohomology.KummerTheory.TwSecPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory.SecSHPf

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `x y hxy`. Establish `h` using `Presheaf.equalizerSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)) (X := op U) x y hxy`. Use `hU _ h` as an intermediate fact. Simplify using `[Presheaf.equalizerSieve] at this`.

Conclude with `this`. Introduce `s`. Establish `h` using `Presheaf.imageSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)) (U := op U) s`. Take `⟨t, ht⟩` from `hU _ h`. Use `⟨t, ?_⟩` and prove the remaining obligations.

Simplify using `at ht`. Conclude with `ht`.
-/
theorem bij_of_top (R : Type) [CommRing R] (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)) (U : Scheme.{0})
    (hU : ∀ S ∈ Scheme.etaleTopology U, S (𝟙 U)) : Function.Bijective (ofRings.sec M U) := by
  constructor
  · intro x y hxy
    have h := Presheaf.equalizerSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M))
      (X := op U) x y hxy
    have := hU _ h
    simp [Presheaf.equalizerSieve] at this
    exact this
  · intro s
    have h := Presheaf.imageSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)) (U := op U) s
    obtain ⟨t, ht⟩ := hU _ h
    refine ⟨t, ?_⟩
    simp at ht
    exact ht

def ShSect : Prop := ∀ (A : Type) [CommRing A], SH A → ∀ (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of A)),
  Etale f → Surjective f → ∃ s : Spec (CommRingCat.of A) ⟶ Y, s ≫ f = 𝟙 _

/- English proof (translation)
Introduce `S hS`. Take `⟨hH, hsc⟩` from `hA`. Take `⟨𝒰, hle⟩` from `Scheme.mem_grothendieckTopology_iff.1 hS`. Take `⟨i, y, hy⟩` from `((Scheme.presieve₀_mem_precoverage_iff 𝒰.toPreZeroHypercover).1 𝒰.mem₀).1 (IsLocalRing.closedPoint A : Spec (CommRingCat.of A))`. Establish `he : Etale (𝒰.f i)` using `𝒰.map_prop i`.

Establish `hsurj : Surjective (𝒰.f i)`. Use `⟨fun p => ?_⟩` and prove the remaining obligations. Establish `hsp : p ⤳ (𝒰.f i) y`. Rewrite using `[hy]`. Conclude with `IsLocalRing.specializes_closedPoint (R := A) p`.

Take `⟨y', -, hy'⟩` from `Flat.generalizingMap (𝒰.f i) hsp`. Conclude with `⟨y', hy'⟩`. Take `⟨s, hs'⟩` from `hs A ⟨hH, hsc⟩ _ (𝒰.f i) he hsurj`. Use `S.downward_closed (hle (𝒰.X i) (𝒰.f i) (Presieve.ofArrows.mk i)) s` as an intermediate fact. Rewrite `this` using `[hs']`. Then use the resulting hypothesis.
-/
theorem top_of_sect (hs : ShSect) (A : Type) [CommRing A] (hA : SH A) :
    ∀ S ∈ Scheme.etaleTopology (Spec (CommRingCat.of A)), S (𝟙 _) := by
  intro S hS
  obtain ⟨hH, hsc⟩ := hA
  obtain ⟨𝒰, hle⟩ := Scheme.mem_grothendieckTopology_iff.1 hS
  obtain ⟨i, y, hy⟩ := ((Scheme.presieve₀_mem_precoverage_iff 𝒰.toPreZeroHypercover).1 𝒰.mem₀).1
    (IsLocalRing.closedPoint A : Spec (CommRingCat.of A))
  have he : Etale (𝒰.f i) := 𝒰.map_prop i
  have hsurj : Surjective (𝒰.f i) := by
    refine ⟨fun p => ?_⟩
    have hsp : p ⤳ (𝒰.f i) y := by
      rw [hy]; exact IsLocalRing.specializes_closedPoint (R := A) p
    obtain ⟨y', -, hy'⟩ := Flat.generalizingMap (𝒰.f i) hsp
    exact ⟨y', hy'⟩
  obtain ⟨s, hs'⟩ := hs A ⟨hH, hsc⟩ _ (𝒰.f i) he hsurj
  have := S.downward_closed (hle (𝒰.X i) (𝒰.f i) (Presieve.ofArrows.mk i)) s
  rwa [hs'] at this

end LateralTheory.KummerTheory.SecSHPf

namespace LateralTheory.KummerTheory

/- English proof (translation)
Introduce `A _ hA R _ M`. Conclude with `SecSHPf.bij_of_top R M _ (SecSHPf.top_of_sect h A hA)`.
-/
theorem SecSH_of (h : SecSHPf.ShSect) : SecSH := by
  intro A _ hA R _ M
  exact SecSHPf.bij_of_top R M _ (SecSHPf.top_of_sect h A hA)

end LateralTheory.KummerTheory
