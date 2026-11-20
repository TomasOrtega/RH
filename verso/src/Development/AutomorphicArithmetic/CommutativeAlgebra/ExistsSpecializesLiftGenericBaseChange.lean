import Mathlib
import Development.EtaleCohomology.EtaleSheaves.H0TwistOverClosedField

open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4

/- English proof (translation)
Substitute `hg` using the available equality. Establish `hfst : ∀ p, (pullback.fst w (j ≫ i)) ((pullbackLeftPullbackSndIso w i j).hom p) = (pullback.fst w i) ((pullback.fst (pullback.snd w i) j) p)`. Introduce `p`. Use `show ((pullbackLeftPullbackSndIso w i j).hom ≫ pullback.fst w (j ≫ i)).base p = (pullback.fst (pullback.snd w i) j ≫ pullback.fst w i).base p`. Rewrite using `[pullbackLeftPullbackSndIso_hom_fst]`.

Establish `hy : (pullbackLeftPullbackSndIso w i j).hom ((pullbackLeftPullbackSndIso w i j).inv y') = y'` using `by show ((pullbackLeftPullbackSndIso w i j).inv ≫ (pullbackLeftPullbackSndIso w i j).hom).base y' = y'`. Rewrite using `[Iso.inv_hom_id]`. Both sides reduce to the same expression. Take `⟨z, hz⟩` from `hxr`. Establish `hxz : z ⤳ (pullback.fst (pullback.snd w i) j) ((pullbackLeftPullbackSndIso w i j).inv y')`.

Rewrite using `[← (IsPreimmersion.isEmbedding (pullback.fst w i)).isInducing.specializes_iff, hz, ← hfst, hy]`. Conclude with `hx`. Take `⟨x'', hx'', hx''z⟩` from `Flat.generalizingMap (pullback.fst (pullback.snd w i) j) hxz`. Use `⟨(pullbackLeftPullbackSndIso w i j).hom x'', ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← hy]`.

Conclude with `hx''.map (Scheme.Hom.continuous _)`. Rewrite using `[hfst, hx''z, hz]`.
-/
private lemma aux {W S T U : Scheme.{0}} (w : W ⟶ S) (i : T ⟶ S) (j : U ⟶ T) (g : U ⟶ S)
    (hg : j ≫ i = g) [Flat j] [IsPreimmersion i] (y' : ↑(pullback w g)) (x : W)
    (hx : x ⤳ (pullback.fst w g) y') (hxr : x ∈ Set.range (pullback.fst w i)) :
    ∃ x' : ↑(pullback w g), x' ⤳ y' ∧ (pullback.fst w g) x' = x := by
  subst hg
  have hfst : ∀ p, (pullback.fst w (j ≫ i)) ((pullbackLeftPullbackSndIso w i j).hom p) =
      (pullback.fst w i) ((pullback.fst (pullback.snd w i) j) p) := by
    intro p
    show ((pullbackLeftPullbackSndIso w i j).hom ≫ pullback.fst w (j ≫ i)).base p =
      (pullback.fst (pullback.snd w i) j ≫ pullback.fst w i).base p
    rw [pullbackLeftPullbackSndIso_hom_fst]
  have hy : (pullbackLeftPullbackSndIso w i j).hom ((pullbackLeftPullbackSndIso w i j).inv y') = y' := by
    show ((pullbackLeftPullbackSndIso w i j).inv ≫ (pullbackLeftPullbackSndIso w i j).hom).base y' = y'
    rw [Iso.inv_hom_id]
    rfl
  obtain ⟨z, hz⟩ := hxr
  have hxz : z ⤳ (pullback.fst (pullback.snd w i) j) ((pullbackLeftPullbackSndIso w i j).inv y') := by
    rw [← (IsPreimmersion.isEmbedding (pullback.fst w i)).isInducing.specializes_iff, hz, ← hfst, hy]
    exact hx
  obtain ⟨x'', hx'', hx''z⟩ := Flat.generalizingMap (pullback.fst (pullback.snd w i) j) hxz
  refine ⟨(pullbackLeftPullbackSndIso w i j).hom x'', ?_, ?_⟩
  · rw [← hy]
    exact hx''.map (Scheme.Hom.continuous _)
  · rw [hfst, hx''z, hz]

/- English proof (translation)
Apply `PrimeSpectrum.ext` to reduce the goal to its premises. Conclude with `Ideal.comap_bot_of_injective f hf`.
-/
private lemma spec_bot {A B : Type} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    (f : A →+* B) (hf : Function.Injective f) :
    Spec.map (CommRingCat.ofHom f) (⊥ : PrimeSpectrum B) = (⊥ : PrimeSpectrum A) := by
  apply PrimeSpectrum.ext
  exact Ideal.comap_bot_of_injective f hf

/- English proof (translation)
The claim follows from `PrimeSpectrum.ext (Ideal.eq_bot_of_prime _)`.
-/
private lemma spec_field {F : Type} [Field F] (z : PrimeSpectrum F) : z = ⊥ :=
  PrimeSpectrum.ext (Ideal.eq_bot_of_prime _)

/- English proof (translation)
The claim follows from `le_bot_iff.1 ((PrimeSpectrum.le_iff_specializes _ _).2 h)`.
-/
private lemma spec_gen {A : Type} [CommRing A] [IsDomain A] (a : PrimeSpectrum A)
    (h : a ⤳ (⊥ : PrimeSpectrum A)) : a = ⊥ :=
  le_bot_iff.1 ((PrimeSpectrum.le_iff_specializes _ _).2 h)

/- English proof (translation)
Introduce `R Ω _ _ _ _ hinj W w y' x hx`. Establish `hRK : Function.Injective (algebraMap R (FractionRing R))` using `IsFractionRing.injective R _`. Use `letI : Algebra (FractionRing R) Ω := (IsFractionRing.lift hinj : FractionRing R →+* Ω).toAlgebra`. Use `haveI : IsPreimmersion (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))) := IsPreimmersion.of_isLocalization (nonZeroDivisors R)`. Establish `hcomp : (algebraMap (FractionRing R) Ω).comp (algebraMap R (FractionRing R)) = algebraMap R Ω` using `IsLocalization.lift_comp _`.

Establish `hg : Spec.map (CommRingCat.ofHom (algebraMap (FractionRing R) Ω)) ≫ Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) = Spec.map (CommRingCat.ofHom (algebraMap R Ω))`. Rewrite using `[← Spec.map_comp, ← CommRingCat.ofHom_comp, hcomp]`. Apply `aux w (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))) (Spec.map (CommRingCat.ofHom (algebraMap (FractionRing R) Ω))) _ hg y' x hx` to reduce the goal to its premises. Establish `hwx : (show PrimeSpectrum R from w x) = ⊥`. Apply `spec_gen` to reduce the goal to its premises.

Establish `h1` using `hx.map w.continuous`. Establish `h2 : w (pullback.fst w (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) y') = Spec.map (CommRingCat.ofHom (algebraMap R Ω)) (pullback.snd w (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) y')` using `by show (pullback.fst w (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) ≫ w).base y' = (pullback.snd w (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) ≫ Spec.map (CommRingCat.ofHom (algebraMap R Ω))).base y'`. Rewrite using `[pullback.condition]`. Rewrite `h1` using `[h2, spec_field (pullback.snd w (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) y'), spec_bot _ hinj]`. Conclude with `h1`.

Take `⟨z, hz, -⟩` from `Scheme.Pullback.exists_preimage_pullback (f := w) (g := Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))) x (⊥ : PrimeSpectrum (FractionRing R)) (by show (show PrimeSpectrum R from w x) = _`. Rewrite using `[hwx, spec_bot _ hRK])`. Conclude with `⟨z, hz⟩`.
-/
theorem UpperTheory.exists_specializes_lift_generic_base_change :
    ∀ (R Ω : Type) [CommRing R] [IsDomain R] [Field Ω] [Algebra R Ω], Function.Injective (algebraMap R Ω) → ∀ {W : Scheme.{0}} (w : W ⟶ Sp R) (y' : ↑(pullback w (Spec.map (CommRingCat.ofHom (algebraMap R Ω))))) (x : W), x ⤳ (pullback.fst w (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))) y' → ∃ x' : ↑(pullback w (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))), x' ⤳ y' ∧ (pullback.fst w (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))) x' = x := by
  intro R Ω _ _ _ _ hinj W w y' x hx
  have hRK : Function.Injective (algebraMap R (FractionRing R)) := IsFractionRing.injective R _
  letI : Algebra (FractionRing R) Ω := (IsFractionRing.lift hinj : FractionRing R →+* Ω).toAlgebra
  haveI : IsPreimmersion (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  have hcomp : (algebraMap (FractionRing R) Ω).comp (algebraMap R (FractionRing R)) =
      algebraMap R Ω := IsLocalization.lift_comp _
  have hg : Spec.map (CommRingCat.ofHom (algebraMap (FractionRing R) Ω)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) =
      Spec.map (CommRingCat.ofHom (algebraMap R Ω)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hcomp]
  apply aux w (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))))
    (Spec.map (CommRingCat.ofHom (algebraMap (FractionRing R) Ω))) _ hg y' x hx
  have hwx : (show PrimeSpectrum R from w x) = ⊥ := by
    apply spec_gen
    have h1 := hx.map w.continuous
    have h2 : w (pullback.fst w (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) y') =
        Spec.map (CommRingCat.ofHom (algebraMap R Ω))
          (pullback.snd w (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) y') := by
      show (pullback.fst w (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) ≫ w).base y' =
        (pullback.snd w (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R Ω))).base y'
      rw [pullback.condition]
    rw [h2, spec_field (pullback.snd w (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) y'),
      spec_bot _ hinj] at h1
    exact h1
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := w)
    (g := Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))) x
    (⊥ : PrimeSpectrum (FractionRing R)) (by
      show (show PrimeSpectrum R from w x) = _
      rw [hwx, spec_bot _ hRK])
  exact ⟨z, hz⟩
