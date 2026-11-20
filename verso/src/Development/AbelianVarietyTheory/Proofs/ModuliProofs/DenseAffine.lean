import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivBasicOpenOfTrivFibre
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsIsGenTranslDiffComp
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjBySmoothIsProperGeometricallyIntegral
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TrivLocallyOfDense

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.AbLaw

noncomputable section
namespace GlobalTheory.SeesawLocal

/- English proof (translation)
Use `(hd.preimage j.isOpenEmbedding.isOpenMap).mono ?_` and prove the remaining obligations. Introduce and unpack `q ⟨K, hK, x, Y, ρ, h, ⟨z, hz⟩, hpb, c, hc⟩`. Establish `hsub : Subsingleton (Sp K)` using `inferInstanceAs (Subsingleton (PrimeSpectrum K))`. Establish `hr : Set.range x ⊆ Set.range j`. Introduce and unpack `_ ⟨w, rfl⟩`.

Conclude with `⟨q, by rw [Subsingleton.elim w z]; exact hz.symm⟩`. Take `⟨x', hx'⟩ : ∃ x' : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R), x' ≫ j = x` from `⟨IsOpenImmersion.lift j x hr, IsOpenImmersion.lift_fac j x hr⟩`. Establish `hmap : Spec.map (CommRingCat.ofHom (Spec.preimage x').hom) = x'`. Rewrite using `[CommRingCat.ofHom_hom, Spec.map_preimage]`. Use `⟨K, hK, (Spec.preimage x').hom, Y, pullback.lift ρ (h ≫ x') (by rw [hpb.w, Category.assoc, hx']), h, ?_, ?_, ?_⟩` and prove the remaining obligations.

Establish `h1 : j (x' z) = j q` using `by rw [← hz, ← hx']; rfl`. Establish `h2 : x' z = q` using `j.isOpenEmbedding.injective h1`. Establish `h3 : Spec.map (Spec.preimage x') z = q` using `by rw [Spec.map_preimage]; exact h2`. Rewrite using `[← h3]`. Express the relevant statement in the definitionally equal form `RingHom.ker (Spec.preimage x').hom = Ideal.comap (Spec.preimage x').hom (z : PrimeSpectrum K).asIdeal`.

Rewrite using `[@Ideal.eq_bot_of_prime K _ (z : PrimeSpectrum K).asIdeal (z : PrimeSpectrum K).isPrime]`. Conclude with `RingHom.ker_eq_comap_bot _`. Rewrite using `[hmap]`. Use `IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback f j)` and prove the remaining obligations. Rewrite using `[pullback.lift_fst, hx']`.

Conclude with `hpb`. Apply `CubeOpen.triv_pull_pull` to reduce the goal to its premises. Rewrite using `[pullback.lift_fst]`. Conclude with `⟨c, hc⟩`.
-/
theorem dense_affine {S X : Scheme.{0}} (f : X ⟶ S) (N : LB X) {R : Type} [CommRing R]
    (j : Spec (CommRingCat.of R) ⟶ S) [IsOpenImmersion j]
    (hd : Dense {p : S | ∃ (K : Type) (_ : Field K) (x : Sp K ⟶ S) (Y : Scheme.{0}) (ρ : Y ⟶ X) (h : Y ⟶ Sp K),
      p ∈ Set.range x ∧ IsPullback ρ h f x ∧ ∃ c : (N.pull ρ).Gen, c.IsGen}) :
    Dense {p : PrimeSpectrum R | ∃ (K : Type) (_ : Field K) (g : R →+* K) (X' : Scheme.{0})
      (π : X' ⟶ pullback f j) (f' : X' ⟶ Spec (CommRingCat.of K)), RingHom.ker g = p.asIdeal ∧
      IsPullback π f' (pullback.snd f j) (Spec.map (CommRingCat.ofHom g)) ∧
      Triv ((N.pull (pullback.fst f j)).pull π)} := by
  refine (hd.preimage j.isOpenEmbedding.isOpenMap).mono ?_
  rintro q ⟨K, hK, x, Y, ρ, h, ⟨z, hz⟩, hpb, c, hc⟩
  have hsub : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  have hr : Set.range x ⊆ Set.range j := by
    rintro _ ⟨w, rfl⟩
    exact ⟨q, by rw [Subsingleton.elim w z]; exact hz.symm⟩
  obtain ⟨x', hx'⟩ : ∃ x' : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R), x' ≫ j = x :=
    ⟨IsOpenImmersion.lift j x hr, IsOpenImmersion.lift_fac j x hr⟩
  have hmap : Spec.map (CommRingCat.ofHom (Spec.preimage x').hom) = x' := by
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  refine ⟨K, hK, (Spec.preimage x').hom, Y,
    pullback.lift ρ (h ≫ x') (by rw [hpb.w, Category.assoc, hx']), h, ?_, ?_, ?_⟩
  · have h1 : j (x' z) = j q := by rw [← hz, ← hx']; rfl
    have h2 : x' z = q := j.isOpenEmbedding.injective h1
    have h3 : Spec.map (Spec.preimage x') z = q := by rw [Spec.map_preimage]; exact h2
    rw [← h3]
    change RingHom.ker (Spec.preimage x').hom =
      Ideal.comap (Spec.preimage x').hom (z : PrimeSpectrum K).asIdeal
    rw [@Ideal.eq_bot_of_prime K _ (z : PrimeSpectrum K).asIdeal (z : PrimeSpectrum K).isPrime]
    exact RingHom.ker_eq_comap_bot _
  · rw [hmap]
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback f j)
    rw [pullback.lift_fst, hx']
    exact hpb
  · apply CubeOpen.triv_pull_pull
    rw [pullback.lift_fst]
    exact ⟨c, hc⟩

/- English proof (translation)
Introduce `S₀ B _ M hA hM hRel S X _ t π f N hpb hN hd s`. Take `⟨R, j, hj, ⟨pt, hpt⟩, -⟩` from `Scheme.exists_affine_mem_range_and_range_subset (X := S) (x := s) (U := ⊤) trivial`. Establish `hRed : _root_.IsReduced R`. Use `isReduced_of_isOpenImmersion j` as an intermediate fact. Conclude with `(affine_isReduced_iff R).mp inferInstance`.

Establish `hsq : IsPullback (pullback.fst f j ≫ π) (pullback.snd f j) B.hom (j ≫ t)` using `(IsPullback.of_hasPullback f j).paste_horiz hpb`. Take `⟨hP, hSm, hPr, hGI⟩` from `AmpleBaseChange.isProjBy_smooth_isProper_geometricallyIntegral S₀ B M hA hM hRel R (j ≫ t) _ _ _ hsq`. Take `⟨r, hr, H⟩` from `SeesawReduced.triv_locally_of_dense R (pullback f j) (pullback.snd f j) (N.pull (pullback.fst f j)) (pull_isLB hN _) hSm hPr hGI hP (dense_affine f N j hd) pt`. Use `set p : PrimeSpectrum R := pt with hp`. Establish `h0 : p ∈ PrimeSpectrum.basicOpen r` using `hr`.

Rewrite `h0` using `[← SetLike.mem_coe, ← PrimeSpectrum.localization_away_comap_range (Localization.Away r) r]`. Take `⟨w, hw⟩` from `h0`. Take `⟨j', hj'⟩ : ∃ j' : Spec (CommRingCat.of (Localization.Away r)) ⟶ S, j' = Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))) ≫ j` from `⟨_, rfl⟩`. Establish `hjo : IsOpenImmersion j'` using `by rw [hj']; infer_instance`. Use `⟨j'.opensRange, ?_, ?_⟩` and prove the remaining obligations.

Use `show s ∈ Set.range j'`. Use `⟨w, ?_⟩` and prove the remaining obligations. Rewrite using `[hj']`. Express the relevant statement in the definitionally equal form `j ((Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))) w) = s`. Rewrite using `[← hpt]`.

Conclude with `congrArg j hw`. Establish `hU : IsPullback (f ⁻¹ᵁ j'.opensRange).ι (morphismRestrict f j'.opensRange ≫ j'.isoOpensRange.inv) f j'`. Establish `hb : IsPullback j'.opensRange.ι j'.isoOpensRange.inv (𝟙 S) j'` using `IsPullback.of_vert_isIso ⟨by simp⟩`. Simplify using `using (isPullback_morphismRestrict f j'.opensRange).flip.paste_vert hb`. Take `⟨π₀, h₁, h₂⟩ : ∃ π₀ : (f ⁻¹ᵁ j'.opensRange).toScheme ⟶ pullback f j, π₀ ≫ pullback.fst f j = (f ⁻¹ᵁ j'.opensRange).ι ∧ π₀ ≫ pullback.snd f j = (morphismRestrict f j'.opensRange ≫ j'.isoOpensRange.inv) ≫ Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))` from `⟨pullback.lift _ _ (by rw [hU.w]; simp only [Category.assoc]; rw [← hj']), pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩`.

Establish `hsq' : IsPullback π₀ (morphismRestrict f j'.opensRange ≫ j'.isoOpensRange.inv) (pullback.snd f j) (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))))`. Use `IsPullback.of_right ?_ h₂ (IsPullback.of_hasPullback f j)` and prove the remaining obligations. Rewrite using `[h₁, ← hj']`. Conclude with `hU`. Take `⟨c, hc⟩` from `H (Localization.Away r) (algebraMap R (Localization.Away r)) _ π₀ _ hsq' (IsLocalization.Away.algebraMap_isUnit r)`.

Take `⟨d, hd'⟩` from `GlobalTheory.exists_isGen_linComb_of_pull N _ _ π₀ c hc`. Conclude with `CubeOpen.triv_comp (f := π₀ ≫ pullback.fst f j) (𝟙 _) (by rw [Category.id_comp, h₁]) ⟨d, hd'⟩`.
-/
theorem triv_locally_of_dense : ∀ (S₀ : Scheme.{0}) (B : Over S₀) [GrpObj B] (M : LB B.left), IsAbelianScheme B → M.IsLB → Out.RelAmple B M → ∀ (S X : Scheme.{0}) [IsReduced S] (t : S ⟶ S₀) (π : X ⟶ B.left) (f : X ⟶ S) (N : LB X), IsPullback π f B.hom t → N.IsLB → Dense {p : S | ∃ (K : Type) (_ : Field K) (x : Sp K ⟶ S) (Y : Scheme.{0}) (ρ : Y ⟶ X) (h : Y ⟶ Sp K), p ∈ Set.range x ∧ IsPullback ρ h f x ∧ ∃ c : (N.pull ρ).Gen, c.IsGen} → ∀ s : S, ∃ U : S.Opens, s ∈ U ∧ ∃ c : (N.pull (f ⁻¹ᵁ U).ι).Gen, c.IsGen := by
  intro S₀ B _ M hA hM hRel S X _ t π f N hpb hN hd s
  obtain ⟨R, j, hj, ⟨pt, hpt⟩, -⟩ :=
    Scheme.exists_affine_mem_range_and_range_subset (X := S) (x := s) (U := ⊤) trivial
  have hRed : _root_.IsReduced R := by
    have := isReduced_of_isOpenImmersion j
    exact (affine_isReduced_iff R).mp inferInstance
  have hsq : IsPullback (pullback.fst f j ≫ π) (pullback.snd f j) B.hom (j ≫ t) :=
    (IsPullback.of_hasPullback f j).paste_horiz hpb
  obtain ⟨hP, hSm, hPr, hGI⟩ := AmpleBaseChange.isProjBy_smooth_isProper_geometricallyIntegral
    S₀ B M hA hM hRel R (j ≫ t) _ _ _ hsq
  obtain ⟨r, hr, H⟩ := SeesawReduced.triv_locally_of_dense R (pullback f j) (pullback.snd f j)
    (N.pull (pullback.fst f j)) (pull_isLB hN _) hSm hPr hGI hP (dense_affine f N j hd) pt
  set p : PrimeSpectrum R := pt with hp
  have h0 : p ∈ PrimeSpectrum.basicOpen r := hr
  rw [← SetLike.mem_coe, ← PrimeSpectrum.localization_away_comap_range (Localization.Away r) r] at h0
  obtain ⟨w, hw⟩ := h0
  obtain ⟨j', hj'⟩ : ∃ j' : Spec (CommRingCat.of (Localization.Away r)) ⟶ S,
      j' = Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))) ≫ j := ⟨_, rfl⟩
  have hjo : IsOpenImmersion j' := by rw [hj']; infer_instance
  refine ⟨j'.opensRange, ?_, ?_⟩
  · show s ∈ Set.range j'
    refine ⟨w, ?_⟩
    rw [hj']
    change j ((Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))) w) = s
    rw [← hpt]
    exact congrArg j hw
  · have hU : IsPullback (f ⁻¹ᵁ j'.opensRange).ι (morphismRestrict f j'.opensRange ≫ j'.isoOpensRange.inv)
        f j' := by
      have hb : IsPullback j'.opensRange.ι j'.isoOpensRange.inv (𝟙 S) j' :=
        IsPullback.of_vert_isIso ⟨by simp⟩
      simpa using (isPullback_morphismRestrict f j'.opensRange).flip.paste_vert hb
    obtain ⟨π₀, h₁, h₂⟩ : ∃ π₀ : (f ⁻¹ᵁ j'.opensRange).toScheme ⟶ pullback f j,
        π₀ ≫ pullback.fst f j = (f ⁻¹ᵁ j'.opensRange).ι ∧
        π₀ ≫ pullback.snd f j = (morphismRestrict f j'.opensRange ≫ j'.isoOpensRange.inv) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))) :=
      ⟨pullback.lift _ _ (by rw [hU.w]; simp only [Category.assoc]; rw [← hj']), pullback.lift_fst _ _ _,
        pullback.lift_snd _ _ _⟩
    have hsq' : IsPullback π₀ (morphismRestrict f j'.opensRange ≫ j'.isoOpensRange.inv)
        (pullback.snd f j) (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))) := by
      refine IsPullback.of_right ?_ h₂ (IsPullback.of_hasPullback f j)
      rw [h₁, ← hj']
      exact hU
    obtain ⟨c, hc⟩ := H (Localization.Away r) (algebraMap R (Localization.Away r)) _ π₀ _ hsq'
      (IsLocalization.Away.algebraMap_isUnit r)
    obtain ⟨d, hd'⟩ := GlobalTheory.exists_isGen_linComb_of_pull N _ _ π₀ c hc
    exact CubeOpen.triv_comp (f := π₀ ≫ pullback.fst f j) (𝟙 _) (by rw [Category.id_comp, h₁]) ⟨d, hd'⟩

end GlobalTheory.SeesawLocal
