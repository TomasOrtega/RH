import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FinCover
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.BlowUpChart2
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.BlowUpOff
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.CoordEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.DChartEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.ExChart
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StdSmoothMvPolynomial

open CategoryTheory Limits AlgebraicGeometry UpperTheory.Gal.DifferentialFormSections

namespace UpperTheory.Gal.KunnethLefschetz.G

/- English proof (translation)
Establish `h0 : (algebraMap A (MvPolynomial (Fin d) A)).IsStandardSmoothOfRelativeDimension d` using `(RingHom.isStandardSmoothOfRelativeDimension_algebraMap (n := d)).mpr (GlobalTheory.CompanionTheory.Ar.LieInh.stdSmooth_mvPolynomial A d)`. Set `e₁ : MvPolynomial (Fin d) A ≃+* MvPolynomial σ A` to `(MvPolynomial.renameEquiv A (Fintype.equivFinOfCardEq hd).symm).toRingEquiv`. Set `e₂ : MvPolynomial σ A ≃+* B` to `RingEquiv.ofBijective _ hb`. Establish `hφ : φ = (e₁.trans e₂).toRingHom.comp (algebraMap A (MvPolynomial (Fin d) A))`. Use extensionality with `a`.

Simplify using `[e₁, e₂, MvPolynomial.algebraMap_eq]`. Rewrite using `[hφ]`. Conclude with `RingHom.isStandardSmoothOfRelativeDimension_respectsIso.1 _ _ h0`.
-/
private theorem stdSmooth_of_bijective {A B σ : Type} [CommRing A] [CommRing B] [Fintype σ] {d : ℕ}
    (hd : Fintype.card σ = d) (φ : A →+* B) (y : σ → B)
    (hb : Function.Bijective (MvPolynomial.eval₂Hom φ y)) :
    φ.IsStandardSmoothOfRelativeDimension d := by
  have h0 : (algebraMap A (MvPolynomial (Fin d) A)).IsStandardSmoothOfRelativeDimension d :=
    (RingHom.isStandardSmoothOfRelativeDimension_algebraMap (n := d)).mpr
      (GlobalTheory.CompanionTheory.Ar.LieInh.stdSmooth_mvPolynomial A d)
  let e₁ : MvPolynomial (Fin d) A ≃+* MvPolynomial σ A :=
    (MvPolynomial.renameEquiv A (Fintype.equivFinOfCardEq hd).symm).toRingEquiv
  let e₂ : MvPolynomial σ A ≃+* B := RingEquiv.ofBijective _ hb
  have hφ : φ = (e₁.trans e₂).toRingHom.comp (algebraMap A (MvPolynomial (Fin d) A)) := by
    ext a
    simp [e₁, e₂, MvPolynomial.algebraMap_eq]
  rw [hφ]
  exact RingHom.isStandardSmoothOfRelativeDimension_respectsIso.1 _ _ h0

/- English proof (translation)
Set `e : MvPolynomial σ A ≃+* B` to `RingEquiv.ofBijective _ hb`. Set `ρ : B →+* A` to `(MvPolynomial.eval₂Hom (RingHom.id A) fun _ => 0).comp e.symm.toRingHom`. Establish `hρ : ρ.comp φ = RingHom.id A`. Use extensionality with `a`. Establish `: e.symm (φ a) = MvPolynomial.C a` using `e.symm_apply_eq.2 (by simp [e])`.

Simplify using `[ρ, this]`. Introduce `p`. Use `⟨PrimeSpectrum.comap ρ p, ?_⟩` and prove the remaining obligations. Rewrite using `[← PrimeSpectrum.comap_comp_apply, hρ, PrimeSpectrum.comap_id]`.
-/
private theorem comap_surjective_of_bijective {A B σ : Type} [CommRing A] [CommRing B]
    (φ : A →+* B) (y : σ → B) (hb : Function.Bijective (MvPolynomial.eval₂Hom φ y)) :
    Function.Surjective (PrimeSpectrum.comap φ) := by
  let e : MvPolynomial σ A ≃+* B := RingEquiv.ofBijective _ hb
  let ρ : B →+* A := (MvPolynomial.eval₂Hom (RingHom.id A) fun _ => 0).comp e.symm.toRingHom
  have hρ : ρ.comp φ = RingHom.id A := by
    ext a
    have : e.symm (φ a) = MvPolynomial.C a :=
      e.symm_apply_eq.2 (by simp [e])
    simp [ρ, this]
  intro p
  refine ⟨PrimeSpectrum.comap ρ p, ?_⟩
  rw [← PrimeSpectrum.comap_comp_apply, hρ, PrimeSpectrum.comap_id]

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨p, rfl⟩ : y ∈ Set.range hU.fromSpec := by`. Rewrite using `[hU.range_fromSpec]`. Conclude with `hy`. Take `⟨q, rfl⟩` from `hs p`. Use `⟨hV.fromSpec q, ?_⟩` and prove the remaining obligations.

Establish `h` using `congr($(IsAffineOpen.SpecMap_appLE_fromSpec f hU hV e) q)`. Simplify using `only [Scheme.Hom.comp_apply] at h`. Conclude with `h.symm`.
-/
private theorem exists_apply_eq {X Y : Scheme.{0}} (f : X ⟶ Y) {U : Y.Opens} (hU : IsAffineOpen U)
    {V : X.Opens} (hV : IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U)
    (hs : Function.Surjective (PrimeSpectrum.comap (f.appLE U V e).hom)) {y : Y} (hy : y ∈ U) :
    ∃ x, f x = y := by
  obtain ⟨p, rfl⟩ : y ∈ Set.range hU.fromSpec := by
    rw [hU.range_fromSpec]
    exact hy
  obtain ⟨q, rfl⟩ := hs p
  refine ⟨hV.fromSpec q, ?_⟩
  have h := congr($(IsAffineOpen.SpecMap_appLE_fromSpec f hU hV e) q)
  simp only [Scheme.Hom.comp_apply] at h
  exact h.symm

/- English proof (translation)
The claim follows from `haveI := hf; inferInstance`.
-/
private theorem isProper_snd {X Y S : Scheme.{0}} (f : X ⟶ S) (g : Y ⟶ S) (hf : IsProper f) :
    IsProper (pullback.snd f g) :=
  haveI := hf; inferInstance

/- English proof (translation)
Take `⟨U, u, hz, hc⟩` from `coordEx R Z (d + 1) z`. Take `⟨c, -, -, hN⟩` from `(dChartEx R Z (d + 1)).1 U u hc z hz`. Conclude with `⟨c, (blChart R π hπ (d + 1) c).some, hN⟩`.
-/
private theorem exists_chart {R : Type} [CommRing R] {Z W : Sch R} (d : ℕ) [IsSeparated Z.hom]
    [SmoothOfRelativeDimension (d + 1) Z.hom] (π : W ⟶ XX Z) (hπ : IsBl π) (z : Z.left) :
    ∃ (c : DChart Z (d + 1)) (_ : BChart π c.N c.s), (dg Z).left z ∈ c.N := by
  obtain ⟨U, u, hz, hc⟩ := coordEx R Z (d + 1) z
  obtain ⟨c, -, -, hN⟩ := (dChartEx R Z (d + 1)).1 U u hc z hz
  exact ⟨c, (blChart R π hπ (d + 1) c).some, hN⟩

/- English proof (translation)
Introduce `R _ _ Z W d _ _ π hπ`. Use `haveI : Smooth Z.hom := SmoothOfRelativeDimension.smooth (d + 1) Z.hom`. Use `⟨⟨fun x => ?_⟩, ?_, ⟨fun z => ?_⟩⟩` and prove the remaining obligations. Take `⟨c, b, hN⟩` from `exists_chart d π hπ ((exG π).left x)`. Establish `e : (exI π).left ≫ π.left = (exG π).left ≫ (dg Z).left` using `pullback.condition`.

Establish `hW : (exI π).left x ∈ π.left ⁻¹ᵁ c.N`. Establish `h` using `congr($e x)`. Simplify using `only [Scheme.Hom.comp_apply] at h`. Express the relevant statement in the definitionally equal form `π.left ((exI π).left x) ∈ c.N`. Rewrite using `[h]`.

Conclude with `hN`. Rewrite `hW` using `[← b.cov]`. Take `⟨j, hj⟩` from `TopologicalSpace.Opens.mem_iSup.1 hW`. Take `⟨hA, hB, -, h, hbij⟩` from `exChart R π (d + 1) c b j`. Conclude with `⟨_, hA, _, hB, hj, h, stdSmooth_of_bijective (by simp [Fintype.card_subtype_compl]) _ _ hbij⟩`.

Conclude with `isProper_snd π.left (dg Z).left (blOff R π hπ).1`. Take `⟨c, b, hN⟩` from `exists_chart d π hπ z`. Take `⟨hA, hB, -, h, hbij⟩` from `exChart R π (d + 1) c b 0`. Conclude with `exists_apply_eq _ hA hB h (comap_surjective_of_bijective _ _ hbij) hN`.
-/
theorem exSmooth : ExSmooth := by
  intro R _ _ Z W d _ _ π hπ
  haveI : Smooth Z.hom := SmoothOfRelativeDimension.smooth (d + 1) Z.hom
  refine ⟨⟨fun x => ?_⟩, ?_, ⟨fun z => ?_⟩⟩
  · obtain ⟨c, b, hN⟩ := exists_chart d π hπ ((exG π).left x)
    have e : (exI π).left ≫ π.left = (exG π).left ≫ (dg Z).left := pullback.condition
    have hW : (exI π).left x ∈ π.left ⁻¹ᵁ c.N := by
      have h := congr($e x)
      simp only [Scheme.Hom.comp_apply] at h
      change π.left ((exI π).left x) ∈ c.N
      rw [h]
      exact hN
    rw [← b.cov] at hW
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hW
    obtain ⟨hA, hB, -, h, hbij⟩ := exChart R π (d + 1) c b j
    exact ⟨_, hA, _, hB, hj, h, stdSmooth_of_bijective (by simp [Fintype.card_subtype_compl]) _ _ hbij⟩
  · exact isProper_snd π.left (dg Z).left (blOff R π hπ).1
  · obtain ⟨c, b, hN⟩ := exists_chart d π hπ z
    obtain ⟨hA, hB, -, h, hbij⟩ := exChart R π (d + 1) c b 0
    exact exists_apply_eq _ hA hB h (comap_surjective_of_bijective _ _ hbij) hN

end UpperTheory.Gal.KunnethLefschetz.G
