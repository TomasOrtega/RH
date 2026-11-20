import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianTorsionFiniteAndMulNSurjective
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SepClosedDiv

/- English proof (translation)
Set `i` to `X.affineCover.idx x`. Take `⟨y, -⟩` from `X.affineCover.covers x`. Take `⟨R, e⟩ : ∃ R : CommRingCat, X.affineCover.X i = Spec R` from `⟨_, rfl⟩`. Set `φ : CommRingCat.of Ω ⟶ R` to `Spec.preimage (eqToHom e.symm ≫ X.affineCover.f i ≫ f)`. Establish `hφ : Spec.map φ = eqToHom e.symm ≫ X.affineCover.f i ≫ f` using `Spec.map_preimage _`.

Establish `hg : Etale (Spec.map φ)` using `by rw [hφ]; infer_instance`. Establish `hr : φ.hom.Etale` using `(HasRingHomProperty.Spec_iff (P := @Etale)).1 hg`. Use `letI := φ.hom.toAlgebra`. Establish `: Algebra.Etale Ω R` using `hr`. Set `q : PrimeSpectrum R` to `(eqToHom e).base y`.

Take `⟨ψ⟩` from `GlobalTheory.nonempty_algHom_of_etale_of_isSepClosed (R := Ω) (A := R) (K := Ω) q.asIdeal (by`. Rewrite using `[(Ideal.comap (algebraMap Ω R) q.asIdeal).eq_bot_of_prime]`. Conclude with `((RingHom.injective_iff_ker_eq_bot _).1 (algebraMap Ω Ω).injective).symm)`. Use `⟨Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ eqToHom e.symm ≫ X.affineCover.f i, ?_⟩` and prove the remaining obligations. Simplify using `only [Category.assoc]`.

Rewrite using `[← hφ, ← Spec.map_comp]`. Rewrite using `[← Spec.map_id]`. Use `congr 1`. Use extensionality with `a`. Conclude with `ψ.commutes a`.
-/
theorem exists_section_of_etale {Ω : Type} [Field Ω] [IsSepClosed Ω] {X : Scheme.{0}} (f : X ⟶ Sp Ω)
    [Etale f] (x : X) : ∃ s : Sp Ω ⟶ X, s ≫ f = 𝟙 _ := by
  let i := X.affineCover.idx x
  obtain ⟨y, -⟩ := X.affineCover.covers x
  obtain ⟨R, e⟩ : ∃ R : CommRingCat, X.affineCover.X i = Spec R := ⟨_, rfl⟩
  let φ : CommRingCat.of Ω ⟶ R := Spec.preimage (eqToHom e.symm ≫ X.affineCover.f i ≫ f)
  have hφ : Spec.map φ = eqToHom e.symm ≫ X.affineCover.f i ≫ f := Spec.map_preimage _
  have hg : Etale (Spec.map φ) := by rw [hφ]; infer_instance
  have hr : φ.hom.Etale := (HasRingHomProperty.Spec_iff (P := @Etale)).1 hg
  letI := φ.hom.toAlgebra
  have : Algebra.Etale Ω R := hr
  let q : PrimeSpectrum R := (eqToHom e).base y
  obtain ⟨ψ⟩ := GlobalTheory.nonempty_algHom_of_etale_of_isSepClosed (R := Ω) (A := R) (K := Ω) q.asIdeal
    (by
      rw [(Ideal.comap (algebraMap Ω R) q.asIdeal).eq_bot_of_prime]
      exact ((RingHom.injective_iff_ker_eq_bot _).1 (algebraMap Ω Ω).injective).symm)
  refine ⟨Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ eqToHom e.symm ≫ X.affineCover.f i, ?_⟩
  simp only [Category.assoc]
  rw [← hφ, ← Spec.map_comp]
  rw [← Spec.map_id]
  congr 1
  ext a
  exact ψ.commutes a

/- English proof (translation)
Introduce `K Ω _ _ _ _ A _ _ hA n hn x`. Use `hA.smooth` as an intermediate fact. Establish `hu : IsUnit (n : Γ(Sp K, ⊤))`. Simplify using `using (isUnit_iff_ne_zero.2 hn).map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom`. Establish `he : Etale (mulN A n).left` using `GlobalTheory.GrpTangent.etale_mulN A hu`.

Establish `hs : Surjective (mulN A n).left` using `GlobalTheory.surjective_mulN_of_isAbelianScheme K A hA n hn`. Set `m` to `(mulN A n).left`. Establish `he' : Etale (pullback.snd m x.left)` using `inferInstance`. Take `⟨z, -⟩` from `(pullback.snd m x.left).surjective (IsLocalRing.closedPoint Ω)`. Take `⟨s, hs'⟩` from `exists_section_of_etale (pullback.snd m x.left) z`.

Establish `h : (s ≫ pullback.fst m x.left) ≫ m = x.left`. Rewrite using `[Category.assoc, pullback.condition, reassoc_of% hs']`. Use `⟨Over.homMk (s ≫ pullback.fst m x.left) ?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(s ≫ pullback.fst m x.left) ≫ A.hom = _`. Rewrite using `[← Over.w (mulN A n), ← Category.assoc, h]`.

Conclude with `Over.w x`. Rewrite using `[← GlobalTheory.GrpTangent.comp_mulN]`. Conclude with `Over.OverMorphism.ext h`.
-/
theorem exists_pow_eq : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsSepClosed Ω] (A : Over (Sp K)) [GrpObj A]
    [IsCommMonObj A], IsAbelianScheme A → ∀ n : ℕ, (n : K) ≠ 0 → ∀ x : ptOver K Ω ⟶ A, ∃ y, y ^ n = x := by
  intro K Ω _ _ _ _ A _ _ hA n hn x
  have := hA.smooth
  have hu : IsUnit (n : Γ(Sp K, ⊤)) := by
    simpa using (isUnit_iff_ne_zero.2 hn).map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  have he : Etale (mulN A n).left := GlobalTheory.GrpTangent.etale_mulN A hu
  have hs : Surjective (mulN A n).left := GlobalTheory.surjective_mulN_of_isAbelianScheme K A hA n hn
  let m := (mulN A n).left
  have he' : Etale (pullback.snd m x.left) := inferInstance
  obtain ⟨z, -⟩ := (pullback.snd m x.left).surjective (IsLocalRing.closedPoint Ω)
  obtain ⟨s, hs'⟩ := exists_section_of_etale (pullback.snd m x.left) z
  have h : (s ≫ pullback.fst m x.left) ≫ m = x.left := by
    rw [Category.assoc, pullback.condition, reassoc_of% hs']
  refine ⟨Over.homMk (s ≫ pullback.fst m x.left) ?_, ?_⟩
  · change (s ≫ pullback.fst m x.left) ≫ A.hom = _
    rw [← Over.w (mulN A n), ← Category.assoc, h]
    exact Over.w x
  · rw [← GlobalTheory.GrpTangent.comp_mulN]
    exact Over.OverMorphism.ext h

end GlobalTheory.SepClosedDiv
