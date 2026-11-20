import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsNeZeroIsStandardSmoothOfRelativeDimension

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

/- English proof (translation)
Establish `key : FaithfulSMul R B ∧ Algebra.trdeg R B = g`. Take `⟨e, he⟩` from `Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial g R B`. Use `letI : Algebra (MvPolynomial (Fin g) R) B := e.toRingHom.toAlgebra`. Use `haveI : Algebra.Etale (MvPolynomial (Fin g) R) B := he`. Use `haveI : IsScalarTower R (MvPolynomial (Fin g) R) B := IsScalarTower.of_algebraMap_eq fun x => (e.commutes x).symm`.

Take `⟨_, _⟩` from `AffinePoints.faithfulSMul_and_isAlgebraic_of_etale (MvPolynomial (Fin g) R) B`. Use `⟨FaithfulSMul.trans R (MvPolynomial (Fin g) R) B, ?_⟩` and prove the remaining obligations. Rewrite using `[trdeg_eq_of_isAlgebraic_top R (MvPolynomial (Fin g) R) B, MvPolynomial.trdeg_of_isDomain]`. Simplify using the standard rewrite rules. Take `⟨_, htr⟩` from `key`.

Set `x : Fin g → B` to `fun i => ψ (MvPolynomial.X i)`. Establish `hx : ψ = MvPolynomial.aeval x` using `MvPolynomial.aeval_unique ψ`. Establish `hr : ψ.range = Algebra.adjoin R (Set.range x)`. Rewrite using `[Algebra.adjoin_range_eq_range_aeval, ← hx]`. Establish `h1 : (algebraMap ψ.range B).QuasiFinite` using `RingHom.QuasiFinite.of_comp (f := algebraMap ψ.range B) (g := ψ.rangeRestrict.toRingHom) hψ`.

Rewrite `h1` using `[RingHom.quasiFinite_algebraMap]`. Establish `h2 : Algebra.IsAlgebraic ψ.range B` using `isAlgebraic_of_quasiFiniteAt ψ.range B ⊥`. Rewrite `h2` using `[hr]`. Establish `h3` using `Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg_of_finite R x (by simp [htr])`. Rewrite using `[hx]`.

Conclude with `h3.1`.
-/
theorem injective_of_quasiFinite_of_isStandardSmoothOfRelativeDimension {R B : Type} [CommRing R]
    [IsDomain R] [CommRing B] [IsDomain B] [Algebra R B] {g : ℕ}
    [Algebra.IsStandardSmoothOfRelativeDimension g R B] (ψ : MvPolynomial (Fin g) R →ₐ[R] B)
    (hψ : ψ.toRingHom.QuasiFinite) : Function.Injective ψ := by
  have key : FaithfulSMul R B ∧ Algebra.trdeg R B = g := by
    obtain ⟨e, he⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial g R B
    letI : Algebra (MvPolynomial (Fin g) R) B := e.toRingHom.toAlgebra
    haveI : Algebra.Etale (MvPolynomial (Fin g) R) B := he
    haveI : IsScalarTower R (MvPolynomial (Fin g) R) B :=
      IsScalarTower.of_algebraMap_eq fun x => (e.commutes x).symm
    obtain ⟨_, _⟩ :=
      AffinePoints.faithfulSMul_and_isAlgebraic_of_etale (MvPolynomial (Fin g) R) B
    refine ⟨FaithfulSMul.trans R (MvPolynomial (Fin g) R) B, ?_⟩
    rw [trdeg_eq_of_isAlgebraic_top R (MvPolynomial (Fin g) R) B, MvPolynomial.trdeg_of_isDomain]
    simp
  obtain ⟨_, htr⟩ := key
  let x : Fin g → B := fun i => ψ (MvPolynomial.X i)
  have hx : ψ = MvPolynomial.aeval x := MvPolynomial.aeval_unique ψ
  have hr : ψ.range = Algebra.adjoin R (Set.range x) := by
    rw [Algebra.adjoin_range_eq_range_aeval, ← hx]
  have h1 : (algebraMap ψ.range B).QuasiFinite :=
    RingHom.QuasiFinite.of_comp (f := algebraMap ψ.range B) (g := ψ.rangeRestrict.toRingHom) hψ
  rw [RingHom.quasiFinite_algebraMap] at h1
  have h2 : Algebra.IsAlgebraic ψ.range B := isAlgebraic_of_quasiFiniteAt ψ.range B ⊥
  rw [hr] at h2
  have h3 := Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg_of_finite R x (by simp [htr])
  rw [hx]
  exact h3.1

/- English proof (translation)
Establish `hp` using `AffineSpace.isPullback_map (n := Fin g) i`. Establish `: IsOpenImmersion (AffineSpace.map (Fin g) i)` using `MorphismProperty.of_isPullback hp.flip ‹_›`. Take `⟨ψ, hψ⟩` from `Spec.map_surjective (hp.lift f (Spec.map φ) hf ≫ (AffineSpace.SpecIso (Fin g) R).hom)`. Establish `e : f = Spec.map ψ ≫ (AffineSpace.SpecIso (Fin g) R).inv ≫ AffineSpace.map (Fin g) i`. Rewrite using `[hψ]`.

Simplify using the standard rewrite rules. Establish `e2 : CommRingCat.ofHom MvPolynomial.C ≫ ψ = φ`. Apply `Spec.map_injective` to reduce the goal to its premises. Rewrite using `[Spec.map_comp, hψ, ← AffineSpace.SpecIso_inv_over, Category.assoc, Iso.hom_inv_id_assoc, IsPullback.lift_snd]`. Establish `hq : LocallyQuasiFinite (Spec.map ψ)`.

Rewrite using `[e] at ‹LocallyQuasiFinite f›`. Conclude with `.of_comp _ ((AffineSpace.SpecIso (Fin g) R).inv ≫ AffineSpace.map (Fin g) i)`. Rewrite `hq` using `[HasRingHomProperty.Spec_iff (P := @LocallyQuasiFinite)]`. Use `letI : Algebra R B := φ.hom.toAlgebra`. Use `haveI : Algebra.IsStandardSmoothOfRelativeDimension g R B := hφ`.

Establish `hinj` using `injective_of_quasiFinite_of_isStandardSmoothOfRelativeDimension (R := R) (B := B) (g := g) { ψ.hom with commutes' := fun r => congr($e2 r) } hq`. Establish `: IsDominant (Spec.map ψ)` using `⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (by rw [(RingHom.injective_iff_ker_eq_bot ψ.hom).1 hinj]; exact bot_le)⟩`. Establish `: IsDominant (AffineSpace.map (Fin g) i)` using `⟨(AffineSpace.map (Fin g) i).isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)⟩`. Rewrite using `[e]`. Use `infer_instance`.
-/
theorem isDominant_of_locallyQuasiFinite_affineSpace {Z : Scheme.{0}} [IsIntegral Z]
    {R B : CommRingCat.{0}} [IsDomain R] [IsDomain B] {g : ℕ} (φ : R ⟶ B)
    (hφ : φ.hom.IsStandardSmoothOfRelativeDimension g) (i : Spec R ⟶ Z) [IsOpenImmersion i]
    (f : Spec B ⟶ 𝔸(Fin g; Z)) [LocallyQuasiFinite f]
    (hf : f ≫ 𝔸(Fin g; Z) ↘ Z = Spec.map φ ≫ i) : IsDominant f := by
  have hp := AffineSpace.isPullback_map (n := Fin g) i
  have : IsOpenImmersion (AffineSpace.map (Fin g) i) :=
    MorphismProperty.of_isPullback hp.flip ‹_›
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective
    (hp.lift f (Spec.map φ) hf ≫ (AffineSpace.SpecIso (Fin g) R).hom)
  have e : f = Spec.map ψ ≫ (AffineSpace.SpecIso (Fin g) R).inv ≫ AffineSpace.map (Fin g) i := by
    rw [hψ]; simp
  have e2 : CommRingCat.ofHom MvPolynomial.C ≫ ψ = φ := by
    apply Spec.map_injective
    rw [Spec.map_comp, hψ, ← AffineSpace.SpecIso_inv_over, Category.assoc, Iso.hom_inv_id_assoc,
      IsPullback.lift_snd]
  have hq : LocallyQuasiFinite (Spec.map ψ) := by
    rw [e] at ‹LocallyQuasiFinite f›
    exact .of_comp _ ((AffineSpace.SpecIso (Fin g) R).inv ≫ AffineSpace.map (Fin g) i)
  rw [HasRingHomProperty.Spec_iff (P := @LocallyQuasiFinite)] at hq
  letI : Algebra R B := φ.hom.toAlgebra
  haveI : Algebra.IsStandardSmoothOfRelativeDimension g R B := hφ
  have hinj := injective_of_quasiFinite_of_isStandardSmoothOfRelativeDimension
    (R := R) (B := B) (g := g) { ψ.hom with commutes' := fun r => congr($e2 r) } hq
  have : IsDominant (Spec.map ψ) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
      (by rw [(RingHom.injective_iff_ker_eq_bot ψ.hom).1 hinj]; exact bot_le)⟩
  have : IsDominant (AffineSpace.map (Fin g) i) :=
    ⟨(AffineSpace.map (Fin g) i).isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)⟩
  rw [e]
  infer_instance

/- English proof (translation)
Introduce `X Z _ _ t _ g U hU hs u w hw`. Establish `hf` using `AffineSpace.homOfVector_over t u`. Generalize the expression as in `AffineSpace.homOfVector t u = f at hf hw`. Establish `: LocallyOfFiniteType f`. Establish `: LocallyOfFiniteType (f ≫ 𝔸(Fin g; Z) ↘ Z)` using `by rw [hf]; infer_instance`.

Conclude with `locallyOfFiniteType_of_comp f (𝔸(Fin g; Z) ↘ Z)`. Take `⟨x, hxU, hxV⟩` from `nonempty_preirreducible_inter U.isOpen f.quasiFiniteLocus.isOpen hU ⟨w, hw⟩`. Set `W : X.Opens` to `U ⊓ f.quasiFiniteLocus`. Establish `h1 : SmoothOfRelativeDimension (0 + g) (X.homOfLE (inf_le_left : W ≤ U) ≫ U.ι ≫ t)` using `inferInstance`. Establish `h2 : LocallyQuasiFinite (X.homOfLE (inf_le_right : W ≤ f.quasiFiniteLocus) ≫ f.quasiFiniteLocus.ι ≫ f)` using `inferInstance`.

Rewrite `h1`, `h2` using `[Scheme.homOfLE_ι_assoc]`. Rewrite `h1` using `[zero_add]`. Take `⟨Z', hZ', V, hV, hx, e, hsm⟩` from `h1.exists_isStandardSmoothOfRelativeDimension ⟨x, hxU, hxV⟩`. Establish `: Nonempty W` using `⟨⟨x, hxU, hxV⟩⟩`. Establish `: Nonempty V` using `⟨⟨_, hx⟩⟩`.

Establish `: Nonempty Z'` using `⟨⟨_, e hx⟩⟩`. Establish `: IsDominant (hV.fromSpec ≫ W.ι ≫ f)` using `isDominant_of_locallyQuasiFinite_affineSpace _ hsm hZ'.fromSpec _ (by`. Rewrite using `[IsAffineOpen.SpecMap_appLE_fromSpec _ hZ' hV e]`. Simplify using `[hf, W])`. Establish `: IsDominant (W.ι ≫ f)` using `.of_comp hV.fromSpec _`.

Conclude with `.of_comp W.ι _`.
-/
theorem isDominant_homOfVector_of_quasiFiniteAt :
    ∀ (X Z : Scheme.{0}) [IsIntegral X] [IsIntegral Z] (t : X ⟶ Z) [LocallyOfFiniteType t] (g : ℕ) (U : X.Opens), (U : Set X).Nonempty → SmoothOfRelativeDimension g (U.ι ≫ t) → ∀ (u : Fin g → Γ(X, ⊤)) (w : X), (AffineSpace.homOfVector t u).QuasiFiniteAt w → IsDominant (AffineSpace.homOfVector t u) := by
  intro X Z _ _ t _ g U hU hs u w hw
  have hf := AffineSpace.homOfVector_over t u
  generalize AffineSpace.homOfVector t u = f at hf hw
  have : LocallyOfFiniteType f := by
    have : LocallyOfFiniteType (f ≫ 𝔸(Fin g; Z) ↘ Z) := by rw [hf]; infer_instance
    exact locallyOfFiniteType_of_comp f (𝔸(Fin g; Z) ↘ Z)
  obtain ⟨x, hxU, hxV⟩ := nonempty_preirreducible_inter U.isOpen f.quasiFiniteLocus.isOpen hU
    ⟨w, hw⟩
  let W : X.Opens := U ⊓ f.quasiFiniteLocus
  have h1 : SmoothOfRelativeDimension (0 + g) (X.homOfLE (inf_le_left : W ≤ U) ≫ U.ι ≫ t) :=
    inferInstance
  have h2 : LocallyQuasiFinite (X.homOfLE (inf_le_right : W ≤ f.quasiFiniteLocus) ≫
    f.quasiFiniteLocus.ι ≫ f) := inferInstance
  rw [Scheme.homOfLE_ι_assoc] at h1 h2
  rw [zero_add] at h1
  obtain ⟨Z', hZ', V, hV, hx, e, hsm⟩ := h1.exists_isStandardSmoothOfRelativeDimension ⟨x, hxU, hxV⟩
  have : Nonempty W := ⟨⟨x, hxU, hxV⟩⟩
  have : Nonempty V := ⟨⟨_, hx⟩⟩
  have : Nonempty Z' := ⟨⟨_, e hx⟩⟩
  have : IsDominant (hV.fromSpec ≫ W.ι ≫ f) :=
    isDominant_of_locallyQuasiFinite_affineSpace _ hsm hZ'.fromSpec _ (by
      rw [IsAffineOpen.SpecMap_appLE_fromSpec _ hZ' hV e]; simp [hf, W])
  have : IsDominant (W.ι ≫ f) := .of_comp hV.fromSpec _
  exact .of_comp W.ι _

end GlobalTheory
