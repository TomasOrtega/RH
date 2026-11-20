import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.MinSt5OfMinSt4
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitExistsAfterFiniteExtensionOfCompleteDVRStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormalizationBlowupIsIsoDense
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TChart

/- English proof (translation)
Distinguish the cases in `h : IsField A`. Use `letI := h.toField`. Use `⟨PowerSeries A, inferInstance, inferInstance, inferInstance, ?_, PowerSeries.C, RingHom.injective _, inferInstance⟩` and prove the remaining obligations. Rewrite using `[PowerSeries.maximalIdeal_eq_span_X]`. Use `infer_instance`.

Take `⟨O, _, _, _, _, φ, h1, h2⟩` from `GlobalTheory.exists_complete_discreteValuationRing_dominating A h`. Conclude with `⟨O, inferInstance, inferInstance, inferInstance, inferInstance, φ, h1, h2⟩`.
-/
theorem exists_complete_dvr_of_local (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W)
      (_ : IsAdicComplete (maximalIdeal W) W) (ψ : A →+* W), Function.Injective ψ ∧ IsLocalHom ψ := by
  by_cases h : IsField A
  · letI := h.toField
    refine ⟨PowerSeries A, inferInstance, inferInstance, inferInstance, ?_, PowerSeries.C,
      RingHom.injective _, inferInstance⟩
    rw [PowerSeries.maximalIdeal_eq_span_X]; infer_instance
  · obtain ⟨O, _, _, _, _, φ, h1, h2⟩ := GlobalTheory.exists_complete_discreteValuationRing_dominating A h
    exact ⟨O, inferInstance, inferInstance, inferInstance, inferInstance, φ, h1, h2⟩

/- English proof (translation)
Introduce `g n F S s _ _ j _ _ hd hjs x`. Use `haveI := F.smooth`. Use `haveI : Smooth F.s := SmoothOfRelativeDimension.smooth (g * (g + 1) / 2) F.s`. Use `haveI : Flat F.s := inferInstance`. Take `⟨_, ⟨y0, rfl⟩, hw⟩` from `GlobalTheory.BlowOpen.exists_specializes_of_dense_scheme S _ j.isOpenEmbedding.isOpen_range hd x`.

Take `⟨y1, hy1, e1⟩` from `Flat.generalizingMap F.s (genericPoint_specializes (F.s y0))`. Establish `hη : j y1 ⤳ x` using `(hy1.map j.continuous).trans hw`. Take `⟨q, hq⟩ : j y1 ∈ Set.range (S.fromSpecStalk x)` from `by rw [Scheme.range_fromSpecStalk]; exact hη`. Use `haveI : q.asIdeal.IsPrime := q.isPrime`. Use `haveI : IsLocalRing (S.presheaf.stalk x ⧸ q.asIdeal) := .of_surjective' _ Ideal.Quotient.mk_surjective`.

Take `⟨W, _, _, _, hWc, ψ, hψi, hψl⟩` from `exists_complete_dvr_of_local (S.presheaf.stalk x ⧸ q.asIdeal)`. Use `haveI : IsLocalHom (Ideal.Quotient.mk q.asIdeal) := .of_surjective _ Ideal.Quotient.mk_surjective`. Set `ψ' : S.presheaf.stalk x →+* W` to `ψ.comp (Ideal.Quotient.mk q.asIdeal)`. Use `haveI : IsLocalHom ψ' := RingHom.isLocalHom_comp _ _`. Set `ξ0 : Sp W ⟶ S` to `spMap ψ' ≫ S.fromSpecStalk x`.

Establish `hξc : ξ0 (closedPoint W) = x` using `by show S.fromSpecStalk x (spMap ψ' (closedPoint W)) = x`. Establish `e : spMap ψ' (closedPoint W) = closedPoint (S.presheaf.stalk x)` using `IsLocalRing.comap_closedPoint ψ'`. Rewrite using `[e]`. Conclude with `Scheme.fromSpecStalk_closedPoint`. Establish `hξg : ξ0 (⊥ : PrimeSpectrum W) = j y1` using `by show S.fromSpecStalk x (spMap ψ' (⊥ : PrimeSpectrum W)) = j y1`.

Establish `: spMap ψ' (⊥ : PrimeSpectrum W) = q`. Apply `PrimeSpectrum.ext` to reduce the goal to its premises. Use `show Ideal.comap ψ' ⊥ = q.asIdeal`. Rewrite using `[← RingHom.ker_eq_comap_bot, RingHom.ker_comp_of_injective _ hψi, Ideal.mk_ker]`. Rewrite using `[this, hq]`.

Establish `hjKbot : ∀ pt : Sp (FractionRing W), jK W pt = (⊥ : PrimeSpectrum W)` using `fun pt => by`. Apply `PrimeSpectrum.ext` to reduce the goal to its premises. Establish `hpt : pt = (⊥ : PrimeSpectrum (FractionRing W))` using `Subsingleton.elim (α := PrimeSpectrum (FractionRing W)) _ _`. Substitute `hpt` using the available equality. Use `show Ideal.comap (algebraMap W (FractionRing W)) ⊥ = ⊥`.

Conclude with `(RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective W (FractionRing W))`. Establish `hrange : Set.range (jK W ≫ ξ0) ⊆ Set.range j`. Introduce and unpack `_ ⟨pt, rfl⟩`. Rewrite using `[Scheme.Hom.comp_apply, hjKbot, hξg]`. Conclude with `⟨y1, rfl⟩`.

Set `y : Sp (FractionRing W) ⟶ F.X` to `IsOpenImmersion.lift j (jK W ≫ ξ0) hrange`. Establish `hy : y ≫ j = jK W ≫ ξ0` using `IsOpenImmersion.lift_fac _ _ _`. Take `⟨θ, hθ⟩` from `Spec.map_surjective (ξ0 ≫ s)`. Set `b0 : cycAway n →+* W` to `θ.hom`. Establish `hb0 : spMap b0 = ξ0 ≫ s` using `hθ`.

Establish `hb0i : Function.Injective b0`. Establish `h1 : (spMap b0) (⊥ : PrimeSpectrum W) = genericPoint (Sp (cycAway n))`. Rewrite using `[hb0]`. Conclude with `(Scheme.Hom.comp_apply ξ0 s _).trans (by rw [hξg, ← Scheme.Hom.comp_apply, hjs, e1])`. Rewrite `h1` using `[genericPoint_eq_bot_of_affine]`.

Rewrite using `[RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_comap_bot]`. Conclude with `congrArg PrimeSpectrum.asIdeal h1`. Use `haveI : CharZero W := charZero_of_injective_ringHom hb0i`. Establish `hBase : GlobalTheory.Mum.Base W` using `⟨⟨inferInstance, inferInstance, inferInstance, hWc⟩, inferInstance⟩`. Take `⟨T, f, fK, -, hfl, -, hcomp, hTy⟩` from `GlobalTheory.T.traitExistsAfterFiniteExtension_of_completeDVR g n (cycAway n) (zetaAway n) F W hBase inferInstance y`.

Use `haveI := hfl`. Use `⟨T, spMap f ≫ ξ0, f.comp b0, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `show ξ0 (spMap f (closedPoint T.V)) = x`. Establish `e : spMap f (closedPoint T.V) = closedPoint W` using `IsLocalRing.comap_closedPoint f`. Rewrite using `[e, hξc]`.

Establish `key : jK T.V ≫ spMap f = spMap fK ≫ jK W`. Simplify using `only [jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]`. Use `congr 2`. Use extensionality with `a`. Conclude with `(hcomp a).symm`.

Rewrite using `[hTy, Category.assoc, hy, ← Category.assoc, key, Category.assoc]`. Rewrite using `[Category.assoc, ← hb0]`. Simplify using `only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]`.
-/
theorem exists_trait_at : ∀ {g n : ℕ} (F : SFam g n (zetaAway n)) (S : Scheme.{0}) (s : S ⟶ Sp (cycAway n))
    [LocallyOfFiniteType s] [IsLocallyNoetherian S] (j : F.X ⟶ S) [IsOpenImmersion j], 3 ≤ n → Dense (Set.range j) →
    j ≫ s = F.s → ∀ x : S, ∃ (T : GlobalTheory.Poinc.Trait F) (ξT : Sp T.V ⟶ S) (b : cycAway n →+* T.V),
      ξT (closedPoint T.V) = x ∧ jK T.V ≫ ξT = T.y ≫ j ∧ ξT ≫ s = spMap b := by
  intro g n F S s _ _ j _ _ hd hjs x
  haveI := F.smooth
  haveI : Smooth F.s := SmoothOfRelativeDimension.smooth (g * (g + 1) / 2) F.s
  haveI : Flat F.s := inferInstance
  obtain ⟨_, ⟨y0, rfl⟩, hw⟩ :=
    GlobalTheory.BlowOpen.exists_specializes_of_dense_scheme S _ j.isOpenEmbedding.isOpen_range hd x
  obtain ⟨y1, hy1, e1⟩ := Flat.generalizingMap F.s (genericPoint_specializes (F.s y0))
  have hη : j y1 ⤳ x := (hy1.map j.continuous).trans hw
  obtain ⟨q, hq⟩ : j y1 ∈ Set.range (S.fromSpecStalk x) := by rw [Scheme.range_fromSpecStalk]; exact hη
  haveI : q.asIdeal.IsPrime := q.isPrime
  haveI : IsLocalRing (S.presheaf.stalk x ⧸ q.asIdeal) := .of_surjective' _ Ideal.Quotient.mk_surjective
  obtain ⟨W, _, _, _, hWc, ψ, hψi, hψl⟩ := exists_complete_dvr_of_local (S.presheaf.stalk x ⧸ q.asIdeal)
  haveI : IsLocalHom (Ideal.Quotient.mk q.asIdeal) := .of_surjective _ Ideal.Quotient.mk_surjective
  let ψ' : S.presheaf.stalk x →+* W := ψ.comp (Ideal.Quotient.mk q.asIdeal)
  haveI : IsLocalHom ψ' := RingHom.isLocalHom_comp _ _
  let ξ0 : Sp W ⟶ S := spMap ψ' ≫ S.fromSpecStalk x
  have hξc : ξ0 (closedPoint W) = x := by
    show S.fromSpecStalk x (spMap ψ' (closedPoint W)) = x
    have e : spMap ψ' (closedPoint W) = closedPoint (S.presheaf.stalk x) := IsLocalRing.comap_closedPoint ψ'
    rw [e]
    exact Scheme.fromSpecStalk_closedPoint
  have hξg : ξ0 (⊥ : PrimeSpectrum W) = j y1 := by
    show S.fromSpecStalk x (spMap ψ' (⊥ : PrimeSpectrum W)) = j y1
    have : spMap ψ' (⊥ : PrimeSpectrum W) = q := by
      apply PrimeSpectrum.ext
      show Ideal.comap ψ' ⊥ = q.asIdeal
      rw [← RingHom.ker_eq_comap_bot, RingHom.ker_comp_of_injective _ hψi, Ideal.mk_ker]
    rw [this, hq]
  have hjKbot : ∀ pt : Sp (FractionRing W), jK W pt = (⊥ : PrimeSpectrum W) := fun pt => by
    apply PrimeSpectrum.ext
    have hpt : pt = (⊥ : PrimeSpectrum (FractionRing W)) := Subsingleton.elim (α := PrimeSpectrum (FractionRing W)) _ _
    subst hpt
    show Ideal.comap (algebraMap W (FractionRing W)) ⊥ = ⊥
    exact (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective W (FractionRing W))
  have hrange : Set.range (jK W ≫ ξ0) ⊆ Set.range j := by
    rintro _ ⟨pt, rfl⟩
    rw [Scheme.Hom.comp_apply, hjKbot, hξg]
    exact ⟨y1, rfl⟩
  let y : Sp (FractionRing W) ⟶ F.X := IsOpenImmersion.lift j (jK W ≫ ξ0) hrange
  have hy : y ≫ j = jK W ≫ ξ0 := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨θ, hθ⟩ := Spec.map_surjective (ξ0 ≫ s)
  let b0 : cycAway n →+* W := θ.hom
  have hb0 : spMap b0 = ξ0 ≫ s := hθ
  have hb0i : Function.Injective b0 := by
    have h1 : (spMap b0) (⊥ : PrimeSpectrum W) = genericPoint (Sp (cycAway n)) := by
      rw [hb0]
      exact (Scheme.Hom.comp_apply ξ0 s _).trans (by rw [hξg, ← Scheme.Hom.comp_apply, hjs, e1])
    rw [genericPoint_eq_bot_of_affine] at h1
    rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_comap_bot]
    exact congrArg PrimeSpectrum.asIdeal h1
  haveI : CharZero W := charZero_of_injective_ringHom hb0i
  have hBase : GlobalTheory.Mum.Base W := ⟨⟨inferInstance, inferInstance, inferInstance, hWc⟩, inferInstance⟩
  obtain ⟨T, f, fK, -, hfl, -, hcomp, hTy⟩ := GlobalTheory.T.traitExistsAfterFiniteExtension_of_completeDVR g n (cycAway n) (zetaAway n) F W hBase inferInstance y
  haveI := hfl
  refine ⟨T, spMap f ≫ ξ0, f.comp b0, ?_, ?_, ?_⟩
  · show ξ0 (spMap f (closedPoint T.V)) = x
    have e : spMap f (closedPoint T.V) = closedPoint W := IsLocalRing.comap_closedPoint f
    rw [e, hξc]
  · have key : jK T.V ≫ spMap f = spMap fK ≫ jK W := by
      simp only [jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
      ext a
      exact (hcomp a).symm
    rw [hTy, Category.assoc, hy, ← Category.assoc, key, Category.assoc]
  · rw [Category.assoc, ← hb0]
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

end GlobalTheory.TChart
