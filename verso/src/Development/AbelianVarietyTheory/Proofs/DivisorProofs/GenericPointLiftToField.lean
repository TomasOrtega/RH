import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTangentPresentationPrime

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.GenericFactor

/- English proof (translation)
Introduce `E _ _ _ H Dw l' Xo' c' W Y p _ _ R _ _ ξ hξ`. Use `haveI := Y.jQ_open`. Take `⟨u, hu⟩` from `hξ`. Set `g₀ : Sp (FractionRing R) ⟶ Y.X` to `spMap (algebraMap R (FractionRing R)) ≫ ξ`. Set `φ : c'.V W →+* FractionRing R` to `(Spec.preimage (g₀ ≫ Y.s)).hom`.

Establish `hφ : spMap φ = g₀ ≫ Y.s` using `Spec.map_preimage _`. Establish `hpt : ∀ q : Sp (FractionRing R), g₀ q = Y.j u`. Introduce `q`. Rewrite using `[hu]`. Use `show ξ ((spMap (algebraMap R (FractionRing R))) q) = _`.

Use `congr 1`. Apply `PrimeSpectrum.ext` to reduce the goal to its premises. Use `show Ideal.comap (algebraMap R (FractionRing R)) q.asIdeal = ⊥`. Rewrite using `[@Ideal.eq_bot_of_prime _ _ q.asIdeal (PrimeSpectrum.isPrime (self := q)), ← RingHom.ker_eq_comap_bot]`. Conclude with `(RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))`.

Establish `hinj : Function.Injective φ`. Rewrite using `[RingHom.injective_iff_ker_eq_bot]`. Set `q : Sp (FractionRing R)` to `⟨⊥, Ideal.isPrime_bot⟩`. Establish `h1 : ((spMap φ) q).asIdeal = RingHom.ker φ` using `by show Ideal.comap φ ⊥ = _`. Conclude with `(RingHom.ker_eq_comap_bot φ).symm`.

Establish `h2 : (spMap φ) q = Y.s (Y.j u)`. Rewrite using `[hφ, ← hpt q]`. Both sides reduce to the same expression. Establish `h3 : Y.s (Y.j u) = (spMap (c'.V W).subtype) ((pullback.snd Y.s (spMap (c'.V W).subtype)) (Y.jQ u))`. Express the relevant statement in the definitionally equal form `(Y.j ≫ Y.s) u = (Y.jQ ≫ pullback.snd _ _ ≫ spMap (c'.V W).subtype) u`.

Rewrite using `[Model.j_s, ← Category.assoc, Y.jQ_over]`. Rewrite using `[← h1, h2, h3]`. Use `show Ideal.comap (c'.V W).subtype _ = ⊥`. Establish `hF : ∀ z : Sp c'.F, z.asIdeal = ⊥` using `fun z => @Ideal.eq_bot_of_prime _ _ z.asIdeal (PrimeSpectrum.isPrime (self := z))`. Rewrite using `[hF, ← RingHom.ker_eq_comap_bot]`.

Conclude with `(RingHom.injective_iff_ker_eq_bot _).1 Subtype.val_injective`. Set `ψ : c'.F →+* FractionRing R` to `IsFractionRing.lift hinj`. Establish `hψ : ψ.comp (c'.V W).subtype = φ` using `IsLocalization.lift_comp _`. Establish `hw : g₀ ≫ Y.s = spMap ψ ≫ spMap (c'.V W).subtype`. Rewrite using `[← hφ, ← spMap_comp, hψ]`.

Set `w : Sp (FractionRing R) ⟶ pullback Y.s (spMap (c'.V W).subtype)` to `pullback.lift g₀ (spMap ψ) hw`. Establish `hr : Set.range w ⊆ Set.range Y.jQ`. Introduce and unpack `_ ⟨q, rfl⟩`. Rewrite using `[← Y.ab_gen]`. Use `show (w ≫ pullback.fst _ _) q ∈ abLocus Y.t.G`.

Rewrite using `[pullback.lift_fst, hpt q]`. Establish `: Y.jQ u ∈ Set.range Y.jQ` using `⟨u, rfl⟩`. Rewrite `this` using `[← Y.ab_gen]`. Conclude with `this`. Use `⟨IsOpenImmersion.lift Y.jQ w hr, ?_⟩` and prove the remaining obligations.

Use `show g₀ = _`. Rewrite using `[Model.j, ← Category.assoc, IsOpenImmersion.lift_fac, pullback.lift_fst]`.
-/
theorem exists_factor_generic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l' : Level H)
    (Xo' : Moduli Dw l') (c' : Coeff l') (W : ValuationSubring ℂ) (Y : Model Xo' c' (c'.V W).subtype) (p : ℕ),
    p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (R : Type) [CommRing R] [IsDomain R] (ξ : Sp R ⟶ Y.X),
    ξ (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R) ∈ Set.range Y.j →
    ∃ y : Sp (FractionRing R) ⟶ Xo'.XF c', spMap (algebraMap R (FractionRing R)) ≫ ξ = y ≫ Y.j := by
  intro E _ _ _ H Dw l' Xo' c' W Y p _ _ R _ _ ξ hξ
  haveI := Y.jQ_open
  obtain ⟨u, hu⟩ := hξ
  let g₀ : Sp (FractionRing R) ⟶ Y.X := spMap (algebraMap R (FractionRing R)) ≫ ξ
  let φ : c'.V W →+* FractionRing R := (Spec.preimage (g₀ ≫ Y.s)).hom
  have hφ : spMap φ = g₀ ≫ Y.s := Spec.map_preimage _
  have hpt : ∀ q : Sp (FractionRing R), g₀ q = Y.j u := by
    intro q
    rw [hu]
    show ξ ((spMap (algebraMap R (FractionRing R))) q) = _
    congr 1
    apply PrimeSpectrum.ext
    show Ideal.comap (algebraMap R (FractionRing R)) q.asIdeal = ⊥
    rw [@Ideal.eq_bot_of_prime _ _ q.asIdeal (PrimeSpectrum.isPrime (self := q)), ← RingHom.ker_eq_comap_bot]
    exact (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))
  have hinj : Function.Injective φ := by
    rw [RingHom.injective_iff_ker_eq_bot]
    let q : Sp (FractionRing R) := ⟨⊥, Ideal.isPrime_bot⟩
    have h1 : ((spMap φ) q).asIdeal = RingHom.ker φ := by
      show Ideal.comap φ ⊥ = _
      exact (RingHom.ker_eq_comap_bot φ).symm
    have h2 : (spMap φ) q = Y.s (Y.j u) := by
      rw [hφ, ← hpt q]; rfl
    have h3 : Y.s (Y.j u) = (spMap (c'.V W).subtype) ((pullback.snd Y.s (spMap (c'.V W).subtype)) (Y.jQ u)) := by
      change (Y.j ≫ Y.s) u = (Y.jQ ≫ pullback.snd _ _ ≫ spMap (c'.V W).subtype) u
      rw [Model.j_s, ← Category.assoc, Y.jQ_over]
    rw [← h1, h2, h3]
    show Ideal.comap (c'.V W).subtype _ = ⊥
    have hF : ∀ z : Sp c'.F, z.asIdeal = ⊥ := fun z => @Ideal.eq_bot_of_prime _ _ z.asIdeal (PrimeSpectrum.isPrime (self := z))
    rw [hF, ← RingHom.ker_eq_comap_bot]
    exact (RingHom.injective_iff_ker_eq_bot _).1 Subtype.val_injective
  let ψ : c'.F →+* FractionRing R := IsFractionRing.lift hinj
  have hψ : ψ.comp (c'.V W).subtype = φ := IsLocalization.lift_comp _
  have hw : g₀ ≫ Y.s = spMap ψ ≫ spMap (c'.V W).subtype := by
    rw [← hφ, ← spMap_comp, hψ]
  let w : Sp (FractionRing R) ⟶ pullback Y.s (spMap (c'.V W).subtype) := pullback.lift g₀ (spMap ψ) hw
  have hr : Set.range w ⊆ Set.range Y.jQ := by
    rintro _ ⟨q, rfl⟩
    rw [← Y.ab_gen]
    show (w ≫ pullback.fst _ _) q ∈ abLocus Y.t.G
    rw [pullback.lift_fst, hpt q]
    have : Y.jQ u ∈ Set.range Y.jQ := ⟨u, rfl⟩
    rw [← Y.ab_gen] at this
    exact this
  refine ⟨IsOpenImmersion.lift Y.jQ w hr, ?_⟩
  show g₀ = _
  rw [Model.j, ← Category.assoc, IsOpenImmersion.lift_fac, pullback.lift_fst]

end GlobalTheory.GenericFactor
