import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsChartOf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

namespace GlobalTheory.TorRef

open IsLocalRing in

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `h`. Use `⟨RingHom.Flat.comp (RingHom.Flat.of_bijective he) h1, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← Ideal.map_map, IsLocalRing.map_maximalIdeal_of_surjective e he.2]`. Conclude with `h2`. Rewrite using `[← RingHom.comp_assoc]`.

Conclude with `RingHom.Finite.comp h3 (RingHom.Finite.of_surjective e he.2)`.
-/
theorem isEtaleCompletion_comp_bij {B A R : Type} [CommRing B] [IsLocalRing B] [CommRing A] [IsLocalRing A]
    [CommRing R] [IsLocalRing R] (e : B →+* A) (he : Function.Bijective e) (φ : A →+* R)
    (h : Toroidal.IsEtaleCompletion φ) : Toroidal.IsEtaleCompletion (φ.comp e) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨RingHom.Flat.comp (RingHom.Flat.of_bijective he) h1, ?_, ?_⟩
  · rw [← Ideal.map_map, IsLocalRing.map_maximalIdeal_of_surjective e he.2]
    exact h2
  · rw [← RingHom.comp_assoc]
    exact RingHom.Finite.comp h3 (RingHom.Finite.of_surjective e he.2)

end GlobalTheory.TorRef

namespace GlobalTheory.TorRef

/- English proof (translation)
Introduce `z`. Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, a i ∉ (Z.s z).asIdeal := by`. Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Establish `hle : Ideal.span (Set.range a) ≤ (Z.s z).asIdeal`.

Rewrite using `[Ideal.span_le]`. Introduce and unpack `_ ⟨j, rfl⟩`. Conclude with `hne j`. Rewrite `hle` using `[hcov.2.2]`. Conclude with `(Z.s z).isPrime.ne_top (top_le_iff.mp hle)`.

Take `⟨hoi, -, hrange, -, ⟨mu⟩⟩` from `hch i`. Establish `hz : z ∈ Set.range (u i)`. Rewrite using `[hrange]`. Conclude with `hi`. Take `⟨z', rfl⟩` from `hz`.

Take `⟨Rl, _, _, _, ξ, t, m, P, k, γ, hcn, hpt, het, hfu, htor, hcone, hin⟩` from `hC i z'`. Take `⟨n, -⟩` from `ObjMaps.exists_sab_comp mu m`. Establish `hb : Function.Bijective ((u i).stalkMap (ξ (IsLocalRing.closedPoint (CommRingCat.of Rl)))).hom` using `ConcreteCategory.bijective_of_isIso _`. Use `⟨Rl, inferInstance, inferInstance, inferInstance, ξ ≫ u i, t, n, P, k, γ, hcn, ?_, ?_, ?_, htor, hcone, hin⟩` and prove the remaining obligations. Use `show (u i) (ξ _) = _`.

Rewrite using `[hpt]`. Rewrite using `[Scheme.stalkClosedPointTo_comp]`. Conclude with `isEtaleCompletion_comp_bij _ hb _ het`. Rewrite using `[Scheme.stalkClosedPointTo_comp]`. Establish `h2` using `RingHom.FormallyUnramified.comp (RingHom.FormallyUnramified.of_surjective hb.2) hfu`.

Conclude with `h2`.
-/
theorem hasCones_of_charts {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} {I : Type} [Finite I] {R : I → Type} [∀ i, CommRing (R i)] {a : I → 𝓞 c.F}
    {b : ∀ i, 𝓞 c.F →+* R i} {ω : ∀ i, R i →+* c.F}
    (Cn : ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] (m : ℕ),
      (Fin m → LinearMap.BilinForm ℤ X) → Prop) (Z : GMod Xo c) (C : ∀ i, Model Xo c (ω i)) (u : ∀ i, (C i).X ⟶ Z.X)
    (hcov : IsCover (algebraMap (𝓞 c.F) c.F) R a b ω) (hch : ∀ i, IsChartOf Z (C i) (a i) (b i) (u i))
    (hC : ∀ i, HasCones Cn (C i)) : HasCones Cn Z := by
  intro z
  obtain ⟨i, hi⟩ : ∃ i, a i ∉ (Z.s z).asIdeal := by
    by_contra hne
    push_neg at hne
    have hle : Ideal.span (Set.range a) ≤ (Z.s z).asIdeal := by
      rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      exact hne j
    rw [hcov.2.2] at hle
    exact (Z.s z).isPrime.ne_top (top_le_iff.mp hle)
  obtain ⟨hoi, -, hrange, -, ⟨mu⟩⟩ := hch i
  have hz : z ∈ Set.range (u i) := by
    rw [hrange]
    exact hi
  obtain ⟨z', rfl⟩ := hz
  obtain ⟨Rl, _, _, _, ξ, t, m, P, k, γ, hcn, hpt, het, hfu, htor, hcone, hin⟩ := hC i z'
  obtain ⟨n, -⟩ := ObjMaps.exists_sab_comp mu m
  have hb : Function.Bijective ((u i).stalkMap (ξ (IsLocalRing.closedPoint (CommRingCat.of Rl)))).hom :=
    ConcreteCategory.bijective_of_isIso _
  refine ⟨Rl, inferInstance, inferInstance, inferInstance, ξ ≫ u i, t, n, P, k, γ, hcn, ?_, ?_, ?_, htor, hcone, hin⟩
  · show (u i) (ξ _) = _
    rw [hpt]
  · rw [Scheme.stalkClosedPointTo_comp]
    exact isEtaleCompletion_comp_bij _ hb _ het
  · rw [Scheme.stalkClosedPointTo_comp]
    have h2 := RingHom.FormallyUnramified.comp (RingHom.FormallyUnramified.of_surjective hb.2) hfu
    exact h2

end GlobalTheory.TorRef
