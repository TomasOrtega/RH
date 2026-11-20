import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FractionGeneratorsArcs
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure

noncomputable section

namespace GlobalTheory.OneArcCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.IndefiniteRowSideFullHecke.FractionGeneratorsArcs

/- English proof (translation)
Establish `e : Mono (spMap β) ↔ Epi (CommRingCat.ofHom β)`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h' : Mono (Scheme.Spec.map (CommRingCat.ofHom β).op)` using `h`. Use `Scheme.Spec.mono_of_mono_map h'` as an intermediate fact.

Conclude with `(inferInstance : Epi (CommRingCat.ofHom β).op.unop)`. Introduce `h`. Conclude with `(inferInstance : Mono (Scheme.Spec.map (CommRingCat.ofHom β).op))`. Rewrite using `[e]`. Prove the components needed by the constructor for the conclusion.

Introduce `h x`. Set `K : Subfield F` to `Subfield.closure (Set.range β)`. Set `β₁ : O →+* K` to `β.codRestrict K fun r => Subfield.subset_closure ⟨r, rfl⟩`. Establish `h₁ : Epi (CommRingCat.ofHom β₁ ≫ CommRingCat.ofHom K.subtype)` using `h`. Establish `h₂ : Epi (CommRingCat.ofHom K.subtype)` using `epi_of_epi (CommRingCat.ofHom β₁) _`.

Establish `: IsScalarTower ℚ K F` using `IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)`. Establish `h₃ : Module.Finite K F` using `Module.Finite.of_restrictScalars_finite ℚ K F`. Take `⟨⟨x', hx'⟩, rfl⟩` from `RingHom.surjective_of_epi_of_finite (CommRingCat.ofHom K.subtype) h₃ x`. Take `⟨p, hp, q, hq, rfl⟩` from `Subfield.mem_closure_iff.1 hx'`. Establish `hc : Subring.closure (Set.range β) = β.range` using `Subring.closure_eq β.range`.

Rewrite `hp`, `hq` using `[hc]`. Take `⟨r, rfl⟩` from `hp`. Take `⟨s, rfl⟩` from `hq`. Distinguish the cases in `hs : β s = 0`. Conclude with `⟨0, 1, by simp, by simp [hs]⟩`.

Conclude with `⟨r, s, hs, div_mul_cancel₀ _ hs⟩`. Introduce `h`. Use `⟨fun {A} f g hfg => ?_⟩` and prove the remaining obligations. Use extensionality with `x`. Take `⟨r, s, hs, hx⟩` from `h x`.

Establish `k : ∀ r, f.hom (β r) = g.hom (β r)` using `fun r => congrArg (fun q => q.hom r) hfg`. Establish `hu : IsUnit (f.hom (β s))` using `(IsUnit.mk0 _ hs).map f.hom`. Use `hu.mul_right_cancel ?_` and prove the remaining obligations. Rewrite using `[← map_mul, hx, k r, k s, ← map_mul, hx]`.
-/
theorem mono_spMap_iff {O F : Type} [CommRing O] [Field F] [CharZero F] [FiniteDimensional ℚ F] (β : O →+* F) :
    Mono (spMap β) ↔ GeneratesFrac β := by
  have e : Mono (spMap β) ↔ Epi (CommRingCat.ofHom β) := by
    constructor
    · intro h
      have h' : Mono (Scheme.Spec.map (CommRingCat.ofHom β).op) := h
      have := Scheme.Spec.mono_of_mono_map h'
      exact (inferInstance : Epi (CommRingCat.ofHom β).op.unop)
    · intro h
      exact (inferInstance : Mono (Scheme.Spec.map (CommRingCat.ofHom β).op))
  rw [e]
  constructor
  · intro h x
    let K : Subfield F := Subfield.closure (Set.range β)
    let β₁ : O →+* K := β.codRestrict K fun r => Subfield.subset_closure ⟨r, rfl⟩
    have h₁ : Epi (CommRingCat.ofHom β₁ ≫ CommRingCat.ofHom K.subtype) := h
    have h₂ : Epi (CommRingCat.ofHom K.subtype) := epi_of_epi (CommRingCat.ofHom β₁) _
    have : IsScalarTower ℚ K F := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
    have h₃ : Module.Finite K F := Module.Finite.of_restrictScalars_finite ℚ K F
    obtain ⟨⟨x', hx'⟩, rfl⟩ := RingHom.surjective_of_epi_of_finite (CommRingCat.ofHom K.subtype) h₃ x
    obtain ⟨p, hp, q, hq, rfl⟩ := Subfield.mem_closure_iff.1 hx'
    have hc : Subring.closure (Set.range β) = β.range := Subring.closure_eq β.range
    rw [hc] at hp hq
    obtain ⟨r, rfl⟩ := hp
    obtain ⟨s, rfl⟩ := hq
    by_cases hs : β s = 0
    · exact ⟨0, 1, by simp, by simp [hs]⟩
    · exact ⟨r, s, hs, div_mul_cancel₀ _ hs⟩
  · intro h
    refine ⟨fun {A} f g hfg => ?_⟩
    ext x
    obtain ⟨r, s, hs, hx⟩ := h x
    have k : ∀ r, f.hom (β r) = g.hom (β r) := fun r => congrArg (fun q => q.hom r) hfg
    have hu : IsUnit (f.hom (β s)) := (IsUnit.mk0 _ hs).map f.hom
    refine hu.mul_right_cancel ?_
    rw [← map_mul, hx, k r, k s, ← map_mul, hx]

/- English proof (translation)
Establish `key : ∀ {T : Scheme.{0}} (t : T ⟶ S'), IsProper (pullback.snd G'.hom t) ↔ IsProper (pullback.snd G.hom (t ≫ f))`. Introduce `T t`. Establish `hp` using `(IsPullback.of_hasPullback G'.hom t).paste_horiz h`. Establish `e` using `hp.isoPullback_hom_snd`. Prove the components needed by the constructor for the conclusion.

Introduce `_`. Rewrite using `[← hp.isoPullback_inv_snd]`. Use `infer_instance`. Introduce `_`. Rewrite using `[← e]`.

Use `infer_instance`. Prove the components needed by the constructor for the conclusion. Introduce `hx K _ _ t ⟨p, hp⟩`. Conclude with `(key t).2 (hx K (t ≫ f) ⟨p, by rw [← hp]; simp⟩)`. Introduce `hx`.

Set `K` to `AlgebraicClosure (S'.residueField x)`. Set `t : Sp K ⟶ S'` to `Spec.map (CommRingCat.ofHom (algebraMap (S'.residueField x) K)) ≫ S'.fromSpecResidueField x`. Establish `p : Sp K` using `(default : PrimeSpectrum K)`. Establish `ht : t p = x` using `Scheme.fromSpecResidueField_apply x _`. Conclude with `abLocusOne S G hG K (t ≫ f) ((key t).1 (hx K t ⟨p, ht⟩)) ⟨p, congrArg (fun z => f z) ht⟩`.
-/
theorem mem_abLocus_pullback {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G]
    (hG : IsSemiAbelian G) {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsPullback φ G'.hom G.hom f) (x : S') :
    f x ∈ abLocus G ↔ x ∈ abLocus G' := by
  have key : ∀ {T : Scheme.{0}} (t : T ⟶ S'),
      IsProper (pullback.snd G'.hom t) ↔ IsProper (pullback.snd G.hom (t ≫ f)) := by
    intro T t
    have hp := (IsPullback.of_hasPullback G'.hom t).paste_horiz h
    have e := hp.isoPullback_hom_snd
    constructor
    · intro _
      rw [← hp.isoPullback_inv_snd]; infer_instance
    · intro _
      rw [← e]; infer_instance
  constructor
  · intro hx K _ _ t ⟨p, hp⟩
    exact (key t).2 (hx K (t ≫ f) ⟨p, by rw [← hp]; simp⟩)
  · intro hx
    let K := AlgebraicClosure (S'.residueField x)
    let t : Sp K ⟶ S' := Spec.map (CommRingCat.ofHom (algebraMap (S'.residueField x) K)) ≫ S'.fromSpecResidueField x
    have p : Sp K := (default : PrimeSpectrum K)
    have ht : t p = x := Scheme.fromSpecResidueField_apply x _
    exact abLocusOne S G hG K (t ≫ f) ((key t).1 (hx K t ⟨p, ht⟩)) ⟨p, congrArg (fun z => f z) ht⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l}

end GlobalTheory.OneArcCompare
