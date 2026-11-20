import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsChartOf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GlueSchemesOverOpensAlongCocycle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSemiAbelianTripleGlueCommonGenericPart
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SemiAbelianHomExtendsUniquelyOverDvr
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabDescentOfFieldExtension
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAbelianTripleGlueTwoOpenImmersions
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.GlueLoc

/- English proof (translation)
Use `IsZariskiLocalAtSource.of_iSup_eq_top (fun i => (ψ i).opensRange) ?_ fun i => ?_` and prove the remaining obligations. Use `eq_top_iff.2 fun x _ => ?_` and prove the remaining obligations. Take `⟨i, hi⟩` from `hcov x`. Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨i, hi⟩`. Establish `e0 : (ψ i).isoOpensRange.inv ≫ ψ i = (ψ i).opensRange.ι` using `(Iso.inv_comp_eq _).2 (Scheme.Hom.isoOpensRange_hom_ι (ψ i)).symm`.

Establish `e : (ψ i).opensRange.ι ≫ f = (ψ i).isoOpensRange.inv ≫ ψ i ≫ f`. Rewrite using `[← Category.assoc, e0]`. Rewrite using `[e, P.cancel_left_of_respectsIso]`. Conclude with `h i`.
-/
theorem of_cover_openImmersions {P : MorphismProperty Scheme.{0}} [IsZariskiLocalAtSource P] {I : Type}
    {A Y : Scheme.{0}} {X : I → Scheme.{0}} (ψ : ∀ i, X i ⟶ A) [∀ i, IsOpenImmersion (ψ i)]
    (hcov : ∀ x : A, ∃ i, x ∈ Set.range (ψ i)) (f : A ⟶ Y) (h : ∀ i, P (ψ i ≫ f)) : P f := by
  refine IsZariskiLocalAtSource.of_iSup_eq_top (fun i => (ψ i).opensRange) ?_ fun i => ?_
  · refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨i, hi⟩ := hcov x
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hi⟩
  · have e0 : (ψ i).isoOpensRange.inv ≫ ψ i = (ψ i).opensRange.ι :=
      (Iso.inv_comp_eq _).2 (Scheme.Hom.isoOpensRange_hom_ι (ψ i)).symm
    have e : (ψ i).opensRange.ι ≫ f = (ψ i).isoOpensRange.inv ≫ ψ i ≫ f := by
      rw [← Category.assoc, e0]
    rw [e, P.cancel_left_of_respectsIso]
    exact h i

/- English proof (translation)
Introduce `E _ _ _ H D l Xo c I _ R _ a b ω C A F ψ hC hpb hj`. Take `⟨hβ, hR, hspan⟩` from `hC`. Establish `hbo : ∀ i, IsOpenImmersion (spMap (b i))` using `fun i => by`. Use `letI := (b i).toAlgebra`. Use `(hR i).2.2` as an intermediate fact.

Conclude with `IsOpenImmersion.of_isLocalization (a i)`. Establish `hψo : ∀ i, IsOpenImmersion (ψ i)` using `fun i => MorphismProperty.of_isPullback (hpb i).flip (hbo i)`. Establish `hψq : ∀ i, QuasiCompact (ψ i)` using `fun i => MorphismProperty.of_isPullback (P := @QuasiCompact) (hpb i).flip inferInstance`. Establish `hcov : ∀ x : A, ∃ i, x ∈ Set.range (ψ i)`. Introduce `x`.

Establish `: ∃ i, a i ∉ (F x).asIdeal`. Assume the negation of the conclusion as `hno`. Use `push_neg at hno`. Establish `hle : Ideal.span (Set.range a) ≤ (F x).asIdeal` using `Ideal.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hno i)`. Rewrite `hle` using `[hspan]`.

Conclude with `(F x).isPrime.ne_top (top_le_iff.1 hle)`. Take `⟨i, hi⟩` from `this`. Use `letI := (b i).toAlgebra`. Use `(hR i).2.2` as an intermediate fact. Take `⟨y, hy⟩` from `(PrimeSpectrum.localization_away_comap_range (R i) (a i)).ge hi`.

Take `⟨z, hz, -⟩` from `Scheme.exists_preimage_of_isPullback (hpb i) x y hy.symm`. Conclude with `⟨i, z, hz⟩`. Establish `hdj : ∀ i, IsPreimmersion (C i).j ∧ Flat (C i).j ∧ IsDominant (C i).j ∧ QuasiCompact (C i).j` using `fun i => by`. Take `⟨-, -, -, h1, h2, h3, h4⟩` from `GlobalTheory.ModelRelCompare.densePart (C i) (hR i).1`. Conclude with `⟨h1, h2, h3, h4⟩`.

Establish `hOZ : LocallyOfFiniteType (spMap (algebraMap ℤ (𝓞 c.F))) ∧ Flat (spMap (algebraMap ℤ (𝓞 c.F)))` using `by haveI : FiniteDimensional ℚ c.F := c.fin haveI : NumberField c.F := ⟨⟩`. Conclude with `⟨(HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).2 (RingHom.finiteType_algebraMap.2 inferInstance), (HasRingHomProperty.Spec_iff (P := @Flat)).2 (RingHom.flat_algebraMap_iff.2 inferInstance)⟩`. Establish `hsft : ∀ i, LocallyOfFiniteType (C i).s` using `fun i => by`. Take `⟨N, e, he, hs⟩` from `(C i).proj`. Use `isProper_str (R i) N` as an intermediate fact.

Rewrite using `[← hs]`. Use `infer_instance`. Use `haveI : IsZariskiLocalAtSource @Flat.{0} := HasRingHomProperty.instIsZariskiLocalAtSource`. Use `haveI : IsZariskiLocalAtSource @LocallyOfFiniteType.{0} := HasRingHomProperty.instIsZariskiLocalAtSource`. Establish `hflat : Flat F` using `of_cover_openImmersions ψ hcov F fun i => by`.

Rewrite using `[(hpb i).w]`. Use `(C i).flat` as an intermediate fact. Use `infer_instance`. Use `⟨hcov, ?_, hflat, ⟨F ≫ spMap (algebraMap ℤ (𝓞 c.F)), ?_, ?_⟩, fun i => ?_⟩` and prove the remaining obligations. Introduce `x`.

Take `⟨i, z, rfl⟩` from `hcov x`. Take `⟨h1, h2⟩` from `(C i).normal z`. Set `e` to `(asIso ((ψ i).stalkMap z)).commRingCatIsoToRingEquiv`. Conclude with `⟨e.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e.symm⟩`. Use `of_cover_openImmersions ψ hcov _ fun i => ?_` and prove the remaining obligations.

Rewrite using `[← Category.assoc, (hpb i).w, Category.assoc]`. Use `hOZ.1` as an intermediate fact. Use `infer_instance`. Use `hOZ.2 infer_instance` as an intermediate fact. Take `⟨h1, h2, -, h4⟩` from `hdj i`.

Use `⟨inferInstance, inferInstance, ?_, inferInstance⟩` and prove the remaining obligations. Use `⟨fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[mem_closure_iff]`. Introduce `o ho hx`. Take `⟨k, z, rfl⟩` from `hcov x`.

Establish `hV : IsOpen ((ψ k) ⁻¹' o)` using `ho.preimage (ψ k).continuous`. Establish `hd` using `(hdj k).2.2.1`. Take `⟨_, hw, w, rfl⟩` from `(hd.denseRange).inter_open_nonempty _ hV ⟨z, hx⟩`. Use `⟨((C k).j ≫ ψ k) w, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Scheme.Hom.comp_apply]`.

Conclude with `hw`. Rewrite using `[hj k i]`. Conclude with `⟨w, rfl⟩`.
-/
theorem glue_local : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
    {c : Coeff l} {I : Type} [Finite I] {R : I → Type} [∀ i, CommRing (R i)] {a : I → 𝓞 c.F} {b : ∀ i, 𝓞 c.F →+* R i}
    {ω : ∀ i, R i →+* c.F} (C : ∀ i, Model Xo c (ω i)) (A : Scheme.{0}) (F : A ⟶ Sp (𝓞 c.F)) (ψ : ∀ i, (C i).X ⟶ A),
    IsCover (algebraMap (𝓞 c.F) c.F) R a b ω → (∀ i, IsPullback (ψ i) (C i).s F (spMap (b i))) →
    (∀ i k, (C i).j ≫ ψ i = (C k).j ≫ ψ k) →
    (∀ x : A, ∃ i, x ∈ Set.range (ψ i)) ∧ Geo.Tor.IsNormalScheme A ∧ Flat F ∧ (∃ z : A ⟶ Sp ℤ, LocallyOfFiniteType z ∧ Flat z) ∧
      ∀ i, IsPreimmersion ((C i).j ≫ ψ i) ∧ Flat ((C i).j ≫ ψ i) ∧ IsDominant ((C i).j ≫ ψ i) ∧
        QuasiCompact ((C i).j ≫ ψ i) := by
  intro E _ _ _ H D l Xo c I _ R _ a b ω C A F ψ hC hpb hj
  obtain ⟨hβ, hR, hspan⟩ := hC
  have hbo : ∀ i, IsOpenImmersion (spMap (b i)) := fun i => by
    letI := (b i).toAlgebra
    have := (hR i).2.2
    exact IsOpenImmersion.of_isLocalization (a i)
  have hψo : ∀ i, IsOpenImmersion (ψ i) := fun i => MorphismProperty.of_isPullback (hpb i).flip (hbo i)
  have hψq : ∀ i, QuasiCompact (ψ i) := fun i =>
    MorphismProperty.of_isPullback (P := @QuasiCompact) (hpb i).flip inferInstance

  have hcov : ∀ x : A, ∃ i, x ∈ Set.range (ψ i) := by
    intro x
    have : ∃ i, a i ∉ (F x).asIdeal := by
      by_contra hno
      push_neg at hno
      have hle : Ideal.span (Set.range a) ≤ (F x).asIdeal := Ideal.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hno i)
      rw [hspan] at hle
      exact (F x).isPrime.ne_top (top_le_iff.1 hle)
    obtain ⟨i, hi⟩ := this
    letI := (b i).toAlgebra
    have := (hR i).2.2
    obtain ⟨y, hy⟩ := (PrimeSpectrum.localization_away_comap_range (R i) (a i)).ge hi
    obtain ⟨z, hz, -⟩ := Scheme.exists_preimage_of_isPullback (hpb i) x y hy.symm
    exact ⟨i, z, hz⟩
  have hdj : ∀ i, IsPreimmersion (C i).j ∧ Flat (C i).j ∧ IsDominant (C i).j ∧ QuasiCompact (C i).j := fun i => by
    obtain ⟨-, -, -, h1, h2, h3, h4⟩ := GlobalTheory.ModelRelCompare.densePart (C i) (hR i).1
    exact ⟨h1, h2, h3, h4⟩
  have hOZ : LocallyOfFiniteType (spMap (algebraMap ℤ (𝓞 c.F))) ∧ Flat (spMap (algebraMap ℤ (𝓞 c.F))) := by
    haveI : FiniteDimensional ℚ c.F := c.fin
    haveI : NumberField c.F := ⟨⟩
    exact ⟨(HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).2 (RingHom.finiteType_algebraMap.2 inferInstance),
      (HasRingHomProperty.Spec_iff (P := @Flat)).2 (RingHom.flat_algebraMap_iff.2 inferInstance)⟩
  have hsft : ∀ i, LocallyOfFiniteType (C i).s := fun i => by
    obtain ⟨N, e, he, hs⟩ := (C i).proj
    have := isProper_str (R i) N
    rw [← hs]; infer_instance
  haveI : IsZariskiLocalAtSource @Flat.{0} := HasRingHomProperty.instIsZariskiLocalAtSource
  haveI : IsZariskiLocalAtSource @LocallyOfFiniteType.{0} := HasRingHomProperty.instIsZariskiLocalAtSource
  have hflat : Flat F := of_cover_openImmersions ψ hcov F fun i => by
    rw [(hpb i).w]
    have := (C i).flat
    infer_instance
  refine ⟨hcov, ?_, hflat, ⟨F ≫ spMap (algebraMap ℤ (𝓞 c.F)), ?_, ?_⟩, fun i => ?_⟩
  · intro x
    obtain ⟨i, z, rfl⟩ := hcov x
    obtain ⟨h1, h2⟩ := (C i).normal z
    let e := (asIso ((ψ i).stalkMap z)).commRingCatIsoToRingEquiv
    exact ⟨e.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e.symm⟩
  · refine of_cover_openImmersions ψ hcov _ fun i => ?_
    rw [← Category.assoc, (hpb i).w, Category.assoc]
    have := hOZ.1
    infer_instance
  · have := hOZ.2
    infer_instance
  · obtain ⟨h1, h2, -, h4⟩ := hdj i
    refine ⟨inferInstance, inferInstance, ?_, inferInstance⟩
    refine ⟨fun x => ?_⟩
    rw [mem_closure_iff]
    intro o ho hx
    obtain ⟨k, z, rfl⟩ := hcov x
    have hV : IsOpen ((ψ k) ⁻¹' o) := ho.preimage (ψ k).continuous
    have hd := (hdj k).2.2.1
    obtain ⟨_, hw, w, rfl⟩ := (hd.denseRange).inter_open_nonempty _ hV ⟨z, hx⟩
    refine ⟨((C k).j ≫ ψ k) w, ?_, ?_⟩
    · rw [Scheme.Hom.comp_apply]; exact hw
    · rw [hj k i]; exact ⟨w, rfl⟩

end GlobalTheory.GlueLoc
