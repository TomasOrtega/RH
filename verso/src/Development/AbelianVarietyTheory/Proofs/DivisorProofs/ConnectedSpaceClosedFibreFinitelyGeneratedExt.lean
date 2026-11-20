import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppTopBijectiveAndSurjectiveNormalDomain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppBijectiveOfFlatBaseChangeGlobalFunctions
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZariskiConnectednessIsPreconnectedFibreStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

/- English proof (translation)
Introduce `R _ _ _ S π hprop hsurj hbij K _ κ L hL n c hLc`. Use `haveI := hprop`. Use `haveI := hsurj`. Establish `hc : ∀ j, c j ∈ L` using `fun j => hLc ▸ Subfield.subset_closure (Or.inr ⟨j, rfl⟩)`. Use `set A := MvPolynomial (Fin n) R`.

Use `set ιC : R →+* A := MvPolynomial.C with hC`. Use `set β : R →+* L := (κ.codRestrict L hL).comp (residue R) with hβ`. Use `set φ : A →+* L := MvPolynomial.eval₂Hom β (fun j => ⟨c j, hc j⟩) with hφ`. Establish `hφC : φ.comp ιC = β`. Use `RingHom.ext fun r => ?_` and prove the remaining obligations.

Use `show MvPolynomial.eval₂ β (fun j => (⟨c j, hc j⟩ : L)) (MvPolynomial.C r) = β r`. Conclude with `MvPolynomial.eval₂_C _ _ _`. Establish `hx : spMap β = spMap φ ≫ spMap ιC`. Rewrite using `[← hφC]`. Use `show Spec.map (CommRingCat.ofHom (φ.comp ιC)) = Spec.map (CommRingCat.ofHom φ) ≫ Spec.map (CommRingCat.ofHom ιC)`.

Rewrite using `[← Spec.map_comp]`. Both sides reduce to the same expression. Establish `hdiv : ∀ x : L, ∃ a b : A, φ b ≠ 0 ∧ φ b * x = φ a`. Establish `hsub : Subring.closure (Set.range κ ∪ Set.range c) ≤ (φ.range).map L.subtype`. Rewrite using `[Subring.closure_le]`.

Introduce and unpack `y (⟨z, rfl⟩ | ⟨j, rfl⟩)`. Take `⟨r, rfl⟩` from `residue_surjective z`. Conclude with `⟨β r, ⟨MvPolynomial.C r, MvPolynomial.eval₂_C _ _ _⟩, rfl⟩`. Conclude with `⟨⟨c j, hc j⟩, ⟨MvPolynomial.X j, MvPolynomial.eval₂_X _ _ _⟩, rfl⟩`. Introduce `x`.

Establish `hx' : (x : K) ∈ Subfield.closure (Set.range κ ∪ Set.range c)` using `hLc ▸ x.2`. Take `⟨y, hy, z, hz, hyz⟩` from `Subfield.mem_closure_iff.1 hx'`. Take `⟨y', ⟨a, rfl⟩, rfl⟩` from `hsub hy`. Take `⟨z', ⟨b, rfl⟩, rfl⟩` from `hsub hz`. Distinguish the cases in `hb : φ b = 0`.

Use `⟨0, 1, by simp, ?_⟩` and prove the remaining obligations. Establish `: (x : K) = 0` using `by rw [← hyz]; simp [hb]`. Establish `: x = 0` using `Subtype.ext this`. Simplify using `[this]`. Use `⟨a, b, hb, ?_⟩` and prove the remaining obligations.

Apply `Subtype.ext` to reduce the goal to its premises. Establish `hb' : ((φ b : L) : K) ≠ 0` using `fun h => hb (Subtype.ext h)`. Simplify using `only [Subfield.coe_mul, L.subtype_apply] at hyz ⊢`. Rewrite using `[← hyz]`. Clear the denominators using the available nonvanishing facts.

Establish `hstalk : φ.SurjectiveOnStalks`. Use `RingHom.surjectiveOnStalks_of_exists_div fun x => ?_` and prove the remaining obligations. Take `⟨a, b, hb, e⟩` from `hdiv x`. Conclude with `⟨a, b, (isUnit_iff_ne_zero).2 hb, e⟩`. Use `haveI hpre : IsPreimmersion (spMap φ) := by`.

Rewrite using `[IsPreimmersion.SpecMap_iff]`. Use `⟨?_, hstalk⟩` and prove the remaining obligations. Use `haveI : Subsingleton (PrimeSpectrum L) := inferInstance`. Conclude with `Topology.IsEmbedding.of_subsingleton _`. Use `set π' : pullback π (spMap ιC) ⟶ Sp A := pullback.snd π (spMap ιC) with hπ'`.

Establish `hflat : Flat (spMap ιC)`. Use `Flat.SpecMap_iff.2 ?_` and prove the remaining obligations. Use `show (algebraMap R A).Flat`. Conclude with `RingHom.flat_algebraMap_iff.2 inferInstance`. Establish `hbij' : ∀ V : (Sp A).Opens, Function.Bijective (π'.app V).hom` using `GlobalTheory.Mum.app_bijective_of_flat_baseChange R S (Sp A) _ π (spMap ιC) _ _ inferInstance inferInstance hbij hflat (IsPullback.of_hasPullback π (spMap ιC)).flip`.

Take `⟨q⟩ : Nonempty (PrimeSpectrum L)` from `inferInstance`. Establish `hconn` using `GlobalTheory.T.zariski_connectedness_isPreconnected_fibre _ _ π' inferInstance inferInstance hbij' (spMap φ q)`. Establish `hrange : Set.range (spMap φ) = {spMap φ q}`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨q', rfl⟩`. Rewrite using `[Subsingleton.elim q' q]`. Both sides reduce to the same expression. Introduce and unpack `rfl`. Conclude with `⟨q, rfl⟩`.

Use `set f := pullback.fst π' (spMap φ) with hf`. Establish `hfr : Set.range f = {s | π' s = spMap φ q}`. Rewrite using `[hf, Scheme.Pullback.range_fst, hrange]`. Both sides reduce to the same expression. Establish `hP : PreconnectedSpace ↥(pullback π' (spMap φ))`.

Use `⟨?_⟩` and prove the remaining obligations. Rewrite using `[← f.isEmbedding.isInducing.isPreconnected_image, Set.image_univ, hfr]`. Conclude with `hconn`. Establish `e : pullback π (spMap β) ≅ pullback π' (spMap φ)` using `pullback.congrHom rfl hx ≪≫ (pullbackLeftPullbackSndIso π (spMap ιC) (spMap φ)).symm`. Take `⟨z, -⟩` from `(pullback.snd π (spMap β)).surjective q`.

Use `haveI : ConnectedSpace ↥(pullback π' (spMap φ)) := ConnectedSpace.mk ⟨e.hom z⟩`. Conclude with `(Scheme.homeoOfIso e).symm.surjective.connectedSpace (Scheme.homeoOfIso e).symm.continuous`.
-/
theorem connectedSpace_pullback_of_finitelyGenerated_residue :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (S : Scheme.{0}) (π : S ⟶ Sp R),
      IsProper π → Surjective π → Function.Bijective π.appTop.hom →
      ∀ (K : Type) [Field K] (κ : ResidueField R →+* K) (L : Subfield K) (hL : ∀ x, κ x ∈ L) (n : ℕ) (c : Fin n → K),
        L = Subfield.closure (Set.range κ ∪ Set.range c) →
        ConnectedSpace (pullback π (spMap ((κ.codRestrict L hL).comp (residue R))) : Scheme.{0}) := by
  intro R _ _ _ S π hprop hsurj hbij K _ κ L hL n c hLc
  haveI := hprop
  haveI := hsurj
  have hc : ∀ j, c j ∈ L := fun j => hLc ▸ Subfield.subset_closure (Or.inr ⟨j, rfl⟩)
  set A := MvPolynomial (Fin n) R
  set ιC : R →+* A := MvPolynomial.C with hC
  set β : R →+* L := (κ.codRestrict L hL).comp (residue R) with hβ
  set φ : A →+* L := MvPolynomial.eval₂Hom β (fun j => ⟨c j, hc j⟩) with hφ
  have hφC : φ.comp ιC = β := by
    refine RingHom.ext fun r => ?_
    show MvPolynomial.eval₂ β (fun j => (⟨c j, hc j⟩ : L)) (MvPolynomial.C r) = β r
    exact MvPolynomial.eval₂_C _ _ _
  have hx : spMap β = spMap φ ≫ spMap ιC := by
    rw [← hφC]
    show Spec.map (CommRingCat.ofHom (φ.comp ιC)) = Spec.map (CommRingCat.ofHom φ) ≫ Spec.map (CommRingCat.ofHom ιC)
    rw [← Spec.map_comp]; rfl

  have hdiv : ∀ x : L, ∃ a b : A, φ b ≠ 0 ∧ φ b * x = φ a := by
    have hsub : Subring.closure (Set.range κ ∪ Set.range c) ≤ (φ.range).map L.subtype := by
      rw [Subring.closure_le]
      rintro y (⟨z, rfl⟩ | ⟨j, rfl⟩)
      · obtain ⟨r, rfl⟩ := residue_surjective z
        exact ⟨β r, ⟨MvPolynomial.C r, MvPolynomial.eval₂_C _ _ _⟩, rfl⟩
      · exact ⟨⟨c j, hc j⟩, ⟨MvPolynomial.X j, MvPolynomial.eval₂_X _ _ _⟩, rfl⟩
    intro x
    have hx' : (x : K) ∈ Subfield.closure (Set.range κ ∪ Set.range c) := hLc ▸ x.2
    obtain ⟨y, hy, z, hz, hyz⟩ := Subfield.mem_closure_iff.1 hx'
    obtain ⟨y', ⟨a, rfl⟩, rfl⟩ := hsub hy
    obtain ⟨z', ⟨b, rfl⟩, rfl⟩ := hsub hz
    by_cases hb : φ b = 0
    · refine ⟨0, 1, by simp, ?_⟩
      have : (x : K) = 0 := by rw [← hyz]; simp [hb]
      have : x = 0 := Subtype.ext this
      simp [this]
    · refine ⟨a, b, hb, ?_⟩
      apply Subtype.ext
      have hb' : ((φ b : L) : K) ≠ 0 := fun h => hb (Subtype.ext h)
      simp only [Subfield.coe_mul, L.subtype_apply] at hyz ⊢
      rw [← hyz]; field_simp
  have hstalk : φ.SurjectiveOnStalks := by
    refine RingHom.surjectiveOnStalks_of_exists_div fun x => ?_
    obtain ⟨a, b, hb, e⟩ := hdiv x
    exact ⟨a, b, (isUnit_iff_ne_zero).2 hb, e⟩
  haveI hpre : IsPreimmersion (spMap φ) := by
    rw [IsPreimmersion.SpecMap_iff]
    refine ⟨?_, hstalk⟩
    haveI : Subsingleton (PrimeSpectrum L) := inferInstance
    exact Topology.IsEmbedding.of_subsingleton _

  set π' : pullback π (spMap ιC) ⟶ Sp A := pullback.snd π (spMap ιC) with hπ'
  have hflat : Flat (spMap ιC) := by
    refine Flat.SpecMap_iff.2 ?_
    show (algebraMap R A).Flat
    exact RingHom.flat_algebraMap_iff.2 inferInstance
  have hbij' : ∀ V : (Sp A).Opens, Function.Bijective (π'.app V).hom :=
    GlobalTheory.Mum.app_bijective_of_flat_baseChange R S (Sp A) _ π (spMap ιC) _ _ inferInstance inferInstance
      hbij hflat (IsPullback.of_hasPullback π (spMap ιC)).flip
  obtain ⟨q⟩ : Nonempty (PrimeSpectrum L) := inferInstance
  have hconn := GlobalTheory.T.zariski_connectedness_isPreconnected_fibre _ _ π' inferInstance inferInstance hbij' (spMap φ q)
  have hrange : Set.range (spMap φ) = {spMap φ q} := by
    ext y
    constructor
    · rintro ⟨q', rfl⟩; rw [Subsingleton.elim q' q]; rfl
    · rintro rfl; exact ⟨q, rfl⟩
  set f := pullback.fst π' (spMap φ) with hf
  have hfr : Set.range f = {s | π' s = spMap φ q} := by
    rw [hf, Scheme.Pullback.range_fst, hrange]; rfl
  have hP : PreconnectedSpace ↥(pullback π' (spMap φ)) := by
    refine ⟨?_⟩
    rw [← f.isEmbedding.isInducing.isPreconnected_image, Set.image_univ, hfr]
    exact hconn
  have e : pullback π (spMap β) ≅ pullback π' (spMap φ) :=
    pullback.congrHom rfl hx ≪≫ (pullbackLeftPullbackSndIso π (spMap ιC) (spMap φ)).symm
  obtain ⟨z, -⟩ := (pullback.snd π (spMap β)).surjective q
  haveI : ConnectedSpace ↥(pullback π' (spMap φ)) := ConnectedSpace.mk ⟨e.hom z⟩
  exact (Scheme.homeoOfIso e).symm.surjective.connectedSpace (Scheme.homeoOfIso e).symm.continuous

end GlobalTheory.Mum
