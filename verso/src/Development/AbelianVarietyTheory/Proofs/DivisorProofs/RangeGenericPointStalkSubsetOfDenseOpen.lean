import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

/- English proof (translation)
Introduce and unpack `_ ⟨x, rfl⟩`. Establish `hZ : irreducibleComponent s ∈ irreducibleComponents S` using `irreducibleComponent_mem_irreducibleComponents s`. Establish `hZo : IsOpen (irreducibleComponent s)` using `GlobalTheory.IsNormalScheme.isOpen_of_mem_irreducibleComponents hZ`. Take `⟨_, hu, ⟨u, rfl⟩⟩` from `hj.inter_open_nonempty _ hZo ⟨s, mem_irreducibleComponent⟩`. Establish `hg` using `hZ.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ hZ)`.

Establish `hgs : hZ.1.genericPoint ⤳ s` using `hg.specializes mem_irreducibleComponent`. Establish `hgr : hZ.1.genericPoint ∈ Set.range (S.fromSpecStalk s)`. Rewrite using `[Scheme.range_fromSpecStalk]`. Conclude with `hgs`. Take `⟨p, hp⟩` from `hgr`.

Establish `hxp : (ReciprocityTheory.ChartRestriction.G.Out.jK (S.presheaf.stalk s)) x ⤳ p`. Use `(PrimeSpectrum.le_iff_specializes (R := S.presheaf.stalk s) _ _).mp ?_` and prove the remaining obligations. Use `show Ideal.comap _ x.asIdeal ≤ p.asIdeal`. Establish `hx0 : x.asIdeal = ⊥` using `@Ideal.eq_bot_of_prime (FractionRing (S.presheaf.stalk s)) _ x.asIdeal x.isPrime`. Introduce `a ha`.

Rewrite `ha` using `[Ideal.mem_comap, hx0, Ideal.mem_bot]`. Establish `ha0 : a = 0` using `IsFractionRing.injective (S.presheaf.stalk s) (FractionRing (S.presheaf.stalk s)) (by simpa using ha)`. Rewrite using `[ha0]`. Conclude with `Ideal.zero_mem _`. Establish `h1 : (ReciprocityTheory.ChartRestriction.G.Out.jK (S.presheaf.stalk s) ≫ S.fromSpecStalk s) x ⤳ hZ.1.genericPoint`.

Rewrite using `[Scheme.Hom.comp_apply, ← hp]`. Conclude with `hxp.map (S.fromSpecStalk s).continuous`. Establish `h2 : hZ.1.genericPoint ⤳ j u` using `hg.specializes hu`. Conclude with `(h1.trans h2).mem_open j.isOpenEmbedding.isOpen_range ⟨u, rfl⟩`.
-/
theorem range_jK_fromSpecStalk_subset_of_dense_range {U S : Scheme.{0}} [GlobalTheory.IsNormalScheme S]
    [IsLocallyNoetherian S] (j : U ⟶ S) [IsOpenImmersion j] (hj : Dense (Set.range j)) (s : S) :
    Set.range (ReciprocityTheory.ChartRestriction.G.Out.jK (S.presheaf.stalk s) ≫ S.fromSpecStalk s) ⊆
      Set.range j := by
  rintro _ ⟨x, rfl⟩
  have hZ : irreducibleComponent s ∈ irreducibleComponents S :=
    irreducibleComponent_mem_irreducibleComponents s
  have hZo : IsOpen (irreducibleComponent s) :=
    GlobalTheory.IsNormalScheme.isOpen_of_mem_irreducibleComponents hZ
  obtain ⟨_, hu, ⟨u, rfl⟩⟩ := hj.inter_open_nonempty _ hZo ⟨s, mem_irreducibleComponent⟩
  have hg := hZ.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ hZ)
  have hgs : hZ.1.genericPoint ⤳ s := hg.specializes mem_irreducibleComponent
  have hgr : hZ.1.genericPoint ∈ Set.range (S.fromSpecStalk s) := by
    rw [Scheme.range_fromSpecStalk]; exact hgs
  obtain ⟨p, hp⟩ := hgr
  have hxp : (ReciprocityTheory.ChartRestriction.G.Out.jK (S.presheaf.stalk s)) x ⤳ p := by
    refine (PrimeSpectrum.le_iff_specializes (R := S.presheaf.stalk s) _ _).mp ?_
    show Ideal.comap _ x.asIdeal ≤ p.asIdeal
    have hx0 : x.asIdeal = ⊥ :=
      @Ideal.eq_bot_of_prime (FractionRing (S.presheaf.stalk s)) _ x.asIdeal x.isPrime
    intro a ha
    rw [Ideal.mem_comap, hx0, Ideal.mem_bot] at ha
    have ha0 : a = 0 :=
      IsFractionRing.injective (S.presheaf.stalk s) (FractionRing (S.presheaf.stalk s))
        (by simpa using ha)
    rw [ha0]
    exact Ideal.zero_mem _
  have h1 : (ReciprocityTheory.ChartRestriction.G.Out.jK (S.presheaf.stalk s) ≫ S.fromSpecStalk s) x ⤳
      hZ.1.genericPoint := by
    rw [Scheme.Hom.comp_apply, ← hp]
    exact hxp.map (S.fromSpecStalk s).continuous
  have h2 : hZ.1.genericPoint ⤳ j u := hg.specializes hu
  exact (h1.trans h2).mem_open j.isOpenEmbedding.isOpen_range ⟨u, rfl⟩

end GlobalTheory
