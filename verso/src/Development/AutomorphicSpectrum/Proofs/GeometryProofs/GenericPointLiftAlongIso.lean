import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSncPatchRat
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsCptGenResidueFieldGeneric
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenPtSpecializes

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

namespace GlobalTheory.CompanionTheory.Ar.SncBase

/- English proof (translation)
Use `haveI := IsOpenImmersion.of_isIso (f ∣_ U)`. Set `a : (f ⁻¹ᵁ U : Scheme)` to `⟨y, hy⟩`. Set `a' : (f ⁻¹ᵁ U : Scheme)` to `⟨y', hy'⟩`. Establish `h : (f ∣_ U) a = (f ∣_ U) a'` using `Subtype.ext (by rw [morphismRestrict_base_coe, morphismRestrict_base_coe]; exact e)`. Conclude with `congrArg Subtype.val ((f ∣_ U).isOpenEmbedding.injective h)`.
-/
theorem eq_of_isIso_restrict {W X' : Scheme.{0}} (f : X' ⟶ W) (U : W.Opens) (hU : IsIso (f ∣_ U)) {y y' : X'}
    (hy : f y ∈ U) (hy' : f y' ∈ U) (e : f y = f y') : y = y' := by
  haveI := IsOpenImmersion.of_isIso (f ∣_ U)
  let a : (f ⁻¹ᵁ U : Scheme) := ⟨y, hy⟩
  let a' : (f ⁻¹ᵁ U : Scheme) := ⟨y', hy'⟩
  have h : (f ∣_ U) a = (f ∣_ U) a' :=
    Subtype.ext (by rw [morphismRestrict_base_coe, morphismRestrict_base_coe]; exact e)
  exact congrArg Subtype.val ((f ∣_ U).isOpenEmbedding.injective h)

/- English proof (translation)
Apply `PrimeSpectrum.ext` to reduce the goal to its premises. Establish `h` using `(IsLocalRing.isField_iff_maximalIdeal_eq (R := R)).1 hR`. Establish `h1 : z.asIdeal ≤ IsLocalRing.maximalIdeal R` using `IsLocalRing.le_maximalIdeal z.isPrime.ne_top`. Use `show z.asIdeal = IsLocalRing.maximalIdeal R`. Rewrite `h1`, the goal using `[h]`.

Conclude with `le_bot_iff.1 h1`.
-/
private theorem eq_closedPoint_of_isField {R : Type} [CommRing R] [IsLocalRing R] (hR : IsField R)
    (z : PrimeSpectrum R) : z = IsLocalRing.closedPoint R := by
  apply PrimeSpectrum.ext
  have h := (IsLocalRing.isField_iff_maximalIdeal_eq (R := R)).1 hR
  have h1 : z.asIdeal ≤ IsLocalRing.maximalIdeal R := IsLocalRing.le_maximalIdeal z.isPrime.ne_top
  show z.asIdeal = IsLocalRing.maximalIdeal R
  rw [h] at h1 ⊢
  exact le_bot_iff.1 h1

/- English proof (translation)
Establish `hF : IsField (X.presheaf.stalk (genPt ξ))` using `MulEquiv.isField (Field.toIsField Ω) (RingEquiv.ofBijective _ hb).toMulEquiv`. Establish `hy' : y ∈ Set.range (X.fromSpecStalk (genPt ξ))`. Rewrite using `[Scheme.range_fromSpecStalk]`. Conclude with `hy`. Take `⟨q, rfl⟩` from `hy'`.

Rewrite using `[eq_closedPoint_of_isField hF q, Scheme.fromSpecStalk_closedPoint]`.
-/
private theorem eq_genPt_of_specializes_of_bijective {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (hb : Function.Bijective (Scheme.stalkClosedPointTo ξ).hom) (y : X) (hy : y ⤳ genPt ξ) :
    y = genPt ξ := by
  have hF : IsField (X.presheaf.stalk (genPt ξ)) :=
    MulEquiv.isField (Field.toIsField Ω) (RingEquiv.ofBijective _ hb).toMulEquiv
  have hy' : y ∈ Set.range (X.fromSpecStalk (genPt ξ)) := by
    rw [Scheme.range_fromSpecStalk]; exact hy
  obtain ⟨q, rfl⟩ := hy'
  rw [eq_closedPoint_of_isField hF q, Scheme.fromSpecStalk_closedPoint]

/- English proof (translation)
Substitute `h` using the available equality. Rewrite `hξ` using `[Scheme.stalkClosedPointTo_comp]`. Introduce `z`. Take `⟨a, ha⟩` from `hξ z`. Conclude with `⟨(Scheme.Hom.stalkMap f _).hom a, ha⟩`.
-/
private theorem surjective_stalkClosedPointTo_of_comp {X Y : Scheme.{0}} {Ω : Type} [Field Ω]
    (g : Spec (CommRingCat.of Ω) ⟶ X) (f : X ⟶ Y) (ξ : Spec (CommRingCat.of Ω) ⟶ Y) (h : g ≫ f = ξ)
    (hξ : Function.Surjective (Scheme.stalkClosedPointTo ξ).hom) :
    Function.Surjective (Scheme.stalkClosedPointTo g).hom := by
  subst h
  rw [Scheme.stalkClosedPointTo_comp] at hξ
  intro z
  obtain ⟨a, ha⟩ := hξ z
  exact ⟨(Scheme.Hom.stalkMap f _).hom a, ha⟩

/- English proof (translation)
Introduce `W X' f U Ω _ ξ hiso hU hξ hdom`. Take `⟨hb, -⟩` from `hξ`. Establish `hr : Set.range ξ ⊆ Set.range U.ι`. Rewrite using `[Scheme.Opens.range_ι]`. Introduce and unpack `_ ⟨z, rfl⟩`.

Rewrite using `[eq_closedPoint_of_isField (Field.toIsField Ω) z]`. Conclude with `hU`. Set `ξ' : Sp Ω ⟶ X'` to `IsOpenImmersion.lift U.ι ξ hr ≫ inv (f ∣_ U) ≫ (f ⁻¹ᵁ U).ι`. Establish `hfac : ξ' ≫ f = ξ`. Simplify using `only [ξ', Category.assoc]`.

Rewrite using `[← morphismRestrict_ι, IsIso.inv_hom_id_assoc, IsOpenImmersion.lift_fac]`. Establish `hfg : f (genPt ξ') = genPt ξ`. Establish `h3` using `Scheme.Hom.comp_apply ξ' f (IsLocalRing.closedPoint Ω)`. Rewrite `h3` using `[hfac]`. Conclude with `h3.symm`.

Establish `hmem : genPt ξ' ∈ f ⁻¹ᵁ U` using `by show f (genPt ξ') ∈ U`. Rewrite using `[hfg]`. Conclude with `hU`. Use `⟨ξ', hfac, ?_⟩` and prove the remaining obligations. Use `isCptGen_of_maximal_of_surjective hdom ξ' ?_ ?_` and prove the remaining obligations.

Introduce `y hy`. Establish `hyU : y ∈ f ⁻¹ᵁ U` using `hy.mem_open (f ⁻¹ᵁ U).isOpen hmem`. Establish `h1 : f y ⤳ genPt ξ`. Establish `h2` using `hy.map f.continuous`. Rewrite `h2` using `[hfg]`. Then use the resulting hypothesis.

Conclude with `eq_of_isIso_restrict f U hiso hyU hmem ((eq_genPt_of_specializes_of_bijective ξ hb (f y) h1).trans hfg.symm)`. Conclude with `surjective_stalkClosedPointTo_of_comp ξ' f ξ hfac hb.2`.
-/
theorem exists_lift_isCptGen : ∀ (W X' : Scheme.{0}) (f : X' ⟶ W) (U : W.Opens) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ W),
    IsIso (f ∣_ U) → genPt ξ ∈ U → IsCptGen ξ → (∀ x : X', IsDomain (X'.presheaf.stalk x)) →
    ∃ ξ' : Sp Ω ⟶ X', ξ' ≫ f = ξ ∧ IsCptGen ξ' := by
  intro W X' f U Ω _ ξ hiso hU hξ hdom
  obtain ⟨hb, -⟩ := hξ
  have hr : Set.range ξ ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    rw [eq_closedPoint_of_isField (Field.toIsField Ω) z]
    exact hU
  let ξ' : Sp Ω ⟶ X' := IsOpenImmersion.lift U.ι ξ hr ≫ inv (f ∣_ U) ≫ (f ⁻¹ᵁ U).ι
  have hfac : ξ' ≫ f = ξ := by
    simp only [ξ', Category.assoc]
    rw [← morphismRestrict_ι, IsIso.inv_hom_id_assoc, IsOpenImmersion.lift_fac]
  have hfg : f (genPt ξ') = genPt ξ := by
    have h3 := Scheme.Hom.comp_apply ξ' f (IsLocalRing.closedPoint Ω)
    rw [hfac] at h3
    exact h3.symm
  have hmem : genPt ξ' ∈ f ⁻¹ᵁ U := by
    show f (genPt ξ') ∈ U
    rw [hfg]; exact hU
  refine ⟨ξ', hfac, ?_⟩
  refine isCptGen_of_maximal_of_surjective hdom ξ' ?_ ?_
  · intro y hy
    have hyU : y ∈ f ⁻¹ᵁ U := hy.mem_open (f ⁻¹ᵁ U).isOpen hmem
    have h1 : f y ⤳ genPt ξ := by
      have h2 := hy.map f.continuous
      rwa [hfg] at h2
    exact eq_of_isIso_restrict f U hiso hyU hmem ((eq_genPt_of_specializes_of_bijective ξ hb (f y) h1).trans hfg.symm)
  · exact surjective_stalkClosedPointTo_of_comp ξ' f ξ hfac hb.2

end GlobalTheory.CompanionTheory.Ar.SncBase
