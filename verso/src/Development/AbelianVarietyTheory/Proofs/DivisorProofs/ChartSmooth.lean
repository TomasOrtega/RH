import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeometricallyConnectedOfAlgClosedInFunctionField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimEqSucc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLocalSubringGenericPoint
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CurveSmooth

/- English proof (translation)
The claim follows from `((genericPoint_spec C).mem_open_set_iff V.isOpen).2 ⟨z, trivial, hz⟩`.
-/
theorem genericPoint_mem {C : Scheme.{0}} [IsIntegral C] (V : C.Opens) {z : C} (hz : z ∈ V) :
    genericPoint C ∈ V :=
  ((genericPoint_spec C).mem_open_set_iff V.isOpen).2 ⟨z, trivial, hz⟩

/- English proof (translation)
Introduce `hF`. Establish `key : ∀ p : PrimeSpectrum Γ(C, U), p.asIdeal = ⊥` using `fun p => by`. Rewrite using `[eq_bot_iff]`. Introduce `a ha`. Assume the negation of the conclusion as `h0`.

Take `⟨b, hb⟩` from `hF.mul_inv_cancel h0`. Conclude with `p.2.ne_top ((Ideal.eq_top_iff_one _).2 (hb ▸ p.asIdeal.mul_mem_right b ha))`. Establish `hη` using `genericPoint_mem U hx`. Establish `e : hU.primeIdealOf ⟨x, hx⟩ = hU.primeIdealOf ⟨genericPoint C, hη⟩` using `PrimeSpectrum.ext ((key _).trans (key _).symm)`. Apply `hxη` to reduce the goal to its premises.

Establish `h1` using `hU.fromSpec_primeIdealOf ⟨x, hx⟩`. Establish `h2` using `hU.fromSpec_primeIdealOf ⟨genericPoint C, hη⟩`. Rewrite `h1` using `[e]`. Conclude with `h1.symm.trans h2`.
-/
theorem not_isField_of_mem {C : Scheme.{0}} [IsIntegral C] {U : C.Opens} (hU : IsAffineOpen U)
    {x : C} (hx : x ∈ U) (hxη : x ≠ genericPoint C) : ¬ IsField Γ(C, U) := by
  intro hF
  have key : ∀ p : PrimeSpectrum Γ(C, U), p.asIdeal = ⊥ := fun p => by
    rw [eq_bot_iff]
    intro a ha
    by_contra h0
    obtain ⟨b, hb⟩ := hF.mul_inv_cancel h0
    exact p.2.ne_top ((Ideal.eq_top_iff_one _).2 (hb ▸ p.asIdeal.mul_mem_right b ha))
  have hη := genericPoint_mem U hx
  have e : hU.primeIdealOf ⟨x, hx⟩ = hU.primeIdealOf ⟨genericPoint C, hη⟩ :=
    PrimeSpectrum.ext ((key _).trans (key _).symm)
  apply hxη
  have h1 := hU.fromSpec_primeIdealOf ⟨x, hx⟩
  have h2 := hU.fromSpec_primeIdealOf ⟨genericPoint C, hη⟩
  rw [e] at h1
  exact h1.symm.trans h2

/- English proof (translation)
Use `haveI := h U hU ⟨⟨x, hx⟩⟩`. Establish `hnf` using `not_isField_of_mem hU hx hxη`. Set `e` to `Scheme.ΓSpecIso (CommRingCat.of K)`. Establish `hft' : ((strHom K C).appLE ⊤ U le_top).hom.FiniteType` using `HasRingHomProperty.appLE @LocallyOfFiniteType (strHom K C) hft ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top`. Set `φ : K →+* Γ(C, U)` to `(e.inv ≫ (strHom K C).appLE ⊤ U le_top).hom`.

Establish `hφ : φ.FiniteType` using `(RingHom.finiteType_respectsIso.cancel_left_isIso e.inv ((strHom K C).appLE ⊤ U le_top)).2 hft'`. Use `letI := φ.toAlgebra`. Use `haveI : Algebra.FiniteType K Γ(C, U) := hφ`. Establish `hs` using `GlobalTheory.RegGenSmooth.smooth_of_regular K Γ(C, U) 1 fun m hm => by`. Establish `hne : m ≠ ⊥` using `fun h0 => hnf (Ring.isField_iff_maximal_bot.2 (h0 ▸ hm))`.

Use `haveI := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain Γ(C, U) hne (Localization.AtPrime m)`. Use `⟨inferInstance, ?_⟩` and prove the remaining obligations. Rewrite using `[IsPrincipalIdealRing.ringKrullDim_eq_one _ (IsDiscreteValuationRing.not_isField (Localization.AtPrime m))]`. Both sides reduce to the same expression. Establish `hQ : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1) φ` using `HasRingHomProperty.Spec_iff.1 hs`.

Conclude with `((HasRingHomProperty.isLocal_ringHomProperty (@SmoothOfRelativeDimension 1)).respectsIso.cancel_left_isIso e.inv ((strHom K C).appLE ⊤ U le_top)).1 hQ`.
-/
theorem chart_smooth (K : Type) [Field K] [PerfectField K] (C : Scheme.{0}) [IsIntegral C]
    [Algebra K Γ(C, ⊤)] (hft : LocallyOfFiniteType (strHom K C))
    (h : ∀ U : C.Opens, IsAffineOpen U → Nonempty U → IsDedekindDomain Γ(C, U))
    (U : C.Opens) (hU : IsAffineOpen U) {x : C} (hx : x ∈ U) (hxη : x ≠ genericPoint C) :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)
      ((strHom K C).appLE ⊤ U le_top).hom := by
  haveI := h U hU ⟨⟨x, hx⟩⟩
  have hnf := not_isField_of_mem hU hx hxη
  let e := Scheme.ΓSpecIso (CommRingCat.of K)
  have hft' : ((strHom K C).appLE ⊤ U le_top).hom.FiniteType :=
    HasRingHomProperty.appLE @LocallyOfFiniteType (strHom K C) hft ⟨⊤, isAffineOpen_top _⟩
      ⟨U, hU⟩ le_top
  let φ : K →+* Γ(C, U) := (e.inv ≫ (strHom K C).appLE ⊤ U le_top).hom
  have hφ : φ.FiniteType :=
    (RingHom.finiteType_respectsIso.cancel_left_isIso e.inv ((strHom K C).appLE ⊤ U le_top)).2 hft'
  letI := φ.toAlgebra
  haveI : Algebra.FiniteType K Γ(C, U) := hφ
  have hs := GlobalTheory.RegGenSmooth.smooth_of_regular K Γ(C, U) 1 fun m hm => by
    have hne : m ≠ ⊥ := fun h0 => hnf (Ring.isField_iff_maximal_bot.2 (h0 ▸ hm))
    haveI := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain Γ(C, U) hne
      (Localization.AtPrime m)
    refine ⟨inferInstance, ?_⟩
    rw [IsPrincipalIdealRing.ringKrullDim_eq_one _
      (IsDiscreteValuationRing.not_isField (Localization.AtPrime m))]
    rfl
  have hQ : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1) φ :=
    HasRingHomProperty.Spec_iff.1 hs
  exact ((HasRingHomProperty.isLocal_ringHomProperty (@SmoothOfRelativeDimension 1)).respectsIso.cancel_left_isIso
    e.inv ((strHom K C).appLE ⊤ U le_top)).1 hQ

/- English proof (translation)
Introduce `K _ _ C _ _ hft hd h`. Take `⟨x₀, hx₀⟩ : ∃ x₀ : C, x₀ ≠ genericPoint C` from `by by_contra! hall haveI : Subsingleton C := ⟨fun a b => (hall a).trans (hall b).symm⟩`. Establish `h0` using `topologicalKrullDim_zero_of_discreteTopology C`. Rewrite `h0` using `[hd]`. Conclude with `absurd h0 (by decide)`.

Use `HasRingHomProperty.of_iSup_eq_top (P := @SmoothOfRelativeDimension 1) (fun U : {U : C.affineOpens // ∃ x ∈ U.1, x ≠ genericPoint C} => U.1) ?_ ?_` and prove the remaining obligations. Rewrite using `[eq_top_iff]`. Introduce `y _`. Take `⟨U, hU, hy, -⟩` from `exists_isAffineOpen_mem_and_subset (U := ⊤) (x := y) trivial`. Distinguish the cases in `hex : ∃ x ∈ U, x ≠ genericPoint C`.

Conclude with `Opens.mem_iSup.2 ⟨⟨⟨U, hU⟩, hex⟩, hy⟩`. Use `push_neg at hex`. Take `⟨V, hV, hx₀V, -⟩` from `exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x₀) trivial`. Rewrite using `[hex y hy]`. Conclude with `Opens.mem_iSup.2 ⟨⟨⟨V, hV⟩, x₀, hx₀V, hx₀⟩, genericPoint_mem V hx₀V⟩`.

Introduce and unpack `⟨⟨U, hU⟩, x, hx, hxη⟩`. Conclude with `chart_smooth K C hft h U hU hx hxη`.
-/
theorem smoothOfRelativeDimension_one : ∀ (K : Type) [Field K] [PerfectField K] (C : Scheme.{0})
    [IsIntegral C] [Algebra K Γ(C, ⊤)], LocallyOfFiniteType (strHom K C) →
    topologicalKrullDim C = 1 →
    (∀ U : C.Opens, IsAffineOpen U → Nonempty U → IsDedekindDomain Γ(C, U)) →
    SmoothOfRelativeDimension 1 (strHom K C) := by
  intro K _ _ C _ _ hft hd h
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : C, x₀ ≠ genericPoint C := by
    by_contra! hall
    haveI : Subsingleton C := ⟨fun a b => (hall a).trans (hall b).symm⟩
    have h0 := topologicalKrullDim_zero_of_discreteTopology C
    rw [hd] at h0
    exact absurd h0 (by decide)
  refine HasRingHomProperty.of_iSup_eq_top (P := @SmoothOfRelativeDimension 1)
    (fun U : {U : C.affineOpens // ∃ x ∈ U.1, x ≠ genericPoint C} => U.1) ?_ ?_
  · rw [eq_top_iff]
    intro y _
    obtain ⟨U, hU, hy, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := y) trivial
    by_cases hex : ∃ x ∈ U, x ≠ genericPoint C
    · exact Opens.mem_iSup.2 ⟨⟨⟨U, hU⟩, hex⟩, hy⟩
    · push_neg at hex
      obtain ⟨V, hV, hx₀V, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x₀) trivial
      rw [hex y hy]
      exact Opens.mem_iSup.2 ⟨⟨⟨V, hV⟩, x₀, hx₀V, hx₀⟩, genericPoint_mem V hx₀V⟩
  · rintro ⟨⟨U, hU⟩, x, hx, hxη⟩
    exact chart_smooth K C hft h U hU hx hxη

end GlobalTheory.CurveSmooth
