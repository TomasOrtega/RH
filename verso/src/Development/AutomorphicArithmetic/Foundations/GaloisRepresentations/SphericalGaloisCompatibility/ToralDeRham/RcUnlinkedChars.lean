import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LanglandsClassificationSupercuspidalSupportMulti
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportUniqueGL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodToralOfIsSubquotientProdIrr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BernsteinZelevinskyFinitenessHolds
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneCharpolyTwistSpecial
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLanglandsExtensionPreservesCuspidal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Mono0OfLpDimEqOne
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalGaloisCompatibility.Chl

namespace GalTw
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RoadU.UnlinkedChars

/- English proof (translation)
Introduce `hI Ω _ E _ _ _ _ w A h a ha rc H x n ξ hξ hs hu`. Use `haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective`. Take `⟨𝔪, hm⟩` from `hI.exh (w.adicCompletion E) x`. Establish `hs' : HasSupport x.rep (msupp 𝔪)` using `GlobalTheory.LocGL.hasSupport_msupp_of_isL hI.zel _ 𝔪 x hm`. Establish `he : chars ξ hξ = msupp 𝔪` using `GlobalTheory.LocGL.SupportUnique.hasSupport_unique GlobalTheory.RecT.geometricLemma_holds GlobalTheory.bernsteinZelevinskyFiniteness_holds hI.zel _ x _ _ hs hs'`.

Establish `hL` using `H.langlands 𝔪.toList x (by rw [Multiset.coe_toList]; exact hm)`. Establish `hmem : ∀ Δ ∈ 𝔪, ∀ i : Fin Δ.len, Δ.term i ∈ chars ξ hξ` using `fun Δ hΔ i => by`. Rewrite using `[he, msupp]`. Conclude with `Multiset.mem_bind.2 ⟨Δ, hΔ, Multiset.mem_map.2 ⟨i, Finset.mem_univ_val _, rfl⟩⟩`. Establish `hlen : ∀ Δ ∈ 𝔪, Δ.len = 1`.

Introduce `Δ hΔ`. Assume the negation of the conclusion as `hne`. Establish `h2 : 1 < Δ.len` using `lt_of_le_of_ne Δ.len_pos (Ne.symm hne)`. Use `hu _ (hmem Δ hΔ ⟨1, h2⟩) _ (hmem Δ hΔ ⟨0, Δ.len_pos⟩) ?_` and prove the remaining obligations. Simplify using `only [Segment.term, IrrGL.nu_nu]`.

Evaluate the numerical expressions. Establish `hms : ∀ Δ ∈ 𝔪, Δ.ms = {Δ.first}`. Introduce `Δ hΔ`. Establish `e : Δ = Segment.single Δ.first Δ.isCusp_first` using `Segment.ext_first rfl (by rw [hlen Δ hΔ]; rfl)`. Rewrite using `[e, Segment.ms_single]`.

Both sides reduce to the same expression. Establish `hsupp : msupp 𝔪 = 𝔪.map Segment.first`. Rewrite using `[msupp, ← Multiset.bind_singleton]`. Conclude with `Multiset.bind_congr hms`. Establish `hchar : ∀ y ∈ chars ξ hξ, ∃ j, y = IrrGL.ofChar (ξ j) (hξ j)` using `fun y hy => by`.

Take `⟨j, -, rfl⟩` from `Multiset.mem_map.1 hy`. Conclude with `⟨j, rfl⟩`. Establish `hfirst : ∀ Δ ∈ 𝔪, ∃ j, Δ.first = IrrGL.ofChar (ξ j) (hξ j)` using `fun Δ hΔ => hchar _ (by rw [he, hsupp]; exact Multiset.mem_map_of_mem _ hΔ)`. Establish `hsum : rc x = sumList (𝔪.toList.map fun Δ => rc Δ.first)`. Rewrite using `[hL, segSum]`.

Use `congr 1`. Apply `List.map_congr_left` to reduce the goal to its premises. Introduce `Δ hΔ`. Rewrite using `[hlen Δ (Multiset.mem_toList.1 hΔ)]`. Simplify using `only [Nat.cast_one, sub_self, zero_div]`.

Conclude with `(GlobalTheory.WeilDeligne.charPol_lpTw_lpChar_lpSp E Ω A w h _).1`. Establish `hpol1 : ∀ j (g : Weil h), (rc (IrrGL.ofChar (ξ j) (hξ j))).charPol g = X - C ((ξ j (a g) : ℂˣ) : ℂ)`. Introduce `j g`. Rewrite using `[H.one, WD.lpOfChar, WD.charPol_mk, WDRep.ofChars_ρ, charpoly_diagEnd]`. Simplify using the standard rewrite rules.

Use `⟨?_, fun g => ?_⟩` and prove the remaining obligations. Rewrite using `[hsum]`. Establish `key : ∀ L : List (Segment (w.adicCompletion E)), (∀ Δ ∈ L, Δ ∈ 𝔪) → (sumList (L.map fun Δ => rc Δ.first)).mono0`. Introduce `L`. Proceed by induction on `L with`.

Consider the case `nil`. Introduce `_`. Use `show (WD.lpZero h).mono0`. Conclude with `(WD.monodromyZero_ofWeilDeligneRepClass_iff _).2 rfl`. Consider the case `cons Δ L ih`.

Introduce `hL'`. Take `⟨j, hj⟩` from `hfirst Δ (hL' Δ List.mem_cons_self)`. Use `show (WD.lpSum _ _).mono0`. Use `(WD.monomial_sum_iff _ _).2 ⟨?_, ih fun Δ' h' => hL' Δ' (List.mem_cons_of_mem _ h')⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(rc Δ.first).mono0`.

Rewrite using `[hj]`. Conclude with `WD.mono0_of_lpDim_eq_one (by rw [H.dim]; rfl)`. Conclude with `key _ fun Δ hΔ => Multiset.mem_toList.1 hΔ`. Rewrite using `[hsum, GlobalTheory.LocLanglands.CuspExt.charPol_sumList, List.map_map]`. Establish `r1 : (∏ j, (X - C ((ξ j (a g) : ℂˣ) : ℂ))) = ((chars ξ hξ).map fun y => (rc y).charPol g).prod`.

Rewrite using `[chars, Multiset.map_map, Finset.prod_eq_multiset_prod]`. Conclude with `congrArg Multiset.prod (Multiset.map_congr rfl fun j _ => (hpol1 j g).symm)`. Rewrite using `[r1, he, hsupp, Multiset.map_map, ← Multiset.prod_coe, ← Multiset.map_coe, Multiset.coe_toList]`. Both sides reduce to the same expression.
-/
theorem rc_unlinked_chars : UpperTheory.Gal.ToralGalois.Inq → ∀ (Ω : Type) [Field Ω] (E : Type) [Field E] [NumberField E] [Algebra E Ω] [IsAlgClosure E Ω] (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w), ∀ (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a) (rc : IrrGL (w.adicCompletion E) → WD h), UpperTheory.Zero.LLC.LawsT a ha rc → ∀ (x : IrrGL (w.adicCompletion E)) (n : ℕ), ∀ (ξ : Fin n → ((w.adicCompletion E)ˣ →* ℂˣ)) (hξ : ∀ j, IsSmoothChar (ξ j)), HasSupport x.rep (chars ξ hξ) → Unlinked (chars ξ hξ) → (rc x).mono0 ∧ ∀ g : Weil h, (rc x).charPol g = ∏ j, (X - C ((ξ j (a g) : ℂˣ) : ℂ)) := by
  intro hI Ω _ E _ _ _ _ w A h a ha rc H x n ξ hξ hs hu
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  obtain ⟨𝔪, hm⟩ := hI.exh (w.adicCompletion E) x
  have hs' : HasSupport x.rep (msupp 𝔪) := GlobalTheory.LocGL.hasSupport_msupp_of_isL hI.zel _ 𝔪 x hm
  have he : chars ξ hξ = msupp 𝔪 :=
    GlobalTheory.LocGL.SupportUnique.hasSupport_unique GlobalTheory.RecT.geometricLemma_holds GlobalTheory.bernsteinZelevinskyFiniteness_holds
      hI.zel _ x _ _ hs hs'
  have hL := H.langlands 𝔪.toList x (by rw [Multiset.coe_toList]; exact hm)
  have hmem : ∀ Δ ∈ 𝔪, ∀ i : Fin Δ.len, Δ.term i ∈ chars ξ hξ := fun Δ hΔ i => by
    rw [he, msupp]
    exact Multiset.mem_bind.2 ⟨Δ, hΔ, Multiset.mem_map.2 ⟨i, Finset.mem_univ_val _, rfl⟩⟩

  have hlen : ∀ Δ ∈ 𝔪, Δ.len = 1 := by
    intro Δ hΔ
    by_contra hne
    have h2 : 1 < Δ.len := lt_of_le_of_ne Δ.len_pos (Ne.symm hne)
    refine hu _ (hmem Δ hΔ ⟨1, h2⟩) _ (hmem Δ hΔ ⟨0, Δ.len_pos⟩) ?_
    simp only [Segment.term, IrrGL.nu_nu]
    norm_num
  have hms : ∀ Δ ∈ 𝔪, Δ.ms = {Δ.first} := by
    intro Δ hΔ
    have e : Δ = Segment.single Δ.first Δ.isCusp_first := Segment.ext_first rfl (by rw [hlen Δ hΔ]; rfl)
    rw [e, Segment.ms_single]
    rfl
  have hsupp : msupp 𝔪 = 𝔪.map Segment.first := by
    rw [msupp, ← Multiset.bind_singleton]
    exact Multiset.bind_congr hms
  have hchar : ∀ y ∈ chars ξ hξ, ∃ j, y = IrrGL.ofChar (ξ j) (hξ j) := fun y hy => by
    obtain ⟨j, -, rfl⟩ := Multiset.mem_map.1 hy
    exact ⟨j, rfl⟩
  have hfirst : ∀ Δ ∈ 𝔪, ∃ j, Δ.first = IrrGL.ofChar (ξ j) (hξ j) := fun Δ hΔ =>
    hchar _ (by rw [he, hsupp]; exact Multiset.mem_map_of_mem _ hΔ)
  have hsum : rc x = sumList (𝔪.toList.map fun Δ => rc Δ.first) := by
    rw [hL, segSum]
    congr 1
    apply List.map_congr_left
    intro Δ hΔ
    rw [hlen Δ (Multiset.mem_toList.1 hΔ)]
    simp only [Nat.cast_one, sub_self, zero_div]
    exact (GlobalTheory.WeilDeligne.charPol_lpTw_lpChar_lpSp E Ω A w h _).1
  have hpol1 : ∀ j (g : Weil h), (rc (IrrGL.ofChar (ξ j) (hξ j))).charPol g = X - C ((ξ j (a g) : ℂˣ) : ℂ) := by
    intro j g
    rw [H.one, WD.lpOfChar, WD.charPol_mk, WDRep.ofChars_ρ, charpoly_diagEnd]
    simp
  refine ⟨?_, fun g => ?_⟩
  · rw [hsum]
    have key : ∀ L : List (Segment (w.adicCompletion E)), (∀ Δ ∈ L, Δ ∈ 𝔪) →
        (sumList (L.map fun Δ => rc Δ.first)).mono0 := by
      intro L
      induction L with
      | nil =>
        intro _
        show (WD.lpZero h).mono0
        exact (WD.monodromyZero_ofWeilDeligneRepClass_iff _).2 rfl
      | cons Δ L ih =>
        intro hL'
        obtain ⟨j, hj⟩ := hfirst Δ (hL' Δ List.mem_cons_self)
        show (WD.lpSum _ _).mono0
        refine (WD.monomial_sum_iff _ _).2 ⟨?_, ih fun Δ' h' => hL' Δ' (List.mem_cons_of_mem _ h')⟩
        change (rc Δ.first).mono0
        rw [hj]
        exact WD.mono0_of_lpDim_eq_one (by rw [H.dim]; rfl)
    exact key _ fun Δ hΔ => Multiset.mem_toList.1 hΔ
  · rw [hsum, GlobalTheory.LocLanglands.CuspExt.charPol_sumList, List.map_map]
    have r1 : (∏ j, (X - C ((ξ j (a g) : ℂˣ) : ℂ))) = ((chars ξ hξ).map fun y => (rc y).charPol g).prod := by
      rw [chars, Multiset.map_map, Finset.prod_eq_multiset_prod]
      exact congrArg Multiset.prod (Multiset.map_congr rfl fun j _ => (hpol1 j g).symm)
    rw [r1, he, hsupp, Multiset.map_map, ← Multiset.prod_coe, ← Multiset.map_coe, Multiset.coe_toList]
    rfl

end GlobalTheory.RoadU.UnlinkedChars

section

end
