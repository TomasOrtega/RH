import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.WeilBound.CoreStatements.HodgeTatePoints.MaBase
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

noncomputable section

namespace PositivityTheory.HtPt.Mb.LFracExt.FracExt

def genCpt {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) : Cpt ξ :=
  ⟨genPt ξ, specializes_rfl⟩

/- English proof (translation)
Take `⟨s, hs⟩` from `h.bij.2 a`. Use `⟨s, ?_⟩` and prove the remaining obligations. Establish `e : X.presheaf.stalkSpecializes (genCpt ξ).2 = 𝟙 _` using `TopCat.Presheaf.stalkSpecializes_refl _ _`. Simplify using `only [genMap, e, Category.id_comp]`. Conclude with `hs`.
-/
theorem mem_regAt_genCpt {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} (h : IsCptGen ξ)
    (a : Ω) : a ∈ regAt ξ (genCpt ξ) := by
  obtain ⟨s, hs⟩ := h.bij.2 a
  refine ⟨s, ?_⟩
  have e : X.presheaf.stalkSpecializes (genCpt ξ).2 = 𝟙 _ := TopCat.Presheaf.stalkSpecializes_refl _ _
  simp only [genMap, e, Category.id_comp]
  exact hs

/- English proof (translation)
Establish `hp : InChart M.ξ x c (genCpt M.ξ)` using `⟨hc, fun _ => mem_regAt_genCpt M.tie.gen _⟩`. Take `⟨u, hu, v, hv, -, e⟩` from `((PositivityTheory.HtPt.Ma.regat_loc o Ω κ x M c _ hp).2 a).1 (mem_regAt_genCpt M.tie.gen a)`. Conclude with `⟨u, hu, v, hv, e⟩`.
-/
theorem exists_frac {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} [Finite κ] {x : κ → Ω}
    (M : PModel o x) {c : κ} (hc : x c ≠ 0) (a : Ω) :
    ∃ u ∈ chRing o x c, ∃ v ∈ chRing o x c, a = u / v := by
  have hp : InChart M.ξ x c (genCpt M.ξ) := ⟨hc, fun _ => mem_regAt_genCpt M.tie.gen _⟩
  obtain ⟨u, hu, v, hv, -, e⟩ := ((PositivityTheory.HtPt.Ma.regat_loc o Ω κ x M c _ hp).2 a).1 (mem_regAt_genCpt M.tie.gen a)
  exact ⟨u, hu, v, hv, e⟩

/- English proof (translation)
Proceed by induction on `ha using Algebra.adjoin_induction with`. Consider the case `mem a h`. Take `⟨j, rfl⟩` from `h`. Rewrite using `[map_div₀]`. Conclude with `Algebra.subset_adjoin ⟨j, rfl⟩`.

Consider the case `algebraMap r`. Rewrite using `[← IsScalarTower.algebraMap_apply]`. Conclude with `Subalgebra.algebraMap_mem _ r`. Consider the case `add a b _ _ ha hb => rw [map_add]`. Conclude with `add_mem ha hb`.

Consider the case `mul a b _ _ ha hb => rw [map_mul]`. Conclude with `mul_mem ha hb`.
-/
theorem algebraMap_mem_chRing {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} (x : κ → Ω)
    (Ω' : Type) [Field Ω'] [Algebra Ω Ω'] [Algebra o Ω'] [IsScalarTower o Ω Ω'] (c : κ) {a : Ω}
    (ha : a ∈ chRing o x c) : algebraMap Ω Ω' a ∈ chRing o (fun k => algebraMap Ω Ω' (x k)) c := by
  induction ha using Algebra.adjoin_induction with
  | mem a h =>
    obtain ⟨j, rfl⟩ := h
    rw [map_div₀]
    exact Algebra.subset_adjoin ⟨j, rfl⟩
  | algebraMap r =>
    rw [← IsScalarTower.algebraMap_apply]
    exact Subalgebra.algebraMap_mem _ r
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb

/- English proof (translation)
Introduce `o _ Ω _ _ κ _ x M Ω' _ _ _ _ _ c hc a`. Use `haveI : IsFractionRing (chRing o x c) Ω := IsFractionRing.of_field _ _ fun z => by`. Take `⟨u, hu, v, hv, e⟩` from `exists_frac M hc z`. Conclude with `⟨⟨u, hu⟩, ⟨v, hv⟩, e⟩`. Establish `halg : IsAlgebraic (chRing o x c) a` using `by haveI : Algebra.IsAlgebraic (chRing o x c) Ω' := (IsFractionRing.comap_isAlgebraic_iff (A := chRing o x c) (K := Ω) (C := Ω')).2 inferInstance`.

Conclude with `Algebra.IsAlgebraic.isAlgebraic a`. Take `⟨y, hy0, hi⟩` from `halg.exists_integral_multiple`. Establish `hy0' : (y : Ω) ≠ 0` using `fun h => hy0 (Subtype.ext h)`. Establish `hv : algebraMap Ω Ω' (y : Ω) ≠ 0` using `(map_ne_zero _).2 hy0'`. Set `φ : chRing o x c →+* chRing o (fun k => algebraMap Ω Ω' (x k)) c` to `((algebraMap Ω Ω').comp (chRing o x c).val.toRingHom).codRestrict _ fun r => algebraMap_mem_chRing x Ω' c r.2`.

Establish `hb` using `IsIntegral.map_of_comp_eq φ (RingHom.id Ω') (by ext r; rfl) hi`. Use `⟨y • a, algebraMap Ω Ω' (y : Ω), hb, algebraMap_mem_chRing x Ω' c y.2, hv, ?_⟩` and prove the remaining obligations. Establish `e : y • a = algebraMap Ω Ω' (y : Ω) * a`. Rewrite using `[Algebra.smul_def]`. Both sides reduce to the same expression.

Rewrite using `[e, mul_div_cancel_left₀ _ hv]`.
-/
theorem exists_integral_div : ∀ {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} [Finite κ]
    {x : κ → Ω} (M : PModel o x) (Ω' : Type) [Field Ω'] [Algebra Ω Ω'] [FiniteDimensional Ω Ω'] [Algebra o Ω']
    [IsScalarTower o Ω Ω'] (c : κ), x c ≠ 0 → ∀ a : Ω', ∃ b v : Ω',
      IsIntegral (chRing o (fun k => algebraMap Ω Ω' (x k)) c) b ∧
        v ∈ chRing o (fun k => algebraMap Ω Ω' (x k)) c ∧ v ≠ 0 ∧ a = b / v := by
  intro o _ Ω _ _ κ _ x M Ω' _ _ _ _ _ c hc a
  haveI : IsFractionRing (chRing o x c) Ω := IsFractionRing.of_field _ _ fun z => by
    obtain ⟨u, hu, v, hv, e⟩ := exists_frac M hc z
    exact ⟨⟨u, hu⟩, ⟨v, hv⟩, e⟩
  have halg : IsAlgebraic (chRing o x c) a := by
    haveI : Algebra.IsAlgebraic (chRing o x c) Ω' :=
      (IsFractionRing.comap_isAlgebraic_iff (A := chRing o x c) (K := Ω) (C := Ω')).2 inferInstance
    exact Algebra.IsAlgebraic.isAlgebraic a
  obtain ⟨y, hy0, hi⟩ := halg.exists_integral_multiple
  have hy0' : (y : Ω) ≠ 0 := fun h => hy0 (Subtype.ext h)
  have hv : algebraMap Ω Ω' (y : Ω) ≠ 0 := (map_ne_zero _).2 hy0'
  let φ : chRing o x c →+* chRing o (fun k => algebraMap Ω Ω' (x k)) c :=
    ((algebraMap Ω Ω').comp (chRing o x c).val.toRingHom).codRestrict _
      fun r => algebraMap_mem_chRing x Ω' c r.2
  have hb := IsIntegral.map_of_comp_eq φ (RingHom.id Ω') (by ext r; rfl) hi
  refine ⟨y • a, algebraMap Ω Ω' (y : Ω), hb, algebraMap_mem_chRing x Ω' c y.2, hv, ?_⟩
  have e : y • a = algebraMap Ω Ω' (y : Ω) * a := by
    rw [Algebra.smul_def]; rfl
  rw [e, mul_div_cancel_left₀ _ hv]

end PositivityTheory.HtPt.Mb.LFracExt.FracExt

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField in

/- English proof (translation)
The claim follows from `@PositivityTheory.HtPt.Mb.LFracExt.FracExt.exists_integral_div`.
-/
theorem PositivityTheory.HtPt.Mb.frac_ext : ∀ {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} [Finite κ] {x : κ → Ω} (M : PModel o x) (Ω' : Type) [Field Ω'] [Algebra Ω Ω'] [FiniteDimensional Ω Ω'] [Algebra o Ω'] [IsScalarTower o Ω Ω'] (c : κ), x c ≠ 0 → ∀ a : Ω', ∃ b v : Ω', IsIntegral (chRing o (fun k => algebraMap Ω Ω' (x k)) c) b ∧ v ∈ chRing o (fun k => algebraMap Ω Ω' (x k)) c ∧ v ≠ 0 ∧ a = b / v :=
  @PositivityTheory.HtPt.Mb.LFracExt.FracExt.exists_integral_div
