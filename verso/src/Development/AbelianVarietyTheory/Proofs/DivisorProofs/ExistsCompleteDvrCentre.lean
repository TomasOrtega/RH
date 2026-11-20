import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.IsE8ThetaStructure
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH
open scoped CategoryTheory.Obj
open Classical

namespace GlobalTheory.DvrCentre

/- English proof (translation)
Introduce `o Ω _ _ _ hA M z`. Establish `hΩ : CharZero Ω` using `hA.char`. Distinguish the cases in `hz : z = genericPoint M.Z`. Substitute `hz` using the available equality. Establish `: CharZero (PowerSeries Ω)` using `charZero_of_injective_ringHom (PowerSeries.C_injective (R := Ω))`.

Establish `hc : IsAdicComplete (IsLocalRing.maximalIdeal (PowerSeries Ω)) (PowerSeries Ω)` using `by first`. Consider the case `infer_instance`. Consider the case `(rw [PowerSeries.maximalIdeal_eq_span_X]; infer_instance)`. Use `⟨PowerSeries Ω, inferInstance, inferInstance, inferInstance, this, spMap (PowerSeries.C (R := Ω)) ≫ M.pt, hc, ?_, IsLocalRing.closedPoint _, ?_⟩` and prove the remaining obligations. Conclude with `M.pt_apply _`.

Conclude with `M.pt_apply _`. Establish `: IsDedekindDomain o` using `hA.ded`. Establish `: IsLocallyNoetherian M.Z`. Use `M.lft` as an intermediate fact. Conclude with `LocallyOfFiniteType.isLocallyNoetherian M.s`.

Set `S` to `M.Z.presheaf.stalk z`. Establish `hS : CharZero S` using `(M.stalkHom z).charZero`. Establish `hgen : M.Z.fromSpecStalk z (⊥ : PrimeSpectrum S) = genericPoint M.Z`. Establish `h1 : genericPoint M.Z ∈ Set.range (M.Z.fromSpecStalk z)`. Rewrite using `[Scheme.range_fromSpecStalk]`.

Conclude with `genericPoint_specializes z`. Take `⟨q, hq⟩` from `h1`. Establish `h2 : (⊥ : PrimeSpectrum S) ⤳ q` using `(PrimeSpectrum.le_iff_specializes _ _).1 bot_le`. Establish `h3` using `h2.map (M.Z.fromSpecStalk z).continuous`. Rewrite `h3` using `[hq]`.

Conclude with `(h3.antisymm (genericPoint_specializes _)).eq`. Establish `hne : (⊥ : Ideal S) ≠ IsLocalRing.maximalIdeal S`. Introduce `e`. Apply `hz` to reduce the goal to its premises. Establish `: (⊥ : PrimeSpectrum S) = IsLocalRing.closedPoint S` using `PrimeSpectrum.ext e`.

Rewrite using `[← hgen, this, Scheme.fromSpecStalk_closedPoint]`. Take `⟨O, _, hO, hO', hO'', φ, h1, h2⟩` from `GlobalTheory.exists_complete_discreteValuationRing_ker_eq (S := S) (⊥ : Ideal S) hne`. Establish `hφ : Function.Injective φ` using `(RingHom.injective_iff_ker_eq_bot φ).2 h1`. Establish `: CharZero O` using `charZero_of_injective_ringHom hφ`. Use `⟨O, inferInstance, hO, hO', this, spMap φ ≫ M.Z.fromSpecStalk z, hO'', ?_, (⊥ : PrimeSpectrum O), ?_⟩` and prove the remaining obligations.

Use `(Scheme.Hom.comp_apply _ _ _).trans (Eq.trans (congrArg (M.Z.fromSpecStalk z) ?_) (Scheme.fromSpecStalk_closedPoint (x := z)))` and prove the remaining obligations. Conclude with `IsLocalRing.comap_closedPoint φ`. Use `(Scheme.Hom.comp_apply _ _ _).trans (Eq.trans (congrArg (M.Z.fromSpecStalk z) ?_) hgen)` and prove the remaining obligations. Conclude with `PrimeSpectrum.ext h1`.
-/
theorem exists_complete_dvr_centre : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω]
    (M : RatModel o Ω) (z : M.Z), ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V)
    (_ : CharZero V) (ξ : Sp V ⟶ M.Z), IsAdicComplete (IsLocalRing.maximalIdeal V) V ∧
    ξ (IsLocalRing.closedPoint V) = z ∧ ∃ w, ξ w = genericPoint M.Z := by
  intro o Ω _ _ _ hA M z
  have hΩ : CharZero Ω := hA.char
  by_cases hz : z = genericPoint M.Z
  · subst hz
    have : CharZero (PowerSeries Ω) := charZero_of_injective_ringHom (PowerSeries.C_injective (R := Ω))
    have hc : IsAdicComplete (IsLocalRing.maximalIdeal (PowerSeries Ω)) (PowerSeries Ω) := by
      first
      | infer_instance
      | (rw [PowerSeries.maximalIdeal_eq_span_X]; infer_instance)
    refine ⟨PowerSeries Ω, inferInstance, inferInstance, inferInstance, this,
      spMap (PowerSeries.C (R := Ω)) ≫ M.pt, hc, ?_, IsLocalRing.closedPoint _, ?_⟩
    · exact M.pt_apply _
    · exact M.pt_apply _
  · have : IsDedekindDomain o := hA.ded
    have : IsLocallyNoetherian M.Z := by
      have := M.lft
      exact LocallyOfFiniteType.isLocallyNoetherian M.s
    let S := M.Z.presheaf.stalk z
    have hS : CharZero S := (M.stalkHom z).charZero

    have hgen : M.Z.fromSpecStalk z (⊥ : PrimeSpectrum S) = genericPoint M.Z := by
      have h1 : genericPoint M.Z ∈ Set.range (M.Z.fromSpecStalk z) := by
        rw [Scheme.range_fromSpecStalk]
        exact genericPoint_specializes z
      obtain ⟨q, hq⟩ := h1
      have h2 : (⊥ : PrimeSpectrum S) ⤳ q := (PrimeSpectrum.le_iff_specializes _ _).1 bot_le
      have h3 := h2.map (M.Z.fromSpecStalk z).continuous
      rw [hq] at h3
      exact (h3.antisymm (genericPoint_specializes _)).eq
    have hne : (⊥ : Ideal S) ≠ IsLocalRing.maximalIdeal S := by
      intro e
      apply hz
      have : (⊥ : PrimeSpectrum S) = IsLocalRing.closedPoint S := PrimeSpectrum.ext e
      rw [← hgen, this, Scheme.fromSpecStalk_closedPoint]
    obtain ⟨O, _, hO, hO', hO'', φ, h1, h2⟩ :=
      GlobalTheory.exists_complete_discreteValuationRing_ker_eq (S := S) (⊥ : Ideal S) hne
    have hφ : Function.Injective φ := (RingHom.injective_iff_ker_eq_bot φ).2 h1
    have : CharZero O := charZero_of_injective_ringHom hφ
    refine ⟨O, inferInstance, hO, hO', this, spMap φ ≫ M.Z.fromSpecStalk z, hO'', ?_, (⊥ : PrimeSpectrum O), ?_⟩
    · refine (Scheme.Hom.comp_apply _ _ _).trans
        (Eq.trans (congrArg (M.Z.fromSpecStalk z) ?_) (Scheme.fromSpecStalk_closedPoint (x := z)))
      exact IsLocalRing.comap_closedPoint φ
    · refine (Scheme.Hom.comp_apply _ _ _).trans (Eq.trans (congrArg (M.Z.fromSpecStalk z) ?_) hgen)
      exact PrimeSpectrum.ext h1

end GlobalTheory.DvrCentre
