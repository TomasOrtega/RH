import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpanDifferentEqLocalGeneratorStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RelIndexMulMeasure
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AbsNormEqFinprod
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUniquePlace
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SubMemDifferentIdeal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc

open ValuativeRel Formalism.MainNotions.S.Loc IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DiffModProd

/- English proof (translation)
Introduce `h`. Use `absNorm_differentIdeal F (𝓞 F)` as an intermediate fact. Rewrite `this` using `[h, map_zero]`. Conclude with `discr_ne_zero F (Int.natAbs_eq_zero.1 this.symm)`.
-/
theorem different_ne_zero (F : Type) [Field F] [NumberField F] : differentIdeal ℤ (𝓞 F) ≠ 0 := by
  intro h
  have := absNorm_differentIdeal F (𝓞 F)
  rw [h, map_zero] at this
  exact discr_ne_zero F (Int.natAbs_eq_zero.1 this.symm)

/- English proof (translation)
Rewrite using `[← D.what₂.card_Tau]`. Conclude with `(Fintype.card_of_bijective ((Function.bijective_iff_existsUnique _).2 (GlobalTheory.RealPlaces.existsUnique_place D))).symm`.
-/
theorem card_infinitePlace (D : D7) : Fintype.card (InfinitePlace D.host.E) = D.R.f := by
  rw [← D.what₂.card_Tau]
  exact (Fintype.card_of_bijective
    ((Function.bijective_iff_existsUnique _).2 (GlobalTheory.RealPlaces.existsUnique_place D))).symm

/- English proof (translation)
Take `⟨h1, -⟩` from `GlobalTheory.cm_discr_sq D.host.F D.host.E D.sp.cm`. Establish `hpos : Module.finrank ℚ D.host.E ≠ 0` using `Module.finrank_pos.ne'`. Rewrite using `[card_infinitePlace, ← GlobalTheory.RealPlaces.finrank_E D]`. Unfold `Host.rdE`. Rewrite using `[one_div, Real.rpow_inv_natCast_pow (abs_nonneg _) hpos]`.

Establish `h3 : |(discr D.host.E : ℝ)| = (discr D.host.F : ℝ) ^ 2` using `by exact_mod_cast h1`. Rewrite using `[h3, sq_abs]`.
-/
theorem rdE_pow (D : D7) :
    D.host.rdE ^ (2 * Fintype.card (InfinitePlace D.host.E)) = |(NumberField.discr D.host.F : ℝ)| ^ 2 := by
  obtain ⟨h1, -⟩ := GlobalTheory.cm_discr_sq D.host.F D.host.E D.sp.cm
  have hpos : Module.finrank ℚ D.host.E ≠ 0 := Module.finrank_pos.ne'
  rw [card_infinitePlace, ← GlobalTheory.RealPlaces.finrank_E D]
  unfold Host.rdE
  rw [one_div, Real.rpow_inv_natCast_pow (abs_nonneg _) hpos]
  have h3 : |(discr D.host.E : ℝ)| = (discr D.host.F : ℝ) ^ 2 := by exact_mod_cast h1
  rw [h3, sq_abs]

/- English proof (translation)
Introduce `D Z`. Set `A : GlobalTheory.HL.Places D.host.F D.host.E D.conjF` to `{ quad := D.sp.cm.deg2, loc := D.s.atP, L := fun p => (Z.M p).L, L_cj := fun p => Z.hcj p }`. Establish `hex : ∀ p : PlF D, ∃ ϖ : 𝒪[(D.s.atP p).Fp], Irreducible ϖ` using `fun p => by haveI := (D.s.atP p).lf`. Conclude with `IsDiscreteValuationRing.exists_irreducible _`. Use `choose ϖ hϖ using hex`.

Establish `hδ : ∀ p, Z.δ p ≠ 0` using `fun p => (Z.agree p).2.1`. Establish `hI` using `different_ne_zero D.host.F`. Use `set g : PlF D → ℝ := fun p => (GlobalTheory.HL.resQ (ϖ p) : ℝ) ^ GlobalTheory.HL.vE (Z.M p).L (ϖ p) (algebraMap _ _ (Z.δ p)) with hg`. Establish `hmod : ∀ p, (Z.M p).modK (algebraMap _ _ (Z.δ p)) = (g p ^ 2)⁻¹`. Introduce `p`.

Rewrite using `[(GlobalTheory.BaseModule.modK_algebraMap (Z.M p) (Z.agree p).1 (ϖ p) (hϖ p)).2 _ (hδ p), hg]`. Simplify using `only`. Rewrite using `[← zpow_natCast, ← zpow_mul, ← zpow_neg]`. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `hcount : ∀ p, GlobalTheory.HL.vE (Z.M p).L (ϖ p) (algebraMap _ _ (Z.δ p)) = ((Associates.mk p.asIdeal).count (Associates.mk (differentIdeal ℤ (𝓞 D.host.F))).factors : ℕ)` using `fun p => GlobalTheory.IdealResProd.vE_eq_count (D.s.atP p) (Z.M p).L (hϖ p) _ hI (hδ p) (GlobalTheory.T.span_different_eq_localGenerator D Z p)`. Establish `hfin : (Function.mulSupport g).Finite`. Use `(Ideal.finite_factors hI).subset fun p hp => ?_` and prove the remaining obligations. Simplify using `only [Set.mem_setOf_eq]`.

Assume the negation of the conclusion as `h`. Apply `hp` to reduce the goal to its premises. Establish `h0 : (Associates.mk p.asIdeal).count (Associates.mk (differentIdeal ℤ (𝓞 D.host.F))).factors = 0`. Assume the negation of the conclusion as `hne`. Conclude with `h ((Associates.count_ne_zero_iff_dvd hI p.irreducible).1 hne)`.

Simplify using `[g, hcount p, h0]`. Establish `hprod : ∏ᶠ p, g p = |(NumberField.discr D.host.F : ℝ)|` using `(GlobalTheory.IdealResProd.discr_and_level A ϖ hϖ).1 (fun p => Units.mk0 (Z.δ p) (hδ p)) (fun p => GlobalTheory.T.span_different_eq_localGenerator D Z p)`. Establish `hsupp : (Function.mulSupport fun p : PlF D => (Z.M p).modK (algebraMap _ _ (Z.δ p))) ⊆ Function.mulSupport g` using `fun p hp h => hp (by show (Z.M p).modK _ = 1; rw [hmod, h]; simp)`. Use `⟨hfin.subset hsupp, ?_⟩` and prove the remaining obligations. Rewrite using `[finprod_congr hmod, finprod_inv_distrib, ← finprod_pow hfin, hprod, rdE_pow]`.
-/
theorem finprod_modK_localGen : ∀ (D : D7) (Z : LocDat D),
    (Function.mulSupport fun p : PlF D => (Z.M p).modK (algebraMap _ _ (Z.δ p))).Finite ∧
    ∏ᶠ p : PlF D, (Z.M p).modK (algebraMap _ _ (Z.δ p)) =
      (D.host.rdE ^ (2 * Fintype.card (InfinitePlace D.host.E)))⁻¹ := by
  intro D Z
  let A : GlobalTheory.HL.Places D.host.F D.host.E D.conjF :=
    { quad := D.sp.cm.deg2, loc := D.s.atP, L := fun p => (Z.M p).L, L_cj := fun p => Z.hcj p }
  have hex : ∀ p : PlF D, ∃ ϖ : 𝒪[(D.s.atP p).Fp], Irreducible ϖ := fun p => by
    haveI := (D.s.atP p).lf
    exact IsDiscreteValuationRing.exists_irreducible _
  choose ϖ hϖ using hex
  have hδ : ∀ p, Z.δ p ≠ 0 := fun p => (Z.agree p).2.1
  have hI := different_ne_zero D.host.F
  set g : PlF D → ℝ := fun p =>
    (GlobalTheory.HL.resQ (ϖ p) : ℝ) ^ GlobalTheory.HL.vE (Z.M p).L (ϖ p) (algebraMap _ _ (Z.δ p)) with hg
  have hmod : ∀ p, (Z.M p).modK (algebraMap _ _ (Z.δ p)) = (g p ^ 2)⁻¹ := by
    intro p
    rw [(GlobalTheory.BaseModule.modK_algebraMap (Z.M p) (Z.agree p).1 (ϖ p) (hϖ p)).2 _ (hδ p), hg]
    dsimp only
    rw [← zpow_natCast, ← zpow_mul, ← zpow_neg]
    congr 1
    push_cast
    ring
  have hcount : ∀ p, GlobalTheory.HL.vE (Z.M p).L (ϖ p) (algebraMap _ _ (Z.δ p)) =
      ((Associates.mk p.asIdeal).count (Associates.mk (differentIdeal ℤ (𝓞 D.host.F))).factors : ℕ) :=
    fun p => GlobalTheory.IdealResProd.vE_eq_count (D.s.atP p) (Z.M p).L (hϖ p) _ hI (hδ p) (GlobalTheory.T.span_different_eq_localGenerator D Z p)
  have hfin : (Function.mulSupport g).Finite := by
    refine (Ideal.finite_factors hI).subset fun p hp => ?_
    simp only [Set.mem_setOf_eq]
    by_contra h
    apply hp
    have h0 : (Associates.mk p.asIdeal).count (Associates.mk (differentIdeal ℤ (𝓞 D.host.F))).factors = 0 := by
      by_contra hne
      exact h ((Associates.count_ne_zero_iff_dvd hI p.irreducible).1 hne)
    simp [g, hcount p, h0]
  have hprod : ∏ᶠ p, g p = |(NumberField.discr D.host.F : ℝ)| :=
    (GlobalTheory.IdealResProd.discr_and_level A ϖ hϖ).1 (fun p => Units.mk0 (Z.δ p) (hδ p))
      (fun p => GlobalTheory.T.span_different_eq_localGenerator D Z p)
  have hsupp : (Function.mulSupport fun p : PlF D => (Z.M p).modK (algebraMap _ _ (Z.δ p))) ⊆
      Function.mulSupport g := fun p hp h => hp (by show (Z.M p).modK _ = 1; rw [hmod, h]; simp)
  refine ⟨hfin.subset hsupp, ?_⟩
  rw [finprod_congr hmod, finprod_inv_distrib, ← finprod_pow hfin, hprod, rdE_pow]

end GlobalTheory.DiffModProd
