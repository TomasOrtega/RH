import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarCohPfD
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.EmbeddingIntegerAlgebraMap
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocModel
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocalDiscriminantIsUnit
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsDenominatorSecond

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching IsDedekindDomain ValuativeRel

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open CohCut

namespace CohIntPf

variable {D : Formalism.BasicNotions.D7}

/- English proof (translation)
Take `⟨a, b, hb, rfl⟩` from `IsFractionRing.div_surjective (A := 𝓞 D.host.E) x`. Establish `hb0 : (b : D.host.E) ≠ 0`. Establish `: (b : 𝓞 D.host.E) ≠ 0` using `nonZeroDivisors.ne_zero hb`. Conclude with `this` after adjusting the coercions. Establish `hbi : IsIntegral ℤ (b : D.host.E)` using `(b : 𝓞 D.host.E).2`.

Establish `hbc : IsIntegral ℤ (D.conjF (b : D.host.E))` using `hbi.map (D.conjF.toRingHom.toIntAlgHom)`. Take `⟨t0, ht0⟩` from `Formalism.L2.SG.Pf.LocalDenominators.conjF_fix ((b : D.host.E) * D.conjF (b : D.host.E)) (by rw [map_mul, Formalism.L2.SG.Pf.LocalDenominators.conjF_invol, mul_comm])`. Establish `ht0i : IsIntegral ℤ t0` using `(isIntegral_algebraMap_iff (algebraMap D.host.F D.host.E).injective).1 (by rw [ht0]; exact hbi.mul hbc)`. Use `⟨⟨t0, ht0i⟩, ?_, ?_⟩` and prove the remaining obligations. Introduce `h`.

Establish `h1 : t0 = 0` using `congrArg Subtype.val h`. Rewrite `ht0` using `[h1, map_zero]`. Establish `hc0 : D.conjF (b : D.host.E) ≠ 0`. Introduce `hc`. Apply `hb0` to reduce the goal to its premises.

Use `congrArg D.conjF hc` as an intermediate fact. Rewrite `this` using `[Formalism.L2.SG.Pf.LocalDenominators.conjF_invol, map_zero]`. Then use the resulting hypothesis. Conclude with `mul_ne_zero hb0 hc0 ht0.symm`. Use `show IsIntegral ℤ (algebraMap D.host.F D.host.E t0 * (algebraMap (𝓞 D.host.E) D.host.E a / algebraMap (𝓞 D.host.E) D.host.E (b : 𝓞 D.host.E)))`. Establish `e : algebraMap D.host.F D.host.E t0 * (algebraMap (𝓞 D.host.E) D.host.E a / algebraMap (𝓞 D.host.E) D.host.E (b : 𝓞 D.host.E)) = D.conjF (b : D.host.E) * (a : D.host.E)`.

Rewrite using `[ht0]`. Establish `hb0' : algebraMap (𝓞 D.host.E) D.host.E (b : 𝓞 D.host.E) ≠ 0` using `hb0`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e]`. Conclude with `hbc.mul (a : 𝓞 D.host.E).2`.
-/
theorem denF' (x : D.host.E) :
    ∃ d : 𝓞 D.host.F, d ≠ 0 ∧ IsIntegral ℤ (algebraMap D.host.F D.host.E (d : D.host.F) * x) := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 D.host.E) x
  have hb0 : (b : D.host.E) ≠ 0 := by
    have : (b : 𝓞 D.host.E) ≠ 0 := nonZeroDivisors.ne_zero hb
    exact_mod_cast this
  have hbi : IsIntegral ℤ (b : D.host.E) := (b : 𝓞 D.host.E).2
  have hbc : IsIntegral ℤ (D.conjF (b : D.host.E)) := hbi.map (D.conjF.toRingHom.toIntAlgHom)
  obtain ⟨t0, ht0⟩ := Formalism.L2.SG.Pf.LocalDenominators.conjF_fix ((b : D.host.E) * D.conjF (b : D.host.E))
    (by rw [map_mul, Formalism.L2.SG.Pf.LocalDenominators.conjF_invol, mul_comm])
  have ht0i : IsIntegral ℤ t0 := (isIntegral_algebraMap_iff (algebraMap D.host.F D.host.E).injective).1
    (by rw [ht0]; exact hbi.mul hbc)
  refine ⟨⟨t0, ht0i⟩, ?_, ?_⟩
  · intro h
    have h1 : t0 = 0 := congrArg Subtype.val h
    rw [h1, map_zero] at ht0
    have hc0 : D.conjF (b : D.host.E) ≠ 0 := by
      intro hc; apply hb0
      have := congrArg D.conjF hc
      rwa [Formalism.L2.SG.Pf.LocalDenominators.conjF_invol, map_zero] at this
    exact mul_ne_zero hb0 hc0 ht0.symm
  · show IsIntegral ℤ (algebraMap D.host.F D.host.E t0 *
      (algebraMap (𝓞 D.host.E) D.host.E a / algebraMap (𝓞 D.host.E) D.host.E (b : 𝓞 D.host.E)))
    have e : algebraMap D.host.F D.host.E t0 *
        (algebraMap (𝓞 D.host.E) D.host.E a / algebraMap (𝓞 D.host.E) D.host.E (b : 𝓞 D.host.E)) =
        D.conjF (b : D.host.E) * (a : D.host.E) := by
      rw [ht0]
      have hb0' : algebraMap (𝓞 D.host.E) D.host.E (b : 𝓞 D.host.E) ≠ 0 := hb0
      field_simp
    rw [e]; exact hbc.mul (a : 𝓞 D.host.E).2

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_alg (s : 𝓞 D.host.F) :
    ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) s : 𝓞 D.host.E) : D.host.E) = algebraMap D.host.F D.host.E (s : D.host.F) :=
  rfl

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.ExistsBaseFieldIntegerDenominator.exists_den hΛ x`.
-/
theorem exists_den {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hΛ : Submodule.IsLattice D.host.E Λ) (x : (VS D).V) :
    ∃ d : 𝓞 D.host.F, d ≠ 0 ∧ algebraMap (𝓞 D.host.F) (𝓞 D.host.E) d • x ∈ Λ :=
  _root_.UpperTheory.Reformulated.B.ExistsBaseFieldIntegerDenominator.exists_den hΛ x

variable (Zd : LocDat D)

/- English proof (translation)
Take `⟨d, hd, hdx⟩` from `exists_den hΛ x`. Establish `hI : Ideal.span {d} ≠ (0 : Ideal (𝓞 D.host.F))`. Rewrite using `[Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]`. Conclude with `hd`. Use `(Ideal.finite_factors hI).subset fun p hp => ?_` and prove the remaining obligations.

Simplify using `only [Set.mem_ofPred_eq] at hp ⊢`. Rewrite using `[Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]`. Assume the negation of the conclusion as `hnd`. Apply `hp` to reduce the goal to its premises. Use `p.isPrime` as an intermediate fact.

Rewrite using `[Formalism.L2.SG.Pf.LocalDenominators.baseChangeAt_mem_localLattice_iff Zd p hΛ]`. Conclude with `(Formalism.HermitianLattices.Ext.L3.LocalSpans.mem_locF p.asIdeal Λ x).2 ⟨d, hnd, hdx⟩`.
-/
theorem bcP_mem_cof {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hΛ : Submodule.IsLattice D.host.E Λ) (x : (VS D).V) :
    {p : PlF D | baseChange₂ D p x ∉ lattice₂ D Zd.M p Λ}.Finite := by
  obtain ⟨d, hd, hdx⟩ := exists_den hΛ x
  have hI : Ideal.span {d} ≠ (0 : Ideal (𝓞 D.host.F)) := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hd
  refine (Ideal.finite_factors hI).subset fun p hp => ?_
  simp only [Set.mem_ofPred_eq] at hp ⊢
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  by_contra hnd
  apply hp
  have := p.isPrime
  rw [Formalism.L2.SG.Pf.LocalDenominators.baseChangeAt_mem_localLattice_iff Zd p hΛ]
  exact (Formalism.HermitianLattices.Ext.L3.LocalSpans.mem_locF p.asIdeal Λ x).2 ⟨d, hnd, hdx⟩

/- English proof (translation)
Establish `hs' : (D.s.atP p).split = none`. Establish `hA` using `(Zd.agree p).2.2.2.2.2`. Rewrite `hA` using `[hs]`. Consider the cases of `h2 : (D.s.atP p).split with`. Consider the case `none => rfl`.

Consider the case `some sg`. Rewrite `hA` using `[h2]`. Conclude with `(hA : False).elim`. Use `Subring.mul_mem _ ?_ ?_` and prove the remaining obligations. Unfold `TermLoc.sgnP'`.

Rewrite using `[hs']`. Conclude with `Subring.pow_mem _ (Subring.neg_mem _ (Subring.one_mem _)) _`. Rewrite using `[Formalism.L2.SG.Pf.BBTie.bt_frFac_eq Zd p b] set w : (D.s.atP p).Ep := algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Zd.δ p)⁻¹ * (D.s.atP p).ιE ((uP p : D.host.E)⁻¹) with hw`. Establish `hwO : w ∈ (D.s.atP p).O` using `Subring.mul_mem _ (Formalism.L2.SG.Pf.LocalDenominators.alg_mem_O (D.s.atP p) hδ.2) hu.2`. Establish `hinv : (((Formalism.L2.SG.Pf.BBTie.bt_T_unit Zd p).unit⁻¹ : (D.s.atP p).Epˣ) : (D.s.atP p).Ep) = w`.

Apply `Units.inv_eq_of_mul_eq_one_right` to reduce the goal to its premises. Rewrite using `[IsUnit.unit_spec]`. Use `show algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Zd.δ p) * (D.s.atP p).ιE (uP p : D.host.E) * w = 1`. Rewrite using `[hw]`. Establish `hδ0 : Zd.δ p ≠ 0` using `(Zd.agree p).2.1`.

Establish `hu0` using `Formalism.L2.SG.Pf.BBTie.uP_ne (D := D) p`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Units.val_pow_eq_pow_val, hinv]`. Conclude with `Subring.pow_mem _ hwO _`.
-/
theorem scal_mem {p : PlF D} (hs : (Zd.M p).split = none)
    (hδ : Zd.δ p ∈ 𝒪[(D.s.atP p).Fp] ∧ (Zd.δ p)⁻¹ ∈ 𝒪[(D.s.atP p).Fp])
    (hu : (D.s.atP p).ιE (uP p : D.host.E) ∈ (D.s.atP p).O ∧ (D.s.atP p).ιE ((uP p : D.host.E)⁻¹) ∈ (D.s.atP p).O)
    (b : Fin (D.R.rS + 1)) : TermLoc.sgnP' D p b * frFac Zd.δ p b ∈ (D.s.atP p).O := by
  have hs' : (D.s.atP p).split = none := by
    have hA := (Zd.agree p).2.2.2.2.2
    rw [hs] at hA
    cases h2 : (D.s.atP p).split with
    | none => rfl
    | some sg =>
      rw [h2] at hA
      exact (hA : False).elim
  refine Subring.mul_mem _ ?_ ?_
  · unfold TermLoc.sgnP'
    rw [hs']
    exact Subring.pow_mem _ (Subring.neg_mem _ (Subring.one_mem _)) _
  · rw [Formalism.L2.SG.Pf.BBTie.bt_frFac_eq Zd p b]
    set w : (D.s.atP p).Ep := algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Zd.δ p)⁻¹ *
      (D.s.atP p).ιE ((uP p : D.host.E)⁻¹) with hw
    have hwO : w ∈ (D.s.atP p).O :=
      Subring.mul_mem _ (Formalism.L2.SG.Pf.LocalDenominators.alg_mem_O (D.s.atP p) hδ.2) hu.2
    have hinv : (((Formalism.L2.SG.Pf.BBTie.bt_T_unit Zd p).unit⁻¹ : (D.s.atP p).Epˣ) : (D.s.atP p).Ep) = w := by
      apply Units.inv_eq_of_mul_eq_one_right
      rw [IsUnit.unit_spec]
      show algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Zd.δ p) * (D.s.atP p).ιE (uP p : D.host.E) * w = 1
      rw [hw]
      have hδ0 : Zd.δ p ≠ 0 := (Zd.agree p).2.1
      have hu0 := Formalism.L2.SG.Pf.BBTie.uP_ne (D := D) p
      calc algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Zd.δ p) * (D.s.atP p).ιE (uP p : D.host.E) *
            (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Zd.δ p)⁻¹ * (D.s.atP p).ιE ((uP p : D.host.E)⁻¹))
          = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Zd.δ p * (Zd.δ p)⁻¹) *
            (D.s.atP p).ιE ((uP p : D.host.E) * (uP p : D.host.E)⁻¹) := by rw [map_mul, map_mul]; ring
        _ = 1 := by rw [mul_inv_cancel₀ hδ0, mul_inv_cancel₀ hu0, map_one, map_one, mul_one]
    rw [Units.val_pow_eq_pow_val, hinv]
    exact Subring.pow_mem _ hwO _

end CohIntPf

open CohIntPf

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

/- English proof (translation)
Introduce `hP γ Z F'₂ φ' _`. Establish `hΛ : Submodule.IsLattice D.host.E γ.lam` using `(hP.2.1.1 γ.lam γ.mem).1.1`. Establish `hgood` using `Formalism.L2.SG.Pf.LocModel.good_cofinite Zd.δ Zd.M Zd.agree ∅`. Rewrite `hgood` using `[Filter.eventually_cofinite]`. Use `(hgood.union (Set.finite_iUnion fun b => bcP_mem_cof Zd hΛ (frame F'₂ b))).subset ?_` and prove the remaining obligations.

Introduce `p hp`. Assume the negation of the conclusion as `hn`. Simplify using `only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_iUnion, not_or, not_exists, not_not] at hn`. Take `⟨hg, hb⟩` from `hn`. Apply `hp` to reduce the goal to its premises.

Introduce `b`. Conclude with `Formalism.L2.SG.Pf.LocalDenominators.smul_mem_localLattice Zd p (scal_mem Zd hg.1 hg.2.1 hg.2.2.1 b) (hb b)`.
-/
theorem cohInt_holds : CohInt Zd u u' F0 what₂ := by
  intro hP γ Z F'₂ φ' _
  have hΛ : Submodule.IsLattice D.host.E γ.lam := (hP.2.1.1 γ.lam γ.mem).1.1
  have hgood := Formalism.L2.SG.Pf.LocModel.good_cofinite Zd.δ Zd.M Zd.agree ∅
  rw [Filter.eventually_cofinite] at hgood
  refine (hgood.union (Set.finite_iUnion fun b => bcP_mem_cof Zd hΛ (frame F'₂ b))).subset ?_
  intro p hp
  by_contra hn
  simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_iUnion, not_or, not_exists, not_not] at hn
  obtain ⟨hg, hb⟩ := hn
  apply hp
  intro b
  exact Formalism.L2.SG.Pf.LocalDenominators.smul_mem_localLattice Zd p (scal_mem Zd hg.1 hg.2.1 hg.2.2.1 b) (hb b)

/- English proof (translation)
The claim follows from `star_coherence_of_four Zd (cohInt_holds Zd) hDG hLp hGood`.
-/
theorem star_coherence_of_three (hDG : CohDG Zd u u' F0 what₂) (hLp : CohLp Zd u u' F0 what₂) (hGood : CohGood Zd u u' F0 what₂) :
    CtxP u u' F0 what₂ → StarCoh Zd u u' F0 what₂ :=
  star_coherence_of_four Zd (cohInt_holds Zd) hDG hLp hGood

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
