import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.StdBases
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BeData
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.StatementB
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.BiextensionHypothesesOfLevelOne
import Formalism.GaussJetBounds.GaussJetProofs.Transfer
import Formalism.SharpRestriction.Divisibility.JetPolynomialLogs.LetterLogIntegrality

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual addC thetaInZ sumE)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

namespace GlobalTheory.KerStd.StdHyp

open Formalism.DworkPowerSeriesWeights (BHyp NoLowBidegree degE degO letterLog mvExp de1 de2 Integral torus lw V2)
open Formalism.MainNotions.DIV.Bridge.LetterLogIntegrality (eV coeff_subst_scale lw_twist cobX_eq cobY_eq jetLog_rename coeff_subst_rename
  hasSubst_XeV letterLog_cc jetLogG_cc)

/- English proof (translation)
Establish `hS : {ζ : ℂ_[l] | ∃ n : ℕ, 0 < n ∧ ¬ l ∣ n ∧ ζ ^ n = 1} = product_zeroth_first_parts.rootsPrimeTo l`. Use extensionality with `ζ`. Simplify using `only [Set.mem_setOf_eq, product_zeroth_first_parts.rootsPrimeTo]`. Use `exists_congr fun n => and_congr_right fun _ => and_congr_left fun _ => ?_` and prove the remaining obligations. Rewrite using `[Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd (Fact.out : l.Prime)]`.

Establish `halg : ∀ x ∈ product_zeroth_first_parts.rootsPrimeTo l, IsAlgebraic ℚ_[l] x`. Introduce and unpack `x ⟨n, hn, -, hx⟩`. Conclude with `(IsIntegral.of_pow hn (by rw [hx]; exact isIntegral_one)).isAlgebraic`. Establish `hsub : (Subfield.closure (product_zeroth_first_parts.rootsPrimeTo l) : Set ℂ_[l]) ⊆ Algebra.adjoin ℚ_[l] (product_zeroth_first_parts.rootsPrimeTo l)`. Introduce `x hx`.

Establish `h1 : Subfield.closure (product_zeroth_first_parts.rootsPrimeTo l) ≤ (IntermediateField.adjoin ℚ_[l] (product_zeroth_first_parts.rootsPrimeTo l)).toSubfield` using `Subfield.closure_le.mpr (IntermediateField.subset_adjoin _ _)`. Establish `h2` using `h1 hx`. Rewrite using `[← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic halg]`. Conclude with `h2`. Introduce `x hx`.

Unfold `MaximalUnramifiedExtension at hx`. Rewrite `hx` using `[hS]`. Unfold `product_zeroth_first_parts.Wfrac`. Establish `hc : x ∈ closure (Subfield.closure (product_zeroth_first_parts.rootsPrimeTo l) : Set ℂ_[l])` using `hx`. Conclude with `closure_mono hsub hc`.
-/
theorem kur_sub_wfrac (l : ℕ) [Fact l.Prime] : ∀ x ∈ MaximalUnramifiedExtension l, x ∈ product_zeroth_first_parts.Wfrac l := by
  have hS : {ζ : ℂ_[l] | ∃ n : ℕ, 0 < n ∧ ¬ l ∣ n ∧ ζ ^ n = 1} = product_zeroth_first_parts.rootsPrimeTo l := by
    ext ζ
    simp only [Set.mem_setOf_eq, product_zeroth_first_parts.rootsPrimeTo]
    refine exists_congr fun n => and_congr_right fun _ => and_congr_left fun _ => ?_
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd (Fact.out : l.Prime)]
  have halg : ∀ x ∈ product_zeroth_first_parts.rootsPrimeTo l, IsAlgebraic ℚ_[l] x := by
    rintro x ⟨n, hn, -, hx⟩
    exact (IsIntegral.of_pow hn (by rw [hx]; exact isIntegral_one)).isAlgebraic
  have hsub : (Subfield.closure (product_zeroth_first_parts.rootsPrimeTo l) : Set ℂ_[l]) ⊆ Algebra.adjoin ℚ_[l] (product_zeroth_first_parts.rootsPrimeTo l) := by
    intro x hx
    have h1 : Subfield.closure (product_zeroth_first_parts.rootsPrimeTo l) ≤
        (IntermediateField.adjoin ℚ_[l] (product_zeroth_first_parts.rootsPrimeTo l)).toSubfield :=
      Subfield.closure_le.mpr (IntermediateField.subset_adjoin _ _)
    have h2 := h1 hx
    rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic halg]
    exact h2
  intro x hx
  unfold MaximalUnramifiedExtension at hx
  rw [hS] at hx
  unfold product_zeroth_first_parts.Wfrac
  have hc : x ∈ closure (Subfield.closure (product_zeroth_first_parts.rootsPrimeTo l) : Set ℂ_[l]) := hx
  exact closure_mono hsub hc

/- English proof (translation)
Introduce `n hn`. Take `⟨h1, h2, h3⟩` from `h n hn`. Establish `e1 : (product_zeroth_first_parts.bideg d n).1 = degE n`. Unfold `product_zeroth_first_parts.bideg degE`. Simplify using `only [Nat.even_iff]`.

Apply the tactic sequence `exact Finsupp.sum_fintype _ _ (by intro s; split_ifs <;> rfl)`. Establish `e2 : (product_zeroth_first_parts.bideg d n).2 = degO n`. Unfold `product_zeroth_first_parts.bideg degO`. Simplify using `only [Nat.even_iff]`. Apply the tactic sequence `exact Finsupp.sum_fintype _ _ (by intro s; split_ifs <;> rfl)`.

Use `⟨by rw [e1]; exact h1.ne', by rw [e2]; exact h2.ne', ?_⟩` and prove the remaining obligations. Introduce `hb`. Apply `h3` to reduce the goal to its premises. Establish `a` using `congrArg Prod.fst hb`. Establish `b` using `congrArg Prod.snd hb`.

Conclude with `⟨e1 ▸ a, e2 ▸ b⟩`.
-/
theorem b3_of_noLowBidegree (l d : ℕ) [Fact l.Prime] [NeZero d] (be : MvPowerSeries (ZMod d) ℂ_[l])
    (h : NoLowBidegree be) : product_zeroth_first_parts.B3 l d be := by
  intro n hn
  obtain ⟨h1, h2, h3⟩ := h n hn
  have e1 : (product_zeroth_first_parts.bideg d n).1 = degE n := by
    unfold product_zeroth_first_parts.bideg degE
    simp only [Nat.even_iff]
    exact Finsupp.sum_fintype _ _ (by intro s; split_ifs <;> rfl)
  have e2 : (product_zeroth_first_parts.bideg d n).2 = degO n := by
    unfold product_zeroth_first_parts.bideg degO
    simp only [Nat.even_iff]
    exact Finsupp.sum_fintype _ _ (by intro s; split_ifs <;> rfl)
  refine ⟨by rw [e1]; exact h1.ne', by rw [e2]; exact h2.ne', ?_⟩
  intro hb
  apply h3
  have a := congrArg Prod.fst hb
  have b := congrArg Prod.snd hb
  exact ⟨e1 ▸ a, e2 ▸ b⟩

/- English proof (translation)
Introduce `u hu m`. Use `haveI : NeZero (l ^ d - 1) := ⟨by`. Establish `h1` using `(Fact.out : l.Prime).one_lt`. Establish `: 1 < l ^ d` using `Nat.one_lt_pow (NeZero.ne d) h1`. Use the proof step `omega⟩`.

Take `⟨i, -, rfl⟩` from `hζ.eq_pow_of_pow_eq_one hu`. Establish `hm` using `congrArg (MvPowerSeries.coeff m) h`. Establish `e : (torus l ζ : ZMod d → MvPowerSeries (ZMod d) ℂ_[l]) = fun s => MvPowerSeries.C (ζ ^ lw l s) * MvPowerSeries.X s` using `rfl`. Rewrite `hm` using `[e, coeff_subst_scale]`. Distinguish the cases in `hc : MvPowerSeries.coeff m be = 0`.

Rewrite using `[hc, zero_mul]`. Establish `hP : (m.prod fun s k => (ζ ^ lw l s) ^ k) = 1` using `mul_right_cancel₀ hc (by rw [one_mul]; exact hm)`. Establish `hT : (m.prod fun s n => product_zeroth_first_parts.twist l d (ζ ^ i) s ^ n) = (m.prod fun s k => (ζ ^ lw l s) ^ k) ^ i`. Unfold `Finsupp.prod`. Rewrite using `[← Finset.prod_pow]`.

Use `Finset.prod_congr rfl fun s _ => ?_` and prove the remaining obligations. Use `show product_zeroth_first_parts.twist l d (ζ ^ i) s ^ m s = ((ζ ^ lw l s) ^ m s) ^ i`. Rewrite using `[← lw_twist]`. Simplify using `only [← zpow_natCast, ← zpow_mul]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hT, hP, one_pow, mul_one]`.
-/
theorem b2_of_subst_torus_eq (l d : ℕ) [Fact l.Prime] [NeZero d] (ζ : ℂ_[l]) (hζ : IsPrimitiveRoot ζ (l ^ d - 1))
    (be : MvPowerSeries (ZMod d) ℂ_[l]) (h : MvPowerSeries.subst (torus l ζ) be = be) : product_zeroth_first_parts.B2 l d be := by
  intro u hu m
  haveI : NeZero (l ^ d - 1) := ⟨by
    have h1 := (Fact.out : l.Prime).one_lt
    have : 1 < l ^ d := Nat.one_lt_pow (NeZero.ne d) h1
    omega⟩
  obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hu
  have hm := congrArg (MvPowerSeries.coeff m) h
  have e : (torus l ζ : ZMod d → MvPowerSeries (ZMod d) ℂ_[l]) =
      fun s => MvPowerSeries.C (ζ ^ lw l s) * MvPowerSeries.X s := rfl
  rw [e, coeff_subst_scale] at hm
  by_cases hc : MvPowerSeries.coeff m be = 0
  · rw [hc, zero_mul]
  have hP : (m.prod fun s k => (ζ ^ lw l s) ^ k) = 1 :=
    mul_right_cancel₀ hc (by rw [one_mul]; exact hm)
  have hT : (m.prod fun s n => product_zeroth_first_parts.twist l d (ζ ^ i) s ^ n) = (m.prod fun s k => (ζ ^ lw l s) ^ k) ^ i := by
    unfold Finsupp.prod
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun s _ => ?_
    show product_zeroth_first_parts.twist l d (ζ ^ i) s ^ m s = ((ζ ^ lw l s) ^ m s) ^ i
    rw [← lw_twist]
    simp only [← zpow_natCast, ← zpow_mul]
    congr 1
    ring
  rw [hT, hP, one_pow, mul_one]

/- English proof (translation)
Establish `hb` using `hasSubst_XeV l d`. Establish `hbs : MvPowerSeries.HasSubst (fun w : ZMod d × Fin 2 => (MvPowerSeries.X ((eV d).symm w) : MvPowerSeries (V2 d) ℂ_[l]))` using `MvPowerSeries.hasSubst_of_constantCoeff_zero (fun w => by simp)`. Establish `hJ : MvPowerSeries.HasSubst (Formalism.BasicNotions.jetLogG l d (β` using `Fin 2)) := MvPowerSeries.hasSubst_of_constantCoeff_zero (jetLogG_cc l d)`. Establish `hD : MvPowerSeries.HasSubst (fun _ : Unit => D)` using `MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => hD0)`. Establish `hLr : MvPowerSeries.HasSubst (fun v : ZMod d × Fin 2 => letterLog (K` using `ℂ_[l]) l ((eV d).symm v)) := MvPowerSeries.hasSubst_of_constantCoeff_zero (fun v => letterLog_cc l d _)`.

Establish `hrn : (fun v : ZMod d × Fin 2 => MvPowerSeries.subst (fun w : ZMod d × Fin 2 => (MvPowerSeries.X ((eV d).symm w) : MvPowerSeries (V2 d) ℂ_[l])) (Formalism.BasicNotions.jetLogG l d (β` using `Fin 2) v)) = fun v => letterLog (K := ℂ_[l]) l ((eV d).symm v) := by`. Use function extensionality and compare the values at `v`. Use `jetLog_rename l d ((eV d).symm v)` as an intermediate fact. Rewrite `this` using `[Equiv.apply_symm_apply]`. Then use the resulting hypothesis. Establish `hexp : product_zeroth_first_parts.expS ℂ_[l] (MvPowerSeries.subst (fun u : Bool × ZMod d => (MvPowerSeries.X (eV d u) : MvPowerSeries (ZMod d × Fin 2) ℂ_[l])) D) = MvPowerSeries.subst (fun u : Bool × ZMod d => (MvPowerSeries.X (eV d u) : MvPowerSeries (ZMod d × Fin 2) ℂ_[l])) (mv …`.

Unfold `product_zeroth_first_parts.expS mvExp PowerSeries.subst`. Rewrite using `[MvPowerSeries.subst_comp_subst_apply hD hb]`. Establish `key : MvPowerSeries.subst (fun w : ZMod d × Fin 2 => (MvPowerSeries.X ((eV d).symm w) : MvPowerSeries (V2 d) ℂ_[l])) (MvPowerSeries.subst (Formalism.BasicNotions.jetLogG l d (β` using `Fin 2)) (product_zeroth_first_parts.expS ℂ_[l] (MvPowerSeries.subst (fun u : Bool × ZMod d => (MvPowerSeries.X (eV d u) : MvPowerSeries (ZMod d × Fin 2) ℂ_[l])) D))) = MvPowerSeries.subst (letterLog (K := ℂ_[l]) l) (mvExp D) := by`. Rewrite using `[hexp, MvPowerSeries.subst_comp_subst_apply hJ hbs, hrn, MvPowerSeries.subst_comp_subst_apply hb hLr]`. Use `congr 1`.

Use function extensionality and compare the values at `u`. Rewrite using `[MvPowerSeries.subst_X hLr, Equiv.symm_apply_apply]`. Use `⟨fun n => ?_, ?_⟩` and prove the remaining obligations. Use `hW (Finsupp.equivMapDomain (eV d).symm n)` as an intermediate fact. Rewrite `this` using `[← key, coeff_subst_rename, Equiv.symm_symm, ← Finsupp.equivMapDomain_trans]`.

Simplify using `using this`. Establish `e` using `congrArg (MvPowerSeries.coeff 0) key`. Rewrite `e` using `[coeff_subst_rename, Finsupp.equivMapDomain_zero, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_zero_eq_constantCoeff_apply]`. Rewrite using `[e, h1]`.
-/
theorem b4_of_coeff_subst_letterLog (l d : ℕ) [Fact l.Prime] [NeZero d] (D : MvPowerSeries (V2 d) ℂ_[l])
    (hD0 : MvPowerSeries.constantCoeff D = 0)
    (hW : ∀ n, MvPowerSeries.coeff n (MvPowerSeries.subst (letterLog (K := ℂ_[l]) l) (mvExp D)) ∈ product_zeroth_first_parts.Wint l)
    (h1 : MvPowerSeries.constantCoeff (MvPowerSeries.subst (letterLog (K := ℂ_[l]) l) (mvExp D)) = 1) :
    product_zeroth_first_parts.OverWOne l (MvPowerSeries.subst (Formalism.BasicNotions.jetLogG l d (β := Fin 2))
      (product_zeroth_first_parts.expS ℂ_[l] (MvPowerSeries.subst (fun u : Bool × ZMod d => (MvPowerSeries.X (eV d u) :
        MvPowerSeries (ZMod d × Fin 2) ℂ_[l])) D))) := by
  have hb := hasSubst_XeV l d
  have hbs : MvPowerSeries.HasSubst (fun w : ZMod d × Fin 2 => (MvPowerSeries.X ((eV d).symm w) :
      MvPowerSeries (V2 d) ℂ_[l])) := MvPowerSeries.hasSubst_of_constantCoeff_zero (fun w => by simp)
  have hJ : MvPowerSeries.HasSubst (Formalism.BasicNotions.jetLogG l d (β := Fin 2)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (jetLogG_cc l d)
  have hD : MvPowerSeries.HasSubst (fun _ : Unit => D) := MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => hD0)
  have hLr : MvPowerSeries.HasSubst (fun v : ZMod d × Fin 2 => letterLog (K := ℂ_[l]) l ((eV d).symm v)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun v => letterLog_cc l d _)
  have hrn : (fun v : ZMod d × Fin 2 => MvPowerSeries.subst (fun w : ZMod d × Fin 2 => (MvPowerSeries.X ((eV d).symm w) :
      MvPowerSeries (V2 d) ℂ_[l])) (Formalism.BasicNotions.jetLogG l d (β := Fin 2) v)) =
      fun v => letterLog (K := ℂ_[l]) l ((eV d).symm v) := by
    funext v
    have := jetLog_rename l d ((eV d).symm v)
    rwa [Equiv.apply_symm_apply] at this
  have hexp : product_zeroth_first_parts.expS ℂ_[l] (MvPowerSeries.subst (fun u : Bool × ZMod d => (MvPowerSeries.X (eV d u) :
        MvPowerSeries (ZMod d × Fin 2) ℂ_[l])) D) =
      MvPowerSeries.subst (fun u : Bool × ZMod d => (MvPowerSeries.X (eV d u) :
        MvPowerSeries (ZMod d × Fin 2) ℂ_[l])) (mvExp D) := by
    unfold product_zeroth_first_parts.expS mvExp PowerSeries.subst
    rw [MvPowerSeries.subst_comp_subst_apply hD hb]
  have key : MvPowerSeries.subst (fun w : ZMod d × Fin 2 => (MvPowerSeries.X ((eV d).symm w) :
      MvPowerSeries (V2 d) ℂ_[l])) (MvPowerSeries.subst (Formalism.BasicNotions.jetLogG l d (β := Fin 2))
        (product_zeroth_first_parts.expS ℂ_[l] (MvPowerSeries.subst (fun u : Bool × ZMod d => (MvPowerSeries.X (eV d u) :
          MvPowerSeries (ZMod d × Fin 2) ℂ_[l])) D))) =
      MvPowerSeries.subst (letterLog (K := ℂ_[l]) l) (mvExp D) := by
    rw [hexp, MvPowerSeries.subst_comp_subst_apply hJ hbs, hrn, MvPowerSeries.subst_comp_subst_apply hb hLr]
    congr 1
    funext u
    rw [MvPowerSeries.subst_X hLr, Equiv.symm_apply_apply]
  refine ⟨fun n => ?_, ?_⟩
  · have := hW (Finsupp.equivMapDomain (eV d).symm n)
    rw [← key, coeff_subst_rename, Equiv.symm_symm, ← Finsupp.equivMapDomain_trans] at this
    simpa using this
  · have e := congrArg (MvPowerSeries.coeff 0) key
    rw [coeff_subst_rename, Finsupp.equivMapDomain_zero, MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply] at e
    rw [e, h1]

end GlobalTheory.KerStd.StdHyp

namespace GlobalTheory.KerStd

open Formalism.DworkPowerSeriesWeights (NoLowBidegree)
open Formalism.DworkPowerSeriesWeights.Transfer (map_defectOne map_defectTwo map_logExp constantCoeff_defectOne constantCoeff_defectTwo cc_of_noLow map_torus cc_torus)

/- English proof (translation)
Introduce `l d _ _ be _ hd2 hde hstd`. Take `⟨σ, F, be0, om, oms, ζ, ⟨hσ, hF, hF1, -, hO, -, hζ⟩, rfl⟩` from `hstd`. Take `⟨-, h2, h3, ⟨h4, h4'⟩, ⟨h5, h5'⟩⟩` from `Formalism.L2.Th1.D.biextension_hypotheses_of_level_one (MaximalUnramifiedExtension l) l d σ hσ hd2 hde F hF be0 hF1 (Fin (d / 2)) om oms hO ζ hζ`. Establish `hbe : beOf l d σ be0 om oms ζ = MvPowerSeries.map (MaximalUnramifiedExtension l).subtype (Formalism.L2.Th1.D.beMean (d` using `d) l σ be0 om oms ζ) := rfl`. Rewrite using `[hbe]`.

Establish `hc` using `cc_of_noLow h3`. Establish `hc' : MvPowerSeries.constantCoeff (MvPowerSeries.map (MaximalUnramifiedExtension l).subtype (Formalism.L2.Th1.D.beMean (d` using `d) l σ be0 om oms ζ)) = 0 := by`. Rewrite using `[MvPowerSeries.constantCoeff_map, hc, map_zero]`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `m`.

Rewrite using `[MvPowerSeries.coeff_map]`. Conclude with `StdHyp.kur_sub_wfrac l _ (SetLike.coe_mem _)`. Establish `ht` using `congrArg (MvPowerSeries.map (MaximalUnramifiedExtension l).subtype) h2`. Rewrite `ht` using `[MvPowerSeries.map_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero (cc_torus l ζ))]`. Simplify using `only [map_torus] at ht`.

Conclude with `StdHyp.b2_of_subst_torus_eq l d _ (hζ.map_of_injective (MaximalUnramifiedExtension l).subtype.injective) _ ht`. Apply `StdHyp.b3_of_noLowBidegree` to reduce the goal to its premises. Introduce `n hn`. Use `h3 n ?_` and prove the remaining obligations. Introduce `h0`.

Rewrite `hn` using `[MvPowerSeries.coeff_map, h0, map_zero]`. Conclude with `hn rfl`. Unfold `product_zeroth_first_parts.B4`. Rewrite using `[Formalism.MainNotions.DIV.Bridge.LetterLogIntegrality.cobX_eq, Formalism.MainNotions.DIV.Bridge.LetterLogIntegrality.cobY_eq]`. Prove the components needed by the constructor for the conclusion.

Use `StdHyp.b4_of_coeff_subst_letterLog l d _ (constantCoeff_defectOne hc') (fun n => ?_) ?_` and prove the remaining obligations. Rewrite using `[← map_defectOne, ← map_logExp _ l (constantCoeff_defectOne hc), MvPowerSeries.coeff_map]`. Conclude with `⟨StdHyp.kur_sub_wfrac l _ (SetLike.coe_mem _), h4 n⟩`. Rewrite using `[← map_defectOne, ← map_logExp _ l (constantCoeff_defectOne hc), MvPowerSeries.constantCoeff_map, h4', map_one]`. Use `StdHyp.b4_of_coeff_subst_letterLog l d _ (constantCoeff_defectTwo hc') (fun n => ?_) ?_` and prove the remaining obligations.

Rewrite using `[← map_defectTwo, ← map_logExp _ l (constantCoeff_defectTwo hc), MvPowerSeries.coeff_map]`. Conclude with `⟨StdHyp.kur_sub_wfrac l _ (SetLike.coe_mem _), h5 n⟩`. Rewrite using `[← map_defectTwo, ← map_logExp _ l (constantCoeff_defectTwo hc), MvPowerSeries.constantCoeff_map, h5', map_one]`.
-/
theorem bHyps_of_beStd : ∀ (l d : ℕ) [Fact l.Prime] [NeZero d] (be : MvPowerSeries (ZMod d) ℂ_[l]), 5 ≤ l → 2 ≤ d →
    Even d → BeStd l d be → product_zeroth_first_parts.B1 l d be ∧ product_zeroth_first_parts.B2 l d be ∧ product_zeroth_first_parts.B3 l d be ∧ product_zeroth_first_parts.B4 l d be := by
  intro l d _ _ be _ hd2 hde hstd
  obtain ⟨σ, F, be0, om, oms, ζ, ⟨hσ, hF, hF1, -, hO, -, hζ⟩, rfl⟩ := hstd
  obtain ⟨-, h2, h3, ⟨h4, h4'⟩, ⟨h5, h5'⟩⟩ := Formalism.L2.Th1.D.biextension_hypotheses_of_level_one (MaximalUnramifiedExtension l) l d σ hσ hd2 hde F hF be0 hF1
    (Fin (d / 2)) om oms hO ζ hζ
  have hbe : beOf l d σ be0 om oms ζ =
      MvPowerSeries.map (MaximalUnramifiedExtension l).subtype (Formalism.L2.Th1.D.beMean (d := d) l σ be0 om oms ζ) := rfl
  rw [hbe]
  have hc := cc_of_noLow h3
  have hc' : MvPowerSeries.constantCoeff
      (MvPowerSeries.map (MaximalUnramifiedExtension l).subtype (Formalism.L2.Th1.D.beMean (d := d) l σ be0 om oms ζ)) = 0 := by
    rw [MvPowerSeries.constantCoeff_map, hc, map_zero]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro m
    rw [MvPowerSeries.coeff_map]
    exact StdHyp.kur_sub_wfrac l _ (SetLike.coe_mem _)
  · have ht := congrArg (MvPowerSeries.map (MaximalUnramifiedExtension l).subtype) h2
    rw [MvPowerSeries.map_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero (cc_torus l ζ))] at ht
    simp only [map_torus] at ht
    exact StdHyp.b2_of_subst_torus_eq l d _ (hζ.map_of_injective (MaximalUnramifiedExtension l).subtype.injective) _ ht
  · apply StdHyp.b3_of_noLowBidegree
    intro n hn
    refine h3 n ?_
    intro h0
    rw [MvPowerSeries.coeff_map, h0, map_zero] at hn
    exact hn rfl
  · unfold product_zeroth_first_parts.B4
    rw [Formalism.MainNotions.DIV.Bridge.LetterLogIntegrality.cobX_eq, Formalism.MainNotions.DIV.Bridge.LetterLogIntegrality.cobY_eq]
    constructor
    · refine StdHyp.b4_of_coeff_subst_letterLog l d _ (constantCoeff_defectOne hc') (fun n => ?_) ?_
      · rw [← map_defectOne, ← map_logExp _ l (constantCoeff_defectOne hc), MvPowerSeries.coeff_map]
        exact ⟨StdHyp.kur_sub_wfrac l _ (SetLike.coe_mem _), h4 n⟩
      · rw [← map_defectOne, ← map_logExp _ l (constantCoeff_defectOne hc), MvPowerSeries.constantCoeff_map, h4', map_one]
    · refine StdHyp.b4_of_coeff_subst_letterLog l d _ (constantCoeff_defectTwo hc') (fun n => ?_) ?_
      · rw [← map_defectTwo, ← map_logExp _ l (constantCoeff_defectTwo hc), MvPowerSeries.coeff_map]
        exact ⟨StdHyp.kur_sub_wfrac l _ (SetLike.coe_mem _), h5 n⟩
      · rw [← map_defectTwo, ← map_logExp _ l (constantCoeff_defectTwo hc), MvPowerSeries.constantCoeff_map, h5', map_one]

end GlobalTheory.KerStd
