import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.SphericalTwists.UnramifiedTwists.SatFrobT
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicFormHyp

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.Zero.LLC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.V.Z.Desc.W.SatakeFrobeniusEigenvalues
open Polynomial GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
open scoped commutatorElement
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
/- English proof (translation)
Take `⟨a, ha, H⟩` from `H`. Use `haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective`. Establish `hL` using `GlobalTheory.T.spherical_satake_eq_langlandsQuotient_unramified Pr.exh Pr.multi Pr.cos Pr.zel GlobalTheory.RecT.geometricLemma_holds Pr.bz (w.adicCompletion E) x α hα`. Rewrite `hL` using `[Fin.univ_val_map]`. Rewrite using `[H.langlands _ x hL, segSum, List.map_ofFn, ← SatakeLaw.sumList_ofFn_diag]`.

Use `congr 1`. Use `List.ofFn_inj.mpr (funext fun i => ?_)` and prove the remaining obligations. Simplify using `only [Function.comp_apply, Segment.single, Segment.first_ofFirst, Segment.len_ofFirst, Nat.cast_one, sub_self, zero_div, WD.lpTw_zero, Test.lpChar_lpSp_one, H.one]`. Conclude with `Test.lpOfChar_unrChar ha (α i) _`.
-/
private theorem rec_diag {rc : IrrGL (w.adicCompletion E) → WD h} (H : IsRecT h rc) (x : IrrGL (w.adicCompletion E))
    (α : Fin x.1 → ℂˣ) (hα : HasSatake x.rep α) : rc x = WD.mk (WDRep.diag h fun i => (α i)⁻¹) := by
  obtain ⟨a, ha, H⟩ := H
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  have hL := GlobalTheory.T.spherical_satake_eq_langlandsQuotient_unramified Pr.exh Pr.multi Pr.cos Pr.zel GlobalTheory.RecT.geometricLemma_holds Pr.bz (w.adicCompletion E) x α hα
  rw [Fin.univ_val_map] at hL
  rw [H.langlands _ x hL, segSum, List.map_ofFn, ← SatakeLaw.sumList_ofFn_diag]
  congr 1
  refine List.ofFn_inj.mpr (funext fun i => ?_)
  simp only [Function.comp_apply, Segment.single, Segment.first_ofFirst, Segment.len_ofFirst, Nat.cast_one, sub_self,
    zero_div, WD.lpTw_zero, Test.lpChar_lpSp_one, H.one]
  exact Test.lpOfChar_unrChar ha (α i) _
/- English proof (translation)
Use `haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective`. Take `⟨α, hαB, hα⟩` from `(GlobalTheory.LGrp.SatakeCompare.hasSatakeGL_iff _ _ _ σ.ρ B).1 (GlobalTheory.LFun.SatCompare.hasSatakeGL_iff.2 ⟨⟨σ.smooth, σ.irred⟩, hB⟩)`. Use `⟨α, hαB.symm, ?_⟩` and prove the remaining obligations. Establish `φ` using `IrrGL.equivOf σ.ρ σ.smooth σ.irred`. Establish `e : rc (IrrGL.of σ.ρ σ.smooth σ.irred) = WD.mk (WDRep.diag h fun i => (α i)⁻¹)` using `rec_diag H (IrrGL.of σ.ρ σ.smooth σ.irred) α ⟨IrrRep.irr _, fixed_ne_bot_of_equiv φ hα.2.1, (IsSubquotient.of_surjective φ.toIntertwiningMap φ.toLinearEquiv.surjective).trans hα.2.2⟩`.

Take `⟨a, ha, L⟩` from `H`. Rewrite using `[algNorm, L.nu, e, WD.lpTw_mk]`. Use `WD.sound ⟨.refl _ _, fun g v => funext fun i => ?_, fun v => rfl⟩` and prove the remaining obligations. Simplify using `[mul_zpow, mul_comm, mul_left_comm, mul_assoc]`.
-/
private theorem rec_algNorm_diag {rc : IrrGL (w.adicCompletion E) → WD h} (H : IsRecT h rc) {n : ℕ}
    (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) (B : Multiset ℂˣ) (hB : GlobalTheory.LFun.HasSatGL w σ.ρ B) :
    ∃ α : Fin n → ℂˣ, B = Finset.univ.val.map α ∧
      rc (algNorm σ) = WD.mk (WDRep.diag h fun i => (α i)⁻¹ * qPow w ((1 - (n : ℝ)) / 2)) := by
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  obtain ⟨α, hαB, hα⟩ := (GlobalTheory.LGrp.SatakeCompare.hasSatakeGL_iff _ _ _ σ.ρ B).1
    (GlobalTheory.LFun.SatCompare.hasSatakeGL_iff.2 ⟨⟨σ.smooth, σ.irred⟩, hB⟩)
  refine ⟨α, hαB.symm, ?_⟩
  have φ := IrrGL.equivOf σ.ρ σ.smooth σ.irred
  have e : rc (IrrGL.of σ.ρ σ.smooth σ.irred) = WD.mk (WDRep.diag h fun i => (α i)⁻¹) :=
    rec_diag H (IrrGL.of σ.ρ σ.smooth σ.irred) α ⟨IrrRep.irr _, fixed_ne_bot_of_equiv φ hα.2.1,
      (IsSubquotient.of_surjective φ.toIntertwiningMap φ.toLinearEquiv.surjective).trans hα.2.2⟩
  obtain ⟨a, ha, L⟩ := H
  rw [algNorm, L.nu, e, WD.lpTw_mk]
  refine WD.sound ⟨.refl _ _, fun g v => funext fun i => ?_, fun v => rfl⟩
  simp [mul_zpow, mul_comm, mul_left_comm, mul_assoc]
/- English proof (translation)
Use `⟨fun s t => ?_, WD.unr_mono0 _ ((WD.unr_mk _).2 (WDRep.unr_diag _))⟩` and prove the remaining obligations. Establish `hd : deg (⁅s, t⁆ : Weil h) = 0`. Rewrite using `[commutatorElement_def, deg_mul, deg_mul, deg_mul, deg_inv, deg_inv]`. Expand and normalize the polynomial expressions, which then agree. Use `show WD.charPol _ _ = _`.

Rewrite using `[WD.charPol_mk, WDRep.diag_ρ, charpoly_diagEnd, hd]`. Simplify using the standard rewrite rules.
-/
private theorem gd_diag {n : ℕ} (c : Fin n → ℂˣ) : Z.Win.Gd (WD.mk (WDRep.diag h c)) := by
  refine ⟨fun s t => ?_, WD.unr_mono0 _ ((WD.unr_mk _).2 (WDRep.unr_diag _))⟩
  have hd : deg (⁅s, t⁆ : Weil h) = 0 := by
    rw [commutatorElement_def, deg_mul, deg_mul, deg_mul, deg_inv, deg_inv]
    ring
  show WD.charPol _ _ = _
  rw [WD.charPol_mk, WDRep.diag_ρ, charpoly_diagEnd, hd]
  simp
/- English proof (translation)
Rewrite using `[Complex.ofReal_cpow (Nat.cast_nonneg _), zpow_neg_one, Units.val_mul, mul_inv, Units.val_inv_eq_inv_val, inv_inv, coe_qPow, ← Complex.cpow_neg, mul_comm]`. Use `congr 2`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem val_inv_eq (n : ℕ) (a : ℂˣ) :
    (((a⁻¹ * qPow w ((1 - (n : ℝ)) / 2) : ℂˣ) : ℂ)) ^ (-1 : ℤ) =
      ((((normV w : ℕ) : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) * (a : ℂ) := by
  rw [Complex.ofReal_cpow (Nat.cast_nonneg _), zpow_neg_one, Units.val_mul, mul_inv, Units.val_inv_eq_inv_val, inv_inv,
    coe_qPow, ← Complex.cpow_neg, mul_comm]
  congr 2
  push_cast
  ring
end UpperTheory.V.Z.Desc.W.SatakeFrobeniusEigenvalues
open UpperTheory.V.Z.Desc.W.SatakeFrobeniusEigenvalues in
/- English proof (translation)
Introduce `_ F Ω _ _ _ _ _ l _ ι n r _ w hl σ B hB H A h`. Take `⟨rc, hrec⟩` from `recTExists F Ω A w h`. Take `⟨α, rfl, e⟩` from `rec_algNorm_diag hrec σ B hB`. Establish `hx` using `(H A h rc hrec).isWDOf (e ▸ gd_diag _)`. Establish `hw` using `(hx.wdOf_eq hl).trans e`.

Take `⟨t, ht, φ, hφ, N', a, hN, -⟩` from `hx`. Use `⟨(hN.unr_wdOf_iff hl ht ι).1 (by rw [hw, WD.unr_mk]; exact WDRep.unr_diag _), fun s hs => ?_⟩` and prove the remaining obligations. Establish `hd : deg (⟨s, mem_Weil_of_isFrob h hs⟩ : Weil h) = 1` using `deg_eq_one_iff.2 hs`. Use `hN.charPol_wdOf hl ht ι (⟨s, mem_Weil_of_isFrob h hs⟩ : Weil h)⁻¹` as an intermediate fact. Rewrite `this` using `[hw, WD.charPol_mk, WDRep.diag_ρ, charpoly_diagEnd, deg_inv, hd]`.

Use `this.symm.trans ?_` and prove the remaining obligations. Simplify using `only [val_inv_eq, algSat, Multiset.map_map, Multiset.pure_def, Multiset.bind_def, Multiset.bind_singleton]`. Both sides reduce to the same expression.
-/
theorem UpperTheory.V.Z.Desc.W.satFrobT_alt :
    _root_.UpperTheory.V.Af.Hypotheses' → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (n : ℕ) (r : G F Ω →* GL (Fin n) (Qbar l)), Continuous r → ∀ w : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∉ w.asIdeal →
    ∀ (σ : SmIrr (GL (Fin n) (w.adicCompletion F))) (B : Multiset ℂˣ), GlobalTheory.LFun.HasSatGL w σ.ρ B →
    (∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w) (rc : IrrGL (w.adicCompletion F) → WD h), IsRecT h rc → Z.Win.WDT ι r (rc (algNorm σ))) →
    FrobEig ι r w (algSat n (normV w) B) := by
  intro _ F Ω _ _ _ _ _ l _ ι n r _ w hl σ B hB H A h
  obtain ⟨rc, hrec⟩ := recTExists F Ω A w h
  obtain ⟨α, rfl, e⟩ := rec_algNorm_diag hrec σ B hB
  have hx := (H A h rc hrec).isWDOf (e ▸ gd_diag _)
  have hw := (hx.wdOf_eq hl).trans e
  obtain ⟨t, ht, φ, hφ, N', a, hN, -⟩ := hx
  refine ⟨(hN.unr_wdOf_iff hl ht ι).1 (by rw [hw, WD.unr_mk]; exact WDRep.unr_diag _), fun s hs => ?_⟩
  have hd : deg (⟨s, mem_Weil_of_isFrob h hs⟩ : Weil h) = 1 := deg_eq_one_iff.2 hs
  have := hN.charPol_wdOf hl ht ι (⟨s, mem_Weil_of_isFrob h hs⟩ : Weil h)⁻¹
  rw [hw, WD.charPol_mk, WDRep.diag_ρ, charpoly_diagEnd, deg_inv, hd] at this
  refine this.symm.trans ?_
  simp only [val_inv_eq, algSat, Multiset.map_map, Multiset.pure_def, Multiset.bind_def, Multiset.bind_singleton]
  rfl
end
