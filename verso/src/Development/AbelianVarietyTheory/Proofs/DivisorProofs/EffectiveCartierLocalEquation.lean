import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOrdSubOneLeOrdWedgeDifferentials
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackProportionalOfProporti
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUniqueLbIsoPullEqOfCoheightLeOne
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIdealSheafAwayFromP
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Cartier.IdealDiv

/- English proof (translation)
Take `⟨h, hhW, hxh⟩` from `U.2.exists_basicOpen_le (V := U.1 ⊓ V.1) ⟨_, ⟨hU, hV⟩⟩ hU`. Set `Wa : Y.affineOpens` to `⟨Y.basicOpen h, U.2.basicOpen h⟩`. Establish `hWU : Wa.1 ≤ U.1` using `hhW.trans inf_le_left`. Establish `hWV : Wa.1 ≤ V.1` using `hhW.trans inf_le_right`. Use `haveI : Nonempty Wa.1 := ⟨⟨_, hxh⟩⟩`.

Establish `e1 : J.ideal Wa = Ideal.span {resG Y hWU f}`. Rewrite using `[← Scheme.IdealSheafData.map_ideal _ (U := Wa) (V := U) hWU, hf, Ideal.map_span, Set.image_singleton]`. Both sides reduce to the same expression. Establish `e2 : J.ideal Wa = Ideal.span {resG Y hWV f'}`. Rewrite using `[← Scheme.IdealSheafData.map_ideal _ (U := Wa) (V := V) hWV, hf', Ideal.map_span, Set.image_singleton]`.

Both sides reduce to the same expression. Take `⟨u, hu⟩` from `Ideal.span_singleton_eq_span_singleton.1 (e1.symm.trans e2)`. Establish `hg` using `gen_mem (U := Wa.1) hxh`. Establish `e` using `congrArg (fnOf Wa.1 hg) hu`. Rewrite `e` using `[map_mul, fnOf_resG, fnOf_resG]`.

Rewrite using `[← e, mul_div_cancel_left₀ _ h0]`. Conclude with `unitAt_fnOf hxh hg u`.
-/
theorem unitAt_div_of_ideal_eq {Y : Scheme.{0}} [IsIntegral Y] (J : Y.IdealSheafData) {y : Y}
    {U V : Y.affineOpens} {f : Γ(Y, U.1)} {f' : Γ(Y, V.1)} (hU : y ∈ U.1) (hV : y ∈ V.1)
    (hf : J.ideal U = Ideal.span {f}) (hf' : J.ideal V = Ideal.span {f'})
    (h0 : fnOf U.1 (gen_mem hU) f ≠ 0) :
    UnitAt y (fnOf V.1 (gen_mem hV) f' / fnOf U.1 (gen_mem hU) f) := by
  obtain ⟨h, hhW, hxh⟩ := U.2.exists_basicOpen_le (V := U.1 ⊓ V.1) ⟨_, ⟨hU, hV⟩⟩ hU
  let Wa : Y.affineOpens := ⟨Y.basicOpen h, U.2.basicOpen h⟩
  have hWU : Wa.1 ≤ U.1 := hhW.trans inf_le_left
  have hWV : Wa.1 ≤ V.1 := hhW.trans inf_le_right
  haveI : Nonempty Wa.1 := ⟨⟨_, hxh⟩⟩
  have e1 : J.ideal Wa = Ideal.span {resG Y hWU f} := by
    rw [← Scheme.IdealSheafData.map_ideal _ (U := Wa) (V := U) hWU, hf, Ideal.map_span, Set.image_singleton]
    rfl
  have e2 : J.ideal Wa = Ideal.span {resG Y hWV f'} := by
    rw [← Scheme.IdealSheafData.map_ideal _ (U := Wa) (V := V) hWV, hf', Ideal.map_span, Set.image_singleton]
    rfl
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.1 (e1.symm.trans e2)
  have hg := gen_mem (U := Wa.1) hxh
  have e := congrArg (fnOf Wa.1 hg) hu
  rw [map_mul, fnOf_resG, fnOf_resG] at e
  rw [← e, mul_div_cancel_left₀ _ h0]
  exact unitAt_fnOf hxh hg u

/- English proof (translation)
Introduce `Y _ J hJ`. Use `choose U f hyU hnzd hid using hJ`. Establish `hne : ∀ y, fnOf (U y).1 (gen_mem (hyU y)) (f y) ≠ 0`. Introduce `y h`. Use `haveI : Nonempty (U y).1 := ⟨⟨y, hyU y⟩⟩`.

Establish `h0 : f y = 0` using `fnOf_injective _ _ (h.trans (map_zero _).symm)`. Conclude with `nonZeroDivisors.ne_zero (hnzd y) h0`. Set `v : ∀ y : Y, Y.functionFieldˣ` to `fun y => Units.mk0 _ (hne y)`. Set `E : CartierDiv Y` to `show cartierGroup Y from ⟨fun y => germOf y (v y), fun x => ⟨(U x).1, hyU x, v x, fun y hy => germOf_eq_iff.2 (unitAt_div_of_ideal_eq J (hyU y) hy (hid y) (hid x) (hne y))⟩⟩`. Establish `hE : ∀ y, E.IsEqn y (v y)` using `fun y => rfl`.

Use `⟨E, fun x => ⟨v x, hE x, by rw [one_mul]; exact regAt_fnOf (hyU x) _ _⟩, ?_, ?_⟩` and prove the remaining obligations. Use extensionality with `x`. Rewrite using `[SetLike.mem_coe, SetLike.mem_coe, (hE x).mem_supp_iff, Units.val_mk0, unitAt_fnOf_iff (hyU x), Scheme.IdealSheafData.mem_support_iff_of_mem (U := U x) (hyU x), hid x, Scheme.zeroLocus_span, Scheme.zeroLocus_singleton]`. Both sides reduce to the same expression. Introduce `y V g hy hg hV`.

Conclude with `(hE y).iff_unitAt.2 (unitAt_div_of_ideal_eq J (hyU y) hy (hid y) hV (hne y))`.
-/
theorem exists_cartierDiv_of_effCartier : ∀ (Y : Scheme.{0}) [IsIntegral Y] (J : Y.IdealSheafData),
    FinalTheorems.EffCartier J → ∃ E : CartierDiv Y, E.Eff ∧ E.supp = J.support ∧
      ∀ (y : Y) (U : Y.affineOpens) (f : Γ(Y, U.1)) (hy : y ∈ U.1) (hf : fnOf U.1 (gen_mem hy) f ≠ 0),
        J.ideal U = Ideal.span {f} → E.IsEqn y (Units.mk0 _ hf) := by
  intro Y _ J hJ
  choose U f hyU hnzd hid using hJ
  have hne : ∀ y, fnOf (U y).1 (gen_mem (hyU y)) (f y) ≠ 0 := by
    intro y h
    haveI : Nonempty (U y).1 := ⟨⟨y, hyU y⟩⟩
    have h0 : f y = 0 := fnOf_injective _ _ (h.trans (map_zero _).symm)
    exact nonZeroDivisors.ne_zero (hnzd y) h0
  let v : ∀ y : Y, Y.functionFieldˣ := fun y => Units.mk0 _ (hne y)
  let E : CartierDiv Y := show cartierGroup Y from ⟨fun y => germOf y (v y), fun x =>
    ⟨(U x).1, hyU x, v x, fun y hy =>
      germOf_eq_iff.2 (unitAt_div_of_ideal_eq J (hyU y) hy (hid y) (hid x) (hne y))⟩⟩
  have hE : ∀ y, E.IsEqn y (v y) := fun y => rfl
  refine ⟨E, fun x => ⟨v x, hE x, by rw [one_mul]; exact regAt_fnOf (hyU x) _ _⟩, ?_, ?_⟩
  · ext x
    rw [SetLike.mem_coe, SetLike.mem_coe, (hE x).mem_supp_iff, Units.val_mk0, unitAt_fnOf_iff (hyU x),
      Scheme.IdealSheafData.mem_support_iff_of_mem (U := U x) (hyU x), hid x, Scheme.zeroLocus_span,
      Scheme.zeroLocus_singleton]
    rfl
  · intro y V g hy hg hV
    exact (hE y).iff_unitAt.2 (unitAt_div_of_ideal_eq J (hyU y) hy (hid y) hV (hne y))

end GlobalTheory.Cartier.IdealDiv
