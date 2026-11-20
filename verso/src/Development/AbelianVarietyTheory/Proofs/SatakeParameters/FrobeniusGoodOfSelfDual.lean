import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MonodromyVanishesWeilTwistIff
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsGoodConjSelfDualTwistSplitUnramified
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsUnitaryTwistAbsPow
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspRepSatakeIffLocalComponentSatake
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsTemperedGLOfHasSatGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormsFiniteGL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalArtinExistsHolds
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSteinberg
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumSegmentsLanglands
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSstAtOfIsCrysAt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FontaineParameterTwistPotentiallySemistable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfMapEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisHodgeOfCuspidal
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RoadU.PhiTwist

open GlobalTheory.GalCut.IwaTwist GlobalTheory.GalCut7.IwahoriTwist UpperTheory.V UpperTheory.V.Af ValuativeRel

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}

/- English proof (translation)
Use `MonoidHom.ext fun x => ?_` and prove the remaining obligations. Establish `h2` using `unif_spec w`. Establish `h0 : Valued.v (x : w.adicCompletion E) ≠ 0` using `by simp`. Establish `h1 : IsUnitAt w (x * (atFin w (unif w) ^ ord (w.adicCompletion E) x)⁻¹)`. Unfold `IsUnitAt IsUnifAt at *`.

Rewrite using `[Units.val_mul, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, map_mul, map_inv₀, map_zpow₀, h2, ← WithZero.exp_zsmul, SphCompletion.ord_completion]`. Simplify using `only [smul_eq_mul, mul_neg, mul_one, neg_neg]`. Rewrite using `[WithZero.exp_log h0, mul_inv_cancel₀ h0]`. Establish `h3` using `hu _ h1`. Rewrite `h3` using `[map_mul, map_inv, map_zpow, mul_inv_eq_one]`.

Conclude with `h3`.
-/
theorem loc_eq_unrChar [IsTotallyComplex E] (χ : HChar E) (hu : χ.UnrAt w) :
    χ.loc w = SmGL.unrChar (w.adicCompletion E) (χ.val w) := by
  refine MonoidHom.ext fun x => ?_
  have h2 := unif_spec w
  have h0 : Valued.v (x : w.adicCompletion E) ≠ 0 := by simp
  have h1 : IsUnitAt w (x * (atFin w (unif w) ^ ord (w.adicCompletion E) x)⁻¹) := by
    unfold IsUnitAt IsUnifAt at *
    rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, map_mul,
      map_inv₀, map_zpow₀, h2, ← WithZero.exp_zsmul, SphCompletion.ord_completion]
    simp only [smul_eq_mul, mul_neg, mul_one, neg_neg]
    rw [WithZero.exp_log h0, mul_inv_cancel₀ h0]
  have h3 := hu _ h1
  rw [map_mul, map_inv, map_zpow, mul_inv_eq_one] at h3
  exact h3

/- English proof (translation)
Establish `hM : WD.lpOfChar h ((SmGL.unrChar (w.adicCompletion E) c).comp art) hs = WD.mk (WDRep.diag h fun _ : Fin 1 => c⁻¹)` using `Test.lpOfChar_unrChar ha c hs`. Establish `hMu : (WD.mk (WDRep.diag h fun _ : Fin 1 => c⁻¹)).unr` using `(WD.unr_mk _).mpr (WDRep.unr_diag _)`. Establish `hMf : (WD.mk (WDRep.diag h fun _ : Fin 1 => c⁻¹)).frobEig = {((c⁻¹ : ℂˣ) : ℂ)}`. Rewrite using `[WD.frobEig_diag]`. Simplify using the standard rewrite rules.

Establish `h0 : (0 : ℂ) ∉ B.map fun b => ((b⁻¹ : ℂˣ) : ℂ)`. Simplify using the standard rewrite rules. Take `⟨hu0, hf0, -⟩` from `WD.lpUnr_spec (h := h) _ h0`. Establish `hU : WD.lpUnr h ((B.map (· * c)).map fun b => ((b⁻¹ : ℂˣ) : ℂ)) = (WD.lpUnr h (B.map fun b => ((b⁻¹ : ℂˣ) : ℂ))).lpChar (WD.mk (WDRep.diag h fun _ : Fin 1 => c⁻¹))`. Establish `hu1` using `WD.unr_lpChar _ _ hu0 hMu`.

Rewrite using `[WD.unr_eq_lpUnr _ hu1, WD.frobEig_char _ _ _ hu0 hMu hMf, hf0, Multiset.map_map, Multiset.map_map]`. Use `congr 1`. Use `Multiset.map_congr rfl fun b _ => ?_` and prove the remaining obligations. Simplify using `[mul_inv_rev, mul_comm]`. Rewrite using `[← lpChar_lpOfChar, hM, satWD, satWD, GlobalTheory.NuShift.lpChar_lpTw, hU]`.
-/
theorem satWD_map_mul (h : Formalism.ConjugateSelfDual.IsPlaceOver A w) (a : ℕ) (B : Multiset ℂˣ) (c : ℂˣ)
    {art : Weil h →* (w.adicCompletion E)ˣ} (ha : IsLocalArtin h art)
    (hs : GlobalTheory.WeilDeligne.IsSmooth ((SmGL.unrChar (w.adicCompletion E) c).comp art)) :
    satWD h a (B.map (· * c)) = (satWD h a B).lpTwist _ hs := by
  have hM : WD.lpOfChar h ((SmGL.unrChar (w.adicCompletion E) c).comp art) hs =
      WD.mk (WDRep.diag h fun _ : Fin 1 => c⁻¹) := Test.lpOfChar_unrChar ha c hs
  have hMu : (WD.mk (WDRep.diag h fun _ : Fin 1 => c⁻¹)).unr := (WD.unr_mk _).mpr (WDRep.unr_diag _)
  have hMf : (WD.mk (WDRep.diag h fun _ : Fin 1 => c⁻¹)).frobEig = {((c⁻¹ : ℂˣ) : ℂ)} := by
    rw [WD.frobEig_diag]; simp
  have h0 : (0 : ℂ) ∉ B.map fun b => ((b⁻¹ : ℂˣ) : ℂ) := by
    simp
  obtain ⟨hu0, hf0, -⟩ := WD.lpUnr_spec (h := h) _ h0
  have hU : WD.lpUnr h ((B.map (· * c)).map fun b => ((b⁻¹ : ℂˣ) : ℂ)) =
      (WD.lpUnr h (B.map fun b => ((b⁻¹ : ℂˣ) : ℂ))).lpChar (WD.mk (WDRep.diag h fun _ : Fin 1 => c⁻¹)) := by
    have hu1 := WD.unr_lpChar _ _ hu0 hMu
    rw [WD.unr_eq_lpUnr _ hu1, WD.frobEig_char _ _ _ hu0 hMu hMf, hf0, Multiset.map_map, Multiset.map_map]
    congr 1
    refine Multiset.map_congr rfl fun b _ => ?_
    simp [mul_inv_rev, mul_comm]
  rw [← lpChar_lpOfChar, hM, satWD, satWD, GlobalTheory.NuShift.lpChar_lpTw, hU]

end GlobalTheory.RoadU.PhiTwist

open GlobalTheory.GalCut.IwaTwist GlobalTheory.GalCut7.IwahoriTwist GlobalTheory.RoadU.PhiTwist UpperTheory.V UpperTheory.V.Af in

/- English proof (translation)
Introduce `hI Hc Hp E Ω _ _ _ _ _ _ l _ ι a ha π χ hS r hr w hw B hB`. Introduce `P AI hT A h O _ _ _ Bw hj g`. Take `⟨κ, m, hκ, hu, hS'⟩` from `GlobalTheory.GoodCsdTwist.exists_goodCsd_twist GlobalTheory.automorphicFormsFiniteGL E l a ha π χ hS w hw`. Take `⟨art, hart, hμ⟩` from `(GlobalTheory.Published.GlobalArtinReciprocity.heckeLAdicCharacter_and_principalIdealSt GlobalTheory.globalArtinReciprocity_holds).1 E Ω`. Establish `hκ'` using `isAlgPos_of_isAlg hκ`.

Take `⟨μ, ⟨hμc, hL⟩, -⟩` from `hμ l ι κ m hκ'`. Establish `hcont : Continuous (tw r μ)` using `UpperTheory.galoisRep_irreducibility_criterion.2 _ _ a r μ hr.1 hμc`. Establish `hr' : Weak (π.twist κ) ι (tw r μ)` using `⟨hcont, UpperTheory.V.Af.Cq.attTwist E Ω l ι a r π hr.2 art κ m μ hart hL⟩`. Establish `hB' : (CG.mk (π.twist κ)).HasSat w (B.map (· * κ.val w))` using `CG.HasSat.twist hB hu`. Establish `C : (wdAt P ι Bw h hj ((tw r μ).comp (ReciprocityTheory.Gal.Dec (F` using `E) A).subtype)).charPol g = (satWD h a (B.map (· * κ.val w))).charPol g := Hp E Ω l ι a ha (π.twist κ) _ hS' (tw r μ) hr' w hw _ hB' P AI hT A h O Bw hj g`.

Take `⟨σ, hσ, -⟩` from `GlobalTheory.CuspRep.LocEx.exists_isLocComp GlobalTheory.automorphicFormsFiniteGL E a π w`. Establish `hsph : SmGL.IsSpherical σ.ρ` using `GlobalTheory.CohomologicalConjSelfDualTempered.UnrModel.isSpherical_of_hasSatGL w a (((GlobalTheory.Cong.satake_locComp E a π w σ hσ).1 B).1 hB)`. Establish `c1 : IsCrysAt P Bw ((tw r μ).comp (ReciprocityTheory.Gal.Dec (F` using `E) A).subtype) := Hc E Ω l ι a ha (π.twist κ) _ hS' (tw r μ) hr' w hw _ hB' P AI hT A h O Bw hj _ (hσ.twist κ) (GlobalTheory.CrysTwistBack.isSpherical_twist_of_unr a w σ κ hu hsph)`. Take `⟨T⟩` from `hT`. Establish `c1s : IsSstAt P Bw ((tw r μ).comp (ReciprocityTheory.Gal.Dec (F` using `E) A).subtype) := GlobalTheory.CrysSst.isSstAt_of_isCrysAt l P AI ⟨T⟩ E Ω _ O Bw a _ c1`.

Establish `hμi : IsCrysAt P Bw ((GlobalTheory.TripleGal.rk1 μ⁻¹).comp (ReciprocityTheory.Gal.Dec (F` using `E) A).subtype) := (GlobalTheory.Published.heckeLAdicCharacterAbove_iff.1 hI.hk E Ω l P AI ⟨T⟩ ι art hart κ⁻¹ (-m) μ⁻¹ (GlobalTheory.GalChar.isAlgPos_inv hκ') hμc.inv hL.inv w A h O Bw hj).2.2.1 hu.inv`. Establish `hrr : r.comp (ReciprocityTheory.Gal.Dec (F` using `E) A).subtype = Formalism.MainNotions.SumRepresentations.At.twGL ((tw r μ).comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype) (Matrix.GeneralLinearGroup.det.comp ((GlobalTheory.TripleGal.rk1 μ⁻¹).comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype)) := by`. Use extensionality with `g i j`. Simplify using `[Formalism.MainNotions.SumRepresentations.At.twGL, tw_val, GlobalTheory.TripleGal.rk1, Matrix.det_unique, Algebra.algebraMap_eq_smul_one, Matrix.smul_apply]`. Establish `hct : Continuous fun g : ↥(ReciprocityTheory.Gal.Dec (F` using `E) A) => (((tw r μ).comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) := Units.continuous_val.comp (hcont.comp continuous_subtype_val)`.

Establish `hcμi : Continuous fun g : ↥(ReciprocityTheory.Gal.Dec (F` using `E) A) => (((GlobalTheory.TripleGal.rk1 μ⁻¹).comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype g : GL (Fin 1) (Om l)) : Matrix (Fin 1) (Fin 1) (Om l)) := by`. Use `continuous_matrix fun i j => ?_` and prove the remaining obligations. Use `fin_cases i`. Use `fin_cases j`. Use `Units.continuous_val.comp (hμc.inv.comp (continuous_subtype_val (p := fun x => x ∈ ReciprocityTheory.Gal.Dec (F := E) A)))` as an intermediate fact.

Simplify `this` using `[GlobalTheory.TripleGal.rk1, Function.comp_def]`. Establish `hsst : IsSstAt P Bw (r.comp (ReciprocityTheory.Gal.Dec (F` using `E) A).subtype) := by`. Rewrite using `[hrr]`. Conclude with `isSstAt_twist hI.pst P AI ⟨T⟩ Bw _ _ hct hcμi c1s hμi`. Take `⟨a', ha'⟩` from `GlobalTheory.localArtinExists_holds E Ω A w h`.

Establish `hc` using `GlobalTheory.Published.ParamAboveModel.isComp_loc (w := w) κ`. Establish `hdet : Matrix.GeneralLinearGroup.det.comp ((GlobalTheory.TripleGal.rk1 μ).comp (ReciprocityTheory.Gal.Dec (F` using `E) A).subtype) = μ.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype := by`. Use extensionality with `g`. Simplify using `[GlobalTheory.TripleGal.rk1, Matrix.det_unique]`. Establish `htw : (tw r μ).comp (ReciprocityTheory.Gal.Dec (F` using `E) A).subtype = Formalism.MainNotions.SumRepresentations.At.twGL (r.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype) (Matrix.GeneralLinearGroup.det.comp ((GlobalTheory.TripleGal.rk1 μ).comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype)) := by`.

Rewrite using `[hdet]`. Use extensionality with `g i j`. Simplify using `[Formalism.MainNotions.SumRepresentations.At.twGL, tw_val, Algebra.algebraMap_eq_smul_one, Matrix.smul_apply]`. Establish `hcR : Continuous fun g : ↥(ReciprocityTheory.Gal.Dec (F` using `E) A) => ((r.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) := Units.continuous_val.comp (hr.1.comp continuous_subtype_val)`. Establish `hcμ : Continuous fun g : ↥(ReciprocityTheory.Gal.Dec (F` using `E) A) => (((GlobalTheory.TripleGal.rk1 μ).comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype g : GL (Fin 1) (Om l)) : Matrix (Fin 1) (Fin 1) (Om l)) := by`.

Use `continuous_matrix fun i j => ?_` and prove the remaining obligations. Use `fin_cases i`. Use `fin_cases j`. Use `Units.continuous_val.comp (hμc.comp (continuous_subtype_val (p := fun x => x ∈ ReciprocityTheory.Gal.Dec (F := E) A)))` as an intermediate fact. Simplify `this` using `[GlobalTheory.TripleGal.rk1, Function.comp_def]`.

Establish `hdR` using `(GlobalTheory.Published.heckeLAdicCharacterAbove_iff.1 hI.hk E Ω l P AI ⟨T⟩ ι art hart κ m μ hκ' hμc hL w A h O Bw hj).1`. Establish `hPμ` using `GlobalTheory.Published.DeRhamPotSemistable.isPstAt hI.pst T Bw _ hcμ hdR`. Establish `hP` using `isPstAt_of_isSstAt P AI ⟨T⟩ Bw _ hsst`. Establish `hP'` using `isPstAt_of_isSstAt P AI ⟨T⟩ Bw _ c1s`. Rewrite `hP'` using `[htw]`.

Establish `hWD : wdAt P ι Bw h hj ((tw r μ).comp (ReciprocityTheory.Gal.Dec (F` using `E) A).subtype) = (wdAt P ι Bw h hj (r.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype)).lpTwist ((κ.loc w).comp a') (ha'.smooth hc.1) := by`. Rewrite using `[htw, GlobalTheory.TwistParamAbove.wdAt_twist l P AI ⟨T⟩ ι E Ω A w h O Bw hj a _ _ hcR hcμ hP hPμ hP', hI.alg E Ω l P AI ⟨T⟩ ι art hart κ m μ hκ' hμc hL w A h O Bw hj _ hc a' ha', lpChar_lpOfChar]`. Establish `hsat : ∀ (ξ : (w.adicCompletion E)ˣ →* ℂˣ) (hξ : GlobalTheory.WeilDeligne.IsSmooth (ξ.comp a')), ξ = SmGL.unrChar (w.adicCompletion E) (κ.val w) → satWD h a (B.map (· * κ.val w)) = (satWD h a B).lpTwist _ hξ`. Introduce and unpack `ξ hξ rfl`. Conclude with `satWD_map_mul h a B (κ.val w) ha' hξ`.

Rewrite `C` using `[hWD, hsat (κ.loc w) (ha'.smooth hc.1) (loc_eq_unrChar κ hu)]`. Conclude with `(charPol_lpTwist_iff _ _ _ _ g).1 C`.
-/
theorem GlobalTheory.RoadU.holdsS_good_phi : Inputs → SphericalLevelCondition .csd .crys → SphericalLevelCondition .csd .phi → SphericalLevelCondition .good .phi := by
  intro hI Hc Hp E Ω _ _ _ _ _ _ l _ ι a ha π χ hS r hr w hw B hB
  intro P AI hT A h O _ _ _ Bw hj g
  obtain ⟨κ, m, hκ, hu, hS'⟩ := GlobalTheory.GoodCsdTwist.exists_goodCsd_twist GlobalTheory.automorphicFormsFiniteGL E l a ha π χ hS w hw
  obtain ⟨art, hart, hμ⟩ := (GlobalTheory.Published.GlobalArtinReciprocity.heckeLAdicCharacter_and_principalIdealSt
    GlobalTheory.globalArtinReciprocity_holds).1 E Ω
  have hκ' := isAlgPos_of_isAlg hκ
  obtain ⟨μ, ⟨hμc, hL⟩, -⟩ := hμ l ι κ m hκ'
  have hcont : Continuous (tw r μ) := UpperTheory.galoisRep_irreducibility_criterion.2 _ _ a r μ hr.1 hμc
  have hr' : Weak (π.twist κ) ι (tw r μ) := ⟨hcont, UpperTheory.V.Af.Cq.attTwist E Ω l ι a r π hr.2 art κ m μ hart hL⟩
  have hB' : (CG.mk (π.twist κ)).HasSat w (B.map (· * κ.val w)) := CG.HasSat.twist hB hu
  have C : (wdAt P ι Bw h hj ((tw r μ).comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype)).charPol g =
      (satWD h a (B.map (· * κ.val w))).charPol g :=
    Hp E Ω l ι a ha (π.twist κ) _ hS' (tw r μ) hr' w hw _ hB' P AI hT A h O Bw hj g
  obtain ⟨σ, hσ, -⟩ := GlobalTheory.CuspRep.LocEx.exists_isLocComp GlobalTheory.automorphicFormsFiniteGL E a π w
  have hsph : SmGL.IsSpherical σ.ρ :=
    GlobalTheory.CohomologicalConjSelfDualTempered.UnrModel.isSpherical_of_hasSatGL w a (((GlobalTheory.Cong.satake_locComp E a π w σ hσ).1 B).1 hB)
  have c1 : IsCrysAt P Bw ((tw r μ).comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype) :=
    Hc E Ω l ι a ha (π.twist κ) _ hS' (tw r μ) hr' w hw _ hB' P AI hT A h O Bw hj _ (hσ.twist κ)
      (GlobalTheory.CrysTwistBack.isSpherical_twist_of_unr a w σ κ hu hsph)
  obtain ⟨T⟩ := hT
  have c1s : IsSstAt P Bw ((tw r μ).comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype) :=
    GlobalTheory.CrysSst.isSstAt_of_isCrysAt l P AI ⟨T⟩ E Ω _ O Bw a _ c1
  have hμi : IsCrysAt P Bw ((GlobalTheory.TripleGal.rk1 μ⁻¹).comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype) :=
    (GlobalTheory.Published.heckeLAdicCharacterAbove_iff.1 hI.hk E Ω l P AI ⟨T⟩ ι art hart κ⁻¹ (-m) μ⁻¹
      (GlobalTheory.GalChar.isAlgPos_inv hκ') hμc.inv hL.inv w A h O Bw hj).2.2.1 hu.inv
  have hrr : r.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype = Formalism.MainNotions.SumRepresentations.At.twGL ((tw r μ).comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype)
      (Matrix.GeneralLinearGroup.det.comp ((GlobalTheory.TripleGal.rk1 μ⁻¹).comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype)) := by
    ext g i j
    simp [Formalism.MainNotions.SumRepresentations.At.twGL, tw_val, GlobalTheory.TripleGal.rk1, Matrix.det_unique, Algebra.algebraMap_eq_smul_one,
      Matrix.smul_apply]
  have hct : Continuous fun g : ↥(ReciprocityTheory.Gal.Dec (F := E) A) =>
      (((tw r μ).comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) :=
    Units.continuous_val.comp (hcont.comp continuous_subtype_val)
  have hcμi : Continuous fun g : ↥(ReciprocityTheory.Gal.Dec (F := E) A) =>
      (((GlobalTheory.TripleGal.rk1 μ⁻¹).comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype g : GL (Fin 1) (Om l)) :
        Matrix (Fin 1) (Fin 1) (Om l)) := by
    refine continuous_matrix fun i j => ?_
    fin_cases i; fin_cases j
    have := Units.continuous_val.comp (hμc.inv.comp (continuous_subtype_val (p := fun x => x ∈ ReciprocityTheory.Gal.Dec (F := E) A)))
    simpa [GlobalTheory.TripleGal.rk1, Function.comp_def] using this
  have hsst : IsSstAt P Bw (r.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype) := by
    rw [hrr]
    exact isSstAt_twist hI.pst P AI ⟨T⟩ Bw _ _ hct hcμi c1s hμi
  obtain ⟨a', ha'⟩ := GlobalTheory.localArtinExists_holds E Ω A w h
  have hc := GlobalTheory.Published.ParamAboveModel.isComp_loc (w := w) κ
  have hdet : Matrix.GeneralLinearGroup.det.comp ((GlobalTheory.TripleGal.rk1 μ).comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype)
      = μ.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype := by
    ext g
    simp [GlobalTheory.TripleGal.rk1, Matrix.det_unique]
  have htw : (tw r μ).comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype =
      Formalism.MainNotions.SumRepresentations.At.twGL (r.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype)
        (Matrix.GeneralLinearGroup.det.comp ((GlobalTheory.TripleGal.rk1 μ).comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype)) := by
    rw [hdet]
    ext g i j
    simp [Formalism.MainNotions.SumRepresentations.At.twGL, tw_val, Algebra.algebraMap_eq_smul_one, Matrix.smul_apply]
  have hcR : Continuous fun g : ↥(ReciprocityTheory.Gal.Dec (F := E) A) =>
      ((r.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) :=
    Units.continuous_val.comp (hr.1.comp continuous_subtype_val)
  have hcμ : Continuous fun g : ↥(ReciprocityTheory.Gal.Dec (F := E) A) =>
      (((GlobalTheory.TripleGal.rk1 μ).comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype g : GL (Fin 1) (Om l)) :
        Matrix (Fin 1) (Fin 1) (Om l)) := by
    refine continuous_matrix fun i j => ?_
    fin_cases i; fin_cases j
    have := Units.continuous_val.comp (hμc.comp (continuous_subtype_val (p := fun x => x ∈ ReciprocityTheory.Gal.Dec (F := E) A)))
    simpa [GlobalTheory.TripleGal.rk1, Function.comp_def] using this
  have hdR := (GlobalTheory.Published.heckeLAdicCharacterAbove_iff.1 hI.hk E Ω l P AI ⟨T⟩ ι art hart κ m μ hκ' hμc hL w A h O Bw hj).1
  have hPμ := GlobalTheory.Published.DeRhamPotSemistable.isPstAt hI.pst T Bw _ hcμ hdR
  have hP := isPstAt_of_isSstAt P AI ⟨T⟩ Bw _ hsst
  have hP' := isPstAt_of_isSstAt P AI ⟨T⟩ Bw _ c1s
  rw [htw] at hP'
  have hWD : wdAt P ι Bw h hj ((tw r μ).comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype) =
      (wdAt P ι Bw h hj (r.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype)).lpTwist ((κ.loc w).comp a') (ha'.smooth hc.1) := by
    rw [htw, GlobalTheory.TwistParamAbove.wdAt_twist l P AI ⟨T⟩ ι E Ω A w h O Bw hj a _ _ hcR hcμ hP hPμ hP',
      hI.alg E Ω l P AI ⟨T⟩ ι art hart κ m μ hκ' hμc hL w A h O Bw hj _ hc a' ha', lpChar_lpOfChar]
  have hsat : ∀ (ξ : (w.adicCompletion E)ˣ →* ℂˣ) (hξ : GlobalTheory.WeilDeligne.IsSmooth (ξ.comp a')),
      ξ = SmGL.unrChar (w.adicCompletion E) (κ.val w) →
      satWD h a (B.map (· * κ.val w)) = (satWD h a B).lpTwist _ hξ := by
    rintro ξ hξ rfl
    exact satWD_map_mul h a B (κ.val w) ha' hξ
  rw [hWD, hsat (κ.loc w) (ha'.smooth hc.1) (loc_eq_unrChar κ hu)] at C
  exact (charPol_lpTwist_iff _ _ _ _ g).1 C

end
