import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.InducesOfIsInduced
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaLocalInputs
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WeightsConj
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RankOneGaloisClosureGeometric
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Purity
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeLAdicTwistStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.UnrRecOfHasSat
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RecAlgNorm
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EventuallyUnr
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRecTLocRecT

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.GalS.Prod
open GlobalTheory GlobalTheory.GalFirstClause Formalism.BasicNotions.Loc GlobalTheory.Pst GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.GalOfCusp GlobalTheory.HeckeGal
/- English proof (translation)
Establish `hloc0 : ∀ w : PlE D.host, P.T.e w (D.naut.locG π w) = _root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (CG.mk π₀) (D.nd.plOm.2 w)` using `fun w => by`. Rewrite using `[P.cg.loc, hmk]`. Both sides reduce to the same expression. Establish `haw : ∀ (w : PlE D.host) (hl : ((l : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal), Aw (wdOf (D.nd.plOm.2 w) hl ι r) (P.T.e w (D.naut.lpTw (D.naut.locG π w) ((1 - (a : ℝ)) / 2)))` using `fun w hl => by`. Take `⟨σ, hσ, -⟩` from `LocEx.exists_isLocComp hF _ a π₀ w`.

Rewrite using `[P.T.tw, hloc0, _root_.GlobalTheory.CuspRep.ParLaws.local_parameter_eq_reciprocity_of_is_local_component hL hσ]`. Conclude with `H.aw hl (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL _) hσ`. Conclude with `haw`.
-/
theorem core_data_of_point (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) {a : ℕ}
    (π : D.naut.CG a) [IsCMField D.host.E] (π₀ : CuspSub D.host.E a)
    (hmk : CG.mk π₀ = (P.cg.e a π).1) {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ}
    {χ : HChar (maximalRealSubfield D.host.E)} {r : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)} {wt : ℤ}
    {HT : (D.host.E →+* Qbar l) → Multiset ℤ} (H : _root_.UpperTheory.GalS.IsGalUAlt π₀ χ ι r wt HT) :
    (∀ (w : PlE D.host) (hl : ((l : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal),
      Aw (wdOf (D.nd.plOm.2 w) hl ι r) (P.T.e w (D.naut.lpTw (D.naut.locG π w) ((1 - (a : ℝ)) / 2)))) := by
  have hloc0 : ∀ w : PlE D.host, P.T.e w (D.naut.locG π w) = _root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (CG.mk π₀) (D.nd.plOm.2 w) := fun w => by
    rw [P.cg.loc, hmk]
    rfl
  have haw : ∀ (w : PlE D.host) (hl : ((l : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal),
      Aw (wdOf (D.nd.plOm.2 w) hl ι r) (P.T.e w (D.naut.lpTw (D.naut.locG π w) ((1 - (a : ℝ)) / 2))) := fun w hl => by
    obtain ⟨σ, hσ, -⟩ := LocEx.exists_isLocComp hF _ a π₀ w
    rw [P.T.tw, hloc0, _root_.GlobalTheory.CuspRep.ParLaws.local_parameter_eq_reciprocity_of_is_local_component hL hσ]
    exact H.aw hl (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL _) hσ
  exact haw
set_option maxHeartbeats 2000000 in
/- English proof (translation)
Introduce `hF hC hL D P i a ha π hc hr`. Use `host_isCMField D.host` as an intermediate fact. Take `⟨π₀, hπ₀⟩` from `Quotient.exists_rep (P.cg.e a π).1`. Establish `hmk : CG.mk π₀ = (P.cg.e a π).1` using `hπ₀`. Establish `hc₀ : π₀.IsCsd`.

Establish `h1` using `(P.cg.csd a π).1 hc`. Rewrite `h1` using `[CGu.IsCsd, ← hmk]`. Conclude with `h1`. Establish `hinf : ∀ τ, D.naut.infG π τ = (CG.mk π₀).infChar τ` using `fun τ => by`. Rewrite using `[P.cg.inf, CGu.infChar, ← hmk]`.

Establish `hr₀ : (CG.mk π₀).IsRegAlg` using `(GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by`. Use `(D.naut.ralg_def π).1 hr τ` as an intermediate fact. Rewrite `this` using `[hinf]`. Then use the resulting hypothesis. Take `⟨r, wt, HT, H, hLG⟩` from `hC D.host.E D.nd.Om (D.nd.l i) (D.naut.iotaQC i) a ha π₀ hc₀ hr₀`. Establish `hcont : Continuous fun g => (r g : Matrix (Fin a) (Fin a) (Qbar (D.nd.l i)))` using `Units.continuous_val.comp H.cont`.

Establish `hloc : ∀ (w : PlE D.host) (u : ℝ), P.T.e w (D.naut.lpTw (D.naut.locG π w) u) = (_root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (CG.mk π₀) (D.nd.plOm.2 w)).lpTw u` using `fun w u => by`. Rewrite using `[P.T.tw, P.cg.loc, hmk]`. Both sides reduce to the same expression. Establish `haw` using `_root_.UpperTheory.GalS.Prod.core_data_of_point hF hL D P π π₀ hmk H`. Take `⟨K, ρ, hρc, hρ⟩` from `finextRep (D.nd.l i) D.host.E D.nd.Om a r hcont`.

Establish `hncw : ∀ w, Nc D.nd D.naut (D.naut.locG π w) → NcW ((_root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (CG.mk π₀) (D.nd.plOm.2 w)).lpTw ((1 - (a : ℝ)) / 2))` using `fun w k => by`. Rewrite using `[← hloc]`. Conclude with `ncW_of_nc P.T ((nc_tw _ _).2 k)`. Establish `hside : ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)), Nc D.nd D.naut (D.naut.locG π w) → P.wd.IsdRW (D.nd.l i) (D.naut.iotaQC i) r w ∧ ∀ τ : D.host.E →+* Qbar (D.nd.l i), (∀ (A : ValuationSubring D.nd.Om), IsPlaceOver A w → ∀ (O : Type) [CommRing O] [Algebra ℤ_[D.nd.l i] O] [Top …` using `D.host.E) A) O), Induces Bw → ∃ τ' : ↥Bw.Kw.1 →ₐ[ℚ_[D.nd.l i]] ↥Bw.LL.1, IsInduced Bw τ τ') → P.wd.jumpsW (D.nd.l i) (D.naut.iotaQC i) r τ = HT τ := by`. Introduce `w hw hn`.

Establish `hni` using `_root_.UpperTheory.GalS.nice_of_loc_par hL hF (D.nd.plOm.2 w) (hncw w hn)`. Take `⟨j, L0, hj, hLL⟩` from `GlobalTheory.PlaceBridge.exists_locBridge (D.nd.l i) D.host.E D.nd.Om w (D.nd.plOm.1 w) hw (D.nd.plOm.2 w)`. Take `⟨Bw, hBj, hBLL, -, hBto⟩` from `hLL L0 le_rfl`. Establish `hind : Induces Bw` using `fun x => by rw [hBj]; exact hj x`. Set `LL' : FinExt (D.nd.l i)` to `supExt K Bw.LL`.

Establish `hK : K.1 ≤ LL'.1` using `le_sup_left`. Establish `hB : Bw.LL.1 ≤ LL'.1` using `le_sup_right`. Set `ρ' : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin a) ↥LL'.1` to `mapRep (IntermediateField.inclusion hK).toRingHom ρ`. Establish `hρ' : mapRep (algebraMap ↥LL'.1 (Om (D.nd.l i))) ρ' = r`. Rewrite using `[← hρ]`.

Use extensionality with `g i k`. Both sides reduce to the same expression. Establish `hρ'c : Continuous fun g => (ρ' g : Matrix (Fin a) (Fin a) ↥LL'.1)`. Establish `hi : Continuous (IntermediateField.inclusion hK)` using `continuous_induced_rng.2 continuous_subtype_val`. Conclude with `hρc.matrix_map hi`.

Establish `hmodel : IsModel Bw (resDec D.nd.plOm.1 r w) LL' (ρ'.comp (Dec (F` using `D.host.E) (D.nd.plOm.1 w)).subtype) := ⟨hB, by rw [← hρ']; rfl⟩`. Set `φ : ↥(OL L0) →+* Qbar (D.nd.l i)` to `L0.1.val.toRingHom.comp (OL L0).val.toRingHom`. Establish `hφ : ∀ x, φ x = ((Bw.toLL x : ↥Bw.LL.1) : Om (D.nd.l i))` using `fun x => (hBto x).symm`. Establish `hcl` using `(P.wd.loc (D.nd.l i) (D.naut.iotaQC i) w hw _ Bw hind φ hφ).2 LL' hB a ρ' hρ'c`. Rewrite `hcl` using `[hρ']`.

Establish `hab` using `H.above (D.loc (D.nd.l i)) (D.locA (D.nd.l i)) ⟨D.locT (D.nd.l i)⟩ w (D.nd.plOm.1 w) (D.nd.plOm.2 w) _ Bw hind`. Establish `hdR : Bw.IsdRE (D.loc (D.nd.l i)) LL' (ρ'.comp (Dec (F` using `D.host.E) (D.nd.plOm.1 w)).subtype) := (hmodel.isdRAt_iff (D.loc (D.nd.l i))).1 (hab.deRham hni)`. Use `⟨hcl.2.1.2 hdR, fun τ hτ => ?_⟩` and prove the remaining obligations. Take `⟨τ₀, hτ₀⟩` from `hτ _ (D.nd.plOm.2 w) _ Bw hind`. Set `τ'' : ↥Bw.Kw.1 →ₐ[ℚ_[D.nd.l i]] ↥LL'.1` to `(IntermediateField.inclusion hB).comp τ₀`.

Establish `hτ'' : IsInduced Bw τ τ''` using `fun x => hτ₀ x`. Establish `hJ` using `hab.jumps hni τ LL' τ'' hτ''`. Use extensionality with `n`. Apply `Nat.cast_injective (R := ℤ)` to reduce the goal to its premises. Rewrite using `[(hcl.2.2.2 τ τ'' hτ'').2 hdR n, IsJumpsAt.count_eq (D.loc (D.nd.l i)) hmodel hτ'' hJ n]`.

Use `⟨r, hcont, H.ss, fun w hw => ?_, fun w hw hn => ⟨?_, fun τ hτw => ?_, ?_⟩⟩` and prove the remaining obligations. Use `relW_of_aw P.T ?_` and prove the remaining obligations. Rewrite using `[(P.wdOf i a r w).1, P.wd.away _ _ r w hw]`. Conclude with `haw w hw`. Conclude with `((P.wdOf i a r w).2.2.2.1).2 (hside w hw hn).1`.

Take `⟨w', hw', hτ⟩` from `existsIsInduced (D.nd.l i) D.host.E D.nd.Om τ`. Choose the witnesses or unpack the hypotheses as in `rfl : w' = w := by`. Take `⟨LL, Bw', hj', -⟩` from `P.wd.above _ (D.naut.iotaQC i) r w' hw'`. Take `⟨τ', h'⟩` from `hτ _ (D.nd.plOm.2 w') _ Bw' hj'`. Conclude with `HeightOneSpectrum.ext (Ideal.ext fun x => (induces_of_isInduced (D.nd.plOm.2 w') hj' h' x).symm.trans (hτw x))`.

Rewrite using `[(P.wdOf i a r w').2.2.2.2 τ, (hside w' hw' hn).2 τ hτ]`. Apply `Multiset.map_injective (f := fun n : ℤ => (n : ℂ)) Int.cast_injective` to reduce the goal to its premises. Rewrite using `[H.weights, D.naut.jumpsInf_def i π τ hr, hinf]`. Use `Multiset.map_congr rfl fun z _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[(P.wdOf i a r w).1]`. Take `⟨LL, Bw', hj', he⟩` from `P.wd.above _ (D.naut.iotaQC i) r w hw`. Take `⟨σ₀, hσ₀, -⟩` from `LocEx.exists_isLocComp hF _ _ π₀ w`. Establish `h2` using `hLG (D.loc _) (D.locA _) ⟨D.locT _⟩ w hw (D.nd.plOm.1 w) (D.nd.plOm.2 w) _ Bw' hj' σ₀ hσ₀ _ (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 w))`. Use `cuspA_of_ab P.T (by rw [D.naut.lpDim_tw, D.naut.locG_dim]; omega) ?_` and prove the remaining obligations.

Establish `e2 : _root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (D.nd.plOm.2 w) (algNorm σ₀) = P.T.e w (D.naut.lpTw (D.naut.locG π w) ((1 - (a : ℝ)) / 2))`. Rewrite using `[_root_.GlobalTheory.GalOfCusp.rec_algNorm_alt (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 w)) σ₀, hloc, _root_.GlobalTheory.CuspRep.ParLaws.local_parameter_eq_reciprocity_of_is_local_component hL hσ₀ (D.nd.plOm.2 w)]`. Both sides reduce to the same expression. Rewrite using `[he, ← e2]`. Conclude with `h2 (by rw [e2]; exact ncW_of_nc P.T ((nc_tw _ _).2 hn))`.
-/
theorem galRep_rankTwo_alt : GlobalTheory.Published.AutomorphicFormsFiniteGL → _root_.UpperTheory.GalS.CarUAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (i : D.nd.Loc) (a : ℕ), 2 ≤ a → ∀ π : D.naut.CG a, D.naut.csd π → D.naut.ralg π → ∃ ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin a) (Qbar (D.nd.l i)), Formalism.MainNotions.SumRepresentations.At.ContQ D.nd i ρ ∧ IsSSRep ρ ∧ (∀ w, w ∉ placesOver D.host.E (D.nd.l i) → RelW D.nd D.naut (D.naut.wdOf i ρ w) (D.naut.lpTw (D.naut.locG π w) ((1 - (a : ℝ)) / 2))) ∧ (∀ w ∈ placesOver D.host.E (D.nd.l i), Nc D.nd D.naut (D.naut.locG π w) → D.naut.IsdRW i ρ w ∧ (∀ τ, InducesW D.nd i τ w → D.naut.jumpsW i ρ τ = D.naut.jumpsInf i π τ) ∧ UpperTheory.GalN.CuspA D.nd D.naut (D.naut.wdOf i ρ w) (D.naut.lpTw (D.naut.locG π w) ((1 - (a : ℝ)) / 2))) := by
  intro hF hC hL D P i a ha π hc hr
  have := host_isCMField D.host
  obtain ⟨π₀, hπ₀⟩ := Quotient.exists_rep (P.cg.e a π).1
  have hmk : CG.mk π₀ = (P.cg.e a π).1 := hπ₀
  have hc₀ : π₀.IsCsd := by
    have h1 := (P.cg.csd a π).1 hc
    rw [CGu.IsCsd, ← hmk] at h1
    exact h1
  have hinf : ∀ τ, D.naut.infG π τ = (CG.mk π₀).infChar τ := fun τ => by
    rw [P.cg.inf, CGu.infChar, ← hmk]
  have hr₀ : (CG.mk π₀).IsRegAlg := (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by
    have := (D.naut.ralg_def π).1 hr τ
    rwa [hinf] at this
  obtain ⟨r, wt, HT, H, hLG⟩ := hC D.host.E D.nd.Om (D.nd.l i) (D.naut.iotaQC i) a ha π₀ hc₀ hr₀
  have hcont : Continuous fun g => (r g : Matrix (Fin a) (Fin a) (Qbar (D.nd.l i))) := Units.continuous_val.comp H.cont
  have hloc : ∀ (w : PlE D.host) (u : ℝ), P.T.e w (D.naut.lpTw (D.naut.locG π w) u) =
      (_root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (CG.mk π₀) (D.nd.plOm.2 w)).lpTw u := fun w u => by
    rw [P.T.tw, P.cg.loc, hmk]
    rfl
  have haw := _root_.UpperTheory.GalS.Prod.core_data_of_point hF hL D P π π₀ hmk H
  obtain ⟨K, ρ, hρc, hρ⟩ := finextRep (D.nd.l i) D.host.E D.nd.Om a r hcont
  have hncw : ∀ w, Nc D.nd D.naut (D.naut.locG π w) →
      NcW ((_root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (CG.mk π₀) (D.nd.plOm.2 w)).lpTw ((1 - (a : ℝ)) / 2)) := fun w k => by
    rw [← hloc]; exact ncW_of_nc P.T ((nc_tw _ _).2 k)
  have hside : ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)), Nc D.nd D.naut (D.naut.locG π w) → P.wd.IsdRW (D.nd.l i) (D.naut.iotaQC i) r w ∧
      ∀ τ : D.host.E →+* Qbar (D.nd.l i), (∀ (A : ValuationSubring D.nd.Om), IsPlaceOver A w →
        ∀ (O : Type) [CommRing O] [Algebra ℤ_[D.nd.l i] O] [TopologicalSpace O]
          (Bw : LocBridge (D.nd.l i) D.host.E D.nd.Om (Dec (F := D.host.E) A) O),
          Induces Bw → ∃ τ' : ↥Bw.Kw.1 →ₐ[ℚ_[D.nd.l i]] ↥Bw.LL.1, IsInduced Bw τ τ') →
        P.wd.jumpsW (D.nd.l i) (D.naut.iotaQC i) r τ = HT τ := by
    intro w hw hn
    have hni := _root_.UpperTheory.GalS.nice_of_loc_par hL hF (D.nd.plOm.2 w) (hncw w hn)
    obtain ⟨j, L0, hj, hLL⟩ := GlobalTheory.PlaceBridge.exists_locBridge (D.nd.l i) D.host.E D.nd.Om w (D.nd.plOm.1 w) hw
      (D.nd.plOm.2 w)
    obtain ⟨Bw, hBj, hBLL, -, hBto⟩ := hLL L0 le_rfl
    have hind : Induces Bw := fun x => by rw [hBj]; exact hj x
    let LL' : FinExt (D.nd.l i) := supExt K Bw.LL
    have hK : K.1 ≤ LL'.1 := le_sup_left
    have hB : Bw.LL.1 ≤ LL'.1 := le_sup_right
    let ρ' : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin a) ↥LL'.1 := mapRep (IntermediateField.inclusion hK).toRingHom ρ
    have hρ' : mapRep (algebraMap ↥LL'.1 (Om (D.nd.l i))) ρ' = r := by
      rw [← hρ]
      ext g i k
      rfl
    have hρ'c : Continuous fun g => (ρ' g : Matrix (Fin a) (Fin a) ↥LL'.1) := by
      have hi : Continuous (IntermediateField.inclusion hK) :=
        continuous_induced_rng.2 continuous_subtype_val
      exact hρc.matrix_map hi
    have hmodel : IsModel Bw (resDec D.nd.plOm.1 r w) LL' (ρ'.comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype) :=
      ⟨hB, by rw [← hρ']; rfl⟩
    let φ : ↥(OL L0) →+* Qbar (D.nd.l i) := L0.1.val.toRingHom.comp (OL L0).val.toRingHom
    have hφ : ∀ x, φ x = ((Bw.toLL x : ↥Bw.LL.1) : Om (D.nd.l i)) := fun x => (hBto x).symm
    have hcl := (P.wd.loc (D.nd.l i) (D.naut.iotaQC i) w hw _ Bw hind φ hφ).2 LL' hB a ρ' hρ'c
    rw [hρ'] at hcl
    have hab := H.above (D.loc (D.nd.l i)) (D.locA (D.nd.l i)) ⟨D.locT (D.nd.l i)⟩ w (D.nd.plOm.1 w) (D.nd.plOm.2 w) _ Bw hind
    have hdR : Bw.IsdRE (D.loc (D.nd.l i)) LL' (ρ'.comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype) :=
      (hmodel.isdRAt_iff (D.loc (D.nd.l i))).1 (hab.deRham hni)
    refine ⟨hcl.2.1.2 hdR, fun τ hτ => ?_⟩
    obtain ⟨τ₀, hτ₀⟩ := hτ _ (D.nd.plOm.2 w) _ Bw hind
    let τ'' : ↥Bw.Kw.1 →ₐ[ℚ_[D.nd.l i]] ↥LL'.1 := (IntermediateField.inclusion hB).comp τ₀
    have hτ'' : IsInduced Bw τ τ'' := fun x => hτ₀ x
    have hJ := hab.jumps hni τ LL' τ'' hτ''
    ext n
    apply Nat.cast_injective (R := ℤ)
    rw [(hcl.2.2.2 τ τ'' hτ'').2 hdR n, IsJumpsAt.count_eq (D.loc (D.nd.l i)) hmodel hτ'' hJ n]
  refine ⟨r, hcont, H.ss, fun w hw => ?_, fun w hw hn => ⟨?_, fun τ hτw => ?_, ?_⟩⟩
  · refine relW_of_aw P.T ?_
    rw [(P.wdOf i a r w).1, P.wd.away _ _ r w hw]
    exact haw w hw
  · exact ((P.wdOf i a r w).2.2.2.1).2 (hside w hw hn).1
  · obtain ⟨w', hw', hτ⟩ := existsIsInduced (D.nd.l i) D.host.E D.nd.Om τ
    obtain rfl : w' = w := by
      obtain ⟨LL, Bw', hj', -⟩ := P.wd.above _ (D.naut.iotaQC i) r w' hw'
      obtain ⟨τ', h'⟩ := hτ _ (D.nd.plOm.2 w') _ Bw' hj'
      exact HeightOneSpectrum.ext (Ideal.ext fun x => (induces_of_isInduced (D.nd.plOm.2 w') hj' h' x).symm.trans (hτw x))
    rw [(P.wdOf i a r w').2.2.2.2 τ, (hside w' hw' hn).2 τ hτ]
    apply Multiset.map_injective (f := fun n : ℤ => (n : ℂ)) Int.cast_injective
    rw [H.weights, D.naut.jumpsInf_def i π τ hr, hinf]
    refine Multiset.map_congr rfl fun z _ => ?_
    ring
  · rw [(P.wdOf i a r w).1]
    obtain ⟨LL, Bw', hj', he⟩ := P.wd.above _ (D.naut.iotaQC i) r w hw
    obtain ⟨σ₀, hσ₀, -⟩ := LocEx.exists_isLocComp hF _ _ π₀ w
    have h2 := hLG (D.loc _) (D.locA _)
      ⟨D.locT _⟩ w hw (D.nd.plOm.1 w) (D.nd.plOm.2 w) _ Bw' hj' σ₀ hσ₀ _ (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 w))
    refine cuspA_of_ab P.T (by rw [D.naut.lpDim_tw, D.naut.locG_dim]; omega) ?_
    have e2 : _root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (D.nd.plOm.2 w) (algNorm σ₀) =
        P.T.e w (D.naut.lpTw (D.naut.locG π w) ((1 - (a : ℝ)) / 2)) := by
      rw [_root_.GlobalTheory.GalOfCusp.rec_algNorm_alt (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 w)) σ₀, hloc, _root_.GlobalTheory.CuspRep.ParLaws.local_parameter_eq_reciprocity_of_is_local_component hL hσ₀ (D.nd.plOm.2 w)]
      rfl
    rw [he, ← e2]
    exact h2 (by rw [e2]; exact ncW_of_nc P.T ((nc_tw _ _).2 hn))
/- English proof (translation)
Introduce `i`. Use `⟨fun a ha π hc hr => ?_, fun a π hr => _root_.GlobalTheory.GalClose.purity_alt hPr.clo hL D P a π hr, fun χ s hs => ?_⟩` and prove the remaining obligations. Break down `Nat.lt_or_ge a 2 with ha2 | ha2` into its components or cases. Take `rfl : a = 1` from `by omega`. Take `⟨ρ, c, s, o, u⟩` from `_root_.GlobalTheory.GalClose.rankOne_galois_closure_geometric_alt hPr hL D P i π hr`.

Use `⟨ρ, c, s, fun w hw => RelW.of_eq (o w hw).1, fun w hw _ => ⟨(u w hw).1, (u w hw).2.1, UpperTheory.GalN.CuspA.of_eq (u w hw).2.2⟩, fun _ w => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hw : w ∈ placesOver D.host.E (D.nd.l i)`. Conclude with `(u w hw).2.2`. Conclude with `(o w hw).1`. Take `⟨ρ, c, s, o, u⟩` from `_root_.UpperTheory.GalS.Prod.galRep_rankTwo_alt hPr.fin hC hL D P i a ha2 π hc hr`.

Conclude with `⟨ρ, c, s, o, fun w hw k => u w hw (k.resolve_left (by omega)), fun e => absurd e (by omega)⟩`. Conclude with `_root_.GlobalTheory.T.exists_galois_character_of_algebraic_alt hPr.fin hPr.art hPr.chA hPr.chP hL D P i χ s hs`.
-/
theorem automorphic_galois_admissible_of_theta_local_inputs (hPr : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt) (hC : _root_.UpperTheory.GalS.CarUAlt) (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) :
    AutomorphicGaloisAdmissible D.nd D.naut := by
  intro i
  refine ⟨fun a ha π hc hr => ?_, fun a π hr => _root_.GlobalTheory.GalClose.purity_alt hPr.clo hL D P a π hr, fun χ s hs => ?_⟩
  · rcases Nat.lt_or_ge a 2 with ha2 | ha2
    · obtain rfl : a = 1 := by omega
      obtain ⟨ρ, c, s, o, u⟩ := _root_.GlobalTheory.GalClose.rankOne_galois_closure_geometric_alt hPr hL D P i π hr
      refine ⟨ρ, c, s, fun w hw => RelW.of_eq (o w hw).1, fun w hw _ => ⟨(u w hw).1, (u w hw).2.1, UpperTheory.GalN.CuspA.of_eq (u w hw).2.2⟩, fun _ w => ?_⟩
      by_cases hw : w ∈ placesOver D.host.E (D.nd.l i)
      · exact (u w hw).2.2
      · exact (o w hw).1
    · obtain ⟨ρ, c, s, o, u⟩ := _root_.UpperTheory.GalS.Prod.galRep_rankTwo_alt hPr.fin hC hL D P i a ha2 π hc hr
      exact ⟨ρ, c, s, o, fun w hw k => u w hw (k.resolve_left (by omega)), fun e => absurd e (by omega)⟩
  · exact _root_.GlobalTheory.T.exists_galois_character_of_algebraic_alt hPr.fin hPr.art hPr.chA hPr.chP hL D P i χ s hs
end UpperTheory.GalS.Prod
end
end
