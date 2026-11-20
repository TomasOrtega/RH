import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
import Development.AbelianVarietyTheory.Statements.HaarFundamentalDomain.ExistsHaarFundDom
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPlacewiseSeesawTripleOverHermitianStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjUMeasurableEmbedding
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawUnfoldingDoubling
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLieDerivativePolynomialFockSeesaw
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOneParamSubgroupTransposeGramLieAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOneParameterSubgroupTransposeGramRealPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareCommutationIntegralIdentityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdmissibleFormConvergentThetaIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedTripleGlobalLiftIdentity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialDataDecomposesAtFinitePlaces

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.ChainFr MeasureTheory

noncomputable section

namespace GlobalTheory.ConvThetaNe

open GlobalTheory.SquareAgree GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

section Over

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {W W₁ X : HSp D} {A : Fr W} {A₁ : Fr W₁} {B : Fr X}
  {α β : (AE D)ˣ →* Circle} {ν : Measure (GA D W)} {𝓕 : Set (GA D W)} {ν₁ : Measure (GA D W₁)} {𝓕₁ : Set (GA D W₁)}
  {ωA : WRep W X} {ωB : WRep W₁ X} {e : Fin X.rank ≃ Fin (W.rank + W₁.rank)}
  {Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E} {Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank}
  {Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E} {om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W}
  {om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W}
  {cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X}
  {cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X}

/- English proof (translation)
The claim follows from `thetaInt_eq_modelI D W X _ _ _ Γ.M 1 hO.JW ν 𝓕 ωA om (kapX X e hO.JX) ΦD Φ hO.measW hO.domW (hO.theta_eq_A hD) h`.
-/
theorem int_eq (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB) {ΦD : _} {Φ : WO W X → ℂ}
    (hD : IsDatum Γ.M ψ cA ΦD Φ) (h : GA D X) : thetaInt ωA ν 𝓕 Φ h = Γ.M.I om ΦD (kapX X e hO.JX h) :=
  thetaInt_eq_modelI D W X _ _ _ Γ.M 1 hO.JW ν 𝓕 ωA om (kapX X e hO.JX) ΦD Φ hO.measW hO.domW (hO.theta_eq_A hD) h

/- English proof (translation)
Take `⟨ΦD, -, hD⟩` from `hO.algA Φ hΦ`. Establish `he` using `conjU_measurableEmbedding W 1 hO.JW`. Establish `h1` using `hC ΦD hD.1 (kapX X e hO.JX h)`. Rewrite `h1` using `[hO.measW, hO.domW, he.integrableOn_map_iff, Set.preimage_image_eq _ he.injective]`. Establish `e1 : (fun g => thetaKO ωA g h Φ) = (fun g => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta om ΦD g (kapX X e hO.JX h)) ∘ GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 hO.JW` using `funext fun g => (hO.theta_eq_A hD g h).symm`.

Rewrite using `[e1]`. Conclude with `h1`.
-/
theorem integrable_big (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB)
    (hC : ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F _, Γ.M.Conv om Φ) {Φ : WO W X → ℂ} (hΦ : Φ ∈ algF ψ θ true A B) (h : GA D X) :
    IntegrableOn (fun g => thetaKO ωA g h Φ) 𝓕 ν := by
  obtain ⟨ΦD, -, hD⟩ := hO.algA Φ hΦ
  have he := conjU_measurableEmbedding W 1 hO.JW
  have h1 := hC ΦD hD.1 (kapX X e hO.JX h)
  rw [hO.measW, hO.domW, he.integrableOn_map_iff, Set.preimage_image_eq _ he.injective] at h1
  have e1 : (fun g => thetaKO ωA g h Φ) = (fun g => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta om ΦD g (kapX X e hO.JX h)) ∘
      GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 hO.JW := funext fun g => (hO.theta_eq_A hD g h).symm
  rw [e1]
  exact h1

/- English proof (translation)
Take `⟨γ, hγ, hγt⟩` from `GlobalTheory.KapXLine.exists_line D θ X τ Y hθ hY e Γ.W hO.JX`. Take `⟨δ, hδ⟩` from `GlobalTheory.OscLie.exists_lie_deriv_pol Bs Γ Xc om om' hT γ hγ`. Take `⟨ΦD, hΦD, hD⟩` from `hO.algA Φ hΦ`. Take `⟨Φ'D, -, hD'⟩` from `hO.algA Φ' hΦ'`. Establish `hPD : ΦD ∈ GlobalTheory.ThK.PolData Bs Γ.M`.

Use `Submodule.span_mono ?_ hΦD` and prove the remaining obligations. Introduce and unpack `_ ⟨f, φ, h1, h2, h3, rfl⟩`. Conclude with `⟨f, h1, φ, h2, h3, rfl⟩`. Take `⟨T, m, f, φ, hf, rfl⟩` from `GlobalTheory.ThK.CycGen.exists_decOn_some Γ.M ΦD hPD`. Establish `e1` using `GlobalTheory.SquareAgree.DatA.datum_lieDer hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hO hT τ Y γ hγt hγ Φ Φ' hd T m f (fun i => δ (f i)) φ hf (fun i => (hδ _ (hf i).1).2) hD Φ'D hD'`.

Take `⟨l, hla, hl⟩` from `GlobalTheory.ThetaIntAdm.exists_admissible_form_convergent_thetaIntegral Γ.M Bs.ψ _ _ om hT.weil hC`. Take `⟨Φ₁, -, hp, hI⟩` from `GlobalTheory.ThetaIntegralLine.exists_deriv hP Γ.M Bs.ψ _ _ om hT.base.cm hT.base.std hT.weil hC (fun g hg x => by`. Take `⟨L, hL⟩` from `hT.weil.isUSplitting.adm (1, x) l hla g hg`. Use `L.continuous.congr fun u => ?_` and prove the remaining obligations. Rewrite using `[GlobalTheory.BigNZ.I_eq_l hT hl (Submodule.subset_span ⟨u, g, hg, rfl⟩), ← hL u]`.

Use the proof step `rfl) hγ hD.1`. Establish `hM` using `hT.geo.hM`. Establish `hrest : ∀ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (⇑(f i)) (GlobalTheory.EvZeroInf.finPart (φ i))` using `fun i => ⟨fun x z hz => GlobalTheory.EvZeroInf.finPart_add _ x z hz, by`. Rewrite using `[← GlobalTheory.EvZeroInf.pure_eq_tens]`. Conclude with `(GlobalTheory.BigNZ.IsFinPart.fam (M := Γ.M) (T := T) (hf i).2).mem hM _⟩`.

Establish `e2 : Φ₁ = Φ'D`. Use function extensionality and compare the values at `x`. Use `(hp x).unique ?_` and prove the remaining obligations. Rewrite using `[e1]`. Simplify using `only [map_sum, Finset.sum_apply, GlobalTheory.EvZeroInf.pure_eq_tens]`.

Conclude with `HasDerivAt.fun_sum fun i _ => (hδ _ (hf i).1).2 _ (hrest i) x`. Use `hI (kapX X e hO.JX h)` as an intermediate fact. Rewrite `this` using `[e2]`. Simplify using `only [int_eq hO hD, int_eq hO hD', GlobalTheory.KapXLine.kapX_mul, ← hγt]`. Conclude with `this`.
-/
theorem hasDerivAt_big (hP : GlobalTheory.FunPr.Hypotheses₂) (hθ : IsInfFam θ)
    (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB) (hT : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om')
    (hC : ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F _, Γ.M.Conv om Φ) {τ : D.what₂.Tau} {Y : Matrix (Fin X.rank) (Fin X.rank) ℂ}
    (hY : Y ∈ lieAt X τ) {Φ Φ' : WO W X → ℂ} (hΦ : Φ ∈ algF ψ θ true A B) (hΦ' : Φ' ∈ algF ψ θ true A B)
    (hd : IsDer θ X (fun h => ωA (1, h)) τ Y Φ Φ') (h : GA D X) :
    HasDerivAt (fun t : ℝ => thetaInt ωA ν 𝓕 Φ (h * oneP θ X τ Y t)) (thetaInt ωA ν 𝓕 Φ' h) 0 := by
  obtain ⟨γ, hγ, hγt⟩ := GlobalTheory.KapXLine.exists_line D θ X τ Y hθ hY e Γ.W hO.JX
  obtain ⟨δ, hδ⟩ := GlobalTheory.OscLie.exists_lie_deriv_pol Bs Γ Xc om om' hT γ hγ
  obtain ⟨ΦD, hΦD, hD⟩ := hO.algA Φ hΦ
  obtain ⟨Φ'D, -, hD'⟩ := hO.algA Φ' hΦ'
  have hPD : ΦD ∈ GlobalTheory.ThK.PolData Bs Γ.M := by
    refine Submodule.span_mono ?_ hΦD
    rintro _ ⟨f, φ, h1, h2, h3, rfl⟩
    exact ⟨f, h1, φ, h2, h3, rfl⟩
  obtain ⟨T, m, f, φ, hf, rfl⟩ := GlobalTheory.ThK.CycGen.exists_decOn_some Γ.M ΦD hPD
  have e1 := GlobalTheory.SquareAgree.DatA.datum_lieDer hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hO hT τ Y γ
    hγt hγ Φ Φ' hd T m f (fun i => δ (f i)) φ hf (fun i => (hδ _ (hf i).1).2) hD Φ'D hD'
  obtain ⟨l, hla, hl⟩ := GlobalTheory.ThetaIntAdm.exists_admissible_form_convergent_thetaIntegral Γ.M Bs.ψ _ _ om hT.weil hC
  obtain ⟨Φ₁, -, hp, hI⟩ := GlobalTheory.ThetaIntegralLine.exists_deriv hP Γ.M Bs.ψ _ _ om hT.base.cm hT.base.std hT.weil hC
    (fun g hg x => by
      obtain ⟨L, hL⟩ := hT.weil.isUSplitting.adm (1, x) l hla g hg
      refine L.continuous.congr fun u => ?_
      rw [GlobalTheory.BigNZ.I_eq_l hT hl (Submodule.subset_span ⟨u, g, hg, rfl⟩), ← hL u]
      rfl) hγ hD.1
  have hM := hT.geo.hM
  have hrest : ∀ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (⇑(f i)) (GlobalTheory.EvZeroInf.finPart (φ i)) := fun i =>
    ⟨fun x z hz => GlobalTheory.EvZeroInf.finPart_add _ x z hz, by
      rw [← GlobalTheory.EvZeroInf.pure_eq_tens]
      exact (GlobalTheory.BigNZ.IsFinPart.fam (M := Γ.M) (T := T) (hf i).2).mem hM _⟩
  have e2 : Φ₁ = Φ'D := by
    funext x
    refine (hp x).unique ?_
    rw [e1]
    simp only [map_sum, Finset.sum_apply, GlobalTheory.EvZeroInf.pure_eq_tens]
    exact HasDerivAt.fun_sum fun i _ => (hδ _ (hf i).1).2 _ (hrest i) x
  have := hI (kapX X e hO.JX h)
  rw [e2] at this
  simp only [int_eq hO hD, int_eq hO hD', GlobalTheory.KapXLine.kapX_mul, ← hγt]
  exact this

/- English proof (translation)
Take `⟨R, Rf, hm⟩` from `hL _ _ _ Bs _ _ Γ Xc om om' hT`. Take `⟨dec, hk⟩` from `hK.1 _ _ _ Bs _ _ Γ Xc om om' hT`. Take `⟨hc, hco⟩` from `hk R Rf hm`. Take `⟨l, hla, hl⟩` from `GlobalTheory.ThetaIntAdm.exists_admissible_form_convergent_thetaIntegral Γ.M Bs.ψ _ _ om hT.weil dec.1`. Take `⟨f, hf, φ, hφ, hne⟩` from `GlobalTheory.BigNZ.exists_I_ne_zero hm hc hco hla hl`.

Take `⟨Φ, hΦ, hD⟩` from `hO.algA' _ (Submodule.subset_span ⟨f, φ, hf, hφ.fam.1, hφ.fam.2, rfl⟩)`. Use `⟨Φ, hΦ, fun h0 => hne (funext fun x => ?_)⟩` and prove the remaining obligations. Take `⟨h, rfl⟩` from `GlobalTheory.LineAtPlace.kapX_surj X e hO.JX x`. Rewrite using `[← int_eq hO hD, h0]`. Both sides reduce to the same expression.
-/
theorem exists_big_ne (hK : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree) (hL : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching)
    (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB) (hT : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om') :
    ∃ Φ ∈ algF ψ θ true A B, thetaInt ωA ν 𝓕 Φ ≠ 0 := by
  obtain ⟨R, Rf, hm⟩ := hL _ _ _ Bs _ _ Γ Xc om om' hT
  obtain ⟨dec, hk⟩ := hK.1 _ _ _ Bs _ _ Γ Xc om om' hT
  obtain ⟨hc, hco⟩ := hk R Rf hm
  obtain ⟨l, hla, hl⟩ := GlobalTheory.ThetaIntAdm.exists_admissible_form_convergent_thetaIntegral Γ.M Bs.ψ _ _ om hT.weil dec.1
  obtain ⟨f, hf, φ, hφ, hne⟩ := GlobalTheory.BigNZ.exists_I_ne_zero hm hc hco hla hl
  obtain ⟨Φ, hΦ, hD⟩ := hO.algA' _ (Submodule.subset_span ⟨f, φ, hf, hφ.fam.1, hφ.fam.2, rfl⟩)
  refine ⟨Φ, hΦ, fun h0 => hne (funext fun x => ?_)⟩
  obtain ⟨h, rfl⟩ := GlobalTheory.LineAtPlace.kapX_surj X e hO.JX x
  rw [← int_eq hO hD, h0]
  rfl

end Over

/- English proof (translation)
Introduce `hP hK hL D ψ θ hψ hθ W W₁ X A A₁ B α β hT ν₁ 𝓕₁ hν₁ ωA ωB Pm rf rl p p' hm Φ' hΦ' hint' hp' h0'`. Take `⟨ν, 𝓕, hν⟩` from `GlobalTheory.Ker.HypModel.exists_haar_fundDom D W`. Take `⟨e, Bs, Γ, Xc, om, om', cA, cB, hO, hTD⟩` from `GlobalTheory.T.exists_placewise_seesaw_triple_over_hermitian D ψ θ hθ W W₁ X A A₁ B α β hT ν 𝓕 ν₁ 𝓕₁ hν hν₁ ωA ωB hm.weilA hm.weilB`. Establish `hC` using `(hK.1 _ _ _ Bs _ _ Γ Xc om om' hTD).1.1`. Take `⟨c, -, hc⟩` from `GlobalTheory.T.square_commutation_integral_identity hP hK hL D ψ θ hψ hθ W W₁ X A A₁ B α β hT ν 𝓕 ν₁ 𝓕₁ hν hν₁ ωA ωB Pm rf rl p p' hm`.

Use `set S := algF ψ θ true A B with hS`. Establish `hint : ∀ Φ ∈ S, ∀ h, IntegrableOn (fun g => thetaKO ωA g h Φ) 𝓕 ν` using `fun Φ hΦ h => integrable_big hO hC hΦ h`. Establish `tr : ∀ (Φ : WO W X → ℂ) (h k : GA D X), thetaInt ωA ν 𝓕 (ωA (1, k) Φ) h = thetaInt ωA ν 𝓕 Φ (h * k)`. Introduce `Φ h k`. Simplify using `only [thetaInt, thetaKO, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]`.

Establish `tadd : ∀ Φ ∈ S, ∀ Ψ ∈ S, thetaInt ωA ν 𝓕 (Φ + Ψ) = thetaInt ωA ν 𝓕 Φ + thetaInt ωA ν 𝓕 Ψ`. Introduce `Φ hΦ Ψ hΨ`. Use function extensionality and compare the values at `h`. Establish `e : (fun g => thetaKO ωA g h (Φ + Ψ)) = fun g => thetaKO ωA g h Φ + thetaKO ωA g h Ψ`. Use function extensionality and compare the values at `g`.

Simplify using `[thetaKO, map_add]`. Simplify using `only [thetaInt, Pi.add_apply]`. Rewrite using `[e]`. Conclude with `integral_add (hint Φ hΦ h) (hint Ψ hΨ h)`. Establish `tsmul : ∀ (s : ℂ) Φ, thetaInt ωA ν 𝓕 (s • Φ) = s • thetaInt ωA ν 𝓕 Φ`.

Introduce `s Φ`. Use function extensionality and compare the values at `h`. Establish `e : (fun g => thetaKO ωA g h (s • Φ)) = fun g => s * thetaKO ωA g h Φ`. Use function extensionality and compare the values at `g`. Simplify using `[thetaKO, map_smul]`.

Simplify using `only [thetaInt, Pi.smul_apply, smul_eq_mul]`. Rewrite using `[e]`. Conclude with `integral_const_mul s _`. Set `K : Submodule ℂ (WO W X → ℂ)` to `{ carrier := {Φ | Φ ∈ S ∧ thetaInt ωA ν 𝓕 Φ = 0} add_mem' := fun {a b} ha hb => ⟨S.add_mem ha.1 hb.1, by rw [tadd a ha.1 b hb.1, ha.2, hb.2, add_zero]⟩ zero_mem' := ⟨S.zero_mem, by funext h; simp [thetaInt, thetaKO]⟩ smul_mem' := fun s a ha => ⟨S.smul_mem s ha.1, by rw [tsmul, ha …`. Establish `kill : ∀ Ψ ∈ S, p Ψ = 0 → thetaInt ωA ν 𝓕 Ψ = 0` using `fun Ψ hΨ h0 => by`.

Rewrite using `[hc Ψ hΨ 0 (zero_mem _) (fun h => by simp [thetaKO]) (by rw [h0, map_zero])]`. Use function extensionality and compare the values at `h`. Simplify using `[thetaInt, thetaKO]`. Establish `stf : ∀ g ∈ GfC X, ∀ x ∈ K.map p, rf g x ∈ K.map p`. Introduce and unpack `g hg _ ⟨Ψ, ⟨hΨS, hΨ0⟩, rfl⟩`.

Use `⟨ωA (1, g) Ψ, ⟨hm.mapA.stabX.1 g hg Ψ hΨS, ?_⟩, hm.mapA.eqf g hg Ψ hΨS⟩` and prove the remaining obligations. Use function extensionality and compare the values at `h`. Rewrite using `[tr, hΨ0]`. Both sides reduce to the same expression. Establish `stl : ∀ τ, ∀ Y ∈ lieAt X τ, ∀ x ∈ K.map p, rl τ Y x ∈ K.map p`.

Introduce and unpack `τ Y hY _ ⟨Ψ, ⟨hΨS, hΨ0⟩, rfl⟩`. Take `⟨Ψ', hΨ'S, hder⟩` from `hm.mapA.stabX.2 τ Y hY Ψ hΨS`. Use `⟨Ψ', ⟨hΨ'S, funext fun h => ?_⟩, hm.mapA.eql τ Y hY Ψ hΨS Ψ' hΨ'S hder⟩` and prove the remaining obligations. Establish `h1` using `hasDerivAt_big hP hθ hO hTD hC hY hΨS hΨ'S hder h`. Rewrite `h1` using `[hΨ0]`.

Conclude with `h1.unique (hasDerivAt_const (0 : ℝ) (0 : ℂ))`. Break down `hm.irred.2 (K.map p) stf stl with hbot | htop` into its components or cases. Take `⟨Φ, hΦ, hpΦ⟩ : p' Φ' ∈ S.map p` from `hm.mapA.onto ▸ Submodule.mem_top`. Establish `h1 : p Φ ∈ K.map p` using `⟨Φ, ⟨hΦ, by rw [hc Φ hΦ Φ' hΦ' hint' hpΦ, h0', smul_zero]⟩, rfl⟩`. Rewrite `h1` using `[hbot, Submodule.mem_bot, hpΦ]`.

Conclude with `hp' h1`. Take `⟨Φ, hΦ, hne⟩` from `exists_big_ne hK hL hO hTD`. Take `⟨Ψ, ⟨hΨS, hΨ0⟩, hΨp⟩ : p Φ ∈ K.map p` from `by rw [htop]; exact Submodule.mem_top`. Establish `h1` using `tadd _ (S.sub_mem hΦ hΨS) Ψ hΨS`. Rewrite `h1` using `[sub_add_cancel, kill _ (S.sub_mem hΦ hΨS) (by rw [map_sub, hΨp, sub_self]), hΨ0, add_zero]`.

Conclude with `hne h1`.
-/
theorem thetaInt_ne_zero : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β →
  ∀ (ν₁ : Measure (GA D W₁)) (𝓕₁ : Set (GA D W₁)), IsHaarFD W₁ ν₁ 𝓕₁ →
  ∀ ωA ωB Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
  ∀ Φ' ∈ algF ψ θ false A₁ B, (∀ h, IntegrableOn (fun g => thetaKO ωB g h Φ') 𝓕₁ ν₁) → p' Φ' ≠ 0 → thetaInt ωB ν₁ 𝓕₁ Φ' ≠ 0 := by
  intro hP hK hL D ψ θ hψ hθ W W₁ X A A₁ B α β hT ν₁ 𝓕₁ hν₁ ωA ωB Pm rf rl p p' hm Φ' hΦ' hint' hp' h0'
  obtain ⟨ν, 𝓕, hν⟩ := GlobalTheory.Ker.HypModel.exists_haar_fundDom D W
  obtain ⟨e, Bs, Γ, Xc, om, om', cA, cB, hO, hTD⟩ :=
    GlobalTheory.T.exists_placewise_seesaw_triple_over_hermitian D ψ θ hθ W W₁ X A A₁ B α β hT ν 𝓕 ν₁ 𝓕₁ hν hν₁ ωA ωB hm.weilA hm.weilB
  have hC := (hK.1 _ _ _ Bs _ _ Γ Xc om om' hTD).1.1
  obtain ⟨c, -, hc⟩ := GlobalTheory.T.square_commutation_integral_identity hP hK hL D ψ θ hψ hθ W W₁ X A A₁ B α β hT ν 𝓕 ν₁ 𝓕₁ hν hν₁ ωA ωB Pm rf rl p p' hm
  set S := algF ψ θ true A B with hS
  have hint : ∀ Φ ∈ S, ∀ h, IntegrableOn (fun g => thetaKO ωA g h Φ) 𝓕 ν := fun Φ hΦ h => integrable_big hO hC hΦ h
  have tr : ∀ (Φ : WO W X → ℂ) (h k : GA D X), thetaInt ωA ν 𝓕 (ωA (1, k) Φ) h = thetaInt ωA ν 𝓕 Φ (h * k) := by
    intro Φ h k
    simp only [thetaInt, thetaKO, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
  have tadd : ∀ Φ ∈ S, ∀ Ψ ∈ S, thetaInt ωA ν 𝓕 (Φ + Ψ) = thetaInt ωA ν 𝓕 Φ + thetaInt ωA ν 𝓕 Ψ := by
    intro Φ hΦ Ψ hΨ; funext h
    have e : (fun g => thetaKO ωA g h (Φ + Ψ)) = fun g => thetaKO ωA g h Φ + thetaKO ωA g h Ψ := by
      funext g; simp [thetaKO, map_add]
    simp only [thetaInt, Pi.add_apply]
    rw [e]
    exact integral_add (hint Φ hΦ h) (hint Ψ hΨ h)
  have tsmul : ∀ (s : ℂ) Φ, thetaInt ωA ν 𝓕 (s • Φ) = s • thetaInt ωA ν 𝓕 Φ := by
    intro s Φ; funext h
    have e : (fun g => thetaKO ωA g h (s • Φ)) = fun g => s * thetaKO ωA g h Φ := by
      funext g; simp [thetaKO, map_smul]
    simp only [thetaInt, Pi.smul_apply, smul_eq_mul]
    rw [e]
    exact integral_const_mul s _
  let K : Submodule ℂ (WO W X → ℂ) :=
    { carrier := {Φ | Φ ∈ S ∧ thetaInt ωA ν 𝓕 Φ = 0}
      add_mem' := fun {a b} ha hb => ⟨S.add_mem ha.1 hb.1, by rw [tadd a ha.1 b hb.1, ha.2, hb.2, add_zero]⟩
      zero_mem' := ⟨S.zero_mem, by funext h; simp [thetaInt, thetaKO]⟩
      smul_mem' := fun s a ha => ⟨S.smul_mem s ha.1, by rw [tsmul, ha.2, smul_zero]⟩ }
  have kill : ∀ Ψ ∈ S, p Ψ = 0 → thetaInt ωA ν 𝓕 Ψ = 0 := fun Ψ hΨ h0 => by
    rw [hc Ψ hΨ 0 (zero_mem _) (fun h => by simp [thetaKO]) (by rw [h0, map_zero])]
    funext h; simp [thetaInt, thetaKO]
  have stf : ∀ g ∈ GfC X, ∀ x ∈ K.map p, rf g x ∈ K.map p := by
    rintro g hg _ ⟨Ψ, ⟨hΨS, hΨ0⟩, rfl⟩
    refine ⟨ωA (1, g) Ψ, ⟨hm.mapA.stabX.1 g hg Ψ hΨS, ?_⟩, hm.mapA.eqf g hg Ψ hΨS⟩
    funext h
    rw [tr, hΨ0]
    rfl
  have stl : ∀ τ, ∀ Y ∈ lieAt X τ, ∀ x ∈ K.map p, rl τ Y x ∈ K.map p := by
    rintro τ Y hY _ ⟨Ψ, ⟨hΨS, hΨ0⟩, rfl⟩
    obtain ⟨Ψ', hΨ'S, hder⟩ := hm.mapA.stabX.2 τ Y hY Ψ hΨS
    refine ⟨Ψ', ⟨hΨ'S, funext fun h => ?_⟩, hm.mapA.eql τ Y hY Ψ hΨS Ψ' hΨ'S hder⟩
    have h1 := hasDerivAt_big hP hθ hO hTD hC hY hΨS hΨ'S hder h
    rw [hΨ0] at h1
    exact h1.unique (hasDerivAt_const (0 : ℝ) (0 : ℂ))
  rcases hm.irred.2 (K.map p) stf stl with hbot | htop
  · obtain ⟨Φ, hΦ, hpΦ⟩ : p' Φ' ∈ S.map p := hm.mapA.onto ▸ Submodule.mem_top
    have h1 : p Φ ∈ K.map p := ⟨Φ, ⟨hΦ, by rw [hc Φ hΦ Φ' hΦ' hint' hpΦ, h0', smul_zero]⟩, rfl⟩
    rw [hbot, Submodule.mem_bot, hpΦ] at h1
    exact hp' h1
  · obtain ⟨Φ, hΦ, hne⟩ := exists_big_ne hK hL hO hTD
    obtain ⟨Ψ, ⟨hΨS, hΨ0⟩, hΨp⟩ : p Φ ∈ K.map p := by rw [htop]; exact Submodule.mem_top
    have h1 := tadd _ (S.sub_mem hΦ hΨS) Ψ hΨS
    rw [sub_add_cancel, kill _ (S.sub_mem hΦ hΨS) (by rw [map_sub, hΨp, sub_self]), hΨ0, add_zero] at h1
    exact hne h1

end GlobalTheory.ConvThetaNe

end
