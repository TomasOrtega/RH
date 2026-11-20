import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocIsoRefl
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GenPtSSubset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaussianDatumFlippedFiniteTensorBigRoute
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerFixedFunctionsProportionalOfSelfDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzEqPureTensorOfFiniteSlices
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmallModelThetaTransformInjectiveProducts
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmulOfMapsInlMemS
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatPtSLeClosureAndSelfDual
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HTensMixHalfS
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PureVacInj

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.SmallVac

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}

open GlobalTheory.SmallDat

/- English proof (translation)
Unfold `IsLatVac at h₁ h₂`. Rewrite using `[heisS_box t e Γ hW₁ hWW ψ γ f₁ f₂]`. Break down `hγ with ⟨γ', hγ', rfl⟩ | ⟨hγl, ε, hε, hxA, hxB⟩` into its components or cases. Establish `hdA : mapA t e (2 • γ') = 2 • mapA t e γ'` using `by rw [two_nsmul, two_nsmul, mapA_add]`. Establish `hdB : mapB e (2 • γ') = 2 • mapB e γ'` using `by rw [two_nsmul, two_nsmul, mapB_add]`.

Rewrite using `[hdA, hdB, h₁.1 _ hγ'.2.1, h₂.1 _ hγ'.2.2]`. Rewrite using `[h₁.2 ε hε _ hγl.2.1 hxA, h₂.2 ε hε _ hγl.2.2 hxB]`.
-/
theorem heisS_box_gen {t : T} {i j : ℕ} {e : Num G i j} {Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j}
    (hW₁ : Γ.V'.J = (-1 : D.host.E) • (spW₁ G i j).gram) (hWW : Γ.W.J = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram (spV G i j) (spV₁ G i j) e)
    {ψ : AddChar (AF D.host.F) ℂ} {f₁ : HomA G t i j → ℂ} {f₂ : HomB G i j → ℂ}
    (h₁ : IsLatVac (heisO ψ _ _) (latA G t i j) f₁) (h₂ : IsLatVac (heisO ψ _ _) (latB G i j) f₂) {v : Pl D.host.F}
    {γ : PtS G i j} (hγ : γ ∈ genPtS t e v) : heisS Γ ψ γ (boxS t e f₁ f₂) = boxS t e f₁ f₂ := by
  unfold IsLatVac at h₁ h₂
  rw [heisS_box t e Γ hW₁ hWW ψ γ f₁ f₂]
  rcases hγ with ⟨γ', hγ', rfl⟩ | ⟨hγl, ε, hε, hxA, hxB⟩
  · have hdA : mapA t e (2 • γ') = 2 • mapA t e γ' := by rw [two_nsmul, two_nsmul, mapA_add]
    have hdB : mapB e (2 • γ') = 2 • mapB e γ' := by rw [two_nsmul, two_nsmul, mapB_add]
    rw [hdA, hdB, h₁.1 _ hγ'.2.1, h₂.1 _ hγ'.2.2]
  · rw [h₁.2 ε hε _ hγl.2.1 hxA, h₂.2 ε hε _ hγl.2.2 hxB]

variable {W : G.Weil} {t : T} {i j : Fin D.R.m} {M : Vol G} {e : Num G i j} {Bs : Base D.host.F D.host.E}
  {Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j} {X : Chars D.host.F D.host.E} {om : Rep D.sp.cm.sig Γ.V Γ.W} {om' : Rep D.sp.cm.sig Γ.V' Γ.W}

/- English proof (translation)
Establish `hψ : Bs.ψ = W.ψ` using `h.ψ`. Establish `hGood : Γ.M'.IsGood W.ψ` using `hψ ▸ hT.geo.hM'`. Establish `hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd W.ψ` using `hψ ▸ hT.base.std`. Take `⟨-, hvac₁⟩` from `h₁`. Take `⟨-, hvac₂⟩` from `h₂`.

Establish `hbox` using `GlobalTheory.SmallDat.ThBox.thetaS_box W M t i j e Bs Γ X om om' h hT`. Take `⟨Φ, hΦ, hΦθ⟩` from `hbox.2.2 f₁ f₂ hvac₁.theta hvac₂.theta`. Establish `hfix : ∀ v, ∀ γ ∈ genPtS t e v, Γ.M'.co.rho W.ψ γ Φ = Φ`. Introduce `v γ hγ`. Use `hbox.2.1 _ (GlobalTheory.HeisSchA.rho_mem_schA Γ.M' W.ψ hstd γ Φ hΦ) _ hΦ ?_` and prove the remaining obligations.

Rewrite using `[thetaS_rho, hΦθ, heisS_box_gen h.JW₁ h.JWW hvac₁.lat hvac₂.lat hγ]`. Establish `hsd` using `GlobalTheory.SmallDatLat.latPtS_le_closure_and_selfDual hL W t i j e Γ h.JW₁ h.JWW`. Establish `hlat` using `GlobalTheory.SmallDat.latPtS_le_latAtV t i j e Bs Γ X hti`. Take `⟨f, hf⟩` from `GlobalTheory.PureGlue.eq_pure_of_slices Γ.M'.vac (fun v => (hGood.vac v).2.1) hGood.std Φ hΦ (by`. Introduce `v y hy`.

Break down `isEmpty_or_nonempty (IxS G i j) with hκ | ⟨⟨k₀⟩⟩` into its components or cases. Use `⟨(fun ξ : IxS G i j → _ => Φ (y + fun k => GlobalTheory.LatVac.liftV v (ξ k))) default / Γ.M'.vac v default, fun ξ => ?_⟩` and prove the remaining obligations. Establish `hξ : ξ = default` using `Subsingleton.elim _ _`. Substitute `hξ` using the available equality. Establish `hv0 : Γ.M'.vac v default ≠ 0`.

Introduce `h0`. Apply `(hGood.vac v).2.1` to reduce the goal to its premises. Use function extensionality and compare the values at `ξ'`. Rewrite using `[Subsingleton.elim ξ' default]`. Conclude with `h0`.

Rewrite using `[div_mul_cancel₀ _ hv0]`. Take `⟨c, hc0, hcb⟩` from `GlobalTheory.LatBound.locCo_latAtV_bounded Γ.V' Γ.W v Γ.M'.co hT.geo.hV'.lat hT.geo.hW.lat`. Establish `hsdl` using `GlobalTheory.LatVac.DualLoc.map_selfDual v Γ.M'.co W.ψ (latPtS t e v) (fun γ hγ => hγ.1) ((hsd v).2)`. Establish `hcont : Continuous (GlobalTheory.LatVac.psiAt W.ψ v)` using `by show Continuous (fun x => W.ψ (GlobalTheory.LatVac.liftV v x))`. Conclude with `hstd.1.comp (continuous_const.prodMk (GlobalTheory.AdelicU.continuous_singleFin v))`.

Establish `hne1 : GlobalTheory.LatVac.psiAt W.ψ v ≠ 1`. Introduce `h1`. Take `⟨π, hπ⟩` from `IsDedekindDomain.HeightOneSpectrum.valuation_exists_uniformizer (K := D.host.F) v`. Establish `hx : ((π⁻¹ : D.host.F) : v.adicCompletion D.host.F) ∉ v.adicCompletionIntegers D.host.F`. Rewrite using `[IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation', map_inv₀, hπ]`.

Use `first`. Consider the case `decide`. Consider the case `simp`. Consider the case `(intro hle; have := (inv_le_one₀ (by simp)).1 hle; simp at this)`. Establish `hall` using `(hsdl ((fun _ => c⁻¹ * ((π⁻¹ : D.host.F) : v.adicCompletion D.host.F)), 0)).2 (fun l _ => by rw [h1, AddChar.one_apply])`.

Take `⟨γ, hγ, hγe⟩` from `AddSubgroup.mem_map.1 hall`. Establish `h2` using `(hcb γ (hlat v γ hγ) k₀).1`. Rewrite `h2` using `[hγe]`. Establish `h3 : c * (c⁻¹ * ((π⁻¹ : D.host.F) : v.adicCompletion D.host.F)) ∈ v.adicCompletionIntegers D.host.F` using `h2`. Rewrite `h3` using `[mul_inv_cancel_left₀ hc0]`.

Conclude with `hx h3`. Take `⟨a, ha⟩` from `GlobalTheory.SchrFixUniq.proportional_of_fixed v (GlobalTheory.LatVac.psiAt W.ψ v) hcont hne1 (GlobalTheory.LatVac.locCo Γ.M'.co v '' genPtS t e v) ((latPtS t e v).map (GlobalTheory.LatVac.locCo Γ.M'.co v)) c ((AddSubgroup.map_mono ((hsd v).1)).trans (AddMonoidHom.map_closure _ _ …`. Introduce `l hl k`. Take `⟨γ, hγ, rfl⟩` from `AddSubgroup.mem_map.1 hl`. Conclude with `hcb γ (hlat v γ hγ) k)`.

Use the proof step `(Γ.M'.vac v) (fun ξ => Φ (y + fun k => GlobalTheory.LatVac.liftV v (ξ k)))`. Use the proof step `(by`. Introduce and unpack `_ ⟨γ, hγ, rfl⟩`. Conclude with `GlobalTheory.BigDat.schr_eq_of_acts Γ.M'.co W.ψ (genPtS_subset t e v hγ).1 (hGood.vac v).1 (GlobalTheory.SmallDat.VacFix.vac_fixed W M t i j e Bs Γ X om om' h hT v (hlat v) γ hγ))`. Use the proof step `(by`.

Introduce and unpack `_ ⟨γ, hγ, rfl⟩`. Conclude with `GlobalTheory.BigDat.schr_slice Γ.M'.co W.ψ (genPtS_subset t e v hγ).1 (hfix v γ hγ) hy)`. Use the proof step `(hGood.vac v).2.1`. Conclude with `⟨a, fun ξ => by simpa using congrFun ha ξ⟩)`. Conclude with `⟨f, by rw [← hf, hΦθ]⟩`.
-/
theorem exists_vacS (hL : L.Is μ₀) (h : IsTripleOf W M t i j e Bs Γ X) (hT : IsTriple Bs Γ X om om')
    (hti : GlobalTheory.FlipMatch.IsDoublyCompatible t i j e Bs Γ X) {f₁ : HomA G t i j → ℂ} {f₂ : HomB G i j → ℂ}
    (h₁ : W.IsVac (.mu t i j) f₁) (h₂ : W.IsVac (.chi i j) f₂) :
    ∃ f, thetaS Γ W.ψ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f Γ.M'.vac) = boxS t e f₁ f₂ := by
  have hψ : Bs.ψ = W.ψ := h.ψ
  have hGood : Γ.M'.IsGood W.ψ := hψ ▸ hT.geo.hM'
  have hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd W.ψ := hψ ▸ hT.base.std
  obtain ⟨-, hvac₁⟩ := h₁
  obtain ⟨-, hvac₂⟩ := h₂
  have hbox := GlobalTheory.SmallDat.ThBox.thetaS_box W M t i j e Bs Γ X om om' h hT
  obtain ⟨Φ, hΦ, hΦθ⟩ := hbox.2.2 f₁ f₂ hvac₁.theta hvac₂.theta
  have hfix : ∀ v, ∀ γ ∈ genPtS t e v, Γ.M'.co.rho W.ψ γ Φ = Φ := by
    intro v γ hγ
    refine hbox.2.1 _ (GlobalTheory.HeisSchA.rho_mem_schA Γ.M' W.ψ hstd γ Φ hΦ) _ hΦ ?_
    rw [thetaS_rho, hΦθ, heisS_box_gen h.JW₁ h.JWW hvac₁.lat hvac₂.lat hγ]
  have hsd := GlobalTheory.SmallDatLat.latPtS_le_closure_and_selfDual hL W t i j e Γ h.JW₁ h.JWW
  have hlat := GlobalTheory.SmallDat.latPtS_le_latAtV t i j e Bs Γ X hti
  obtain ⟨f, hf⟩ := GlobalTheory.PureGlue.eq_pure_of_slices Γ.M'.vac (fun v => (hGood.vac v).2.1) hGood.std Φ hΦ (by
    intro v y hy
    rcases isEmpty_or_nonempty (IxS G i j) with hκ | ⟨⟨k₀⟩⟩
    · refine ⟨(fun ξ : IxS G i j → _ => Φ (y + fun k => GlobalTheory.LatVac.liftV v (ξ k))) default / Γ.M'.vac v default, fun ξ => ?_⟩
      have hξ : ξ = default := Subsingleton.elim _ _
      subst hξ
      have hv0 : Γ.M'.vac v default ≠ 0 := by
        intro h0
        apply (hGood.vac v).2.1
        funext ξ'
        rw [Subsingleton.elim ξ' default]
        exact h0
      rw [div_mul_cancel₀ _ hv0]
    obtain ⟨c, hc0, hcb⟩ := GlobalTheory.LatBound.locCo_latAtV_bounded Γ.V' Γ.W v Γ.M'.co hT.geo.hV'.lat hT.geo.hW.lat
    have hsdl := GlobalTheory.LatVac.DualLoc.map_selfDual v Γ.M'.co W.ψ (latPtS t e v) (fun γ hγ => hγ.1) ((hsd v).2)
    have hcont : Continuous (GlobalTheory.LatVac.psiAt W.ψ v) := by
      show Continuous (fun x => W.ψ (GlobalTheory.LatVac.liftV v x))
      exact hstd.1.comp (continuous_const.prodMk (GlobalTheory.AdelicU.continuous_singleFin v))
    have hne1 : GlobalTheory.LatVac.psiAt W.ψ v ≠ 1 := by
      intro h1
      obtain ⟨π, hπ⟩ := IsDedekindDomain.HeightOneSpectrum.valuation_exists_uniformizer (K := D.host.F) v
      have hx : ((π⁻¹ : D.host.F) : v.adicCompletion D.host.F) ∉ v.adicCompletionIntegers D.host.F := by
        rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers,
          IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation', map_inv₀, hπ]
        first
        | decide
        | simp
        | (intro hle; have := (inv_le_one₀ (by simp)).1 hle; simp at this)
      have hall := (hsdl ((fun _ => c⁻¹ * ((π⁻¹ : D.host.F) : v.adicCompletion D.host.F)), 0)).2
        (fun l _ => by rw [h1, AddChar.one_apply])
      obtain ⟨γ, hγ, hγe⟩ := AddSubgroup.mem_map.1 hall
      have h2 := (hcb γ (hlat v γ hγ) k₀).1
      rw [hγe] at h2
      have h3 : c * (c⁻¹ * ((π⁻¹ : D.host.F) : v.adicCompletion D.host.F)) ∈ v.adicCompletionIntegers D.host.F := h2
      rw [mul_inv_cancel_left₀ hc0] at h3
      exact hx h3
    obtain ⟨a, ha⟩ := GlobalTheory.SchrFixUniq.proportional_of_fixed v (GlobalTheory.LatVac.psiAt W.ψ v) hcont hne1
      (GlobalTheory.LatVac.locCo Γ.M'.co v '' genPtS t e v) ((latPtS t e v).map (GlobalTheory.LatVac.locCo Γ.M'.co v)) c
      ((AddSubgroup.map_mono ((hsd v).1)).trans (AddMonoidHom.map_closure _ _).le) hc0 hsdl
      (by
        intro l hl k
        obtain ⟨γ, hγ, rfl⟩ := AddSubgroup.mem_map.1 hl
        exact hcb γ (hlat v γ hγ) k)
      (Γ.M'.vac v) (fun ξ => Φ (y + fun k => GlobalTheory.LatVac.liftV v (ξ k)))
      (by
        rintro _ ⟨γ, hγ, rfl⟩
        exact GlobalTheory.BigDat.schr_eq_of_acts Γ.M'.co W.ψ (genPtS_subset t e v hγ).1 (hGood.vac v).1
          (GlobalTheory.SmallDat.VacFix.vac_fixed W M t i j e Bs Γ X om om' h hT v (hlat v) γ hγ))
      (by
        rintro _ ⟨γ, hγ, rfl⟩
        exact GlobalTheory.BigDat.schr_slice Γ.M'.co W.ψ (genPtS_subset t e v hγ).1 (hfix v γ hγ) hy)
      (hGood.vac v).2.1
    exact ⟨a, fun ξ => by simpa using congrFun ha ξ⟩)
  exact ⟨f, by rw [← hf, hΦθ]⟩

end GlobalTheory.SmallVac

namespace GlobalTheory.SmallVac

open GlobalTheory.SmallDat GlobalTheory.FlipMatch

/- English proof (translation)
Introduce `D T L sc G μ₀ hL W ρ t i j M hst e Bs Γ X om om' h hT hti`. Establish `h₁ : W.IsVac (.mu t i j) (ρ.vT i j)` using `ρ.vT_is t i j i.2.le j.2`. Establish `h₂ : W.IsVac (.chi i j) (ρ.vX i j)` using `ρ.vX_is i j i.2 j.2.le`. Take `⟨f, hf⟩` from `exists_vacS hL h hT hti h₁ h₂`. Establish `hGood : Γ.M'.IsGood Bs.ψ` using `hT.geo.hM'`.

Use `⟨f, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `rfl`. Choose the witnesses or unpack the hypotheses as in `⟨x₁, hx₁⟩ : ∃ x : HomA G t i j, ρ.vT i j x ≠ 0 := by`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`.

Conclude with `GlobalTheory.BigDat.vac_ne_zero h₁ (funext hc)`. Choose the witnesses or unpack the hypotheses as in `⟨x₂, hx₂⟩ : ∃ x : HomB G i j, ρ.vX i j x ≠ 0 := by`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Conclude with `GlobalTheory.BigDat.vac_ne_zero h₂ (funext hc)`.

Establish `h0 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (0 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf _ _) Γ.M'.vac = (0 : ℂ) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (0 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorMod …`. Use function extensionality and compare the values at `x`. Simplify using `[GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]`. Establish `hu` using `congrFun hf (ofMaps t e (x₁, x₂))`. Rewrite `hu` using `[h0, thetaS_smul, zero_mul]`.

Unfold `boxS at hu`. Rewrite `hu` using `[mapA_ofMaps, mapB_ofMaps]`. Conclude with `mul_ne_zero hx₁ hx₂ hu.symm`. Conclude with `GlobalTheory.SmallGauss.isGauss W M t i j e Bs Γ X om om' h hT _ _ h₁ h₂ 1 f (by rw [one_smul]; exact hf)`. Conclude with `GlobalTheory.TensUniq.pure_mem_schA f _ (fun v => (hGood.vac v).1) hGood.std`.

Introduce `u erw [Finsupp.sum_single_index, one_mul]`. Conclude with `congrFun hf u`. Conclude with `zero_mul _`.
-/
theorem vac_datumB : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (M : Vol G) (hst : SquareStanding G t) (e : Num G i j) (Bs : Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : Chars D.host.F D.host.E)
    (om : Rep D.sp.cm.sig Γ.V Γ.W) (om' : Rep D.sp.cm.sig Γ.V' Γ.W) (h : IsTripleOf W M t i j e Bs Γ X), IsTriple Bs Γ X om om' → IsDoublyCompatible t i j e Bs Γ X →
    ∃ f₀, f₀ ≠ 0 ∧ Γ.M'.IsGauss Bs.ψ Bs.emb f₀ ∧
      IsDatumB (t := t) W e Γ (Finsupp.single (((), ρ.vT i j), ρ.vX i j) 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ Γ.M'.vac) := by
  intro D T L sc G μ₀ hL W ρ t i j M hst e Bs Γ X om om' h hT hti
  have h₁ : W.IsVac (.mu t i j) (ρ.vT i j) := ρ.vT_is t i j i.2.le j.2
  have h₂ : W.IsVac (.chi i j) (ρ.vX i j) := ρ.vX_is i j i.2 j.2.le
  obtain ⟨f, hf⟩ := exists_vacS hL h hT hti h₁ h₂
  have hGood : Γ.M'.IsGood Bs.ψ := hT.geo.hM'
  refine ⟨f, ?_, ?_, ?_, ?_⟩
  · rintro rfl
    obtain ⟨x₁, hx₁⟩ : ∃ x : HomA G t i j, ρ.vT i j x ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact GlobalTheory.BigDat.vac_ne_zero h₁ (funext hc)
    obtain ⟨x₂, hx₂⟩ : ∃ x : HomB G i j, ρ.vX i j x ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact GlobalTheory.BigDat.vac_ne_zero h₂ (funext hc)
    have h0 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (0 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf _ _) Γ.M'.vac =
        (0 : ℂ) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (0 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf _ _) Γ.M'.vac := by
      funext x
      simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]
    have hu := congrFun hf (ofMaps t e (x₁, x₂))
    rw [h0, thetaS_smul, zero_mul] at hu
    unfold boxS at hu
    rw [mapA_ofMaps, mapB_ofMaps] at hu
    exact mul_ne_zero hx₁ hx₂ hu.symm
  · exact GlobalTheory.SmallGauss.isGauss W M t i j e Bs Γ X om om' h hT _ _ h₁ h₂ 1 f (by rw [one_smul]; exact hf)
  · exact GlobalTheory.TensUniq.pure_mem_schA f _ (fun v => (hGood.vac v).1) hGood.std
  · intro u
    erw [Finsupp.sum_single_index, one_mul]
    · exact congrFun hf u
    · exact zero_mul _

end GlobalTheory.SmallVac
