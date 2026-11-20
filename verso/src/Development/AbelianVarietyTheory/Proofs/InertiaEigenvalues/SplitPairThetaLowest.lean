import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OverRowsAndMono
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIrreducibleTwist
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaCorrespondenceLargeRankStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceLocalComponentExistsUniqueClass
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RankOneLocalComponentDet
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharLocalComponentExistsUniqueUnitary
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PairReadingOfJoin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.FixedNeBotOfEquiv
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitarisableOfIsLocS
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicUnitaryTrivialOutsideSplitPlaceLocEq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsotypicPartSpannedBySplitPlaceLocalComponent
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteTypeSpannedBySplitPlaceLocalComponent
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaPairingOfInvariantTrilinearForm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasThetaAtOfThetaMod
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRowThetaModuleStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.SplitRead GlobalTheory.NPin

noncomputable section

namespace GlobalTheory.RefPair

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Take `⟨Ω, _, _, ω, Λ, φ₀, hinv, hread, hloc⟩` from `hΘ`. Take `⟨f, hf, F, hF, hne⟩` from `hPair`. Establish `hFmem : Mr.real F ∈ NG.AFall D.host.E D.R.nV Mr.wt.ρ`. Establish `: Mr.real F ∈ LinearMap.range Mr.real` using `LinearMap.mem_range_self _ _`. Rewrite `this` using `[Mr.real_range]`.

Conclude with `this.1`. Set `Fp : ↥(NG.AFall D.host.E D.R.nV Mr.wt.ρ)` to `⟨_, hFmem⟩`. Set `yp : ↥X.C` to `⟨X.φ f, X.φ_mem f⟩`. Establish `h0 : Λ φ₀ Fp yp ≠ 0`. Rewrite using `[← hread F f Fp rfl]`.

Introduce `h`. Apply `hne` to reduce the goal to its premises. Use `show inner ℂ F (LinearMap.adjoint (D.what₂.thetaP μt j) f) = 0`. Rewrite using `[LinearMap.adjoint_inner_right, ← inner_conj_symm, h, map_zero]`. Establish `hμc : IsComp μ s.w (μ.loc s.w)` using `⟨GlobalTheory.HeckeComp.smooth_loc μ s.w, fun _ => rfl⟩`.

Establish `hηc : IsComp η s.w (η.loc s.w)` using `⟨GlobalTheory.HeckeComp.smooth_loc η s.w, fun _ => rfl⟩`. Establish `hl` using `hloc s _ _ hμc hηc`. Set `ℓ0 : Ω →+ ℂ` to `AddMonoidHom.mk' (fun φ => Λ φ Fp yp) (by intro a b; simp)`. Take `⟨ι, φ1, hφ1, hℓ1⟩` from `GlobalTheory.PairReadPf.exists_ne_of_mem_iSup _ ℓ0 hl h0`. Take `⟨hLin, φ2, ⟨Φ0, rfl⟩, hℓ2⟩` from `GlobalTheory.PairReadPf.exists_ne_of_mem_iSup _ ℓ0 hφ1 hℓ1`.

Take `⟨c, hc, hci, hιeq⟩` from `hLin`. Establish `hFiso : (Fp : GAf D.host.E D.R.nV → Mr.wt.W) ∈ NG.isoTyp Mr.wt.ρ S` using `hF`. Establish `hspan` using `GlobalTheory.SpanLoc.main D.host.E D.R.nV Mr.wt S hS s π hπ c hc hci`. Set `ℓF : ↥(NG.AFall D.host.E D.R.nV Mr.wt.ρ) →+ ℂ` to `AddMonoidHom.mk' (fun F' => Λ (ι Φ0) F' yp) (by intro a b; simp)`. Take `⟨T1, F1, hF1, hℓF1⟩` from `GlobalTheory.PairReadPf.exists_ne_of_mem_iSup_sub _ _ (fun T => iSup_le fun hT1 => by rintro _ ⟨v, rfl⟩; exact hT1.1 v) ℓF Fp (hspan hFiso) hℓ2`.

Take `⟨hT1, F2, ⟨a0, ha0⟩, hℓF2⟩` from `GlobalTheory.PairReadPf.exists_ne_of_mem_iSup_sub _ _ (fun hT1 => by rintro _ ⟨v, rfl⟩; exact hT1.1 v) ℓF F1 hF1 hℓF1`. Establish `hyI : (yp : X.A) ∈ Formalism.IndefR.principalLevelFrame.isotIn (D` using `D) X.ρ X.C (rep σ) := (X.isot σ f).1 hf`. Unfold `Formalism.IndefR.principalLevelFrame.isotIn at hyI`. Set `ℓy : ↥X.C →+ ℂ` to `(Λ (ι Φ0) F2).toAddMonoidHom`. Take `⟨Φe, y1, hy1, hℓy1⟩` from `GlobalTheory.PairReadPf.exists_ne_of_mem_iSup_sub X.C _ (fun Φe => iSup_le fun h => h.2) ℓy yp hyI hℓF2`.

Take `⟨hΦe, y2, ⟨f2, hf2⟩, hℓy2⟩` from `GlobalTheory.PairReadPf.exists_ne_of_mem_iSup_sub X.C _ (fun h => h.2) ℓy y1 hy1 hℓy1`. Establish `hΦC : ∀ g : ↥(rep σ).S, Φe g ∈ X.C` using `fun g => hΦe.2 (LinearMap.mem_range_self _ _)`. Establish `hspan2` using `GlobalTheory.FinTypSpanLoc.main D.host.E D.R.r (rep σ) s τ hτ c hc hci`. Set `ℓ2 : ↥(rep σ).S →+ ℂ` to `AddMonoidHom.mk' (fun g => Λ (ι Φ0) F2 ⟨Φe g, hΦC g⟩) (by`. Introduce `a b`.

Establish `e : (⟨Φe (a + b), hΦC (a + b)⟩ : ↥X.C) = ⟨Φe a, hΦC a⟩ + ⟨Φe b, hΦC b⟩`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using the standard rewrite rules. Use `show Λ (ι Φ0) F2 ⟨Φe (a + b), hΦC (a + b)⟩ = Λ (ι Φ0) F2 ⟨Φe a, hΦC a⟩ + Λ (ι Φ0) F2 ⟨Φe b, hΦC b⟩`. Rewrite using `[e, map_add])`.

Establish `hℓ2f2 : ℓ2 f2 ≠ 0`. Establish `e : (⟨Φe f2, hΦC f2⟩ : ↥X.C) = y2` using `Subtype.ext hf2`. Use `show Λ (ι Φ0) F2 ⟨Φe f2, hΦC f2⟩ ≠ 0`. Rewrite using `[e]`. Conclude with `hℓy2`.

Take `⟨T2, g1, hg1, hℓg1⟩` from `GlobalTheory.PairReadPf.exists_ne_of_mem_iSup_sub _ _ (fun T => iSup_le fun hT2 => by rintro _ ⟨v, rfl⟩; exact hT2.1 v) ℓ2 f2 (hspan2 f2.2) hℓ2f2`. Take `⟨hT2, g2, ⟨c0, hc0⟩, hℓg2⟩` from `GlobalTheory.PairReadPf.exists_ne_of_mem_iSup_sub _ _ (fun hT2 => by rintro _ ⟨v, rfl⟩; exact hT2.1 v) ℓ2 g1 hg1 hℓg1`. Set `T' : π.V →ₗ[ℂ] ↥(NG.AFall D.host.E D.R.nV Mr.wt.ρ)` to `T1.codRestrict _ hT1.1`. Set `T'' : τ.V →ₗ[ℂ] ↥X.C` to `(Φe ∘ₗ T2.codRestrict _ hT2.1).codRestrict X.C (fun v => hΦC _)`. Establish `hT'eq : ∀ x : GAf D.host.E D.R.nV, TrivOutside {s.v} x → ∀ a, ((T' (π.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x)) a) : ↥(NG.AFall D.host.E D.R.nV Mr.wt.ρ)) : GAf D.host.E D.R.nV → Mr.wt.W) = NG.rt D.host.E D.R.nV x (T' a : GAf D.host.E D.R.nV → Mr.wt.W)` using `fun x hx a => hT1.2 x hx a`.

Establish `hT''eq : ∀ x : GAf D.host.E D.R.r, TrivOutside {s.v} x → ∀ a, ((T'' (τ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.r x)) a) : ↥X.C) : X.A) = X.ρ x (T'' a)`. Introduce `x hx a`. Establish `e : (⟨T2 (τ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.r x)) a), hT2.1 _⟩ : ↥(rep σ).S) = ⟨NG.rt D.host.E D.R.r x (T2 a), (rep σ).stable x _ (hT2.1 a)⟩` using `Subtype.ext (hT2.2 x hx a)`. Use `show Φe ⟨_, _⟩ = X.ρ x (Φe ⟨T2 a, hT2.1 a⟩)`. Rewrite using `[e]`.

Conclude with `hΦe.1 x ⟨T2 a, hT2.1 a⟩`. Set `b` to `((Λ ∘ₗ ι).compl₂ T').compr₂ (GlobalTheory.PairReadPf.precompₛ T'')`. Establish `hb0 : b Φ0 a0 c0 ≠ 0`. Establish `e1 : T' a0 = F2` using `Subtype.ext ha0`. Establish `e2 : T'' c0 = ⟨Φe g2, hΦC g2⟩`.

Apply `Subtype.ext` to reduce the goal to its premises. Use `show Φe ⟨T2 c0, hT2.1 c0⟩ = Φe g2`. Use `congr 1`. Conclude with `Subtype.ext hc0`. Use `show Λ (ι Φ0) (T' a0) (T'' c0) ≠ 0`.

Rewrite using `[e1, e2]`. Conclude with `hℓg2`. Use `GlobalTheory.ThetaRiesz.thetaPair_of_invariant_form _ D.R.r (D.R.r + D.R.t) _ _ (μ.loc s.w) τ.ρ (GlobalTheory.SmGL.twist π.ρ (GlobalTheory.SmGL.detChar (Fin (D.R.r + D.R.t)) (η.loc s.w))) ((hBZ _).1 (Fin D.R.r) _ _ τ.smooth τ.irr) hU (GlobalTheory.HeckeComp.smooth_loc μ s.w) b (f …` and prove the remaining obligations. Introduce `g h Φ Φ' hΦ' a c'`. Take `⟨xh, hxh, exh⟩` from `GlobalTheory.SplitLift.exists_trivOutside_loc_eq D.R.nV s (Matrix.GeneralLinearGroup.map c.symm.toRingHom h)`.

Take `⟨xg, hxg, exg⟩` from `GlobalTheory.SplitLift.exists_trivOutside_loc_eq D.R.r s (Matrix.GeneralLinearGroup.map c.symm.toRingHom g)`. Establish `back : ∀ (n : ℕ) (A : GL (Fin n) (s.w.adicCompletion D.host.E)), Matrix.GeneralLinearGroup.map c.toRingHom (Matrix.GeneralLinearGroup.map c.symm.toRingHom A) = A`. Introduce `n A`. Use extensionality with `k l`. Simplify using the standard rewrite rules.

Establish `eh : (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV xh) : GL (Fin (D.R.r + D.R.t)) (s.w.adicCompletion D.host.E)) = h` using `by rw [exh]; exact back _ h`. Establish `eg : Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.r xg) = g` using `by rw [exg]; exact back _ g`. Substitute `eh eg` using the available equality. Establish `hω` using `hιeq xh xg hxh hxg Φ Φ' hΦ'`. Establish `key` using `hinv xh xg (ι Φ) (T' a) (T' (π.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV xh)) a)) (T'' c') (T'' (τ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.r xg)) c')) (hT'eq xh hxh a) (hT''eq xg hxg c')`.

Rewrite `key` using `[hω]`. Use `show Λ (ι Φ') (T' (GlobalTheory.SmGL.twist π.ρ (GlobalTheory.SmGL.detChar (Fin (D.R.r + D.R.t)) (η.loc s.w)) _ a)) (T'' (τ.ρ _ c')) = Λ (ι Φ) (T' a) (T'' c')`. Rewrite using `[twist_apply, detChar_apply, map_smul, LinearMap.map_smul, LinearMap.smul_apply]`. Rewrite `key` using `[LinearMap.map_smul, LinearMap.smul_apply, LinearMap.smul_apply]`. Conclude with `key`.
-/
theorem thetaPair_of_hasThetaAt (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness) (D : D7) {μt : D.what₂.Tup} {j : ℕ}
    (Mr : MtReal D μt j) {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r} (X : RowMod D rep j) (μ η : HChar D.host.E)
    (hΘ : HasThetaAt D Mr X μ η) (σ : D.what₂.FT) (S : Submodule ℂ (GAf D.host.E D.R.nV → Mr.wt.W))
    (hS : NG.IsIrrRep Mr.wt.ρ S)
    (hPair : ∃ y ∈ D.what₂.isot j σ, ∃ F ∈ (NG.isoTyp Mr.wt.ρ S).comap Mr.real, inner ℂ F (D.what₂.thetaT μt j y) ≠ 0)
    (s : SplitPlace D.host.E) (π : GlobalTheory.SmGL.IrrRep (GL (Fin (D.R.r + D.R.t)) (s.w.adicCompletion D.host.E)))
    (τ : GlobalTheory.SmGL.IrrRep (GL (Fin D.R.r) (s.w.adicCompletion D.host.E)))
    (hπ : IsLocS (n := D.R.nV) S s π) (hτ : IsLocS (rep σ).S s τ) (hU : GlobalTheory.SmGL.IsUnitarisable τ.ρ) :
    GlobalTheory.ThetaGL.ThetaPair (μ.loc s.w) τ.ρ (GlobalTheory.SmGL.twist π.ρ (GlobalTheory.SmGL.detChar (Fin (D.R.r + D.R.t)) (η.loc s.w))) := by
  obtain ⟨Ω, _, _, ω, Λ, φ₀, hinv, hread, hloc⟩ := hΘ
  obtain ⟨f, hf, F, hF, hne⟩ := hPair
  have hFmem : Mr.real F ∈ NG.AFall D.host.E D.R.nV Mr.wt.ρ := by
    have : Mr.real F ∈ LinearMap.range Mr.real := LinearMap.mem_range_self _ _
    rw [Mr.real_range] at this
    exact this.1
  let Fp : ↥(NG.AFall D.host.E D.R.nV Mr.wt.ρ) := ⟨_, hFmem⟩
  let yp : ↥X.C := ⟨X.φ f, X.φ_mem f⟩
  have h0 : Λ φ₀ Fp yp ≠ 0 := by
    rw [← hread F f Fp rfl]
    intro h
    apply hne
    show inner ℂ F (LinearMap.adjoint (D.what₂.thetaP μt j) f) = 0
    rw [LinearMap.adjoint_inner_right, ← inner_conj_symm, h, map_zero]
  have hμc : IsComp μ s.w (μ.loc s.w) := ⟨GlobalTheory.HeckeComp.smooth_loc μ s.w, fun _ => rfl⟩
  have hηc : IsComp η s.w (η.loc s.w) := ⟨GlobalTheory.HeckeComp.smooth_loc η s.w, fun _ => rfl⟩
  have hl := hloc s _ _ hμc hηc
  let ℓ0 : Ω →+ ℂ := AddMonoidHom.mk' (fun φ => Λ φ Fp yp) (by intro a b; simp)
  obtain ⟨ι, φ1, hφ1, hℓ1⟩ := GlobalTheory.PairReadPf.exists_ne_of_mem_iSup _ ℓ0 hl h0
  obtain ⟨hLin, φ2, ⟨Φ0, rfl⟩, hℓ2⟩ := GlobalTheory.PairReadPf.exists_ne_of_mem_iSup _ ℓ0 hφ1 hℓ1
  obtain ⟨c, hc, hci, hιeq⟩ := hLin

  have hFiso : (Fp : GAf D.host.E D.R.nV → Mr.wt.W) ∈ NG.isoTyp Mr.wt.ρ S := hF
  have hspan := GlobalTheory.SpanLoc.main D.host.E D.R.nV Mr.wt S hS s π hπ c hc hci
  let ℓF : ↥(NG.AFall D.host.E D.R.nV Mr.wt.ρ) →+ ℂ :=
    AddMonoidHom.mk' (fun F' => Λ (ι Φ0) F' yp) (by intro a b; simp)
  obtain ⟨T1, F1, hF1, hℓF1⟩ := GlobalTheory.PairReadPf.exists_ne_of_mem_iSup_sub _ _
    (fun T => iSup_le fun hT1 => by rintro _ ⟨v, rfl⟩; exact hT1.1 v) ℓF Fp (hspan hFiso) hℓ2
  obtain ⟨hT1, F2, ⟨a0, ha0⟩, hℓF2⟩ := GlobalTheory.PairReadPf.exists_ne_of_mem_iSup_sub _ _
    (fun hT1 => by rintro _ ⟨v, rfl⟩; exact hT1.1 v) ℓF F1 hF1 hℓF1

  have hyI : (yp : X.A) ∈ Formalism.IndefR.principalLevelFrame.isotIn (D := D) X.ρ X.C (rep σ) := (X.isot σ f).1 hf
  unfold Formalism.IndefR.principalLevelFrame.isotIn at hyI
  let ℓy : ↥X.C →+ ℂ := (Λ (ι Φ0) F2).toAddMonoidHom
  obtain ⟨Φe, y1, hy1, hℓy1⟩ := GlobalTheory.PairReadPf.exists_ne_of_mem_iSup_sub X.C _
    (fun Φe => iSup_le fun h => h.2) ℓy yp hyI hℓF2
  obtain ⟨hΦe, y2, ⟨f2, hf2⟩, hℓy2⟩ := GlobalTheory.PairReadPf.exists_ne_of_mem_iSup_sub X.C _
    (fun h => h.2) ℓy y1 hy1 hℓy1
  have hΦC : ∀ g : ↥(rep σ).S, Φe g ∈ X.C := fun g => hΦe.2 (LinearMap.mem_range_self _ _)
  have hspan2 := GlobalTheory.FinTypSpanLoc.main D.host.E D.R.r (rep σ) s τ hτ c hc hci
  let ℓ2 : ↥(rep σ).S →+ ℂ :=
    AddMonoidHom.mk' (fun g => Λ (ι Φ0) F2 ⟨Φe g, hΦC g⟩) (by
      intro a b
      have e : (⟨Φe (a + b), hΦC (a + b)⟩ : ↥X.C) = ⟨Φe a, hΦC a⟩ + ⟨Φe b, hΦC b⟩ := by
        apply Subtype.ext; simp
      show Λ (ι Φ0) F2 ⟨Φe (a + b), hΦC (a + b)⟩ = Λ (ι Φ0) F2 ⟨Φe a, hΦC a⟩ + Λ (ι Φ0) F2 ⟨Φe b, hΦC b⟩
      rw [e, map_add])
  have hℓ2f2 : ℓ2 f2 ≠ 0 := by
    have e : (⟨Φe f2, hΦC f2⟩ : ↥X.C) = y2 := Subtype.ext hf2
    show Λ (ι Φ0) F2 ⟨Φe f2, hΦC f2⟩ ≠ 0
    rw [e]; exact hℓy2
  obtain ⟨T2, g1, hg1, hℓg1⟩ := GlobalTheory.PairReadPf.exists_ne_of_mem_iSup_sub _ _
    (fun T => iSup_le fun hT2 => by rintro _ ⟨v, rfl⟩; exact hT2.1 v) ℓ2 f2 (hspan2 f2.2) hℓ2f2
  obtain ⟨hT2, g2, ⟨c0, hc0⟩, hℓg2⟩ := GlobalTheory.PairReadPf.exists_ne_of_mem_iSup_sub _ _
    (fun hT2 => by rintro _ ⟨v, rfl⟩; exact hT2.1 v) ℓ2 g1 hg1 hℓg1

  let T' : π.V →ₗ[ℂ] ↥(NG.AFall D.host.E D.R.nV Mr.wt.ρ) := T1.codRestrict _ hT1.1
  let T'' : τ.V →ₗ[ℂ] ↥X.C := (Φe ∘ₗ T2.codRestrict _ hT2.1).codRestrict X.C (fun v => hΦC _)
  have hT'eq : ∀ x : GAf D.host.E D.R.nV, TrivOutside {s.v} x → ∀ a,
      ((T' (π.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x)) a) :
        ↥(NG.AFall D.host.E D.R.nV Mr.wt.ρ)) : GAf D.host.E D.R.nV → Mr.wt.W) =
        NG.rt D.host.E D.R.nV x (T' a : GAf D.host.E D.R.nV → Mr.wt.W) :=
    fun x hx a => hT1.2 x hx a
  have hT''eq : ∀ x : GAf D.host.E D.R.r, TrivOutside {s.v} x → ∀ a,
      ((T'' (τ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.r x)) a) : ↥X.C) : X.A) =
        X.ρ x (T'' a) := by
    intro x hx a
    have e : (⟨T2 (τ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.r x)) a), hT2.1 _⟩ : ↥(rep σ).S) =
        ⟨NG.rt D.host.E D.R.r x (T2 a), (rep σ).stable x _ (hT2.1 a)⟩ := Subtype.ext (hT2.2 x hx a)
    show Φe ⟨_, _⟩ = X.ρ x (Φe ⟨T2 a, hT2.1 a⟩)
    rw [e]
    exact hΦe.1 x ⟨T2 a, hT2.1 a⟩
  let b := ((Λ ∘ₗ ι).compl₂ T').compr₂ (GlobalTheory.PairReadPf.precompₛ T'')
  have hb0 : b Φ0 a0 c0 ≠ 0 := by
    have e1 : T' a0 = F2 := Subtype.ext ha0
    have e2 : T'' c0 = ⟨Φe g2, hΦC g2⟩ := by
      apply Subtype.ext
      show Φe ⟨T2 c0, hT2.1 c0⟩ = Φe g2
      congr 1
      exact Subtype.ext hc0
    show Λ (ι Φ0) (T' a0) (T'' c0) ≠ 0
    rw [e1, e2]
    exact hℓg2
  refine GlobalTheory.ThetaRiesz.thetaPair_of_invariant_form _ D.R.r (D.R.r + D.R.t) _ _ (μ.loc s.w) τ.ρ
    (GlobalTheory.SmGL.twist π.ρ (GlobalTheory.SmGL.detChar (Fin (D.R.r + D.R.t)) (η.loc s.w)))
    ((hBZ _).1 (Fin D.R.r) _ _ τ.smooth τ.irr) hU (GlobalTheory.HeckeComp.smooth_loc μ s.w) b
    (fun h => hb0 (by rw [h]; rfl)) ?_
  intro g h Φ Φ' hΦ' a c'
  obtain ⟨xh, hxh, exh⟩ := GlobalTheory.SplitLift.exists_trivOutside_loc_eq D.R.nV s
    (Matrix.GeneralLinearGroup.map c.symm.toRingHom h)
  obtain ⟨xg, hxg, exg⟩ := GlobalTheory.SplitLift.exists_trivOutside_loc_eq D.R.r s
    (Matrix.GeneralLinearGroup.map c.symm.toRingHom g)
  have back : ∀ (n : ℕ) (A : GL (Fin n) (s.w.adicCompletion D.host.E)),
      Matrix.GeneralLinearGroup.map c.toRingHom (Matrix.GeneralLinearGroup.map c.symm.toRingHom A) = A := by
    intro n A
    ext k l
    simp
  have eh : (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV xh) :
      GL (Fin (D.R.r + D.R.t)) (s.w.adicCompletion D.host.E)) = h := by rw [exh]; exact back _ h
  have eg : Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.r xg) = g := by rw [exg]; exact back _ g
  subst eh eg
  have hω := hιeq xh xg hxh hxg Φ Φ' hΦ'
  have key := hinv xh xg (ι Φ) (T' a) (T' (π.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV xh)) a))
    (T'' c') (T'' (τ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.r xg)) c'))
    (hT'eq xh hxh a) (hT''eq xg hxg c')
  rw [hω] at key
  show Λ (ι Φ') (T' (GlobalTheory.SmGL.twist π.ρ (GlobalTheory.SmGL.detChar (Fin (D.R.r + D.R.t)) (η.loc s.w)) _ a)) (T'' (τ.ρ _ c')) =
    Λ (ι Φ) (T' a) (T'' c')
  rw [twist_apply, detChar_apply, map_smul, LinearMap.map_smul, LinearMap.smul_apply]
  rw [LinearMap.map_smul, LinearMap.smul_apply, LinearMap.smul_apply] at key
  exact key

end GlobalTheory.RefPair

namespace GlobalTheory.RefPair

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.SplitRead GlobalTheory.NPin

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `hN hL`. Establish `hA` using `GlobalTheory.T.exists_row_theta_module hN hL`. Unfold `GlobalTheory.LiftRef.AtRows at hA ⊢`. Use `GlobalTheory.LiftRef.overRows_and_mono hA hA ?_` and prove the remaining obligations. Introduce `K B f T w Z Wt hX z p0 Y hA1 _ Rw a M tup Q hMA hMI j h1 h2 σ S hS hPair s π τ hπ hτ`.

Take `⟨X, hXd⟩` from `hA1 Rw a M tup Q hMA hMI j h1 h2`. Take `⟨Bf, k1, k2, k3, k4⟩` from `GlobalTheory.RowSphSmall.exists_form_rowRepR hN.hc hN.decay _ _ _ _ _ _ _ z.R z.F z.cG p0 Y z.pins σ`. Conclude with `thetaPair_of_hasThetaAt hN.what₂.bz _ _ X _ _ hXd σ S hS hPair s π τ hπ hτ (GlobalTheory.RowSphSmall.isUnitarisable_of_isLocS _ Bf k1 k2 k3 k4 s τ hτ)`.
-/
theorem split_pair_theta_mu0 : PrN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, GlobalTheory.LiftRef.AtRows hL fun D cf rep _ _ M => ∀ (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (σ : D.what₂.FT) (S : Submodule ℂ (Formalism.AUTREP.GAf D.host.E D.R.nV → (M D.what₂.mu0 j h1 h2).wt.W)), NG.IsIrrRep (M D.what₂.mu0 j h1 h2).wt.ρ S → (∃ y ∈ D.what₂.isot j σ, ∃ F ∈ (NG.isoTyp (M D.what₂.mu0 j h1 h2).wt.ρ S).comap (M D.what₂.mu0 j h1 h2).real, inner ℂ F (D.what₂.thetaT D.what₂.mu0 j y) ≠ 0) → ∀ (s : SplitPlace D.host.E) (π : GlobalTheory.SmGL.IrrRep (GL (Fin (D.R.r + D.R.t)) (s.w.adicCompletion D.host.E))) (τ : GlobalTheory.SmGL.IrrRep (GL (Fin D.R.r) (s.w.adicCompletion D.host.E))), IsLocS (n := D.R.nV) S s π → IsLocS (rep σ).S s τ → GlobalTheory.ThetaGL.ThetaPair ((cf.mu0 ⟨j - 1, by omega⟩).loc s.w) τ.ρ (GlobalTheory.SmGL.twist π.ρ (GlobalTheory.SmGL.detChar (Fin (D.R.r + D.R.t)) (cf.eta.loc s.w))) := by
  intro hN hL
  have hA := GlobalTheory.T.exists_row_theta_module hN hL
  unfold GlobalTheory.LiftRef.AtRows at hA ⊢
  refine GlobalTheory.LiftRef.overRows_and_mono hA hA ?_
  intro K B f T w Z Wt hX z p0 Y hA1 _ Rw a M tup Q hMA hMI j h1 h2 σ S hS hPair s π τ hπ hτ
  obtain ⟨X, hXd⟩ := hA1 Rw a M tup Q hMA hMI j h1 h2
  obtain ⟨Bf, k1, k2, k3, k4⟩ := GlobalTheory.RowSphSmall.exists_form_rowRepR hN.hc hN.decay _ _ _ _ _ _ _ z.R z.F z.cG p0 Y z.pins σ
  exact thetaPair_of_hasThetaAt hN.what₂.bz _ _ X _ _ hXd σ S hS hPair s π τ hπ hτ
    (GlobalTheory.RowSphSmall.isUnitarisable_of_isLocS _ Bf k1 k2 k3 k4 s τ hτ)

end GlobalTheory.RefPair

end
