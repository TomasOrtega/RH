import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.CaraianiLocalGlobal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ConclusionFinite
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.NotIsPolarizedOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.NotIsTemperedGLDetRepTwo
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsPotentiallySemistableCoefficientFieldEnlarge
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsKurOfActStFixed
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KummerNotCoboundary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WdParameterMonodromyZeroIffPotentiallyCrystallin

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocGlobAll.Model

variable {E : Type} (Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a : ℕ}

def Compat (π : CuspSub E a) (R : G E Ω →* GL (Fin a) (Qbar l)) : Prop :=
  Continuous R ∧ IsSSRep R ∧
    (∀ (w : HeightOneSpectrum (𝓞 E)), ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (rc : IrrGL (w.adicCompletion E) → WD h), IsRec h rc → ∀ σ, π.IsLocComp w σ → IsWDOf ι R (rc (algNorm σ))) ∧
    ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
      ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
        (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
        (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw),
        IsPstAt P Bw (R.comp (Dec (F := E) A).subtype) ∧ ∀ σ, π.IsLocComp w σ → ∀ rc, IsRec h rc →
          wdAt P ι Bw h hj (R.comp (Dec (F := E) A).subtype) = rc (algNorm σ)

/- English proof (translation)
The claim follows from `H E Ω l ι a ha π hc hcoh`.
-/
theorem compat_of (H : GlobalTheory.Published.CaraianiLocalGlobal) (ha : 2 ≤ a) (π : CuspSub E a) (hc : π.IsCsd)
    (hcoh : GKCoh.IsCohomological π) : ∃ R, Compat Ω ι π R := H E Ω l ι a ha π hc hcoh

omit [IsCMField E] [IsAlgClosure E Ω] [NumberField E] in

/- English proof (translation)
Use `⟨Bw.LL, 1, isModel_one Bw, ?_⟩` and prove the remaining obligations. Use `Bw.LL.2` as an intermediate fact. Set `b` to `Module.finBasis ℚ_[l] (Fin a → ↥Bw.LL.1)`. Use `GlobalTheory.PstExt.isPst_of_coord P (LL := ℚ_[l]) (ρ := (1 : Representation ℚ_[l] ↥(GK Bw.Kw) ℚ_[l])) (E := b.equivFun) (fun g x i => ?_) (isPst_one_of_kummer l P (GlobalTheory.Pst.NoLog.kummer_not_coboundary l P AI T) _)` and prove the remaining obligations. Establish `: Bw.repE Bw.LL (1 : ↥Gw →* GL (Fin a) ↥Bw.LL.1) g x = x` using `by simp [LocBridge.repE]`.

Rewrite using `[this]`. Both sides reduce to the same expression.
-/
theorem isPstAt_one {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) {Gw : Subgroup (Ω ≃ₐ[E] Ω)}
    {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O) :
    IsPstAt P Bw (1 : ↥Gw →* GL (Fin a) (Om l)) := by
  refine ⟨Bw.LL, 1, isModel_one Bw, ?_⟩
  have := Bw.LL.2
  let b := Module.finBasis ℚ_[l] (Fin a → ↥Bw.LL.1)
  refine GlobalTheory.PstExt.isPst_of_coord P (LL := ℚ_[l]) (ρ := (1 : Representation ℚ_[l] ↥(GK Bw.Kw) ℚ_[l]))
    (E := b.equivFun) (fun g x i => ?_)
    (isPst_one_of_kummer l P (GlobalTheory.Pst.NoLog.kummer_not_coboundary l P AI T) _)
  have : Bw.repE Bw.LL (1 : ↥Gw →* GL (Fin a) ↥Bw.LL.1) g x = x := by simp [LocBridge.repE]
  rw [this]; rfl

/- English proof (translation)
Rewrite using `[rec_algNorm hrc]`. Take `⟨a, ha, ε, -, H⟩` from `hrc`. Establish `h1 : SmGL.IsSmoothChar (1 : (w.adicCompletion E)ˣ →* ℂˣ)`. Simplify using `using isSmoothChar_absPow (k := w.adicCompletion E) 0`. Rewrite using `[GlobalTheory.GalOfCusp.Model.locComp_triv hσ h1, H.one]`.

Establish `e : ((1 - ((1 : ℕ) : ℝ)) / 2) = 0` using `by simp`. Rewrite using `[e, WD.lpTw_zero]`. Use `WD.sound ⟨.refl _ _, fun σ v => ?_, fun v => rfl⟩` and prove the remaining obligations. Use extensionality with `i`. Simplify using `[WDRep.ofChars]`.
-/
theorem rec_triv {w : HeightOneSpectrum (𝓞 E)} {A : ValuationSubring Ω} {h : IsPlaceOver A w}
    {rc : IrrGL (w.adicCompletion E) → WD h} (hrc : IsRec h rc) {σ : SmIrr (GL (Fin 1) (w.adicCompletion E))}
    (hσ : (CuspSub.triv E le_rfl).IsLocComp w σ) : rc (algNorm σ) = WD.mk (WDRep.diag h fun _ : Fin 1 => 1) := by
  rw [rec_algNorm hrc]
  obtain ⟨a, ha, ε, -, H⟩ := hrc
  have h1 : SmGL.IsSmoothChar (1 : (w.adicCompletion E)ˣ →* ℂˣ) := by
    simpa using isSmoothChar_absPow (k := w.adicCompletion E) 0
  rw [GlobalTheory.GalOfCusp.Model.locComp_triv hσ h1, H.one]
  have e : ((1 - ((1 : ℕ) : ℝ)) / 2) = 0 := by simp
  rw [e, WD.lpTw_zero]
  refine WD.sound ⟨.refl _ _, fun σ v => ?_, fun v => rfl⟩
  ext i; simp [WDRep.ofChars]

/- English proof (translation)
Use `⟨continuous_const, fun W _ => let ⟨W', h⟩ := W.exists_isCompl; ⟨W', fun g v hv => by simpa using hv, h⟩, fun w hl A h rc hrc σ hσ => ?_, fun P AI ⟨T⟩ w A h O _ _ _ Bw hj => ?_⟩` and prove the remaining obligations. Rewrite using `[rec_triv Ω hrc hσ]`. Conclude with `GlobalTheory.GalOfCusp.Model.isWDOf_one hl h ι`. Establish `hp : IsPstAt P Bw ((1 : G E Ω →* GL (Fin 1) (Qbar l)).comp (Dec (F` using `E) A).subtype) := isPstAt_one Ω T Bw`. Use `⟨hp, fun σ hσ rc hrc => ?_⟩` and prove the remaining obligations.

Rewrite using `[rec_triv Ω hrc hσ]`. Establish `e : (1 : G E Ω →* GL (Fin 1) (Qbar l)) = GlobalTheory.TripleGal.rk1 (1 : G E Ω →* (Qbar l)ˣ)`. Use extensionality with `g i j`. Simplify using `[GlobalTheory.TripleGal.rk1]`. Use `nontrivial_B P` as an intermediate fact.

Establish `hs : WeilDeligne.IsSmooth (1 : Weil h →* ℂˣ)` using `.of_trivial fun _ => rfl`. Rewrite using `[GlobalTheory.Published.ParamAboveModel.eq_lpOfChar h _ (Test.lpDim_wdAt P ι Bw h hj _) 1 hs fun σ => ?_]`. Use `WD.sound ⟨.refl _ _, fun σ v => ?_, fun v => rfl⟩` and prove the remaining obligations. Use extensionality with `i`. Simplify using `[WDRep.ofChars]`.

Rewrite `hp`, the goal using `[e]`. Establish `key` using `GlobalTheory.Published.ParamAboveModel.mem_eig_wdAt P ι Bw h hj 1 hp 1 one_ne_zero 1 one_ne_zero (by simp) (fun _ => 1) (by simp) (by simp) Bw.Kw (fun g _ => by simp) σ`. Simplify using `using key`.
-/
theorem compat_triv : Compat Ω ι (CuspSub.triv E (le_refl 1)) 1 := by
  refine ⟨continuous_const, fun W _ => let ⟨W', h⟩ := W.exists_isCompl; ⟨W', fun g v hv => by simpa using hv, h⟩,
    fun w hl A h rc hrc σ hσ => ?_, fun P AI ⟨T⟩ w A h O _ _ _ Bw hj => ?_⟩
  · rw [rec_triv Ω hrc hσ]; exact GlobalTheory.GalOfCusp.Model.isWDOf_one hl h ι
  have hp : IsPstAt P Bw ((1 : G E Ω →* GL (Fin 1) (Qbar l)).comp (Dec (F := E) A).subtype) := isPstAt_one Ω T Bw
  refine ⟨hp, fun σ hσ rc hrc => ?_⟩
  rw [rec_triv Ω hrc hσ]
  have e : (1 : G E Ω →* GL (Fin 1) (Qbar l)) = GlobalTheory.TripleGal.rk1 (1 : G E Ω →* (Qbar l)ˣ) := by
    ext g i j; simp [GlobalTheory.TripleGal.rk1]
  have := nontrivial_B P
  have hs : WeilDeligne.IsSmooth (1 : Weil h →* ℂˣ) := .of_trivial fun _ => rfl
  rw [GlobalTheory.Published.ParamAboveModel.eq_lpOfChar h _ (Test.lpDim_wdAt P ι Bw h hj _) 1 hs fun σ => ?_]
  · refine WD.sound ⟨.refl _ _, fun σ v => ?_, fun v => rfl⟩
    ext i; simp [WDRep.ofChars]
  · rw [e] at hp ⊢
    have key := GlobalTheory.Published.ParamAboveModel.mem_eig_wdAt P ι Bw h hj 1 hp 1 one_ne_zero 1 one_ne_zero (by simp)
      (fun _ => 1) (by simp) (by simp) Bw.Kw (fun g _ => by simp) σ
    simpa using key

/- English proof (translation)
Introduce and unpack `⟨-, -, H, -⟩`. Take `⟨rc, hrc, -⟩` from `hL.1 E Ω A w h`. Establish `h2 : (CuspSub.triv E (le_refl 1)).IsLocComp w (SmIrr.triv _)` using `⟨LinearMap.toSpanSingleton ℂ _ ⟨oneFn E 1, Submodule.mem_span_singleton_self _⟩, fun h => oneFn_ne_zero ((one_smul ℂ _).symm.trans (congrArg Subtype.val (LinearMap.congr_fun h (1 : ℂ)))), fun _ _ => rfl⟩`. Establish `h3` using `(H w hl A h rc hrc _ h2).wdOf_eq hl`. Rewrite `h3` using `[rec_triv Ω hrc h2, wdOf_cyc]`.

Establish `h4` using `congrArg (fun x : WD h => x.charPol (frob h)) h3`. Simplify using `only [WD.lpTw_mk, WD.charPol_mk] at h4`. Establish `e1 : (WDRep.diag h fun _ : Fin 1 => (1 : ℂˣ)).ρ (frob h) = 1` using `by ext; simp`. Rewrite `h4` using `[WDRep.tw_ρ, e1, deg_frob]`. Establish `h5` using `LinearMap.aeval_self_charpoly ((((normV w : ℕ) : ℂ) ^ (((1 : ℝ) : ℝ) : ℂ)) ^ (1 : ℤ) • (1 : Module.End ℂ (Fin 1 → ℂ)))`.

Rewrite `h5` using `[h4, LinearMap.charpoly_one]`. Establish `h6` using `congrFun (LinearMap.congr_fun h5 fun _ => 1) 0`. Simplify using `[sub_eq_zero] at h6`. Conclude with `(one_lt_normV w).ne' h6`.
-/
theorem not_compat_cyc (hL : GlobalTheory.Published.LocalLanglandsGL) {w : HeightOneSpectrum (𝓞 E)}
    (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) {A : ValuationSubring Ω} (h : IsPlaceOver A w) :
    ¬ Compat Ω ι (CuspSub.triv E (le_refl 1)) ((Matrix.GeneralLinearGroup.scalar (Fin 1)).comp (cyc E Ω l)) := by
  rintro ⟨-, -, H, -⟩
  obtain ⟨rc, hrc, -⟩ := hL.1 E Ω A w h
  have h2 : (CuspSub.triv E (le_refl 1)).IsLocComp w (SmIrr.triv _) :=
    ⟨LinearMap.toSpanSingleton ℂ _ ⟨oneFn E 1, Submodule.mem_span_singleton_self _⟩,
      fun h => oneFn_ne_zero ((one_smul ℂ _).symm.trans (congrArg Subtype.val (LinearMap.congr_fun h (1 : ℂ)))),
      fun _ _ => rfl⟩
  have h3 := (H w hl A h rc hrc _ h2).wdOf_eq hl
  rw [rec_triv Ω hrc h2, wdOf_cyc] at h3
  have h4 := congrArg (fun x : WD h => x.charPol (frob h)) h3
  simp only [WD.lpTw_mk, WD.charPol_mk] at h4
  have e1 : (WDRep.diag h fun _ : Fin 1 => (1 : ℂˣ)).ρ (frob h) = 1 := by ext; simp
  rw [WDRep.tw_ρ, e1, deg_frob] at h4
  have h5 := LinearMap.aeval_self_charpoly ((((normV w : ℕ) : ℂ) ^ (((1 : ℝ) : ℝ) : ℂ)) ^ (1 : ℤ) •
    (1 : Module.End ℂ (Fin 1 → ℂ)))
  rw [h4, LinearMap.charpoly_one] at h5
  have h6 := congrFun (LinearMap.congr_fun h5 fun _ => 1) 0
  simp [sub_eq_zero] at h6
  exact (one_lt_normV w).ne' h6

variable {Ω ι}

/- English proof (translation)
Establish `h1` using `H.2.2.1 w hl A h rc hrc σ hσ`. Take `⟨N, hN⟩` from `(exists_isWDOf_iff hl (isTameChar_tameL h hl)).1 ⟨_, h1⟩`. Rewrite using `[← hN.unr_wdOf_iff hl (isTameChar_tameL h hl) ι, h1.wdOf_eq hl]`. Take `⟨_, _, _, -, L⟩` from `hrc`. Conclude with `(L.sph _).symm`.
-/
theorem Compat.unram_iff {π : CuspSub E a} {R : G E Ω →* GL (Fin a) (Qbar l)} (H : Compat Ω ι π R)
    {w : HeightOneSpectrum (𝓞 E)} (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) {A : ValuationSubring Ω} (h : IsPlaceOver A w)
    {rc : IrrGL (w.adicCompletion E) → WD h} (hrc : IsRec h rc) {σ} (hσ : π.IsLocComp w σ) :
    (∀ g ∈ Ine (F := E) A, R g = 1) ↔ SmGL.IsSpherical (algNorm σ).rep := by
  have h1 := H.2.2.1 w hl A h rc hrc σ hσ
  obtain ⟨N, hN⟩ := (exists_isWDOf_iff hl (isTameChar_tameL h hl)).1 ⟨_, h1⟩
  rw [← hN.unr_wdOf_iff hl (isTameChar_tameL h hl) ι, h1.wdOf_eq hl]
  obtain ⟨_, _, _, -, L⟩ := hrc
  exact (L.sph _).symm

/- English proof (translation)
Take `⟨h1, h2⟩` from `H.2.2.2 P AI ⟨T⟩ w A h O Bw hj`. Rewrite using `[← GlobalTheory.PstLaws.unr_wdAt_iff (h := h) (hj := hj) (ι := ι) (hr := h1), h2 σ hσ rc hrc]`. Take `⟨_, _, _, -, L⟩` from `hrc`. Conclude with `(L.sph _).symm`.
-/
theorem Compat.crys_iff {π : CuspSub E a} {R : G E Ω →* GL (Fin a) (Qbar l)} (H : Compat Ω ι π R)
    {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI)
    {w : HeightOneSpectrum (𝓞 E)} {A : ValuationSubring Ω} (h : IsPlaceOver A w)
    {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw)
    {rc : IrrGL (w.adicCompletion E) → WD h} (hrc : IsRec h rc) {σ} (hσ : π.IsLocComp w σ) :
    IsCrysAt P Bw (R.comp (Dec (F := E) A).subtype) ↔ SmGL.IsSpherical (algNorm σ).rep := by
  obtain ⟨h1, h2⟩ := H.2.2.2 P AI ⟨T⟩ w A h O Bw hj
  rw [← GlobalTheory.PstLaws.unr_wdAt_iff (h := h) (hj := hj) (ι := ι) (hr := h1), h2 σ hσ rc hrc]
  obtain ⟨_, _, _, -, L⟩ := hrc
  exact (L.sph _).symm

end GlobalTheory.LocGlobAll.Model

end
