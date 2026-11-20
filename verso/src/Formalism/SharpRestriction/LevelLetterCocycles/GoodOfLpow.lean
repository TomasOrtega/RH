import Formalism.SharpRestriction.LevelLetterCocycles.ExistsSmulPowEqSumOfInFNc

noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.LevC

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

open Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80.PhiPowers

variable [IsDomain O] [NeZero n]

variable {W}

def Good (A : ArcP n) (c' : ZMod n) (e : ℕ) (T : LocLat G Qp LL O) {d : ℕ} (b : Fin d → W.DD T)
    (sol : Fin d → ℕ → Fin d → LL) (z : W.DD T) : Prop :=
  InFP W T c' e 1 (abelian₂ W A (c' + (e : ZMod n)) e • z) ∧
  ∀ (k : ℕ) (f : Fin d → W.EE),
    RepVV W T c' e (A.M PD.p) (abelian₂ W A (c' + (e : ZMod n)) e) b sol (lA W ^ k • z) f →
    (∀ m, InFr W (c' + (e : ZMod n)) 1 (abelian₂ W A (c' + (e : ZMod n)) e) (f m)) →
    ∃ κ : ℕ, SecIn W (c' + (e : ZMod n)) e (condNN W T (c' + (e : ZMod n)) e b) fun m => lE W κ * f m

/- English proof (translation)
Unfold `lE`. Rewrite using `[pow_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem lE_mul (s t : ℕ) (y : W.EE) : lE W s * (lE W t * y) = lE W (s + t) * y := by
  unfold lE; rw [pow_add]; ring

/- English proof (translation)
Unfold `lE lA`. Rewrite using `[map_pow, map_natCast]`.
-/
theorem lE_eq (t : ℕ) : lE W t = algebraMap (LetA O n) W.EE (lA W ^ t) := by
  unfold lE lA; rw [map_pow, map_natCast]

/- English proof (translation)
Use `repVV_smul W T c' e M Λ b sol _ f (lA_mem W s) h` as an intermediate fact. Rewrite `this` using `[lA_smul_smul, ← lE_eq]`. Then use the resulting hypothesis.
-/
theorem repVV_lA (T : LocLat G Qp LL O) (c' : ZMod n) (e M : ℕ) (Λ : LetA O n) {d : ℕ}
    (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL) (z : W.DD T) (f : Fin d → W.EE) (s t : ℕ)
    (h : RepVV W T c' e M Λ b sol (lA W ^ t • z) f) :
    RepVV W T c' e M Λ b sol (lA W ^ (t + s) • z) (fun m => lE W s * f m) := by
  have := repVV_smul W T c' e M Λ b sol _ f (lA_mem W s) h
  rwa [lA_smul_smul, ← lE_eq] at this

/- English proof (translation)
Use `⟨hz, fun k f hrep hfr => ?_⟩` and prove the remaining obligations. Establish `r1` using `repVV_lA T c' e _ _ b sol z f k₀ k hrep`. Establish `r2` using `repVV_lA T c' e _ _ b sol z f₀ k k₀ hrep₀`. Rewrite `r2` using `[add_comm k₀ k]`. Take `⟨t, ht⟩` from `sec_unique W C.hinj C.hV C.hO2 C.hs C.hR C.hp0 C.h5 C.hTr C.hH C.hCA C.h5p T (C.h3 T hT.1) (C.hmod T hT.1) A hA c' hc' hT b sol hb e _ _ _ r1 r2 (fun m => Formalism.MainNotions.UnusedSlot80.ArcF.inFr_lE W (hfr m) k₀) (fun m => Formalism.MainNotions.UnusedSlot80.ArcF.inFr_lE W (hf …`.

Establish `hD` using `secIn_piLam W C.hR.1 A (c' + (e : ZMod n)) e T b (fun c₀ s hs => dvO_filLow W C.hbij A hA c' hc' T hT b hb.1 e s hs c₀) _ ht`. Establish `hS` using `secIn_add W (Formalism.MainNotions.UnusedSlot80.ArcF.secIn_lE W hD κ₀) (Formalism.MainNotions.UnusedSlot80.ArcF.secIn_lE W hS₀ (t + k))`. Use `⟨κ₀ + (t + k₀), ?_⟩` and prove the remaining obligations. Use `hS using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `m`.

Simplify using `only [Pi.add_apply, lE_mul, mul_sub]`. Rewrite using `[show κ₀ + (t + k₀) = κ₀ + (t + k₀) from rfl]`. Unfold `lE`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem good_of_sec (C : Ctx W) (A : ArcP n) (hA : A.OK) (c' : ZMod n) (hc' : c' ∈ A.cuts)
    (T : LocLat G Qp LL O) (hT : Win W A T) {d : ℕ} (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL)
    (hb : IsHor W T c' b sol) (e : ℕ) (z : W.DD T)
    (hz : InFP W T c' e 1 (abelian₂ W A (c' + (e : ZMod n)) e • z)) (k₀ : ℕ) (f₀ : Fin d → W.EE)
    (hrep₀ : RepVV W T c' e (A.M PD.p) (abelian₂ W A (c' + (e : ZMod n)) e) b sol (lA W ^ k₀ • z) f₀)
    (hfr₀ : ∀ m, InFr W (c' + (e : ZMod n)) 1 (abelian₂ W A (c' + (e : ZMod n)) e) (f₀ m)) (κ₀ : ℕ)
    (hS₀ : SecIn W (c' + (e : ZMod n)) e (condNN W T (c' + (e : ZMod n)) e b) fun m => lE W κ₀ * f₀ m) :
    Good A c' e T b sol z := by
  refine ⟨hz, fun k f hrep hfr => ?_⟩
  have r1 := repVV_lA T c' e _ _ b sol z f k₀ k hrep
  have r2 := repVV_lA T c' e _ _ b sol z f₀ k k₀ hrep₀
  rw [add_comm k₀ k] at r2
  obtain ⟨t, ht⟩ := sec_unique W C.hinj C.hV C.hO2 C.hs C.hR C.hp0 C.h5 C.hTr C.hH C.hCA C.h5p T
    (C.h3 T hT.1) (C.hmod T hT.1) A hA c' hc' hT b sol hb e _ _ _ r1 r2
    (fun m => Formalism.MainNotions.UnusedSlot80.ArcF.inFr_lE W (hfr m) k₀) (fun m => Formalism.MainNotions.UnusedSlot80.ArcF.inFr_lE W (hfr₀ m) k)
  have hD := secIn_piLam W C.hR.1 A (c' + (e : ZMod n)) e T b
    (fun c₀ s hs => dvO_filLow W C.hbij A hA c' hc' T hT b hb.1 e s hs c₀) _ ht
  have hS := secIn_add W (Formalism.MainNotions.UnusedSlot80.ArcF.secIn_lE W hD κ₀) (Formalism.MainNotions.UnusedSlot80.ArcF.secIn_lE W hS₀ (t + k))
  refine ⟨κ₀ + (t + k₀), ?_⟩
  convert hS using 1
  funext m
  simp only [Pi.add_apply, lE_mul, mul_sub]
  rw [show κ₀ + (t + k₀) = κ₀ + (t + k₀) from rfl]
  unfold lE
  ring

/- English proof (translation)
Take `⟨κ, f, hrep, hfr⟩` from `secOfP' W C.hinj C.hO2 C.hR C.hTr C.hH C.hCA C.h5p A hA c' e T hT.1 b sol hb _ h.1`. Take `⟨κ', hS⟩` from `h.2 κ f hrep hfr`. Rewrite `hrep` using `[lA_smul_smul]`. Conclude with `good_of_sec C A hA c' hc' T hT b sol hb e z hz _ f hrep hfr κ' hS`.
-/
theorem good_of_lpow (C : Ctx W) (A : ArcP n) (hA : A.OK) (c' : ZMod n) (hc' : c' ∈ A.cuts)
    (T : LocLat G Qp LL O) (hT : Win W A T) {d : ℕ} (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL)
    (hb : IsHor W T c' b sol) (e K : ℕ) (z : W.DD T)
    (hz : InFP W T c' e 1 (abelian₂ W A (c' + (e : ZMod n)) e • z)) (h : Good A c' e T b sol (lA W ^ K • z)) :
    Good A c' e T b sol z := by
  obtain ⟨κ, f, hrep, hfr⟩ := secOfP' W C.hinj C.hO2 C.hR C.hTr C.hH C.hCA C.h5p A hA c' e T hT.1 b sol hb _
    h.1
  obtain ⟨κ', hS⟩ := h.2 κ f hrep hfr
  rw [lA_smul_smul] at hrep
  exact good_of_sec C A hA c' hc' T hT b sol hb e z hz _ f hrep hfr κ' hS

/- English proof (translation)
Establish `hz : InFP W T c' e 1 (abelian₂ W A (c' + (e : ZMod n)) e • (c • z))`. Rewrite using `[smul_comm]`. Conclude with `Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_smul W T c' e _ hc h.1`. Take `⟨κ, f, hrep, hfr⟩` from `secOfP' W C.hinj C.hO2 C.hR C.hTr C.hH C.hCA C.h5p A hA c' e T hT.1 b sol hb _ h.1`. Take `⟨κ', hS⟩` from `h.2 κ f hrep hfr`.

Establish `hrep'` using `repVV_smul W T c' e _ _ b sol _ f hc hrep`. Rewrite `hrep'` using `[smul_comm]`. Use `good_of_sec C A hA c' hc' T hT b sol hb e _ hz κ _ hrep' (fun m => inFr_mulA W (hfr m) hc) κ' ?_` and prove the remaining obligations. Use `secIn_mulA W hS hc` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `m`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem good_smul (C : Ctx W) (A : ArcP n) (hA : A.OK) (c' : ZMod n) (hc' : c' ∈ A.cuts)
    (T : LocLat G Qp LL O) (hT : Win W A T) {d : ℕ} (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL)
    (hb : IsHor W T c' b sol) (e : ℕ) (z : W.DD T) {c : LetA O n} (hc : c ∈ W.AΔ)
    (h : Good A c' e T b sol z) : Good A c' e T b sol (c • z) := by
  have hz : InFP W T c' e 1 (abelian₂ W A (c' + (e : ZMod n)) e • (c • z)) := by
    rw [smul_comm]; exact Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_smul W T c' e _ hc h.1
  obtain ⟨κ, f, hrep, hfr⟩ := secOfP' W C.hinj C.hO2 C.hR C.hTr C.hH C.hCA C.h5p A hA c' e T hT.1 b sol hb _
    h.1
  obtain ⟨κ', hS⟩ := h.2 κ f hrep hfr
  have hrep' := repVV_smul W T c' e _ _ b sol _ f hc hrep
  rw [smul_comm] at hrep'
  refine good_of_sec C A hA c' hc' T hT b sol hb e _ hz κ _ hrep' (fun m => inFr_mulA W (hfr m) hc) κ' ?_
  have := secIn_mulA W hS hc
  convert this using 1
  funext m; ring

/- English proof (translation)
Establish `hz : InFP W T c' e 1 (abelian₂ W A (c' + (e : ZMod n)) e • (z₁ + z₂))`. Rewrite using `[smul_add]`. Conclude with `Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_add W T c' e _ h₁.1 h₂.1`. Take `⟨κ₁, f₁, hrep₁, hfr₁⟩` from `secOfP' W C.hinj C.hO2 C.hR C.hTr C.hH C.hCA C.h5p A hA c' e T hT.1 b sol hb _ h₁.1`. Take `⟨κ₂, f₂, hrep₂, hfr₂⟩` from `secOfP' W C.hinj C.hO2 C.hR C.hTr C.hH C.hCA C.h5p A hA c' e T hT.1 b sol hb _ h₂.1`.

Take `⟨κ'₁, hS₁⟩` from `h₁.2 κ₁ f₁ hrep₁ hfr₁`. Take `⟨κ'₂, hS₂⟩` from `h₂.2 κ₂ f₂ hrep₂ hfr₂`. Establish `r1` using `repVV_lA T c' e _ _ b sol z₁ f₁ κ₂ κ₁ hrep₁`. Establish `r2` using `repVV_lA T c' e _ _ b sol z₂ f₂ κ₁ κ₂ hrep₂`. Rewrite `r2` using `[add_comm κ₂ κ₁]`.

Establish `r` using `repVV_add W C.hinj T c' e _ _ b sol _ _ _ _ r1 r2`. Rewrite `r` using `[← smul_add]`. Use `good_of_sec C A hA c' hc' T hT b sol hb e _ hz _ _ r (fun m => inFr_add W (Formalism.MainNotions.UnusedSlot80.ArcF.inFr_lE W (hfr₁ m) κ₂) (Formalism.MainNotions.UnusedSlot80.ArcF.inFr_lE W (hfr₂ m) κ₁)) (κ'₁ + κ'₂) ?_` and prove the remaining obligations. Establish `hS` using `secIn_add W (Formalism.MainNotions.UnusedSlot80.ArcF.secIn_lE W hS₁ (κ'₂ + κ₂)) (Formalism.MainNotions.UnusedSlot80.ArcF.secIn_lE W hS₂ (κ'₁ + κ₁))`. Use `hS using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `m`. Simplify using `only [Pi.add_apply]`. Unfold `lE`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem good_add (C : Ctx W) (A : ArcP n) (hA : A.OK) (c' : ZMod n) (hc' : c' ∈ A.cuts)
    (T : LocLat G Qp LL O) (hT : Win W A T) {d : ℕ} (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL)
    (hb : IsHor W T c' b sol) (e : ℕ) (z₁ z₂ : W.DD T)
    (h₁ : Good A c' e T b sol z₁) (h₂ : Good A c' e T b sol z₂) : Good A c' e T b sol (z₁ + z₂) := by
  have hz : InFP W T c' e 1 (abelian₂ W A (c' + (e : ZMod n)) e • (z₁ + z₂)) := by
    rw [smul_add]; exact Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_add W T c' e _ h₁.1 h₂.1
  obtain ⟨κ₁, f₁, hrep₁, hfr₁⟩ := secOfP' W C.hinj C.hO2 C.hR C.hTr C.hH C.hCA C.h5p A hA c' e T hT.1 b sol
    hb _ h₁.1
  obtain ⟨κ₂, f₂, hrep₂, hfr₂⟩ := secOfP' W C.hinj C.hO2 C.hR C.hTr C.hH C.hCA C.h5p A hA c' e T hT.1 b sol
    hb _ h₂.1
  obtain ⟨κ'₁, hS₁⟩ := h₁.2 κ₁ f₁ hrep₁ hfr₁
  obtain ⟨κ'₂, hS₂⟩ := h₂.2 κ₂ f₂ hrep₂ hfr₂
  have r1 := repVV_lA T c' e _ _ b sol z₁ f₁ κ₂ κ₁ hrep₁
  have r2 := repVV_lA T c' e _ _ b sol z₂ f₂ κ₁ κ₂ hrep₂
  rw [add_comm κ₂ κ₁] at r2
  have r := repVV_add W C.hinj T c' e _ _ b sol _ _ _ _ r1 r2
  rw [← smul_add] at r
  refine good_of_sec C A hA c' hc' T hT b sol hb e _ hz _ _ r
    (fun m => inFr_add W (Formalism.MainNotions.UnusedSlot80.ArcF.inFr_lE W (hfr₁ m) κ₂) (Formalism.MainNotions.UnusedSlot80.ArcF.inFr_lE W (hfr₂ m) κ₁))
    (κ'₁ + κ'₂) ?_
  have hS := secIn_add W (Formalism.MainNotions.UnusedSlot80.ArcF.secIn_lE W hS₁ (κ'₂ + κ₂))
    (Formalism.MainNotions.UnusedSlot80.ArcF.secIn_lE W hS₂ (κ'₁ + κ₁))
  convert hS using 1
  funext m
  simp only [Pi.add_apply]
  unfold lE
  ring

end Formalism.MainNotions.UnusedSlot80.LevC
