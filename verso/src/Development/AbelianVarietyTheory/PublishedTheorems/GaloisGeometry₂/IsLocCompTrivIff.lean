import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.CaraianiAboveLHyp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.DualIsConjOfIsCsd
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SemisimpleConjOfTraceEqual
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilTraceEqOfSameWd
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FontaineParameterInvariantUnderConjugation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneParamMonodromyEqZeroIff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CarHyp.Model

open GlobalTheory.TheRec

variable {E : Type} (Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a : ℕ}

omit [IsCMField E] in

/- English proof (translation)
Take `⟨rc', h', -⟩` from `hL.1 E Ω A w h`. Rewrite using `[← H.2 rc' h'.toLit]` and apply the resulting hypothesis.
-/
theorem isRec_of_isTheRec (hL : GlobalTheory.Published.LocalLanglandsGL) {w : HeightOneSpectrum (𝓞 E)} {A : ValuationSubring Ω}
    {h : IsPlaceOver A w} {rc : IrrGL (w.adicCompletion E) → WD h} (H : IsTheRec h rc) : IsRec h rc := by
  obtain ⟨rc', h', -⟩ := hL.1 E Ω A w h
  rwa [← H.2 rc' h'.toLit]

/- English proof (translation)
Introduce `E Ω _ _ _ _ _ _ l _ ι a ha π hc hcoh R hR P AI hT w A h O _ _ _ Bw hj hp σ σ' hσ hσ' rc hrc`. Take `⟨π', c', coh', loc'⟩` from `hd E a π hc hcoh`. Take `⟨R', h1, h2, h3, h4⟩` from `H E Ω l ι a ha π' c' coh'`. Take `⟨p, e⟩` from `hR.2 R' ⟨h1, h2, fun w hl A h rc hrc σ σ' hσ _ hσ' => (h3 w hl A h rc (isRec_of_isTheRec Ω hL hrc) σ' (loc' w σ σ' hσ hσ')).wdOf_eq hl⟩`. Rewrite using `[← (GlobalTheory.PstConj.main E Ω l ι a P AI hT w A h O Bw hj (R.comp (Dec (F := E) A).subtype) (R'.comp (Dec (F := E) A).subtype) p (fun g => e g) hp).2]`.

Conclude with `(h4 P AI hT w A h O Bw hj).2 σ' (loc' w σ σ' hσ hσ') rc (isRec_of_isTheRec Ω hL hrc)`.
-/
theorem caraianiLocalGlobal_of_dual₂ (hL : GlobalTheory.Published.LocalLanglandsGL) (H : GlobalTheory.Published.CaraianiLocalGlobalDual)
    (hd : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (π : CuspSub E a),
      GlobalTheory.ContraPair.DualIsConj π → GKCoh.IsCohomological π →
      ∃ π' : CuspSub E a, GlobalTheory.ContraPair.DualIsConj π' ∧ GKCoh.IsCohomological π' ∧
        ∀ w σ σ', π.IsLocComp w σ → Nonempty (σ'.ρ.Equiv (SmGL.contra σ.ρ)) → π'.IsLocComp w σ') :
    GlobalTheory.Published.CaraianiAboveLHyp := by
  intro E Ω _ _ _ _ _ _ l _ ι a ha π hc hcoh R hR P AI hT w A h O _ _ _ Bw hj hp σ σ' hσ hσ' rc hrc
  obtain ⟨π', c', coh', loc'⟩ := hd E a π hc hcoh
  obtain ⟨R', h1, h2, h3, h4⟩ := H E Ω l ι a ha π' c' coh'
  obtain ⟨p, e⟩ := hR.2 R' ⟨h1, h2, fun w hl A h rc hrc σ σ' hσ _ hσ' =>
    (h3 w hl A h rc (isRec_of_isTheRec Ω hL hrc) σ' (loc' w σ σ' hσ hσ')).wdOf_eq hl⟩
  rw [← (GlobalTheory.PstConj.main E Ω l ι a P AI hT w A h O Bw hj (R.comp (Dec (F := E) A).subtype)
    (R'.comp (Dec (F := E) A).subtype) p (fun g => e g) hp).2]
  exact (h4 P AI hT w A h O Bw hj).2 σ' (loc' w σ σ' hσ hσ') rc (isRec_of_isTheRec Ω hL hrc)

/- English proof (translation)
Take `⟨c, e⟩` from `Submodule.mem_span_singleton.1 φ.2`. Use `Subtype.ext ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `act (.fin _) φ.1 = φ.1`. Rewrite using `[← e]`. Both sides reduce to the same expression.
-/
theorem locRep_triv (w : HeightOneSpectrum (𝓞 E)) (g) (φ : (CuspSub.triv E (le_refl 1)).V) :
    (CuspSub.triv E le_rfl).locRep w g φ = φ := by
  obtain ⟨c, e⟩ := Submodule.mem_span_singleton.1 φ.2
  refine Subtype.ext ?_
  change act (.fin _) φ.1 = φ.1
  rw [← e]; rfl

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨f, h0, hf⟩ g v`. Establish `hinj : Function.Injective f`. Break down `((isIrreducible_iff _).1 σ.irred).2 (LinearMap.ker f) (fun g v hv => by` into its components or cases. Rewrite `hv`, the goal using `[LinearMap.mem_ker]`.

Rewrite using `[hf, hv, map_zero]) with h | h`. Conclude with `LinearMap.ker_eq_bot.1 h`. Conclude with `absurd (LinearMap.ker_eq_top.1 h) h0`. Conclude with `hinj ((hf g v).trans (locRep_triv w g _))`. Introduce `H`.

Use `((isIrreducible_iff _).1 σ.irred).1` as an intermediate fact. Take `⟨v, hv⟩` from `exists_ne (0 : σ.V)`. Take `⟨f, hf⟩` from `Module.Projective.exists_dual_ne_zero ℂ hv`. Set `φ : (CuspSub.triv E (le_refl 1)).V` to `⟨oneFn E 1, Submodule.mem_span_singleton_self _⟩`. Use `⟨f.smulRight φ, fun e => ?_, fun g v => by rw [H, locRep_triv]⟩` and prove the remaining obligations.

Establish `h1` using `congrArg Subtype.val (LinearMap.congr_fun e v)`. Conclude with `(smul_ne_zero hf oneFn_ne_zero) h1`.
-/
theorem isLocComp_triv_iff {w : HeightOneSpectrum (𝓞 E)} (σ : SmIrr (GL (Fin 1) (w.adicCompletion E))) :
    (CuspSub.triv E le_rfl).IsLocComp w σ ↔ ∀ g v, σ.ρ g v = v := by
  constructor
  · rintro ⟨f, h0, hf⟩ g v
    have hinj : Function.Injective f := by
      rcases ((isIrreducible_iff _).1 σ.irred).2 (LinearMap.ker f) (fun g v hv => by
        rw [LinearMap.mem_ker] at hv ⊢; rw [hf, hv, map_zero]) with h | h
      · exact LinearMap.ker_eq_bot.1 h
      · exact absurd (LinearMap.ker_eq_top.1 h) h0
    exact hinj ((hf g v).trans (locRep_triv w g _))
  · intro H
    have := ((isIrreducible_iff _).1 σ.irred).1
    obtain ⟨v, hv⟩ := exists_ne (0 : σ.V)
    obtain ⟨f, hf⟩ := Module.Projective.exists_dual_ne_zero ℂ hv
    let φ : (CuspSub.triv E (le_refl 1)).V := ⟨oneFn E 1, Submodule.mem_span_singleton_self _⟩
    refine ⟨f.smulRight φ, fun e => ?_, fun g v => by rw [H, locRep_triv]⟩
    have h1 := congrArg Subtype.val (LinearMap.congr_fun e v)
    exact (smul_ne_zero hf oneFn_ne_zero) h1

/- English proof (translation)
Take `⟨e⟩` from `e`. Rewrite `h`, the goal using `[isLocComp_triv_iff]`. Introduce `g v`. Apply `e.toLinearEquiv.injective` to reduce the goal to its premises. Establish `h1` using `LinearMap.congr_fun (e.toIntertwiningMap.isIntertwining' g) v`.

Use `h1.trans (Subtype.ext (LinearMap.ext fun x => ?_))` and prove the remaining obligations. Conclude with `congrArg (e.toLinearEquiv v).1 (h g⁻¹ x)`.
-/
theorem isLocComp_contra {w : HeightOneSpectrum (𝓞 E)} {σ σ' : SmIrr (GL (Fin 1) (w.adicCompletion E))}
    (h : (CuspSub.triv E le_rfl).IsLocComp w σ) (e : Nonempty (σ'.ρ.Equiv (SmGL.contra σ.ρ))) :
    (CuspSub.triv E le_rfl).IsLocComp w σ' := by
  obtain ⟨e⟩ := e
  rw [isLocComp_triv_iff] at h ⊢
  intro g v
  apply e.toLinearEquiv.injective
  have h1 := LinearMap.congr_fun (e.toIntertwiningMap.isIntertwining' g) v
  refine h1.trans (Subtype.ext (LinearMap.ext fun x => ?_))
  exact congrArg (e.toLinearEquiv v).1 (h g⁻¹ x)

/- English proof (translation)
Establish `ht : ∀ g (f : Module.Dual ℂ (SmIrr.triv G).V), (SmIrr.triv G).ρ.dual g f = f` using `fun g f => LinearMap.ext fun x => rfl`. Establish `htop : PRep.smoothPart (SmIrr.triv G).ρ.dual = ⊤` using `eq_top_iff.2 fun f _ => SmGL.mem_smoothPart_of_nhds (Filter.univ_mem' fun g => ht g f)`. Set `L : ℂ ≃ₗ[ℂ] Module.Dual ℂ ℂ` to `(LinearMap.ringLmapEquivSelf ℂ ℂ ℂ).symm`. Set `M : (SmIrr.triv G).V ≃ₗ[ℂ] PRep.smoothPart (SmIrr.triv G).ρ.dual` to `L.trans (LinearEquiv.ofTop _ htop).symm`. Conclude with `⟨.mk M fun g => LinearMap.ext fun v => Subtype.ext (ht g _).symm⟩`.
-/
theorem triv_contra (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    Nonempty ((SmIrr.triv G).ρ.Equiv (SmGL.contra (SmIrr.triv G).ρ)) := by
  have ht : ∀ g (f : Module.Dual ℂ (SmIrr.triv G).V), (SmIrr.triv G).ρ.dual g f = f := fun g f => LinearMap.ext fun x => rfl
  have htop : PRep.smoothPart (SmIrr.triv G).ρ.dual = ⊤ := eq_top_iff.2 fun f _ =>
    SmGL.mem_smoothPart_of_nhds (Filter.univ_mem' fun g => ht g f)
  let L : ℂ ≃ₗ[ℂ] Module.Dual ℂ ℂ := (LinearMap.ringLmapEquivSelf ℂ ℂ ℂ).symm
  let M : (SmIrr.triv G).V ≃ₗ[ℂ] PRep.smoothPart (SmIrr.triv G).ρ.dual := L.trans (LinearEquiv.ofTop _ htop).symm
  exact ⟨.mk M fun g => LinearMap.ext fun v => Subtype.ext (ht g _).symm⟩

/- English proof (translation)
Take `⟨a, ha, ε, -, H⟩` from `hrc`. Establish `h1 : SmGL.IsSmoothChar (1 : (w.adicCompletion E)ˣ →* ℂˣ)`. Simplify using `using isSmoothChar_absPow (k := w.adicCompletion E) 0`. Establish `e : (((1 - ((1 : ℕ) : ℝ)) / 2 : ℝ) : ℂ) = 0` using `by simp`. Rewrite using `[algNorm, e, IrrGL.nu_zero, GlobalTheory.GalOfCusp.Model.locComp_triv hσ h1, H.one]`.

Use `WD.sound ⟨.refl _ _, fun σ v => ?_, fun v => rfl⟩` and prove the remaining obligations. Use extensionality with `i`. Simplify using `[WDRep.ofChars]`.
-/
theorem rec_triv {w : HeightOneSpectrum (𝓞 E)} {A : ValuationSubring Ω} {h : IsPlaceOver A w}
    {rc : IrrGL (w.adicCompletion E) → WD h} (hrc : IsRecLit h rc) {σ : SmIrr (GL (Fin 1) (w.adicCompletion E))}
    (hσ : (CuspSub.triv E le_rfl).IsLocComp w σ) : rc (algNorm σ) = WD.mk (WDRep.diag h fun _ : Fin 1 => 1) := by
  obtain ⟨a, ha, ε, -, H⟩ := hrc
  have h1 : SmGL.IsSmoothChar (1 : (w.adicCompletion E)ˣ →* ℂˣ) := by
    simpa using isSmoothChar_absPow (k := w.adicCompletion E) 0
  have e : (((1 - ((1 : ℕ) : ℝ)) / 2 : ℝ) : ℂ) = 0 := by simp
  rw [algNorm, e, IrrGL.nu_zero, GlobalTheory.GalOfCusp.Model.locComp_triv hσ h1, H.one]
  refine WD.sound ⟨.refl _ _, fun σ v => ?_, fun v => rfl⟩
  ext i; simp [WDRep.ofChars]

/- English proof (translation)
The claim follows from `continuous_const ss W _ := let ⟨W', h⟩ := W.exists_isCompl; ⟨W', fun g v hv => by simpa using hv, h⟩ unr w hl A h rc hrc σ σ' hσ _ e := by rw [rec_triv Ω hrc.1 (isLocComp_contra hσ e)] exact (GlobalTheory.GalOfCusp.Model.isWDOf_one hl h ι).wdOf_eq hl`.
-/
theorem isAssoc_triv : IsAssoc (CuspSub.triv E (le_refl 1)) ι (1 : G E Ω →* GL (Fin 1) (Qbar l)) where
  cont := continuous_const
  ss W _ := let ⟨W', h⟩ := W.exists_isCompl; ⟨W', fun g v hv => by simpa using hv, h⟩
  unr w hl A h rc hrc σ σ' hσ _ e := by
    rw [rec_triv Ω hrc.1 (isLocComp_contra hσ e)]
    exact (GlobalTheory.GalOfCusp.Model.isWDOf_one hl h ι).wdOf_eq hl

/- English proof (translation)
Establish `h2 : (CuspSub.triv E (le_refl 1)).IsLocComp w (SmIrr.triv _)` using `(isLocComp_triv_iff _).2 fun _ _ => rfl`. Rewrite using `[H.unr w hl A h rc hrc _ _ h2 ?_ (triv_contra _), rec_triv Ω hrc.1 h2]`. Conclude with `(Submodule.ne_bot_iff _).2 ⟨(1 : ℂ), fun x => (one_smul ℂ _).symm, fun e => one_ne_zero (α := ℂ) e⟩`.
-/
theorem IsAssoc.wdOf_triv {R : G E Ω →* GL (Fin 1) (Qbar l)} (H : IsAssoc (CuspSub.triv E (le_refl 1)) ι R)
    {w : HeightOneSpectrum (𝓞 E)} (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) {A : ValuationSubring Ω} (h : IsPlaceOver A w)
    {rc} (hrc : IsTheRec h rc) : wdOf h hl ι R = WD.mk (WDRep.diag h fun _ : Fin 1 => 1) := by
  have h2 : (CuspSub.triv E (le_refl 1)).IsLocComp w (SmIrr.triv _) := (isLocComp_triv_iff _).2 fun _ _ => rfl
  rw [H.unr w hl A h rc hrc _ _ h2 ?_ (triv_contra _), rec_triv Ω hrc.1 h2]
  exact (Submodule.ne_bot_iff _).2 ⟨(1 : ℂ), fun x => (one_smul ℂ _).symm, fun e => one_ne_zero (α := ℂ) e⟩

/- English proof (translation)
Use `⟨isAssoc_triv Ω ι, fun R hR => GlobalTheory.TraceConjWeil.main E Ω l 1 1 R continuous_const hR.cont (isAssoc_triv Ω ι).ss hR.ss fun w hl A h σ => ?_⟩` and prove the remaining obligations. Take `⟨rc, hrc, -⟩` from `hL.1 E Ω A w h`. Use `GlobalTheory.WdTrace.trace_eq_of_isWDOf E Ω l ι 1 1 R w A h _ (GlobalTheory.GalOfCusp.Model.isWDOf_one hl h ι) ?_ σ` and prove the remaining obligations. Rewrite using `[← IsAssoc.wdOf_triv Ω ι hR hl h (hU.isTheRec_of_isRec hrc)]`. Conclude with `isWDOf_wdOf hl ι (Units.continuous_val.comp hR.cont)`.
-/
theorem isTheRep_triv (hL : GlobalTheory.Published.LocalLanglandsGL) (hU : RecUnique) :
    IsTheRep (CuspSub.triv E (le_refl 1)) ι (1 : G E Ω →* GL (Fin 1) (Qbar l)) := by
  refine ⟨isAssoc_triv Ω ι, fun R hR => GlobalTheory.TraceConjWeil.main E Ω l 1 1 R continuous_const hR.cont
    (isAssoc_triv Ω ι).ss hR.ss fun w hl A h σ => ?_⟩
  obtain ⟨rc, hrc, -⟩ := hL.1 E Ω A w h
  refine GlobalTheory.WdTrace.trace_eq_of_isWDOf E Ω l ι 1 1 R w A h _ (GlobalTheory.GalOfCusp.Model.isWDOf_one hl h ι) ?_ σ
  rw [← IsAssoc.wdOf_triv Ω ι hR hl h (hU.isTheRec_of_isRec hrc)]
  exact isWDOf_wdOf hl ι (Units.continuous_val.comp hR.cont)

/- English proof (translation)
Take `⟨p, e⟩` from `hR.2 1 (isAssoc_triv Ω ι)`. Take `rfl : R = 1` from `MonoidHom.ext fun g => by`. Use `e g` as an intermediate fact. Rewrite `this` using `[MonoidHom.one_apply, eq_mul_inv_iff_mul_eq, one_mul, eq_comm, mul_eq_left]`. Conclude with `this`.

Take `⟨h1, h2⟩` from `(GlobalTheory.LocGlobAll.Model.compat_triv (E := E) Ω ι).2.2.2 P AI hT w A h O Bw hj`. Conclude with `⟨h1, fun σ σ' hσ e rc hrc => h2 σ' (isLocComp_contra hσ e) rc (isRec_of_isTheRec Ω hL hrc)⟩`.
-/
theorem concl_triv (hL : GlobalTheory.Published.LocalLanglandsGL) {R : G E Ω →* GL (Fin 1) (Qbar l)}
    (hR : IsTheRep (CuspSub.triv E (le_refl 1)) ι R) (P : LocPrime l) (AI : LocAinf l P) (hT : Nonempty (LocTied l P AI))
    (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
    (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw) :
    IsPstAt P Bw (R.comp (Dec (F := E) A).subtype) ∧ ∀ σ σ', (CuspSub.triv E (le_refl 1)).IsLocComp w σ →
      Nonempty (σ'.ρ.Equiv (SmGL.contra σ.ρ)) → ∀ rc, IsTheRec h rc →
        wdAt P ι Bw h hj (R.comp (Dec (F := E) A).subtype) = rc (algNorm σ') := by
  obtain ⟨p, e⟩ := hR.2 1 (isAssoc_triv Ω ι)
  obtain rfl : R = 1 := MonoidHom.ext fun g => by
    have := e g
    rw [MonoidHom.one_apply, eq_mul_inv_iff_mul_eq, one_mul, eq_comm, mul_eq_left] at this
    exact this
  obtain ⟨h1, h2⟩ := (GlobalTheory.LocGlobAll.Model.compat_triv (E := E) Ω ι).2.2.2 P AI hT w A h O Bw hj
  exact ⟨h1, fun σ σ' hσ e rc hrc => h2 σ' (isLocComp_contra hσ e) rc (isRec_of_isTheRec Ω hL hrc)⟩

/- English proof (translation)
Introduce `H`. Establish `h3` using `IsAssoc.wdOf_triv Ω ι H hl h hrc`. Rewrite `h3` using `[wdOf_cyc]`. Establish `h4` using `congrArg (fun x : WD h => x.charPol (frob h)) h3`. Simplify using `only [WD.lpTw_mk, WD.charPol_mk] at h4`.

Establish `e1 : (WDRep.diag h fun _ : Fin 1 => (1 : ℂˣ)).ρ (frob h) = 1` using `by ext; simp`. Rewrite `h4` using `[WDRep.tw_ρ, e1, deg_frob]`. Establish `h5` using `LinearMap.aeval_self_charpoly ((((normV w : ℕ) : ℂ) ^ (((1 : ℝ) : ℝ) : ℂ)) ^ (1 : ℤ) • (1 : Module.End ℂ (Fin 1 → ℂ)))`. Rewrite `h5` using `[h4, LinearMap.charpoly_one]`. Establish `h6` using `congrFun (LinearMap.congr_fun h5 fun _ => 1) 0`.

Simplify using `[sub_eq_zero] at h6`. Conclude with `(one_lt_normV w).ne' h6`.
-/
theorem not_isAssoc_cyc {w : HeightOneSpectrum (𝓞 E)} (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) {A : ValuationSubring Ω}
    (h : IsPlaceOver A w) {rc} (hrc : IsTheRec h rc) :
    ¬ IsAssoc (CuspSub.triv E (le_refl 1)) ι ((Matrix.GeneralLinearGroup.scalar (Fin 1)).comp (cyc E Ω l)) := by
  intro H
  have h3 := IsAssoc.wdOf_triv Ω ι H hl h hrc
  rw [wdOf_cyc] at h3
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

end GlobalTheory.CarHyp.Model

end
