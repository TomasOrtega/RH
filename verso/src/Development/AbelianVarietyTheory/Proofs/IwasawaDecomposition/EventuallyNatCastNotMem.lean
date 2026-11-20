import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CGTrue
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneParamMonodromyEqZeroIff

noncomputable section

namespace GlobalTheory.HeightCounting

open Formalism.BasicNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.WeilDeligne NumberField IsDedekindDomain Polynomial

/- English proof (translation)
Establish `h0 : (Ideal.span {((l : ℕ) : 𝓞 E)} : Ideal (𝓞 E)) ≠ 0`. Rewrite using `[Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]`. Conclude with `Nat.cast_ne_zero.2 hl.out.ne_zero`. Rewrite using `[Filter.eventually_cofinite]`. Use `(Ideal.finite_factors h0).subset fun w hw => ?_` and prove the remaining obligations.

Simplify `hw` using `[Ideal.dvd_span_singleton]`.
-/
theorem eventually_natCast_notMem (E : Type) [Field E] [NumberField E] (l : ℕ) [hl : Fact l.Prime] :
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ((l : ℕ) : 𝓞 E) ∉ w.asIdeal := by
  have h0 : (Ideal.span {((l : ℕ) : 𝓞 E)} : Ideal (𝓞 E)) ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact Nat.cast_ne_zero.2 hl.out.ne_zero
  rw [Filter.eventually_cofinite]
  refine (Ideal.finite_factors h0).subset fun w hw => ?_
  simpa [Ideal.dvd_span_singleton] using hw

/- English proof (translation)
Proceed by induction on `π using Quotient.inductionOn with | _ π =>`. Take `⟨r, wt, HT, H⟩` from `hG.of_isCsd Ω ι ha (π := π) hr hc`. Use `⟨r, Units.continuous_val.comp H.cont, H.ss, fun w hl A h => ?_⟩` and prove the remaining obligations. Take `⟨σ, hσ, -⟩` from `LocEx.exists_isLocComp hF E a π w`. Rewrite using `[H.wdOf_eq hl (ParLaws.isRec_locRec hL h) hσ]`.

Conclude with `congrArg (fun x : WD h => x.lpTw _) (ParLaws.locPar_mk hL hσ h).symm`.
-/
theorem exists_wdOf_eq_locPar (hL : GlobalTheory.Published.LocalLanglandsGL) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL)
    (hG : GlobalTheory.Published.GaloisRepOfPolarizedCuspidal) {E : Type} (Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω]
    [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a : ℕ} (ha : 1 ≤ a) (π : CG E a)
    (hc : π.IsCsd) (hr : π.IsRegAlg) :
    ∃ r : G E Ω →* GL (Fin a) (Qbar l), Continuous (fun g => (r g : Matrix (Fin a) (Fin a) (Qbar l))) ∧ IsSSRep r ∧
      ∀ (w : HeightOneSpectrum (𝓞 E)) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w),
        wdOf h hl ι r = (ParLaws.locPar hL π h).lpTw ((1 - (a : ℝ)) / 2) := by
  induction π using Quotient.inductionOn with | _ π =>
  obtain ⟨r, wt, HT, H⟩ := hG.of_isCsd Ω ι ha (π := π) hr hc
  refine ⟨r, Units.continuous_val.comp H.cont, H.ss, fun w hl A h => ?_⟩
  obtain ⟨σ, hσ, -⟩ := LocEx.exists_isLocComp hF E a π w
  rw [H.wdOf_eq hl (ParLaws.isRec_locRec hL h) hσ]
  exact congrArg (fun x : WD h => x.lpTw _) (ParLaws.locPar_mk hL hσ h).symm

/- English proof (translation)
Introduce `l _ ι a ha π hc hr`. Use `host_isCMField D.host` as an intermediate fact. Establish `hr' : (C.e a π).1.IsRegAlg` using `(GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by`. Use `(D.naut.ralg_def π).1 hr τ` as an intermediate fact. Rewrite `this` using `[C.inf]`. Then use the resulting hypothesis.

Take `⟨r, h1, h2, h3⟩` from `exists_wdOf_eq_locPar hL hF hG D.nd.Om ι ha (C.e a π).1 ((C.csd a π).1 hc) hr'`. Use `⟨r, h1, h2, ?_⟩` and prove the remaining obligations. Use `filter_upwards [eventually_natCast_notMem D.host.E l, D.naut.locG_unr_ae π] with w hl hu B σ hB hσ`. Establish `hu'` using `(D.naut.unr_tw _ ((1 - (a : ℝ)) / 2)).2 hu`. Establish `e : T.e w (D.naut.lpTw (D.naut.locG π w) ((1 - (a : ℝ)) / 2)) = wdOf (D.nd.plOm.2 w) hl ι r`.

Rewrite using `[T.tw, C.loc, h3]`. Both sides reduce to the same expression. Rewrite using `[galPol, T.frobEig w _ hu', e]`. Conclude with `frobEig_wdOf hl ι h1 (e ▸ (T.unr w _).1 hu') hB hσ`.
-/
theorem CGTrue.galEx (hL : GlobalTheory.Published.LocalLanglandsGL) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL)
    (hG : GlobalTheory.Published.GaloisRepOfPolarizedCuspidal) {D : D7} {T : GlobalTheory.RowTie.WDTie D.nd D.naut} (C : CGTrue hL D T) :
    GalEx D := by
  intro l _ ι a ha π hc hr
  have := host_isCMField D.host
  have hr' : (C.e a π).1.IsRegAlg := (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by
    have := (D.naut.ralg_def π).1 hr τ
    rwa [C.inf] at this
  obtain ⟨r, h1, h2, h3⟩ := exists_wdOf_eq_locPar hL hF hG D.nd.Om ι ha (C.e a π).1 ((C.csd a π).1 hc) hr'
  refine ⟨r, h1, h2, ?_⟩
  filter_upwards [eventually_natCast_notMem D.host.E l, D.naut.locG_unr_ae π] with w hl hu B σ hB hσ
  have hu' := (D.naut.unr_tw _ ((1 - (a : ℝ)) / 2)).2 hu
  have e : T.e w (D.naut.lpTw (D.naut.locG π w) ((1 - (a : ℝ)) / 2)) = wdOf (D.nd.plOm.2 w) hl ι r := by
    rw [T.tw, C.loc, h3]
    rfl
  rw [galPol, T.frobEig w _ hu', e]
  exact frobEig_wdOf hl ι h1 (e ▸ (T.unr w _).1 hu') hB hσ

/- English proof (translation)
Introduce `hL hF hG _ _ ⟨C⟩` and use `C.galEx hL hF hG`.
-/
theorem galEx_of_cgTrue : ∀ hL : GlobalTheory.Published.LocalLanglandsGL, GlobalTheory.Published.AutomorphicFormsFiniteGL →
    GlobalTheory.Published.GaloisRepOfPolarizedCuspidal → ∀ (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut),
      Nonempty (CGTrue hL D T) → GalEx D :=
  fun hL hF hG _ _ ⟨C⟩ => C.galEx hL hF hG

end GlobalTheory.HeightCounting

end
