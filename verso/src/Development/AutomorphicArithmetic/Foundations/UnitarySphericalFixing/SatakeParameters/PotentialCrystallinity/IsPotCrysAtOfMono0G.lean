import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.IsPotCrysAtOfMono0
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.ExistsCgTrueCharSide
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.Multi
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToralAndGoodOfIsSpherical
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow

noncomputable section

namespace GlobalTheory.HodgeOfTrue
open GlobalTheory.TripleLocal

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.Pst GlobalTheory.GalOfCusp GlobalTheory.HeightCounting
open GlobalTheory.RowTie (WDTie)
open Matrix (GeneralLinearGroup)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section G
variable {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] {a : ℕ}

/- English proof (translation)
The claim follows from `GlobalTheory.HeightCounting.Blocks.locPar_twist_absPow hL hF π hν h`.
-/
theorem locPar_twist_abs_m (hL : GlobalTheory.Published.LocalLanglandsGL) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) (π : CG E a)
    {ν : HChar E} {s : ℝ} (hν : ν.IsAbsPow s) {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} (h : IsPlaceOver A w) :
    ParLaws.locPar hL (π.twist ν) h = (ParLaws.locPar hL π h).lpTw s :=
  GlobalTheory.HeightCounting.Blocks.locPar_twist_absPow hL hF π hν h

/- English proof (translation)
Take `⟨_, _, _, -, H⟩` from `ParLaws.isRec_locRec hL h`. Conclude with `(GlobalTheory.SphSupport.toral_and_good_of_isSpherical UpperTheory.Zero.LLC.Pr.bz _ _ ((H.sph _).2 hu)).2`.
-/
theorem good_of_unr (hL : GlobalTheory.Published.LocalLanglandsGL) (π : CG E a) {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
    (h : IsPlaceOver A w) (hu : (ParLaws.locPar hL π h).unr) :
    UpperTheory.Zero.LLC.Good (⟨a, ParLaws.toCl (π.loc w)⟩ : IrrGL (w.adicCompletion E)) := by
  obtain ⟨_, _, _, -, H⟩ := ParLaws.isRec_locRec hL h
  exact (GlobalTheory.SphSupport.toral_and_good_of_isSpherical UpperTheory.Zero.LLC.Pr.bz _ _ ((H.sph _).2 hu)).2

/- English proof (translation)
Establish `hc' : (π₀.twist ξ).IsCsd` using `CG.IsCsd.twist hξc (π := CG.mk π₀) hc`. Take `⟨r₀, wt₀, HT₀, H₀, K₀⟩` from `hGL E Ω l ι a ha _ hc' hreg`. Establish `e0 : (π₀.twist ξ).twist (ξ⁻¹ * ν) = π₀.twist ν`. Rewrite using `[← CuspSub.twist_mul, mul_inv_cancel_left]`. Establish `hψu : ∀ v, (ξ⁻¹ * ν).UnrAt v` using `fun v => (hξu v).inv.mul (hν.1 v)`.

Establish `hp : ∃ χ', IsPolarized ((CuspSub.triv E (le_refl 1)).twist (ξ⁻¹ * ν)) χ'`. Rewrite using `[CuspSub.twist_mul]`. Conclude with `isPolarized_twist hξc' hν`. Take `⟨c, hcc, hcf, hcr⟩` from `exists_crystalline_galois_character (Ω := Ω) hL hF hG ι (ξ⁻¹ * ν) hψu hint hp`. Establish `hc0 : Continuous fun g => (r₀ g : Matrix (Fin a) (Fin a) (Qbar l))` using `Units.continuous_val.comp H₀.cont`.

Establish `hc1 : Continuous fun g => (r g : Matrix (Fin a) (Fin a) (Qbar l))` using `Units.continuous_val.comp H.cont`. Establish `hc2 : Continuous fun g => (twistBy c r₀ g : Matrix (Fin a) (Fin a) (Qbar l))`. Simplify using `only [coe_twistBy]`. Conclude with `(Units.continuous_val.comp hcc).smul hc0`. Take `⟨B, hBc⟩` from `conj_of_frob hD hc1 hc2 H.ss (isSSRep_twistBy c H₀.ss) (by filter_upwards [eventually_natCast_notMem E l, ParLaws.eventually_unr (Ω := Ω) hL hF (CG.mk (π₀.twist ξ))] with w hl hu Bp g hBp hg`.

Establish `e3 : ParLaws.locPar hL (CG.mk (π₀.twist ν)) hBp = (ParLaws.locPar hL (CG.mk (π₀.twist ξ)) hBp).lpChar (ParLaws.locPar hL (CG.ofChar (ξ⁻¹ * ν)) hBp)`. Rewrite using `[← e0]`. Conclude with `UpperTheory.One.M.locPar_twist hL hF (CG.mk (π₀.twist ξ)) _ hBp (good_of_unr hL _ hBp (hu _ hBp))`. Take `⟨y1, y2⟩` from `locPar_ofChar_unr hL (ξ⁻¹ * ν) hBp (hψu w)`. Establish `u1` using `hu _ hBp`.

Establish `e1` using `H.eq_locPar hL hF hl hBp (by rw [e3]; exact WD.unr_lpChar _ _ u1 y1)`. Establish `e2` using `H₀.eq_locPar hL hF hl hBp u1`. Establish `u2 : (wdOf hBp hl ι r).unr` using `by rw [e1, e3, WD.unr_tw]; exact WD.unr_lpChar _ _ u1 y1`. Establish `u3 : (wdOf hBp hl ι r₀).unr` using `by rw [e2, WD.unr_tw]; exact u1`. Establish `f1` using `frobEig_wdOf hl ι hc1 u2 hBp hg`.

Establish `f2` using `frobEig_wdOf hl ι hc0 u3 hBp hg`. Rewrite `f1` using `[e1, e3, WD.frobEig_tw _ _ (WD.unr_lpChar _ _ u1 y1), WD.frobEig_char _ _ _ u1 y1 y2]`. Rewrite `f2` using `[e2, WD.frobEig_tw _ _ u1]`. Apply `Polynomial.map_injective ι.toRingHom ι.injective` to reduce the goal to its premises. Rewrite using `[f1, coe_twistBy]`.

Establish `f3 : (((c g : Qbar l) • (r₀ g : Matrix (Fin a) (Fin a) (Qbar l))).charpoly.map ι.toRingHom) = ((ι (c g : Qbar l)) • ((r₀ g : Matrix (Fin a) (Fin a) (Qbar l)).map ι.toRingHom)).charpoly`. Rewrite using `[← Matrix.charpoly_map]`. Use `congr 1`. Use extensionality with `i j`. Simplify using the standard rewrite rules.

Rewrite using `[f3, GlobalTheory.Triple.charpoly_smul_of_prod _ _ _ (by rw [Matrix.charpoly_map]; exact f2), hcf w hl Bp g hBp hg]`. Simplify using `only [Multiset.map_map, Function.comp_def]`. Use `congr 1`. Use `Multiset.map_congr rfl fun x _ => ?_` and prove the remaining obligations. Use `congr 2`.

Use the proof step `ring)`. Take `⟨σ₁, hσ₁, -⟩` from `LocEx.exists_isLocComp hF E a (π₀.twist ξ) w`. Establish `g2 : ParLaws.locRec hL h (algNorm σ₁) = (ParLaws.locPar hL (CG.mk (π₀.twist ξ)) h).lpTw ((1 - (a : ℝ)) / 2)`. Rewrite using `[rec_algNorm (ParLaws.isRec_locRec hL h) σ₁]`. Conclude with `congrArg (fun x : WD h => x.lpTw _) (ParLaws.locPar_mk hL hσ₁ h).symm`.

Establish `hn : UpperTheory.GalS.NcW ((ParLaws.locPar hL (CG.mk (π₀.twist ξ)) h).lpTw ((1 - (a : ℝ)) / 2))`. Establish `e4 : ParLaws.locPar hL (CG.mk (π₀.twist ξ)) h = (ParLaws.locPar hL (CG.mk π₀) h).lpChar (ParLaws.locPar hL (CG.ofChar ξ) h)` using `UpperTheory.One.M.locPar_twist hL hF (CG.mk π₀) ξ h hgood`. Rewrite using `[e4]`. Conclude with `(hm.char (ParLaws.lpDim_locPar hL _ h) (locPar_ofChar_unr hL ξ h (hξu w)).1).tw _`. Establish `g1` using `K₀ P AI ⟨T⟩ w hw A h O Bw hj σ₁ hσ₁ _ (ParLaws.isRec_locRec hL h) (g2 ▸ hn)`.

Establish `hm' : (wdAt P ι Bw h hj (r₀.comp (Dec (F` using `E) A).subtype)).mono0 := g1.mono (g2 ▸ hn.2.1)`. Establish `hab` using `H₀.above P AI ⟨T⟩ w A h O Bw hj`. Establish `hpst` using `hB.isPstAt T Bw (r₀.comp (Dec (F := E) A).subtype) (H₀.cont.comp continuous_subtype_val |> Units.continuous_val.comp) (hab.deRham (UpperTheory.GalS.nice_of_locPar hL hF h hn))`. Establish `hpot` using `(GlobalTheory.PstLaws.wdParameterAt_monodromy_zero_iff_potCrystalline Bw h hj P ι _ hpst).1 hm'`. Establish `hpot2` using `potCrys_twistBy T Bw (c.comp (Dec (F := E) A).subtype) (r₀.comp (Dec (F := E) A).subtype) hpot (hcr P AI ⟨T⟩ w A h O Bw hj)`.

Use `(GlobalTheory.ConjLocal.local_conj l P E Ω O _ Bw a _ (r.comp (Dec (F := E) A).subtype) B⁻¹ (fun g => ?_)).2.2.1 hpot2` and prove the remaining obligations. Use `hBc g` as an intermediate fact. Express the relevant statement in the definitionally equal form `r g = B⁻¹ * twistBy c r₀ g * B⁻¹⁻¹`. Rewrite using `[this]`. Use `group`.
-/
theorem isPotCrysAt_of_mono0_g (hL : GlobalTheory.Published.LocalLanglandsGL) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL)
    (hG : UpperTheory.GalS.CuspU) (hB : GlobalTheory.Published.DeRhamPotSemistable) (hGL : UpperTheory.GalS.CarU)
    (hD : ∀ S : Set (HeightOneSpectrum (𝓞 E)), S.Finite → Dense {g : G E Ω | ∃ w ∉ S, ∃ B : ValuationSubring Ω,
      IsPlaceOver (F := E) B w ∧ IsFrob (F := E) B (normV w) g})
    {π₀ : CuspSub E a} (ha : 2 ≤ a) (hc : π₀.IsCsd) {ν : HChar E} {s : ℝ} (hν : ν.IsAbsPow s)
    {ξ : HChar E} (hξu : ∀ v, ξ.UnrAt v) (hξc : (CG.ofChar ξ).IsCsd) (hξc' : (CG.ofChar ξ⁻¹).IsCsd)
    (hreg : (CG.mk (π₀.twist ξ)).IsRegAlg) (hint : ∀ τ, ∃ n : ℤ, expo (ξ⁻¹ * ν) τ = n)
    {ι : Qbar l ≃+* ℂ} {χ : HChar (maximalRealSubfield E)} {r : G E Ω →* GL (Fin a) (Qbar l)} {wt : ℤ}
    {HT : (E →+* Qbar l) → Multiset ℤ} (H : UpperTheory.GalS.IsGalU (π₀.twist ν) χ ι r wt HT)
    {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) {w : HeightOneSpectrum (𝓞 E)} (hw : w ∈ placesOver E l)
    {A : ValuationSubring Ω} (h : IsPlaceOver A w) {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw)
    (hm : UpperTheory.GalS.NcW (ParLaws.locPar hL (CG.mk π₀) h))
    (hgood : UpperTheory.Zero.LLC.Good (⟨a, ParLaws.toCl ((CG.mk π₀).loc w)⟩ : IrrGL (w.adicCompletion E))) :
    IsPotCrysAt P Bw (r.comp (Dec (F := E) A).subtype) := by
  have hc' : (π₀.twist ξ).IsCsd := CG.IsCsd.twist hξc (π := CG.mk π₀) hc
  obtain ⟨r₀, wt₀, HT₀, H₀, K₀⟩ := hGL E Ω l ι a ha _ hc' hreg
  have e0 : (π₀.twist ξ).twist (ξ⁻¹ * ν) = π₀.twist ν := by
    rw [← CuspSub.twist_mul, mul_inv_cancel_left]
  have hψu : ∀ v, (ξ⁻¹ * ν).UnrAt v := fun v => (hξu v).inv.mul (hν.1 v)
  have hp : ∃ χ', IsPolarized ((CuspSub.triv E (le_refl 1)).twist (ξ⁻¹ * ν)) χ' := by
    rw [CuspSub.twist_mul]
    exact isPolarized_twist hξc' hν
  obtain ⟨c, hcc, hcf, hcr⟩ := exists_crystalline_galois_character (Ω := Ω) hL hF hG ι (ξ⁻¹ * ν) hψu hint hp
  have hc0 : Continuous fun g => (r₀ g : Matrix (Fin a) (Fin a) (Qbar l)) := Units.continuous_val.comp H₀.cont
  have hc1 : Continuous fun g => (r g : Matrix (Fin a) (Fin a) (Qbar l)) := Units.continuous_val.comp H.cont
  have hc2 : Continuous fun g => (twistBy c r₀ g : Matrix (Fin a) (Fin a) (Qbar l)) := by
    simp only [coe_twistBy]
    exact (Units.continuous_val.comp hcc).smul hc0
  obtain ⟨B, hBc⟩ := conj_of_frob hD hc1 hc2 H.ss (isSSRep_twistBy c H₀.ss) (by
    filter_upwards [eventually_natCast_notMem E l, ParLaws.eventually_unr (Ω := Ω) hL hF (CG.mk (π₀.twist ξ))] with w hl hu Bp g hBp hg
    have e3 : ParLaws.locPar hL (CG.mk (π₀.twist ν)) hBp =
        (ParLaws.locPar hL (CG.mk (π₀.twist ξ)) hBp).lpChar (ParLaws.locPar hL (CG.ofChar (ξ⁻¹ * ν)) hBp) := by
      rw [← e0]
      exact UpperTheory.One.M.locPar_twist hL hF (CG.mk (π₀.twist ξ)) _ hBp (good_of_unr hL _ hBp (hu _ hBp))
    obtain ⟨y1, y2⟩ := locPar_ofChar_unr hL (ξ⁻¹ * ν) hBp (hψu w)
    have u1 := hu _ hBp
    have e1 := H.eq_locPar hL hF hl hBp (by rw [e3]; exact WD.unr_lpChar _ _ u1 y1)
    have e2 := H₀.eq_locPar hL hF hl hBp u1
    have u2 : (wdOf hBp hl ι r).unr := by rw [e1, e3, WD.unr_tw]; exact WD.unr_lpChar _ _ u1 y1
    have u3 : (wdOf hBp hl ι r₀).unr := by rw [e2, WD.unr_tw]; exact u1
    have f1 := frobEig_wdOf hl ι hc1 u2 hBp hg
    have f2 := frobEig_wdOf hl ι hc0 u3 hBp hg
    rw [e1, e3, WD.frobEig_tw _ _ (WD.unr_lpChar _ _ u1 y1), WD.frobEig_char _ _ _ u1 y1 y2] at f1
    rw [e2, WD.frobEig_tw _ _ u1] at f2
    apply Polynomial.map_injective ι.toRingHom ι.injective
    rw [f1, coe_twistBy]
    have f3 : (((c g : Qbar l) • (r₀ g : Matrix (Fin a) (Fin a) (Qbar l))).charpoly.map ι.toRingHom) =
        ((ι (c g : Qbar l)) • ((r₀ g : Matrix (Fin a) (Fin a) (Qbar l)).map ι.toRingHom)).charpoly := by
      rw [← Matrix.charpoly_map]
      congr 1
      ext i j
      simp
    rw [f3, GlobalTheory.Triple.charpoly_smul_of_prod _ _ _ (by rw [Matrix.charpoly_map]; exact f2), hcf w hl Bp g hBp hg]
    simp only [Multiset.map_map, Function.comp_def]
    congr 1
    refine Multiset.map_congr rfl fun x _ => ?_
    congr 2
    ring)
  obtain ⟨σ₁, hσ₁, -⟩ := LocEx.exists_isLocComp hF E a (π₀.twist ξ) w
  have g2 : ParLaws.locRec hL h (algNorm σ₁) =
      (ParLaws.locPar hL (CG.mk (π₀.twist ξ)) h).lpTw ((1 - (a : ℝ)) / 2) := by
    rw [rec_algNorm (ParLaws.isRec_locRec hL h) σ₁]
    exact congrArg (fun x : WD h => x.lpTw _) (ParLaws.locPar_mk hL hσ₁ h).symm
  have hn : UpperTheory.GalS.NcW ((ParLaws.locPar hL (CG.mk (π₀.twist ξ)) h).lpTw ((1 - (a : ℝ)) / 2)) := by
    have e4 : ParLaws.locPar hL (CG.mk (π₀.twist ξ)) h =
        (ParLaws.locPar hL (CG.mk π₀) h).lpChar (ParLaws.locPar hL (CG.ofChar ξ) h) :=
      UpperTheory.One.M.locPar_twist hL hF (CG.mk π₀) ξ h hgood
    rw [e4]
    exact (hm.char (ParLaws.lpDim_locPar hL _ h) (locPar_ofChar_unr hL ξ h (hξu w)).1).tw _
  have g1 := K₀ P AI ⟨T⟩ w hw A h O Bw hj σ₁ hσ₁ _ (ParLaws.isRec_locRec hL h) (g2 ▸ hn)
  have hm' : (wdAt P ι Bw h hj (r₀.comp (Dec (F := E) A).subtype)).mono0 := g1.mono (g2 ▸ hn.2.1)
  have hab := H₀.above P AI ⟨T⟩ w A h O Bw hj
  have hpst := hB.isPstAt T Bw (r₀.comp (Dec (F := E) A).subtype) (H₀.cont.comp continuous_subtype_val |> Units.continuous_val.comp)
    (hab.deRham (UpperTheory.GalS.nice_of_locPar hL hF h hn))
  have hpot := (GlobalTheory.PstLaws.wdParameterAt_monodromy_zero_iff_potCrystalline Bw h hj P ι _ hpst).1 hm'
  have hpot2 := potCrys_twistBy T Bw (c.comp (Dec (F := E) A).subtype) (r₀.comp (Dec (F := E) A).subtype) hpot
    (hcr P AI ⟨T⟩ w A h O Bw hj)
  refine (GlobalTheory.ConjLocal.local_conj l P E Ω O _ Bw a _ (r.comp (Dec (F := E) A).subtype) B⁻¹ (fun g => ?_)).2.2.1 hpot2
  have := hBc g
  change r g = B⁻¹ * twistBy c r₀ g * B⁻¹⁻¹
  rw [this]
  group

end G

/- English proof (translation)
Introduce `l _ ι π s hc hr`. Use `host_isCMField D.host` as an intermediate fact. Establish `ha : 2 ≤ D.R.r`. Use `D.R.two_le_m` as an intermediate fact. Use `D.R.m_add_three_le_k` as an intermediate fact.

Unfold `Ranks.r`. Use linear arithmetic over natural numbers and integers. Take `⟨π₀, hπ₀⟩` from `Quotient.exists_rep (C.e _ π).1`. Establish `hmk : CG.mk π₀ = (C.e _ π).1` using `hπ₀`. Establish `hc₀ : π₀.IsCsd`.

Establish `h1` using `(C.csd _ π).1 hc`. Rewrite `h1` using `[CGu.IsCsd, ← hmk]`. Conclude with `h1`. Establish `hν` using `GlobalTheory.HeckeGal.Model.absPow_isAbsPow D.host.E s`. Use `set ν := GlobalTheory.HeckeGal.Model.absPow D.host.E s`.

Establish `inf₁ : ∀ τ, (CG.mk (π₀.twist ν)).infChar τ = (D.naut.infG π τ).map (· + (s : ℂ))` using `fun τ => by`. Establish `h1` using `(ParLaws.hasInfChar_infChar (CG.mk π₀) τ).twist ν`. Rewrite `h1` using `[(GlobalTheory.T.heckeChar_exponent_of_infinityType _ ν).2.1 s hν τ]`. Rewrite using `[C.inf, CGu.infChar, ← hmk]`. Conclude with `h1.infChar_eq`.

Establish `hreg : (CG.mk (π₀.twist ν)).IsRegAlg` using `(GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by`. Take `⟨h1, h2⟩` from `hr τ`. Rewrite using `[inf₁]`. Use `⟨h1.map (add_left_injective _), fun z hz => ?_⟩` and prove the remaining obligations. Take `⟨y, hy, rfl⟩` from `Multiset.mem_map.1 hz`.

Conclude with `h2 y hy`. Take `⟨ψp, hP⟩` from `isPolarized_twist hc₀ hν`. Take `⟨r, wt, HT, H⟩` from `hG _ D.nd.Om l ι _ (by omega) _ ψp hreg hP`. Establish `hloc : ∀ (w : PlE D.host) (u : ℝ), T.e w (D.naut.lpTw (D.naut.locG π w) u) = (ParLaws.locPar hL (CG.mk π₀) (D.nd.plOm.2 w)).lpTw u` using `fun w u => by`. Rewrite using `[T.tw, C.loc, hmk]`.

Both sides reduce to the same expression. Establish `haway : ∀ (w : PlE D.host) (hl : ((l : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal), UpperTheory.GalS.Aw (wdOf (D.nd.plOm.2 w) hl ι r) (T.e w (D.naut.lpTw (D.naut.locG π w) (s + (1 - (D.R.r : ℝ)) / 2)))` using `fun w hl => by`. Establish `e` using `locPar_twist_abs_m hL hF (CG.mk π₀) hν (D.nd.plOm.2 w)`. Establish `k` using `H.aw_locPar hL hF hl (D.nd.plOm.2 w)`. Rewrite `k` using `[show ParLaws.locPar hL (CG.mk (π₀.twist ν)) (D.nd.plOm.2 w) = _ from e, WD.lpTw_add, ← hloc]`.

Conclude with `k`. Establish `hv : s + (1 - (D.R.r : ℝ)) / 2 + (wt : ℝ) / 2 = 0`. Establish `hm : ∀ τ, π₀.HasInfChar τ ((CG.mk π₀).infChar τ)` using `fun τ => ParLaws.hasInfChar_infChar (CG.mk π₀) τ`. Establish `hw` using `GlobalTheory.TempSatGal.weight_eq_rank_sub_one_sub_two_mul_of_inf_char_shift (by omega) H (fun τ => (CG.mk π₀).infChar τ) s (fun τ => (hm τ).1) (fun τ => by rw [inf₁, C.inf, CGu.infChar, ← hmk]) (fun τ => GlobalTheory.CsdTwistGal.infChar_conj_of_isCsd _ _ π₀ hc₀ τ _ _ (hm τ) (hm …`. Rewrite using `[hw]`.

Expand and normalize the polynomial expressions, which then agree. Establish `htemp : ∀ w : PlE D.host, ((l : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal → D.naut.unr (D.naut.locG π w) → ∀ α ∈ D.naut.frobEig (D.naut.locG π w), ‖α‖ ≤ ((normV w : ℕ) : ℝ) ^ (((D.R.r : ℝ) + 3) / 2)` using `fun w hl hu α hα => by`. Take `⟨-, hU, hS⟩` from `GlobalTheory.HeightCounting.Blocks.readsCusp hF C`. Take `⟨B, hB, e⟩` from `hS _ π w (by omega) hu`. Rewrite `hα` using `[e]`.

Take `⟨b, hb, rfl⟩` from `Multiset.mem_map.1 hα`. Establish `k : UpperTheory.GalN.OpenB (Formalism.ConjugateSelfDual.normV w) (b : ℂ)` using `PositivityTheory.JacquetShalikaLocal.jacquetShalikaBound D.host.E _ _ (hU _ π (by omega)) w B hB b hb`. Rewrite using `[Units.val_inv_eq_inv_val]`. Establish `hq` using `UpperTheory.GalN.one_lt_q (H := D.host) w`. Use `(k.inv hq).2.le.trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hq.le) ?_)` and prove the remaining obligations.

Establish `: (0 : ℝ) ≤ D.R.r` using `Nat.cast_nonneg _`. Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨r, ⟨Units.continuous_val.comp H.cont, H.ss, haway, htemp⟩, fun w hw O _ _ _ Bw hj => ?_⟩` and prove the remaining obligations. Establish `hpar : T.e w (D.naut.locG π w) = ParLaws.locPar hL (CG.mk π₀) (D.nd.plOm.2 w)`. Rewrite using `[C.loc, hmk]`.

Both sides reduce to the same expression. Establish `hab` using `H.above (D.loc l) (D.locA l) ⟨D.locT l⟩ w _ (D.nd.plOm.2 w) O Bw hj`. Establish `hN : UpperTheory.GalS.Nc D.nd D.naut (D.naut.locG π w) → UpperTheory.GalS.Nice (π₀.twist ν) (D.nd.plOm.2 w)` using `fun k => by`. Use `UpperTheory.GalS.nice_of_locPar hL hF _ (UpperTheory.GalS.NcW.tw ?_ _)` and prove the remaining obligations. Establish `e` using `locPar_twist_abs_m hL hF (CG.mk π₀) hν (D.nd.plOm.2 w)`.

Rewrite using `[show ParLaws.locPar hL (CG.mk (π₀.twist ν)) (D.nd.plOm.2 w) = _ from e, ← hpar]`. Conclude with `(UpperTheory.GalS.ncW_of_nc T k).tw _`. Use `⟨fun k => ⟨hab.deRham (hN k), fun τ L τ' hτ => ⟨HT τ, ?_, hab.jumps (hN k) τ L τ' hτ⟩⟩, fun hu => ?_, fun hm => ?_⟩` and prove the remaining obligations. Rewrite using `[H.weights, inf₁, Multiset.map_map]`. Use `Multiset.map_congr rfl fun z _ => ?_` and prove the remaining obligations.

Simplify using `only [Function.comp_apply]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨σ₀, hσ₀, -⟩` from `LocEx.exists_isLocComp hF _ _ (π₀.twist ν) w`. Use `hab.crys σ₀ hσ₀ ((ParLaws.unr_iff (ParLaws.isRec_locRec hL (D.nd.plOm.2 w)) (ParLaws.toRep σ₀)).1 ?_)` and prove the remaining obligations. Rewrite using `[← ParLaws.locPar_mk hL hσ₀ (D.nd.plOm.2 w)]`.

Establish `e` using `locPar_twist_abs_m hL hF (CG.mk π₀) hν (D.nd.plOm.2 w)`. Rewrite using `[show ParLaws.locPar hL (CG.mk (π₀.twist ν)) (D.nd.plOm.2 w) = _ from e, WD.unr_tw, ← hpar]`. Conclude with `(T.unr w _).1 hu`. Establish `hm' : UpperTheory.GalS.NcW (ParLaws.locPar hL (CG.mk π₀) (D.nd.plOm.2 w))`. Rewrite using `[← hpar]`.

Conclude with `UpperTheory.GalS.ncW_of_nc T hm`. Establish `hgood : UpperTheory.Zero.LLC.Good (⟨D.R.r, ParLaws.toCl ((CG.mk π₀).loc w)⟩ : IrrGL (w.adicCompletion D.host.E))`. Rewrite using `[hmk]`. Conclude with `UpperTheory.One.M.Old.cgGood sw C _ π w`. Establish `hs2 : 2 * s = ((D.R.r : ℤ) - 1 - wt : ℤ)`.

Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `key : ∀ ξ : HChar D.host.E, (∀ τ, ∃ n : ℤ, expo ξ τ = (s : ℂ) + n) → (CG.mk (π₀.twist ξ)).IsRegAlg ∧ ∀ τ, ∃ n : ℤ, expo (ξ⁻¹ * ν) τ = n` using `fun ξ hξ => by`. Use `⟨(GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => ?_, fun τ => ?_⟩` and prove the remaining obligations. Take `⟨h1, h2⟩` from `hr τ`.

Take `⟨n, hn⟩` from `hξ τ`. Establish `e` using `((ParLaws.hasInfChar_infChar (CG.mk π₀) τ).twist ξ).infChar_eq`. Establish `e' : (CG.mk (π₀.twist ξ)).infChar τ = (D.naut.infG π τ).map (· + expo ξ τ)`. Rewrite using `[C.inf, CGu.infChar, ← hmk]`. Conclude with `e`.

Rewrite using `[e']`. Use `⟨h1.map (add_left_injective _), fun z hz => ?_⟩` and prove the remaining obligations. Take `⟨y, hy, rfl⟩` from `Multiset.mem_map.1 hz`. Take `⟨m, hm2⟩` from `h2 y hy`. Use `⟨m + n, ?_⟩` and prove the remaining obligations.

Simplify using `only [hn]`. Use `push_cast`. Take the linear combination `hm2`. Take `⟨n, hn⟩` from `hξ τ`. Use `⟨-n, ?_⟩` and prove the remaining obligations.

Rewrite using `[expo_mul, expo_inv, hn, (GlobalTheory.T.heckeChar_exponent_of_infinityType _ ν).2.1 s hν τ]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hD : ∀ S : Set (HeightOneSpectrum (𝓞 D.host.E)), S.Finite → Dense {g : G D.host.E D.nd.Om | ∃ w ∉ S, ∃ B : ValuationSubring D.nd.Om, IsPlaceOver (F` using `D.host.E) B w ∧ IsFrob (F := D.host.E) B (normV w) g} := fun S hS => Dense.mono (by rintro g ⟨w, h1, -, h2⟩; exact ⟨w, h1, h2⟩) (GlobalTheory.SplitFrobDense.frobDense D (GlobalTheory.Published.chebotarevDegreeOne_iff_cheb.1 GlobalTheory.Published.chebotarevDegreeOne') S hS)`. Take `⟨ξh, x1, x2, x3, x4⟩` from `exists_halfChar D`.

Establish `hone : ∀ v, (1 : HChar D.host.E).UnrAt v` using `fun v x _ => rfl`. Establish `cone : (CG.ofChar (1 : HChar D.host.E)).IsCsd` using `isCsd_ofChar_of_res _ _ (Or.inl ⟨fun v k => by`. Simplify using `only [HChar.resFin, MonoidHom.finset_prod_apply]`. Conclude with `Finset.prod_eq_one fun _ _ => rfl,`. Use `fun v k => by`.

Simplify using `only [HChar.resInf, MonoidHom.finset_prod_apply]`. Conclude with `Finset.prod_eq_one fun _ _ => rfl⟩)`. Break down `Int.even_or_odd' ((D.R.r : ℤ) - 1 - wt) with ⟨k, hk | hk⟩` into its components or cases. Establish `hsk : (s : ℂ) = k`. Rewrite `hs2` using `[hk]`.

Move the coercions through the operations in `at hs2`. Establish `: s = k` using `by linarith`. Rewrite using `[this]`. Simplify using the standard rewrite rules. Take `⟨k1, k2⟩` from `key 1 fun τ => ⟨-k, by rw [CG.expo_one, hsk]; push_cast; ring⟩`.

Conclude with `isPotCrysAt_of_mono0_g hL hF hG hB hGL hD ha hc₀ hν (fun v => hone v) cone (by rwa [inv_one]) k1 k2 H (D.locT l) hw (D.nd.plOm.2 w) Bw hj hm' hgood`. Establish `hsk : (s : ℂ) = k + 1 / 2`. Rewrite `hs2` using `[hk]`. Move the coercions through the operations in `at hs2`. Establish `: s = k + 1 / 2` using `by linarith`.

Rewrite using `[this]`. Simplify using the standard rewrite rules. Take `⟨k1, k2⟩` from `key ξh fun τ => by`. Take `⟨n, hn⟩` from `x4 τ`. Conclude with `⟨n - k, by rw [hn, hsk]; push_cast; ring⟩`.

Conclude with `isPotCrysAt_of_mono0_g hL hF hG hB hGL hD ha hc₀ hν x1 x2 x3 k1 k2 H (D.locT l) hw (D.nd.plOm.2 w) Bw hj hm' hgood`.
-/
theorem galHodge_of_cgTrue_g (sw : UpperTheory.One.M.Sw) (hL : GlobalTheory.Published.LocalLanglandsGL) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL)
    (hG : UpperTheory.GalS.CuspU) (hB : GlobalTheory.Published.DeRhamPotSemistable) (hGL : UpperTheory.GalS.CarU)
    {D : D7} {T : WDTie D.nd D.naut} (C : CGTrue hL D T) : UpperTheory.GalS.GalHodge0 D T := by
  intro l _ ι π s hc hr
  have := host_isCMField D.host
  have ha : 2 ≤ D.R.r := by
    have := D.R.two_le_m; have := D.R.m_add_three_le_k; unfold Ranks.r; omega
  obtain ⟨π₀, hπ₀⟩ := Quotient.exists_rep (C.e _ π).1
  have hmk : CG.mk π₀ = (C.e _ π).1 := hπ₀
  have hc₀ : π₀.IsCsd := by
    have h1 := (C.csd _ π).1 hc
    rw [CGu.IsCsd, ← hmk] at h1
    exact h1
  have hν := GlobalTheory.HeckeGal.Model.absPow_isAbsPow D.host.E s
  set ν := GlobalTheory.HeckeGal.Model.absPow D.host.E s
  have inf₁ : ∀ τ, (CG.mk (π₀.twist ν)).infChar τ = (D.naut.infG π τ).map (· + (s : ℂ)) := fun τ => by
    have h1 := (ParLaws.hasInfChar_infChar (CG.mk π₀) τ).twist ν
    rw [(GlobalTheory.T.heckeChar_exponent_of_infinityType _ ν).2.1 s hν τ] at h1
    rw [C.inf, CGu.infChar, ← hmk]
    exact h1.infChar_eq
  have hreg : (CG.mk (π₀.twist ν)).IsRegAlg := (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by
    obtain ⟨h1, h2⟩ := hr τ
    rw [inf₁]
    refine ⟨h1.map (add_left_injective _), fun z hz => ?_⟩
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hz
    exact h2 y hy
  obtain ⟨ψp, hP⟩ := isPolarized_twist hc₀ hν
  obtain ⟨r, wt, HT, H⟩ := hG _ D.nd.Om l ι _ (by omega) _ ψp hreg hP
  have hloc : ∀ (w : PlE D.host) (u : ℝ), T.e w (D.naut.lpTw (D.naut.locG π w) u) =
      (ParLaws.locPar hL (CG.mk π₀) (D.nd.plOm.2 w)).lpTw u := fun w u => by
    rw [T.tw, C.loc, hmk]
    rfl
  have haway : ∀ (w : PlE D.host) (hl : ((l : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal),
      UpperTheory.GalS.Aw (wdOf (D.nd.plOm.2 w) hl ι r) (T.e w (D.naut.lpTw (D.naut.locG π w) (s + (1 - (D.R.r : ℝ)) / 2))) := fun w hl => by
    have e := locPar_twist_abs_m hL hF (CG.mk π₀) hν (D.nd.plOm.2 w)
    have k := H.aw_locPar hL hF hl (D.nd.plOm.2 w)
    rw [show ParLaws.locPar hL (CG.mk (π₀.twist ν)) (D.nd.plOm.2 w) = _ from e, WD.lpTw_add, ← hloc] at k
    exact k
  have hv : s + (1 - (D.R.r : ℝ)) / 2 + (wt : ℝ) / 2 = 0 := by
    have hm : ∀ τ, π₀.HasInfChar τ ((CG.mk π₀).infChar τ) := fun τ => ParLaws.hasInfChar_infChar (CG.mk π₀) τ
    have hw := GlobalTheory.TempSatGal.weight_eq_rank_sub_one_sub_two_mul_of_inf_char_shift (by omega) H (fun τ => (CG.mk π₀).infChar τ) s (fun τ => (hm τ).1)
      (fun τ => by rw [inf₁, C.inf, CGu.infChar, ← hmk])
      (fun τ => GlobalTheory.CsdTwistGal.infChar_conj_of_isCsd _ _ π₀ hc₀ τ _ _ (hm τ) (hm _))
    rw [hw]; ring
  have htemp : ∀ w : PlE D.host, ((l : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal → D.naut.unr (D.naut.locG π w) →
      ∀ α ∈ D.naut.frobEig (D.naut.locG π w), ‖α‖ ≤ ((normV w : ℕ) : ℝ) ^ (((D.R.r : ℝ) + 3) / 2) := fun w hl hu α hα => by
    obtain ⟨-, hU, hS⟩ := GlobalTheory.HeightCounting.Blocks.readsCusp hF C
    obtain ⟨B, hB, e⟩ := hS _ π w (by omega) hu
    rw [e] at hα
    obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.1 hα
    have k : UpperTheory.GalN.OpenB (Formalism.ConjugateSelfDual.normV w) (b : ℂ) :=
      PositivityTheory.JacquetShalikaLocal.jacquetShalikaBound D.host.E _ _ (hU _ π (by omega)) w B hB b hb
    rw [Units.val_inv_eq_inv_val]
    have hq := UpperTheory.GalN.one_lt_q (H := D.host) w
    refine (k.inv hq).2.le.trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hq.le) ?_)
    have : (0 : ℝ) ≤ D.R.r := Nat.cast_nonneg _
    linarith
  refine ⟨r, ⟨Units.continuous_val.comp H.cont, H.ss, haway, htemp⟩, fun w hw O _ _ _ Bw hj => ?_⟩
  have hpar : T.e w (D.naut.locG π w) = ParLaws.locPar hL (CG.mk π₀) (D.nd.plOm.2 w) := by
    rw [C.loc, hmk]
    rfl
  have hab := H.above (D.loc l) (D.locA l) ⟨D.locT l⟩ w _ (D.nd.plOm.2 w) O Bw hj
  have hN : UpperTheory.GalS.Nc D.nd D.naut (D.naut.locG π w) → UpperTheory.GalS.Nice (π₀.twist ν) (D.nd.plOm.2 w) := fun k => by
    refine UpperTheory.GalS.nice_of_locPar hL hF _ (UpperTheory.GalS.NcW.tw ?_ _)
    have e := locPar_twist_abs_m hL hF (CG.mk π₀) hν (D.nd.plOm.2 w)
    rw [show ParLaws.locPar hL (CG.mk (π₀.twist ν)) (D.nd.plOm.2 w) = _ from e, ← hpar]
    exact (UpperTheory.GalS.ncW_of_nc T k).tw _
  refine ⟨fun k => ⟨hab.deRham (hN k), fun τ L τ' hτ => ⟨HT τ, ?_, hab.jumps (hN k) τ L τ' hτ⟩⟩, fun hu => ?_, fun hm => ?_⟩
  · rw [H.weights, inf₁, Multiset.map_map]
    refine Multiset.map_congr rfl fun z _ => ?_
    simp only [Function.comp_apply]
    ring
  · obtain ⟨σ₀, hσ₀, -⟩ := LocEx.exists_isLocComp hF _ _ (π₀.twist ν) w
    refine hab.crys σ₀ hσ₀ ((ParLaws.unr_iff (ParLaws.isRec_locRec hL (D.nd.plOm.2 w)) (ParLaws.toRep σ₀)).1 ?_)
    rw [← ParLaws.locPar_mk hL hσ₀ (D.nd.plOm.2 w)]
    have e := locPar_twist_abs_m hL hF (CG.mk π₀) hν (D.nd.plOm.2 w)
    rw [show ParLaws.locPar hL (CG.mk (π₀.twist ν)) (D.nd.plOm.2 w) = _ from e, WD.unr_tw, ← hpar]
    exact (T.unr w _).1 hu
  · have hm' : UpperTheory.GalS.NcW (ParLaws.locPar hL (CG.mk π₀) (D.nd.plOm.2 w)) := by
      rw [← hpar]
      exact UpperTheory.GalS.ncW_of_nc T hm
    have hgood : UpperTheory.Zero.LLC.Good (⟨D.R.r, ParLaws.toCl ((CG.mk π₀).loc w)⟩ : IrrGL (w.adicCompletion D.host.E)) := by
      rw [hmk]
      exact UpperTheory.One.M.Old.cgGood sw C _ π w
    have hs2 : 2 * s = ((D.R.r : ℤ) - 1 - wt : ℤ) := by
      push_cast
      linarith
    have key : ∀ ξ : HChar D.host.E, (∀ τ, ∃ n : ℤ, expo ξ τ = (s : ℂ) + n) →
        (CG.mk (π₀.twist ξ)).IsRegAlg ∧ ∀ τ, ∃ n : ℤ, expo (ξ⁻¹ * ν) τ = n := fun ξ hξ => by
      refine ⟨(GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => ?_, fun τ => ?_⟩
      · obtain ⟨h1, h2⟩ := hr τ
        obtain ⟨n, hn⟩ := hξ τ
        have e := ((ParLaws.hasInfChar_infChar (CG.mk π₀) τ).twist ξ).infChar_eq
        have e' : (CG.mk (π₀.twist ξ)).infChar τ = (D.naut.infG π τ).map (· + expo ξ τ) := by
          rw [C.inf, CGu.infChar, ← hmk]
          exact e
        rw [e']
        refine ⟨h1.map (add_left_injective _), fun z hz => ?_⟩
        obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hz
        obtain ⟨m, hm2⟩ := h2 y hy
        refine ⟨m + n, ?_⟩
        simp only [hn]
        push_cast
        linear_combination hm2
      · obtain ⟨n, hn⟩ := hξ τ
        refine ⟨-n, ?_⟩
        rw [expo_mul, expo_inv, hn, (GlobalTheory.T.heckeChar_exponent_of_infinityType _ ν).2.1 s hν τ]
        push_cast
        ring
    have hD : ∀ S : Set (HeightOneSpectrum (𝓞 D.host.E)), S.Finite → Dense {g : G D.host.E D.nd.Om | ∃ w ∉ S,
        ∃ B : ValuationSubring D.nd.Om, IsPlaceOver (F := D.host.E) B w ∧ IsFrob (F := D.host.E) B (normV w) g} := fun S hS =>
      Dense.mono (by rintro g ⟨w, h1, -, h2⟩; exact ⟨w, h1, h2⟩)
        (GlobalTheory.SplitFrobDense.frobDense D (GlobalTheory.Published.chebotarevDegreeOne_iff_cheb.1 GlobalTheory.Published.chebotarevDegreeOne') S hS)
    obtain ⟨ξh, x1, x2, x3, x4⟩ := exists_halfChar D
    have hone : ∀ v, (1 : HChar D.host.E).UnrAt v := fun v x _ => rfl
    have cone : (CG.ofChar (1 : HChar D.host.E)).IsCsd := isCsd_ofChar_of_res _ _ (Or.inl
      ⟨fun v k => by
        simp only [HChar.resFin, MonoidHom.finset_prod_apply]
        exact Finset.prod_eq_one fun _ _ => rfl,
      fun v k => by
        simp only [HChar.resInf, MonoidHom.finset_prod_apply]
        exact Finset.prod_eq_one fun _ _ => rfl⟩)
    rcases Int.even_or_odd' ((D.R.r : ℤ) - 1 - wt) with ⟨k, hk | hk⟩
    · have hsk : (s : ℂ) = k := by
        rw [hk] at hs2
        push_cast at hs2
        have : s = k := by linarith
        rw [this]
        simp
      obtain ⟨k1, k2⟩ := key 1 fun τ => ⟨-k, by rw [CG.expo_one, hsk]; push_cast; ring⟩
      exact isPotCrysAt_of_mono0_g hL hF hG hB hGL hD ha hc₀ hν (fun v => hone v) cone (by rwa [inv_one]) k1 k2 H (D.locT l) hw
        (D.nd.plOm.2 w) Bw hj hm' hgood
    · have hsk : (s : ℂ) = k + 1 / 2 := by
        rw [hk] at hs2
        push_cast at hs2
        have : s = k + 1 / 2 := by linarith
        rw [this]
        simp
      obtain ⟨k1, k2⟩ := key ξh fun τ => by
        obtain ⟨n, hn⟩ := x4 τ
        exact ⟨n - k, by rw [hn, hsk]; push_cast; ring⟩
      exact isPotCrysAt_of_mono0_g hL hF hG hB hGL hD ha hc₀ hν x1 x2 x3 k1 k2 H (D.locT l) hw (D.nd.plOm.2 w) Bw hj hm' hgood

/- English proof (translation)
The claim follows from `@locPar_twist_abs_m`.
-/
example : type_of% @locPar_twist_abs := @locPar_twist_abs_m
/- English proof (translation)
The claim follows from `@galHodge_of_cgTrue_g sw`.
-/
example (sw : UpperTheory.One.M.Sw) : type_of% @galHodge_of_cgTrue_alt := @galHodge_of_cgTrue_g sw

end GlobalTheory.HodgeOfTrue
