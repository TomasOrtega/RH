import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.WeightsConj
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PstAndWdAtOfIsRegAlg
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PowFinrankEqZeroOfIsNilpotent
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RankOneUnitary

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.GalN

/- English proof (translation)
Introduce `φ hφ α hα`. Proceed by induction on `x using WD.ind with`. Consider the case `hP n b`. Rewrite `hα` using `[WD.eig, WD.charPol_mk]`. Rewrite `hx` using `[WD.tempered_mk]`.

Rewrite using `[WD.lpDim_mk]`. Establish `hroot : IsRoot (b.ρ φ).charpoly α` using `(mem_roots (LinearMap.charpoly_monic _).ne_zero).mp hα`. Establish `hev : Module.End.HasEigenvalue (b.ρ φ) α` using `(Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).mpr hroot`. Establish `hq : (1 : ℝ) < ((normV w : ℕ) : ℝ)` using `by exact_mod_cast one_lt_normV w`. Conclude with `(GlobalTheory.LocalInv.norm_le_of_isPurePair hq b.nilpotent (hx φ hφ) hev).2.trans (Real.rpow_le_rpow_of_exponent_le hq.le (by linarith))`.
-/
theorem Sz.of_tempered {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w} {x : WD h} (hx : x.tempered) : Sz x := by
  intro φ hφ α hα
  induction x using WD.ind with
  | hP n b =>
    rw [WD.eig, WD.charPol_mk] at hα
    rw [WD.tempered_mk] at hx
    rw [WD.lpDim_mk]
    have hroot : IsRoot (b.ρ φ).charpoly α := (mem_roots (LinearMap.charpoly_monic _).ne_zero).mp hα
    have hev : Module.End.HasEigenvalue (b.ρ φ) α := (Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).mpr hroot
    have hq : (1 : ℝ) < ((normV w : ℕ) : ℝ) := by exact_mod_cast one_lt_normV w
    exact (GlobalTheory.LocalInv.norm_le_of_isPurePair hq b.nilpotent (hx φ hφ) hev).2.trans
      (Real.rpow_le_rpow_of_exponent_le hq.le (by linarith))

section
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime] {a : ℕ}
  [IsAlgClosure E Ω] [IsCMField E]

/- English proof (translation)
The claim follows from `H.cont ss := H.ss pol := H.pol.imp fun _ k => k.1 away w hl A h rc hrc σ hσ := Aw.of_eq ((H.away w hl A h rc hrc σ hσ).wdOf_eq hl) size _ hl _ h := Sz.of_tempered (H.tempered_wdOf hl h) weights := H.weights weights_conj := H.weights_conj above P AI T w A h O _ _ _ Bw hj := have k …`.
-/
theorem IsGalU.of_old {π : CuspSub E a} {χ : HChar (maximalRealSubfield E)} {ι : Qbar l ≃+* ℂ}
    {r : G E Ω →* GL (Fin a) (Qbar l)} {wt : ℤ} {HT : (E →+* Qbar l) → Multiset ℤ}
    (H : IsGalRepOf π χ ι r wt HT) : IsGalU π χ ι r wt HT where
  cont := H.cont
  ss := H.ss
  pol := H.pol.imp fun _ k => k.1
  away w hl A h rc hrc σ hσ := Aw.of_eq ((H.away w hl A h rc hrc σ hσ).wdOf_eq hl)
  size _ hl _ h := Sz.of_tempered (H.tempered_wdOf hl h)
  weights := H.weights
  weights_conj := H.weights_conj
  above P AI T w A h O _ _ _ Bw hj :=
    have k := H.above P AI T w A h O Bw hj
    ⟨k.deRham, k.jumps, fun σ hσ hi _ => ⟨(k.iwahori σ hσ hi).1, fun rc hrc =>
      ⟨fun g => by rw [(k.iwahori σ hσ hi).2 rc hrc], fun m => by rw [(k.iwahori σ hσ hi).2 rc hrc]; exact m⟩⟩, k.crys⟩

/- English proof (translation)
Establish `e : ι.toRingHom.comp (ι.symm.toRingHom.comp s) = s` using `by ext x; simp`. Establish `h1` using `H.weights (ι.symm.toRingHom.comp s)`. Establish `h2` using `H.weights ((ι.symm.toRingHom.comp s).comp (IsCMField.complexConj E).toRingEquiv.toRingHom)`. Rewrite `h2` using `[H.weights_conj, ← RingHom.comp_assoc, e, Multiset.map_map]`. Rewrite `h1` using `[e]`.

Establish `c1 : Multiset.card (HT (ι.symm.toRingHom.comp s)) = a`. Use `congrArg Multiset.card h1` as an intermediate fact. Rewrite `this` using `[Multiset.card_map, Multiset.card_map, CG.card_infChar]`. Then use the resulting hypothesis. Establish `s1` using `congrArg Multiset.sum h1`. Establish `s2` using `congrArg Multiset.sum h2`.

Establish `q : ∀ (c : ℂ) (m : Multiset ℂ), (m.map fun z => c - z).sum = Multiset.card m * c - m.sum` using `fun c m => by`. Proceed by induction on `m using Multiset.induction_on with`. Consider the case `empty => simp`. Consider the case `cons x m ih => rw [Multiset.map_cons, Multiset.sum_cons, ih, Multiset.sum_cons, Multiset.card_cons]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite `s1`, `s2` using `[q, CG.card_infChar]`. Simplify using `only [Function.comp_def, Int.cast_sub, Multiset.sum_map_sub, Multiset.map_const', Multiset.sum_replicate, c1, nsmul_eq_mul] at s2`. Take the linear combination `s1 + s2`.
-/
theorem wt_sum {π : CuspSub E a} {χ : HChar (maximalRealSubfield E)} {ι : Qbar l ≃+* ℂ}
    {r : G E Ω →* GL (Fin a) (Qbar l)} {wt : ℤ} {HT : (E →+* Qbar l) → Multiset ℤ} (H : IsGalU π χ ι r wt HT) (s : E →+* ℂ) :
    (a : ℂ) * wt = a * ((a : ℂ) - 1) - ((CG.mk π).infChar s).sum -
      ((CG.mk π).infChar (s.comp (IsCMField.complexConj E).toRingEquiv.toRingHom)).sum := by
  have e : ι.toRingHom.comp (ι.symm.toRingHom.comp s) = s := by ext x; simp
  have h1 := H.weights (ι.symm.toRingHom.comp s)
  have h2 := H.weights ((ι.symm.toRingHom.comp s).comp (IsCMField.complexConj E).toRingEquiv.toRingHom)
  rw [H.weights_conj, ← RingHom.comp_assoc, e, Multiset.map_map] at h2
  rw [e] at h1
  have c1 : Multiset.card (HT (ι.symm.toRingHom.comp s)) = a := by
    have := congrArg Multiset.card h1
    rwa [Multiset.card_map, Multiset.card_map, CG.card_infChar] at this
  have s1 := congrArg Multiset.sum h1
  have s2 := congrArg Multiset.sum h2
  have q : ∀ (c : ℂ) (m : Multiset ℂ), (m.map fun z => c - z).sum = Multiset.card m * c - m.sum := fun c m => by
    induction m using Multiset.induction_on with
    | empty => simp
    | cons x m ih => rw [Multiset.map_cons, Multiset.sum_cons, ih, Multiset.sum_cons, Multiset.card_cons]; push_cast; ring
  rw [q, CG.card_infChar] at s1 s2
  simp only [Function.comp_def, Int.cast_sub, Multiset.sum_map_sub, Multiset.map_const', Multiset.sum_replicate,
    c1, nsmul_eq_mul] at s2
  linear_combination s1 + s2

/- English proof (translation)
Take `⟨s⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Establish `h` using `(wt_sum H s).trans (wt_sum H' s).symm`. Establish `h0 : (a : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 (by omega)`. Conclude with `mul_left_cancel₀ h0 h` after adjusting the coercions.
-/
theorem wt_eq {l' : ℕ} [Fact l'.Prime] (ha : 1 ≤ a) {π : CuspSub E a} {χ χ' : HChar (maximalRealSubfield E)}
    {ι : Qbar l ≃+* ℂ} {ι' : Qbar l' ≃+* ℂ} {r : G E Ω →* GL (Fin a) (Qbar l)} {r' : G E Ω →* GL (Fin a) (Qbar l')}
    {wt wt' : ℤ} {HT : (E →+* Qbar l) → Multiset ℤ} {HT' : (E →+* Qbar l') → Multiset ℤ}
    (H : IsGalU π χ ι r wt HT) (H' : IsGalU π χ' ι' r' wt' HT') : wt = wt' := by
  obtain ⟨s⟩ : Nonempty (E →+* ℂ) := inferInstance
  have h := (wt_sum H s).trans (wt_sum H' s).symm
  have h0 : (a : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  exact_mod_cast mul_left_cancel₀ h0 h

end

/- English proof (translation)
Introduce `E Ω _ _ _ _ _ _ l _ ι a ha π χ hr hp` and use `by obtain ⟨r, wt, HT, H⟩ := h E Ω l ι a ha π χ hr hp exact ⟨r, wt, HT, .of_old H⟩`.
-/
theorem weakP (h : GlobalTheory.Published.GaloisRepOfPolarizedPair) : PairU :=
  fun E Ω _ _ _ _ _ _ l _ ι a ha π χ hr hp => by
    obtain ⟨r, wt, HT, H⟩ := h E Ω l ι a ha π χ hr hp
    exact ⟨r, wt, HT, .of_old H⟩
/- English proof (translation)
The claim follows from `h`.
-/
theorem weakP' (h : PairU) : PairU := h

/- English proof (translation)
Introduce `E Ω _ _ _ _ _ _ l _ ι a ha π χ hr hp` and use `by obtain ⟨r, wt, HT, H⟩ := h E Ω l ι a ha π χ hr hp exact ⟨r, wt, HT, .of_old H⟩`.
-/
theorem weakG (h : GlobalTheory.Published.GaloisRepOfPolarizedCuspidal) : CuspU :=
  fun E Ω _ _ _ _ _ _ l _ ι a ha π χ hr hp => by
    obtain ⟨r, wt, HT, H⟩ := h E Ω l ι a ha π χ hr hp
    exact ⟨r, wt, HT, .of_old H⟩
/- English proof (translation)
The claim follows from `h`.
-/
theorem weakG' (h : CuspU) : CuspU := h

/- English proof (translation)
Introduce `E Ω _ _ _ _ _ _ l _ ι a ha π hc hr`. Take `⟨r, wt, HT, H⟩` from `hG.of_isCsd Ω ι (by omega) hr hc`. Use `⟨r, wt, HT, .of_old H, fun P AI T w hw A h O _ _ _ Bw hj => ⟨fun _ => ?_, fun σ hσ rc hrc => Ab.of_eq (hC E Ω l ι a ha π hc hr r wt HT H P AI T w hw A h O Bw hj σ hσ rc hrc)⟩⟩` and prove the remaining obligations. Take `⟨σ, hσ, -⟩` from `LocEx.exists_isLocComp hF E a π w`. Establish `hrc` using `ParLaws.isRec_locRec hL h`.

Rewrite using `[hC E Ω l ι a ha π hc hr r wt HT H P AI T w hw A h O Bw hj σ hσ _ hrc]`. Establish `key : ∀ (p : ℕ) [Fact p.Prime], ((p : ℕ) : 𝓞 E) ∉ w.asIdeal → Sz ((ParLaws.locRec hL h (algNorm σ)).lpTw ((wt : ℝ) / 2))` using `fun p _ hp => by`. Take `⟨ι'⟩ : Nonempty (Qbar p ≃+* ℂ)` from `GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex p`. Take `⟨r', wt', HT', H'⟩` from `hG.of_isCsd Ω ι' (by omega) hr hc`. Rewrite using `[wt_eq (by omega) (IsGalU.of_old H) (IsGalU.of_old H'), ← (H'.away w hp A h _ hrc σ hσ).wdOf_eq hp]`.

Conclude with `Sz.of_tempered (H'.tempered_wdOf hp h)`. Distinguish the cases in `h2 : ((2 : ℕ) : 𝓞 E) ∈ w.asIdeal`. Use `key 3 fun h3 => w.isPrime.ne_top ?_` and prove the remaining obligations. Rewrite using `[Ideal.eq_top_iff_one]`. Establish `e : ((3 : ℕ) : 𝓞 E) - ((2 : ℕ) : 𝓞 E) = 1` using `by push_cast; ring`.

Rewrite using `[← e]`. Conclude with `w.asIdeal.sub_mem h3 h2`. Conclude with `key 2 h2`.
-/
theorem merge (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) (hL : GlobalTheory.Published.LocalLanglandsGL)
    (hG : GlobalTheory.Published.GaloisRepOfPolarizedCuspidal) (hC : GlobalTheory.GalOfCusp.LocalGlobalAboveL) : CarU := by
  intro E Ω _ _ _ _ _ _ l _ ι a ha π hc hr
  obtain ⟨r, wt, HT, H⟩ := hG.of_isCsd Ω ι (by omega) hr hc
  refine ⟨r, wt, HT, .of_old H, fun P AI T w hw A h O _ _ _ Bw hj => ⟨fun _ => ?_, fun σ hσ rc hrc =>
    Ab.of_eq (hC E Ω l ι a ha π hc hr r wt HT H P AI T w hw A h O Bw hj σ hσ rc hrc)⟩⟩
  obtain ⟨σ, hσ, -⟩ := LocEx.exists_isLocComp hF E a π w
  have hrc := ParLaws.isRec_locRec hL h
  rw [hC E Ω l ι a ha π hc hr r wt HT H P AI T w hw A h O Bw hj σ hσ _ hrc]
  have key : ∀ (p : ℕ) [Fact p.Prime], ((p : ℕ) : 𝓞 E) ∉ w.asIdeal →
      Sz ((ParLaws.locRec hL h (algNorm σ)).lpTw ((wt : ℝ) / 2)) := fun p _ hp => by
    obtain ⟨ι'⟩ : Nonempty (Qbar p ≃+* ℂ) := GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex p
    obtain ⟨r', wt', HT', H'⟩ := hG.of_isCsd Ω ι' (by omega) hr hc
    rw [wt_eq (by omega) (IsGalU.of_old H) (IsGalU.of_old H'), ← (H'.away w hp A h _ hrc σ hσ).wdOf_eq hp]
    exact Sz.of_tempered (H'.tempered_wdOf hp h)
  by_cases h2 : ((2 : ℕ) : 𝓞 E) ∈ w.asIdeal
  · refine key 3 fun h3 => w.isPrime.ne_top ?_
    rw [Ideal.eq_top_iff_one]
    have e : ((3 : ℕ) : 𝓞 E) - ((2 : ℕ) : 𝓞 E) = 1 := by push_cast; ring
    rw [← e]
    exact w.asIdeal.sub_mem h3 h2
  · exact key 2 h2
/- English proof (translation)
The claim follows from `h`.
-/
theorem merge' (_ : GlobalTheory.Published.AutomorphicFormsFiniteGL) (_ : GlobalTheory.Published.LocalLanglandsGL) (_ : CuspU) (h : CarU) : CarU := h

/- English proof (translation)
The claim follows from `merge hF hL hG (hC.regAlg hR)`.
-/
theorem mergeP (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) (hL : GlobalTheory.Published.LocalLanglandsGL)
    (hG : GlobalTheory.Published.GaloisRepOfPolarizedCuspidal) (hC : GlobalTheory.Published.LocalGlobalAboveL)
    (hR : GlobalTheory.Published.RegularAlgebraicPurity) : CarU := merge hF hL hG (hC.regAlg hR)
/- English proof (translation)
The claim follows from `h`.
-/
theorem mergeP' (_ : GlobalTheory.Published.AutomorphicFormsFiniteGL) (_ : GlobalTheory.Published.LocalLanglandsGL) (_ : CuspU) (h : CarU)
    (_ : GlobalTheory.Published.RegularAlgebraicPurity) : CarU := h

/- English proof (translation)
The claim follows from `mergeP hF hL hG hC.localGlobalAboveL hR`.
-/
theorem mergePst (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) (hL : GlobalTheory.Published.LocalLanglandsGL)
    (hG : GlobalTheory.Published.GaloisRepOfPolarizedCuspidal) (hC : GlobalTheory.Published.LocalGlobalAboveLPst)
    (hR : GlobalTheory.Published.RegularAlgebraicPurity) : CarU := mergeP hF hL hG hC.localGlobalAboveL hR

end UpperTheory.GalN
