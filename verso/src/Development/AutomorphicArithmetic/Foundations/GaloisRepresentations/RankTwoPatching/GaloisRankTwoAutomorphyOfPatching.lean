import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.RealPatch
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RankTwoPatching.UnrAtOfIsoTwist
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RankTwoPatching.RatioT
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RankTwoPatching.RowOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PAdicTorsionHoms.PlainOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PAdicTorsionHoms.WinPt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.NormAbsPowUnif

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
open UpperTheory.Zero.LLC UpperTheory.V.Z.Win

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open UpperTheory.V.Af.Bc GlobalTheory.RealGal UpperTheory.V.Af.ExLib
open private UpperTheory.V.Z.Win.SplitTorusFixedPoints.plainTor_of_iso from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PAdicTorsionHoms.SplitTr

namespace UpperTheory.Gal.SV

/- English proof (translation)
Establish `hc` using `continuous_of_iso H.cont h`. Take `⟨g, hg⟩` from `h`. Establish `hg' : ∀ s, g * r s = r' s * g` using `fun s => by rw [hg, inv_mul_cancel_right]`. Establish `ew : ∀ (w : HeightOneSpectrum (𝓞 E)) (hw : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w), wdOf h hw ι r' = wdOf h hw ι r` using `fun w hw A h => ((isWDOf_wdOf (h := h) hw ι (Units.continuous_val.comp H.cont)).of_conj hw g fun s => hg' _).wdOf_eq hw`. Use `⟨hc, hs, fun w hw A h rc hrc σ hσ => ew w hw A h ▸ H.away w hw A h rc hrc σ hσ, H.weights, H.weights_conj, fun P AI T w A h O _ _ _ Bw hj => ?_⟩` and prove the remaining obligations.

Establish `Ha` using `H.above P AI T w A h O Bw hj`. Establish `e : ∀ s : ↥(Dec (F` using `E) A), r'.comp (Dec (F := E) A).subtype s = g * r.comp (Dec (F := E) A).subtype s * g⁻¹ := fun s => hg s`. Take `⟨c1, c2, -, c4⟩` from `GlobalTheory.T.padicHodgeProperties_conj_invariant l P E Ω O _ Bw m _ _ g e`. Use `⟨fun σ hσ hf => ?_, fun σ hσ rc hrc h1 h2 => ?_⟩` and prove the remaining obligations. Take `⟨a1, a2, a3⟩` from `Ha.crys σ hσ hf`.

Conclude with `⟨c2 a1, c1 a2, fun τ L τ' hτ => c4 _ _ (a3 τ L τ' hτ)⟩`. Take `⟨a1, a2, a3, a4⟩` from `Ha.nice σ hσ rc hrc h1 h2`. Conclude with `⟨c1 a1, isPstAt_conj P Bw g e a2, fun τ L τ' hτ => c4 _ _ (a3 τ L τ' hτ), wdAt_conj P ι Bw h hj g e ▸ a4⟩`.
-/
theorem props_iso {Rc : UpperTheory.GalStar.RecNotion} {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime] {m : ℕ}
    [NumberField E] [IsAlgClosure E Ω] [IsCMField E] {π : CuspSub E m}
    {ι : Qbar l ≃+* ℂ} {r r' : G E Ω →* GL (Fin m) (Qbar l)} {wt : ℤ}
    {HT : (E →+* Qbar l) → Multiset ℤ} (H : UpperTheory.GalStar.PropsB Rc π ι r wt HT) (hs : IsSSRep r') (h : RepIso r r') :
    UpperTheory.GalStar.PropsB Rc π ι r' wt HT := by
  have hc := continuous_of_iso H.cont h
  obtain ⟨g, hg⟩ := h
  have hg' : ∀ s, g * r s = r' s * g := fun s => by rw [hg, inv_mul_cancel_right]
  have ew : ∀ (w : HeightOneSpectrum (𝓞 E)) (hw : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w),
      wdOf h hw ι r' = wdOf h hw ι r := fun w hw A h =>
    ((isWDOf_wdOf (h := h) hw ι (Units.continuous_val.comp H.cont)).of_conj hw g fun s => hg' _).wdOf_eq hw
  refine ⟨hc, hs, fun w hw A h rc hrc σ hσ => ew w hw A h ▸ H.away w hw A h rc hrc σ hσ, H.weights, H.weights_conj,
    fun P AI T w A h O _ _ _ Bw hj => ?_⟩
  have Ha := H.above P AI T w A h O Bw hj
  have e : ∀ s : ↥(Dec (F := E) A), r'.comp (Dec (F := E) A).subtype s = g * r.comp (Dec (F := E) A).subtype s * g⁻¹ :=
    fun s => hg s
  obtain ⟨c1, c2, -, c4⟩ := GlobalTheory.T.padicHodgeProperties_conj_invariant l P E Ω O _ Bw m _ _ g e
  refine ⟨fun σ hσ hf => ?_, fun σ hσ rc hrc h1 h2 => ?_⟩
  · obtain ⟨a1, a2, a3⟩ := Ha.crys σ hσ hf
    exact ⟨c2 a1, c1 a2, fun τ L τ' hτ => c4 _ _ (a3 τ L τ' hτ)⟩
  · obtain ⟨a1, a2, a3, a4⟩ := Ha.nice σ hσ rc hrc h1 h2
    exact ⟨c1 a1, isPstAt_conj P Bw g e a2, fun τ L τ' hτ => c4 _ _ (a3 τ L τ' hτ), wdAt_conj P ι Bw h hj g e ▸ a4⟩

/- English proof (translation)
Introduce `L F Ω _ _ _ _ _ _ K _ _ _ _ _ _ _ l _ ι a ha π P hBC r wt HT H`. Establish `hloc` using `GlobalTheory.T.local_global_compatibility_complex L`. Establish `hsl` using `GlobalTheory.T.satakeParameters_local`. Use `(hBC.unr.and (eventually_not_mem K l)).mono ?_` and prove the remaining obligations. Introduce and unpack `w ⟨hu, hw⟩ f hf`.

Take `⟨B, hB, hBw⟩` from `hu (w.under (𝓞 F)) rfl f hf`. Use `⟨B, hB, ?_⟩` and prove the remaining obligations. Take `⟨⟨σ, hσ⟩, hi⟩` from `hloc K a P w`. Establish `hS` using `((hsl K a w σ).2 _ P.finPart (hi σ hσ) _).1 hBw`. Establish `h1` using `frob_of (ι := ι) (r := r) hw σ hS fun A h rc hrc => by`.

Establish `g` using `gdOf K Ω A w h rc hrc a σ ((plainOf K a ha P w).2 ⟨_, hBw⟩ σ hσ)`. Rewrite using `[← (H.away w hw A h rc hrc σ hσ).tor g.1 g.2]`. Conclude with `isWDOf_wdOf (h := h) hw ι (Units.continuous_val.comp H.cont)`. Rewrite `h1` using `[hf, GlobalTheory.RealGal.AttResProof.algSat_pow]`. Then use the resulting hypothesis.
-/
theorem attRes : GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → ∀ (π : TR.CuspSub F a) (P : CuspSub K a), IsBC π P → ∀ (r : G K Ω →* GL (Fin a) (Qbar l)) (wt : ℤ) (HT : (K →+* Qbar l) → Multiset ℤ), UpperTheory.GalStar.PropsB (fun h rc => IsRecT h rc) P ι r wt HT → AttRes π ι K r := by
  intro L F Ω _ _ _ _ _ _ K _ _ _ _ _ _ _ l _ ι a ha π P hBC r wt HT H
  have hloc := GlobalTheory.T.local_global_compatibility_complex L
  have hsl := GlobalTheory.T.satakeParameters_local
  refine (hBC.unr.and (eventually_not_mem K l)).mono ?_
  rintro w ⟨hu, hw⟩ f hf
  obtain ⟨B, hB, hBw⟩ := hu (w.under (𝓞 F)) rfl f hf
  refine ⟨B, hB, ?_⟩
  obtain ⟨⟨σ, hσ⟩, hi⟩ := hloc K a P w
  have hS := ((hsl K a w σ).2 _ P.finPart (hi σ hσ) _).1 hBw
  have h1 := frob_of (ι := ι) (r := r) hw σ hS fun A h rc hrc => by
    have g := gdOf K Ω A w h rc hrc a σ ((plainOf K a ha P w).2 ⟨_, hBw⟩ σ hσ)
    rw [← (H.away w hw A h rc hrc σ hσ).tor g.1 g.2]
    exact isWDOf_wdOf (h := h) hw ι (Units.continuous_val.comp H.cont)
  rwa [hf, GlobalTheory.RealGal.AttResProof.algSat_pow] at h1

/- English proof (translation)
Introduce `F Ω _ _ _ _ _ _ l _ ι a π hπ`. Use `choose HTF hHTF using fun τ : F →+* Qbar l => exists_hodgeTate π hπ (InfinitePlace.mk (ι.toRingHom.comp τ))`. Establish `key : ∀ (τ : F →+* Qbar l) (m : Multiset ℂ), π.HasInfChar (InfinitePlace.mk (ι.toRingHom.comp τ)) m → (HTF τ).map (fun n : ℤ => (n : ℂ)) = m.map fun z => ((a : ℂ) - 1) / 2 - z`. Introduce `τ m hm`. Take `⟨m0, hm0, e⟩` from `hHTF τ`.

Rewrite using `[e, TR.CuspSub.HasInfChar.unique hm0 hm]`. Use `⟨HTF, fun τ => ?_, key, ?_⟩` and prove the remaining obligations. Take `⟨m0, hm0, e⟩` from `hHTF τ`. Use `congrArg Multiset.card e` as an intermediate fact. Simplify `this` using `[hm0.1]`.

Introduce `K _ _ _ _ _ _ _ h2 P hBC r wt HT hG`. Establish `hK : ∀ τ : K →+* Qbar l, HT τ = HTF (τ.comp (algebraMap F K))`. Introduce `τ`. Take `⟨m0, hm0, e⟩` from `hHTF (τ.comp (algebraMap F K))`. Establish `h1 : P.HasInfChar (ι.toRingHom.comp τ) m0` using `hBC.inf _ _ hm0`.

Establish `h3 : (CG.mk P).infChar (ι.toRingHom.comp τ) = m0` using `CG.HasInfChar.infChar_eq h1`. Apply `Multiset.map_injective (f := fun n : ℤ => (n : ℂ)) Int.cast_injective` to reduce the goal to its premises. Rewrite using `[hG.weights τ, h3, e]`. Use `⟨hK, fun τ => ?_⟩` and prove the remaining obligations. Use `letI : Algebra F (Qbar l) := τ.toAlgebra`.

Use `haveI : Module.Finite F K := Module.finite_of_finrank_pos (by omega)`. Use `haveI : Algebra.IsAlgebraic F K := Algebra.IsAlgebraic.of_finite F K`. Set `τ' : K →ₐ[F] Qbar l` to `IsAlgClosed.lift`. Establish `hτ' : (τ' : K →+* Qbar l).comp (algebraMap F K) = τ` using `RingHom.ext fun x => τ'.commutes x`. Establish `hc : ((τ' : K →+* Qbar l).comp (IsCMField.complexConj K).toRingEquiv.toRingHom).comp (algebraMap F K) = τ`.

Rewrite using `[← hτ']`. Use extensionality with `x`. Simplify using `only [RingHom.comp_apply]`. Conclude with `congrArg τ' (complexConj_algebraMap (K := K) x)`. Use `hG.weights_conj (τ' : K →+* Qbar l)` as an intermediate fact.

Rewrite `this` using `[hK, hK, hc, hτ']`. Conclude with `this`.
-/
theorem hodgeTate : ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (π : TR.CuspSub F a), π.IsRegAlg → ∃ HTF : (F →+* Qbar l) → Multiset ℤ, (∀ τ, (HTF τ).card = a) ∧ (∀ (τ : F →+* Qbar l) (m : Multiset ℂ), π.HasInfChar (InfinitePlace.mk (ι.toRingHom.comp τ)) m → (HTF τ).map (fun n : ℤ => (n : ℂ)) = m.map fun z => ((a : ℂ) - 1) / 2 - z) ∧ ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω], Module.finrank F K = 2 → ∀ (P : CuspSub K a), IsBC π P → ∀ (r : G K Ω →* GL (Fin a) (Qbar l)) (wt : ℤ) (HT : (K →+* Qbar l) → Multiset ℤ), UpperTheory.GalStar.PropsB (fun h rc => IsRecT h rc) P ι r wt HT → (∀ τ : K →+* Qbar l, HT τ = HTF (τ.comp (algebraMap F K))) ∧ ∀ τ : F →+* Qbar l, HTF τ = (HTF τ).map (wt - ·) := by
  intro F Ω _ _ _ _ _ _ l _ ι a π hπ
  choose HTF hHTF using fun τ : F →+* Qbar l => exists_hodgeTate π hπ (InfinitePlace.mk (ι.toRingHom.comp τ))
  have key : ∀ (τ : F →+* Qbar l) (m : Multiset ℂ), π.HasInfChar (InfinitePlace.mk (ι.toRingHom.comp τ)) m →
      (HTF τ).map (fun n : ℤ => (n : ℂ)) = m.map fun z => ((a : ℂ) - 1) / 2 - z := by
    intro τ m hm
    obtain ⟨m0, hm0, e⟩ := hHTF τ
    rw [e, TR.CuspSub.HasInfChar.unique hm0 hm]
  refine ⟨HTF, fun τ => ?_, key, ?_⟩
  · obtain ⟨m0, hm0, e⟩ := hHTF τ
    have := congrArg Multiset.card e
    simpa [hm0.1] using this
  · intro K _ _ _ _ _ _ _ h2 P hBC r wt HT hG
    have hK : ∀ τ : K →+* Qbar l, HT τ = HTF (τ.comp (algebraMap F K)) := by
      intro τ
      obtain ⟨m0, hm0, e⟩ := hHTF (τ.comp (algebraMap F K))
      have h1 : P.HasInfChar (ι.toRingHom.comp τ) m0 := hBC.inf _ _ hm0
      have h3 : (CG.mk P).infChar (ι.toRingHom.comp τ) = m0 := CG.HasInfChar.infChar_eq h1
      apply Multiset.map_injective (f := fun n : ℤ => (n : ℂ)) Int.cast_injective
      rw [hG.weights τ, h3, e]
    refine ⟨hK, fun τ => ?_⟩
    letI : Algebra F (Qbar l) := τ.toAlgebra
    haveI : Module.Finite F K := Module.finite_of_finrank_pos (by omega)
    haveI : Algebra.IsAlgebraic F K := Algebra.IsAlgebraic.of_finite F K
    let τ' : K →ₐ[F] Qbar l := IsAlgClosed.lift
    have hτ' : (τ' : K →+* Qbar l).comp (algebraMap F K) = τ := RingHom.ext fun x => τ'.commutes x
    have hc : ((τ' : K →+* Qbar l).comp (IsCMField.complexConj K).toRingEquiv.toRingHom).comp (algebraMap F K) = τ := by
      rw [← hτ']
      ext x
      simp only [RingHom.comp_apply]
      exact congrArg τ' (complexConj_algebraMap (K := K) x)
    have := hG.weights_conj (τ' : K →+* Qbar l)
    rw [hK, hK, hc, hτ'] at this
    exact this

section Descent

variable {F Ω : Type} [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {l : ℕ} [Fact l.Prime] {a : ℕ}

structure At (π : TR.CuspSub F a) (ι : Qbar l ≃+* ℂ) (r : G F Ω →* GL (Fin a) (Qbar l)) (HT : (F →+* Qbar l) → Multiset ℤ)
    {v : HeightOneSpectrum (𝓞 F)} {A : ValuationSubring Ω} (h : IsPlaceOver A v) : Prop where
  plain : ∀ B, π.HasSat v B → PlainAtR π v
  cmp : ∀ σ, π.IsLocComp v σ → GlobalTheory.RoadU.PlainTor (IrrGL.of σ.ρ σ.smooth σ.irred) →
    ∀ rc : IrrGL (v.adicCompletion F) → WD h, IsRecT h rc → CmpT ι r (rc (algNorm σ))
  ht : ∀ σ, π.IsLocComp v σ → GlobalTheory.RoadU.PlainTor (IrrGL.of σ.ρ σ.smooth σ.irred) →
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O), Induces Bw →
      IsdRAt (Loc.PP l) Bw (r.comp (Dec (F := F) A).subtype) ∧
      ∀ (τ : F →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' →
        IsJumpsAt (Loc.PP l) Bw (r.comp (Dec (F := F) A).subtype) τ (HT τ)
  ratio : ∀ hl : ((l : ℕ) : 𝓞 F) ∉ v.asIdeal, PlainAtR π v → UpperTheory.GalN.V.RatioW (wdOf h hl ι r)
  crys : ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O), Induces Bw →
    ∀ σ, π.IsLocComp v σ → GlobalTheory.SmGL.IsSpherical σ.ρ → IsCrysAt (Loc.PP l) Bw (r.comp (Dec (F := F) A).subtype)

/- English proof (translation)
Take `⟨w, h', i, hi⟩` from `GlobalTheory.T.exists_place_completion_iso F Ω K v A h hdec`. Establish `hlw : ((l : ℕ) : 𝓞 F) ∉ v.asIdeal → ((l : ℕ) : 𝓞 K) ∉ w.asIdeal` using `fun hl hw => by`. Apply `hl` to reduce the goal to its premises. Establish `e1` using `(h ((l : ℕ) : 𝓞 F))`. Establish `e2` using `(h' ((l : ℕ) : 𝓞 K))`.

Simplify using `only [map_natCast] at e1 e2`. Conclude with `e1.1 (e2.2 hw)`. Establish `ST` using `splitTr F K a ha π P hBC v w i ⟨hi.cont, hi.loc⟩`. Take `⟨⟨σ', hσ'⟩, -⟩` from `GlobalTheory.T.local_global_compatibility_complex L K a P w`. Take `⟨rc', hrc'⟩` from `recTExists K Ω A w h'`.

Take `⟨S, hS, -⟩` from `GlobalTheory.T.place_over_transport_ring_iso_symm F Ω A v h K Ω A w h' _ _ i hi`. Establish `inj : ∀ {x y : WD h} {x' y' : WD h'}, WDRel (RingEquiv.refl Ω) x x' → WDRel (RingEquiv.refl Ω) y y' → x' = y' → x = y` using `fun hx hy e => S.injective (by rw [(hS _ _).1 hx, (hS _ _).1 hy, e])`. Establish `up : ∀ σ, π.IsLocComp v σ → GlobalTheory.RoadU.PlainTor (IrrGL.of σ.ρ σ.smooth σ.irred) → Gd (rc' (algNorm σ'))` using `fun σ hσ hp => by`. Take `⟨e, he⟩` from `hBC.split v w i hi.cont hi.loc σ σ' hσ hσ'`. Conclude with `gdOf K Ω A w h' rc' hrc' a σ' (UpperTheory.V.Z.Win.SplitTorusFixedPoints.plainTor_of_iso i hi.cont (GlobalTheory.LocalFieldIso.continuous_symm i hi.cont) _ _ _ _ e he hp)`.

Establish `br : ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F` using `F) A) O), Induces Bw → ∃ (Bw' : LocBridge l K Ω (Dec (F := K) A) O) (_ : Induces Bw'), Bw'.Kw = Bw.Kw ∧ Bw'.j = Bw.j ∧ Bw'.LL = Bw.LL := fun O _ _ _ Bw hj => by`. Take `⟨Bw', e1, e2, e3⟩` from `UpperTheory.V.Af.Cq.exBridge F K Ω l A O Bw (GlobalTheory.T.local_field_embedding_mem F Ω K l A O Bw hdec)`. Conclude with `⟨Bw', fun x => by rw [e2]; exact hj x, e1, e2, e3⟩`. Use `⟨fun B hB => ST.1.2 ((plainOf K a ha P w).2 (ST.2 ⟨B, hB⟩)), fun σ hσ hp rc hrc => ?_, fun σ hσ hp O _ _ _ Bw hj => ?_, fun hl hp => ?_, fun O _ _ _ Bw hj σ hσ hs => ?_⟩` and prove the remaining obligations. Take `⟨e, he⟩` from `hBC.split v w i hi.cont hi.loc σ σ' hσ hσ'`.

Establish `hy` using `recTr L.aut.art hi σ σ' e he hrc hrc' hp`. Establish `g` using `up σ hσ hp`. Use `⟨fun hl => ?_, fun O _ _ _ Bw hj _ => ?_⟩` and prove the remaining obligations. Take `⟨x, hx, hxx⟩` from `GlobalTheory.T.galois_rep_restriction_local_completion F Ω K l ι a r A v w h h' i hi _ (isWDOf_wdOf (h := h') (hlw hl) ι (Units.continuous_val.comp hG.cont))`. Conclude with `⟨x, hx, fun _ => inj hxx hy ((hG.away w (hlw hl) A h' rc' hrc' σ' hσ').tor g.1 g.2)⟩`.

Take `⟨Bw', hj', e1, e2, e3⟩` from `br O Bw hj`. Take `⟨-, a2, -, a4⟩` from `(hG.above _ _ (Loc.tiedP l) w A h' O Bw' hj').nice σ' hσ' rc' hrc' (Or.inr g.1) g.2`. Establish `hpst` using `(GlobalTheory.T.local_embedding_compatible_extension F Ω K l _ A O Bw Bw' e1 e2 e3 a r).2.2.2.1 a2`. Conclude with `⟨hpst, inj (GlobalTheory.T.local_embedding_restrict_extension F Ω K l _ A O Bw Bw' e1 e2 e3 a r hpst ι v w h h' hj hj' i hi) hy (a4.tor g.1 g.2)⟩`. Establish `g` using `up σ hσ hp`.

Take `⟨Bw', hj', e1, e2, e3⟩` from `br O Bw hj`. Take `⟨a1, -, a3, -⟩` from `(hG.above _ _ (Loc.tiedP l) w A h' O Bw' hj').nice σ' hσ' rc' hrc' (Or.inr g.1) g.2`. Establish `D` using `GlobalTheory.T.local_embedding_compatible_extension F Ω K l (Loc.PP l) A O Bw Bw' e1 e2 e3 a r`. Use `⟨D.1 a1, fun τ LL' τ' hτ => ?_⟩` and prove the remaining obligations. Take `⟨τK, τ'', hτK, hind⟩` from `GlobalTheory.T.local_embedding_agree F Ω K l A O Bw Bw' e1 e2 τ LL' τ' hτ`.

Establish `hJ` using `D.2.2.2.2 τK (HT τK) (a3 τK LL' τ'' hind)`. Rewrite `hJ` using `[hHT τK, hτK]`. Conclude with `hJ`. Establish `hp'` using `ST.1.1 hp`. Establish `g` using `gdOf K Ω A w h' rc' hrc' a σ' (hp' σ' hσ')`.

Take `⟨t, ht⟩` from `winPt UpperTheory.V.Z.Gam.suppFacts UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.winOf K a ha P`. Take `⟨x, hx, hxx⟩` from `GlobalTheory.T.galois_rep_restriction_local_completion F Ω K l ι a r A v w h h' i hi _ (isWDOf_wdOf (h := h') (hlw hl) ι (Units.continuous_val.comp hG.cont))`. Rewrite using `[hx.wdOf_eq hl]`. Use `UpperTheory.GalN.V.RatioW.descend hi hxx ?_` and prove the remaining obligations. Rewrite using `[(hG.away w (hlw hl) A h' rc' hrc' σ' hσ').tor g.1 g.2]`.

Conclude with `ratioT K Ω A w h' rc' hrc' a P t (ht w hp') σ' hσ'`. Take `⟨e, he⟩` from `hBC.split v w i hi.cont hi.loc σ σ' hσ hσ'`. Take `⟨Bw', hj', e1, e2, e3⟩` from `br O Bw hj`. Conclude with `(GlobalTheory.T.local_embedding_compatible_extension F Ω K l _ A O Bw Bw' e1 e2 e3 a r).2.2.1 ((hG.above _ _ (Loc.tiedP l) w A h' O Bw' hj').crys σ' hσ' ((GlobalTheory.T.aux_statement_23 F K v w i hi.cont a σ σ' e he).2 hs)).1`.
-/
theorem descent (L : GlobalTheory.Mem.LiteralAutomorphy.LitN) (ha : 1 ≤ a) {K : Type} [Field K] [NumberField K] [IsCMField K] [Algebra F K] [Algebra K Ω]
    [IsScalarTower F K Ω] [IsAlgClosure K Ω] {ι : Qbar l ≃+* ℂ} {π : TR.CuspSub F a} {P : CuspSub K a} (hBC : IsBC π P)
    {r : G F Ω →* GL (Fin a) (Qbar l)} {wt : ℤ} {HT : (K →+* Qbar l) → Multiset ℤ}
    (hG : UpperTheory.GalStar.PropsB (fun h rc => IsRecT h rc) P ι (r.comp (res F Ω K)) wt HT) {v : HeightOneSpectrum (𝓞 F)} {A : ValuationSubring Ω}
    (h : IsPlaceOver A v) (hdec : Dec (F := F) A ≤ (res F Ω K).range) {HTF : (F →+* Qbar l) → Multiset ℤ}
    (hHT : ∀ τ : K →+* Qbar l, HT τ = HTF (τ.comp (algebraMap F K))) : At π ι r HTF h := by
  obtain ⟨w, h', i, hi⟩ := GlobalTheory.T.exists_place_completion_iso F Ω K v A h hdec
  have hlw : ((l : ℕ) : 𝓞 F) ∉ v.asIdeal → ((l : ℕ) : 𝓞 K) ∉ w.asIdeal := fun hl hw => by
    apply hl
    have e1 := (h ((l : ℕ) : 𝓞 F))
    have e2 := (h' ((l : ℕ) : 𝓞 K))
    simp only [map_natCast] at e1 e2
    exact e1.1 (e2.2 hw)
  have ST := splitTr F K a ha π P hBC v w i ⟨hi.cont, hi.loc⟩
  obtain ⟨⟨σ', hσ'⟩, -⟩ := GlobalTheory.T.local_global_compatibility_complex L K a P w
  obtain ⟨rc', hrc'⟩ := recTExists K Ω A w h'
  obtain ⟨S, hS, -⟩ := GlobalTheory.T.place_over_transport_ring_iso_symm F Ω A v h K Ω A w h' _ _ i hi
  have inj : ∀ {x y : WD h} {x' y' : WD h'}, WDRel (RingEquiv.refl Ω) x x' → WDRel (RingEquiv.refl Ω) y y' → x' = y' → x = y :=
    fun hx hy e => S.injective (by rw [(hS _ _).1 hx, (hS _ _).1 hy, e])
  have up : ∀ σ, π.IsLocComp v σ → GlobalTheory.RoadU.PlainTor (IrrGL.of σ.ρ σ.smooth σ.irred) → Gd (rc' (algNorm σ')) := fun σ hσ hp => by
    obtain ⟨e, he⟩ := hBC.split v w i hi.cont hi.loc σ σ' hσ hσ'
    exact gdOf K Ω A w h' rc' hrc' a σ' (UpperTheory.V.Z.Win.SplitTorusFixedPoints.plainTor_of_iso i hi.cont
      (GlobalTheory.LocalFieldIso.continuous_symm i hi.cont) _ _ _ _ e he hp)
  have br : ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O), Induces Bw →
      ∃ (Bw' : LocBridge l K Ω (Dec (F := K) A) O) (_ : Induces Bw'), Bw'.Kw = Bw.Kw ∧ Bw'.j = Bw.j ∧ Bw'.LL = Bw.LL :=
    fun O _ _ _ Bw hj => by
      obtain ⟨Bw', e1, e2, e3⟩ := UpperTheory.V.Af.Cq.exBridge F K Ω l A O Bw (GlobalTheory.T.local_field_embedding_mem F Ω K l A O Bw hdec)
      exact ⟨Bw', fun x => by rw [e2]; exact hj x, e1, e2, e3⟩
  refine ⟨fun B hB => ST.1.2 ((plainOf K a ha P w).2 (ST.2 ⟨B, hB⟩)), fun σ hσ hp rc hrc => ?_, fun σ hσ hp O _ _ _ Bw hj => ?_,
    fun hl hp => ?_, fun O _ _ _ Bw hj σ hσ hs => ?_⟩
  · obtain ⟨e, he⟩ := hBC.split v w i hi.cont hi.loc σ σ' hσ hσ'
    have hy := recTr L.aut.art hi σ σ' e he hrc hrc' hp
    have g := up σ hσ hp
    refine ⟨fun hl => ?_, fun O _ _ _ Bw hj _ => ?_⟩
    · obtain ⟨x, hx, hxx⟩ := GlobalTheory.T.galois_rep_restriction_local_completion F Ω K l ι a r A v w h h' i hi _
        (isWDOf_wdOf (h := h') (hlw hl) ι (Units.continuous_val.comp hG.cont))
      exact ⟨x, hx, fun _ => inj hxx hy ((hG.away w (hlw hl) A h' rc' hrc' σ' hσ').tor g.1 g.2)⟩
    · obtain ⟨Bw', hj', e1, e2, e3⟩ := br O Bw hj
      obtain ⟨-, a2, -, a4⟩ := (hG.above _ _ (Loc.tiedP l) w A h' O Bw' hj').nice σ' hσ' rc' hrc' (Or.inr g.1) g.2
      have hpst := (GlobalTheory.T.local_embedding_compatible_extension F Ω K l _ A O Bw Bw' e1 e2 e3 a r).2.2.2.1 a2
      exact ⟨hpst, inj (GlobalTheory.T.local_embedding_restrict_extension F Ω K l _ A O Bw Bw' e1 e2 e3 a r hpst ι v w h h' hj hj' i hi) hy (a4.tor g.1 g.2)⟩
  · have g := up σ hσ hp
    obtain ⟨Bw', hj', e1, e2, e3⟩ := br O Bw hj
    obtain ⟨a1, -, a3, -⟩ := (hG.above _ _ (Loc.tiedP l) w A h' O Bw' hj').nice σ' hσ' rc' hrc' (Or.inr g.1) g.2
    have D := GlobalTheory.T.local_embedding_compatible_extension F Ω K l (Loc.PP l) A O Bw Bw' e1 e2 e3 a r
    refine ⟨D.1 a1, fun τ LL' τ' hτ => ?_⟩
    obtain ⟨τK, τ'', hτK, hind⟩ := GlobalTheory.T.local_embedding_agree F Ω K l A O Bw Bw' e1 e2 τ LL' τ' hτ
    have hJ := D.2.2.2.2 τK (HT τK) (a3 τK LL' τ'' hind)
    rw [hHT τK, hτK] at hJ
    exact hJ
  · have hp' := ST.1.1 hp
    have g := gdOf K Ω A w h' rc' hrc' a σ' (hp' σ' hσ')
    obtain ⟨t, ht⟩ := winPt UpperTheory.V.Z.Gam.suppFacts UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.winOf K a ha P
    obtain ⟨x, hx, hxx⟩ := GlobalTheory.T.galois_rep_restriction_local_completion F Ω K l ι a r A v w h h' i hi _
      (isWDOf_wdOf (h := h') (hlw hl) ι (Units.continuous_val.comp hG.cont))
    rw [hx.wdOf_eq hl]
    refine UpperTheory.GalN.V.RatioW.descend hi hxx ?_
    rw [(hG.away w (hlw hl) A h' rc' hrc' σ' hσ').tor g.1 g.2]
    exact ratioT K Ω A w h' rc' hrc' a P t (ht w hp') σ' hσ'
  · obtain ⟨e, he⟩ := hBC.split v w i hi.cont hi.loc σ σ' hσ hσ'
    obtain ⟨Bw', hj', e1, e2, e3⟩ := br O Bw hj
    exact (GlobalTheory.T.local_embedding_compatible_extension F Ω K l _ A O Bw Bw' e1 e2 e3 a r).2.2.1
      ((hG.above _ _ (Loc.tiedP l) w A h' O Bw' hj').crys σ' hσ' ((GlobalTheory.T.aux_statement_23 F K v w i hi.cont a σ σ' e he).2 hs)).1

end Descent

end UpperTheory.Gal.SV
