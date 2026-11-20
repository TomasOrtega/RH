import Formalism.LocalToGlobal.ProjectiveLattices.InvProofs
import Formalism.LocalToGlobal.ProjectiveLattices.DatumOfRecordSignature

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions MeasureTheory
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def Par.Canon (Q : Par D) : Prop :=
  Q.H = hostOfRecord D ∧ ∀ j (hj : InR D j), ∃ hP hd, HEq (Q.Dw j) (datumOfRecord D j hj hP hd)

/- English proof (translation)
Consider the cases of `l`. Consider the cases of `l'`. Simplify using `only at hM hMb hA`. Substitute `hM hMb hA` using the available equality. Both sides reduce to the same expression.
-/
private theorem lev_eq_lemma {H : Host D.host.E} (l l' : Level H) (hM : l.M = l'.M) (hMb : l.Mb = l'.Mb)
    (hA : l.A = l'.A) : l = l' := by
  cases l
  cases l'
  simp only at hM hMb hA
  subst hM hMb hA
  rfl

/- English proof (translation)
Use `haveI : NumberField F := ⟨⟩`. Introduce `z hz`. Take `⟨a, b, _, hab⟩` from `IsFractionRing.div_surjective (A := 𝓞 F) (⟨z, hz⟩ : F)`. Establish `key : ∀ t : 𝓞 F, ((t : F) : ℂ) ∈ F'` using `fun t => by`. Establish `h1` using `hF' (eO'.symm (eO t))`.

Rewrite `h1` using `[RingEquiv.apply_symm_apply, hF t]`. Rewrite using `[h1]`. Conclude with `(eO'.symm (eO t) : F').2`. Establish `hz' : z = ((a : F) : ℂ) / ((b : F) : ℂ)`. Establish `h2` using `congrArg (fun w : F => (w : ℂ)) hab`.

Simplify using `using h2.symm`. Rewrite using `[hz']`. Conclude with `F'.div_mem (key a) (key b)`.
-/
private theorem fld_le_lemma_2 {O : Type} [CommRing O] (e : O →+* ℂ) (F F' : IntermediateField ℚ ℂ)
    [FiniteDimensional ℚ F] (eO : 𝓞 F ≃+* O) (eO' : 𝓞 F' ≃+* O) (hF : ∀ x : 𝓞 F, e (eO x) = ((x : F) : ℂ))
    (hF' : ∀ x : 𝓞 F', e (eO' x) = ((x : F') : ℂ)) : F ≤ F' := by
  haveI : NumberField F := ⟨⟩
  intro z hz
  obtain ⟨a, b, _, hab⟩ := IsFractionRing.div_surjective (A := 𝓞 F) (⟨z, hz⟩ : F)
  have key : ∀ t : 𝓞 F, ((t : F) : ℂ) ∈ F' := fun t => by
    have h1 := hF' (eO'.symm (eO t))
    rw [RingEquiv.apply_symm_apply, hF t] at h1
    rw [h1]
    exact (eO'.symm (eO t) : F').2
  have hz' : z = ((a : F) : ℂ) / ((b : F) : ℂ) := by
    have h2 := congrArg (fun w : F => (w : ℂ)) hab
    simpa using h2.symm
  rw [hz']
  exact F'.div_mem (key a) (key b)

/- English proof (translation)
Take `⟨H, l, c, Dw, Xo, eO⟩` from `Q`. Take `⟨H', l', c', Dw', Xo', eO'⟩` from `Q'`. Simplify using `only at hH hM hA hMb hF hF' ⊢`. Substitute `hH` using the available equality. Establish `hl` using `lev_eq_lemma l l' hM hMb hA`.

Substitute `hl` using the available equality. Establish `hFF : c.F = c'.F` using `by haveI := c.fin haveI := c'.fin`. Conclude with `le_antisymm (fld_le_lemma_2 (D.what₂.embLL.comp D.what₂.OtoLL) _ _ eO eO' hF hF') (fld_le_lemma_2 (D.what₂.embLL.comp D.what₂.OtoLL) _ _ eO' eO hF' hF)`. Take `⟨F, fin, cj, zm, le⟩` from `c`. Take `⟨F', fin', cj', zm', le'⟩` from `c'`.

Simplify using `only at hFF hF hF'`. Substitute `hFF` using the available equality. Use `⟨rfl, HEq.rfl, HEq.rfl, heq_of_eq ?_⟩` and prove the remaining obligations. Establish `inj : ∀ y y' : D.what₂.O, D.what₂.embLL (D.what₂.OtoLL y) = D.what₂.embLL (D.what₂.OtoLL y') → y = y'`. Introduce `y y' hy`.

Take `⟨x, rfl⟩` from `eO.surjective y`. Take `⟨x', rfl⟩` from `eO.surjective y'`. Rewrite `hy` using `[hF, hF]`. Rewrite using `[NumberField.RingOfIntegers.ext (Subtype.ext hy)]`. Conclude with `RingEquiv.ext fun x => inj _ _ (by rw [hF, hF'])`.
-/
private theorem par_eqs_lemma_3 (Q Q' : Par D) (hH : Q.H = Q'.H) (hM : Q.l.M = Q'.l.M) (hA : Q.l.A = Q'.l.A)
    (hMb : Q.l.Mb = Q'.l.Mb)
    (hF : ∀ x : 𝓞 Q.c.F, D.what₂.embLL (D.what₂.OtoLL (Q.eO x)) = ((x : Q.c.F) : ℂ))
    (hF' : ∀ x : 𝓞 Q'.c.F, D.what₂.embLL (D.what₂.OtoLL (Q'.eO x)) = ((x : Q'.c.F) : ℂ)) :
    Q.H = Q'.H ∧ HEq Q.l Q'.l ∧ HEq Q.c Q'.c ∧ HEq Q.eO Q'.eO := by
  obtain ⟨H, l, c, Dw, Xo, eO⟩ := Q
  obtain ⟨H', l', c', Dw', Xo', eO'⟩ := Q'
  simp only at hH hM hA hMb hF hF' ⊢
  subst hH
  have hl := lev_eq_lemma l l' hM hMb hA
  subst hl
  have hFF : c.F = c'.F := by
    haveI := c.fin
    haveI := c'.fin
    exact le_antisymm (fld_le_lemma_2 (D.what₂.embLL.comp D.what₂.OtoLL) _ _ eO eO' hF hF')
      (fld_le_lemma_2 (D.what₂.embLL.comp D.what₂.OtoLL) _ _ eO' eO hF' hF)
  obtain ⟨F, fin, cj, zm, le⟩ := c
  obtain ⟨F', fin', cj', zm', le'⟩ := c'
  simp only at hFF hF hF'
  subst hFF
  refine ⟨rfl, HEq.rfl, HEq.rfl, heq_of_eq ?_⟩
  have inj : ∀ y y' : D.what₂.O, D.what₂.embLL (D.what₂.OtoLL y) = D.what₂.embLL (D.what₂.OtoLL y') → y = y' := by
    intro y y' hy
    obtain ⟨x, rfl⟩ := eO.surjective y
    obtain ⟨x', rfl⟩ := eO.surjective y'
    rw [hF, hF] at hy
    rw [NumberField.RingOfIntegers.ext (Subtype.ext hy)]
  exact RingEquiv.ext fun x => inj _ _ (by rw [hF, hF'])

/- English proof (translation)
Establish `hp` using `h.pins`. Establish `hp'` using `h'.pins`. Unfold `Par.Pins Par.PinLevel Par.PinField at hp hp'`. Unfold `Par.Canon at hc hc'`. Establish `hH : T.Q.H = T'.Q.H` using `hc.1.trans hc'.1.symm`.

Establish `hMb : T.Q.l.Mb = T'.Q.l.Mb` using `by rw [h.half.2, h'.half.2, hb]`. Take `⟨r1, r2, r3, r4⟩` from `par_eqs_lemma_3 T.Q T'.Q hH (hp.2.1.1.trans hp'.2.1.1.symm) (hp.2.1.2.trans hp'.2.1.2.symm) hMb hp.2.2.1 hp'.2.2.1`. Use `⟨r1, r2, r3, ?_, r4⟩` and prove the remaining obligations. Take `⟨_, _, e1⟩` from `hc.2 j hj`. Take `⟨_, _, e2⟩` from `hc'.2 j hj`.

Conclude with `e1.trans e2.symm`.
-/
theorem canon_eqs {T T' : Core D} (h : LawsM T) (h' : LawsM T') (hc : T.Q.Canon) (hc' : T'.Q.Canon)
    (hb : T.pb = T'.pb) (j : ℕ) (hj : InR D j) :
    T.Q.H = T'.Q.H ∧ HEq T.Q.l T'.Q.l ∧ HEq T.Q.c T'.Q.c ∧ HEq (T.Q.Dw j) (T'.Q.Dw j) ∧
      HEq T.Q.eO T'.Q.eO := by
  have hp := h.pins
  have hp' := h'.pins
  unfold Par.Pins Par.PinLevel Par.PinField at hp hp'
  unfold Par.Canon at hc hc'
  have hH : T.Q.H = T'.Q.H := hc.1.trans hc'.1.symm
  have hMb : T.Q.l.Mb = T'.Q.l.Mb := by rw [h.half.2, h'.half.2, hb]
  obtain ⟨r1, r2, r3, r4⟩ := par_eqs_lemma_3 T.Q T'.Q hH (hp.2.1.1.trans hp'.2.1.1.symm)
    (hp.2.1.2.trans hp'.2.1.2.symm) hMb hp.2.2.1 hp'.2.2.1
  refine ⟨r1, r2, r3, ?_, r4⟩
  obtain ⟨_, _, e1⟩ := hc.2 j hj
  obtain ⟨_, _, e2⟩ := hc'.2 j hj
  exact e1.trans e2.symm

def ModTr (D : D7) : Prop :=
  ∀ (T T' : Core D) (_h : LawsM T) (_h' : LawsM T') (j : ℕ), InR D j →
    T.Q.H = T'.Q.H → HEq T.Q.l T'.Q.l → HEq T.Q.c T'.Q.c → HEq (T.Q.Dw j) (T'.Q.Dw j) →
    HEq T.Q.eO T'.Q.eO →
    ∃ (U : ∀ j (σ : T'.Q.c.F →+* ℂ), Unf (T'.Q.Xo j) T'.Q.c σ D.R.r) (V : ℕ → (T'.Q.c.F →+* ℂ) → HSp D)
      (dict : ∀ j σ, GA D (V j σ) → Σ k, Frame ((U j σ).X k).Ψ D.R.r) (mu : ∀ j σ, GA D (V j σ) → ℂ)
      (Kf : ∀ j σ, Subgroup (GA D (V j σ)))
      (h'' : LawsM { T' with U := U, V := V, dict := dict, mu := mu, Kf := Kf })
      (fe : T.Q.c.F ≃+* T'.Q.c.F) (Φ : T.R j ≃+* T'.R j)
      (pl : HeightOneSpectrum (𝓞 T.Q.c.F) → HeightOneSpectrum (𝓞 T'.Q.c.F)), IsCoreIso _h h'' j fe Φ pl

def ParTrC (D : D7) : Prop :=
  ∀ (T T' : Core D) (_h : LawsM T) (_h' : LawsM T'), T.Q.Canon → T'.Q.Canon → T.pb = T'.pb →
    ∀ (j : ℕ), InR D j →
    ∃ (U : ∀ j (σ : T'.Q.c.F →+* ℂ), Unf (T'.Q.Xo j) T'.Q.c σ D.R.r) (V : ℕ → (T'.Q.c.F →+* ℂ) → HSp D)
      (dict : ∀ j σ, GA D (V j σ) → Σ k, Frame ((U j σ).X k).Ψ D.R.r) (mu : ∀ j σ, GA D (V j σ) → ℂ)
      (Kf : ∀ j σ, Subgroup (GA D (V j σ)))
      (h'' : LawsM { T' with U := U, V := V, dict := dict, mu := mu, Kf := Kf })
      (fe : T.Q.c.F ≃+* T'.Q.c.F) (Φ : T.R j ≃+* T'.R j)
      (pl : HeightOneSpectrum (𝓞 T.Q.c.F) → HeightOneSpectrum (𝓞 T'.Q.c.F)), IsCoreIso _h h'' j fe Φ pl

def INVC (D : D7) : Prop :=
  ∀ (T T' : Core D) (h : LawsM T) (h' : LawsM T'), T.Q.Canon → T'.Q.Canon → T.pb = T'.pb →
    ∀ (j : ℕ), InR D j →
    ∃ (fe : T.Q.c.F ≃+* T'.Q.c.F) (Φ : T.R j ≃+* T'.R j)
      (pl : HeightOneSpectrum (𝓞 T.Q.c.F) → HeightOneSpectrum (𝓞 T'.Q.c.F)), IsCoreIso h h' j fe Φ pl

/- English proof (translation)
Introduce `T T' h h' hc hc' hb j hj`. Take `⟨e1, e2, e3, e4, e5⟩` from `canon_eqs h h' hc hc' hb j hj`. Conclude with `hm T T' h h' j hj e1 e2 e3 e4 e5`.
-/
theorem parTrC_of (hm : ModTr D) : ParTrC D := by
  intro T T' h h' hc hc' hb j hj
  obtain ⟨e1, e2, e3, e4, e5⟩ := canon_eqs h h' hc hc' hb j hj
  exact hm T T' h h' j hj e1 e2 e3 e4 e5

/- English proof (translation)
Introduce `T T' h h' hcT hcT' hb j hj`. Take `⟨U, V, dict, mu, Kf, h'', fe, Φ, pl, hiso⟩` from `hp T T' h h' hcT hcT' hb j hj`. Establish `q` using `hc`. Unfold `CxIndep at q`. Establish `r` using `q T' U V dict mu Kf h' h'' j hj`.

Take `⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩` from `hiso`. Establish `hm : ∀ w f, f ∈ T.C j w → Φ f ∈ T'.C j w` using `fun w f hf => by`. Rewrite using `[(r w).1]`. Conclude with `(a7 w f).1 hf`. Use `⟨fe, Φ, pl, a1, a2, a3, a4, a5, a6, ?_, a8, ?_, ?_⟩` and prove the remaining obligations.

Introduce `w f`. Rewrite using `[(r w).1]`. Conclude with `a7 w f`. Introduce `w σ f hf`. Rewrite using `[((r w).2 σ (Φ f) (hm w f hf)).1]`.

Conclude with `a9 w σ f hf`. Introduce `w σ f hf`. Rewrite using `[((r w).2 σ (Φ f) (hm w f hf)).2]`. Conclude with `a10 w σ f hf`.
-/
theorem invC_of (hp : ParTrC D) (hc : CxIndep D) : INVC D := by
  intro T T' h h' hcT hcT' hb j hj
  obtain ⟨U, V, dict, mu, Kf, h'', fe, Φ, pl, hiso⟩ := hp T T' h h' hcT hcT' hb j hj
  have q := hc
  unfold CxIndep at q
  have r := q T' U V dict mu Kf h' h'' j hj
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := hiso
  have hm : ∀ w f, f ∈ T.C j w → Φ f ∈ T'.C j w := fun w f hf => by
    rw [(r w).1]; exact (a7 w f).1 hf
  refine ⟨fe, Φ, pl, a1, a2, a3, a4, a5, a6, ?_, a8, ?_, ?_⟩
  · intro w f; rw [(r w).1]; exact a7 w f
  · intro w σ f hf; rw [((r w).2 σ (Φ f) (hm w f hf)).1]; exact a9 w σ f hf
  · intro w σ f hf; rw [((r w).2 σ (Φ f) (hm w f hf)).2]; exact a10 w σ f hf

/- English proof (translation)
The claim follows from `invC_of (parTrC_of hm) (cxIndep_of hR hL)`.
-/
theorem invC_of_laws (hm : ModTr D) (hR : RdUIndep D) (hL : L2Independence D) : INVC D :=
  invC_of (parTrC_of hm) (cxIndep_of hR hL)

end Formalism.L2.Pj
