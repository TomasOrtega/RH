import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
import Formalism.LocalToGlobal.Divisibility.ColumnFamilyPlaceCharacterComap
import Formalism.LocalToGlobal.Divisibility.TiedLemmas
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.InGeoIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.VolumeLeOfTrivialFirstPair

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Cx GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.R3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Record

variable {X : Stages} {px : PreX X.B.toPre} {I : ColIn X.B px} {hX : X.B.fields.Ok} {T : Top.TwDat X.B}

def plB (X : Stages) : X.B.places.Pl ≃ HeightOneSpectrum (𝓞 X.toD7.what₂.LL) := X.toD7.plEq

/- English proof (translation)
Establish `hc` using `plConjEq X.toD7`. Conclude with `hc w`.
-/
theorem plB_conj (w : X.B.places.Pl) : plB X (X.B.places.conj w) = Formalism.DivisionValues.conjPl (plB X w) := by
  have hc := plConjEq X.toD7
  exact hc w

def ConjStable (X : Stages) (Wt : Set X.B.places.Pl) : Prop := ∀ w ∈ Wt, X.B.places.conj w ∈ Wt

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hv`. Establish `e : X.B.places.conj ((plB X).symm (Formalism.DivisionValues.conjPl v)) = (plB X).symm v`. Apply `(plB X).injective` to reduce the goal to its premises. Rewrite using `[plB_conj, Equiv.apply_symm_apply, Equiv.apply_symm_apply, Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl]`.

Rewrite using `[← e]`. Conclude with `h _ hv`. Introduce `hv`. Establish `e : X.B.places.conj ((plB X).symm v) = (plB X).symm (Formalism.DivisionValues.conjPl v)`. Apply `(plB X).injective` to reduce the goal to its premises.

Rewrite using `[plB_conj, Equiv.apply_symm_apply, Equiv.apply_symm_apply]`. Rewrite using `[← e]`. Conclude with `h _ hv`.
-/
theorem ConjStable.symm_mem_iff {Wt : Set X.B.places.Pl} (h : ConjStable X Wt) (v : HeightOneSpectrum (𝓞 X.toD7.what₂.LL)) :
    (plB X).symm (Formalism.DivisionValues.conjPl v) ∈ Wt ↔ (plB X).symm v ∈ Wt := by
  constructor
  · intro hv
    have e : X.B.places.conj ((plB X).symm (Formalism.DivisionValues.conjPl v)) = (plB X).symm v := by
      apply (plB X).injective
      rw [plB_conj, Equiv.apply_symm_apply, Equiv.apply_symm_apply, Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl]
    rw [← e]
    exact h _ hv
  · intro hv
    have e : X.B.places.conj ((plB X).symm v) = (plB X).symm (Formalism.DivisionValues.conjPl v) := by
      apply (plB X).injective
      rw [plB_conj, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    rw [← e]
    exact h _ hv

/- English proof (translation)
Introduce `τ hτ`. Take `⟨a, ha, rfl⟩` from `(mem_tuOf I).1 hτ`. Conclude with `(mem_tuOf I).2 ⟨a, h ha, rfl⟩`.
-/
theorem tuOf_mono (I : ColIn X.B px) {U U' : Set I.ι} (h : U' ⊆ U) : tuOf I U' ⊆ tuOf I U := by
  intro τ hτ
  obtain ⟨a, ha, rfl⟩ := (mem_tuOf I).1 hτ
  exact (mem_tuOf I).2 ⟨a, h ha, rfl⟩

def inclU (I : ColIn X.B px) {U U' : Set I.ι} (h : U' ⊆ U) : TupU I U' → TupU I U := TupF.incl (tuOf_mono I h)

/- English proof (translation)
Introduce `s t hst`. Establish `hv : (inclU I h s).1 = (inclU I h t).1` using `congrArg Subtype.val hst`. Conclude with `Subtype.ext hv`.
-/
theorem inclU_injective {U U' : Set I.ι} (h : U' ⊆ U) : Function.Injective (inclU I h) := by
  intro s t hst
  have hv : (inclU I h s).1 = (inclU I h t).1 := congrArg Subtype.val hst
  exact Subtype.ext hv

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem ixOf_inclU {U U' : Set I.ι} (h : U' ⊆ U) (t : TupU I U') : ixOf I U (inclU I h t) = ixOf I U' t := rfl

variable {Wt Wt' : Set X.B.places.Pl} (z : Dat X I hX T Wt)

namespace Dat

/- English proof (translation)
Conclude with `(z.mu w).1`.
-/
theorem plB_mem_twPl (w : X.B.places.Pl) : plB X w ∈ z.R.twPl ↔ w ∈ Wt := by
  exact (z.mu w).1

/- English proof (translation)
Establish `hm` using `(z.mu w).2`. Rewrite `hm` using `[if_pos hw]`. Conclude with `hm`.
-/
theorem xi_mu {w : X.B.places.Pl} (hw : w ∈ Wt) : I.xi (ixOf I (usedOf I T Wt) (z.R.mu (plB X w))) = T.xiTw I.C w := by
  have hm := (z.mu w).2
  rw [if_pos hw] at hm
  exact hm

/- English proof (translation)
Establish `hx` using `z.xi_mu (h hv)`. Rewrite `hx` using `[Equiv.apply_symm_apply]`. Establish `hu : ixOf I (usedOf I T Wt) (z.R.mu v) ∈ usedOf I T Wt'` using `⟨(plB X).symm v, hv, hx⟩`. Establish `hm` using `(tup_mem_tuOf I).2 hu`. Rewrite `hm` using `[tup_ixOf]`. Then use the resulting hypothesis.
-/
theorem mu_mem (h : Wt' ⊆ Wt) {v : HeightOneSpectrum (𝓞 X.toD7.what₂.LL)} (hv : (plB X).symm v ∈ Wt') :
    (z.R.mu v).1 ∈ tuOf I (usedOf I T Wt') := by
  have hx := z.xi_mu (h hv)
  rw [Equiv.apply_symm_apply] at hx
  have hu : ixOf I (usedOf I T Wt) (z.R.mu v) ∈ usedOf I T Wt' := ⟨(plB X).symm v, hv, hx⟩
  have hm := (tup_mem_tuOf I).2 hu
  rwa [tup_ixOf] at hm

open Classical in

def resMu (h : Wt' ⊆ Wt) (v : HeightOneSpectrum (𝓞 X.toD7.what₂.LL)) : TupU I (usedOf I T Wt') :=
  if hv : (plB X).symm v ∈ Wt' then ⟨(z.R.mu v).1, Or.inr (z.mu_mem h hv)⟩ else mu0F (X := X.B.fields) (tuOf I (usedOf I T Wt'))

open Classical in

def resTw (Wt' : Set X.B.places.Pl) : Finset (HeightOneSpectrum (𝓞 X.toD7.what₂.LL)) :=
  z.R.twPl.filter fun v => (plB X).symm v ∈ Wt'

/- English proof (translation)
Establish `hm` using `z.plB_mem_twPl ((plB X).symm v)`. Rewrite `hm` using `[Equiv.apply_symm_apply]`. Then use the resulting hypothesis.
-/
theorem mem_twPl (v : HeightOneSpectrum (𝓞 X.toD7.what₂.LL)) : v ∈ z.R.twPl ↔ (plB X).symm v ∈ Wt := by
  have hm := z.plB_mem_twPl ((plB X).symm v)
  rwa [Equiv.apply_symm_apply] at hm

/- English proof (translation)
Unfold `resTw`. Rewrite using `[Finset.mem_filter, z.mem_twPl]`. Conclude with `⟨fun hv => hv.2, fun hv => ⟨h hv, hv⟩⟩`.
-/
theorem mem_resTw (h : Wt' ⊆ Wt) (v : HeightOneSpectrum (𝓞 X.toD7.what₂.LL)) : v ∈ z.resTw Wt' ↔ (plB X).symm v ∈ Wt' := by
  classical
  unfold resTw
  rw [Finset.mem_filter, z.mem_twPl]
  exact ⟨fun hv => hv.2, fun hv => ⟨h hv, hv⟩⟩

/- English proof (translation)
Establish `e : z.resMu h v = ⟨(z.R.mu v).1, Or.inr (z.mu_mem h hv)⟩` using `dif_pos hv`. Rewrite using `[e]`. Both sides reduce to the same expression.
-/
theorem inclU_resMu (h : Wt' ⊆ Wt) {v : HeightOneSpectrum (𝓞 X.toD7.what₂.LL)} (hv : (plB X).symm v ∈ Wt') :
    inclU I (usedOf_mono I T h) (z.resMu h v) = z.R.mu v := by
  have e : z.resMu h v = ⟨(z.R.mu v).1, Or.inr (z.mu_mem h hv)⟩ := dif_pos hv
  rw [e]
  rfl

/- English proof (translation)
Conclude with `dif_neg hv`.
-/
theorem resMu_off (h : Wt' ⊆ Wt) {v : HeightOneSpectrum (𝓞 X.toD7.what₂.LL)} (hv : (plB X).symm v ∉ Wt') :
    z.resMu h v = mu0F (X := X.B.fields) (tuOf I (usedOf I T Wt')) := by
  exact dif_neg hv

/- English proof (translation)
Take `⟨τ, hτ | hτ⟩` from `t`. Use `left`. Conclude with `Subtype.ext hτ`. Use `right`. Take `⟨a, ha, rfl⟩` from `(mem_tuOf I).1 hτ`.

Take `⟨w, hw, hxa⟩` from `ha`. Use `⟨plB X w, ?_⟩` and prove the remaining obligations. Establish `hw' : (plB X).symm (plB X w) ∈ Wt'`. Rewrite using `[Equiv.symm_apply_apply]`. Conclude with `hw`.

Establish `hau : a ∈ usedOf I T Wt` using `usedOf_mono I T h ⟨w, hw, hxa⟩`. Take `⟨ta, hta⟩ : ∃ ta : TupU I (usedOf I T Wt), ta.1 = I.tup a` from `⟨⟨I.tup a, Or.inr ((tup_mem_tuOf I).2 hau)⟩, rfl⟩`. Establish `hix : ixOf I (usedOf I T Wt) ta = a` using `ixOf_eq I hta.symm`. Establish `hs` using `z.xi_mu (h hw)`. Establish `hxi : z.R.toLevCh.xiH ta = z.R.toLevCh.xiH (z.R.mu (plB X w))`.

Rewrite using `[z.lev.xiH, z.lev.xiH, hix, hs, hxa]`. Establish `he` using `z.lev.is.xi_inj hxi`. Establish `e : z.resMu h (plB X w) = ⟨(z.R.mu (plB X w)).1, Or.inr (z.mu_mem h hw')⟩` using `dif_pos hw'`. Rewrite using `[e]`. Apply `Subtype.ext` to reduce the goal to its premises.

Use `show (z.R.mu (plB X w)).1 = I.tup a`. Rewrite using `[← he]`. Conclude with `hta`.
-/
theorem resMu_used (h : Wt' ⊆ Wt) (t : TupU I (usedOf I T Wt')) :
    t = mu0F (X := X.B.fields) (tuOf I (usedOf I T Wt')) ∨ ∃ v, z.resMu h v = t := by
  obtain ⟨τ, hτ | hτ⟩ := t
  · left
    exact Subtype.ext hτ
  · right
    obtain ⟨a, ha, rfl⟩ := (mem_tuOf I).1 hτ
    obtain ⟨w, hw, hxa⟩ := ha
    refine ⟨plB X w, ?_⟩
    have hw' : (plB X).symm (plB X w) ∈ Wt' := by
      rw [Equiv.symm_apply_apply]
      exact hw

    have hau : a ∈ usedOf I T Wt := usedOf_mono I T h ⟨w, hw, hxa⟩
    obtain ⟨ta, hta⟩ : ∃ ta : TupU I (usedOf I T Wt), ta.1 = I.tup a :=
      ⟨⟨I.tup a, Or.inr ((tup_mem_tuOf I).2 hau)⟩, rfl⟩
    have hix : ixOf I (usedOf I T Wt) ta = a := ixOf_eq I hta.symm
    have hs := z.xi_mu (h hw)
    have hxi : z.R.toLevCh.xiH ta = z.R.toLevCh.xiH (z.R.mu (plB X w)) := by
      rw [z.lev.xiH, z.lev.xiH, hix, hs, hxa]

    have he := z.lev.is.xi_inj hxi
    have e : z.resMu h (plB X w) = ⟨(z.R.mu (plB X w)).1, Or.inr (z.mu_mem h hw')⟩ := dif_pos hw'
    rw [e]
    apply Subtype.ext
    show (z.R.mu (plB X w)).1 = I.tup a
    rw [← he]
    exact hta

/- English proof (translation)
Introduce `w`. Establish `hpl : (plB X).symm (X.toD7.plEq w) = w` using `(plB X).symm_apply_apply w`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[z.mem_resTw h, hpl]`. Distinguish the cases in `hw : w ∈ Wt'`.

Rewrite using `[if_pos hw]`. Establish `hw' : (plB X).symm (X.toD7.plEq w) ∈ Wt'`. Rewrite using `[hpl]`. Conclude with `hw`. Rewrite using `[← ixOf_inclU (usedOf_mono I T h), z.inclU_resMu h hw']`.

Conclude with `z.xi_mu (h hw)`. Rewrite using `[if_neg hw]`. Establish `hw' : (plB X).symm (X.toD7.plEq w) ∉ Wt'`. Rewrite using `[hpl]`. Conclude with `hw`.

Rewrite using `[z.resMu_off h hw', ixOf_mu0F]`. Establish `hb` using `z.lev.is.xi_base`. Rewrite `hb` using `[z.lev.xiH, ixOf_mu0F]`. Conclude with `hb`.
-/
theorem muOf_res (h : Wt' ⊆ Wt) : MuOf X I T Wt' (z.resMu h) (z.resTw Wt') := by
  intro w
  have hpl : (plB X).symm (X.toD7.plEq w) = w := (plB X).symm_apply_apply w
  refine ⟨?_, ?_⟩
  · rw [z.mem_resTw h, hpl]
  · by_cases hw : w ∈ Wt'
    · rw [if_pos hw]
      have hw' : (plB X).symm (X.toD7.plEq w) ∈ Wt' := by
        rw [hpl]
        exact hw
      rw [← ixOf_inclU (usedOf_mono I T h), z.inclU_resMu h hw']
      exact z.xi_mu (h hw)
    · rw [if_neg hw]
      have hw' : (plB X).symm (X.toD7.plEq w) ∉ Wt' := by
        rw [hpl]
        exact hw
      rw [z.resMu_off h hw', ixOf_mu0F]

      have hb := z.lev.is.xi_base
      rw [z.lev.xiH, ixOf_mu0F] at hb
      exact hb

set_option maxHeartbeats 1000000 in

def resR (h : Wt' ⊆ Wt) : RealDat3 X.toD7 (famR X I hX (usedOf I T Wt') z.Xg z.tr) z.core.Q.c.F :=
  Res.dat3 (A3 := famR X I hX (usedOf I T Wt) z.Xg z.tr) (inclU I (usedOf_mono I T h))
    (mu0F (X := X.B.fields) (tuOf I (usedOf I T Wt'))) z.R (z.resMu h) (z.resTw Wt')

set_option maxHeartbeats 1000000 in

/- English proof (translation)
The claim follows from `(z.mem_twPl v).2 (h ((z.mem_resTw h v).1 hv)) conj v := by rw [z.mem_resTw h, z.mem_resTw h] exact hc.symm_mem_iff v on v hv := z.inclU_resMu h ((z.mem_resTw h v).1 hv) off v hv := z.resMu_off h fun hv' => hv ((z.mem_resTw h v).2 hv') used t := z.resMu_used h t`.
-/
theorem newTup (h : Wt' ⊆ Wt) (hc : ConjStable X Wt') :
    Res.NewTup (A3 := famR X I hX (usedOf I T Wt) z.Xg z.tr) (f := inclU I (usedOf_mono I T h))
      (μ := mu0F (X := X.B.fields) (tuOf I (usedOf I T Wt'))) z.R (z.resMu h) (z.resTw Wt') where
  sub v hv := (z.mem_twPl v).2 (h ((z.mem_resTw h v).1 hv))
  conj v := by
    rw [z.mem_resTw h, z.mem_resTw h]
    exact hc.symm_mem_iff v
  on v hv := z.inclU_resMu h ((z.mem_resTw h v).1 hv)
  off v hv := z.resMu_off h fun hv' => hv ((z.mem_resTw h v).2 hv')
  used t := z.resMu_used h t

end Dat

end Record

end GlobalTheory.Mem.R3

end
