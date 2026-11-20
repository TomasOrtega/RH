import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideMultiplicityFamily
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.LocLevel

/- English proof (translation)
Establish `h1 : ((p : ℕ) : 𝓞 (maximalRealSubfield D.host.E)) ∈ v.asIdeal`. Rewrite using `[← hw', Ideal.mem_comap, map_natCast]`. Conclude with `h`. Rewrite `h1` using `[← hw, Ideal.mem_comap, map_natCast]`. Conclude with `h1`.
-/
theorem mem_placesOver_of_overPl' {D : D7} {p : ℕ} {w w' : PlE D.host}
    {v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))} (hw : NG.OverPl w v) (hw' : NG.OverPl w' v)
    (h : w' ∈ placesOver D.host.E p) : w ∈ placesOver D.host.E p := by
  have h1 : ((p : ℕ) : 𝓞 (maximalRealSubfield D.host.E)) ∈ v.asIdeal := by
    rw [← hw', Ideal.mem_comap, map_natCast]; exact h
  rw [← hw, Ideal.mem_comap, map_natCast] at h1
  exact h1

/- English proof (translation)
Unfold `NG.OverPl`. Rewrite using `[← s.w_under]`. Use extensionality with `a`. Rewrite using `[Ideal.mem_comap, Ideal.mem_comap]`. Apply `hc` to reduce the goal to its premises.

Establish `hy` using `GlobalTheory.SplitConjPlace.cO_algebraMap a`. Use `set y := algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E) a`. Establish `e1 : (y : D.host.E) = IsCMField.complexConj D.host.E (y : D.host.E)` using `by conv_lhs => rw [← hy]`. Rewrite using `[IsCMField.coe_ringOfIntegersComplexConj]`. Rewrite using `[e1]`.

Use `conv_rhs => rw [← e1]`. Conclude with `D.host.φ₀.injective (by`. Rewrite using `[NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply])`.
-/
theorem overPl_of_isConjPl {D : D7} {w : PlE D.host} {s : SplitPlace D.host.E} (hc : IsConjPl D.host w s.w) :
    NG.OverPl w s.v := by
  unfold NG.OverPl
  rw [← s.w_under]
  ext a
  rw [Ideal.mem_comap, Ideal.mem_comap]
  apply hc
  have hy := GlobalTheory.SplitConjPlace.cO_algebraMap a
  set y := algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E) a
  have e1 : (y : D.host.E) = IsCMField.complexConj D.host.E (y : D.host.E) := by
    conv_lhs => rw [← hy]
    rw [IsCMField.coe_ringOfIntegersComplexConj]
  rw [e1]
  conv_rhs => rw [← e1]
  exact D.host.φ₀.injective (by
    rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply])

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

/- English proof (translation)
Introduce `D cf jE A M C tp hMI big X T Sp i w s hw hc κ htr`. Establish `hov : NG.OverPl w s.v` using `overPl_of_isConjPl hc`. Establish `hjf : X.nd.j i - 1 + 1 = X.nd.j i` using `by have := X.nd.j_range i; omega`. Set `jf : Fin D.R.m` to `⟨X.nd.j i - 1, by have := X.nd.j_range i; omega⟩`. Establish `h0` using `hMI.hyp (X.nd.w i) jf`.

Establish `hyp : NG.HypOutside (mlX M X i).J (mlX M X i).χ (gPl D ∪ qPl D (tp.tup (D.what₂.muTw (X.nd.w i)) jf))` using `GlobalTheory.FitHecke.hypOutside_transport' (M := M) (X.nd.mu_w i).symm hjf _ _ (X.nd.j_range i).1 (X.nd.j_range i).2 _ h0`. Establish `hS` using `(X.nd.S_def i w).not.1 hw.2.2.1`. Establish `hl` using `hw.2.1`. Establish `hg : ∀ k, w ∉ placesOver D.host.E (D.host.g k)`. Introduce `k hk`.

Apply `hS` to reduce the goal to its premises. Use `⟨?_, hl⟩` and prove the remaining obligations. Use `fin_cases k`. Conclude with `Or.inl hk`. Conclude with `Or.inr (Or.inl hk)`.

Establish `hp : w ∉ placesOver D.host.E (if X.nd.l i = D.host.pde then D.host.pde' else D.host.pde)` using `fun h => hS ⟨Or.inr (Or.inr h), hl⟩`. Establish `hi : i ∈ X.nd.locs (X.nd.j i) (X.nd.w i)` using `(X.nd.locs_mem _ _ i).2 ⟨rfl, rfl⟩`. Establish `hQe : C.Q (X.nd.w i) = Sp.B.Qc (X.nd.j i) (X.nd.w i)` using `(Sp.Qc_eq _ _).symm`. Establish `hvB : s.v ∉ gPl D ∪ qPl D (tp.tup (D.what₂.muTw (X.nd.w i)) jf)`. Introduce and unpack `(⟨w', hov', k, hk⟩ | hq)`.

Conclude with `hg k (mem_placesOver_of_overPl' hov hov' hk)`. Take `⟨w', hov', hw'⟩` from `GlobalTheory.FitHecke.qPl_sub tp (X.nd.w i) (X.nd.w_tw i) jf hq`. Break down `hw' with hQ' | hp'` into its components or cases. Rewrite `hQ'` using `[hQe]`. Establish `hwQ : w ∈ Sp.B.Qc (X.nd.j i) (X.nd.w i)` using `Sp.B.Qc_over _ _ w' w hQ' ⟨s.v, hov', hov⟩`.

Rewrite `hwQ` using `[← Sp.Q_eq _ _ i hi]`. Conclude with `hw.2.2.2 hwQ`. Rewrite `hp'` using `[X.nd.w_l i]`. Conclude with `hp (mem_placesOver_of_overPl' hov hov' hp')`. Establish `htr' : TrivOutside (gPl D ∪ qPl D (tp.tup (D.what₂.muTw (X.nd.w i)) jf))ᶜ κ`.

Introduce `v hv`. Apply `htr v` to reduce the goal to its premises. Introduce and unpack `rfl`. Conclude with `hv hvB`. Conclude with `hyp κ htr'`.
-/
theorem level_at_splitOut : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C) (hMI : MtInput D M tp.tup C.Q) (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T) (i : X.nd.Loc) (w : PlE D.host) (s : SplitPlace D.host.E), SplitOut X.nd i w → IsConjPl D.host w s.w → ∀ κ : GAf D.host.E D.R.nV, TrivOutside {s.v} κ → (κ ∈ (mlX M X i).J ↔ κ ∈ Umax D.host.E D.R.nV) ∧ ∀ h : κ ∈ (mlX M X i).J, (mlX M X i).χ ⟨κ, h⟩ = 1 := by
  intro D cf jE A M C tp hMI big X T Sp i w s hw hc κ htr
  classical
  have hov : NG.OverPl w s.v := overPl_of_isConjPl hc
  have hjf : X.nd.j i - 1 + 1 = X.nd.j i := by have := X.nd.j_range i; omega
  let jf : Fin D.R.m := ⟨X.nd.j i - 1, by have := X.nd.j_range i; omega⟩
  have h0 := hMI.hyp (X.nd.w i) jf
  have hyp : NG.HypOutside (mlX M X i).J (mlX M X i).χ (gPl D ∪ qPl D (tp.tup (D.what₂.muTw (X.nd.w i)) jf)) :=
    GlobalTheory.FitHecke.hypOutside_transport' (M := M) (X.nd.mu_w i).symm hjf _ _ (X.nd.j_range i).1 (X.nd.j_range i).2 _ h0
  have hS := (X.nd.S_def i w).not.1 hw.2.2.1
  have hl := hw.2.1
  have hg : ∀ k, w ∉ placesOver D.host.E (D.host.g k) := by
    intro k hk
    apply hS
    refine ⟨?_, hl⟩
    fin_cases k
    · exact Or.inl hk
    · exact Or.inr (Or.inl hk)
  have hp : w ∉ placesOver D.host.E (if X.nd.l i = D.host.pde then D.host.pde' else D.host.pde) :=
    fun h => hS ⟨Or.inr (Or.inr h), hl⟩
  have hi : i ∈ X.nd.locs (X.nd.j i) (X.nd.w i) := (X.nd.locs_mem _ _ i).2 ⟨rfl, rfl⟩
  have hQe : C.Q (X.nd.w i) = Sp.B.Qc (X.nd.j i) (X.nd.w i) := (Sp.Qc_eq _ _).symm
  have hvB : s.v ∉ gPl D ∪ qPl D (tp.tup (D.what₂.muTw (X.nd.w i)) jf) := by
    rintro (⟨w', hov', k, hk⟩ | hq)
    · exact hg k (mem_placesOver_of_overPl' hov hov' hk)
    · obtain ⟨w', hov', hw'⟩ := GlobalTheory.FitHecke.qPl_sub tp (X.nd.w i) (X.nd.w_tw i) jf hq
      rcases hw' with hQ' | hp'
      · rw [hQe] at hQ'
        have hwQ : w ∈ Sp.B.Qc (X.nd.j i) (X.nd.w i) := Sp.B.Qc_over _ _ w' w hQ' ⟨s.v, hov', hov⟩
        rw [← Sp.Q_eq _ _ i hi] at hwQ
        exact hw.2.2.2 hwQ
      · rw [X.nd.w_l i] at hp'
        exact hp (mem_placesOver_of_overPl' hov hov' hp')
  have htr' : TrivOutside (gPl D ∪ qPl D (tp.tup (D.what₂.muTw (X.nd.w i)) jf))ᶜ κ := by
    intro v hv
    apply htr v
    rintro rfl
    exact hv hvB
  exact hyp κ htr'

end GlobalTheory.LocLevel
