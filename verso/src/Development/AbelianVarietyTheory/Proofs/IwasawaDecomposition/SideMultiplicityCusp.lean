import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DenseFrobSet
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteExceptionalPlacesOverPrimeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaloisFamilyLocalGlobalStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteSplittingSetFrobeniusPolynomialsStatement

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.OSplitBig

/- English proof (translation)
Introduce `D cf jE A low Pq S hL eig θ Bs M C tp hCS hMt hstar hExp hsplit hCheb`. Establish `hsys` using `fun w => GlobalTheory.T.galois_family_local_global D cf jE A low Pq S hL eig θ Bs M C tp hCS hMt hstar hExp hsplit hCheb w`. Use `choose FA Sy hSy using hsys`. Establish `hexc` using `fun w : D.what₂.places.Pl => GlobalTheory.T.finite_exceptional_places_over_prime D (D.what₂.places.resChar w) (D.what₂.places.resChar_prime w)`. Use `choose FB hFB using hexc`.

Set `Fw : D.what₂.places.Pl → Finset (PlE D.host)` to `fun w => FA w ∪ FB w ∪ C.Q w`. Set `Pv : D.what₂.places.Pl → G D.host.E D.nd.Om → PlE D.host → Prop` to `fun w σ v => v ∉ Fw w ∧ IsSplitPl D.host v ∧ ∃ B : ValuationSubring D.nd.Om, IsPlaceOver (F := D.host.E) B v ∧ IsFrob (F := D.host.E) B (normV v) σ`. Set `pw : D.what₂.places.Pl → (PlE D.host → ℕ → ℂ) → G D.host.E D.nd.Om → ℂ[X]` to `fun w c σ => if h : ∃ v, Pv w σ v then sysPol D c h.choose else 0`. Establish `hcore` using `fun (w : D.what₂.places.Pl) (c : PlE D.host → ℕ → ℂ) => GlobalTheory.T.exists_finite_splitting_set_frobeniusPolynomials (D.what₂.places.resChar w) (A.pl.ι w) D.host.E D.nd.Om D.R.nV (frobSet D (Fw w)) (pw w c) (dense_frobSet D hCheb (Fw w))`. Use `choose SC hSC using hcore`.

Use `⟨fun w => (Sy w).biUnion (SC w), ?_⟩` and prove the remaining obligations. Introduce `L Sp hAut i x r hr`. Take `⟨c, hcS, hc⟩` from `hSy ((withLoc L).nd.w i) _ L Sp hAut i x rfl`. Use `haveI : Fact ((withLoc L).nd.l i).Prime := (withLoc L).nd.lPrime i`. Use `letI := (withLoc L).nd.dvrO i`.

Use `letI := (withLoc L).nd.algO i`. Use `letI := (withLoc L).nd.finO i`. Use `letI := (withLoc L).nd.topO i`. Use `letI := (withLoc L).nd.trO i`. Use `hSC ((withLoc L).nd.w i) c ((withLoc L).nd.l i) ((withLoc L).nd.w_l i) ((withLoc L).nd.O i) ((withLoc L).nd.O_adic i) (Sp.iq i) ?_ ?_ r hr.1 hr.2.1 ?_` and prove the remaining obligations.

Conclude with `fun z => Sp.iq_alg i z`. Introduce `z hz`. Conclude with `Sp.iq_big i z (Finset.mem_biUnion.2 ⟨c, hcS, hz⟩)`. Introduce `σ hσ`. Establish `hex : ∃ v, Pv ((withLoc L).nd.w i) σ v` using `hσ`.

Establish `hspec` using `hex.choose_spec`. Take `⟨hvF, hvs, B, hB, hFr⟩` from `hspec`. Establish `hvF'` using `hvF`. Simplify using `only [Fw, Finset.mem_union, not_or] at hvF'`. Take `⟨⟨hvA, hvB⟩, hvQ⟩` from `hvF'`.

Establish `hSO : SplitOut (withLoc L).nd i hex.choose`. Establish `hQi : (withLoc L).nd.Q i = C.Q ((withLoc L).nd.w i)` using `(Sp.Q_eq _ _ i ((L.X.nd.locs_mem _ _ i).2 ⟨rfl, rfl⟩)).trans (Sp.Qc_eq _ _)`. Take `⟨h1, h2⟩` from `hFB ((withLoc L).nd.w i) _ hvB`. Use `⟨hvs, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← (withLoc L).nd.w_l i]`.

Conclude with `h1`. Introduce `hmem`. Apply `h2` to reduce the goal to its premises. Use `((withLoc L).nd.S_def i _).1 hmem` as an intermediate fact. Rewrite `this` using `[← (withLoc L).nd.w_l i]`.

Conclude with `this`. Use `show _ ∉ (withLoc L).nd.Q i`. Rewrite using `[hQi]`. Conclude with `hvQ`. Use `(congrArg (Polynomial.map _) (hr.2.2 _ hSO B σ hB hFr)).trans ?_` and prove the remaining obligations.

Establish `hio : (qCast ((withLoc L).nd.w_l i) (A.pl.ι ((withLoc L).nd.w i))).toRingHom.comp ((Sp.iq i).comp (algebraMap ((withLoc L).nd.O i) (FractionRing ((withLoc L).nd.O i)))) = iotaOC (withLoc L) i`. Use extensionality with `z`. Simplify using `only [iotaOC, RingHom.comp_apply]`. Rewrite using `[show (withLoc L).naut.iotaQC i = L.Y.naut.iotaQC i from rfl, hAut.iotaQC i, show (withLoc L).naut.iotaQ i = L.Y.naut.iotaQ i from rfl, hAut.iotaQ i]`. Both sides reduce to the same expression.

Use `(congrArg (fun f => (heckePol (withLoc L).nd i x hex.choose).map f) hio).trans ?_` and prove the remaining obligations. Rewrite using `[heckePol_map D L i x _ hSO]`. Simplify using `only [pw, dif_pos hex, sysPol]`. Use `congr 1`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[hc _ hvA k]`.
-/
theorem exists_big_oSplit : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → ∃ big : D.what₂.places.Pl → Finset ℂ, ∀ (L : LocAll (lay0 D)) (Sp : NdSpec A.pl M C big L.X L.T), AutSpec A M tp.tup Sp.iq L.Y L.C → GlobalTheory.SplitCoef.OSplit (withLoc L) := by
  intro D cf jE A low Pq S hL eig θ Bs M C tp hCS hMt hstar hExp hsplit hCheb
  classical
  have hsys := fun w => GlobalTheory.T.galois_family_local_global D cf jE A low Pq S hL eig θ Bs M C tp hCS hMt hstar hExp hsplit hCheb w
  choose FA Sy hSy using hsys
  have hexc := fun w : D.what₂.places.Pl => GlobalTheory.T.finite_exceptional_places_over_prime D (D.what₂.places.resChar w) (D.what₂.places.resChar_prime w)
  choose FB hFB using hexc
  let Fw : D.what₂.places.Pl → Finset (PlE D.host) := fun w => FA w ∪ FB w ∪ C.Q w
  let Pv : D.what₂.places.Pl → G D.host.E D.nd.Om → PlE D.host → Prop := fun w σ v =>
    v ∉ Fw w ∧ IsSplitPl D.host v ∧
      ∃ B : ValuationSubring D.nd.Om, IsPlaceOver (F := D.host.E) B v ∧ IsFrob (F := D.host.E) B (normV v) σ
  let pw : D.what₂.places.Pl → (PlE D.host → ℕ → ℂ) → G D.host.E D.nd.Om → ℂ[X] := fun w c σ =>
    if h : ∃ v, Pv w σ v then sysPol D c h.choose else 0
  have hcore := fun (w : D.what₂.places.Pl) (c : PlE D.host → ℕ → ℂ) =>
    GlobalTheory.T.exists_finite_splitting_set_frobeniusPolynomials (D.what₂.places.resChar w) (A.pl.ι w) D.host.E D.nd.Om D.R.nV (frobSet D (Fw w)) (pw w c)
      (dense_frobSet D hCheb (Fw w))
  choose SC hSC using hcore
  refine ⟨fun w => (Sy w).biUnion (SC w), ?_⟩
  intro L Sp hAut i x r hr
  obtain ⟨c, hcS, hc⟩ := hSy ((withLoc L).nd.w i) _ L Sp hAut i x rfl
  haveI : Fact ((withLoc L).nd.l i).Prime := (withLoc L).nd.lPrime i
  letI := (withLoc L).nd.dvrO i
  letI := (withLoc L).nd.algO i
  letI := (withLoc L).nd.finO i
  letI := (withLoc L).nd.topO i
  letI := (withLoc L).nd.trO i
  refine hSC ((withLoc L).nd.w i) c ((withLoc L).nd.l i) ((withLoc L).nd.w_l i) ((withLoc L).nd.O i) ((withLoc L).nd.O_adic i) (Sp.iq i) ?_ ?_ r
    hr.1 hr.2.1 ?_
  · exact fun z => Sp.iq_alg i z
  · intro z hz
    exact Sp.iq_big i z (Finset.mem_biUnion.2 ⟨c, hcS, hz⟩)
  · intro σ hσ
    have hex : ∃ v, Pv ((withLoc L).nd.w i) σ v := hσ
    have hspec := hex.choose_spec
    obtain ⟨hvF, hvs, B, hB, hFr⟩ := hspec
    have hvF' := hvF
    simp only [Fw, Finset.mem_union, not_or] at hvF'
    obtain ⟨⟨hvA, hvB⟩, hvQ⟩ := hvF'
    have hSO : SplitOut (withLoc L).nd i hex.choose := by
      have hQi : (withLoc L).nd.Q i = C.Q ((withLoc L).nd.w i) :=
        (Sp.Q_eq _ _ i ((L.X.nd.locs_mem _ _ i).2 ⟨rfl, rfl⟩)).trans (Sp.Qc_eq _ _)
      obtain ⟨h1, h2⟩ := hFB ((withLoc L).nd.w i) _ hvB
      refine ⟨hvs, ?_, ?_, ?_⟩
      · rw [← (withLoc L).nd.w_l i]; exact h1
      · intro hmem
        apply h2
        have := ((withLoc L).nd.S_def i _).1 hmem
        rw [← (withLoc L).nd.w_l i] at this
        exact this
      · show _ ∉ (withLoc L).nd.Q i
        rw [hQi]; exact hvQ
    refine (congrArg (Polynomial.map _) (hr.2.2 _ hSO B σ hB hFr)).trans ?_
    have hio : (qCast ((withLoc L).nd.w_l i) (A.pl.ι ((withLoc L).nd.w i))).toRingHom.comp
        ((Sp.iq i).comp (algebraMap ((withLoc L).nd.O i) (FractionRing ((withLoc L).nd.O i)))) = iotaOC (withLoc L) i := by
      ext z
      simp only [iotaOC, RingHom.comp_apply]
      rw [show (withLoc L).naut.iotaQC i = L.Y.naut.iotaQC i from rfl, hAut.iotaQC i,
        show (withLoc L).naut.iotaQ i = L.Y.naut.iotaQ i from rfl, hAut.iotaQ i]
      rfl
    refine (congrArg (fun f => (heckePol (withLoc L).nd i x hex.choose).map f) hio).trans ?_
    rw [heckePol_map D L i x _ hSO]
    simp only [pw, dif_pos hex, sysPol]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hc _ hvA k]

end GlobalTheory.OSplitBig
