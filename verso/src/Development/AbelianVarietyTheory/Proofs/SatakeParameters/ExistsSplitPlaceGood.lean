import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoOneOfSummable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTwistPlacesAboveK
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodPlaceOutsideBadSets
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimPartsAtIffBadAndOff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumWIffGoodFormsOrthSum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqOfMapEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalHeckeScalarOnTypeSpacesAllPlaces
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.OffBad

/- English proof (translation)
Establish `hc : ∀ x : 𝓞 D.host.E, ((GlobalTheory.SumWCompare.cj D.host.E x : 𝓞 D.host.E) : D.host.E) = D.host.conj (x : D.host.E)`. Introduce `x`. Rewrite using `[GlobalTheory.SumWCompare.cj_coe, GlobalTheory.DimPartsCompare.star_conj]`. Establish `hcc : ∀ z : D.host.E, D.host.conj (D.host.conj z) = z`. Introduce `z`.

Rewrite using `[← GlobalTheory.DimPartsCompare.star_conj, ← GlobalTheory.DimPartsCompare.star_conj, star_star]`. Take `⟨x, hx, hy⟩` from `hw`. Establish `hsp : IsSplitPl D.host (GlobalTheory.DimPartsCompare.cPl w)`. Use `⟨GlobalTheory.SumWCompare.cj D.host.E x, ?_, fun y e hy' => ?_⟩` and prove the remaining obligations. Rewrite using `[GlobalTheory.DimPartsCompare.mem_cPl, GlobalTheory.SumWCompare.cj_cj]`.

Conclude with `hx`. Rewrite `hy'` using `[GlobalTheory.DimPartsCompare.mem_cPl]`. Use `hy _ ?_ hy'` and prove the remaining obligations. Rewrite using `[hc, show y = x from RingOfIntegers.ext (by rw [e, hc, hcc])]`. Take `⟨s, -, hs, -⟩` from `GlobalTheory.SplitConjPlace.splitEx_all D _ hsp`.

Use `⟨s, HeightOneSpectrum.ext (Ideal.ext fun y => ?_)⟩` and prove the remaining obligations. Use `hs (GlobalTheory.SumWCompare.cj D.host.E y) y (by rw [hc, hcc])` as an intermediate fact. Rewrite `this` using `[GlobalTheory.DimPartsCompare.mem_cPl, GlobalTheory.SumWCompare.cj_cj]`. Conclude with `this.symm`.
-/
theorem splitPlace_of_isSplitPl (D : D7) (w : PlE D.host) (hw : IsSplitPl D.host w) : ∃ s : SplitPlace D.host.E, s.w = w := by
  have hc : ∀ x : 𝓞 D.host.E, ((GlobalTheory.SumWCompare.cj D.host.E x : 𝓞 D.host.E) : D.host.E) = D.host.conj (x : D.host.E) := by
    intro x; rw [GlobalTheory.SumWCompare.cj_coe, GlobalTheory.DimPartsCompare.star_conj]
  have hcc : ∀ z : D.host.E, D.host.conj (D.host.conj z) = z := by
    intro z; rw [← GlobalTheory.DimPartsCompare.star_conj, ← GlobalTheory.DimPartsCompare.star_conj, star_star]
  obtain ⟨x, hx, hy⟩ := hw
  have hsp : IsSplitPl D.host (GlobalTheory.DimPartsCompare.cPl w) := by
    refine ⟨GlobalTheory.SumWCompare.cj D.host.E x, ?_, fun y e hy' => ?_⟩
    · rw [GlobalTheory.DimPartsCompare.mem_cPl, GlobalTheory.SumWCompare.cj_cj]; exact hx
    · rw [GlobalTheory.DimPartsCompare.mem_cPl] at hy'
      refine hy _ ?_ hy'
      rw [hc, show y = x from RingOfIntegers.ext (by rw [e, hc, hcc])]
  obtain ⟨s, -, hs, -⟩ := GlobalTheory.SplitConjPlace.splitEx_all D _ hsp
  refine ⟨s, HeightOneSpectrum.ext (Ideal.ext fun y => ?_)⟩
  have := hs (GlobalTheory.SumWCompare.cj D.host.E y) y (by rw [hc, hcc])
  rw [GlobalTheory.DimPartsCompare.mem_cPl, GlobalTheory.SumWCompare.cj_cj] at this
  exact this.symm

/- English proof (translation)
Take `⟨P, Q, hPQ, hP, hQ⟩` from `h`. Rewrite using `[GlobalTheory.Mem.GoodPlace.isSplitPl_iff]`. Distinguish the cases in `hw : w = P`. Use `⟨Q, fun e => hPQ (hw.symm.trans e), ?_⟩ ext1` and prove the remaining obligations. Conclude with `hQ`.

Use `⟨P, hw, ?_⟩ ext1` and prove the remaining obligations. Conclude with `hP`.
-/
theorem isSplitPl_of_isSplit (D : D7) (w : PlE D.host)
    (h : Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (w.under (𝓞 D.host.F))) : IsSplitPl D.host w := by
  obtain ⟨P, Q, hPQ, hP, hQ⟩ := h
  rw [GlobalTheory.Mem.GoodPlace.isSplitPl_iff]
  by_cases hw : w = P
  · refine ⟨Q, fun e => hPQ (hw.symm.trans e), ?_⟩
    ext1; exact hQ
  · refine ⟨P, hw, ?_⟩
    ext1; exact hP

/- English proof (translation)
Establish `hlev` using `X.recR.base.lev`. Establish `hmu : D.nd.mu i = D.what₂.muAt (D.nd.w i)`. Break down `D.what₂.muAt_or (D.nd.w i) with h | h` into its components or cases. Conclude with `absurd h (D.nd.w_tw i)`. Rewrite using `[h, D.nd.mu_w i]`.

Establish `hxi` using `X.recR.tupXi (D.nd.mu i) (Or.inr ⟨D.nd.w i, hmu⟩)`. Establish `hunr : (X.R.xiH (X.tupT (D.nd.mu i))).UnrAt w`. Assume the negation of the conclusion as `hn`. Break down `(hlev.Q_ram _ w).1 hn with h | ⟨PP, hPP, hc⟩` into its components or cases. Conclude with `(hG w (Or.inr h)).1 rfl`.

Conclude with `(hG PP (Or.inr hPP)).2 hc`. Rewrite `hunr` using `[hxi, D.nd.mu_w i, X.Tp.xi_tw, D.nd.w_l i]`. Establish `hψ` using `X.Tp.psi_is (D.nd.w i) (D.nd.w_tw i)`. Rewrite `hψ` using `[D.nd.w_l i]`. Use `set δ := X.R.C.delAt (D.nd.l i) with hδdef`.

Use `set ψ := X.Tp.psi (D.nd.w i) with hψdef`. Use `set p := if D.nd.l i = D.host.pde then D.host.pde' else D.host.pde with hpdef`. Establish `hd : IsDelta (H` using `D.host) p δ := by`. Rewrite using `[hδdef, hpdef, CharFrame.delAt]`. Use `split_ifs`.

Use `exacts [X.R.C.isDel', X.R.C.isDel]`. Establish `hmul : ∀ x, (δ * ψ).loc w x = δ.loc w x * ψ.loc w x` using `fun _ => rfl`. Establish `hnp : ¬ OverP D.host p w`. Introduce `hw`. Take `⟨a, ha⟩` from `hψ.ord`.

Establish `h15 : 15 ∣ D.nd.l i ^ a`. Use `(hd.ine w hw (D.nd.l i ^ a)).1 fun x hx => ?_` and prove the remaining obligations. Establish `h1 : δ.loc w x * ψ.loc w x = 1` using `(hmul x).symm.trans (hunr x hx)`. Establish `h2 : ψ.loc w x ^ (D.nd.l i ^ a) = 1`. Use `congrArg (fun ξ : HChar D.host.E => ξ.loc w x) ha` as an intermediate fact.

Simplify `this` using `[HChar.loc]`. Establish `h3 : (δ.loc w x * ψ.loc w x) ^ (D.nd.l i ^ a) = 1` using `by rw [h1, one_pow]`. Rewrite `h3` using `[mul_pow, h2, mul_one]`. Then use the resulting hypothesis. Establish `hl : (D.nd.l i).Prime` using `(D.nd.lPrime i).out`. Establish `h3 : 3 = D.nd.l i` using `(Nat.prime_dvd_prime_iff_eq Nat.prime_three hl).1 (Nat.prime_three.dvd_of_dvd_pow (dvd_trans (by norm_num) h15))`.

Establish `h5 : 5 = D.nd.l i` using `(Nat.prime_dvd_prime_iff_eq (by norm_num) hl).1 ((show (5 : ℕ).Prime by norm_num).dvd_of_dvd_pow (dvd_trans (by norm_num) h15))`. Use linear arithmetic over natural numbers and integers. Establish `hng : ∀ k : Fin 2, w ∉ placesOver D.host.E (D.host.g k)`. Introduce `k hw`. Establish `hs : GlobalTheory.Mem.Chr.SplitsC D.host.E (D.host.g k)` using `D.nd.g_split k`.

Break down `(GlobalTheory.BigOn.Inhab.overP_iff (D.host.g_prime k) hs (X.R.C.P.pb_over k) w).1 hw with h | ⟨w', h, hc⟩` into its components or cases. Conclude with `(hG w (Or.inl ((hlev.Pg w).2 ⟨k, GlobalTheory.BigOn.Inhab.mem_aboveK.1 h⟩))).1 rfl`. Conclude with `(hG w' (Or.inl ((hlev.Pg w').2 ⟨k, GlobalTheory.BigOn.Inhab.mem_aboveK.1 h⟩))).2 hc`. Conclude with `⟨hng, hnp⟩`.
-/
theorem good_off_gp (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D) (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp)
    (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hG : GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) w) :
    (∀ k : Fin 2, w ∉ placesOver D.host.E (D.host.g k)) ∧
      w ∉ placesOver D.host.E (if D.nd.l i = D.host.pde then D.host.pde' else D.host.pde) := by
  have hlev := X.recR.base.lev
  have hmu : D.nd.mu i = D.what₂.muAt (D.nd.w i) := by
    rcases D.what₂.muAt_or (D.nd.w i) with h | h
    · exact absurd h (D.nd.w_tw i)
    · rw [h, D.nd.mu_w i]
  have hxi := X.recR.tupXi (D.nd.mu i) (Or.inr ⟨D.nd.w i, hmu⟩)
  have hunr : (X.R.xiH (X.tupT (D.nd.mu i))).UnrAt w := by
    by_contra hn
    rcases (hlev.Q_ram _ w).1 hn with h | ⟨PP, hPP, hc⟩
    · exact (hG w (Or.inr h)).1 rfl
    · exact (hG PP (Or.inr hPP)).2 hc
  rw [hxi, D.nd.mu_w i, X.Tp.xi_tw, D.nd.w_l i] at hunr
  have hψ := X.Tp.psi_is (D.nd.w i) (D.nd.w_tw i)
  rw [D.nd.w_l i] at hψ
  set δ := X.R.C.delAt (D.nd.l i) with hδdef
  set ψ := X.Tp.psi (D.nd.w i) with hψdef
  set p := if D.nd.l i = D.host.pde then D.host.pde' else D.host.pde with hpdef
  have hd : IsDelta (H := D.host) p δ := by
    rw [hδdef, hpdef, CharFrame.delAt]
    split_ifs
    exacts [X.R.C.isDel', X.R.C.isDel]
  have hmul : ∀ x, (δ * ψ).loc w x = δ.loc w x * ψ.loc w x := fun _ => rfl
  have hnp : ¬ OverP D.host p w := by
    intro hw
    obtain ⟨a, ha⟩ := hψ.ord
    have h15 : 15 ∣ D.nd.l i ^ a := by
      refine (hd.ine w hw (D.nd.l i ^ a)).1 fun x hx => ?_
      have h1 : δ.loc w x * ψ.loc w x = 1 := (hmul x).symm.trans (hunr x hx)
      have h2 : ψ.loc w x ^ (D.nd.l i ^ a) = 1 := by
        have := congrArg (fun ξ : HChar D.host.E => ξ.loc w x) ha
        simpa [HChar.loc] using this
      have h3 : (δ.loc w x * ψ.loc w x) ^ (D.nd.l i ^ a) = 1 := by rw [h1, one_pow]
      rwa [mul_pow, h2, mul_one] at h3
    have hl : (D.nd.l i).Prime := (D.nd.lPrime i).out
    have h3 : 3 = D.nd.l i := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hl).1
      (Nat.prime_three.dvd_of_dvd_pow (dvd_trans (by norm_num) h15))
    have h5 : 5 = D.nd.l i := (Nat.prime_dvd_prime_iff_eq (by norm_num) hl).1
      ((show (5 : ℕ).Prime by norm_num).dvd_of_dvd_pow (dvd_trans (by norm_num) h15))
    omega
  have hng : ∀ k : Fin 2, w ∉ placesOver D.host.E (D.host.g k) := by
    intro k hw
    have hs : GlobalTheory.Mem.Chr.SplitsC D.host.E (D.host.g k) := D.nd.g_split k
    rcases (GlobalTheory.BigOn.Inhab.overP_iff (D.host.g_prime k) hs (X.R.C.P.pb_over k) w).1 hw with h | ⟨w', h, hc⟩
    · exact (hG w (Or.inl ((hlev.Pg w).2 ⟨k, GlobalTheory.BigOn.Inhab.mem_aboveK.1 h⟩))).1 rfl
    · exact (hG w' (Or.inl ((hlev.Pg w').2 ⟨k, GlobalTheory.BigOn.Inhab.mem_aboveK.1 h⟩))).2 hc
  exact ⟨hng, hnp⟩

end GlobalTheory.OffBad

namespace GlobalTheory.OffBad

/- English proof (translation)
Introduce `_ hL D P X hA h41 _ htl i w hG hsplit`. Take `⟨sp, hsp⟩` from `splitPlace_of_isSplitPl D w (isSplitPl_of_isSplit D w hsplit)`. Take `⟨hng, hnp⟩` from `good_off_gp hL D P X i w hG`. Establish `hQ` using `(GlobalTheory.OffSQ.good_off_SQ hL D P X hA h41 htl i w hG).2`. Establish `HT` using `P.H.hecke`.

Establish `hbad : sp.v ∉ badPl D i`. Introduce and unpack `⟨w', hover, hw'⟩`. Establish `hp : ∀ p : ℕ, w' ∈ placesOver D.host.E p → w ∈ placesOver D.host.E p`. Introduce `p hp`. Establish `h1 : algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E) (p : 𝓞 (maximalRealSubfield D.host.E)) ∈ w'.asIdeal` using `by rw [map_natCast]; exact hp`.

Establish `h2 : (p : 𝓞 (maximalRealSubfield D.host.E)) ∈ sp.v.asIdeal`. Rewrite using `[← hover]`. Conclude with `h1`. Establish `h3 : algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E) (p : 𝓞 (maximalRealSubfield D.host.E)) ∈ sp.w.asIdeal`. Rewrite using `[← Ideal.mem_comap, sp.w_under]`.

Conclude with `h2`. Rewrite `h3` using `[map_natCast, hsp]`. Conclude with `h3`. Break down `hw' with hQ' | ⟨kk, hg⟩ | hpd` into its components or cases. Break down `GlobalTheory.SplitConjPlace.eq_or_eq_conjPlE sp.w w' (hover.trans sp.w_under.symm) with e | e` into its components or cases.

Rewrite `hQ'` using `[e, hsp]`. Conclude with `hQ hQ'`. Apply `hQ` to reduce the goal to its premises. Rewrite using `[← hsp]`. Use `HT.Q_conj i w' sp.w ?_ hQ'` and prove the remaining obligations.

Rewrite using `[e]`. Introduce `x y hxy`. Rewrite using `[GlobalTheory.SplitConjPlace.mem_conjPlE]`. Establish `hy : IsCMField.ringOfIntegersComplexConj D.host.E x = y`. Apply `RingOfIntegers.ext` to reduce the goal to its premises.

Rewrite using `[IsCMField.coe_ringOfIntegersComplexConj, hxy, GlobalTheory.HeckeScalarAll.host_conj_eq']`. Rewrite using `[← hy]`. Conclude with `hng kk (hp _ hg)`. Conclude with `hnp (hp _ hpd)`. Use `⟨sp, hsp, fun κ hκ => HT.J_hyp i κ (fun v hv => hκ v ?_)⟩` and prove the remaining obligations.

Introduce and unpack `rfl`. Conclude with `hv hbad`.
-/
theorem offbad : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), Formalism.MainNotions.SumRepresentations.Conclusion41 D → Formalism.MainNotions.SumRepresentations.adm7 D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)), GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) w → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (w.under (𝓞 D.host.F)) → ∃ sp : SplitPlace D.host.E, sp.w = w ∧ (∀ κ : GAf D.host.E D.R.nV, TrivOutside {sp.v} κ → (κ ∈ (P.M.loc i).J ↔ κ ∈ Umax D.host.E D.R.nV) ∧ ∀ hκ : κ ∈ (P.M.loc i).J, (P.M.loc i).χ ⟨κ, hκ⟩ = 1) := by
  intro _ hL D P X hA h41 _ htl i w hG hsplit
  obtain ⟨sp, hsp⟩ := splitPlace_of_isSplitPl D w (isSplitPl_of_isSplit D w hsplit)
  obtain ⟨hng, hnp⟩ := good_off_gp hL D P X i w hG
  have hQ := (GlobalTheory.OffSQ.good_off_SQ hL D P X hA h41 htl i w hG).2
  have HT := P.H.hecke
  have hbad : sp.v ∉ badPl D i := by
    rintro ⟨w', hover, hw'⟩
    have hp : ∀ p : ℕ, w' ∈ placesOver D.host.E p → w ∈ placesOver D.host.E p := by
      intro p hp
      have h1 : algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E) (p : 𝓞 (maximalRealSubfield D.host.E)) ∈
          w'.asIdeal := by rw [map_natCast]; exact hp
      have h2 : (p : 𝓞 (maximalRealSubfield D.host.E)) ∈ sp.v.asIdeal := by
        rw [← hover]; exact h1
      have h3 : algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E) (p : 𝓞 (maximalRealSubfield D.host.E)) ∈
          sp.w.asIdeal := by
        rw [← Ideal.mem_comap, sp.w_under]; exact h2
      rw [map_natCast, hsp] at h3
      exact h3
    rcases hw' with hQ' | ⟨kk, hg⟩ | hpd
    · rcases GlobalTheory.SplitConjPlace.eq_or_eq_conjPlE sp.w w' (hover.trans sp.w_under.symm) with e | e
      · rw [e, hsp] at hQ'
        exact hQ hQ'
      · apply hQ
        rw [← hsp]
        refine HT.Q_conj i w' sp.w ?_ hQ'
        rw [e]
        intro x y hxy
        rw [GlobalTheory.SplitConjPlace.mem_conjPlE]
        have hy : IsCMField.ringOfIntegersComplexConj D.host.E x = y := by
          apply RingOfIntegers.ext
          rw [IsCMField.coe_ringOfIntegersComplexConj, hxy, GlobalTheory.HeckeScalarAll.host_conj_eq']
        rw [← hy]
    · exact hng kk (hp _ hg)
    · exact hnp (hp _ hpd)
  refine ⟨sp, hsp, fun κ hκ => HT.J_hyp i κ (fun v hv => hκ v ?_)⟩
  rintro rfl
  exact hv hbad

end GlobalTheory.OffBad
