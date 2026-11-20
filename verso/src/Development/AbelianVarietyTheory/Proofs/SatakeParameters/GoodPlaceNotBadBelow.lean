import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoOneOfSummable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTwistPlacesAboveK
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.GoodOffBad

/- English proof (translation)
The claim follows from `D.host.φ₀.injective (by rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply])`.
-/
theorem conj_eq_complexConj (D : D7) (x : D.host.E) : D.host.conj x = IsCMField.complexConj D.host.E x :=
  D.host.φ₀.injective (by
    rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply])

/- English proof (translation)
Introduce `x y hxy`. Rewrite using `[GlobalTheory.SplitConjPlace.mem_conjPlE]`. Establish `: IsCMField.ringOfIntegersComplexConj D.host.E x = y`. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Rewrite using `[IsCMField.coe_ringOfIntegersComplexConj, hxy, conj_eq_complexConj]`.

Rewrite using `[this]`.
-/
theorem isConjPl_conjPlE_left {D : D7} (P : PlE D.host) : IsConjPl D.host (GlobalTheory.SplitConjPlace.conjPlE P) P := by
  intro x y hxy
  rw [GlobalTheory.SplitConjPlace.mem_conjPlE]
  have : IsCMField.ringOfIntegersComplexConj D.host.E x = y := by
    apply RingOfIntegers.ext
    rw [IsCMField.coe_ringOfIntegersComplexConj, hxy, conj_eq_complexConj]
  rw [this]

/- English proof (translation)
Use `show ((p : ℕ) : 𝓞 D.host.E) ∈ (GlobalTheory.SplitConjPlace.conjPlE P).asIdeal ↔ ((p : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal`. Rewrite using `[GlobalTheory.SplitConjPlace.mem_conjPlE, map_natCast]`.
-/
theorem conjPlE_mem_placesOver {D : D7} (P : PlE D.host) (p : ℕ) :
    GlobalTheory.SplitConjPlace.conjPlE P ∈ placesOver D.host.E p ↔ P ∈ placesOver D.host.E p := by
  show ((p : ℕ) : 𝓞 D.host.E) ∈ (GlobalTheory.SplitConjPlace.conjPlE P).asIdeal ↔ ((p : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal
  rw [GlobalTheory.SplitConjPlace.mem_conjPlE, map_natCast]

/- English proof (translation)
Introduce `hL D P X i _ w hG v hov`. Establish `hlev` using `X.recR.base.lev`. Establish `hmu : D.nd.mu i = D.what₂.muAt (D.nd.w i)`. Break down `D.what₂.muAt_or (D.nd.w i) with h | h` into its components or cases. Conclude with `absurd h (D.nd.w_tw i)`.

Rewrite using `[h, D.nd.mu_w i]`. Establish `hxi` using `X.recR.tupXi (D.nd.mu i) (Or.inr ⟨D.nd.w i, hmu⟩)`. Establish `hunr : (X.R.xiH (X.tupT (D.nd.mu i))).UnrAt w`. Assume the negation of the conclusion as `hn`. Break down `(hlev.Q_ram _ w).1 hn with h | ⟨PP, hPP, hc⟩` into its components or cases.

Conclude with `(hG w (Or.inr h)).1 rfl`. Conclude with `(hG PP (Or.inr hPP)).2 hc`. Rewrite `hunr` using `[hxi, D.nd.mu_w i, X.Tp.xi_tw, D.nd.w_l i]`. Establish `hψ` using `X.Tp.psi_is (D.nd.w i) (D.nd.w_tw i)`. Rewrite `hψ` using `[D.nd.w_l i]`.

Use `set δ := X.R.C.delAt (D.nd.l i) with hδdef`. Use `set ψ := X.Tp.psi (D.nd.w i) with hψdef`. Use `set p := if D.nd.l i = D.host.pde then D.host.pde' else D.host.pde with hpdef`. Establish `hd : IsDelta (H` using `D.host) p δ := by`. Rewrite using `[hδdef, hpdef, CharFrame.delAt]`.

Use `split_ifs`. Use `exacts [X.R.C.isDel', X.R.C.isDel]`. Establish `hmul : ∀ x, (δ * ψ).loc w x = δ.loc w x * ψ.loc w x` using `fun _ => rfl`. Establish `hnp : ¬ OverP D.host p w`. Introduce `hw`.

Take `⟨a, ha⟩` from `hψ.ord`. Establish `h15 : 15 ∣ D.nd.l i ^ a`. Use `(hd.ine w hw (D.nd.l i ^ a)).1 fun x hx => ?_` and prove the remaining obligations. Establish `h1 : δ.loc w x * ψ.loc w x = 1` using `(hmul x).symm.trans (hunr x hx)`. Establish `h2 : ψ.loc w x ^ (D.nd.l i ^ a) = 1`.

Use `congrArg (fun ξ : HChar D.host.E => ξ.loc w x) ha` as an intermediate fact. Simplify `this` using `[HChar.loc]`. Establish `h3 : (δ.loc w x * ψ.loc w x) ^ (D.nd.l i ^ a) = 1` using `by rw [h1, one_pow]`. Rewrite `h3` using `[mul_pow, h2, mul_one]`. Then use the resulting hypothesis. Establish `hl : (D.nd.l i).Prime` using `(D.nd.lPrime i).out`.

Establish `h3 : 3 = D.nd.l i` using `(Nat.prime_dvd_prime_iff_eq Nat.prime_three hl).1 (Nat.prime_three.dvd_of_dvd_pow (dvd_trans (by norm_num) h15))`. Establish `h5 : 5 = D.nd.l i` using `(Nat.prime_dvd_prime_iff_eq (by norm_num) hl).1 ((show (5 : ℕ).Prime by norm_num).dvd_of_dvd_pow (dvd_trans (by norm_num) h15))`. Use linear arithmetic over natural numbers and integers. Establish `hng : ∀ k : Fin 2, w ∉ placesOver D.host.E (D.host.g k)`. Introduce `k hw`.

Establish `hs : GlobalTheory.Mem.Chr.SplitsC D.host.E (D.host.g k)` using `D.nd.g_split k`. Break down `(GlobalTheory.BigOn.Inhab.overP_iff (D.host.g_prime k) hs (X.R.C.P.pb_over k) w).1 hw with h | ⟨w', h, hc⟩` into its components or cases. Conclude with `(hG w (Or.inl ((hlev.Pg w).2 ⟨k, GlobalTheory.BigOn.Inhab.mem_aboveK.1 h⟩))).1 rfl`. Conclude with `(hG w' (Or.inl ((hlev.Pg w').2 ⟨k, GlobalTheory.BigOn.Inhab.mem_aboveK.1 h⟩))).2 hc`. Establish `hnQ : w ∉ D.nd.Q i`.

Introduce `hQ`. Rewrite `hQ` using `[P.Q_eq i]`. Use `(hψ.ram w).1 ?_ hQ` and prove the remaining obligations. Introduce `x hx`. Establish `h1 : δ.loc w x * ψ.loc w x = 1` using `(hmul x).symm.trans (hunr x hx)`.

Rewrite `h1` using `[hd.unr w hnp x hx, one_mul]`. Conclude with `h1`. Establish `hnp' : w ∉ placesOver D.host.E p` using `hnp`. Introduce and unpack `⟨w', hover, hw'⟩`. Break down `GlobalTheory.SplitConjPlace.eq_or_eq_conjPlE w w' (hover.trans hov.symm) with e | e` into its components or cases.

Substitute `e` using the available equality. Break down `hw' with hQ | ⟨k, hg⟩ | hpd` into its components or cases. Conclude with `hnQ hQ`. Conclude with `hng k hg`. Conclude with `hnp' hpd`.

Substitute `e` using the available equality. Break down `hw' with hQ | ⟨k, hg⟩ | hpd` into its components or cases. Conclude with `hnQ (P.H.hecke.Q_conj i _ w (isConjPl_conjPlE_left w) hQ)`. Conclude with `hng k ((conjPlE_mem_placesOver w _).1 hg)`. Conclude with `hnp' ((conjPlE_mem_placesOver w _).1 hpd)`.
-/
theorem good_not_mem_badPl : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D) (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (i : D.nd.Loc), Formalism.IndefR.RecTie.Used0 D (D.nd.mu i) → ∀ Pp, GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) Pp → ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)), Formalism.L2.NG.OverPl Pp v → v ∉ Formalism.L2.badPl D i := by
  intro hL D P X i _ w hG v hov
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

  have hnQ : w ∉ D.nd.Q i := by
    intro hQ
    rw [P.Q_eq i] at hQ
    refine (hψ.ram w).1 ?_ hQ
    intro x hx
    have h1 : δ.loc w x * ψ.loc w x = 1 := (hmul x).symm.trans (hunr x hx)
    rw [hd.unr w hnp x hx, one_mul] at h1
    exact h1

  have hnp' : w ∉ placesOver D.host.E p := hnp
  rintro ⟨w', hover, hw'⟩
  rcases GlobalTheory.SplitConjPlace.eq_or_eq_conjPlE w w' (hover.trans hov.symm) with e | e
  · subst e
    rcases hw' with hQ | ⟨k, hg⟩ | hpd
    · exact hnQ hQ
    · exact hng k hg
    · exact hnp' hpd
  · subst e
    rcases hw' with hQ | ⟨k, hg⟩ | hpd
    · exact hnQ (P.H.hecke.Q_conj i _ w (isConjPl_conjPlE_left w) hQ)
    · exact hng k ((conjPlE_mem_placesOver w _).1 hg)
    · exact hnp' ((conjPlE_mem_placesOver w _).1 hpd)

end GlobalTheory.GoodOffBad
