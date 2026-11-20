import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.VpBounds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricSumEqHeckeLValueMulAuxiliaryFactors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPartEqOneOfLevel
import Development.AbelianVarietyTheory.Definitions.Divisors.IsValCharTwist
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeanValuationGeOfIntegralAtPrimeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialZetaValuesAtNegIntUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareNuTwistedTupleIsCMValueHeckeCharacterStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistPlacesUnderSplitCoprimeConductorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareNuTwistedTupleRamifiedAtTwistPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistPlacesUnderPrimeNotMemOfNormCoprimeStatement

noncomputable section
open NumberField IsDedekindDomain Polynomial
open Formalism.BasicNotions Formalism.IndefR.Links GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.CMVal
open Formalism.DivisionValues (vw)

namespace GlobalTheory.RhoLowProof

/- English proof (translation)
The claim follows from `GlobalTheory.T.meanValuation_ge_of_integral_at_prime σ hp hβ hc hl hw h`.
-/
theorem meanVal_lower {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ) {β : ℂ} {p : K[X]}
    (hp : IsMinPol σ β p) (hβ : β ≠ 0) {c : K} (hc : c ≠ 0) {l : ℕ} (hl : l.Prime)
    {w : Formalism.PairingDivisionLocalBalance.Pl K} (hw : (l : 𝓞 K) ∈ w.asIdeal) {m : ℕ}
    (h : IntAt l ((l : ℂ) ^ m * (σ c * β))) :
    -((m : ℝ) * (vw w (l : K) : ℝ)) ≤ (vw w c : ℝ) + meanVal_vw w p :=
  GlobalTheory.T.meanValuation_ge_of_integral_at_prime σ hp hβ hc hl hw h

/- English proof (translation)
The claim follows from `GlobalTheory.T.partialZeta_values_at_neg_int_unique hk h h'`.
-/
theorem classZetaVals_unique {E : Type} [Field E] [NumberField E] {k : ℕ} (hk : 2 ≤ k) {z z' : ClassGroup (OF E) → ℚ}
    (h : GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsClassZetaVals k z) (h' : GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsClassZetaVals k z') : z = z' :=
  GlobalTheory.T.partialZeta_values_at_neg_int_unique hk h h'

section Twist
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc)

open Classical in

/- English proof (translation)
The claim follows from `GlobalTheory.T.square_nu_twisted_tuple_isCMValueHeckeCharacter G hL t i j hs`.
-/
theorem twist_val {μ₀ : T} (hL : L.Is μ₀) (t : T) (i j : Fin D.R.m) {s : ℕ} (hs : s ≤ halfRank D i j) :
    IsValChar (cmPhi D) s (kap D sc.cGap i j s) (condF G.pl)
      ((GlobalTheory.SqTop.twPl G t).image fun P => P.under (𝓞 D.host.F)) (nuH G t i j) :=
  GlobalTheory.T.square_nu_twisted_tuple_isCMValueHeckeCharacter G hL t i j hs

open Classical in

/- English proof (translation)
The claim follows from `GlobalTheory.T.isFinSetSplitPlacesCoprimeConductor_twPl_under G hL t`.
-/
theorem squareTopTwistPlaces_coprime_splitPlaces {μ₀ : T} (hL : L.Is μ₀) (t : T) :
    IsFinSetSplitPlacesCoprimeConductor (condF G.pl) ((GlobalTheory.SqTop.twPl G t).image fun P => P.under (𝓞 D.host.F)) :=
  GlobalTheory.T.isFinSetSplitPlacesCoprimeConductor_twPl_under G hL t

/- English proof (translation)
The claim follows from `GlobalTheory.T.square_nu_twisted_tuple_ramified_at_twist_place G hL t i j`.
-/
theorem twist_ram {μ₀ : T} (hL : L.Is μ₀) (t : T) (i j : Fin D.R.m) :
    ∀ P ∈ GlobalTheory.SqTop.twPl G t, ¬ (nuH G t i j).UnrAt P :=
  GlobalTheory.T.square_nu_twisted_tuple_ramified_at_twist_place G hL t i j

open Classical in

/- English proof (translation)
The claim follows from `GlobalTheory.T.twist_places_under_prime_not_mem_of_norm_coprime G t hl hlw hQ`.
-/
theorem twist_prime (t : T) {l : ℕ} (hl : l.Prime) {w : Formalism.PairingDivisionLocalBalance.Pl D.what₂.LL} (hlw : (l : 𝓞 D.what₂.LL) ∈ w.asIdeal)
    (hQ : (GlobalTheory.SqTop.Qn G t : 𝓞 D.what₂.LL) ∉ w.asIdeal) :
    ∀ q ∈ (GlobalTheory.SqTop.twPl G t).image (fun P => P.under (𝓞 D.host.F)), (l : 𝓞 D.host.F) ∉ q.asIdeal :=
  GlobalTheory.T.twist_places_under_prime_not_mem_of_norm_coprime G t hl hlw hQ

end Twist

/- English proof (translation)
Unfold `vw`. Rewrite using `[← FractionalIdeal.spanSingleton_pow, FractionalIdeal.count_pow]`.
-/
theorem vw_pow {K : Type} [Field K] [NumberField K] (w : Formalism.PairingDivisionLocalBalance.Pl K) {z : K} (hz : z ≠ 0) (n : ℕ) :
    vw w (z ^ n) = n * vw w z := by
  unfold vw
  rw [← FractionalIdeal.spanSingleton_pow, FractionalIdeal.count_pow]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem over_under {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) :
    Over P (P.under (OF E)) := rfl

set_option maxHeartbeats 1000000 in
open Classical in

/- English proof (translation)
Use `haveI := hcm`. Use `haveI := hab`. Take `⟨x, hx, hx0, -, Λl, p, hΛl, hp, hg⟩` from `htv`. Establish `hU : UnramFin D.host.E` using `hfd.2.2.1`. Establish `hφ : IsCMType (cmPhi D)` using `hfd.2.2.2.2.2.2.1`.

Establish `e0 : x = Λ₀ s`. Establish `h` using `GlobalTheory.ToricSumValue.toricSum_eq GlobalTheory.Published.HeckeEntire_holds D.host.E D.what₂.Tau (cmPhi D) hφ s (kap D sc.cGap i j s) (condF G.pl) ∅ (nuH G μ₀ i j) (fun _ => G.pl.w G.pl.v0) Λ₀ hU hs1 hbc (fun q hq => absurd hq (Finset.notMem_empty q)) hx.1 (fun q hq => absurd …`. Simplify using `only [condQ, Finset.prod_empty, mul_one, Finset.filter_empty] at h`. Conclude with `hx.2.unique h`. Take `⟨Q, hQdef⟩ : ∃ Q : Finset (HeightOneSpectrum (OF D.host.E)), Q = (GlobalTheory.SqTop.twPl G t).image fun P => P.under (𝓞 D.host.F)` from `⟨_, rfl⟩`.

Establish `hQval` using `twist_val G hL t i j hs2`. Establish `hQaux` using `squareTopTwistPlaces_coprime_splitPlaces G hL t`. Establish `hQram` using `twist_ram G hL t i j`. Establish `hQpr` using `twist_prime G t hl hlw hQw`. Rewrite `hQval`, `hQaux`, `hQpr` using `[← hQdef]`.

Establish `hex : ∀ q ∈ Q, ∃ P ∈ GlobalTheory.SqTop.twPl G t, P.under (𝓞 D.host.F) = q` using `fun q hq => by`. Rewrite `hq` using `[hQdef]`. Conclude with `Finset.mem_image.1 hq`. Set `Pq : HeightOneSpectrum (OF D.host.E) → HeightOneSpectrum (𝓞 D.host.E)` to `fun q => if h : ∃ P ∈ GlobalTheory.SqTop.twPl G t, P.under (𝓞 D.host.F) = q then h.choose else G.pl.w G.pl.v0`. Establish `hPq : ∀ q ∈ Q, Pq q ∈ GlobalTheory.SqTop.twPl G t ∧ (Pq q).under (𝓞 D.host.F) = q` using `fun q hq => by`.

Establish `h` using `hex q hq`. Simplify using `only [Pq, dif_pos h]`. Conclude with `h.choose_spec`. Establish `hov : ∀ q ∈ Q, Over (Pq q) q` using `fun q hq => (over_under (Pq q)).trans (congrArg HeightOneSpectrum.asIdeal (hPq q hq).2)`. Establish `htor` using `GlobalTheory.ToricSumValue.toricSum_eq GlobalTheory.Published.HeckeEntire_holds D.host.E D.what₂.Tau (cmPhi D) hφ s (kap D sc.cGap i j s) (condF G.pl) Q (nuH G t i j) Pq Λ hU hs1 hbc hQaux hQval hov hΛ`.

Rewrite `htor` using `[Finset.filter_false_of_mem (fun q hq => hQram _ (hPq q hq).1), Finset.prod_empty, mul_one]`. Establish `hnu : nuH G t i j = nuH G μ₀ i j * Lc.xiH t`. Rewrite using `[nuH, nuH, hL.xi_base, mul_one, div_mul_eq_mul_div]`. Establish `hpic : GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsPicChar (condQ (condF G.pl) Q) (Lc.xiH t)`. Take `⟨k, hk, hko⟩` from `hL.xi_fin t`.

Use `⟨fun y => GlobalTheory.TypeValues.inf_eq_one _ hk hko y, fun u hu => ?_⟩` and prove the remaining obligations. Establish `a` using `GlobalTheory.CMVal.OrderUnits.finPart_eq_one D.host.E D.what₂.Tau (cmPhi D) hφ s (kap D sc.cGap i j s) (condF G.pl) Q (nuH G t i j) hU hbc hQaux hQval u hu`. Establish `hle : condQ (condF G.pl) Q ≤ condQ (condF G.pl) ∅`. Simplify using `only [condQ, Finset.prod_empty, mul_one]`. Conclude with `Ideal.mul_le_left`.

Establish `b` using `GlobalTheory.CMVal.OrderUnits.finPart_eq_one D.host.E D.what₂.Tau (cmPhi D) hφ s (kap D sc.cGap i j s) (condF G.pl) ∅ (nuH G μ₀ i j) hU hbc (fun q hq => absurd hq (Finset.notMem_empty q)) hx.1 u (hatOUnits_mono hle hu)`. Rewrite `a` using `[hnu, finPart_mul, b, one_mul]`. Conclude with `a`. Take `⟨zc, hzc, H⟩` from `hTD D.host.E D.what₂.Tau D.host.d (cmPhi D) s hfd hs1`. Establish `hV` using `((H (kap D sc.cGap i j s) (condF G.pl) Λl (nuH G μ₀ i j) hbc hΛl hx.1) l hl Q hQaux hQpr).2 (Lc.xiH t) (Λ s) hpic (hnu ▸ htor)`.

Take `⟨zc', hzc', hn⟩` from `hden`. Take `rfl : zc = zc'` from `classZetaVals_unique (by omega) hzc hzc'`. Use `set B := GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.betaBound_vp D.host.d s (kap D sc.cGap i j s) (condF G.pl) zc l with hB`. Use `set N := ⌈B / 12⌉₊ with hN`. Establish `hnl : n l = N` using `by rw [hn l hl]`.

Establish `hInt` using `hV (12 * N : ℕ) 1 one_pos (by`. Use `push_cast`. Use `Nat.le_ceil (B / 12)` as an intermediate fact. Use the proof step `linarith)`. Establish `hv0 : G.pl.v0 ∉ Q` using `fun h => by`.

Take `⟨P, hP, e⟩` from `hex _ h`. Establish `hP' : P ∈ Lc.Q t`. Simplify using `only [GlobalTheory.SqTop.twPl, Finset.mem_filter, locPl, Finset.mem_union] at hP`. Conclude with `hP.1.resolve_left hP.2`. Conclude with `G.pl.levelPlace_ne_basePlace t P hP' e`.

Establish `hram0 : ¬ (nuH G t i j).UnrAt (G.pl.w G.pl.v0)`. Establish `h1` using `(hQval.2.2.2 G.pl.v0 (G.pl.w G.pl.v0) ((over_under _).trans (congrArg HeightOneSpectrum.asIdeal (G.pl.w_over _ (Finset.mem_insert_self _ _))))).2 hv0`. Rewrite `h1` using `[GlobalTheory.FunObj.SqNum.Model.expIn_condF, if_pos (G.pl.mem_S0_of_sum_eq.2 (Or.inl rfl)), condExp, if_pos rfl]`. Conclude with `h1.not_unrAt one_ne_zero`. Establish `hΛs : Λ s ≠ 0` using `GlobalTheory.HeckePartial.IsHeckeL.ne_zero_of_one_le hQval.1 (GlobalTheory.HeckeOne.not_isNormPow_of_not_unrAt hram0) hΛ (by simpa using (by exact_mod_cast hs1 : (1 : ℝ) ≤ s))`.

Establish `hz0 : z ≠ 0`. Introduce and unpack `rfl`. Conclude with `hΛs (by rw [← hz, map_zero, zero_mul])`. Establish `hbeta : beta D.host.E D.host.d s (kap D sc.cGap i j s) Λl (Λ s) = D.what₂.embLL (z ^ 12) * beta D.host.E D.host.d s (kap D sc.cGap i j s) Λl x`. Rewrite using `[← hz, ← e0, beta, beta, map_pow]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hβ0 : beta D.host.E D.host.d s (kap D sc.cGap i j s) Λl x ≠ 0`. Rewrite using `[beta]`. Use `div_ne_zero (pow_ne_zero _ (mul_ne_zero ?_ hx0)) (pow_ne_zero _ (latDisc_ne_zero Λl))` and prove the remaining obligations. Conclude with `(cmValueConst_pos D.host.E (hfd.1.pos) (by omega) _).ne'` after adjusting the coercions.

Rewrite `hInt` using `[hbeta, pow_one, zpow_natCast]`. Establish `key` using `meanVal_lower D.what₂.embLL hp hβ0 (pow_ne_zero 12 hz0) hl hlw hInt`. Rewrite `key` using `[vw_pow w hz0]`. Establish `h2 : ((-(N * vw w (l : D.what₂.LL)) : ℤ) : ℝ) ≤ (vw w z : ℝ) + meanVal_vw w p / 12`. Move the coercions through the operations in `at key ⊢`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `h3` using `GlobalTheory.FunObj.SqNum.le_add_truncZero h2`. Rewrite using `[hnl, hg w]`. Establish `h4 : ((-(N * vw w (l : D.what₂.LL)) : ℤ) : ℝ) ≤ ((vw w z + GlobalTheory.LeafRestExamples.truncZero (meanVal_vw w p / 12) : ℤ) : ℝ)`. Conclude with `h3` after adjusting the coercions.

Move the coercions through the operations in `at h4 ⊢`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem core (hTD : GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ToricDenominator) {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} {μ₀ : T}
    (hL : Lc.Is μ₀) (G : GridData Lc sc) (hcm : IsCMField D.host.E) (hab : IsAbelianGalois ℚ D.host.E)
    (hfd : GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData D.host.d (cmPhi D)) (hbc : IsBaseCond (condF G.pl))
    (i j : Fin D.R.m) (s : ℕ) (hs1 : 1 ≤ s) (hs2 : s ≤ halfRank D i j)
    (t : T) (Λ Λ₀ : ℂ → ℂ) (z : D.what₂.LL) (zd : Bool → D.what₂.LL) (g : Formalism.PairingDivisionLocalBalance.Pl D.what₂.LL → ℤ) (n : ℕ → ℝ)
    (hΛ : IsHeckeL (nuH G t i j) Λ) (hΛ₀ : IsHeckeL (nuH G μ₀ i j) Λ₀) (hz : D.what₂.embLL z * Λ₀ s = Λ s)
    (htv : IsTorVal G μ₀ i j s zd g) (hden : IsDenom G i j s n)
    (w : Formalism.PairingDivisionLocalBalance.Pl D.what₂.LL) (l : ℕ) (hl : l.Prime) (hlw : (l : 𝓞 D.what₂.LL) ∈ w.asIdeal)
    (hQw : (GlobalTheory.SqTop.Qn G t : 𝓞 D.what₂.LL) ∉ w.asIdeal) :
    -(n l * (vw w (l : D.what₂.LL) : ℝ)) ≤ ((vw w z + g w : ℤ) : ℝ) := by
  haveI := hcm
  haveI := hab
  obtain ⟨x, hx, hx0, -, Λl, p, hΛl, hp, hg⟩ := htv
  have hU : UnramFin D.host.E := hfd.2.2.1
  have hφ : IsCMType (cmPhi D) := hfd.2.2.2.2.2.2.1

  have e0 : x = Λ₀ s := by
    have h := GlobalTheory.ToricSumValue.toricSum_eq GlobalTheory.Published.HeckeEntire_holds D.host.E D.what₂.Tau (cmPhi D) hφ s
      (kap D sc.cGap i j s) (condF G.pl) ∅ (nuH G μ₀ i j) (fun _ => G.pl.w G.pl.v0) Λ₀ hU hs1 hbc
      (fun q hq => absurd hq (Finset.notMem_empty q)) hx.1 (fun q hq => absurd hq (Finset.notMem_empty q)) hΛ₀
    simp only [condQ, Finset.prod_empty, mul_one, Finset.filter_empty] at h
    exact hx.2.unique h

  obtain ⟨Q, hQdef⟩ : ∃ Q : Finset (HeightOneSpectrum (OF D.host.E)),
      Q = (GlobalTheory.SqTop.twPl G t).image fun P => P.under (𝓞 D.host.F) := ⟨_, rfl⟩
  have hQval := twist_val G hL t i j hs2
  have hQaux := squareTopTwistPlaces_coprime_splitPlaces G hL t
  have hQram := twist_ram G hL t i j
  have hQpr := twist_prime G t hl hlw hQw
  rw [← hQdef] at hQval hQaux hQpr
  have hex : ∀ q ∈ Q, ∃ P ∈ GlobalTheory.SqTop.twPl G t, P.under (𝓞 D.host.F) = q := fun q hq => by
    rw [hQdef] at hq
    exact Finset.mem_image.1 hq
  let Pq : HeightOneSpectrum (OF D.host.E) → HeightOneSpectrum (𝓞 D.host.E) := fun q =>
    if h : ∃ P ∈ GlobalTheory.SqTop.twPl G t, P.under (𝓞 D.host.F) = q then h.choose else G.pl.w G.pl.v0
  have hPq : ∀ q ∈ Q, Pq q ∈ GlobalTheory.SqTop.twPl G t ∧ (Pq q).under (𝓞 D.host.F) = q := fun q hq => by
    have h := hex q hq
    simp only [Pq, dif_pos h]
    exact h.choose_spec
  have hov : ∀ q ∈ Q, Over (Pq q) q := fun q hq =>
    (over_under (Pq q)).trans (congrArg HeightOneSpectrum.asIdeal (hPq q hq).2)
  have htor := GlobalTheory.ToricSumValue.toricSum_eq GlobalTheory.Published.HeckeEntire_holds D.host.E D.what₂.Tau (cmPhi D) hφ s
    (kap D sc.cGap i j s) (condF G.pl) Q (nuH G t i j) Pq Λ hU hs1 hbc hQaux hQval
    hov hΛ
  rw [Finset.filter_false_of_mem (fun q hq => hQram _ (hPq q hq).1), Finset.prod_empty, mul_one] at htor

  have hnu : nuH G t i j = nuH G μ₀ i j * Lc.xiH t := by
    rw [nuH, nuH, hL.xi_base, mul_one, div_mul_eq_mul_div]
  have hpic : GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsPicChar (condQ (condF G.pl) Q) (Lc.xiH t) := by
    obtain ⟨k, hk, hko⟩ := hL.xi_fin t
    refine ⟨fun y => GlobalTheory.TypeValues.inf_eq_one _ hk hko y, fun u hu => ?_⟩
    have a := GlobalTheory.CMVal.OrderUnits.finPart_eq_one D.host.E D.what₂.Tau (cmPhi D) hφ s (kap D sc.cGap i j s)
      (condF G.pl) Q (nuH G t i j) hU hbc hQaux hQval u hu
    have hle : condQ (condF G.pl) Q ≤ condQ (condF G.pl) ∅ := by
      simp only [condQ, Finset.prod_empty, mul_one]
      exact Ideal.mul_le_left
    have b := GlobalTheory.CMVal.OrderUnits.finPart_eq_one D.host.E D.what₂.Tau (cmPhi D) hφ s (kap D sc.cGap i j s)
      (condF G.pl) ∅ (nuH G μ₀ i j) hU hbc (fun q hq => absurd hq (Finset.notMem_empty q)) hx.1 u
      (hatOUnits_mono hle hu)
    rw [hnu, finPart_mul, b, one_mul] at a
    exact a

  obtain ⟨zc, hzc, H⟩ := hTD D.host.E D.what₂.Tau D.host.d (cmPhi D) s hfd hs1
  have hV := ((H (kap D sc.cGap i j s) (condF G.pl) Λl (nuH G μ₀ i j) hbc hΛl hx.1) l hl Q hQaux hQpr).2
    (Lc.xiH t) (Λ s) hpic (hnu ▸ htor)
  obtain ⟨zc', hzc', hn⟩ := hden
  obtain rfl : zc = zc' := classZetaVals_unique (by omega) hzc hzc'
  set B := GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.betaBound_vp D.host.d s (kap D sc.cGap i j s) (condF G.pl) zc l with hB
  set N := ⌈B / 12⌉₊ with hN
  have hnl : n l = N := by rw [hn l hl]
  have hInt := hV (12 * N : ℕ) 1 one_pos (by
    push_cast
    have := Nat.le_ceil (B / 12)
    linarith)

  have hv0 : G.pl.v0 ∉ Q := fun h => by
    obtain ⟨P, hP, e⟩ := hex _ h
    have hP' : P ∈ Lc.Q t := by
      simp only [GlobalTheory.SqTop.twPl, Finset.mem_filter, locPl, Finset.mem_union] at hP
      exact hP.1.resolve_left hP.2
    exact G.pl.levelPlace_ne_basePlace t P hP' e
  have hram0 : ¬ (nuH G t i j).UnrAt (G.pl.w G.pl.v0) := by
    have h1 := (hQval.2.2.2 G.pl.v0 (G.pl.w G.pl.v0) ((over_under _).trans (congrArg HeightOneSpectrum.asIdeal (G.pl.w_over _ (Finset.mem_insert_self _ _))))).2 hv0
    rw [GlobalTheory.FunObj.SqNum.Model.expIn_condF, if_pos (G.pl.mem_S0_of_sum_eq.2 (Or.inl rfl)), condExp, if_pos rfl] at h1
    exact h1.not_unrAt one_ne_zero
  have hΛs : Λ s ≠ 0 := GlobalTheory.HeckePartial.IsHeckeL.ne_zero_of_one_le hQval.1
    (GlobalTheory.HeckeOne.not_isNormPow_of_not_unrAt hram0) hΛ (by simpa using (by exact_mod_cast hs1 : (1 : ℝ) ≤ s))
  have hz0 : z ≠ 0 := by
    rintro rfl
    exact hΛs (by rw [← hz, map_zero, zero_mul])

  have hbeta : beta D.host.E D.host.d s (kap D sc.cGap i j s) Λl (Λ s) =
      D.what₂.embLL (z ^ 12) * beta D.host.E D.host.d s (kap D sc.cGap i j s) Λl x := by
    rw [← hz, ← e0, beta, beta, map_pow]
    ring
  have hβ0 : beta D.host.E D.host.d s (kap D sc.cGap i j s) Λl x ≠ 0 := by
    rw [beta]
    refine div_ne_zero (pow_ne_zero _ (mul_ne_zero ?_ hx0)) (pow_ne_zero _ (latDisc_ne_zero Λl))
    exact_mod_cast (cmValueConst_pos D.host.E (hfd.1.pos) (by omega) _).ne'
  rw [hbeta, pow_one, zpow_natCast] at hInt
  have key := meanVal_lower D.what₂.embLL hp hβ0 (pow_ne_zero 12 hz0) hl hlw hInt
  rw [vw_pow w hz0] at key
  have h2 : ((-(N * vw w (l : D.what₂.LL)) : ℤ) : ℝ) ≤ (vw w z : ℝ) + meanVal_vw w p / 12 := by
    push_cast at key ⊢
    linarith
  have h3 := GlobalTheory.FunObj.SqNum.le_add_truncZero h2
  rw [hnl, hg w]
  have h4 : ((-(N * vw w (l : D.what₂.LL)) : ℤ) : ℝ) ≤ ((vw w z + GlobalTheory.LeafRestExamples.truncZero (meanVal_vw w p / 12) : ℤ) : ℝ) := by
    exact_mod_cast h3
  push_cast at h4 ⊢
  linarith

/- English proof (translation)
Introduce `hTD hF _`. Take `⟨CF0, hF⟩` from `hF`. Use `⟨CF0, fun ε CF hCF => ?_⟩` and prove the remaining obligations. Take `⟨C0, x₀, hF⟩` from `hF ε CF hCF`. Use `⟨C0, x₀, fun C hC D large₂ he hx hR T Lc μ₀ hL G => ?_⟩` and prove the remaining obligations.

Take `⟨hcm, hab, hfd, hbc, -⟩` from `hF C hC D large₂ he hx hR T Lc μ₀ hL G`. Introduce `i j s hs1 hs2 t Λ Λ₀ z zd g n hΛ hΛ₀ hz htv hden w l hl hlw hQw`. Conclude with `core hTD hL G hcm hab hfd hbc i j s hs1 hs2 t Λ Λ₀ z zd g n hΛ hΛ₀ hz htv hden w l hl hlw hQw`.
-/
theorem rhoLow_holds : GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ToricDenominator → GlobalTheory.SqTop.FieldDat → GlobalTheory.SqTop.TorEx → GlobalTheory.SqTop.RhoLow := by
  intro hTD hF _
  obtain ⟨CF0, hF⟩ := hF
  refine ⟨CF0, fun ε CF hCF => ?_⟩
  obtain ⟨C0, x₀, hF⟩ := hF ε CF hCF
  refine ⟨C0, x₀, fun C hC D large₂ he hx hR T Lc μ₀ hL G => ?_⟩
  obtain ⟨hcm, hab, hfd, hbc, -⟩ := hF C hC D large₂ he hx hR T Lc μ₀ hL G
  intro i j s hs1 hs2 t Λ Λ₀ z zd g n hΛ hΛ₀ hz htv hden w l hl hlw hQw
  exact core hTD hL G hcm hab hfd hbc i j s hs1 hs2 t Λ Λ₀ z zd g n hΛ hΛ₀ hz htv hden w l hl hlw hQw

end GlobalTheory.RhoLowProof

end
