import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsGaloisConjugatesHeckeCharTrivialOnRealIdel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPrimeNotDvdRelIndexSplitPlace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaChainStepVectorLocalPureTensor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPartConjMem
import Formalism.LocalToGlobal.Columns.DecoFin
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.HeckeDetChar

open Formalism.L2.JoinChr
open Formalism.L2.NTheta (IsIdemAt)

variable {D : D7}

/- English proof (translation)
Use `HeightOneSpectrum.ext (Ideal.ext fun x => ?_)` and prove the remaining obligations. Distinguish the cases in `hx : x = 0`. Rewrite using `[hx]`. Conclude with `iff_of_true (zero_mem _) (zero_mem _)`. Rewrite using `[h.2 x hx, h'.2 x hx]`.
-/
theorem place_eq {e : AE D} {P P' : Pl D.host.E} (h : IsIdemAt e P) (h' : IsIdemAt e P') : P = P' := by
  refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
  by_cases hx : x = 0
  · rw [hx]; exact iff_of_true (zero_mem _) (zero_mem _)
  · rw [h.2 x hx, h'.2 x hx]

/- English proof (translation)
Assume the negation of the conclusion as `hc`. Use `(he.2 1 one_ne_zero).2 (by` as an intermediate fact. Rewrite using `[show ((1 : 𝓞 D.host.E) : D.host.E) = 1 from rfl, inv_one, RingHom.map_one, mul_one])` and apply the resulting hypothesis. Conclude with `P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 this)`.
-/
theorem finPart_mem {e : AE D} {P : Pl D.host.E} (he : IsIdemAt e P) : finPart D e ∈ intAE D := by
  by_contra hc
  have := (he.2 1 one_ne_zero).2 (by
    rwa [show ((1 : 𝓞 D.host.E) : D.host.E) = 1 from rfl, inv_one, RingHom.map_one, mul_one])
  exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 this)

/- English proof (translation)
Take `⟨n, d, h⟩` from `P.exists_primeCompl_mul_eq_of_integer x hx`. Establish `hd : (d : 𝓞 D.host.E) ∉ P.asIdeal` using `d.2`. Establish `hd0 : (d : 𝓞 D.host.E) ≠ 0` using `fun h0 => hd (h0 ▸ zero_mem _)`. Establish `hdE : ((d : 𝓞 D.host.E) : D.host.E) ≠ 0`. Introduce `h0`.

Apply `hd0` to reduce the goal to its premises. Conclude with `RingOfIntegers.ext h0`. Establish `hxe : x = (n : D.host.E) * ((d : 𝓞 D.host.E) : D.host.E)⁻¹`. Rewrite using `[eq_mul_inv_iff_mul_eq₀ hdE]`. Conclude with `h`.

Establish `h1 : finPart D (e * incA D (((d : 𝓞 D.host.E) : D.host.E)⁻¹)) ∈ intAE D` using `not_not.1 (mt (he.2 _ hd0).2 hd)`. Rewrite using `[hxe, RingHom.map_mul (incA D), show e * (incA D (n : D.host.E) * incA D (((d : 𝓞 D.host.E) : D.host.E)⁻¹)) = incA D (n : D.host.E) * (e * incA D (((d : 𝓞 D.host.E) : D.host.E)⁻¹)) by ring, RingHom.map_mul (finPart D)]`. Conclude with `GlobalTheory.HeckeConj.mul_mem_intAE D (GlobalTheory.SplitIndex.finPart_incA_mem n) h1`.
-/
theorem finPart_mul_incA_mem {e : AE D} {P : Pl D.host.E} (he : IsIdemAt e P) {x : D.host.E}
    (hx : P.valuation D.host.E x ≤ 1) : finPart D (e * incA D x) ∈ intAE D := by
  obtain ⟨n, d, h⟩ := P.exists_primeCompl_mul_eq_of_integer x hx
  have hd : (d : 𝓞 D.host.E) ∉ P.asIdeal := d.2
  have hd0 : (d : 𝓞 D.host.E) ≠ 0 := fun h0 => hd (h0 ▸ zero_mem _)
  have hdE : ((d : 𝓞 D.host.E) : D.host.E) ≠ 0 := by
    intro h0; apply hd0; exact RingOfIntegers.ext h0
  have hxe : x = (n : D.host.E) * ((d : 𝓞 D.host.E) : D.host.E)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq₀ hdE]; exact h
  have h1 : finPart D (e * incA D (((d : 𝓞 D.host.E) : D.host.E)⁻¹)) ∈ intAE D :=
    not_not.1 (mt (he.2 _ hd0).2 hd)
  rw [hxe, RingHom.map_mul (incA D), show e * (incA D (n : D.host.E) * incA D (((d : 𝓞 D.host.E) : D.host.E)⁻¹)) =
    incA D (n : D.host.E) * (e * incA D (((d : 𝓞 D.host.E) : D.host.E)⁻¹)) by ring, RingHom.map_mul (finPart D)]
  exact GlobalTheory.HeckeConj.mul_mem_intAE D (GlobalTheory.SplitIndex.finPart_incA_mem n) h1

/- English proof (translation)
Establish `hc : IsIdemAt (cA D e) (conjPl P)` using `GlobalTheory.MovedIdem.isIdemAt_conj he fun _ => Iff.rfl`. Rewrite using `[idem, map_sum, ← Finset.sum_add_distrib, Finset.sum_mul]`. Use `Finset.sum_eq_zero fun Q' hQ' => ?_` and prove the remaining obligations. Establish `he'` using `hS.isIdemAt hQ'`. Rewrite using `[add_mul]`.

Establish `a1 : idemAt Q' * e = 0`. Break down `GlobalTheory.PlaceModelSum.eq_or_mul_eq_zero he'.1 he.1 with h | h` into its components or cases. Rewrite `he'` using `[h]`. Conclude with `absurd (place_eq he he' ▸ hQ' : P ∈ (Q : Set (Pl D.host.E))) hoff.2.1`. Conclude with `h`.

Establish `a2 : cA D (idemAt Q') * e = 0`. Break down `GlobalTheory.PlaceModelSum.eq_or_mul_eq_zero he'.1 hc.1 with h | h` into its components or cases. Rewrite `he'` using `[h]`. Establish `hPQ` using `place_eq hc he'`. Use `absurd ?_ (hoff.2.2 Q' hQ')` and prove the remaining obligations.

Rewrite using `[← hPQ]`. Use extensionality with `x`. Rewrite using `[Formalism.L2.Col.mem_conjIdeal]`. Both sides reduce to the same expression. Use `congrArg (cA D) h` as an intermediate fact.

Rewrite `this` using `[map_mul, GlobalTheory.MovedIdem.cA_cA, map_zero]`. Then use the resulting hypothesis. Rewrite using `[a1, a2, add_zero]`.
-/
theorem idem_mul_eq_zero {Q : Finset (Pl D.host.E)} (hS : SplitSet Q) {P : Pl D.host.E}
    (hoff : Bridge.SplitOff P (Q : Set (Pl D.host.E))) {e : AE D} (he : IsIdemAt e P) :
    (idem Q + cA D (idem Q)) * e = 0 := by
  have hc : IsIdemAt (cA D e) (conjPl P) := GlobalTheory.MovedIdem.isIdemAt_conj he fun _ => Iff.rfl
  rw [idem, map_sum, ← Finset.sum_add_distrib, Finset.sum_mul]
  refine Finset.sum_eq_zero fun Q' hQ' => ?_
  have he' := hS.isIdemAt hQ'
  rw [add_mul]
  have a1 : idemAt Q' * e = 0 := by
    rcases GlobalTheory.PlaceModelSum.eq_or_mul_eq_zero he'.1 he.1 with h | h
    · rw [h] at he'
      exact absurd (place_eq he he' ▸ hQ' : P ∈ (Q : Set (Pl D.host.E))) hoff.2.1
    · exact h
  have a2 : cA D (idemAt Q') * e = 0 := by
    rcases GlobalTheory.PlaceModelSum.eq_or_mul_eq_zero he'.1 hc.1 with h | h
    · rw [h] at he'
      have hPQ := place_eq hc he'
      refine absurd ?_ (hoff.2.2 Q' hQ')
      rw [← hPQ]
      ext x
      rw [Formalism.L2.Col.mem_conjIdeal]
      rfl
    · have := congrArg (cA D) h
      rwa [map_mul, GlobalTheory.MovedIdem.cA_cA, map_zero] at this
  rw [a1, a2, add_zero]

/- English proof (translation)
Establish `key : ∀ w : AE D, finPart D (e * w) ∈ intAE D → finPart D (1 + e * (w - 1)) ∈ intAE D` using `fun w hw => by`. Rewrite using `[show 1 + e * (w - 1) = 1 - e + e * w by ring, RingHom.map_add, RingHom.map_sub, RingHom.map_one]`. Conclude with `add_mem (sub_mem (GlobalTheory.HeckeConj.one_mem_intAE D) (finPart_mem he)) hw`. Use `hχ x ?_ ?_ ?_ ?_` and prove the remaining obligations. Rewrite using `[hx, RingHom.map_add, RingHom.map_one, RingHom.map_mul, GlobalTheory.StepVec.infPart_idemAt he, zero_mul, add_zero]`.

Rewrite using `[hx]`. Conclude with `key y hy`. Rewrite using `[hx']`. Conclude with `key y' hy'`. Rewrite using `[hx, mul_add, mul_one, ← mul_assoc, hQ, zero_mul, add_zero]`.
-/
theorem chi_eq_one {χ : (AE D)ˣ →* Circle} {Q : Finset (Pl D.host.E)} (hχ : GlobalTheory.ExportSeries.UnramOutside χ Q)
    {e : AE D} {P : Pl D.host.E} (he : IsIdemAt e P) (hQ : (idem Q + cA D (idem Q)) * e = 0) (x : (AE D)ˣ)
    (y y' : AE D) (hx : (x : AE D) = 1 + e * (y - 1)) (hx' : ((x⁻¹ : (AE D)ˣ) : AE D) = 1 + e * (y' - 1))
    (hy : finPart D (e * y) ∈ intAE D) (hy' : finPart D (e * y') ∈ intAE D) : χ x = 1 := by
  have key : ∀ w : AE D, finPart D (e * w) ∈ intAE D → finPart D (1 + e * (w - 1)) ∈ intAE D := fun w hw => by
    rw [show 1 + e * (w - 1) = 1 - e + e * w by ring, RingHom.map_add, RingHom.map_sub, RingHom.map_one]
    exact add_mem (sub_mem (GlobalTheory.HeckeConj.one_mem_intAE D) (finPart_mem he)) hw
  refine hχ x ?_ ?_ ?_ ?_
  · rw [hx, RingHom.map_add, RingHom.map_one, RingHom.map_mul, GlobalTheory.StepVec.infPart_idemAt he, zero_mul, add_zero]
  · rw [hx]; exact key y hy
  · rw [hx']; exact key y' hy'
  · rw [hx, mul_add, mul_one, ← mul_assoc, hQ, zero_mul, add_zero]

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Rewrite using `[pow_succ, ih, pow_succ]`. Take the linear combination `(a ^ k - 1) * (a - 1) * he`.
-/
theorem locE_pow {e : AE D} (he : e * e = e) (a : AE D) (k : ℕ) :
    (1 + e * (a - 1)) ^ k = 1 + e * (a ^ k - 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, pow_succ]
    linear_combination (a ^ k - 1) * (a - 1) * he

/- English proof (translation)
Take `⟨⟨h1, h2, v, ε, hv, hs⟩, h3⟩` from `he`. Conclude with `⟨h1, ⟨v, ε, hv, Or.inl ⟨h2, hs⟩⟩, h3⟩`.
-/
theorem isPlIdem {e : AE D} {P : Pl D.host.E} (he : IsIdemAt e P) : IsPlIdem D e P := by
  obtain ⟨⟨h1, h2, v, ε, hv, hs⟩, h3⟩ := he
  exact ⟨h1, ⟨v, ε, hv, Or.inl ⟨h2, hs⟩⟩, h3⟩

/- English proof (translation)
Establish `hmul : locU he k * locU he k⁻¹ = 1`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Units.val_mul, locU_val, locU_val, locE_mul_locE he, Units.mul_inv, Units.val_one]`. Simplify using `[locE]`. Rewrite using `[inv_eq_of_mul_eq_one_right hmul, locU_val]`.
-/
theorem locU_inv {e : AE D} (he : e * e = e) (k : D.host.Eˣ) :
    (((locU he k)⁻¹ : (AE D)ˣ) : AE D) = locE D e ((k⁻¹ : D.host.Eˣ) : D.host.E) := by
  have hmul : locU he k * locU he k⁻¹ = 1 := by
    apply Units.ext
    rw [Units.val_mul, locU_val, locU_val, locE_mul_locE he, Units.mul_inv, Units.val_one]
    simp [locE]
  rw [inv_eq_of_mul_eq_one_right hmul, locU_val]

/- English proof (translation)
Establish `hϖ0 : ϖ ≠ 0` using `by rintro rfl; exact hP2 (zero_mem _)`. Rewrite using `[show (ϖ : D.host.E) = algebraMap (𝓞 D.host.E) D.host.E ϖ from rfl, P.valuation_of_algebraMap]`. Establish `a1` using `(P.intValuation_lt_one_iff_mem ϖ).2 hP`. Establish `a2` using `(P.intValuation_le_pow_iff_mem ϖ 2).not.2 hP2`. Rewrite `a1`, `a2`, the goal using `[P.intValuation_eq_exp_neg_multiplicity hϖ0]`.

Rewrite `a1` using `[← WithZero.exp_zero, WithZero.exp_lt_exp]`. Rewrite `a2` using `[WithZero.exp_le_exp]`. Use `congr 1`. Move the coercions through the operations in `at a2`. Use linear arithmetic over natural numbers and integers.
-/
theorem val_unif {P : Pl D.host.E} {ϖ : 𝓞 D.host.E} (hP : ϖ ∈ P.asIdeal) (hP2 : ϖ ∉ P.asIdeal ^ 2) :
    P.valuation D.host.E (ϖ : D.host.E) = WithZero.exp (-1 : ℤ) := by
  have hϖ0 : ϖ ≠ 0 := by rintro rfl; exact hP2 (zero_mem _)
  rw [show (ϖ : D.host.E) = algebraMap (𝓞 D.host.E) D.host.E ϖ from rfl, P.valuation_of_algebraMap]
  have a1 := (P.intValuation_lt_one_iff_mem ϖ).2 hP
  have a2 := (P.intValuation_le_pow_iff_mem ϖ 2).not.2 hP2
  rw [P.intValuation_eq_exp_neg_multiplicity hϖ0] at a1 a2 ⊢
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at a1
  rw [WithZero.exp_le_exp] at a2
  congr 1
  push_cast at a2
  omega

/- English proof (translation)
Introduce `D χ c hχc Q hU hS P hoff V k α hα z hz`. Take `⟨e, ϖ, he, hϖP, hϖP2, hH⟩` from `hα`. Rewrite `hz` using `[idemAt_eq he]`. Take `⟨-, -, -, -, u, u', hu, hu', huu, hdet⟩` from `hH`. Establish `hQe` using `idem_mul_eq_zero hS hoff he`.

Establish `hee : e * e = e` using `he.1.1`. Establish `hv` using `val_unif hϖP hϖP2`. Establish `hϖ0 : (ϖ : D.host.E) ≠ 0`. Introduce `h0`. Rewrite `hv` using `[h0, map_zero]`.

Conclude with `WithZero.exp_ne_zero hv.symm`. Use `set ϖU : D.host.Eˣ := Units.mk0 (ϖ : D.host.E) hϖ0 with hϖU`. Set `wU : (AE D)ˣ` to `⟨1 + e * (u - 1), 1 + e * (u' - 1), by linear_combination (u - 1) * (u' - 1) * hee + huu, by linear_combination (u - 1) * (u' - 1) * hee + huu⟩`. Establish `hw : χ wU = 1` using `chi_eq_one hU he hQe wU u u' rfl rfl (by rw [RingHom.map_mul]; exact GlobalTheory.HeckeConj.mul_mem_intAE D (finPart_mem he) hu) (by rw [RingHom.map_mul]; exact GlobalTheory.HeckeConj.mul_mem_intAE D (finPart_mem he) hu')`. Establish `hz' : z = locU hee ϖU ^ k * wU`.

Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Units.val_mul, Units.val_pow_eq_pow_val, locU_val, locE, locE_pow hee, hz]`. Use `show e * (mt V α).det + (1 - e) = (1 + e * (incA D (ϖ : D.host.E) ^ k - 1)) * (1 + e * (u - 1))`. Take the linear combination `hdet - (incA D (ϖ : D.host.E) ^ k - 1) * (u - 1) * hee`. Establish `h1 : ((χ (locU hee ϖU) : Circle) : ℂ) = ((c.locK P ϖU : ℂˣ) : ℂ)` using `hχc.2 P e (isPlIdem he) ϖU _ (locU_val hee ϖU)`.

Use `set rU : D.host.Eˣ := ϖU * (Formalism.L2.Host.unif P)⁻¹ with hrU`. Establish `hvπ : P.valuation D.host.E ((Formalism.L2.Host.unif P : D.host.Eˣ) : D.host.E) = WithZero.exp (-1 : ℤ)`. Use `Formalism.L2.Host.unif_spec P` as an intermediate fact. Unfold `Formalism.L2.Host.IsUnifAt at this`. Rewrite using `[← this]`.

Use `show _ = Valued.v (algebraMap D.host.E (P.adicCompletion D.host.E) _)`. Conclude with `(HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P _).symm`. Establish `hvr : P.valuation D.host.E (rU : D.host.E) = 1`. Rewrite using `[hrU, Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, hvπ, hϖU, Units.val_mk0, hv]`. Conclude with `mul_inv_cancel₀ (WithZero.exp_ne_zero)`.

Establish `hr1 : χ (locU hee rU) = 1`. Use `chi_eq_one hU he hQe _ (incA D (rU : D.host.E)) (incA D ((rU⁻¹ : D.host.Eˣ) : D.host.E)) rfl (locU_inv hee rU) (finPart_mul_incA_mem he hvr.le) (finPart_mul_incA_mem he ?_)` and prove the remaining obligations. Rewrite using `[Units.val_inv_eq_inv_val, map_inv₀, hvr, inv_one]`. Establish `hr2 : ((χ (locU hee rU) : Circle) : ℂ) = ((c.locK P rU : ℂˣ) : ℂ)` using `hχc.2 P e (isPlIdem he) rU _ (locU_val hee rU)`. Rewrite `hr2` using `[hr1]`.

Establish `hval : ((c.locK P ϖU : ℂˣ) : ℂ) = ((c.val P : ℂˣ) : ℂ)`. Establish `: ϖU = rU * Formalism.L2.Host.unif P` using `by rw [hrU, inv_mul_cancel_right]`. Rewrite using `[this, map_mul, Units.val_mul, ← hr2, Formalism.L2.Host.HChar.val]`. Simplify using the standard rewrite rules. Rewrite using `[hz', map_mul, map_pow, hw, mul_one, Circle.coe_pow, h1, hval]`.
-/
theorem chi_detAt : ∀ {D : D7} {χ : (AE D)ˣ →* Circle} {c : Formalism.L2.Host.HChar D.host.E}, ChrEq χ c →
    ∀ {Q : Finset (Pl D.host.E)}, GlobalTheory.ExportSeries.UnramOutside χ Q → GlobalTheory.ExportSeries.SplitSet Q → ∀ {P : Pl D.host.E},
    Bridge.SplitOff P (Q : Set (Pl D.host.E)) → ∀ {V : HSp D} {k : ℕ} {α : GA D V}, IsHeckeAt V P k α →
    ∀ {z : (AE D)ˣ}, IsDetAt (idemAt P) V α z → ((χ z : Circle) : ℂ) = ((c.val P : ℂˣ) : ℂ) ^ k := by
  intro D χ c hχc Q hU hS P hoff V k α hα z hz
  obtain ⟨e, ϖ, he, hϖP, hϖP2, hH⟩ := hα
  rw [idemAt_eq he] at hz
  obtain ⟨-, -, -, -, u, u', hu, hu', huu, hdet⟩ := hH
  have hQe := idem_mul_eq_zero hS hoff he
  have hee : e * e = e := he.1.1
  have hv := val_unif hϖP hϖP2
  have hϖ0 : (ϖ : D.host.E) ≠ 0 := by
    intro h0; rw [h0, map_zero] at hv; exact WithZero.exp_ne_zero hv.symm
  set ϖU : D.host.Eˣ := Units.mk0 (ϖ : D.host.E) hϖ0 with hϖU

  let wU : (AE D)ˣ := ⟨1 + e * (u - 1), 1 + e * (u' - 1),
    by linear_combination (u - 1) * (u' - 1) * hee + huu,
    by linear_combination (u - 1) * (u' - 1) * hee + huu⟩
  have hw : χ wU = 1 := chi_eq_one hU he hQe wU u u' rfl rfl
    (by rw [RingHom.map_mul]; exact GlobalTheory.HeckeConj.mul_mem_intAE D (finPart_mem he) hu)
    (by rw [RingHom.map_mul]; exact GlobalTheory.HeckeConj.mul_mem_intAE D (finPart_mem he) hu')

  have hz' : z = locU hee ϖU ^ k * wU := by
    apply Units.ext
    rw [Units.val_mul, Units.val_pow_eq_pow_val, locU_val, locE, locE_pow hee, hz]
    show e * (mt V α).det + (1 - e) = (1 + e * (incA D (ϖ : D.host.E) ^ k - 1)) * (1 + e * (u - 1))
    linear_combination hdet - (incA D (ϖ : D.host.E) ^ k - 1) * (u - 1) * hee

  have h1 : ((χ (locU hee ϖU) : Circle) : ℂ) = ((c.locK P ϖU : ℂˣ) : ℂ) :=
    hχc.2 P e (isPlIdem he) ϖU _ (locU_val hee ϖU)

  set rU : D.host.Eˣ := ϖU * (Formalism.L2.Host.unif P)⁻¹ with hrU
  have hvπ : P.valuation D.host.E ((Formalism.L2.Host.unif P : D.host.Eˣ) : D.host.E) = WithZero.exp (-1 : ℤ) := by
    have := Formalism.L2.Host.unif_spec P
    unfold Formalism.L2.Host.IsUnifAt at this
    rw [← this]
    show _ = Valued.v (algebraMap D.host.E (P.adicCompletion D.host.E) _)
    exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P _).symm
  have hvr : P.valuation D.host.E (rU : D.host.E) = 1 := by
    rw [hrU, Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, hvπ, hϖU, Units.val_mk0, hv]
    exact mul_inv_cancel₀ (WithZero.exp_ne_zero)
  have hr1 : χ (locU hee rU) = 1 := by
    refine chi_eq_one hU he hQe _ (incA D (rU : D.host.E)) (incA D ((rU⁻¹ : D.host.Eˣ) : D.host.E)) rfl
      (locU_inv hee rU) (finPart_mul_incA_mem he hvr.le) (finPart_mul_incA_mem he ?_)
    rw [Units.val_inv_eq_inv_val, map_inv₀, hvr, inv_one]
  have hr2 : ((χ (locU hee rU) : Circle) : ℂ) = ((c.locK P rU : ℂˣ) : ℂ) :=
    hχc.2 P e (isPlIdem he) rU _ (locU_val hee rU)
  rw [hr1] at hr2
  have hval : ((c.locK P ϖU : ℂˣ) : ℂ) = ((c.val P : ℂˣ) : ℂ) := by
    have : ϖU = rU * Formalism.L2.Host.unif P := by rw [hrU, inv_mul_cancel_right]
    rw [this, map_mul, Units.val_mul, ← hr2, Formalism.L2.Host.HChar.val]
    simp
  rw [hz', map_mul, map_pow, hw, mul_one, Circle.coe_pow, h1, hval]

end GlobalTheory.HeckeDetChar
