import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpBinomialPowerSubOneSeriesIntegralityCompositio
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpSeriesCoeffNormBoundedRingLaws
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpTransportedTaylorSeriesInChartRingHomLaws
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpTransportedTaylorSeriesMultiplicativeChart
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpTransportedTaylorSeriesTranslateNormLeStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpSeriesCoeffBoundedTaylorEllipticOfPolesStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SmallTorsionKilledByPrimePowersStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ScaledThetaTranslationQuotientEllipticStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CmEvenThetaSeriesChartCoeffIntegralStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpSeriesBoundedOneTorsionTranslateCmThetaStatement

noncomputable section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne.TranslNorm

/- English proof (translation)
Assemble the required witnesses or components as `⟨0, 0, by simp⟩`.
-/
lemma inOK_zero (d : ℕ) : InOK d 0 := ⟨0, 0, by simp⟩

/- English proof (translation)
Take `⟨u, v, rfl⟩` from `h`. Conclude with `⟨n * u, n * v, by push_cast; ring⟩`.
-/
lemma inOK_natMul {d : ℕ} {z : ℂ} (n : ℕ) (h : InOK d z) : InOK d ((n : ℂ) * z) := by
  obtain ⟨u, v, rfl⟩ := h
  exact ⟨n * u, n * v, by push_cast; ring⟩

/- English proof (translation)
Introduce and unpack `⟨u, v, h⟩`. Establish `hs : 0 < Real.sqrt d` using `Real.sqrt_pos.mpr (by exact_mod_cast hd)`. Establish `him` using `congrArg Complex.im h`. Establish `hre` using `congrArg Complex.re h`. Simplify using `[wK] at him hre`.

Establish `hv : v = 0`. Break down `him with h | h` into its components or cases. Conclude with `h`. It suffices to derive a contradiction. Apply the tactic sequence `first | exact hs.ne' h | omega`.

Substitute `hv` using the available equality. Simplify using `at hre`. Establish `h2 : ((2 * u : ℤ) : ℝ) = ((-1 : ℤ) : ℝ)` using `by push_cast; rw [← hre]; norm_num`. Establish `h3 : 2 * u = -1` using `by exact_mod_cast h2`. Use linear arithmetic over natural numbers and integers.
-/
lemma not_inOK_half {d : ℕ} (hd : 0 < d) : ¬ InOK d (0 - 1 / 2) := by
  rintro ⟨u, v, h⟩
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  simp [wK] at him hre
  have hv : v = 0 := by
    rcases him with h | h
    · exact h
    · exfalso; first | exact hs.ne' h | omega
  subst hv
  simp at hre
  have h2 : ((2 * u : ℤ) : ℝ) = ((-1 : ℤ) : ℝ) := by push_cast; rw [← hre]; norm_num
  have h3 : 2 * u = -1 := by exact_mod_cast h2
  omega

/- English proof (translation)
Use `choose n hn0 hnq hn using hs`. Take `⟨k, hk0, hkq, hk⟩` from `ht`. Use `⟨k * ∏ j, n j, Nat.mul_pos hk0 (Finset.prod_pos fun j _ => hn0 j), Nat.Coprime.mul_left hkq (Nat.Coprime.prod_left fun j _ => hnq j), ?_, fun j => ?_⟩` and prove the remaining obligations. Use `inOK_natMul (∏ j, n j) hk` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Rewrite using `[Nat.cast_mul]`. Expand and normalize the polynomial expressions, which then agree. Use `inOK_natMul (k * ∏ i ∈ Finset.univ.erase j, n i) (hn j)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Rewrite using `[← Finset.mul_prod_erase Finset.univ n (Finset.mem_univ j)]`.

Simplify using `only [Nat.cast_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma exists_common {d q m : ℕ} (s : Fin m → ℂ) (t : ℂ) (hs : ∀ j, PrimeTo d q (s j)) (ht : PrimeTo d q t) :
    ∃ S : ℕ, 0 < S ∧ Nat.Coprime S q ∧ InOK d ((S : ℂ) * t) ∧ ∀ j, InOK d ((S : ℂ) * s j) := by
  classical
  choose n hn0 hnq hn using hs
  obtain ⟨k, hk0, hkq, hk⟩ := ht
  refine ⟨k * ∏ j, n j, Nat.mul_pos hk0 (Finset.prod_pos fun j _ => hn0 j),
    Nat.Coprime.mul_left hkq (Nat.Coprime.prod_left fun j _ => hnq j), ?_, fun j => ?_⟩
  · have := inOK_natMul (∏ j, n j) hk
    convert this using 1
    rw [Nat.cast_mul]; ring
  · have := inOK_natMul (k * ∏ i ∈ Finset.univ.erase j, n i) (hn j)
    convert this using 1
    rw [← Finset.mul_prod_erase Finset.univ n (Finset.mem_univ j)]
    simp only [Nat.cast_mul]; ring

/- English proof (translation)
Unfold `U1 h1`. Use `fun_prop`.
-/
lemma differentiable_U1 (d : ℕ) (x : ℂ) {F : ℂ → ℂ} (hF : Differentiable ℂ F) : Differentiable ℂ (U1 d x F) := by
  unfold U1 h1
  fun_prop

variable {q : ℕ} [Fact q.Prime]

/- English proof (translation)
Proceed by induction on `a with`. Consider the case `zero`. Introduce `n`. Rewrite using `[pow_zero, coeff_one]`. Apply the tactic sequence `split_ifs <;> simp`.

Consider the case `succ a ih`. Use `((GlobalTheory.MomOne.sup_norm_laws q).1 _ _ _ _ ih hf).2` as an intermediate fact. Rewrite `this` using `[one_mul, ← pow_succ]`. Then use the resulting hypothesis.
-/
lemma bd_pow {f : ℂ_[q]⟦X⟧} (hf : Bd 1 f) (a : ℕ) : Bd 1 (f ^ a) := by
  induction a with
  | zero =>
    intro n
    rw [pow_zero, coeff_one]
    split_ifs <;> simp
  | succ a ih =>
    have := ((GlobalTheory.MomOne.sup_norm_laws q).1 _ _ _ _ ih hf).2
    rwa [one_mul, ← pow_succ] at this

/- English proof (translation)
The claim follows from `((GlobalTheory.MomOne.TaylorRead.hat_laws q ι ℓ hl).1 F G hF hG).2.1`.
-/
lemma hat_mul (ι : ℂ ≃+* ℂ_[q]) {ℓ : ℂ_[q]⟦X⟧} (hl : constantCoeff ℓ = 0) {F G : ℂ → ℂ}
    (hF : AnalyticAt ℂ F 0) (hG : AnalyticAt ℂ G 0) :
    hat ι ℓ (fun z => F z * G z) = hat ι ℓ F * hat ι ℓ G :=
  ((GlobalTheory.MomOne.TaylorRead.hat_laws q ι ℓ hl).1 F G hF hG).2.1

/- English proof (translation)
Proceed by induction on `a with`. Consider the case `zero`. Use `(GlobalTheory.MomOne.TaylorRead.hat_laws q ι ℓ hl).2.1 1` as an intermediate fact. Simplify using `using this`. Consider the case `succ a ih`.

Simplify using `only [pow_succ]`. Rewrite using `[hat_mul ι hl (F := fun z => F z ^ a) (by fun_prop) hF, ih]`.
-/
lemma hat_pow (ι : ℂ ≃+* ℂ_[q]) {ℓ : ℂ_[q]⟦X⟧} (hl : constantCoeff ℓ = 0) {F : ℂ → ℂ}
    (hF : AnalyticAt ℂ F 0) (a : ℕ) : hat ι ℓ (fun z => F z ^ a) = hat ι ℓ F ^ a := by
  induction a with
  | zero =>
    have := (GlobalTheory.MomOne.TaylorRead.hat_laws q ι ℓ hl).2.1 1
    simpa using this
  | succ a ih =>
    simp only [pow_succ]
    rw [hat_mul ι hl (F := fun z => F z ^ a) (by fun_prop) hF, ih]

/- English proof (translation)
Proceed by induction on `T using Finset.induction_on with`. Consider the case `empty`. Use `(GlobalTheory.MomOne.TaylorRead.hat_laws q ι ℓ hl).2.1 0` as an intermediate fact. Simplify using `using this`. Consider the case `insert i T hi ih`.

Simplify using `only [Finset.sum_insert hi]`. Establish `hi'` using `hF i`. Establish `h1 : AnalyticAt ℂ (fun z => ι.symm (c i) * F i z ^ a) 0` using `by fun_prop`. Establish `h2 : AnalyticAt ℂ (fun z => ∑ j ∈ T, ι.symm (c j) * F j z ^ a) 0` using `Finset.analyticAt_fun_sum _ fun j _ => by have := hF j; fun_prop`. Rewrite using `[((GlobalTheory.MomOne.TaylorRead.hat_laws q ι ℓ hl).1 _ _ h1 h2).1, ih, hat_mul ι hl (F := fun _ => ι.symm (c i)) (G := fun z => F i z ^ a) analyticAt_const (by fun_prop), hat_pow ι hl hi', (GlobalTheory.MomOne.TaylorRead.hat_laws q ι ℓ hl).2.1]`.

Simplify using the standard rewrite rules.
-/
lemma hat_comb (ι : ℂ ≃+* ℂ_[q]) {ℓ : ℂ_[q]⟦X⟧} (hl : constantCoeff ℓ = 0) {κ : Type} (T : Finset κ)
    (c : κ → ℂ_[q]) (F : κ → ℂ → ℂ) (hF : ∀ j, AnalyticAt ℂ (F j) 0) (a : ℕ) :
    hat ι ℓ (fun z => ∑ j ∈ T, ι.symm (c j) * F j z ^ a) = ∑ j ∈ T, C (c j) * hat ι ℓ (F j) ^ a := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    have := (GlobalTheory.MomOne.TaylorRead.hat_laws q ι ℓ hl).2.1 0
    simpa using this
  | insert i T hi ih =>
    simp only [Finset.sum_insert hi]
    have hi' := hF i
    have h1 : AnalyticAt ℂ (fun z => ι.symm (c i) * F i z ^ a) 0 := by fun_prop
    have h2 : AnalyticAt ℂ (fun z => ∑ j ∈ T, ι.symm (c j) * F j z ^ a) 0 :=
      Finset.analyticAt_fun_sum _ fun j _ => by have := hF j; fun_prop
    rw [((GlobalTheory.MomOne.TaylorRead.hat_laws q ι ℓ hl).1 _ _ h1 h2).1, ih,
      hat_mul ι hl (F := fun _ => ι.symm (c i)) (G := fun z => F i z ^ a) analyticAt_const (by fun_prop),
      hat_pow ι hl hi', (GlobalTheory.MomOne.TaylorRead.hat_laws q ι ℓ hl).2.1]
    simp

/- English proof (translation)
Rewrite using `[(GlobalTheory.MomOne.hat_multiplicative_chart q ι ω G hG).2.2.1 (S : ℂ) (S : ℤ_[q]) (by simp [zc])]`. Use `(GlobalTheory.MomOne.MulSeries.mulS_laws q).2.2.2.1 _ _ _ ?_` and prove the remaining obligations. Conclude with `PadicInt.norm_natCast_eq_one_iff.mpr hS.symm`.
-/
lemma bd_scale_iff (ι : ℂ ≃+* ℂ_[q]) (ω : ℂ_[q]) {S : ℕ} (hS : Nat.Coprime S q) {G : ℂ → ℂ}
    (hG : AnalyticAt ℂ G 0) (B : ℝ) :
    Bd B (hat ι (C ω * logS) (fun z => G ((S : ℂ) * z))) ↔ Bd B (hat ι (C ω * logS) G) := by
  rw [(GlobalTheory.MomOne.hat_multiplicative_chart q ι ω G hG).2.2.1 (S : ℂ) (S : ℤ_[q]) (by simp [zc])]
  refine (GlobalTheory.MomOne.MulSeries.mulS_laws q).2.2.2.1 _ _ _ ?_
  exact PadicInt.norm_natCast_eq_one_iff.mpr hS.symm

/- English proof (translation)
Introduce `d q _ M ω θ hd hd16 hsp hL hM hθ a m c s t B hs ht ht2 hB`. Take `⟨S, hS0, hSq, hSt, hSs⟩` from `exists_common s t hs ht`. Establish `hl : constantCoeff (C ω * logS : ℂ_[q]⟦X⟧) = 0` using `hM.2.1`. Establish `hSne : (S : ℂ) ≠ 0` using `by exact_mod_cast hS0.ne'`. Establish `hθd : Differentiable ℂ θ` using `hθ.1`.

Establish `hθt : θ t ≠ 0` using `fun h => ht2 (hθ.2.2.2.2 t h)`. Establish `hU : ∀ j, Differentiable ℂ (U1 d (s j) θ)` using `fun j => differentiable_U1 d _ hθd`. Establish `hUU : ∀ j, Differentiable ℂ (U1 d t (U1 d (s j) θ))` using `fun j => differentiable_U1 d _ (hU j)`. Establish `hUt : Differentiable ℂ (U1 d t θ)` using `differentiable_U1 d _ hθd`. Establish `E` using `fun j => GlobalTheory.T.scaledThetaTranslationQuotient_elliptic d q M ω θ hd hd16 hsp hL hM hθ (s j) S hS0 hSq (hSs j)`.

Establish `Et` using `(GlobalTheory.T.scaledThetaTranslationQuotient_elliptic d q M ω θ hd hd16 hsp hL hM hθ t S hS0 hSq hSt).2.2.2.1`. Simplify using `only at E`. Use `set t' : ℂ := t / S with ht'`. Establish `hSt' : (S : ℂ) * t' = t` using `by rw [ht']; field_simp`. Use `set φ : ℂ → ℂ := fun z => ∑ j, M.ι.symm (c j) * (U1 d (s j) θ ((S : ℂ) * z) / θ ((S : ℂ) * z)) ^ a with hφ`.

Establish `hφan : ∀ p, θ ((S : ℂ) * p) ≠ 0 → AnalyticAt ℂ φ p` using `fun p hp => Finset.analyticAt_fun_sum _ fun j _ => analyticAt_const.fun_mul (((E j).2.2.1 p hp).fun_pow a)`. Establish `hφper : ∀ l ∈ M.L.lattice, ∀ z, φ (z + l) = φ z` using `fun l hl z => Finset.sum_congr rfl fun j _ => by`. Use `(E j).1.2 l hl z` as an intermediate fact. Simplify using `only at this`. Rewrite using `[this]`.

Establish `hφmer : ∀ p, MeromorphicAt φ p` using `fun p => MeromorphicAt.fun_sum fun j _ => (MeromorphicAt.const _ _).fun_mul (((E j).1.1 p).fun_pow a)`. Establish `h0 : θ ((S : ℂ) * 0) ≠ 0` using `by rw [mul_zero, hθ.2.1]; exact one_ne_zero`. Establish `h0' : θ ((S : ℂ) * t') ≠ 0` using `by rw [hSt']; exact hθt`. Establish `hφ0` using `hφan 0 h0`. Establish `hφt` using `hφan t' h0'`.

Establish `hφt0 : AnalyticAt ℂ (fun z => φ (z + t')) 0` using `AnalyticAt.comp_of_eq hφt (f := fun z => z + t') (by fun_prop) (zero_add _)`. Establish `hθS : AnalyticAt ℂ (fun z => θ ((S : ℂ) * z)) 0` using `(show Differentiable ℂ (fun z => θ ((S : ℂ) * z)) by fun_prop).analyticAt 0`. Establish `hUtS : AnalyticAt ℂ (fun z => U1 d t θ ((S : ℂ) * z)) 0` using `(show Differentiable ℂ (fun z => U1 d t θ ((S : ℂ) * z)) by fun_prop).analyticAt 0`. Establish `hBφ : Bd B (hat M.ι (C ω * logS) φ)`. Establish `hG : Differentiable ℂ (fun z => ∑ j, M.ι.symm (c j) * U1 d (s j) θ z ^ a)` using `by fun_prop`.

Rewrite `hB` using `[← hat_comb M.ι hl _ c _ (fun j => (hU j).analyticAt 0), ← bd_scale_iff M.ι ω hSq (hG.analyticAt 0)]`. Establish `hGS : AnalyticAt ℂ (fun z => ∑ j, M.ι.symm (c j) * U1 d (s j) θ ((S : ℂ) * z) ^ a) 0` using `(show Differentiable ℂ (fun z => ∑ j, M.ι.symm (c j) * U1 d (s j) θ ((S : ℂ) * z) ^ a) by fun_prop).analyticAt 0`. Establish `hpr : AnalyticAt ℂ (fun z => θ ((S : ℂ) * z) ^ a * φ z) 0` using `(hθS.fun_pow a).fun_mul hφ0`. Establish `hev : ∀ᶠ z in 𝓝[≠] (0 : ℂ), (∑ j, M.ι.symm (c j) * U1 d (s j) θ ((S : ℂ) * z) ^ a) = θ ((S : ℂ) * z) ^ a * φ z`. Use `Filter.Eventually.filter_mono nhdsWithin_le_nhds ?_` and prove the remaining obligations.

Use `filter_upwards [hθS.continuousAt.eventually_ne h0] with z hz`. Rewrite using `[hφ, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[div_pow]`. Clear the denominators using the available nonvanishing facts.

Rewrite `hB` using `[((GlobalTheory.MomOne.TaylorRead.hat_laws q M.ι _ hl).1 _ _ hGS hpr).2.2.1 hev, hat_mul M.ι hl (hθS.fun_pow a) hφ0, hat_pow M.ι hl hθS]`. Establish `h1 : Bd 1 (hat M.ι (C ω * logS) (fun z => θ ((S : ℂ) * z)))` using `(bd_scale_iff M.ι ω hSq (hθd.analyticAt 0) 1).mpr (GlobalTheory.T.cm_even_theta_series_chart_coeff_integral d q M ω θ hd hd16 hsp hL hM hθ)`. Use `(GlobalTheory.MomOne.sup_norm_laws q).2.2.2.2.2 _ _ 0 B (bd_pow h1 a) ?_ (by rwa [pow_zero, one_mul])` and prove the remaining obligations. Rewrite using `[map_pow, (GlobalTheory.MomOne.TaylorRead.hat_laws q M.ι _ hl).2.2.2.1]`. Simplify using `[hθ.2.1]`.

Establish `hBφt : Bd B (hat M.ι (C ω * logS) (fun z => φ (z + t')))`. Distinguish the cases in `hsm : M.Small t'`. Establish `hpt : PrimeTo d q t'` using `⟨S * S, Nat.mul_pos hS0 hS0, Nat.Coprime.mul_left hSq hSq, by`. Rewrite using `[Nat.cast_mul, mul_assoc, hSt']`. Conclude with `hSt⟩`.

Establish `hin` using `(hL t').mpr ((GlobalTheory.T.smallTorsion_killed_by_prime_powers d q M ω hd hd16 hsp hL hM).2.2.1 t' hpt hsm)`. Establish `: (fun z => φ (z + t')) = φ` using `funext fun z => hφper t' hin z`. Rewrite using `[this]` and apply the resulting hypothesis. Use `GlobalTheory.T.cpTransportedTaylorSeries_translate_norm_le q M _ φ t' B hM ⟨hφmer, hφper⟩ hφ0 hφt (fun p hp => ?_) hsm ?_ hBφ` and prove the remaining obligations. Use `Et p 0 ⟨1, one_pos, Nat.coprime_one_left q, by simpa using inOK_zero d⟩ (not_inOK_half hd.pos) ?_` and prove the remaining obligations.

Assume the negation of the conclusion as `hne`. Rewrite `hne` using `[add_zero]`. Conclude with `absurd (hφan p hne).meromorphicOrderAt_nonneg (not_le.mpr hp)`. Use `GlobalTheory.T.cpSeriesCoeffBounded_taylor_elliptic_of_poles q M _ _ hM ⟨fun p => ?_, fun l hl z => ?_⟩ hφt0 (fun p hp => ?_)` and prove the remaining obligations. Conclude with `MeromorphicAt.comp_analyticAt (f := φ) (g := fun z => z + t') (hφmer _) (by fun_prop)`.

Use `show φ (z + l + t') = φ (z + t')`. Rewrite using `[add_right_comm, hφper l hl]`. Use `Et p t ht ht2 ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Establish `h2 : AnalyticAt ℂ φ (p + t')` using `hφan _ (by rwa [mul_add, hSt'])`.

Establish `h3 : AnalyticAt ℂ (fun z => φ (z + t')) p` using `AnalyticAt.comp_of_eq h2 (f := fun z => z + t') (by fun_prop) rfl`. Conclude with `absurd h3.meromorphicOrderAt_nonneg (not_le.mpr hp)`. Establish `hG : Differentiable ℂ (fun z => ∑ j, M.ι.symm (c j) * U1 d t (U1 d (s j) θ) z ^ a)` using `by fun_prop`. Rewrite using `[← hat_comb M.ι hl _ c _ (fun j => (hUU j).analyticAt 0), ← bd_scale_iff M.ι ω hSq (hG.analyticAt 0)]`. Establish `hGS : AnalyticAt ℂ (fun z => ∑ j, M.ι.symm (c j) * U1 d t (U1 d (s j) θ) ((S : ℂ) * z) ^ a) 0` using `(show Differentiable ℂ (fun z => ∑ j, M.ι.symm (c j) * U1 d t (U1 d (s j) θ) ((S : ℂ) * z) ^ a) by fun_prop).analyticAt 0`.

Establish `hpr : AnalyticAt ℂ (fun z => U1 d t θ ((S : ℂ) * z) ^ a * φ (z + t')) 0` using `(hUtS.fun_pow a).fun_mul hφt0`. Establish `hev : ∀ᶠ z in 𝓝[≠] (0 : ℂ), (∑ j, M.ι.symm (c j) * U1 d t (U1 d (s j) θ) ((S : ℂ) * z) ^ a) = U1 d t θ ((S : ℂ) * z) ^ a * φ (z + t')`. Use `Filter.Eventually.filter_mono nhdsWithin_le_nhds ?_` and prove the remaining obligations. Establish `hc : ContinuousAt (fun z => θ ((S : ℂ) * z + t)) 0` using `(show Differentiable ℂ (fun z => θ ((S : ℂ) * z + t)) by fun_prop).continuous.continuousAt`. Use `filter_upwards [hc.eventually_ne (y := 0) (by simpa using hθt)] with z hz`.

Rewrite using `[hφ, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Establish `key : U1 d t (U1 d (s j) θ) ((S : ℂ) * z) = U1 d t θ ((S : ℂ) * z) * (U1 d (s j) θ ((S : ℂ) * (z + t')) / θ ((S : ℂ) * (z + t')))`. Rewrite using `[mul_add, hSt']`. Generalize the expression as in `U1 d (s j) θ = F`.

Simplify using `only [U1]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[key, mul_pow]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[((GlobalTheory.MomOne.TaylorRead.hat_laws q M.ι _ hl).1 _ _ hGS hpr).2.2.1 hev, hat_mul M.ι hl (hUtS.fun_pow a) hφt0, hat_pow M.ι hl hUtS]`.

Establish `h1 : Bd 1 (hat M.ι (C ω * logS) (fun z => U1 d t θ ((S : ℂ) * z)))` using `(bd_scale_iff M.ι ω hSq (hUt.analyticAt 0) 1).mpr (GlobalTheory.T.cpSeriesBounded_one_torsionTranslate_cmTheta d q M ω θ hd hd16 hsp hL hM hθ t ht ht2)`. Use `((GlobalTheory.MomOne.sup_norm_laws q).1 _ _ _ _ (bd_pow h1 a) hBφt).2` as an intermediate fact. Rewrite `this` using `[one_mul]`. Then use the resulting hypothesis.
-/
theorem translate_bd : ∀ (d q : ℕ) [Fact q.Prime] (M : Mdl q) (ω : ℂ_[q]) (θ : ℂ → ℂ), d.Prime → d % 16 = 7 → Split d q → IsOK d M.L → M.MChart ω → IsTh d θ → ∀ (a m : ℕ) (c : Fin m → ℂ_[q]) (s : Fin m → ℂ) (t : ℂ) (B : ℝ), (∀ j, PrimeTo d q (s j)) → PrimeTo d q t → ¬ InOK d (t - 1 / 2) → Bd B (∑ j, C (c j) * hat M.ι (C ω * logS) (U1 d (s j) θ) ^ a) → Bd B (∑ j, C (c j) * hat M.ι (C ω * logS) (U1 d t (U1 d (s j) θ)) ^ a) := by
  intro d q _ M ω θ hd hd16 hsp hL hM hθ a m c s t B hs ht ht2 hB
  obtain ⟨S, hS0, hSq, hSt, hSs⟩ := exists_common s t hs ht
  have hl : constantCoeff (C ω * logS : ℂ_[q]⟦X⟧) = 0 := hM.2.1
  have hSne : (S : ℂ) ≠ 0 := by exact_mod_cast hS0.ne'
  have hθd : Differentiable ℂ θ := hθ.1
  have hθt : θ t ≠ 0 := fun h => ht2 (hθ.2.2.2.2 t h)
  have hU : ∀ j, Differentiable ℂ (U1 d (s j) θ) := fun j => differentiable_U1 d _ hθd
  have hUU : ∀ j, Differentiable ℂ (U1 d t (U1 d (s j) θ)) := fun j => differentiable_U1 d _ (hU j)
  have hUt : Differentiable ℂ (U1 d t θ) := differentiable_U1 d _ hθd
  have E := fun j => GlobalTheory.T.scaledThetaTranslationQuotient_elliptic d q M ω θ hd hd16 hsp hL hM hθ (s j) S hS0 hSq (hSs j)
  have Et := (GlobalTheory.T.scaledThetaTranslationQuotient_elliptic d q M ω θ hd hd16 hsp hL hM hθ t S hS0 hSq hSt).2.2.2.1
  simp only at E
  set t' : ℂ := t / S with ht'
  have hSt' : (S : ℂ) * t' = t := by rw [ht']; field_simp
  set φ : ℂ → ℂ := fun z => ∑ j, M.ι.symm (c j) * (U1 d (s j) θ ((S : ℂ) * z) / θ ((S : ℂ) * z)) ^ a with hφ
  have hφan : ∀ p, θ ((S : ℂ) * p) ≠ 0 → AnalyticAt ℂ φ p := fun p hp =>
    Finset.analyticAt_fun_sum _ fun j _ => analyticAt_const.fun_mul (((E j).2.2.1 p hp).fun_pow a)
  have hφper : ∀ l ∈ M.L.lattice, ∀ z, φ (z + l) = φ z := fun l hl z =>
    Finset.sum_congr rfl fun j _ => by
      have := (E j).1.2 l hl z
      simp only at this
      rw [this]
  have hφmer : ∀ p, MeromorphicAt φ p := fun p =>
    MeromorphicAt.fun_sum fun j _ => (MeromorphicAt.const _ _).fun_mul (((E j).1.1 p).fun_pow a)
  have h0 : θ ((S : ℂ) * 0) ≠ 0 := by rw [mul_zero, hθ.2.1]; exact one_ne_zero
  have h0' : θ ((S : ℂ) * t') ≠ 0 := by rw [hSt']; exact hθt
  have hφ0 := hφan 0 h0
  have hφt := hφan t' h0'
  have hφt0 : AnalyticAt ℂ (fun z => φ (z + t')) 0 :=
    AnalyticAt.comp_of_eq hφt (f := fun z => z + t') (by fun_prop) (zero_add _)
  have hθS : AnalyticAt ℂ (fun z => θ ((S : ℂ) * z)) 0 :=
    (show Differentiable ℂ (fun z => θ ((S : ℂ) * z)) by fun_prop).analyticAt 0
  have hUtS : AnalyticAt ℂ (fun z => U1 d t θ ((S : ℂ) * z)) 0 :=
    (show Differentiable ℂ (fun z => U1 d t θ ((S : ℂ) * z)) by fun_prop).analyticAt 0

  have hBφ : Bd B (hat M.ι (C ω * logS) φ) := by
    have hG : Differentiable ℂ (fun z => ∑ j, M.ι.symm (c j) * U1 d (s j) θ z ^ a) := by fun_prop
    rw [← hat_comb M.ι hl _ c _ (fun j => (hU j).analyticAt 0),
      ← bd_scale_iff M.ι ω hSq (hG.analyticAt 0)] at hB
    have hGS : AnalyticAt ℂ (fun z => ∑ j, M.ι.symm (c j) * U1 d (s j) θ ((S : ℂ) * z) ^ a) 0 :=
      (show Differentiable ℂ (fun z => ∑ j, M.ι.symm (c j) * U1 d (s j) θ ((S : ℂ) * z) ^ a) by
        fun_prop).analyticAt 0
    have hpr : AnalyticAt ℂ (fun z => θ ((S : ℂ) * z) ^ a * φ z) 0 := (hθS.fun_pow a).fun_mul hφ0
    have hev : ∀ᶠ z in 𝓝[≠] (0 : ℂ), (∑ j, M.ι.symm (c j) * U1 d (s j) θ ((S : ℂ) * z) ^ a)
        = θ ((S : ℂ) * z) ^ a * φ z := by
      refine Filter.Eventually.filter_mono nhdsWithin_le_nhds ?_
      filter_upwards [hθS.continuousAt.eventually_ne h0] with z hz
      rw [hφ, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [div_pow]; field_simp
    rw [((GlobalTheory.MomOne.TaylorRead.hat_laws q M.ι _ hl).1 _ _ hGS hpr).2.2.1 hev,
      hat_mul M.ι hl (hθS.fun_pow a) hφ0, hat_pow M.ι hl hθS] at hB
    have h1 : Bd 1 (hat M.ι (C ω * logS) (fun z => θ ((S : ℂ) * z))) :=
      (bd_scale_iff M.ι ω hSq (hθd.analyticAt 0) 1).mpr (GlobalTheory.T.cm_even_theta_series_chart_coeff_integral d q M ω θ hd hd16 hsp hL hM hθ)
    refine (GlobalTheory.MomOne.sup_norm_laws q).2.2.2.2.2 _ _ 0 B (bd_pow h1 a) ?_ (by rwa [pow_zero, one_mul])
    rw [map_pow, (GlobalTheory.MomOne.TaylorRead.hat_laws q M.ι _ hl).2.2.2.1]
    simp [hθ.2.1]

  have hBφt : Bd B (hat M.ι (C ω * logS) (fun z => φ (z + t'))) := by
    by_cases hsm : M.Small t'
    · have hpt : PrimeTo d q t' :=
        ⟨S * S, Nat.mul_pos hS0 hS0, Nat.Coprime.mul_left hSq hSq, by
          rw [Nat.cast_mul, mul_assoc, hSt']; exact hSt⟩
      have hin := (hL t').mpr ((GlobalTheory.T.smallTorsion_killed_by_prime_powers d q M ω hd hd16 hsp hL hM).2.2.1 t' hpt hsm)
      have : (fun z => φ (z + t')) = φ := funext fun z => hφper t' hin z
      rwa [this]
    · refine GlobalTheory.T.cpTransportedTaylorSeries_translate_norm_le q M _ φ t' B hM ⟨hφmer, hφper⟩ hφ0 hφt (fun p hp => ?_) hsm ?_ hBφ
      · refine Et p 0 ⟨1, one_pos, Nat.coprime_one_left q, by simpa using inOK_zero d⟩
          (not_inOK_half hd.pos) ?_
        by_contra hne
        rw [add_zero] at hne
        exact absurd (hφan p hne).meromorphicOrderAt_nonneg (not_le.mpr hp)
      · refine GlobalTheory.T.cpSeriesCoeffBounded_taylor_elliptic_of_poles q M _ _ hM ⟨fun p => ?_, fun l hl z => ?_⟩ hφt0 (fun p hp => ?_)
        · exact MeromorphicAt.comp_analyticAt (f := φ) (g := fun z => z + t') (hφmer _) (by fun_prop)
        · show φ (z + l + t') = φ (z + t')
          rw [add_right_comm, hφper l hl]
        · refine Et p t ht ht2 ?_
          by_contra hne
          have h2 : AnalyticAt ℂ φ (p + t') := hφan _ (by rwa [mul_add, hSt'])
          have h3 : AnalyticAt ℂ (fun z => φ (z + t')) p :=
            AnalyticAt.comp_of_eq h2 (f := fun z => z + t') (by fun_prop) rfl
          exact absurd h3.meromorphicOrderAt_nonneg (not_le.mpr hp)

  have hG : Differentiable ℂ (fun z => ∑ j, M.ι.symm (c j) * U1 d t (U1 d (s j) θ) z ^ a) := by fun_prop
  rw [← hat_comb M.ι hl _ c _ (fun j => (hUU j).analyticAt 0),
    ← bd_scale_iff M.ι ω hSq (hG.analyticAt 0)]
  have hGS : AnalyticAt ℂ (fun z => ∑ j, M.ι.symm (c j) * U1 d t (U1 d (s j) θ) ((S : ℂ) * z) ^ a) 0 :=
    (show Differentiable ℂ (fun z => ∑ j, M.ι.symm (c j) * U1 d t (U1 d (s j) θ) ((S : ℂ) * z) ^ a) by
      fun_prop).analyticAt 0
  have hpr : AnalyticAt ℂ (fun z => U1 d t θ ((S : ℂ) * z) ^ a * φ (z + t')) 0 := (hUtS.fun_pow a).fun_mul hφt0
  have hev : ∀ᶠ z in 𝓝[≠] (0 : ℂ), (∑ j, M.ι.symm (c j) * U1 d t (U1 d (s j) θ) ((S : ℂ) * z) ^ a)
      = U1 d t θ ((S : ℂ) * z) ^ a * φ (z + t') := by
    refine Filter.Eventually.filter_mono nhdsWithin_le_nhds ?_
    have hc : ContinuousAt (fun z => θ ((S : ℂ) * z + t)) 0 :=
      (show Differentiable ℂ (fun z => θ ((S : ℂ) * z + t)) by fun_prop).continuous.continuousAt
    filter_upwards [hc.eventually_ne (y := 0) (by simpa using hθt)] with z hz
    rw [hφ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have key : U1 d t (U1 d (s j) θ) ((S : ℂ) * z) = U1 d t θ ((S : ℂ) * z) *
        (U1 d (s j) θ ((S : ℂ) * (z + t')) / θ ((S : ℂ) * (z + t'))) := by
      rw [mul_add, hSt']
      generalize U1 d (s j) θ = F
      simp only [U1]
      field_simp
    rw [key, mul_pow]; ring
  rw [((GlobalTheory.MomOne.TaylorRead.hat_laws q M.ι _ hl).1 _ _ hGS hpr).2.2.1 hev,
    hat_mul M.ι hl (hUtS.fun_pow a) hφt0, hat_pow M.ι hl hUtS]
  have h1 : Bd 1 (hat M.ι (C ω * logS) (fun z => U1 d t θ ((S : ℂ) * z))) :=
    (bd_scale_iff M.ι ω hSq (hUt.analyticAt 0) 1).mpr (GlobalTheory.T.cpSeriesBounded_one_torsionTranslate_cmTheta d q M ω θ hd hd16 hsp hL hM hθ t ht ht2)
  have := ((GlobalTheory.MomOne.sup_norm_laws q).1 _ _ _ _ (bd_pow h1 a) hBφt).2
  rwa [one_mul] at this

end GlobalTheory.MomOne.TranslNorm
