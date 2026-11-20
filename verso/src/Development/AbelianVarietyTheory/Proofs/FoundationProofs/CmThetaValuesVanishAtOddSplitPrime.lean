import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaPointsIntegralNormConjugateLawsStatement
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.CoeffSubstInvMemOfTwoLeOrder
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.ThetaSplit

/- English proof (translation)
Rewrite `h` using `[← jacobiSym.legendreSym.to_jacobiSym]`. Establish `ha : (a : ZMod p) ≠ 0`. Introduce `h0`. Rewrite `h` using `[(legendreSym.eq_zero_iff p a).2 h0]`. Conclude with `zero_ne_one h`.

Take `⟨r, hr⟩` from `(legendreSym.eq_one_iff p ha).1 h`. Take `⟨r, rfl⟩` from `ZMod.intCast_surjective r`. Establish `hr0 : (r : ZMod p) ≠ 0` using `fun h0 => ha (by rw [hr, h0, mul_zero])`. Establish `h20 : ((2 : ℤ) : ZMod p) ≠ 0`. Rewrite using `[Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]`.

Introduce `hd`. Establish `: p ∣ 2` using `by exact_mod_cast hd`. Conclude with `h2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 this)`. Establish `hn : ‖((2 * r : ℤ) : ℤ_[p])‖ = 1`. Use `le_antisymm (PadicInt.norm_le_one _) (not_lt.1 fun hlt => ?_)` and prove the remaining obligations.

Rewrite `hlt` using `[PadicInt.norm_int_lt_one_iff_dvd, ← ZMod.intCast_zmod_eq_zero_iff_dvd]`. Move the coercions through the operations in `at hlt h20`. Conclude with `mul_ne_zero h20 hr0 hlt`. Establish `hlt : ‖((r ^ 2 - a : ℤ) : ℤ_[p])‖ < 1`. Rewrite using `[PadicInt.norm_int_lt_one_iff_dvd, ← ZMod.intCast_zmod_eq_zero_iff_dvd]`.

Use `push_cast`. Rewrite using `[hr]`. Expand and normalize the polynomial expressions, which then agree. Establish `e1 : ∀ z : ℤ_[p], Polynomial.aeval z (Polynomial.X ^ 2 - Polynomial.C a : Polynomial ℤ) = z ^ 2 - a`. Introduce `z`.

Simplify using the standard rewrite rules. Establish `e2 : ∀ z : ℤ_[p], Polynomial.aeval z (Polynomial.derivative (Polynomial.X ^ 2 - Polynomial.C a : Polynomial ℤ)) = 2 * z`. Introduce `z`. Simplify using `[map_ofNat]`. Take `⟨z, hz, -, hz', -⟩` from `hensels_lemma (p := p) (F := (Polynomial.X ^ 2 - Polynomial.C a : Polynomial ℤ)) (a := (r : ℤ_[p])) (by`.

Rewrite using `[e1, e2]`. Move the coercions through the operations in `at hn hlt`. Rewrite using `[hn]`. Simplify using `using hlt)`. Rewrite `hz` using `[e1]`.

Rewrite `hz'` using `[e2, e2]`. Move the coercions through the operations in `at hn`. Conclude with `⟨z, sub_eq_zero.1 hz, PadicInt.isUnit_iff.2 (hz'.trans hn)⟩`.
-/
theorem exists_sqrt_padic {p : ℕ} [hp : Fact p.Prime] (h2 : p ≠ 2) {a : ℤ} (h : jacobiSym a p = 1) :
    ∃ z : ℤ_[p], z ^ 2 = (a : ℤ_[p]) ∧ IsUnit (2 * z) := by
  rw [← jacobiSym.legendreSym.to_jacobiSym] at h
  have ha : (a : ZMod p) ≠ 0 := by
    intro h0
    rw [(legendreSym.eq_zero_iff p a).2 h0] at h
    exact zero_ne_one h
  obtain ⟨r, hr⟩ := (legendreSym.eq_one_iff p ha).1 h
  obtain ⟨r, rfl⟩ := ZMod.intCast_surjective r
  have hr0 : (r : ZMod p) ≠ 0 := fun h0 => ha (by rw [hr, h0, mul_zero])
  have h20 : ((2 : ℤ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    intro hd
    have : p ∣ 2 := by exact_mod_cast hd
    exact h2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 this)
  have hn : ‖((2 * r : ℤ) : ℤ_[p])‖ = 1 := by
    refine le_antisymm (PadicInt.norm_le_one _) (not_lt.1 fun hlt => ?_)
    rw [PadicInt.norm_int_lt_one_iff_dvd, ← ZMod.intCast_zmod_eq_zero_iff_dvd] at hlt
    push_cast at hlt h20
    exact mul_ne_zero h20 hr0 hlt
  have hlt : ‖((r ^ 2 - a : ℤ) : ℤ_[p])‖ < 1 := by
    rw [PadicInt.norm_int_lt_one_iff_dvd, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hr]; ring
  have e1 : ∀ z : ℤ_[p], Polynomial.aeval z (Polynomial.X ^ 2 - Polynomial.C a : Polynomial ℤ) = z ^ 2 - a := by
    intro z; simp
  have e2 : ∀ z : ℤ_[p], Polynomial.aeval z
      (Polynomial.derivative (Polynomial.X ^ 2 - Polynomial.C a : Polynomial ℤ)) = 2 * z := by
    intro z; simp [map_ofNat]
  obtain ⟨z, hz, -, hz', -⟩ := hensels_lemma (p := p) (F := (Polynomial.X ^ 2 - Polynomial.C a : Polynomial ℤ))
    (a := (r : ℤ_[p])) (by
      rw [e1, e2]
      push_cast at hn hlt
      rw [hn]; simpa using hlt)
  rw [e1] at hz
  rw [e2, e2] at hz'
  push_cast at hn
  exact ⟨z, sub_eq_zero.1 hz, PadicInt.isUnit_iff.2 (hz'.trans hn)⟩

/- English proof (translation)
Establish `hm : ∀ x, D.host.φ₀ x ∈ Qbar` using `fun x => by`. Rewrite using `[mem_algebraicClosure_iff]`. Conclude with `(Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom D.host.φ₀.toRatAlgHom`. Use `⟨lam.comp (D.host.φ₀.codRestrict Qbar hm), fun x => ?_⟩` and prove the remaining obligations. Simplify using `only [lamC, dif_pos (hm x)]`.

Both sides reduce to the same expression.
-/
theorem exists_emb (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) :
    ∃ ψ : D.host.E →+* ℂ_[p], ∀ x, lamC lam (D.host.φ₀ x) = ψ x := by
  have hm : ∀ x, D.host.φ₀ x ∈ Qbar := fun x => by
    rw [mem_algebraicClosure_iff]
    exact (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom D.host.φ₀.toRatAlgHom
  refine ⟨lam.comp (D.host.φ₀.codRestrict Qbar hm), fun x => ?_⟩
  simp only [lamC, dif_pos (hm x)]
  rfl

/- English proof (translation)
Establish `hb : D.host.sqrtMinusD ^ 2 = -(D.host.d : D.host.E)` using `D.host.sqd_sq`. Establish `hK : D.host.sqrtMinusD ∈ D.host.K` using `IntermediateField.mem_adjoin_simple_self ℚ _`. Establish `hi : IsIntegral ℤ (⟨D.host.sqrtMinusD, hK⟩ : D.host.K)`. Use `IsIntegral.of_pow two_pos ?_` and prove the remaining obligations. Establish `: (⟨D.host.sqrtMinusD, hK⟩ : D.host.K) ^ 2 = algebraMap ℤ D.host.K (-(D.host.d : ℤ))`.

Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `using hb`. Rewrite using `[this]`. Conclude with `isIntegral_algebraMap`. Conclude with `⟨⟨_, hi⟩, hb, D.host.conj_sqd⟩`.
-/
theorem exists_sqrt_host (D : D7) : ∃ b : 𝓞 D.host.K, ((b : D.host.K) : D.host.E) ^ 2 = -(D.host.d : D.host.E) ∧
    D.host.conj ((b : D.host.K) : D.host.E) = -((b : D.host.K) : D.host.E) := by
  have hb : D.host.sqrtMinusD ^ 2 = -(D.host.d : D.host.E) := D.host.sqd_sq
  have hK : D.host.sqrtMinusD ∈ D.host.K := IntermediateField.mem_adjoin_simple_self ℚ _
  have hi : IsIntegral ℤ (⟨D.host.sqrtMinusD, hK⟩ : D.host.K) := by
    refine IsIntegral.of_pow two_pos ?_
    have : (⟨D.host.sqrtMinusD, hK⟩ : D.host.K) ^ 2 = algebraMap ℤ D.host.K (-(D.host.d : ℤ)) := by
      apply Subtype.ext
      simpa using hb
    rw [this]; exact isIntegral_algebraMap
  exact ⟨⟨_, hi⟩, hb, D.host.conj_sqd⟩

/- English proof (translation)
Take `⟨ψ, hψ⟩` from `exists_emb D lam`. Take `⟨b, hb, hc⟩` from `exists_sqrt_host D`. Set `ι : ℤ_[p] →+* ℂ_[p]` to `(algebraMap ℚ_[p] ℂ_[p]).comp PadicInt.Coe.ringHom`. Establish `hι : Continuous ι` using `(continuous_algebraMap ℚ_[p] ℂ_[p]).comp continuous_subtype_val`. Use `set s := ψ ((b : D.host.K) : D.host.E) with hsdef`.

Establish `hs2 : s ^ 2 = -(D.host.d : ℂ_[p])` using `by rw [hsdef, ← map_pow, hb]; simp`. Choose the witnesses or unpack the hypotheses as in `⟨z, hz, hu⟩ : ∃ z : ℤ_[p], ι z = s ∧ IsUnit (2 * z) := by`. Take `⟨z, hz, hu⟩` from `exists_sqrt_padic h2 hs`. Establish `: ι z ^ 2 = s ^ 2` using `by rw [← map_pow, hz, hs2]; simp`. Break down `sq_eq_sq_iff_eq_or_eq_neg.1 this with h | h` into its components or cases.

Conclude with `⟨z, h, hu⟩`. Conclude with `⟨-z, by rw [map_neg, h, neg_neg], by simpa using hu.neg⟩`. Take `⟨w, hw⟩` from `hu.exists_right_inv`. Set `f : ℤ_[p] × ℤ_[p] → ℂ_[p] × ℂ_[p]` to `fun x => (ι x.1 + ι x.2 * s, ι x.1 - ι x.2 * s)`. Establish `hf : Continuous f` using `by fun_prop`.

Establish `hd : DenseRange (Prod.map (Int.cast : ℤ → ℤ_[p]) (Int.cast : ℤ → ℤ_[p]))` using `PadicInt.denseRange_intCast.prodMap PadicInt.denseRange_intCast`. Establish `hw' : 2 * s * ι w = 1`. Use `congrArg ι hw` as an intermediate fact. Rewrite `this` using `[map_mul, map_mul, map_ofNat, hz, map_one]`. Then use the resulting hypothesis. Establish `h1 : f (z * w, w) = (1, 0)`.

Simplify using `only [f, map_mul, hz]`. Use `ext`. Take the linear combination `hw'`. Simplify using `only`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[← h1]`. Use `map_mem_closure hf (hd (z * w, w)) ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨⟨m, n⟩, rfl⟩`. Use `⟨(m : 𝓞 D.host.K) + n * b, ?_⟩` and prove the remaining obligations. Simplify using `only [GL3Theta.tauK, GL3Theta.tauKc, hψ, f, Prod.map]`.

Simplify using `[hc, hsdef, sub_eq_add_neg]`.
-/
theorem idem_mem (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (h2 : p ≠ 2)
    (hs : GL3Theta.SplitK D p) : ((1, 0) : ℂ_[p] × ℂ_[p]) ∈ GL3Theta.OKp D lam := by
  obtain ⟨ψ, hψ⟩ := exists_emb D lam
  obtain ⟨b, hb, hc⟩ := exists_sqrt_host D
  let ι : ℤ_[p] →+* ℂ_[p] := (algebraMap ℚ_[p] ℂ_[p]).comp PadicInt.Coe.ringHom
  have hι : Continuous ι := (continuous_algebraMap ℚ_[p] ℂ_[p]).comp continuous_subtype_val
  set s := ψ ((b : D.host.K) : D.host.E) with hsdef
  have hs2 : s ^ 2 = -(D.host.d : ℂ_[p]) := by rw [hsdef, ← map_pow, hb]; simp
  obtain ⟨z, hz, hu⟩ : ∃ z : ℤ_[p], ι z = s ∧ IsUnit (2 * z) := by
    obtain ⟨z, hz, hu⟩ := exists_sqrt_padic h2 hs
    have : ι z ^ 2 = s ^ 2 := by rw [← map_pow, hz, hs2]; simp
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 this with h | h
    · exact ⟨z, h, hu⟩
    · exact ⟨-z, by rw [map_neg, h, neg_neg], by simpa using hu.neg⟩
  obtain ⟨w, hw⟩ := hu.exists_right_inv
  let f : ℤ_[p] × ℤ_[p] → ℂ_[p] × ℂ_[p] := fun x => (ι x.1 + ι x.2 * s, ι x.1 - ι x.2 * s)
  have hf : Continuous f := by fun_prop
  have hd : DenseRange (Prod.map (Int.cast : ℤ → ℤ_[p]) (Int.cast : ℤ → ℤ_[p])) :=
    PadicInt.denseRange_intCast.prodMap PadicInt.denseRange_intCast
  have hw' : 2 * s * ι w = 1 := by
    have := congrArg ι hw
    rwa [map_mul, map_mul, map_ofNat, hz, map_one] at this
  have h1 : f (z * w, w) = (1, 0) := by
    simp only [f, map_mul, hz]
    ext
    · linear_combination hw'
    · simp only; ring
  rw [← h1]
  refine map_mem_closure hf (hd (z * w, w)) ?_
  rintro _ ⟨⟨m, n⟩, rfl⟩
  refine ⟨(m : 𝓞 D.host.K) + n * b, ?_⟩
  simp only [GL3Theta.tauK, GL3Theta.tauKc, hψ, f, Prod.map]
  simp [hc, hsdef, sub_eq_add_neg]

section Series
variable {p : ℕ} [Fact p.Prime] (g : GL3Theta.G1 p) {σ : Type*}

/- English proof (translation)
Rewrite using `[← PowerSeries.coeff_zero_eq_constantCoeff_apply]`. Simplify using `[GL3Theta.G1.l, flog]`.
-/
theorem const_l : PowerSeries.constantCoeff g.l = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [GL3Theta.G1.l, flog]

/- English proof (translation)
Simplify using `only [GL3Theta.G1.ph, map_neg, neg_eq_zero]`. Use `show GL3Theta.logMv _ 0 = 0`. Simplify using `[GL3Theta.logMv]`.
-/
theorem const_ph : PowerSeries.constantCoeff g.ph = 0 := by
  simp only [GL3Theta.G1.ph, map_neg, neg_eq_zero]
  show GL3Theta.logMv _ 0 = 0
  simp [GL3Theta.logMv]

/- English proof (translation)
Take `⟨-, -, h0, h1⟩` from `h`. Establish `hl : ∀ _ : Unit, MvPowerSeries.constantCoeff (g.l : MvPowerSeries Unit ℂ_[p]) = 0` using `fun _ => const_l g`. Establish `he : ∀ _ : Unit, MvPowerSeries.constantCoeff (g.ex : MvPowerSeries Unit ℂ_[p]) = 0` using `fun _ => h0`. Establish `h2 : ∀ i : Unit, MvPowerSeries.subst (fun _ : Unit => (g.ex : MvPowerSeries Unit ℂ_[p])) (g.l : MvPowerSeries Unit ℂ_[p]) = MvPowerSeries.X i` using `fun _ => h1`. Establish `h3` using `GlobalTheory.FormalInv.eq_substInv_of_right hl he h2`.

Establish `h4` using `GlobalTheory.FormalInv.subst_substInv_left hl (IsUnit.of_mul_eq_one _ (GlobalTheory.FormalInv.linearPart_mul_eq_one hl he h2)) ()`. Rewrite `h4` using `[← h3]`. Conclude with `h4`.
-/
theorem ex_l (h : g.Ok) : PowerSeries.subst g.l g.ex = PowerSeries.X := by
  obtain ⟨-, -, h0, h1⟩ := h
  have hl : ∀ _ : Unit, MvPowerSeries.constantCoeff (g.l : MvPowerSeries Unit ℂ_[p]) = 0 := fun _ => const_l g
  have he : ∀ _ : Unit, MvPowerSeries.constantCoeff (g.ex : MvPowerSeries Unit ℂ_[p]) = 0 := fun _ => h0
  have h2 : ∀ i : Unit, MvPowerSeries.subst (fun _ : Unit => (g.ex : MvPowerSeries Unit ℂ_[p]))
      (g.l : MvPowerSeries Unit ℂ_[p]) = MvPowerSeries.X i := fun _ => h1
  have h3 := GlobalTheory.FormalInv.eq_substInv_of_right hl he h2
  have h4 := GlobalTheory.FormalInv.subst_substInv_left hl
    (IsUnit.of_mul_eq_one _ (GlobalTheory.FormalInv.linearPart_mul_eq_one hl he h2)) ()
  rw [← h3] at h4
  exact h4

/- English proof (translation)
Establish `ha'` using `PowerSeries.HasSubst.of_constantCoeff_zero ha`. Rewrite using `[GL3Theta.G1.pt, GL3Theta.G1.lg, ← PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' (const_l g)) ha', ex_l g h, PowerSeries.subst_X ha']`.
-/
theorem pt_lg (h : g.Ok) {a : MvPowerSeries σ ℂ_[p]} (ha : MvPowerSeries.constantCoeff a = 0) :
    g.pt (g.lg a) = a := by
  have ha' := PowerSeries.HasSubst.of_constantCoeff_zero ha
  rw [GL3Theta.G1.pt, GL3Theta.G1.lg, ← PowerSeries.subst_comp_subst_apply
    (PowerSeries.HasSubst.of_constantCoeff_zero' (const_l g)) ha', ex_l g h, PowerSeries.subst_X ha']

/- English proof (translation)
Take `⟨k, rfl⟩` from `PowerSeries.X_dvd_iff.2 hf`. Establish `h0 : PowerSeries.HasSubst (0 : MvPowerSeries σ ℂ_[p])` using `PowerSeries.HasSubst.of_constantCoeff_zero (map_zero _)`. Rewrite using `[PowerSeries.subst_mul h0, PowerSeries.subst_X h0, zero_mul]`.
-/
theorem subst_zero {f : PowerSeries ℂ_[p]} (hf : PowerSeries.constantCoeff f = 0) :
    PowerSeries.subst (0 : MvPowerSeries σ ℂ_[p]) f = 0 := by
  obtain ⟨k, rfl⟩ := PowerSeries.X_dvd_iff.2 hf
  have h0 : PowerSeries.HasSubst (0 : MvPowerSeries σ ℂ_[p]) := PowerSeries.HasSubst.of_constantCoeff_zero (map_zero _)
  rw [PowerSeries.subst_mul h0, PowerSeries.subst_X h0, zero_mul]

/- English proof (translation)
Rewrite using `[GL3Theta.G1.mulBy, map_one, one_mul, pt_lg g h (MvPowerSeries.constantCoeff_X i)]`.
-/
theorem mulBy_one (h : g.Ok) (i : σ) : g.mulBy 1 (GL3Theta.Xv i) = GL3Theta.Xv i := by
  rw [GL3Theta.G1.mulBy, map_one, one_mul, pt_lg g h (MvPowerSeries.constantCoeff_X i)]

/- English proof (translation)
Rewrite using `[GL3Theta.G1.mulBy, map_zero, zero_mul, GL3Theta.G1.pt, subst_zero h.2.2.1]`.
-/
theorem mulBy_zero (h : g.Ok) (a : MvPowerSeries σ ℂ_[p]) : g.mulBy 0 a = 0 := by
  rw [GL3Theta.G1.mulBy, map_zero, zero_mul, GL3Theta.G1.pt, subst_zero h.2.2.1]

/- English proof (translation)
Establish `h1 : g.lg (0 : MvPowerSeries σ ℂ_[p]) = 0` using `subst_zero (const_l g)`. Establish `h2 : g.phAt (0 : MvPowerSeries σ ℂ_[p]) = 0` using `subst_zero (const_ph g)`. Rewrite using `[GL3Theta.G1.be, GL3Theta.G1.add, h1, add_zero, pt_lg g h (MvPowerSeries.constantCoeff_X i), h2]`. Simplify using the standard rewrite rules.
-/
theorem be_zero (h : g.Ok) (i : σ) : g.be (GL3Theta.Xv i) 0 = 0 := by
  have h1 : g.lg (0 : MvPowerSeries σ ℂ_[p]) = 0 := subst_zero (const_l g)
  have h2 : g.phAt (0 : MvPowerSeries σ ℂ_[p]) = 0 := subst_zero (const_ph g)
  rw [GL3Theta.G1.be, GL3Theta.G1.add, h1, add_zero, pt_lg g h (MvPowerSeries.constantCoeff_X i), h2]
  simp

end Series

/- English proof (translation)
Introduce `D p _ cc δ g hg h2 hs`. Take `⟨-, hN, hC⟩` from `GlobalTheory.T.cmThetaPoints_integral_norm_conjugate_laws D`. Establish `hα` using `idem_mem D g.lam h2 hs`. Establish `hok : g.Ok` using `hg.2.2.2.2`. Establish `h1` using `hC p cc δ g hg h2 _ hα`.

Establish `h3` using `hN p cc δ g hg h2 _ hα`. Simplify using `only [mulBy_one g hok, mulBy_zero g hok, be_zero g hok, mul_zero, map_zero, zero_mul] at h1 h3`. Conclude with `⟨h1, h3⟩`.
-/
theorem splitZero : ∀ D : D7, GL3Theta.splitZero D := by
  intro D p _ cc δ g hg h2 hs
  obtain ⟨-, hN, hC⟩ := GlobalTheory.T.cmThetaPoints_integral_norm_conjugate_laws D
  have hα := idem_mem D g.lam h2 hs
  have hok : g.Ok := hg.2.2.2.2
  have h1 := hC p cc δ g hg h2 _ hα
  have h3 := hN p cc δ g hg h2 _ hα
  simp only [mulBy_one g hok, mulBy_zero g hok, be_zero g hok, mul_zero, map_zero, zero_mul] at h1 h3
  exact ⟨h1, h3⟩

end GlobalTheory.ThetaSplit
