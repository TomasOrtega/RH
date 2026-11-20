import Mathlib
import GroundTheory.PAdicHodge.SlopeDescentBounded
import GroundTheory.PAdicHodge.ExtRobbaFixedBridge
import GroundTheory.PAdicHodge.ExtRobbaFixedUnif
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open Laurent Filter Topology UniformSpace

/- English proof (translation)
Rewrite using `[Real.mul_rpow (Real.rpow_nonneg ha _) (Real.rpow_nonneg hb _), ← Real.rpow_mul ha, ← Real.rpow_mul hb, ← Real.rpow_mul ha, ← Real.rpow_mul hb, mul_comm (1 - t), mul_comm t]`.
-/
theorem rpow_interp_eq {a b t c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a ^ (1 - t) * b ^ t) ^ c = (a ^ c) ^ (1 - t) * (b ^ c) ^ t := by
  rw [Real.mul_rpow (Real.rpow_nonneg ha _) (Real.rpow_nonneg hb _), ← Real.rpow_mul ha,
    ← Real.rpow_mul hb, ← Real.rpow_mul ha, ← Real.rpow_mul hb, mul_comm (1 - t), mul_comm t]

/- English proof (translation)
Establish `hlogσ : Real.log σ ≠ 0` using `(Real.log_neg hσ0 hσ1).ne`. Use `set c := Real.log (f σ) / Real.log σ with hc`. Use `⟨c, ?_⟩` and prove the remaining obligations. Establish `hfσ : f σ = σ ^ c`. Rewrite using `[Real.rpow_def_of_pos hσ0, hc, mul_div_cancel₀ _ hlogσ, Real.exp_log (hpos σ hσ0 le_rfl)]`.

Establish `hpowQ : ∀ x : ℝ, 0 ≤ x → (x ^ Q) ^ c = (x ^ c) ^ Q`. Introduce `x hx`. Rewrite using `[← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hx, ← Real.rpow_mul hx, mul_comm]`. Establish `hσQ : ∀ J : ℕ, 0 < σ ^ Q ^ J ∧ σ ^ Q ^ J ≤ σ ∧ f (σ ^ Q ^ J) = (σ ^ Q ^ J) ^ c`. Introduce `J`.

Proceed by induction on `J with`. Consider the case `zero => simp only [pow_zero, pow_one]`. Conclude with `⟨hσ0, le_rfl, hfσ⟩`. Consider the case `succ J ih`. Take `⟨h0, h1, h2⟩` from `ih`.

Establish `e : σ ^ Q ^ (J + 1) = (σ ^ Q ^ J) ^ Q` using `by rw [← pow_mul, ← pow_succ]`. Use `⟨pow_pos hσ0 _, pow_le_of_le_one hσ0.le hσ1.le (by positivity), ?_⟩` and prove the remaining obligations. Rewrite using `[e, hpow _ h0 h1, h2, hpowQ _ h0.le]`. Establish `hupper : ∀ s, 0 < s → s ≤ σ → f s ≤ s ^ c`. Introduce `s hs0 hsσ`.

Break down `hsσ.lt_or_eq with hlt | heq` into its components or cases. Take `⟨J, hJ⟩` from `exists_pow_lt_of_lt_one hs0 hσ1`. Establish `hJ' : σ ^ Q ^ J < s`. Use `lt_of_le_of_lt (pow_le_pow_of_le_one hσ0.le hσ1.le ?_) hJ` and prove the remaining obligations. Conclude with `(Nat.lt_pow_self (by omega)).le`.

Take `⟨t, ht0, ht1, hst⟩` from `TeichLift.exists_interp_exponent (hσQ J).1 hJ' hlt`. Establish `h` using `hconv _ s σ t (hσQ J).1 hJ'.le hlt.le le_rfl ht0.le ht1.le hst`. Rewrite `h` using `[(hσQ J).2.2, hfσ, ← rpow_interp_eq (hσQ J).1.le hσ0.le, ← hst]`. Conclude with `h`. Rewrite using `[heq, hfσ]`.

Establish `hlower1 : ∀ s, 0 < s → s ≤ σ ^ Q → s ^ c ≤ f s`. Introduce `s hs0 hsQ`. Establish `hσQσ : σ ^ Q < σ` using `pow_lt_self_of_lt_one₀ hσ0 hσ1 (by omega)`. Break down `hsQ.lt_or_eq with hlt | heq` into its components or cases. Take `⟨t, ht0, ht1, hst⟩` from `TeichLift.exists_interp_exponent hs0 hlt hσQσ`.

Establish `h` using `hconv s (σ ^ Q) σ t hs0 hlt.le hσQσ.le le_rfl ht0.le ht1.le hst`. Establish `h1` using `(hσQ 1).2.2`. Rewrite `h1` using `[pow_one]`. Rewrite `h` using `[h1, hfσ, hst, rpow_interp_eq hs0.le hσ0.le]`. Assume the negation of the conclusion as `hcon`.

Rewrite `hcon` using `[not_le]`. Establish `hlt2 : f s ^ (1 - t) < (s ^ c) ^ (1 - t)` using `Real.rpow_lt_rpow (hpos s hs0 (hsQ.trans hσQσ.le)).le hcon (by linarith)`. Use `mul_lt_mul_of_pos_right hlt2 (Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hσ0 c) t)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h1` using `(hσQ 1).2.2`.

Rewrite `h1` using `[pow_one]`. Rewrite using `[heq, h1]`. Establish `hlower : ∀ s, 0 < s → s ≤ σ → s ^ c ≤ f s`. Introduce `s hs0 hsσ`. Break down `le_or_gt s (σ ^ Q) with h | h` into its components or cases.

Conclude with `hlower1 s hs0 h`. Establish `hsQ : s ^ Q ≤ σ ^ Q` using `pow_le_pow_left₀ hs0.le hsσ Q`. Establish `h2` using `hlower1 (s ^ Q) (pow_pos hs0 Q) hsQ`. Rewrite `h2` using `[hpow s hs0 hsσ, hpowQ s hs0.le]`. Conclude with `(pow_le_pow_iff_left₀ (Real.rpow_nonneg hs0.le c) (hpos s hs0 hsσ).le (by omega)).1 h2`.

Introduce `s hs0 hsσ`. Conclude with `le_antisymm (hupper s hs0 hsσ) (hlower s hs0 hsσ)`.
-/
theorem eq_rpow_of_logConvex {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) {Q : ℕ} (hQ : 2 ≤ Q)
    (f : ℝ → ℝ) (hpos : ∀ s, 0 < s → s ≤ σ → 0 < f s)
    (hpow : ∀ s, 0 < s → s ≤ σ → f (s ^ Q) = f s ^ Q)
    (hconv : ∀ a r b t : ℝ, 0 < a → a ≤ r → r ≤ b → b ≤ σ → 0 ≤ t → t ≤ 1 →
      r = a ^ (1 - t) * b ^ t → f r ≤ f a ^ (1 - t) * f b ^ t) :
    ∃ c : ℝ, ∀ s, 0 < s → s ≤ σ → f s = s ^ c := by
  have hlogσ : Real.log σ ≠ 0 := (Real.log_neg hσ0 hσ1).ne
  set c := Real.log (f σ) / Real.log σ with hc
  refine ⟨c, ?_⟩
  have hfσ : f σ = σ ^ c := by
    rw [Real.rpow_def_of_pos hσ0, hc, mul_div_cancel₀ _ hlogσ, Real.exp_log (hpos σ hσ0 le_rfl)]
  have hpowQ : ∀ x : ℝ, 0 ≤ x → (x ^ Q) ^ c = (x ^ c) ^ Q := by
    intro x hx
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hx, ← Real.rpow_mul hx, mul_comm]
  have hσQ : ∀ J : ℕ, 0 < σ ^ Q ^ J ∧ σ ^ Q ^ J ≤ σ ∧ f (σ ^ Q ^ J) = (σ ^ Q ^ J) ^ c := by
    intro J
    induction J with
    | zero => simp only [pow_zero, pow_one]; exact ⟨hσ0, le_rfl, hfσ⟩
    | succ J ih =>
      obtain ⟨h0, h1, h2⟩ := ih
      have e : σ ^ Q ^ (J + 1) = (σ ^ Q ^ J) ^ Q := by rw [← pow_mul, ← pow_succ]
      refine ⟨pow_pos hσ0 _, pow_le_of_le_one hσ0.le hσ1.le (by positivity), ?_⟩
      rw [e, hpow _ h0 h1, h2, hpowQ _ h0.le]

  have hupper : ∀ s, 0 < s → s ≤ σ → f s ≤ s ^ c := by
    intro s hs0 hsσ
    rcases hsσ.lt_or_eq with hlt | heq
    · obtain ⟨J, hJ⟩ := exists_pow_lt_of_lt_one hs0 hσ1
      have hJ' : σ ^ Q ^ J < s := by
        refine lt_of_le_of_lt (pow_le_pow_of_le_one hσ0.le hσ1.le ?_) hJ
        exact (Nat.lt_pow_self (by omega)).le
      obtain ⟨t, ht0, ht1, hst⟩ := TeichLift.exists_interp_exponent (hσQ J).1 hJ' hlt
      have h := hconv _ s σ t (hσQ J).1 hJ'.le hlt.le le_rfl ht0.le ht1.le hst
      rw [(hσQ J).2.2, hfσ, ← rpow_interp_eq (hσQ J).1.le hσ0.le, ← hst] at h
      exact h
    · rw [heq, hfσ]

  have hlower1 : ∀ s, 0 < s → s ≤ σ ^ Q → s ^ c ≤ f s := by
    intro s hs0 hsQ
    have hσQσ : σ ^ Q < σ := pow_lt_self_of_lt_one₀ hσ0 hσ1 (by omega)
    rcases hsQ.lt_or_eq with hlt | heq
    · obtain ⟨t, ht0, ht1, hst⟩ := TeichLift.exists_interp_exponent hs0 hlt hσQσ
      have h := hconv s (σ ^ Q) σ t hs0 hlt.le hσQσ.le le_rfl ht0.le ht1.le hst
      have h1 := (hσQ 1).2.2
      rw [pow_one] at h1
      rw [h1, hfσ, hst, rpow_interp_eq hs0.le hσ0.le] at h
      by_contra hcon
      rw [not_le] at hcon
      have hlt2 : f s ^ (1 - t) < (s ^ c) ^ (1 - t) :=
        Real.rpow_lt_rpow (hpos s hs0 (hsQ.trans hσQσ.le)).le hcon (by linarith)
      have := mul_lt_mul_of_pos_right hlt2 (Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hσ0 c) t)
      linarith
    · have h1 := (hσQ 1).2.2
      rw [pow_one] at h1
      rw [heq, h1]
  have hlower : ∀ s, 0 < s → s ≤ σ → s ^ c ≤ f s := by
    intro s hs0 hsσ
    rcases le_or_gt s (σ ^ Q) with h | h
    · exact hlower1 s hs0 h
    · have hsQ : s ^ Q ≤ σ ^ Q := pow_le_pow_left₀ hs0.le hsσ Q
      have h2 := hlower1 (s ^ Q) (pow_pos hs0 Q) hsQ
      rw [hpow s hs0 hsσ, hpowQ s hs0.le] at h2
      exact (pow_le_pow_iff_left₀ (Real.rpow_nonneg hs0.le c) (hpos s hs0 hsσ).le
        (by omega)).1 h2
  intro s hs0 hsσ
  exact le_antisymm (hupper s hs0 hsσ) (hlower s hs0 hsσ)

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] {T : TeichLift p L Γ}

/- English proof (translation)
Use `show T.ofRad fixRad ((1 : T.Econ fixRad) : T.RobbaExt fixRad) = 1`. Rewrite using `[Completion.coe_one, map_one]`.
-/
theorem tildeOf_one : T.tildeOf 1 (by simpa using (convAll_π_pow (T := T) 0)) = 1 := by
  show T.ofRad fixRad ((1 : T.Econ fixRad) : T.RobbaExt fixRad) = 1
  rw [Completion.coe_one, map_one]

namespace TeichFrob

variable (F : T.TeichFrob)

/- English proof (translation)
Take `⟨σ, x₀, rfl⟩` from `T.exists_ofRad x`. Use `⟨σ, x₀, rfl, T.ofRad_injective (F.powRadius σ) ?_⟩` and prove the remaining obligations. Rewrite using `[← F.tildeFrob_ofRad, hx, T.ofRad_res]`.
-/
theorem exists_ofRad_of_fixed {x : T.RobbaTilde} (hx : F.tildeFrob x = x) :
    ∃ σ : Set.Ioo (0 : ℝ) 1, ∃ x₀ : T.RobbaExt σ, T.ofRad σ x₀ = x ∧
      F.extFrob σ x₀ = T.res (F.powRadius_le_self σ) x₀ := by
  obtain ⟨σ, x₀, rfl⟩ := T.exists_ofRad x
  refine ⟨σ, x₀, rfl, T.ofRad_injective (F.powRadius σ) ?_⟩
  rw [← F.tildeFrob_ofRad, hx, T.ofRad_res]

/- English proof (translation)
Establish `h1` using `F.extNorm_extFrob σ r x₀`. Rewrite `h1` using `[h, extNorm_res]`. Conclude with `h1`.
-/
theorem extNorm_pow_of_fixed {σ : Set.Ioo (0 : ℝ) 1} {x₀ : T.RobbaExt σ}
    (h : F.extFrob σ x₀ = T.res (F.powRadius_le_self σ) x₀) (r : Set.Ioc (0 : ℝ) σ) :
    T.extNorm σ ⟨(r : ℝ) ^ p ^ F.a, pow_pos r.2.1 _,
      (pow_le_of_le_one r.2.1.le (r.2.2.trans σ.2.2.le) F.q_pos.ne').trans r.2.2⟩ x₀ =
      T.extNorm σ r x₀ ^ p ^ F.a := by
  have h1 := F.extNorm_extFrob σ r x₀
  rw [h, extNorm_res] at h1
  exact h1

/- English proof (translation)
Use `show F.tildeFrob (T.ofRad σ ((⟨b, hb⟩ : T.Econ σ) : T.RobbaExt σ)) = T.ofRad (F.powRadius σ) ((⟨F.toB b, F.toB_mem_Econ_iff.2 hb⟩ : T.Econ (F.powRadius σ)) : T.RobbaExt (F.powRadius σ))`. Rewrite using `[F.tildeFrob_ofRad, F.extFrob_coe]`. Both sides reduce to the same expression.
-/
theorem tildeFrob_econToTilde (σ : Set.Ioo (0 : ℝ) 1) {b : T.B} (hb : b ∈ T.Econ σ) :
    F.tildeFrob (T.econToTilde σ ⟨b, hb⟩) =
      T.econToTilde (F.powRadius σ) ⟨F.toB b, F.toB_mem_Econ_iff.2 hb⟩ := by
  show F.tildeFrob (T.ofRad σ ((⟨b, hb⟩ : T.Econ σ) : T.RobbaExt σ)) =
    T.ofRad (F.powRadius σ) ((⟨F.toB b, F.toB_mem_Econ_iff.2 hb⟩ : T.Econ (F.powRadius σ)) :
      T.RobbaExt (F.powRadius σ))
  rw [F.tildeFrob_ofRad, F.extFrob_coe]
  rfl

/- English proof (translation)
Take `⟨σ, x₀, hxσ, hfix⟩` from `F.exists_ofRad_of_fixed hx`. Establish `hσ0 : (0 : ℝ) < σ` using `σ.2.1`. Establish `hσ1 : (σ : ℝ) < 1` using `σ.2.2`. Establish `hx₀ : x₀ ≠ 0` using `fun h => hx0 (by rw [← hxσ, h, map_zero])`. Use `set Q : ℕ := p ^ F.a with hQ`.

Establish `hQ2 : 2 ≤ Q`. Use `hp.out.two_le` as an intermediate fact. Combine the equalities or inequalities in the displayed calculation. Set `f : ℝ → ℝ` to `fun s => if h : 0 < s ∧ s ≤ σ then T.extNorm σ ⟨s, h.1, h.2⟩ x₀ else 0`. Establish `hf : ∀ (s : ℝ) (h0 : 0 < s) (h1 : s ≤ σ), f s = T.extNorm σ ⟨s, h0, h1⟩ x₀`.

Introduce `s h0 h1`. Simplify using `only [f, dif_pos (And.intro h0 h1)]`. Take `⟨c, hc⟩` from `eq_rpow_of_logConvex hσ0 hσ1 hQ2 f (fun s h0 h1 => by rw [hf s h0 h1]; exact T.extNorm_pos hx₀ _) (fun s h0 h1 => by`. Establish `hs1 : s ^ Q ≤ σ` using `(pow_le_of_le_one h0.le (h1.trans hσ1.le) (by omega)).trans h1`. Rewrite using `[hf _ (pow_pos h0 Q) hs1, hf s h0 h1]`.

Conclude with `F.extNorm_pow_of_fixed hfix ⟨s, h0, h1⟩)`. Use the proof step `(fun a r b t ha0 har hrb hbσ ht0 ht1 hr => by`. Rewrite using `[hf a ha0 (har.trans (hrb.trans hbσ)), hf r (ha0.trans_le har) (hrb.trans hbσ), hf b (ha0.trans_le (har.trans hrb)) hbσ]`. Conclude with `T.extNorm_interp_le _ _ _ ht0 ht1 hr x₀)`. Establish `hN : ∀ s : Set.Ioc (0 : ℝ) σ, T.extNorm σ s x₀ = (s : ℝ) ^ c`.

Introduce `s`. Use `hc s s.2.1 s.2.2` as an intermediate fact. Rewrite `this` using `[hf s s.2.1 s.2.2]`. Then use the resulting hypothesis. Use `set Pu : T.B := T.πB * algebraMap Γ T.B z with hPudef`. Establish `hPu : T.IsUnitTerm Pu 1` using `⟨z, hz, hz1, by rw [zpow_one]⟩`.

Establish `hPuφ : F.toB Pu = Pu`. Rewrite using `[hPudef, πB, ← map_mul, F.toB_algebraMap, hzφ]`. Use `set m : ℤ := ⌊c⌋ with hm`. Establish `hP` using `hPu.zpow (-m)`. Establish `hPc : T.ConvAll (Pu ^ (-m))` using `hP.convAll`.

Establish `hPnorm : ∀ s : ℝ, 0 < s → s < 1 → gaussNorm (T.coeffB (Pu ^ (-m))) s = s ^ (-m : ℝ)`. Introduce `s h0 h1`. Use `hP.gaussNorm_mul_teich 1 h0 h1` as an intermediate fact. Rewrite `this` using `[T.teich_one, map_one, mul_one, norm_one, mul_one, mul_one]`. Rewrite using `[this, ← Real.rpow_intCast]`.

Use `push_cast`. Put the polynomial expressions in normal form. Use `set d : ℝ := c - m with hd`. Establish `hd0 : 0 ≤ d` using `by rw [hd]; linarith [Int.floor_le c]`. Establish `hd1 : d < 1` using `by rw [hd]; linarith [Int.lt_floor_add_one c]`.

Use `set y := T.ofAll _ hPc σ * x₀ with hy`. Establish `hyN : ∀ s : Set.Ioc (0 : ℝ) σ, T.extNorm σ s y = (s : ℝ) ^ d`. Introduce `s`. Establish `hs0 : (0 : ℝ) < s` using `s.2.1`. Rewrite using `[hy, extNorm_mul, extNorm_ofAll, hPnorm s hs0 (s.2.2.trans_lt hσ1), hN s, ← Real.rpow_add hs0, hd]`.

Put the polynomial expressions in normal form. Take `⟨w, hwE, hw⟩` from `exists_gamma_of_extNorm_le y (C := 1) (β := 0) 0 (by norm_num) (fun s => by`. Rewrite using `[hyN s, neg_zero, Real.rpow_zero, one_mul]`. Conclude with `Real.rpow_le_one s.2.1.le (s.2.2.trans hσ1.le) hd0)`. Rewrite `hw` using `[← πExt_pow_eq_ofAll, _root_.pow_zero, one_mul]`.

Use `set bw : T.B := algebraMap Γ T.B w with hbw`. Establish `hwc : ConvergesAt (T.zcoeff w) σ`. Use `(T.mem_Econ).1 hwE` as an intermediate fact. Rewrite `this` using `[coeffB_algebraMap]`. Then use the resulting hypothesis. Establish `hwN : ∀ s : Set.Ioc (0 : ℝ) σ, gaussNorm (T.zcoeff w) s = (s : ℝ) ^ d`.

Introduce `s`. Rewrite using `[← hyN s, hw, extNorm_coe, coeffB_algebraMap]`. Establish `hd_eq : d = 0`. Assume the negation of the conclusion as `hdne`. Establish `hdpos : 0 < d` using `lt_of_le_of_ne hd0 (Ne.symm hdne)`.

Establish `hw0 : T.coeff w 0 = 0`. Assume the negation of the conclusion as `h0`. Establish `hpos : 0 < ‖T.coeff w 0‖` using `norm_pos_iff.2 h0`. Take `⟨t, ht0, htσ, htC⟩` from `exists_rpow_small hσ0 hdpos zero_le_one (half_pos hpos)`. Establish `h1` using `T.weight_natCast_le (convergesAt_of_le (T.zcoeff_neg_exists w) hwc ht0 htσ) 0`.

Rewrite `h1` using `[hwN ⟨t, ht0, htσ⟩]`. Simplify using `only [Nat.cast_zero, zpow_zero, mul_one] at h1`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hs2 : (0 : ℝ) < σ / 2` using `by positivity`. Establish `hs2σ : (σ : ℝ) / 2 ≤ σ` using `by linarith`.

Establish `hbound : gaussNorm (T.zcoeff w) (σ / 2) ≤ (1 / 2) * gaussNorm (T.zcoeff w) σ`. Use `gaussNorm_le fun n => ?_` and prove the remaining obligations. Establish `hG : 0 ≤ gaussNorm (T.zcoeff w) σ` using `gaussNorm_nonneg hσ0`. Break down `lt_or_ge n 1 with hn | hn` into its components or cases. Break down `lt_or_ge n 0 with hn0 | hn0` into its components or cases.

Rewrite using `[T.zcoeff_of_neg _ hn0, norm_zero, zero_mul]`. Check the signs of the components of the expression. Establish `: n = ((0 : ℕ) : ℤ)` using `by omega`. Rewrite using `[this, T.zcoeff_natCast, hw0, norm_zero, zero_mul]`. Check the signs of the components of the expression.

Establish `h1` using `hwc.le_gaussNorm n`. Establish `h2 : ((σ : ℝ) / 2) ^ n ≤ (1 / 2) * (σ : ℝ) ^ n`. Rewrite using `[div_eq_mul_one_div, mul_zpow, mul_comm]`. Use `mul_le_mul_of_nonneg_right ?_ (zpow_pos hσ0 n).le` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Combine the equalities or inequalities in the displayed calculation. Establish `hσN : gaussNorm (T.zcoeff w) σ = (σ : ℝ) ^ d` using `hwN (topRad σ)`. Establish `h2N : gaussNorm (T.zcoeff w) ((σ : ℝ) / 2) = ((σ : ℝ) / 2) ^ d` using `hwN ⟨σ / 2, Set.mem_Ioc.2 ⟨hs2, hs2σ⟩⟩`. Rewrite `hbound` using `[h2N, hσN]`. Rewrite `hbound` using `[Real.div_rpow hσ0.le (by norm_num)]`.

Establish `h2d : (2 : ℝ) ^ d < 2`. Combine the equalities or inequalities in the displayed calculation. Establish `hσd : 0 < (σ : ℝ) ^ d` using `Real.rpow_pos_of_pos hσ0 d`. Establish `h2pos : 0 < (2 : ℝ) ^ d` using `Real.rpow_pos_of_pos (by norm_num) d`. Rewrite `hbound` using `[div_le_iff₀ h2pos]`.

Use the polynomial consequences of the given equalities and inequalities. Establish `hcm : c = m` using `by linarith`. Establish `hwN1 : ∀ s : Set.Ioc (0 : ℝ) σ, gaussNorm (T.zcoeff w) s = 1` using `fun s => by`. Rewrite using `[hwN s, hd_eq, Real.rpow_zero]`. Establish `hxR : T.tildeOf _ hPc * x = T.econToTilde σ ⟨bw, hwE⟩`.

Rewrite using `[T.tildeOf_eq _ hPc σ, ← hxσ, ← map_mul, ← hy, hw]`. Both sides reduce to the same expression. Establish `hwφ : F.φ w = w`. Establish `h1 : F.tildeFrob (T.tildeOf _ hPc * x) = T.tildeOf _ hPc * x`. Rewrite using `[map_mul, hx, F.tildeFrob_tildeOf]`.

Use `congr 1`. Conclude with `T.tildeOf_congr _ _ (by rw [map_zpow₀, hPuφ])`. Rewrite `h1` using `[hxR, F.tildeFrob_econToTilde, T.econToTilde_eq _ (T.Econ_anti (F.powRadius_le_self σ) hwE)]`. Establish `h2` using `congrArg Subtype.val (T.econToTilde_injective _ h1)`. Simplify using `only [hbw, F.toB_algebraMap] at h2`.

Conclude with `T.algebraMap_injective h2`. Establish `htoB : F.toB bw = bw` using `by rw [hbw, F.toB_algebraMap, hwφ]`. Establish `hall : ∀ k : ℕ, ∀ ρ : Set.Ioo (0 : ℝ) 1, (ρ : ℝ) ^ Q ^ k ≤ σ → bw ∈ T.Econ ρ ∧ gaussNorm (T.coeffB bw) ρ = 1`. Introduce `k`. Proceed by induction on `k with`.

Consider the case `zero`. Introduce `ρ hρ`. Rewrite `hρ` using `[_root_.pow_zero, pow_one]`. Use `⟨T.Econ_anti hρ hwE, ?_⟩` and prove the remaining obligations. Rewrite using `[hbw, coeffB_algebraMap]`.

Conclude with `hwN1 ⟨ρ, ρ.2.1, hρ⟩`. Consider the case `succ k ih`. Introduce `ρ hρ`. Establish `h1 : ((F.powRadius ρ : Set.Ioo (0 : ℝ) 1) : ℝ) ^ Q ^ k ≤ σ` using `by show ((ρ : ℝ) ^ p ^ F.a) ^ Q ^ k ≤ σ`. Rewrite using `[← pow_mul, ← _root_.pow_succ']`.

Conclude with `hρ`. Take `⟨hE, hn⟩` from `ih _ h1`. Use `⟨F.toB_mem_Econ_iff.1 (by rw [htoB]; exact hE), ?_⟩` and prove the remaining obligations. Establish `h2` using `F.gaussNorm_toB_pow ρ.2.1 ρ.2.2 (F.toB_mem_Econ_iff.1 (by rw [htoB]; exact hE))`. Rewrite `h2` using `[htoB]`.

Express the relevant statement in the definitionally equal form `gaussNorm (T.coeffB bw) ((ρ : ℝ) ^ p ^ F.a) = _ at hn`. Rewrite `h2` using `[hn]`. Conclude with `((pow_eq_one_iff_of_nonneg (gaussNorm_nonneg ρ.2.1) (by positivity)).1 h2.symm)`. Establish `hall' : ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ConvergesAt (T.zcoeff w) ρ ∧ gaussNorm (T.zcoeff w) ρ = 1`. Introduce `ρ h0 h1`.

Take `⟨k, hk⟩` from `exists_pow_lt_of_lt_one hσ0 h1`. Establish `hk' : ρ ^ Q ^ k ≤ σ` using `(pow_le_pow_of_le_one h0.le h1.le (Nat.lt_pow_self (by omega)).le).trans hk.le`. Take `⟨hE, hn⟩` from `hall k ⟨ρ, h0, h1⟩ hk'`. Rewrite `hn` using `[hbw, coeffB_algebraMap]`. Use `⟨?_, hn⟩` and prove the remaining obligations.

Use `(T.mem_Econ).1 hE` as an intermediate fact. Rewrite `this` using `[hbw, coeffB_algebraMap]`. Then use the resulting hypothesis. Establish `hwint : w ∈ T.int`. Use `T.mem_int_iff.2 fun n => norm_le_one_of_forall_weight_le (n := n) fun ρ h0 h1 => ?_` and prove the remaining obligations. Establish `h` using `T.weight_natCast_le (hall' ρ h0 h1).1 n`.

Rewrite `h` using `[(hall' ρ h0 h1).2, zpow_natCast]`. Then use the resulting hypothesis. Establish `hwred : ‖T.red w‖ = 1`. Use `le_antisymm (T.norm_red_le_one w hwint) ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hlt`. Rewrite `hlt` using `[not_le]`.

Establish `hG : gaussNorm (T.zcoeff w) (1 / 2) ≤ max ‖T.red w‖ (1 / 2)`. Use `gaussNorm_le fun n => ?_` and prove the remaining obligations. Break down `lt_or_ge n 0 with hn0 | hn0` into its components or cases. Rewrite using `[T.zcoeff_of_neg _ hn0, norm_zero, zero_mul]`. Check the signs of the components of the expression.

Take `⟨k, rfl⟩ : ∃ k : ℕ, n = k` from `⟨n.toNat, (Int.toNat_of_nonneg hn0).symm⟩`. Rewrite using `[T.zcoeff_natCast, zpow_natCast]`. Break down `k with _ | k` into its components or cases. Rewrite using `[_root_.pow_zero, mul_one, T.coeff_zero]`. Conclude with `le_max_left _ _`.

Use `le_max_of_le_right ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[one_mul]`. Conclude with `pow_le_of_le_one (by norm_num) (by norm_num) (by omega) |>.trans (by norm_num)`. Rewrite `hG` using `[(hall' (1 / 2) (by norm_num) (by norm_num)).2]`.

Establish `: max ‖T.red w‖ (1 / 2) < 1` using `max_lt hlt (by norm_num)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hbwc : T.ConvAll bw` using `fun ρ h0 h1 => by`. Rewrite using `[hbw, coeffB_algebraMap]`. Conclude with `(hall' ρ h0 h1).1`.

Use `⟨m, w, hwint, hwred, hwφ, ((hPu.zpow m).convAll).mul hbwc, ?_⟩` and prove the remaining obligations. Establish `hbwT : T.econToTilde σ ⟨bw, hwE⟩ = T.tildeOf bw hbwc`. Rewrite using `[T.tildeOf_eq _ hbwc σ]`. Both sides reduce to the same expression. Rewrite `hxR` using `[hbwT]`.

Establish `hone : T.tildeOf (Pu ^ m) (hPu.zpow m).convAll * T.tildeOf _ hPc = 1`. Rewrite using `[← tildeOf_mul, ← tildeOf_one]`. Conclude with `T.tildeOf_congr _ _ (by rw [← zpow_add₀ hPu.ne_zero, add_neg_cancel, zpow_zero])`. Rewrite using `[tildeOf_mul (hPu.zpow m).convAll hbwc, ← hxR, ← mul_assoc, hone, one_mul]`.
-/
theorem exists_eq_zpow_mul_of_fixed [CompleteSpace L] (ha : 0 < F.a) {z : Γ} (hz : z ∈ T.int)
    (hz1 : ‖T.red z‖ = 1) (hzφ : F.φ (T.π * z) = T.π * z) {x : T.RobbaTilde} (hx0 : x ≠ 0)
    (hx : F.tildeFrob x = x) :
    ∃ (c : ℤ) (u : Γ), u ∈ T.int ∧ ‖T.red u‖ = 1 ∧ F.φ u = u ∧
      ∃ h : T.ConvAll ((T.πB * algebraMap Γ T.B z) ^ c * algebraMap Γ T.B u),
        x = T.tildeOf _ h := by
  obtain ⟨σ, x₀, hxσ, hfix⟩ := F.exists_ofRad_of_fixed hx
  have hσ0 : (0 : ℝ) < σ := σ.2.1
  have hσ1 : (σ : ℝ) < 1 := σ.2.2
  have hx₀ : x₀ ≠ 0 := fun h => hx0 (by rw [← hxσ, h, map_zero])
  set Q : ℕ := p ^ F.a with hQ
  have hQ2 : 2 ≤ Q := by
    have := hp.out.two_le
    calc 2 ≤ p := this
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ F.a := Nat.pow_le_pow_right hp.out.pos ha

  let f : ℝ → ℝ := fun s => if h : 0 < s ∧ s ≤ σ then T.extNorm σ ⟨s, h.1, h.2⟩ x₀ else 0
  have hf : ∀ (s : ℝ) (h0 : 0 < s) (h1 : s ≤ σ), f s = T.extNorm σ ⟨s, h0, h1⟩ x₀ := by
    intro s h0 h1; simp only [f, dif_pos (And.intro h0 h1)]
  obtain ⟨c, hc⟩ := eq_rpow_of_logConvex hσ0 hσ1 hQ2 f
    (fun s h0 h1 => by rw [hf s h0 h1]; exact T.extNorm_pos hx₀ _)
    (fun s h0 h1 => by
      have hs1 : s ^ Q ≤ σ :=
        (pow_le_of_le_one h0.le (h1.trans hσ1.le) (by omega)).trans h1
      rw [hf _ (pow_pos h0 Q) hs1, hf s h0 h1]
      exact F.extNorm_pow_of_fixed hfix ⟨s, h0, h1⟩)
    (fun a r b t ha0 har hrb hbσ ht0 ht1 hr => by
      rw [hf a ha0 (har.trans (hrb.trans hbσ)), hf r (ha0.trans_le har) (hrb.trans hbσ),
        hf b (ha0.trans_le (har.trans hrb)) hbσ]
      exact T.extNorm_interp_le _ _ _ ht0 ht1 hr x₀)
  have hN : ∀ s : Set.Ioc (0 : ℝ) σ, T.extNorm σ s x₀ = (s : ℝ) ^ c := by
    intro s
    have := hc s s.2.1 s.2.2
    rwa [hf s s.2.1 s.2.2] at this

  set Pu : T.B := T.πB * algebraMap Γ T.B z with hPudef
  have hPu : T.IsUnitTerm Pu 1 := ⟨z, hz, hz1, by rw [zpow_one]⟩
  have hPuφ : F.toB Pu = Pu := by
    rw [hPudef, πB, ← map_mul, F.toB_algebraMap, hzφ]
  set m : ℤ := ⌊c⌋ with hm
  have hP := hPu.zpow (-m)
  have hPc : T.ConvAll (Pu ^ (-m)) := hP.convAll
  have hPnorm : ∀ s : ℝ, 0 < s → s < 1 → gaussNorm (T.coeffB (Pu ^ (-m))) s = s ^ (-m : ℝ) := by
    intro s h0 h1
    have := hP.gaussNorm_mul_teich 1 h0 h1
    rw [T.teich_one, map_one, mul_one, norm_one, mul_one, mul_one] at this
    rw [this, ← Real.rpow_intCast]
    push_cast
    ring_nf
  set d : ℝ := c - m with hd
  have hd0 : 0 ≤ d := by rw [hd]; linarith [Int.floor_le c]
  have hd1 : d < 1 := by rw [hd]; linarith [Int.lt_floor_add_one c]
  set y := T.ofAll _ hPc σ * x₀ with hy
  have hyN : ∀ s : Set.Ioc (0 : ℝ) σ, T.extNorm σ s y = (s : ℝ) ^ d := by
    intro s
    have hs0 : (0 : ℝ) < s := s.2.1
    rw [hy, extNorm_mul, extNorm_ofAll, hPnorm s hs0 (s.2.2.trans_lt hσ1), hN s,
      ← Real.rpow_add hs0, hd]
    ring_nf
  obtain ⟨w, hwE, hw⟩ := exists_gamma_of_extNorm_le y (C := 1) (β := 0) 0 (by norm_num)
    (fun s => by
      rw [hyN s, neg_zero, Real.rpow_zero, one_mul]
      exact Real.rpow_le_one s.2.1.le (s.2.2.trans hσ1.le) hd0)
  rw [← πExt_pow_eq_ofAll, _root_.pow_zero, one_mul] at hw
  set bw : T.B := algebraMap Γ T.B w with hbw
  have hwc : ConvergesAt (T.zcoeff w) σ := by
    have := (T.mem_Econ).1 hwE
    rwa [coeffB_algebraMap] at this
  have hwN : ∀ s : Set.Ioc (0 : ℝ) σ, gaussNorm (T.zcoeff w) s = (s : ℝ) ^ d := by
    intro s
    rw [← hyN s, hw, extNorm_coe, coeffB_algebraMap]

  have hd_eq : d = 0 := by
    by_contra hdne
    have hdpos : 0 < d := lt_of_le_of_ne hd0 (Ne.symm hdne)
    have hw0 : T.coeff w 0 = 0 := by
      by_contra h0
      have hpos : 0 < ‖T.coeff w 0‖ := norm_pos_iff.2 h0
      obtain ⟨t, ht0, htσ, htC⟩ := exists_rpow_small hσ0 hdpos zero_le_one (half_pos hpos)
      have h1 := T.weight_natCast_le (convergesAt_of_le (T.zcoeff_neg_exists w) hwc ht0 htσ) 0
      rw [hwN ⟨t, ht0, htσ⟩] at h1
      simp only [Nat.cast_zero, zpow_zero, mul_one] at h1
      linarith
    have hs2 : (0 : ℝ) < σ / 2 := by positivity
    have hs2σ : (σ : ℝ) / 2 ≤ σ := by linarith
    have hbound : gaussNorm (T.zcoeff w) (σ / 2) ≤ (1 / 2) * gaussNorm (T.zcoeff w) σ := by
      refine gaussNorm_le fun n => ?_
      have hG : 0 ≤ gaussNorm (T.zcoeff w) σ := gaussNorm_nonneg hσ0
      rcases lt_or_ge n 1 with hn | hn
      · rcases lt_or_ge n 0 with hn0 | hn0
        · rw [T.zcoeff_of_neg _ hn0, norm_zero, zero_mul]; positivity
        · have : n = ((0 : ℕ) : ℤ) := by omega
          rw [this, T.zcoeff_natCast, hw0, norm_zero, zero_mul]; positivity
      · have h1 := hwc.le_gaussNorm n
        have h2 : ((σ : ℝ) / 2) ^ n ≤ (1 / 2) * (σ : ℝ) ^ n := by
          rw [div_eq_mul_one_div, mul_zpow, mul_comm]
          refine mul_le_mul_of_nonneg_right ?_ (zpow_pos hσ0 n).le
          calc (1 / 2 : ℝ) ^ n ≤ (1 / 2 : ℝ) ^ (1 : ℤ) :=
                zpow_le_zpow_right_of_le_one₀ (by norm_num) (by norm_num) hn
            _ = 1 / 2 := zpow_one _
        calc ‖T.zcoeff w n‖ * ((σ : ℝ) / 2) ^ n ≤ ‖T.zcoeff w n‖ * ((1 / 2) * (σ : ℝ) ^ n) :=
              mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
          _ = (1 / 2) * (‖T.zcoeff w n‖ * (σ : ℝ) ^ n) := by ring
          _ ≤ (1 / 2) * gaussNorm (T.zcoeff w) σ := mul_le_mul_of_nonneg_left h1 (by norm_num)
    have hσN : gaussNorm (T.zcoeff w) σ = (σ : ℝ) ^ d := hwN (topRad σ)
    have h2N : gaussNorm (T.zcoeff w) ((σ : ℝ) / 2) = ((σ : ℝ) / 2) ^ d :=
      hwN ⟨σ / 2, Set.mem_Ioc.2 ⟨hs2, hs2σ⟩⟩
    rw [h2N, hσN] at hbound
    rw [Real.div_rpow hσ0.le (by norm_num)] at hbound
    have h2d : (2 : ℝ) ^ d < 2 := by
      calc (2 : ℝ) ^ d < 2 ^ (1 : ℝ) := Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hd1
        _ = 2 := Real.rpow_one 2
    have hσd : 0 < (σ : ℝ) ^ d := Real.rpow_pos_of_pos hσ0 d
    have h2pos : 0 < (2 : ℝ) ^ d := Real.rpow_pos_of_pos (by norm_num) d
    rw [div_le_iff₀ h2pos] at hbound
    nlinarith
  have hcm : c = m := by linarith
  have hwN1 : ∀ s : Set.Ioc (0 : ℝ) σ, gaussNorm (T.zcoeff w) s = 1 := fun s => by
    rw [hwN s, hd_eq, Real.rpow_zero]

  have hxR : T.tildeOf _ hPc * x = T.econToTilde σ ⟨bw, hwE⟩ := by
    rw [T.tildeOf_eq _ hPc σ, ← hxσ, ← map_mul, ← hy, hw]
    rfl
  have hwφ : F.φ w = w := by
    have h1 : F.tildeFrob (T.tildeOf _ hPc * x) = T.tildeOf _ hPc * x := by
      rw [map_mul, hx, F.tildeFrob_tildeOf]
      congr 1
      exact T.tildeOf_congr _ _ (by rw [map_zpow₀, hPuφ])
    rw [hxR, F.tildeFrob_econToTilde,
      T.econToTilde_eq _ (T.Econ_anti (F.powRadius_le_self σ) hwE)] at h1
    have h2 := congrArg Subtype.val (T.econToTilde_injective _ h1)
    simp only [hbw, F.toB_algebraMap] at h2
    exact T.algebraMap_injective h2
  have htoB : F.toB bw = bw := by rw [hbw, F.toB_algebraMap, hwφ]

  have hall : ∀ k : ℕ, ∀ ρ : Set.Ioo (0 : ℝ) 1, (ρ : ℝ) ^ Q ^ k ≤ σ →
      bw ∈ T.Econ ρ ∧ gaussNorm (T.coeffB bw) ρ = 1 := by
    intro k
    induction k with
    | zero =>
      intro ρ hρ
      rw [_root_.pow_zero, pow_one] at hρ
      refine ⟨T.Econ_anti hρ hwE, ?_⟩
      rw [hbw, coeffB_algebraMap]; exact hwN1 ⟨ρ, ρ.2.1, hρ⟩
    | succ k ih =>
      intro ρ hρ
      have h1 : ((F.powRadius ρ : Set.Ioo (0 : ℝ) 1) : ℝ) ^ Q ^ k ≤ σ := by
        show ((ρ : ℝ) ^ p ^ F.a) ^ Q ^ k ≤ σ
        rw [← pow_mul, ← _root_.pow_succ']; exact hρ
      obtain ⟨hE, hn⟩ := ih _ h1
      refine ⟨F.toB_mem_Econ_iff.1 (by rw [htoB]; exact hE), ?_⟩
      have h2 := F.gaussNorm_toB_pow ρ.2.1 ρ.2.2 (F.toB_mem_Econ_iff.1 (by rw [htoB]; exact hE))
      rw [htoB] at h2
      change gaussNorm (T.coeffB bw) ((ρ : ℝ) ^ p ^ F.a) = _ at hn
      rw [hn] at h2
      exact ((pow_eq_one_iff_of_nonneg (gaussNorm_nonneg ρ.2.1) (by positivity)).1 h2.symm)
  have hall' : ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ConvergesAt (T.zcoeff w) ρ ∧ gaussNorm (T.zcoeff w) ρ = 1 := by
    intro ρ h0 h1
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hσ0 h1
    have hk' : ρ ^ Q ^ k ≤ σ :=
      (pow_le_pow_of_le_one h0.le h1.le (Nat.lt_pow_self (by omega)).le).trans hk.le
    obtain ⟨hE, hn⟩ := hall k ⟨ρ, h0, h1⟩ hk'
    rw [hbw, coeffB_algebraMap] at hn
    refine ⟨?_, hn⟩
    have := (T.mem_Econ).1 hE
    rwa [hbw, coeffB_algebraMap] at this

  have hwint : w ∈ T.int := by
    refine T.mem_int_iff.2 fun n => norm_le_one_of_forall_weight_le (n := n) fun ρ h0 h1 => ?_
    have h := T.weight_natCast_le (hall' ρ h0 h1).1 n
    rwa [(hall' ρ h0 h1).2, zpow_natCast] at h
  have hwred : ‖T.red w‖ = 1 := by
    refine le_antisymm (T.norm_red_le_one w hwint) ?_
    by_contra hlt
    rw [not_le] at hlt
    have hG : gaussNorm (T.zcoeff w) (1 / 2) ≤ max ‖T.red w‖ (1 / 2) := by
      refine gaussNorm_le fun n => ?_
      rcases lt_or_ge n 0 with hn0 | hn0
      · rw [T.zcoeff_of_neg _ hn0, norm_zero, zero_mul]; positivity
      · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k := ⟨n.toNat, (Int.toNat_of_nonneg hn0).symm⟩
        rw [T.zcoeff_natCast, zpow_natCast]
        rcases k with _ | k
        · rw [_root_.pow_zero, mul_one, T.coeff_zero]; exact le_max_left _ _
        · refine le_max_of_le_right ?_
          calc ‖T.coeff w (k + 1)‖ * (1 / 2 : ℝ) ^ (k + 1) ≤ 1 * (1 / 2 : ℝ) ^ (k + 1) :=
                mul_le_mul_of_nonneg_right (T.mem_int_iff.1 hwint _) (by positivity)
            _ ≤ 1 / 2 := by
                rw [one_mul]
                exact pow_le_of_le_one (by norm_num) (by norm_num) (by omega) |>.trans
                  (by norm_num)
    rw [(hall' (1 / 2) (by norm_num) (by norm_num)).2] at hG
    have : max ‖T.red w‖ (1 / 2) < 1 := max_lt hlt (by norm_num)
    linarith

  have hbwc : T.ConvAll bw := fun ρ h0 h1 => by
    rw [hbw, coeffB_algebraMap]; exact (hall' ρ h0 h1).1
  refine ⟨m, w, hwint, hwred, hwφ, ((hPu.zpow m).convAll).mul hbwc, ?_⟩
  have hbwT : T.econToTilde σ ⟨bw, hwE⟩ = T.tildeOf bw hbwc := by
    rw [T.tildeOf_eq _ hbwc σ]; rfl
  rw [hbwT] at hxR
  have hone : T.tildeOf (Pu ^ m) (hPu.zpow m).convAll * T.tildeOf _ hPc = 1 := by
    rw [← tildeOf_mul, ← tildeOf_one]
    exact T.tildeOf_congr _ _ (by rw [← zpow_add₀ hPu.ne_zero, add_neg_cancel, zpow_zero])
  rw [tildeOf_mul (hPu.zpow m).convAll hbwc, ← hxR, ← mul_assoc, hone, one_mul]

end TeichFrob

end TeichLift

end GroundTheory.PAdicHodge
