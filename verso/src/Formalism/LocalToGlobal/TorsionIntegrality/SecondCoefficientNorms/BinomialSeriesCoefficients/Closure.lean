import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.PhNormClosed
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.Points
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.SecondCoeffConsistency

noncomputable section
open scoped BigOperators
open Finset

namespace Formalism.L2.Th1.C

namespace Clo

section Cont

variable {K : Type} [Field K] {σ : Type}

/- English proof (translation)
The claim follows from `MvPowerSeries.coeff_eq_zero_of_constantCoeff_nilpotent (m := 1) (by simpa using hf) (by omega)`.
-/
theorem coeff_pow_zero {f : MvPowerSeries σ K} (hf : MvPowerSeries.constantCoeff f = 0)
    {n : σ →₀ ℕ} {k : ℕ} (h : n.degree < k) : MvPowerSeries.coeff n (f ^ k) = 0 :=
  MvPowerSeries.coeff_eq_zero_of_constantCoeff_nilpotent (m := 1) (by simpa using hf) (by omega)

/- English proof (translation)
Rewrite using `[PowerSeries.coeff_subst (Pts.hasSubst hf), finsum_eq_sum_of_support_subset (s := range (n.degree + 1))]`. Conclude with `Finset.sum_congr rfl fun k _ => by rw [smul_eq_mul]`. Introduce `k hk`. Simplify using `only [Function.mem_support] at hk`. Simplify using `only [Finset.coe_range, Set.mem_Iio]`.

Assume the negation of the conclusion as `hlt`. Apply `hk` to reduce the goal to its premises. Rewrite using `[coeff_pow_zero hf (by omega), smul_zero]`.
-/
theorem coeff_subst_range {f : MvPowerSeries σ K} (hf : MvPowerSeries.constantCoeff f = 0)
    (g : PowerSeries K) (n : σ →₀ ℕ) :
    MvPowerSeries.coeff n (PowerSeries.subst f g) =
      ∑ k ∈ range (n.degree + 1), PowerSeries.coeff k g * MvPowerSeries.coeff n (f ^ k) := by
  classical
  rw [PowerSeries.coeff_subst (Pts.hasSubst hf),
    finsum_eq_sum_of_support_subset (s := range (n.degree + 1))]
  · exact Finset.sum_congr rfl fun k _ => by rw [smul_eq_mul]
  · intro k hk
    simp only [Function.mem_support] at hk
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hlt
    apply hk
    rw [coeff_pow_zero hf (by omega), smul_zero]

variable [TopologicalSpace K] [IsTopologicalRing K] {T : Type} [TopologicalSpace T]

def CoeffCont (f : T → MvPowerSeries σ K) : Prop :=
  ∀ n : σ →₀ ℕ, Continuous fun t => MvPowerSeries.coeff n (f t)

/- English proof (translation)
Introduce `_` and use `continuous_const`.
-/
theorem CoeffCont.const (f : MvPowerSeries σ K) : CoeffCont (fun _ : T => f) :=
  fun _ => continuous_const

/- English proof (translation)
Introduce `n` and use `by simp only [map_add] exact (hf n).add (hg n)`.
-/
theorem CoeffCont.add {f g : T → MvPowerSeries σ K} (hf : CoeffCont f) (hg : CoeffCont g) :
    CoeffCont fun t => f t + g t := fun n => by
  simp only [map_add]
  exact (hf n).add (hg n)

/- English proof (translation)
Introduce `n` and use `by simp only [map_sub] exact (hf n).sub (hg n)`.
-/
theorem CoeffCont.sub {f g : T → MvPowerSeries σ K} (hf : CoeffCont f) (hg : CoeffCont g) :
    CoeffCont fun t => f t - g t := fun n => by
  simp only [map_sub]
  exact (hf n).sub (hg n)

/- English proof (translation)
Introduce `n` and use `by classical simp only [MvPowerSeries.coeff_mul] exact continuous_finsetSum _ fun p _ => (hf p.1).mul (hg p.2)`.
-/
theorem CoeffCont.mul {f g : T → MvPowerSeries σ K} (hf : CoeffCont f) (hg : CoeffCont g) :
    CoeffCont fun t => f t * g t := fun n => by
  classical
  simp only [MvPowerSeries.coeff_mul]
  exact continuous_finsetSum _ fun p _ => (hf p.1).mul (hg p.2)

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simpa only [pow_zero] using CoeffCont.const (T := T) (1 : MvPowerSeries σ K)`. Consider the case `succ k ih => simpa only [pow_succ] using ih.mul hf`.
-/
theorem CoeffCont.pow {f : T → MvPowerSeries σ K} (hf : CoeffCont f) (k : ℕ) :
    CoeffCont fun t => f t ^ k := by
  induction k with
  | zero => simpa only [pow_zero] using CoeffCont.const (T := T) (1 : MvPowerSeries σ K)
  | succ k ih => simpa only [pow_succ] using ih.mul hf

/- English proof (translation)
Introduce `n` and use `by simp only [MvPowerSeries.coeff_C_mul] exact hc.mul (hf n)`.
-/
theorem CoeffCont.C_mul {c : T → K} (hc : Continuous c) {f : T → MvPowerSeries σ K}
    (hf : CoeffCont f) : CoeffCont fun t => MvPowerSeries.C (c t) * f t := fun n => by
  simp only [MvPowerSeries.coeff_C_mul]
  exact hc.mul (hf n)

/- English proof (translation)
Introduce `n` and use `by simp only [map_smul, smul_eq_mul] exact hc.mul (hf n)`.
-/
theorem CoeffCont.smul {c : T → K} (hc : Continuous c) {f : T → MvPowerSeries σ K}
    (hf : CoeffCont f) : CoeffCont fun t => c t • f t := fun n => by
  simp only [map_smul, smul_eq_mul]
  exact hc.mul (hf n)

/- English proof (translation)
Introduce `n` and use `by simp only [coeff_subst_range (h0 _)] exact continuous_finsetSum _ fun k _ => continuous_const.mul (hf.pow k n)`.
-/
theorem CoeffCont.subst {f : T → MvPowerSeries σ K} (hf : CoeffCont f)
    (h0 : ∀ t, MvPowerSeries.constantCoeff (f t) = 0) (g : PowerSeries K) :
    CoeffCont fun t => PowerSeries.subst (f t) g := fun n => by
  simp only [coeff_subst_range (h0 _)]
  exact continuous_finsetSum _ fun k _ => continuous_const.mul (hf.pow k n)

/- English proof (translation)
Simplify using `only [IntMv, Set.ofPred_forall]`. Conclude with `isClosed_iInter fun n => hR.preimage (hf n)`.
-/
theorem isClosed_intMv {R : Subring K} (hR : IsClosed (R : Set K)) {f : T → MvPowerSeries σ K}
    (hf : CoeffCont f) : IsClosed {t | IntMv R (f t)} := by
  simp only [IntMv, Set.ofPred_forall]
  exact isClosed_iInter fun n => hR.preimage (hf n)

/- English proof (translation)
Establish `: {t | LG R (f t)} = {t | IntMv R (mvExp (f t))}`. Use extensionality with `t`. Conclude with `⟨fun h => h.2, fun h => ⟨h0 t, h⟩⟩`. Rewrite using `[this]`. Conclude with `isClosed_intMv hR (hf.subst h0 _)`.
-/
theorem isClosed_LG [CharZero K] {R : Subring K} (hR : IsClosed (R : Set K))
    {f : T → MvPowerSeries σ K} (hf : CoeffCont f)
    (h0 : ∀ t, MvPowerSeries.constantCoeff (f t) = 0) : IsClosed {t | LG R (f t)} := by
  have : {t | LG R (f t)} = {t | IntMv R (mvExp (f t))} := by
    ext t
    exact ⟨fun h => h.2, fun h => ⟨h0 t, h⟩⟩
  rw [this]
  exact isClosed_intMv hR (hf.subst h0 _)

/- English proof (translation)
Rewrite using `[map_mul, hf, mul_zero]`.
-/
theorem cc_C_mul {f : MvPowerSeries σ K} (hf : MvPowerSeries.constantCoeff f = 0) (a : K) :
    MvPowerSeries.constantCoeff (MvPowerSeries.C a * f) = 0 := by
  rw [map_mul, hf, mul_zero]

/- English proof (translation)
Rewrite using `[MvPowerSeries.smul_eq_C_mul]`. Conclude with `cc_C_mul hf a`.
-/
theorem cc_smul {f : MvPowerSeries σ K} (hf : MvPowerSeries.constantCoeff f = 0) (a : K) :
    MvPowerSeries.constantCoeff (a • f) = 0 := by
  rw [MvPowerSeries.smul_eq_C_mul]
  exact cc_C_mul hf a

/- English proof (translation)
The claim follows from `(CoeffCont.C_mul hc (CoeffCont.const _)).subst (fun t => cc_C_mul (Pts.constantCoeff_subst hy hl) (c t)) linv`.
-/
theorem coeffCont_fmul {l : PowerSeries K} (hl : PowerSeries.constantCoeff l = 0)
    (linv : PowerSeries K) {c : T → K} (hc : Continuous c) {y : MvPowerSeries σ K}
    (hy : MvPowerSeries.constantCoeff y = 0) : CoeffCont fun t => fmul l linv (c t) y :=
  (CoeffCont.C_mul hc (CoeffCont.const _)).subst
    (fun t => cc_C_mul (Pts.constantCoeff_subst hy hl) (c t)) linv

/- English proof (translation)
The claim follows from `Pts.constantCoeff_subst (cc_C_mul (Pts.constantCoeff_subst hy hl) a) hli`.
-/
theorem cc_fmul {l linv : PowerSeries K} (hl : PowerSeries.constantCoeff l = 0)
    (hli : PowerSeries.constantCoeff linv = 0) (a : K) {y : MvPowerSeries σ K}
    (hy : MvPowerSeries.constantCoeff y = 0) :
    MvPowerSeries.constantCoeff (fmul l linv a y) = 0 :=
  Pts.constantCoeff_subst (cc_C_mul (Pts.constantCoeff_subst hy hl) a) hli

/- English proof (translation)
The claim follows from `Pts.constantCoeff_subst (by rw [map_add, Pts.constantCoeff_subst hx hl, Pts.constantCoeff_subst hy hl, add_zero]) hli`.
-/
theorem cc_fadd {l linv : PowerSeries K} (hl : PowerSeries.constantCoeff l = 0)
    (hli : PowerSeries.constantCoeff linv = 0) {x y : MvPowerSeries σ K}
    (hx : MvPowerSeries.constantCoeff x = 0) (hy : MvPowerSeries.constantCoeff y = 0) :
    MvPowerSeries.constantCoeff (fadd l linv x y) = 0 :=
  Pts.constantCoeff_subst
    (by rw [map_add, Pts.constantCoeff_subst hx hl, Pts.constantCoeff_subst hy hl, add_zero]) hli

/- English proof (translation)
Rewrite using `[be0, map_sub, map_sub, Pts.constantCoeff_subst (cc_fadd hl hli hx hy) hph, Pts.constantCoeff_subst hx hph, Pts.constantCoeff_subst hy hph, sub_zero, sub_zero]`.
-/
theorem constantCoeff_addDefect {l linv ph : PowerSeries K} (hl : PowerSeries.constantCoeff l = 0)
    (hli : PowerSeries.constantCoeff linv = 0) (hph : PowerSeries.constantCoeff ph = 0)
    {x y : MvPowerSeries σ K}
    (hx : MvPowerSeries.constantCoeff x = 0) (hy : MvPowerSeries.constantCoeff y = 0) :
    MvPowerSeries.constantCoeff (be0 l linv ph x y) = 0 := by
  rw [be0, map_sub, map_sub, Pts.constantCoeff_subst (cc_fadd hl hli hx hy) hph,
    Pts.constantCoeff_subst hx hph, Pts.constantCoeff_subst hy hph, sub_zero, sub_zero]

/- English proof (translation)
Establish `h1 : CoeffCont fun t => PowerSeries.subst x l + PowerSeries.subst (y t) l` using `(CoeffCont.const _).add (hy.subst hy0 l)`. Establish `h2 : CoeffCont fun t => fadd l linv x (y t)` using `h1.subst (fun t => by`. Rewrite using `[map_add, Pts.constantCoeff_subst hx hl, Pts.constantCoeff_subst (hy0 t) hl, add_zero]) linv`. Conclude with `((h2.subst (fun t => cc_fadd hl hli hx (hy0 t)) ph).sub (CoeffCont.const _)).sub (hy.subst hy0 ph)`.
-/
theorem coeffContinuous_addDefect {l linv ph : PowerSeries K} (hl : PowerSeries.constantCoeff l = 0)
    (hli : PowerSeries.constantCoeff linv = 0)
    {x : MvPowerSeries σ K} (hx : MvPowerSeries.constantCoeff x = 0)
    {y : T → MvPowerSeries σ K} (hy : CoeffCont y)
    (hy0 : ∀ t, MvPowerSeries.constantCoeff (y t) = 0) :
    CoeffCont fun t => be0 l linv ph x (y t) := by
  have h1 : CoeffCont fun t => PowerSeries.subst x l + PowerSeries.subst (y t) l :=
    (CoeffCont.const _).add (hy.subst hy0 l)
  have h2 : CoeffCont fun t => fadd l linv x (y t) :=
    h1.subst (fun t => by
      rw [map_add, Pts.constantCoeff_subst hx hl, Pts.constantCoeff_subst (hy0 t) hl, add_zero]) linv
  exact ((h2.subst (fun t => cc_fadd hl hli hx (hy0 t)) ph).sub (CoeffCont.const _)).sub
    (hy.subst hy0 ph)

end Cont

end Clo

open Clo

/- English proof (translation)
Introduce `K _ _ _ R hR l linv hl`. Establish `hX : MvPowerSeries.constantCoeff (PowerSeries.X : MvPowerSeries Unit K) = 0` using `PowerSeries.constantCoeff_X`. Establish `hc : CoeffCont fun a : K => fmul l linv a (PowerSeries.X : MvPowerSeries Unit K)` using `coeffCont_fmul hl linv continuous_id hX`. Establish `: {a : K | EndInt R l linv a} = {a : K | IntMv R (fmul l linv a (PowerSeries.X : MvPowerSeries Unit K))}`. Use extensionality with `a`.

Simplify using `only [Set.mem_ofPred_eq, EndInt, Pts.mulBy_eq_fmul]`. Conclude with `⟨Pts.intMv_of_intPS, Pts.intPS_of_intMv⟩`. Rewrite using `[this]`. Conclude with `isClosed_intMv hR hc`.
-/
theorem integralEndoClosed' : EndIntClosed := by
  intro K _ _ _ R hR l linv hl
  have hX : MvPowerSeries.constantCoeff (PowerSeries.X : MvPowerSeries Unit K) = 0 :=
    PowerSeries.constantCoeff_X
  have hc : CoeffCont fun a : K => fmul l linv a (PowerSeries.X : MvPowerSeries Unit K) :=
    coeffCont_fmul hl linv continuous_id hX
  have : {a : K | EndInt R l linv a} =
      {a : K | IntMv R (fmul l linv a (PowerSeries.X : MvPowerSeries Unit K))} := by
    ext a
    simp only [Set.mem_ofPred_eq, EndInt, Pts.mulBy_eq_fmul]
    exact ⟨Pts.intMv_of_intPS, Pts.intPS_of_intMv⟩
  rw [this]
  exact isClosed_intMv hR hc

/- English proof (translation)
Introduce `K _ _ _ R hR`. Simplify using `only [IsBinomScalar, Set.ofPred_forall]`. Use `isClosed_iInter fun n => hR.preimage ?_` and prove the remaining obligations. Unfold `binom`. Conclude with `(continuous_finsetProd _ fun i _ => continuous_id.sub continuous_const).div_const _`.
-/
theorem binomialScalarClosed' : BinomClosed := by
  intro K _ _ _ R hR
  simp only [IsBinomScalar, Set.ofPred_forall]
  refine isClosed_iInter fun n => hR.preimage ?_
  unfold binom
  exact (continuous_finsetProd _ fun i _ => continuous_id.sub continuous_const).div_const _

/- English proof (translation)
Introduce `K _ _ _ _ R hR l linv ph hl hli hph`. Establish `hX : MvPowerSeries.constantCoeff (PowerSeries.X : MvPowerSeries Unit K) = 0` using `PowerSeries.constantCoeff_X`. Establish `hc : CoeffCont fun p : K × K => fmul l linv p.1 (PowerSeries.X : MvPowerSeries Unit K)` using `coeffCont_fmul hl linv continuous_fst hX`. Establish `h0 : ∀ p : K × K, MvPowerSeries.constantCoeff (fmul l linv p.1 (PowerSeries.X : MvPowerSeries Unit K)) = 0` using `fun p => cc_fmul hl hli p.1 hX`. Simplify using `only [PhNormAt, Cong, Pts.mulBy_eq_fmul]`.

Use `isClosed_LG hR ((hc.subst h0 ph).sub (CoeffCont.smul (continuous_fst.mul continuous_snd) (CoeffCont.const _))) fun p => ?_` and prove the remaining obligations. Rewrite using `[map_sub, Pts.constantCoeff_subst (h0 p) hph, cc_smul hph, sub_zero]`.
-/
theorem logNormClosed' : PhNormClosed := by
  intro K _ _ _ _ R hR l linv ph hl hli hph
  have hX : MvPowerSeries.constantCoeff (PowerSeries.X : MvPowerSeries Unit K) = 0 :=
    PowerSeries.constantCoeff_X
  have hc : CoeffCont fun p : K × K => fmul l linv p.1 (PowerSeries.X : MvPowerSeries Unit K) :=
    coeffCont_fmul hl linv continuous_fst hX
  have h0 : ∀ p : K × K, MvPowerSeries.constantCoeff
      (fmul l linv p.1 (PowerSeries.X : MvPowerSeries Unit K)) = 0 :=
    fun p => cc_fmul hl hli p.1 hX
  simp only [PhNormAt, Cong, Pts.mulBy_eq_fmul]
  refine isClosed_LG hR ((hc.subst h0 ph).sub
    (CoeffCont.smul (continuous_fst.mul continuous_snd) (CoeffCont.const _))) fun p => ?_
  rw [map_sub, Pts.constantCoeff_subst (h0 p) hph, cc_smul hph, sub_zero]

/- English proof (translation)
Introduce `K _ _ _ _ R hR l linv ph hl hli hph`. Simplify using `only [ZLinAt, Cong, Set.ofPred_forall]`. Use `isClosed_iInter fun σ => isClosed_iInter fun x => isClosed_iInter fun y => isClosed_iInter fun hx => isClosed_iInter fun hy => ?_` and prove the remaining obligations. Establish `hc : CoeffCont fun z : K => fmul l linv z y` using `coeffCont_fmul hl linv continuous_id hy.1`. Use `isClosed_LG hR ((coeffContinuous_addDefect hl hli hx.1 hc fun z => cc_fmul hl hli z hy.1).sub (CoeffCont.smul continuous_id (CoeffCont.const _))) fun z => ?_` and prove the remaining obligations.

Rewrite using `[map_sub, constantCoeff_addDefect hl hli hph hx.1 (cc_fmul hl hli z hy.1), cc_smul (constantCoeff_addDefect hl hli hph hx.1 hy.1), sub_zero]`.
-/
theorem scalarLinearClosed' : ZLinClosed := by
  intro K _ _ _ _ R hR l linv ph hl hli hph
  simp only [ZLinAt, Cong, Set.ofPred_forall]
  refine isClosed_iInter fun σ => isClosed_iInter fun x => isClosed_iInter fun y =>
    isClosed_iInter fun hx => isClosed_iInter fun hy => ?_
  have hc : CoeffCont fun z : K => fmul l linv z y := coeffCont_fmul hl linv continuous_id hy.1
  refine isClosed_LG hR ((coeffContinuous_addDefect hl hli hx.1 hc fun z => cc_fmul hl hli z hy.1).sub
    (CoeffCont.smul continuous_id (CoeffCont.const _))) fun z => ?_
  rw [map_sub, constantCoeff_addDefect hl hli hph hx.1 (cc_fmul hl hli z hy.1),
    cc_smul (constantCoeff_addDefect hl hli hph hx.1 hy.1), sub_zero]

namespace Clo

section Lin

variable {K : Type} [Field K] {R : Subring K} {l linv : PowerSeries K}

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => rw [Nat.cast_zero]`. Conclude with `Pts.endInt_zero h`. Consider the case `succ n ih => rw [Nat.cast_succ]`. Conclude with `Pts.endInt_add h hF ih (Pts.endInt_one h)`.
-/
theorem endInt_natCast (h : IsLogPair l linv) (hF : FGInt R l linv) (n : ℕ) :
    EndInt R l linv (n : K) := by
  induction n with
  | zero => rw [Nat.cast_zero]; exact Pts.endInt_zero h
  | succ n ih => rw [Nat.cast_succ]; exact Pts.endInt_add h hF ih (Pts.endInt_one h)

variable [CharZero K] {ph : PowerSeries K} {σ : Type}

/- English proof (translation)
Rewrite using `[be0, Pts.fadd_zero h.1 hx, PowerSeries.subst_zero_of_constantCoeff_zero h.2.2, sub_self, sub_zero]`.
-/
theorem addDefect_zero_right (h : Frame R l linv ph) {x : MvPowerSeries σ K}
    (hx : MvPowerSeries.constantCoeff x = 0) : be0 l linv ph x 0 = 0 := by
  rw [be0, Pts.fadd_zero h.1 hx, PowerSeries.subst_zero_of_constantCoeff_zero h.2.2, sub_self,
    sub_zero]

/- English proof (translation)
Use `h1 σ y y' x hy hy' hx` as an intermediate fact. Rewrite `this` using `[Pts.addDefect_comm ph _ x, Pts.addDefect_comm ph y x, Pts.addDefect_comm ph y' x]`. Conclude with `this`.
-/
theorem addDefect_add_right (h1 : F1 R l linv ph) {x y y' : MvPowerSeries σ K} (hx : IsPt R x)
    (hy : IsPt R y) (hy' : IsPt R y') :
    LG R (be0 l linv ph x (fadd l linv y y') - (be0 l linv ph x y + be0 l linv ph x y')) := by
  have := h1 σ y y' x hy hy' hx
  rw [Pts.addDefect_comm ph _ x, Pts.addDefect_comm ph y x, Pts.addDefect_comm ph y' x] at this
  exact this

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Rewrite using `[Nat.cast_zero, Pts.fmul_zero_left h.1, addDefect_zero_right h hx.1, zero_smul, sub_zero]`. Conclude with `(lGSubgroup K R σ).1`. Consider the case `succ n ih`.

Establish `hp` using `addDefect_add_right h1 hx (Pts.isPt_fmul h.1 (endInt_natCast h.1 h.2.1 n) hy) hy`. Use `(lGSubgroup K R σ).2.1 _ _ hp ih` as an intermediate fact. Rewrite using `[Nat.cast_succ, Pts.fmul_add h.1 _ _ hy.1, Pts.fmul_one h.1 hy.1, add_smul, one_smul]`. Use `this using 1` and compare the differences between its conclusion and the goal. Normalize the expressions using the abelian group laws.
-/
theorem zLin_natCast (h : Frame R l linv ph) (h1 : F1 R l linv ph) {x y : MvPowerSeries σ K}
    (hx : IsPt R x) (hy : IsPt R y) (n : ℕ) :
    LG R (be0 l linv ph x (fmul l linv (n : K) y) - (n : K) • be0 l linv ph x y) := by
  induction n with
  | zero =>
    rw [Nat.cast_zero, Pts.fmul_zero_left h.1, addDefect_zero_right h hx.1, zero_smul, sub_zero]
    exact (lGSubgroup K R σ).1
  | succ n ih =>
    have hp := addDefect_add_right h1 hx (Pts.isPt_fmul h.1 (endInt_natCast h.1 h.2.1 n) hy) hy
    have := (lGSubgroup K R σ).2.1 _ _ hp ih
    rw [Nat.cast_succ, Pts.fmul_add h.1 _ _ hy.1, Pts.fmul_one h.1 hy.1, add_smul, one_smul]
    convert this using 1
    abel

end Lin

end Clo

/- English proof (translation)
Introduce `K _ _ R l linv ph h h1 n σ x y hx hy`. Take `⟨m, rfl | rfl⟩` from `n.eq_nat_or_neg`. Rewrite using `[Int.cast_natCast]`. Conclude with `zLin_natCast h h1 hx hy m`. Rewrite using `[Int.cast_neg, Int.cast_natCast]`.

Establish `hm` using `endInt_natCast (R := R) h.1 h.2.1 m`. Establish `hp` using `addDefect_add_right h1 hx (Pts.isPt_fmul h.1 hm hy) (Pts.isPt_fmul h.1 (Pts.endInt_neg h.1 h.2.1 hm) hy)`. Rewrite `hp` using `[Pts.fadd_fmul_neg h.1 _ hy.1, addDefect_zero_right h hx.1]`. Use `(lGSubgroup K R σ).2.2 _ ((lGSubgroup K R σ).2.1 _ _ hp (zLin_natCast h h1 hx hy m))` as an intermediate fact. Unfold `Cong`.

Rewrite using `[neg_smul]`. Use `this using 1` and compare the differences between its conclusion and the goal. Normalize the expressions using the abelian group laws.
-/
theorem scalarLinearInt' : ZLinInt := by
  intro K _ _ R l linv ph h h1 n σ x y hx hy
  obtain ⟨m, rfl | rfl⟩ := n.eq_nat_or_neg
  · rw [Int.cast_natCast]
    exact zLin_natCast h h1 hx hy m
  · rw [Int.cast_neg, Int.cast_natCast]
    have hm := endInt_natCast (R := R) h.1 h.2.1 m
    have hp := addDefect_add_right h1 hx (Pts.isPt_fmul h.1 hm hy)
      (Pts.isPt_fmul h.1 (Pts.endInt_neg h.1 h.2.1 hm) hy)
    rw [Pts.fadd_fmul_neg h.1 _ hy.1, addDefect_zero_right h hx.1] at hp
    have := (lGSubgroup K R σ).2.2 _
      ((lGSubgroup K R σ).2.1 _ _ hp (zLin_natCast h h1 hx hy m))
    unfold Cong
    rw [neg_smul]
    convert this using 1
    abel

/- English proof (translation)
Introduce `K _ _ _ _ R hR l linv ph h h1 O _ _ _ τ hτ hstar hsa h2R h2O hsum Dn hDn hD`. Establish `hl` using `h.1.1`. Establish `hli` using `h.1.2.2.1`. Establish `hph` using `h.2.2`. Establish `hEu : ∀ α : Oˣ, EndInt R l linv (τ α)`.

Introduce `α`. Establish `hc : IsClosed {β : O | EndInt R l linv (τ β)}` using `(integralEndoClosed' K R hR l linv hl).preimage hτ`. Conclude with `closure_minimal (fun β hβ => (hD β hβ).1) hc (hDn α)`. Establish `hE : ∀ α : O, EndInt R l linv (τ α)`. Introduce `α`.

Take `⟨u, v, rfl⟩` from `hsum α`. Rewrite using `[map_add]`. Conclude with `Pts.endInt_add h.1 h.2.1 (hEu u) (hEu v)`. Establish `hPu : ∀ α : Oˣ, PhNormAt R l linv ph (τ α) (τ (star (α : O)))`. Introduce `α`.

Establish `hc : IsClosed {β : O | PhNormAt R l linv ph (τ β) (τ (star β))}` using `(logNormClosed' K R hR l linv ph hl hli hph).preimage (hτ.prodMk (hτ.comp hstar))`. Conclude with `closure_minimal (fun β hβ => (hD β hβ).2) hc (hDn α)`. Establish `hB : ∀ z : O, star z = z → IsBinomScalar R (τ z)`. Introduce `z hz`. Use `closure_minimal ?_ (binomialScalarClosed' K R hR) (hsa z hz)` and prove the remaining obligations.

Introduce and unpack `_ ⟨n, rfl⟩`. Conclude with `intBinomScalar K R n`. Establish `hZ : ∀ z : O, star z = z → ZLinAt R l linv ph (τ z)`. Introduce `z hz`. Use `closure_minimal ?_ (scalarLinearClosed' K R hR l linv ph hl hli hph) (hsa z hz)` and prove the remaining obligations.

Introduce and unpack `_ ⟨n, rfl⟩`. Conclude with `scalarLinearInt' K R l linv ph h h1 n`. Introduce `α`. Use `hN K R l linv ph h O τ hE hB hZ h1 h2R h2O hsum hPu α` as an intermediate fact. Conclude with `⟨hE α, this.1, this.2⟩`.
-/
theorem endoAll_of (hN : NormAdjAll) : EndoAll := by
  intro K _ _ _ _ R hR l linv ph h h1 O _ _ _ τ hτ hstar hsa h2R h2O hsum Dn hDn hD
  have hl := h.1.1
  have hli := h.1.2.2.1
  have hph := h.2.2
  have hEu : ∀ α : Oˣ, EndInt R l linv (τ α) := by
    intro α
    have hc : IsClosed {β : O | EndInt R l linv (τ β)} :=
      (integralEndoClosed' K R hR l linv hl).preimage hτ
    exact closure_minimal (fun β hβ => (hD β hβ).1) hc (hDn α)
  have hE : ∀ α : O, EndInt R l linv (τ α) := by
    intro α
    obtain ⟨u, v, rfl⟩ := hsum α
    rw [map_add]
    exact Pts.endInt_add h.1 h.2.1 (hEu u) (hEu v)
  have hPu : ∀ α : Oˣ, PhNormAt R l linv ph (τ α) (τ (star (α : O))) := by
    intro α
    have hc : IsClosed {β : O | PhNormAt R l linv ph (τ β) (τ (star β))} :=
      (logNormClosed' K R hR l linv ph hl hli hph).preimage
        (hτ.prodMk (hτ.comp hstar))
    exact closure_minimal (fun β hβ => (hD β hβ).2) hc (hDn α)
  have hB : ∀ z : O, star z = z → IsBinomScalar R (τ z) := by
    intro z hz
    refine closure_minimal ?_ (binomialScalarClosed' K R hR) (hsa z hz)
    rintro _ ⟨n, rfl⟩
    exact intBinomScalar K R n
  have hZ : ∀ z : O, star z = z → ZLinAt R l linv ph (τ z) := by
    intro z hz
    refine closure_minimal ?_ (scalarLinearClosed' K R hR l linv ph hl hli hph) (hsa z hz)
    rintro _ ⟨n, rfl⟩
    exact scalarLinearInt' K R l linv ph h h1 n
  intro α
  have := hN K R l linv ph h O τ hE hB hZ h1 h2R h2O hsum hPu α
  exact ⟨hE α, this.1, this.2⟩

end Formalism.L2.Th1.C
