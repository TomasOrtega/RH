import Formalism.TorsionNormIteration.InvIntegralOfClass
import Formalism.FormalGroupLog.LogDeterminesLaw

noncomputable section

open PowerSeries

namespace Formalism.LT.PadicP

open Formalism.G

/- English proof (translation)
Establish `hy' : y ∈ RingHom.ker (PadicInt.toZMod (p` using `p)) := RingHom.mem_ker.mpr hy`. Rewrite `hy'` using `[PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton]`. Take `⟨z, rfl⟩` from `hy'`. Rewrite using `[norm_mul]`. Conclude with `mul_le_of_le_one_right (norm_nonneg _) (PadicInt.norm_le_one z)`.
-/
theorem padicInt_norm_le_p {p : ℕ} [Fact p.Prime] (y : ℤ_[p]) (hy : PadicInt.toZMod y = 0) :
    ‖y‖ ≤ ‖(p : ℤ_[p])‖ := by
  have hy' : y ∈ RingHom.ker (PadicInt.toZMod (p := p)) := RingHom.mem_ker.mpr hy
  rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hy'
  obtain ⟨z, rfl⟩ := hy'
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (PadicInt.norm_le_one z)

/- English proof (translation)
Introduce `p _`. Use `⟨Fact.out, ⟨1, one_pos, (pow_one p).symm⟩, Padic.norm_p_lt_one, ?_⟩` and prove the remaining obligations. Introduce `a ha`. Set `y : ℤ_[p]` to `⟨a, ha⟩`. Establish `hy : PadicInt.toZMod (y - y ^ p) = 0` using `by rw [map_sub, map_pow, ZMod.pow_card, sub_self]`.

Conclude with `padicInt_norm_le_p _ hy`.
-/
theorem frobLiftPadic : FrobLiftPadic := by
  intro p _
  refine ⟨Fact.out, ⟨1, one_pos, (pow_one p).symm⟩, Padic.norm_p_lt_one, ?_⟩
  intro a ha
  let y : ℤ_[p] := ⟨a, ha⟩
  have hy : PadicInt.toZMod (y - y ^ p) = 0 := by rw [map_sub, map_pow, ZMod.pow_card, sub_self]
  exact padicInt_norm_le_p _ hy

def unitBallEquiv (p : ℕ) [Fact p.Prime] : unitBall ℚ_[p] ≃+* ℤ_[p] where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/- English proof (translation)
Unfold `FormalGroup.map`. Use `congr 1`.
-/
theorem map_map_unitBall (p : ℕ) [Fact p.Prime] (F : FormalGroup (unitBall ℚ_[p])) :
    (F.map (unitBallEquiv p).toRingHom).map PadicInt.Coe.ringHom = F.map (unitBall ℚ_[p]).subtype := by
  unfold FormalGroup.map
  congr 1

/- English proof (translation)
Introduce `p _ f h0 h1 hf`. Take `⟨F, hF⟩` from `hfg ℚ_[p] p p (RingHom.id _) (frobLiftPadic p) f h0 h1 hf`. Conclude with `⟨F.map (unitBallEquiv p).toRingHom, by rw [map_map_unitBall]; exact hF⟩`.
-/
theorem funEqPadic_of (hfg : FunEqFormalGroup.{0}) : FunEqPadic := by
  intro p _ f h0 h1 hf
  obtain ⟨F, hF⟩ := hfg ℚ_[p] p p (RingHom.id _) (frobLiftPadic p) f h0 h1 hf
  exact ⟨F.map (unitBallEquiv p).toRingHom, by rw [map_map_unitBall]; exact hF⟩

/- English proof (translation)
Take `⟨h0, h1, hF⟩` from `hlog`. Use `⟨he0, ?_⟩` and prove the remaining obligations. Establish `hFS : PowerSeries.HasSubst F.toPowerSeries` using `PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff`. Establish `heS : PowerSeries.HasSubst e` using `PowerSeries.HasSubst.of_constantCoeff_zero' he0`. Establish `hcc : ∀ t : Fin 2, MvPowerSeries.constantCoeff (e.subst (MvPowerSeries.X t : MvPowerSeries (Fin 2) R)) = 0` using `fun t => PowerSeries.constantCoeff_subst_eq_zero (by simp) e he0`.

Establish `hv : MvPowerSeries.HasSubst ![atX e, atY e]` using `LogP.hs2 (hcc 0) (hcc 1)`. Establish `hat : ∀ t : Fin 2, f.subst (e.subst (MvPowerSeries.X t : MvPowerSeries (Fin 2) R)) = c • f.subst (MvPowerSeries.X t : MvPowerSeries (Fin 2) R)`. Introduce `t`. Rewrite using `[← PowerSeries.subst_comp_subst_apply heS (PowerSeries.HasSubst.X t), hfe, PowerSeries.subst_smul (PowerSeries.HasSubst.X t)]`. Apply `substInjective R (Fin 2) f _ _ h0 h1` to reduce the goal to its premises.

Conclude with `PowerSeries.constantCoeff_subst_eq_zero F.zero_constantCoeff e he0`. Apply the tactic sequence `rw [LogP.constantCoeff_subst_of_zero F.toPowerSeries (fun i => by fin_cases i <;> simp [hcc]), F.zero_constantCoeff]`. Rewrite using `[← PowerSeries.subst_comp_subst_apply heS hFS, hfe, PowerSeries.subst_smul hFS, hF, ← LogP.psubst_subst f F.zero_constantCoeff hv, hF, MvPowerSeries.subst_add hv]`. Rewrite using `[LogP.psubst_subst f (by simp) hv, LogP.psubst_subst f (by simp) hv, MvPowerSeries.subst_X hv, MvPowerSeries.subst_X hv]`. Simplify using `only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, atX, atY]`.

Rewrite using `[hat 0, hat 1, smul_add]`.
-/
theorem isHom_of_subst_eq_smul {R : Type} [CommRing R] (F : FormalGroup R) (f e : PowerSeries R)
    (c : R) (hlog : IsLog F f) (he0 : constantCoeff e = 0) (hfe : f.subst e = c • f) :
    IsHom F F e := by
  obtain ⟨h0, h1, hF⟩ := hlog
  refine ⟨he0, ?_⟩
  have hFS : PowerSeries.HasSubst F.toPowerSeries :=
    PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff
  have heS : PowerSeries.HasSubst e := PowerSeries.HasSubst.of_constantCoeff_zero' he0
  have hcc : ∀ t : Fin 2, MvPowerSeries.constantCoeff
      (e.subst (MvPowerSeries.X t : MvPowerSeries (Fin 2) R)) = 0 := fun t =>
    PowerSeries.constantCoeff_subst_eq_zero (by simp) e he0
  have hv : MvPowerSeries.HasSubst ![atX e, atY e] := LogP.hs2 (hcc 0) (hcc 1)
  have hat : ∀ t : Fin 2, f.subst (e.subst (MvPowerSeries.X t : MvPowerSeries (Fin 2) R)) =
      c • f.subst (MvPowerSeries.X t : MvPowerSeries (Fin 2) R) := by
    intro t
    rw [← PowerSeries.subst_comp_subst_apply heS (PowerSeries.HasSubst.X t), hfe,
      PowerSeries.subst_smul (PowerSeries.HasSubst.X t)]
  apply substInjective R (Fin 2) f _ _ h0 h1
  · exact PowerSeries.constantCoeff_subst_eq_zero F.zero_constantCoeff e he0
  · rw [LogP.constantCoeff_subst_of_zero F.toPowerSeries (fun i => by fin_cases i <;> simp [hcc]),
      F.zero_constantCoeff]
  · rw [← PowerSeries.subst_comp_subst_apply heS hFS, hfe, PowerSeries.subst_smul hFS, hF,
      ← LogP.psubst_subst f F.zero_constantCoeff hv, hF, MvPowerSeries.subst_add hv]
    rw [LogP.psubst_subst f (by simp) hv, LogP.psubst_subst f (by simp) hv,
      MvPowerSeries.subst_X hv, MvPowerSeries.subst_X hv]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, atX, atY]
    rw [hat 0, hat 1, smul_add]

section LtLog

variable {p : ℕ} [hp : Fact p.Prime]

open Classical in
/- English proof (translation)
Unfold `ltLog`. Conclude with `coeff_mk _ _`.
-/
theorem coeff_ltLog (n : ℕ) :
    coeff n (ltLog p) = if ∃ k : ℕ, p ^ k = n then ((n : ℚ_[p]))⁻¹ else 0 := by
  unfold ltLog
  exact coeff_mk _ _

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨k, hk⟩`. Consider the cases of `k with`. Consider the case `zero`. Rewrite `hk` using `[pow_zero]`.

Establish `h1 : p ∣ 1` using `⟨m, hk⟩`. Conclude with `absurd (Nat.le_of_dvd one_pos h1) (by have := hp.out.two_le; omega)`. Consider the case `succ k`. Conclude with `⟨k, Nat.eq_of_mul_eq_mul_left hp.out.pos (by rw [← pow_succ']; exact hk)⟩`. Introduce and unpack `⟨k, rfl⟩`.

Conclude with `⟨k + 1, pow_succ' p k⟩`.
-/
theorem isPow_mul_iff (m : ℕ) : (∃ k : ℕ, p ^ k = p * m) ↔ ∃ k : ℕ, p ^ k = m := by
  constructor
  · rintro ⟨k, hk⟩
    cases k with
    | zero =>
      rw [pow_zero] at hk
      have h1 : p ∣ 1 := ⟨m, hk⟩
      exact absurd (Nat.le_of_dvd one_pos h1) (by have := hp.out.two_le; omega)
    | succ k =>
      exact ⟨k, Nat.eq_of_mul_eq_mul_left hp.out.pos (by rw [← pow_succ']; exact hk)⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k + 1, pow_succ' p k⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨k, rfl⟩`. Consider the cases of `k with`. Consider the case `zero => exact pow_zero p`. Consider the case `succ k => exact absurd (dvd_pow_self p (Nat.succ_ne_zero k)) h`.

Introduce and unpack `rfl`. Conclude with `⟨0, pow_zero p⟩`.
-/
theorem isPow_iff_of_not_dvd (n : ℕ) (h : ¬ p ∣ n) : (∃ k : ℕ, p ^ k = n) ↔ n = 1 := by
  constructor
  · rintro ⟨k, rfl⟩
    cases k with
    | zero => exact pow_zero p
    | succ k => exact absurd (dvd_pow_self p (Nat.succ_ne_zero k)) h
  · rintro rfl
    exact ⟨0, pow_zero p⟩

/- English proof (translation)
Rewrite using `[← coeff_zero_eq_constantCoeff_apply, coeff_ltLog, if_neg]`. Introduce and unpack `⟨k, hk⟩`. Conclude with `absurd hk (pow_ne_zero k hp.out.ne_zero)`.
-/
theorem constantCoeff_ltLog : constantCoeff (ltLog p) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_ltLog, if_neg]
  rintro ⟨k, hk⟩
  exact absurd hk (pow_ne_zero k hp.out.ne_zero)

/- English proof (translation)
Rewrite using `[coeff_ltLog, if_pos ⟨0, pow_zero p⟩, Nat.cast_one, inv_one]`.
-/
theorem coeff_one_ltLog : coeff 1 (ltLog p) = 1 := by
  rw [coeff_ltLog, if_pos ⟨0, pow_zero p⟩, Nat.cast_one, inv_one]

/- English proof (translation)
Establish `ha : HasSubst ((X : PowerSeries ℚ_[p]) ^ p)` using `HasSubst.of_constantCoeff_zero' (by simp [hp.out.ne_zero])`. Express the relevant statement in the definitionally equal form `MvPowerSeries.coeff (Finsupp.single () n) _ = _`. Rewrite using `[coeff_subst ha]`. Express the relevant statement in the definitionally equal form `∑ᶠ d, coeff d f • coeff n (((X : PowerSeries ℚ_[p]) ^ p) ^ d) = _`. Repeatedly rewrite using `[← pow_mul, coeff_X_pow]`.

Use `split_ifs with h`. Take `⟨m, rfl⟩` from `h`. Rewrite using `[finsum_eq_single _ m]`. Rewrite using `[if_pos rfl, smul_eq_mul, mul_one, Nat.mul_div_cancel_left m hp.out.pos]`. Introduce `d hd`.

Rewrite using `[if_neg (fun h' => hd (Nat.eq_of_mul_eq_mul_left hp.out.pos h').symm), smul_zero]`. Use `finsum_eq_zero_of_forall_eq_zero fun d => ?_` and prove the remaining obligations. Rewrite using `[if_neg (fun h' => h ⟨d, h'⟩), smul_zero]`.
-/
private theorem coeff_subst_X_pow_lemma (f : PowerSeries ℚ_[p]) (n : ℕ) :
    coeff n (f.subst ((X : PowerSeries ℚ_[p]) ^ p)) = if p ∣ n then coeff (n / p) f else 0 := by
  have ha : HasSubst ((X : PowerSeries ℚ_[p]) ^ p) :=
    HasSubst.of_constantCoeff_zero' (by simp [hp.out.ne_zero])
  change MvPowerSeries.coeff (Finsupp.single () n) _ = _
  rw [coeff_subst ha]
  change ∑ᶠ d, coeff d f • coeff n (((X : PowerSeries ℚ_[p]) ^ p) ^ d) = _
  simp_rw [← pow_mul, coeff_X_pow]
  split_ifs with h
  · obtain ⟨m, rfl⟩ := h
    rw [finsum_eq_single _ m]
    · rw [if_pos rfl, smul_eq_mul, mul_one, Nat.mul_div_cancel_left m hp.out.pos]
    · intro d hd
      rw [if_neg (fun h' => hd (Nat.eq_of_mul_eq_mul_left hp.out.pos h').symm), smul_zero]
  · refine finsum_eq_zero_of_forall_eq_zero fun d => ?_
    rw [if_neg (fun h' => h ⟨d, h'⟩), smul_zero]

/- English proof (translation)
Use extensionality with `n`. Rewrite using `[map_sub, PowerSeries.coeff_smul, smul_eq_mul, coeff_subst_X_pow_lemma, coeff_X]`. Simplify using `only [coeff_ltLog]`. Distinguish the cases in `hd : p ∣ n`. Take `⟨m, rfl⟩` from `hd`.

Establish `hne : p * m ≠ 1`. Introduce `h`. Establish `h1` using `Nat.le_of_dvd one_pos ⟨m, h.symm⟩`. Use `hp.out.two_le` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Rewrite using `[if_pos (dvd_mul_right p m), Nat.mul_div_cancel_left m hp.out.pos, if_neg hne]`. Distinguish the cases in `hk : ∃ k, p ^ k = m`. Rewrite using `[if_pos ((isPow_mul_iff m).mpr hk), if_pos hk, Nat.cast_mul, mul_inv, sub_self]`. Rewrite using `[if_neg (fun h => hk ((isPow_mul_iff m).mp h)), if_neg hk, mul_zero, sub_zero]`. Rewrite using `[if_neg hd, mul_zero, sub_zero]`.

Distinguish the cases in `h1 : n = 1`. Substitute `h1` using the available equality. Rewrite using `[if_pos ⟨0, pow_zero p⟩, if_pos rfl, Nat.cast_one, inv_one]`. Rewrite using `[if_neg (fun h => h1 ((isPow_iff_of_not_dvd n hd).mp h)), if_neg h1]`.
-/
theorem ltLog_funEq :
    ltLog p - (p : ℚ_[p])⁻¹ • (ltLog p).subst ((X : PowerSeries ℚ_[p]) ^ p) = X := by
  ext n
  rw [map_sub, PowerSeries.coeff_smul, smul_eq_mul, coeff_subst_X_pow_lemma, coeff_X]
  simp only [coeff_ltLog]
  by_cases hd : p ∣ n
  · obtain ⟨m, rfl⟩ := hd
    have hne : p * m ≠ 1 := by
      intro h
      have h1 := Nat.le_of_dvd one_pos ⟨m, h.symm⟩
      have := hp.out.two_le
      omega
    rw [if_pos (dvd_mul_right p m), Nat.mul_div_cancel_left m hp.out.pos, if_neg hne]
    by_cases hk : ∃ k, p ^ k = m
    · rw [if_pos ((isPow_mul_iff m).mpr hk), if_pos hk, Nat.cast_mul, mul_inv, sub_self]
    · rw [if_neg (fun h => hk ((isPow_mul_iff m).mp h)), if_neg hk, mul_zero, sub_zero]
  · rw [if_neg hd, mul_zero, sub_zero]
    by_cases h1 : n = 1
    · subst h1
      rw [if_pos ⟨0, pow_zero p⟩, if_pos rfl, Nat.cast_one, inv_one]
    · rw [if_neg (fun h => h1 ((isPow_iff_of_not_dvd n hd).mp h)), if_neg h1]

/- English proof (translation)
Establish `hp0 : (p : ℚ_[p]) ≠ 0` using `Nat.cast_ne_zero.mpr hp.out.ne_zero`. Establish `h` using `congrArg (fun t => (p : ℚ_[p]) • t) (ltLog_funEq (p := p))`. Simplify using `only [smul_sub, smul_smul, mul_inv_cancel₀ hp0, one_smul] at h`. Rewrite using `[smul_sub, ← h]`. Normalize the expressions using the abelian group laws.
-/
theorem ltLog_subst_X_pow :
    (ltLog p).subst ((X : PowerSeries ℚ_[p]) ^ p) = (p : ℚ_[p]) • (ltLog p - X) := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  have h := congrArg (fun t => (p : ℚ_[p]) • t) (ltLog_funEq (p := p))
  simp only [smul_sub, smul_smul, mul_inv_cancel₀ hp0, one_smul] at h
  rw [smul_sub, ← h]
  abel

end LtLog

/- English proof (translation)
Establish `ha : HasSubst a` using `HasSubst.of_constantCoeff_zero' ha0`. Express the relevant statement in the definitionally equal form `MvPowerSeries.coeff (Finsupp.single () 1) _ = _`. Rewrite using `[coeff_subst ha]`. Express the relevant statement in the definitionally equal form `∑ᶠ d, coeff d f • coeff 1 (a ^ d) = _`. Rewrite using `[finsum_eq_single _ 1]`.

Rewrite using `[pow_one, smul_eq_mul]`. Introduce `d hd`. Take `⟨a', rfl⟩` from `X_dvd_iff.mpr ha0`. Break down `Nat.lt_or_gt_of_ne hd with h | h` into its components or cases. Establish `h0 : d = 0` using `by omega`.

Substitute `h0` using the available equality. Rewrite using `[pow_zero, coeff_one, if_neg one_ne_zero, smul_zero]`. Rewrite using `[mul_pow, coeff_X_pow_mul', if_neg (by omega), smul_zero]`.
-/
theorem coeff_one_subst {R : Type} [CommRing R] (f a : PowerSeries R)
    (hf0 : constantCoeff f = 0) (ha0 : constantCoeff a = 0) :
    coeff 1 (f.subst a) = coeff 1 f * coeff 1 a := by
  have ha : HasSubst a := HasSubst.of_constantCoeff_zero' ha0
  change MvPowerSeries.coeff (Finsupp.single () 1) _ = _
  rw [coeff_subst ha]
  change ∑ᶠ d, coeff d f • coeff 1 (a ^ d) = _
  rw [finsum_eq_single _ 1]
  · rw [pow_one, smul_eq_mul]
  · intro d hd
    obtain ⟨a', rfl⟩ := X_dvd_iff.mpr ha0
    rcases Nat.lt_or_gt_of_ne hd with h | h
    · have h0 : d = 0 := by omega
      subst h0
      rw [pow_zero, coeff_one, if_neg one_ne_zero, smul_zero]
    · rw [mul_pow, coeff_X_pow_mul', if_neg (by omega), smul_zero]

/- English proof (translation)
Introduce `x y h`. Conclude with `funext fun n => Subtype.ext (congrFun h n)`.
-/
theorem map_coe_injective_mv {p : ℕ} [Fact p.Prime] {σ : Type} :
    Function.Injective (MvPowerSeries.map (σ := σ) (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])) := by
  intro x y h
  exact funext fun n => Subtype.ext (congrFun h n)

/- English proof (translation)
Introduce `p hp`. Establish `hp0 : p ≠ 0` using `hp.out.ne_zero`. Establish `hset` using `frobLiftPadic p`. Establish `hmapid : ∀ g : PowerSeries ℚ_[p], PowerSeries.map (RingHom.id ℚ_[p]) g = g` using `fun g => by`. Simplify using the standard rewrite rules.

Establish `hX_int : IntegralPS (X : PowerSeries ℚ_[p])` using `fun n => by`. Apply the tactic sequence `rw [coeff_X]; split_ifs <;> simp`. Establish `hXp_int : IntegralPS ((X : PowerSeries ℚ_[p]) ^ p)` using `fun n => by`. Apply the tactic sequence `rw [coeff_X_pow]; split_ifs <;> simp`. Establish `hpn : ‖(p : ℚ_[p])‖ ≤ 1` using `hset.2.2.1.le`.

Establish `hfe : IsFunEqType p p (RingHom.id ℚ_[p]) (ltLog p)`. Unfold `IsFunEqType`. Rewrite using `[hmapid, ltLog_funEq]`. Conclude with `hX_int`. Establish `hge : IsFunEqType p p (RingHom.id ℚ_[p]) ((p : ℚ_[p]) • ltLog p)`.

Unfold `IsFunEqType`. Rewrite using `[hmapid, PowerSeries.subst_smul (HasSubst.X_pow hp0), smul_comm ((p : ℚ_[p])⁻¹) (p : ℚ_[p]), ← smul_sub, ltLog_funEq]`. Introduce `n`. Rewrite using `[map_smul, smul_eq_mul, norm_mul]`. Conclude with `mul_le_one₀ hpn (norm_nonneg _) (hX_int n)`.

Take `⟨F, hF⟩` from `funEqPadic_of hfg p (ltLog p) constantCoeff_ltLog coeff_one_ltLog hfe`. Take `⟨eK, heK0, heKi, heK⟩` from `hh ℚ_[p] p p (RingHom.id _) hset (ltLog p) ((p : ℚ_[p]) • ltLog p) constantCoeff_ltLog coeff_one_ltLog hfe (by rw [← coeff_zero_eq_constantCoeff_apply, map_smul, coeff_zero_eq_constantCoeff_apply, constantCoeff_ltLog, smul_zero]) hge`. Set `e : PowerSeries ℤ_[p]` to `PowerSeries.mk fun n => ⟨coeff n eK, heKi n⟩`. Establish `hce : ∀ n, ((coeff n e : ℤ_[p]) : ℚ_[p]) = coeff n eK` using `fun n => by`. Use `PowerSeries.coeff_mk (R := ℤ_[p]) n (fun n => (⟨coeff n eK, heKi n⟩ : ℤ_[p]))` as an intermediate fact.

Conclude with `congrArg Subtype.val this`. Establish `hemap : PowerSeries.map PadicInt.Coe.ringHom e = eK`. Use extensionality with `n`. Rewrite using `[coeff_map]`. Conclude with `hce n`.

Use `⟨F, hF, e, ?_, ?_, ?_⟩` and prove the remaining obligations. Take `⟨_, hK⟩` from `isHom_of_subst_eq_smul (F.map PadicInt.Coe.ringHom) (ltLog p) eK (p : ℚ_[p]) hF heK0 heK`. Establish `he0 : constantCoeff e = 0`. Rewrite using `[← coeff_zero_eq_constantCoeff_apply]`. Apply `PadicInt.ext` to reduce the goal to its premises.

Rewrite using `[hce, coeff_zero_eq_constantCoeff_apply, heK0]`. Both sides reduce to the same expression. Use `⟨he0, ?_⟩` and prove the remaining obligations. Establish `hFS : PowerSeries.HasSubst F.toPowerSeries` using `PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff`. Establish `hcc : ∀ t : Fin 2, MvPowerSeries.constantCoeff (e.subst (MvPowerSeries.X t : MvPowerSeries (Fin 2) ℤ_[p])) = 0` using `fun t => PowerSeries.constantCoeff_subst_eq_zero (by simp) e he0`.

Establish `hv : MvPowerSeries.HasSubst ![atX e, atY e]` using `LogP.hs2 (hcc 0) (hcc 1)`. Apply `map_coe_injective_mv` to reduce the goal to its premises. Rewrite using `[PowerSeries.map_subst hFS, hemap, MvPowerSeries.map_subst hv]`. Establish `hfun : (fun i => MvPowerSeries.map PadicInt.Coe.ringHom (![atX e, atY e] i)) = ![atX eK, atY eK]`. Use function extensionality and compare the values at `i`.

Use `fin_cases i`. Simplify using `only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, atX]`. Rewrite using `[PowerSeries.map_subst (HasSubst.X 0), hemap, MvPowerSeries.map_X]`. Simplify using `only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one, atY]`. Rewrite using `[PowerSeries.map_subst (HasSubst.X 1), hemap, MvPowerSeries.map_X]`.

Rewrite using `[hfun]`. Conclude with `hK`. Apply `PadicInt.ext` to reduce the goal to its premises. Establish `h1` using `congrArg (coeff 1) heK`. Rewrite `h1` using `[coeff_one_subst _ _ constantCoeff_ltLog heK0, coeff_one_ltLog, one_mul, map_smul, coeff_one_ltLog, smul_eq_mul, mul_one]`.

Rewrite using `[hce, h1]`. Both sides reduce to the same expression. Introduce `n`. Establish `hd` using `(hc ℚ_[p] p p (RingHom.id _) hset (ltLog p) constantCoeff_ltLog coeff_one_ltLog hfe eK (X ^ p) heK0 (by simp [hp0]) heKi hXp_int 1 le_rfl).mpr (by`. Rewrite using `[pow_one, heK, ltLog_subst_X_pow, ← smul_sub, sub_sub_cancel]`.

Introduce `n`. Rewrite using `[map_smul, smul_eq_mul, norm_mul]`. Conclude with `mul_le_of_le_one_right (norm_nonneg _) (hX_int n)) n`. Rewrite `hd` using `[pow_one]`. Establish `hm : PowerSeries.map PadicInt.Coe.ringHom (e - X ^ p) = eK - X ^ p`.

Rewrite using `[map_sub, map_pow, map_X, hemap]`. Establish `hcn : ((coeff n (e - X ^ p) : ℤ_[p]) : ℚ_[p]) = coeff n (eK - X ^ p)`. Rewrite using `[← hm, coeff_map]`. Both sides reduce to the same expression. Apply `(PadicInt.norm_lt_one_iff_dvd _).mp` to reduce the goal to its premises.

Rewrite using `[PadicInt.norm_def, hcn]`. Conclude with `lt_of_le_of_lt hd hset.2.2.1`.
-/
theorem lubinTateExample_of (hfg : FunEqFormalGroup.{0}) (hh : FunEqHom.{0})
    (hc : FunEqCongr.{0}) : LubinTateExample := by
  intro p hp
  have hp0 : p ≠ 0 := hp.out.ne_zero
  have hset := frobLiftPadic p
  have hmapid : ∀ g : PowerSeries ℚ_[p], PowerSeries.map (RingHom.id ℚ_[p]) g = g := fun g => by
    simp
  have hX_int : IntegralPS (X : PowerSeries ℚ_[p]) := fun n => by
    rw [coeff_X]; split_ifs <;> simp
  have hXp_int : IntegralPS ((X : PowerSeries ℚ_[p]) ^ p) := fun n => by
    rw [coeff_X_pow]; split_ifs <;> simp
  have hpn : ‖(p : ℚ_[p])‖ ≤ 1 := hset.2.2.1.le
  have hfe : IsFunEqType p p (RingHom.id ℚ_[p]) (ltLog p) := by
    unfold IsFunEqType; rw [hmapid, ltLog_funEq]; exact hX_int
  have hge : IsFunEqType p p (RingHom.id ℚ_[p]) ((p : ℚ_[p]) • ltLog p) := by
    unfold IsFunEqType
    rw [hmapid, PowerSeries.subst_smul (HasSubst.X_pow hp0), smul_comm ((p : ℚ_[p])⁻¹) (p : ℚ_[p]),
      ← smul_sub, ltLog_funEq]
    intro n
    rw [map_smul, smul_eq_mul, norm_mul]
    exact mul_le_one₀ hpn (norm_nonneg _) (hX_int n)
  obtain ⟨F, hF⟩ := funEqPadic_of hfg p (ltLog p) constantCoeff_ltLog coeff_one_ltLog hfe
  obtain ⟨eK, heK0, heKi, heK⟩ := hh ℚ_[p] p p (RingHom.id _) hset (ltLog p)
    ((p : ℚ_[p]) • ltLog p) constantCoeff_ltLog coeff_one_ltLog hfe
    (by rw [← coeff_zero_eq_constantCoeff_apply, map_smul, coeff_zero_eq_constantCoeff_apply,
      constantCoeff_ltLog, smul_zero]) hge
  let e : PowerSeries ℤ_[p] := PowerSeries.mk fun n => ⟨coeff n eK, heKi n⟩
  have hce : ∀ n, ((coeff n e : ℤ_[p]) : ℚ_[p]) = coeff n eK := fun n => by
    have := PowerSeries.coeff_mk (R := ℤ_[p]) n (fun n => (⟨coeff n eK, heKi n⟩ : ℤ_[p]))
    exact congrArg Subtype.val this
  have hemap : PowerSeries.map PadicInt.Coe.ringHom e = eK := by
    ext n; rw [coeff_map]; exact hce n
  refine ⟨F, hF, e, ?_, ?_, ?_⟩
  · obtain ⟨_, hK⟩ := isHom_of_subst_eq_smul (F.map PadicInt.Coe.ringHom) (ltLog p) eK (p : ℚ_[p])
      hF heK0 heK
    have he0 : constantCoeff e = 0 := by
      rw [← coeff_zero_eq_constantCoeff_apply]
      apply PadicInt.ext
      rw [hce, coeff_zero_eq_constantCoeff_apply, heK0]; rfl
    refine ⟨he0, ?_⟩
    have hFS : PowerSeries.HasSubst F.toPowerSeries :=
      PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff
    have hcc : ∀ t : Fin 2, MvPowerSeries.constantCoeff
        (e.subst (MvPowerSeries.X t : MvPowerSeries (Fin 2) ℤ_[p])) = 0 := fun t =>
      PowerSeries.constantCoeff_subst_eq_zero (by simp) e he0
    have hv : MvPowerSeries.HasSubst ![atX e, atY e] := LogP.hs2 (hcc 0) (hcc 1)
    apply map_coe_injective_mv
    rw [PowerSeries.map_subst hFS, hemap, MvPowerSeries.map_subst hv]
    have hfun : (fun i => MvPowerSeries.map PadicInt.Coe.ringHom (![atX e, atY e] i)) =
        ![atX eK, atY eK] := by
      funext i
      fin_cases i
      · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, atX]
        rw [PowerSeries.map_subst (HasSubst.X 0), hemap, MvPowerSeries.map_X]
      · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one, atY]
        rw [PowerSeries.map_subst (HasSubst.X 1), hemap, MvPowerSeries.map_X]
    rw [hfun]
    exact hK
  · apply PadicInt.ext
    have h1 := congrArg (coeff 1) heK
    rw [coeff_one_subst _ _ constantCoeff_ltLog heK0, coeff_one_ltLog, one_mul, map_smul,
      coeff_one_ltLog, smul_eq_mul, mul_one] at h1
    rw [hce, h1]; rfl
  · intro n
    have hd := (hc ℚ_[p] p p (RingHom.id _) hset (ltLog p) constantCoeff_ltLog coeff_one_ltLog hfe
      eK (X ^ p) heK0 (by simp [hp0]) heKi hXp_int 1 le_rfl).mpr (by
        rw [pow_one, heK, ltLog_subst_X_pow, ← smul_sub, sub_sub_cancel]
        intro n
        rw [map_smul, smul_eq_mul, norm_mul]
        exact mul_le_of_le_one_right (norm_nonneg _) (hX_int n)) n
    rw [pow_one] at hd
    have hm : PowerSeries.map PadicInt.Coe.ringHom (e - X ^ p) = eK - X ^ p := by
      rw [map_sub, map_pow, map_X, hemap]
    have hcn : ((coeff n (e - X ^ p) : ℤ_[p]) : ℚ_[p]) = coeff n (eK - X ^ p) := by
      rw [← hm, coeff_map]; rfl
    apply (PadicInt.norm_lt_one_iff_dvd _).mp
    rw [PadicInt.norm_def, hcn]
    exact lt_of_le_of_lt hd hset.2.2.1

end Formalism.LT.PadicP

namespace Formalism.LT

/- English proof (translation)
The claim follows from `PadicP.lubinTateExample_of hfg hh hc`.
-/
theorem LubinTateExample_of (hfg : Formalism.G.FunEqFormalGroup.{0}) (hh : Formalism.G.FunEqHom.{0})
    (hc : Formalism.G.FunEqCongr.{0}) : Formalism.G.LubinTateExample := PadicP.lubinTateExample_of hfg hh hc

end Formalism.LT
