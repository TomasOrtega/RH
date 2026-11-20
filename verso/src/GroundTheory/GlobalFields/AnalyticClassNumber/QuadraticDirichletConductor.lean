import Mathlib
import GroundTheory.GlobalFields.AnalyticClassNumber.DirichletHecke
set_option maxSynthPendingDepth 1

namespace GroundTheory.Global

open IsDedekindDomain NumberField IdeleGroup Topology WithZero
open scoped GroundTheory.LocalField.Abstract

noncomputable section

namespace DirichletHecke

open _root_.GroundTheory.Global.Cyclotomic GroundTheory.LocalField.Abstract RationalSymbol

section Norm

variable {v : HeightOneSpectrum (𝓞 ℚ)}

/- English proof (translation)
Rewrite using `[uniformizer, padicRingEquiv_finiteProj_diagonal, coe_primeRat]`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem padicRingEquiv_uniformizer (v : HeightOneSpectrum (𝓞 ℚ)) :
    padicRingEquiv v (uniformizer v : v.adicCompletion ℚ) = (prime v : ℚ_[prime v]) := by
  rw [uniformizer, padicRingEquiv_finiteProj_diagonal, coe_primeRat]
  push_cast
  rfl

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h ↦ (PadicInt.mem_subring_iff _).1 ((Rat.HeightOneSpectrum.adicCompletion.padicEquiv_bijOn v).mapsTo h), mem_adicCompletionIntegers_of_norm_le v⟩`.
-/
theorem mem_adicCompletionIntegers_iff_norm_le (x : v.adicCompletion ℚ) :
    x ∈ v.adicCompletionIntegers ℚ ↔ ‖padicRingEquiv v x‖ ≤ 1 :=
  ⟨fun h ↦ (PadicInt.mem_subring_iff _).1
    ((Rat.HeightOneSpectrum.adicCompletion.padicEquiv_bijOn v).mapsTo h),
    mem_adicCompletionIntegers_of_norm_le v⟩

/- English proof (translation)
Use `set u : v.adicCompletion ℚ := (uniformizer v : v.adicCompletion ℚ)`. Establish `hval : Valued.v (x * (u ^ n)⁻¹) = Valued.v x * exp (n : ℤ)`. Rewrite using `[map_mul, map_inv₀, map_pow, valued_uniformizer, ← exp_nsmul, ← exp_neg]`. Use `congr 2`. Simplify using the standard rewrite rules.

Establish `hnorm : ‖padicRingEquiv v (x * (u ^ n)⁻¹)‖ = ‖padicRingEquiv v x‖ * (prime v : ℝ) ^ n`. Rewrite using `[map_mul, map_inv₀, map_pow, padicRingEquiv_uniformizer, norm_mul, norm_inv, norm_pow, Padic.norm_p, inv_pow, inv_inv]`. Establish `h1` using `mem_adicCompletionIntegers_iff_norm_le (x * (u ^ n)⁻¹)`. Rewrite `h1` using `[HeightOneSpectrum.mem_adicCompletionIntegers, hval, hnorm]`. Establish `hp : (0 : ℝ) < (prime v : ℝ) ^ n`.

Use `(Fact.out : (prime v).Prime).pos` as an intermediate fact. Check the signs of the components of the expression. Establish `hexp : Valued.v x ≤ exp (-(n : ℤ)) ↔ Valued.v x * exp (n : ℤ) ≤ 1`. Establish `e : exp (-(n : ℤ)) * exp (n : ℤ) = 1` using `by rw [← exp_add, neg_add_cancel, exp_zero]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Combine the equalities or inequalities in the displayed calculation. Introduce `h`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_assoc, mul_comm (exp _), e, mul_one]`.

Use `_ ≤ 1 * exp (-(n : ℤ)) := by gcongr`. Use `_ = exp (-(n : ℤ)) := one_mul _`. Rewrite using `[hexp, h1, inv_eq_one_div, le_div_iff₀ hp]`.
-/
theorem valued_le_exp_neg_iff (x : v.adicCompletion ℚ) (n : ℕ) :
    Valued.v x ≤ exp (-(n : ℤ)) ↔ ‖padicRingEquiv v x‖ ≤ ((prime v : ℝ) ^ n)⁻¹ := by
  set u : v.adicCompletion ℚ := (uniformizer v : v.adicCompletion ℚ)
  have hval : Valued.v (x * (u ^ n)⁻¹) = Valued.v x * exp (n : ℤ) := by
    rw [map_mul, map_inv₀, map_pow, valued_uniformizer, ← exp_nsmul, ← exp_neg]
    congr 2
    simp
  have hnorm : ‖padicRingEquiv v (x * (u ^ n)⁻¹)‖ = ‖padicRingEquiv v x‖ * (prime v : ℝ) ^ n := by
    rw [map_mul, map_inv₀, map_pow, padicRingEquiv_uniformizer, norm_mul, norm_inv, norm_pow,
      Padic.norm_p, inv_pow, inv_inv]
  have h1 := mem_adicCompletionIntegers_iff_norm_le (x * (u ^ n)⁻¹)
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, hval, hnorm] at h1
  have hp : (0 : ℝ) < (prime v : ℝ) ^ n := by
    have := (Fact.out : (prime v).Prime).pos
    positivity
  have hexp : Valued.v x ≤ exp (-(n : ℤ)) ↔ Valued.v x * exp (n : ℤ) ≤ 1 := by
    have e : exp (-(n : ℤ)) * exp (n : ℤ) = 1 := by rw [← exp_add, neg_add_cancel, exp_zero]
    constructor
    · intro h
      calc Valued.v x * exp (n : ℤ) ≤ exp (-(n : ℤ)) * exp (n : ℤ) := by gcongr
        _ = 1 := e
    · intro h
      calc Valued.v x = Valued.v x * exp (n : ℤ) * exp (-(n : ℤ)) := by
            rw [mul_assoc, mul_comm (exp _), e, mul_one]
        _ ≤ 1 * exp (-(n : ℤ)) := by gcongr
        _ = exp (-(n : ℤ)) := one_mul _
  rw [hexp, h1, inv_eq_one_div, le_div_iff₀ hp]

/- English proof (translation)
Rewrite using `[mem_unitsLevel, ← map_one (padicRingEquiv v), ← map_sub, ← valued_le_exp_neg_iff]`. Use `and_congr_left fun _ ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩` and prove the remaining obligations. Use `norm_padicRingEquiv_eq_one ?_` and prove the remaining obligations. Rewrite using `[← unitsLevel_zero, mem_unitsLevel]`. Use `⟨h, ?_⟩` and prove the remaining obligations.

Use `(Valuation.map_sub _ _ _).trans ?_` and prove the remaining obligations. Rewrite using `[h, map_one, max_self]`. Simplify using the standard rewrite rules. Establish `h0` using `mem_units_of_norm_padicRingEquiv_eq_one h`. Rewrite `h0` using `[← unitsLevel_zero, mem_unitsLevel]`.

Conclude with `h0.1`.
-/
theorem mem_unitsLevel_iff (a : (v.adicCompletion ℚ)ˣ) (n : ℕ) :
    a ∈ unitsLevel v n ↔ ‖padicRingEquiv v (a : v.adicCompletion ℚ)‖ = 1 ∧
      ‖padicRingEquiv v (a : v.adicCompletion ℚ) - 1‖ ≤ ((prime v : ℝ) ^ n)⁻¹ := by
  rw [mem_unitsLevel, ← map_one (padicRingEquiv v), ← map_sub, ← valued_le_exp_neg_iff]
  refine and_congr_left fun _ ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · refine norm_padicRingEquiv_eq_one ?_
    rw [← unitsLevel_zero, mem_unitsLevel]
    refine ⟨h, ?_⟩
    refine (Valuation.map_sub _ _ _).trans ?_
    rw [h, map_one, max_self]
    simp
  · have h0 := mem_units_of_norm_padicRingEquiv_eq_one h
    rw [← unitsLevel_zero, mem_unitsLevel] at h0
    exact h0.1

end Norm

section Padic

variable {p : ℕ} [Fact p.Prime]

/- English proof (translation)
Establish `e : (((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) * ((u : ℤ_[p]) : ℚ_[p]) = 1`. Rewrite using `[← PadicInt.coe_mul, Units.inv_mul, PadicInt.coe_one]`. Conclude with `eq_inv_of_mul_eq_one_left e`.
-/
theorem coe_units_inv (u : ℤ_[p]ˣ) :
    (((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) = ((u : ℤ_[p]) : ℚ_[p])⁻¹ := by
  have e : (((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) * ((u : ℤ_[p]) : ℚ_[p]) = 1 := by
    rw [← PadicInt.coe_mul, Units.inv_mul, PadicInt.coe_one]
  exact eq_inv_of_mul_eq_one_left e

/- English proof (translation)
Establish `hx0 : x ≠ 0` using `norm_ne_zero_iff.1 (by rw [hx]; exact one_ne_zero)`. Rewrite using `[show x⁻¹ - 1 = x⁻¹ * (1 - x) by field_simp, norm_mul, norm_inv, hx, inv_one, one_mul, norm_sub_rev]`.
-/
theorem norm_inv_sub_one {x : ℚ_[p]} (hx : ‖x‖ = 1) : ‖x⁻¹ - 1‖ = ‖x - 1‖ := by
  have hx0 : x ≠ 0 := norm_ne_zero_iff.1 (by rw [hx]; exact one_ne_zero)
  rw [show x⁻¹ - 1 = x⁻¹ * (1 - x) by field_simp, norm_mul, norm_inv, hx, inv_one, one_mul,
    norm_sub_rev]

/- English proof (translation)
Establish `hmem : u - 1 ∈ Ideal.span {(p : ℤ_[p]) ^ k}`. Rewrite using `[← PadicInt.norm_le_pow_iff_mem_span_pow, zpow_neg, zpow_natCast]`. Rewrite using `[PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_one]`. Conclude with `h`. Rewrite `hmem` using `[← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_one, sub_eq_zero]`.

Conclude with `hmem`.
-/
theorem toZModPow_eq_one_of_norm_le {u : ℤ_[p]} {k : ℕ}
    (h : ‖(u : ℚ_[p]) - 1‖ ≤ ((p : ℝ) ^ k)⁻¹) : PadicInt.toZModPow k u = 1 := by
  have hmem : u - 1 ∈ Ideal.span {(p : ℤ_[p]) ^ k} := by
    rw [← PadicInt.norm_le_pow_iff_mem_span_pow, zpow_neg, zpow_natCast]
    rw [PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_one]
    exact h
  rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_one, sub_eq_zero] at hmem
  exact hmem

end Padic

section Local

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)

/- English proof (translation)
Rewrite `ha` using `[mem_unitsLevel_iff]`. Take `⟨ha1, ha2⟩` from `ha`. Rewrite using `[HeckeCharacter.localComponent_apply, HeckeCharacter.toIdele_apply]`. Use `Circle.ext ?_` and prove the remaining obligations. Rewrite using `[Circle.coe_one, ← map_one χ]`.

Use `coe_heckeCharacter_mk_of_forall χ ⟨_, finiteEmbedding_mem_positiveSubgroup ha1⟩ fun w hw ↦ ?_` and prove the remaining obligations. Rewrite using `[map_one]`. Distinguish the cases in `hwv : w = v`. Substitute `hwv` using the available equality. Establish `hu : (((unitAt ⟨_, finiteEmbedding_mem_positiveSubgroup ha1⟩ w : ℤ_[prime w]ˣ) : ℤ_[prime w]) : ℚ_[prime w]) = padicRingEquiv w (a : w.adicCompletion ℚ)`.

Rewrite using `[coe_unitAt]`. Express the relevant statement in the definitionally equal form `padicRingEquiv w (finiteProj w (finiteEmbedding w a) : w.adicCompletion ℚ) = _`. Rewrite using `[finiteProj_finiteEmbedding]`. Apply `toZModPow_eq_one_of_norm_le` to reduce the goal to its premises. Rewrite using `[coe_units_inv, hu, norm_inv_sub_one ha1]`.

Conclude with `ha2`. Rewrite using `[unitAt_eq_one (finiteProj_finiteEmbedding_of_ne hwv a), inv_one, Units.val_one, map_one]`.
-/
theorem localComponent_heckeCharacter_eq_one (v : HeightOneSpectrum (𝓞 ℚ))
    {a : (v.adicCompletion ℚ)ˣ} (ha : a ∈ unitsLevel v (N.factorization (prime v))) :
    (heckeCharacter χ).localComponent v a = 1 := by
  rw [mem_unitsLevel_iff] at ha
  obtain ⟨ha1, ha2⟩ := ha
  rw [HeckeCharacter.localComponent_apply, HeckeCharacter.toIdele_apply]
  refine Circle.ext ?_
  rw [Circle.coe_one, ← map_one χ]
  refine coe_heckeCharacter_mk_of_forall χ ⟨_, finiteEmbedding_mem_positiveSubgroup ha1⟩
    fun w hw ↦ ?_
  rw [map_one]
  by_cases hwv : w = v
  · subst hwv
    have hu : (((unitAt ⟨_, finiteEmbedding_mem_positiveSubgroup ha1⟩ w : ℤ_[prime w]ˣ) :
        ℤ_[prime w]) : ℚ_[prime w]) = padicRingEquiv w (a : w.adicCompletion ℚ) := by
      rw [coe_unitAt]
      change padicRingEquiv w (finiteProj w (finiteEmbedding w a) : w.adicCompletion ℚ) = _
      rw [finiteProj_finiteEmbedding]
    apply toZModPow_eq_one_of_norm_le
    rw [coe_units_inv, hu, norm_inv_sub_one ha1]
    exact ha2
  · rw [unitAt_eq_one (finiteProj_finiteEmbedding_of_ne hwv a), inv_one, Units.val_one, map_one]

/- English proof (translation)
Use `set m : ℕ := (b : ZMod N).val with hm`. Establish `hcop : (prime v).Coprime m` using `(Nat.Coprime.coprime_dvd_right hv (ZMod.val_coe_unit_coprime b)).symm`. Establish `hnm : ‖(m : ℚ_[prime v])‖ = 1` using `Padic.norm_natCast_eq_one_iff.2 hcop`. Establish `hm0 : (m : ℚ_[prime v]) ≠ 0` using `norm_ne_zero_iff.1 (by rw [hnm]; exact one_ne_zero)`. Establish `hnorm : ‖padicRingEquiv v (a : v.adicCompletion ℚ)‖ = 1`.

Rewrite using `[ha, norm_inv, hnm, inv_one]`. Use `⟨hnorm, coe_heckeCharacter_mk_of_forall χ ⟨_, finiteEmbedding_mem_positiveSubgroup hnorm⟩ fun w hw ↦ ?_⟩` and prove the remaining obligations. Distinguish the cases in `hwv : w = v`. Substitute `hwv` using the available equality. Establish `hu : (((unitAt ⟨_, finiteEmbedding_mem_positiveSubgroup hnorm⟩ w : ℤ_[prime w]ˣ) : ℤ_[prime w]) : ℚ_[prime w]) = (m : ℚ_[prime w])⁻¹`.

Rewrite using `[coe_unitAt]`. Express the relevant statement in the definitionally equal form `padicRingEquiv w (finiteProj w (finiteEmbedding w a) : w.adicCompletion ℚ) = _`. Rewrite using `[finiteProj_finiteEmbedding, ha]`. Rewrite using `[coe_inv_eq_natCast hm0 hu, map_natCast]`. Use `conv_rhs => rw [← ZMod.natCast_zmod_val (b : ZMod N), ← hm]`.

Rewrite using `[map_natCast]`. Rewrite using `[unitAt_eq_one (finiteProj_finiteEmbedding_of_ne hwv a), inv_one, Units.val_one, map_one]`. Establish `hcp : Nat.Coprime (prime w ^ N.factorization (prime w)) (prime v ^ N.factorization (prime v))` using `Nat.Coprime.pow _ _ (coprime_prime hwv)`. Establish `h1 : prime w ^ N.factorization (prime w) ∣ prime v ^ N.factorization (prime v) * (N / prime v ^ N.factorization (prime v))`. Rewrite using `[Nat.ordProj_mul_ordCompl_eq_self]`.

Conclude with `Nat.ordProj_dvd _ _`. Establish `hdvd` using `hcp.dvd_of_dvd_mul_left h1`. Rewrite using `[← castHom_castHom hdvd (Nat.ordCompl_dvd N (prime v)) (Nat.ordProj_dvd N (prime w))]`. Establish `hb' : ZMod.castHom (Nat.ordCompl_dvd N (prime v)) (ZMod (N / prime v ^ N.factorization (prime v))) (b : ZMod N) = 1` using `congrArg Units.val hb`. Rewrite using `[hb', map_one]`.
-/
theorem coe_heckeCharacter_finiteEmbedding_inv_val {v : HeightOneSpectrum (𝓞 ℚ)} (hv : prime v ∣ N)
    (b : (ZMod N)ˣ) (hb : ZMod.unitsMap (Nat.ordCompl_dvd N (prime v)) b = 1)
    {a : (v.adicCompletion ℚ)ˣ}
    (ha : padicRingEquiv v (a : v.adicCompletion ℚ) = (((b : ZMod N).val : ℕ) : ℚ_[prime v])⁻¹) :
    ‖padicRingEquiv v (a : v.adicCompletion ℚ)‖ = 1 ∧
      (heckeCharacter χ (IdeleClassGroup.mk ℚ (finiteEmbedding v a)) : ℂ) = χ b := by
  set m : ℕ := (b : ZMod N).val with hm
  have hcop : (prime v).Coprime m :=
    (Nat.Coprime.coprime_dvd_right hv (ZMod.val_coe_unit_coprime b)).symm
  have hnm : ‖(m : ℚ_[prime v])‖ = 1 := Padic.norm_natCast_eq_one_iff.2 hcop
  have hm0 : (m : ℚ_[prime v]) ≠ 0 := norm_ne_zero_iff.1 (by rw [hnm]; exact one_ne_zero)
  have hnorm : ‖padicRingEquiv v (a : v.adicCompletion ℚ)‖ = 1 := by
    rw [ha, norm_inv, hnm, inv_one]
  refine ⟨hnorm, coe_heckeCharacter_mk_of_forall χ ⟨_, finiteEmbedding_mem_positiveSubgroup hnorm⟩
    fun w hw ↦ ?_⟩
  by_cases hwv : w = v
  · subst hwv
    have hu : (((unitAt ⟨_, finiteEmbedding_mem_positiveSubgroup hnorm⟩ w : ℤ_[prime w]ˣ) :
        ℤ_[prime w]) : ℚ_[prime w]) = (m : ℚ_[prime w])⁻¹ := by
      rw [coe_unitAt]
      change padicRingEquiv w (finiteProj w (finiteEmbedding w a) : w.adicCompletion ℚ) = _
      rw [finiteProj_finiteEmbedding, ha]
    rw [coe_inv_eq_natCast hm0 hu, map_natCast]
    conv_rhs => rw [← ZMod.natCast_zmod_val (b : ZMod N), ← hm]
    rw [map_natCast]
  · rw [unitAt_eq_one (finiteProj_finiteEmbedding_of_ne hwv a), inv_one, Units.val_one, map_one]
    have hcp : Nat.Coprime (prime w ^ N.factorization (prime w))
        (prime v ^ N.factorization (prime v)) :=
      Nat.Coprime.pow _ _ (coprime_prime hwv)
    have h1 : prime w ^ N.factorization (prime w) ∣
        prime v ^ N.factorization (prime v) * (N / prime v ^ N.factorization (prime v)) := by
      rw [Nat.ordProj_mul_ordCompl_eq_self]
      exact Nat.ordProj_dvd _ _
    have hdvd := hcp.dvd_of_dvd_mul_left h1
    rw [← castHom_castHom hdvd (Nat.ordCompl_dvd N (prime v)) (Nat.ordProj_dvd N (prime w))]
    have hb' : ZMod.castHom (Nat.ordCompl_dvd N (prime v))
        (ZMod (N / prime v ^ N.factorization (prime v))) (b : ZMod N) = 1 := congrArg Units.val hb
    rw [hb', map_one]

/- English proof (translation)
The claim follows from `((heckeCharacter χ).localComponent v).continuous`.
-/
theorem continuous_localComponent (v : HeightOneSpectrum (𝓞 ℚ)) :
    Continuous ((heckeCharacter χ).localComponent v : (v.adicCompletion ℚ)ˣ →* Circle) :=
  ((heckeCharacter χ).localComponent v).continuous

/- English proof (translation)
The claim follows from `(unitsLevel_le_ker_iff v Circle.noSmallSubgroups _ (continuous_localComponent χ v)).1 fun _ ha ↦ localComponent_heckeCharacter_eq_one χ v ha`.
-/
theorem conductorExponent_localComponent_le (v : HeightOneSpectrum (𝓞 ℚ)) :
    conductorExponent v ((heckeCharacter χ).localComponent v : (v.adicCompletion ℚ)ˣ →* Circle) ≤
      N.factorization (prime v) :=
  (unitsLevel_le_ker_iff v Circle.noSmallSubgroups _ (continuous_localComponent χ v)).1
    fun _ ha ↦ localComponent_heckeCharacter_eq_one χ v ha

/- English proof (translation)
Use `set p := prime v with hp`. Use `set k := N.factorization p with hk`. Establish `hpp : p.Prime` using `Fact.out`. Distinguish the cases in `hv : p ∣ N`. Use `swap`.

Rewrite using `[hk, Nat.factorization_eq_zero_of_not_dvd hv]`. Conclude with `Nat.zero_le _`. Establish `hk1 : 1 ≤ k` using `hpp.factorization_pos_of_dvd (NeZero.ne N) hv`. Assume the negation of the conclusion as `hlt`. Use `push Not at hlt`.

Establish `hker : unitsLevel v (k - 1) ≤ ((heckeCharacter χ).localComponent v : (v.adicCompletion ℚ)ˣ →* Circle).ker` using `(unitsLevel_le_ker_iff v Circle.noSmallSubgroups _ (continuous_localComponent χ v)).2 (by omega)`. Establish `hdvd : N / p ∣ N` using `Nat.div_dvd_of_dvd hv`. Establish `hpow : p ^ k = p * p ^ (k - 1)` using `by rw [← pow_succ', Nat.sub_add_cancel hk1]`. Establish `he : N / p = p ^ (k - 1) * (N / p ^ k)` using `by conv_lhs => rw [← Nat.ordProj_mul_ordCompl_eq_self N p]`. Rewrite using `[← hk, hpow, mul_assoc, Nat.mul_div_cancel_left _ hpp.pos]`.

Establish `hpk : p ^ (k - 1) ∣ N / p` using `he ▸ dvd_mul_right _ _`. Establish `hcompl : N / p ^ k ∣ N / p` using `he ▸ dvd_mul_left _ _`. Establish `hf : χ.FactorsThrough (N / p)`. Use `(DirichletCharacter.factorsThrough_iff_ker_unitsMap hdvd).2 fun b hb ↦ ?_` and prove the remaining obligations. Establish `hbN : ZMod.castHom hdvd (ZMod (N / p)) (b : ZMod N) = 1` using `congrArg Units.val hb`.

Use `set m : ℕ := (b : ZMod N).val with hm`. Establish `hcop : p.Coprime m` using `(Nat.Coprime.coprime_dvd_right hv (ZMod.val_coe_unit_coprime b)).symm`. Establish `hnm : ‖(m : ℚ_[p])‖ = 1` using `Padic.norm_natCast_eq_one_iff.2 hcop`. Establish `hm0 : (m : ℚ_[p]) ≠ 0` using `norm_ne_zero_iff.1 (by rw [hnm]; exact one_ne_zero)`. Establish `hmN : ((N / p : ℕ) : ℤ) ∣ (m : ℤ) - 1`.

Use `(ZMod.intCast_eq_intCast_iff_dvd_sub 1 m (N / p)).1 ?_` and prove the remaining obligations. Rewrite using `[Int.cast_one, Int.cast_natCast, hm, ← map_natCast (ZMod.castHom hdvd (ZMod (N / p))), ZMod.natCast_zmod_val, hbN]`. Establish `hb' : ZMod.unitsMap (Nat.ordCompl_dvd N p) b = 1`. Use `Units.ext ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `ZMod.castHom (Nat.ordCompl_dvd N p) (ZMod (N / p ^ k)) (b : ZMod N) = 1`.

Rewrite using `[← ZMod.natCast_zmod_val (b : ZMod N), map_natCast, ← hm]`. Establish `h` using `(ZMod.intCast_eq_intCast_iff_dvd_sub 1 (m : ℤ) (N / p ^ k)).2 ((Int.natCast_dvd_natCast.2 hcompl).trans hmN)`. Rewrite `h` using `[Int.cast_one, Int.cast_natCast]`. Conclude with `h.symm`. Establish `hmp : ((p : ℤ) ^ (k - 1)) ∣ (m : ℤ) - 1` using `(Int.natCast_dvd_natCast.2 hpk).trans (by exact_mod_cast hmN)`.

Establish `hnorm1 : ‖(m : ℚ_[p]) - 1‖ ≤ ((p : ℝ) ^ (k - 1))⁻¹`. Establish `h` using `(Padic.norm_int_le_pow_iff_dvd ((m : ℤ) - 1) (k - 1)).2 hmp`. Rewrite `h` using `[zpow_neg, zpow_natCast]`. Conclude with `h` after adjusting the coercions. Set `a : (v.adicCompletion ℚ)ˣ` to `Units.map (padicRingEquiv v).symm.toMonoidHom (Units.mk0 (m : ℚ_[p]) hm0)⁻¹`.

Establish `ha : padicRingEquiv v (a : v.adicCompletion ℚ) = (m : ℚ_[p])⁻¹`. Simplify using `only [a, Units.coe_map, Units.val_inv_eq_inv_val, Units.val_mk0]`. Conclude with `RingEquiv.apply_symm_apply _ _`. Take `⟨-, hval⟩` from `coe_heckeCharacter_finiteEmbedding_inv_val χ hv b hb' ha`. Establish `hmem : a ∈ unitsLevel v (k - 1)`.

Rewrite using `[mem_unitsLevel_iff, ha, norm_inv, hnm, inv_one, norm_inv_sub_one hnm]`. Conclude with `⟨rfl, hnorm1⟩`. Establish `h1 : (heckeCharacter χ).localComponent v a = 1` using `hker hmem`. Rewrite `h1` using `[HeckeCharacter.localComponent_apply, HeckeCharacter.toIdele_apply]`. Rewrite using `[MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one, ← hval, h1, Circle.coe_one]`.

Establish `hc` using `χ.conductor_dvd_of_mem_conductorSet hf`. Rewrite `hc` using `[hχ]`. Establish `hle` using `Nat.le_of_dvd (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_neZero N) hv) hpp.pos) hc`. Establish `hlt'` using `Nat.div_lt_self (Nat.pos_of_neZero N) hpp.one_lt`. Use linear arithmetic over natural numbers and integers.
-/
theorem le_conductorExponent_localComponent (hχ : χ.IsPrimitive) (v : HeightOneSpectrum (𝓞 ℚ)) :
    N.factorization (prime v) ≤
      conductorExponent v ((heckeCharacter χ).localComponent v : (v.adicCompletion ℚ)ˣ →* Circle) := by
  set p := prime v with hp
  set k := N.factorization p with hk
  have hpp : p.Prime := Fact.out
  by_cases hv : p ∣ N
  swap
  · rw [hk, Nat.factorization_eq_zero_of_not_dvd hv]
    exact Nat.zero_le _
  have hk1 : 1 ≤ k := hpp.factorization_pos_of_dvd (NeZero.ne N) hv
  by_contra hlt
  push Not at hlt
  have hker : unitsLevel v (k - 1) ≤
      ((heckeCharacter χ).localComponent v : (v.adicCompletion ℚ)ˣ →* Circle).ker :=
    (unitsLevel_le_ker_iff v Circle.noSmallSubgroups _ (continuous_localComponent χ v)).2 (by omega)
  have hdvd : N / p ∣ N := Nat.div_dvd_of_dvd hv
  have hpow : p ^ k = p * p ^ (k - 1) := by rw [← pow_succ', Nat.sub_add_cancel hk1]
  have he : N / p = p ^ (k - 1) * (N / p ^ k) := by
    conv_lhs => rw [← Nat.ordProj_mul_ordCompl_eq_self N p]
    rw [← hk, hpow, mul_assoc, Nat.mul_div_cancel_left _ hpp.pos]
  have hpk : p ^ (k - 1) ∣ N / p := he ▸ dvd_mul_right _ _
  have hcompl : N / p ^ k ∣ N / p := he ▸ dvd_mul_left _ _
  have hf : χ.FactorsThrough (N / p) := by
    refine (DirichletCharacter.factorsThrough_iff_ker_unitsMap hdvd).2 fun b hb ↦ ?_
    have hbN : ZMod.castHom hdvd (ZMod (N / p)) (b : ZMod N) = 1 := congrArg Units.val hb
    set m : ℕ := (b : ZMod N).val with hm
    have hcop : p.Coprime m :=
      (Nat.Coprime.coprime_dvd_right hv (ZMod.val_coe_unit_coprime b)).symm
    have hnm : ‖(m : ℚ_[p])‖ = 1 := Padic.norm_natCast_eq_one_iff.2 hcop
    have hm0 : (m : ℚ_[p]) ≠ 0 := norm_ne_zero_iff.1 (by rw [hnm]; exact one_ne_zero)
    have hmN : ((N / p : ℕ) : ℤ) ∣ (m : ℤ) - 1 := by
      refine (ZMod.intCast_eq_intCast_iff_dvd_sub 1 m (N / p)).1 ?_
      rw [Int.cast_one, Int.cast_natCast, hm, ← map_natCast (ZMod.castHom hdvd (ZMod (N / p))),
        ZMod.natCast_zmod_val, hbN]
    have hb' : ZMod.unitsMap (Nat.ordCompl_dvd N p) b = 1 := by
      refine Units.ext ?_
      change ZMod.castHom (Nat.ordCompl_dvd N p) (ZMod (N / p ^ k)) (b : ZMod N) = 1
      rw [← ZMod.natCast_zmod_val (b : ZMod N), map_natCast, ← hm]
      have h := (ZMod.intCast_eq_intCast_iff_dvd_sub 1 (m : ℤ) (N / p ^ k)).2
        ((Int.natCast_dvd_natCast.2 hcompl).trans hmN)
      rw [Int.cast_one, Int.cast_natCast] at h
      exact h.symm
    have hmp : ((p : ℤ) ^ (k - 1)) ∣ (m : ℤ) - 1 :=
      (Int.natCast_dvd_natCast.2 hpk).trans (by exact_mod_cast hmN)
    have hnorm1 : ‖(m : ℚ_[p]) - 1‖ ≤ ((p : ℝ) ^ (k - 1))⁻¹ := by
      have h := (Padic.norm_int_le_pow_iff_dvd ((m : ℤ) - 1) (k - 1)).2 hmp
      rw [zpow_neg, zpow_natCast] at h
      exact_mod_cast h
    let a : (v.adicCompletion ℚ)ˣ :=
      Units.map (padicRingEquiv v).symm.toMonoidHom (Units.mk0 (m : ℚ_[p]) hm0)⁻¹
    have ha : padicRingEquiv v (a : v.adicCompletion ℚ) = (m : ℚ_[p])⁻¹ := by
      simp only [a, Units.coe_map, Units.val_inv_eq_inv_val, Units.val_mk0]
      exact RingEquiv.apply_symm_apply _ _
    obtain ⟨-, hval⟩ := coe_heckeCharacter_finiteEmbedding_inv_val χ hv b hb' ha
    have hmem : a ∈ unitsLevel v (k - 1) := by
      rw [mem_unitsLevel_iff, ha, norm_inv, hnm, inv_one, norm_inv_sub_one hnm]
      exact ⟨rfl, hnorm1⟩
    have h1 : (heckeCharacter χ).localComponent v a = 1 := hker hmem
    rw [HeckeCharacter.localComponent_apply, HeckeCharacter.toIdele_apply] at h1
    rw [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one, ← hval, h1,
      Circle.coe_one]
  have hc := χ.conductor_dvd_of_mem_conductorSet hf
  rw [hχ] at hc
  have hle := Nat.le_of_dvd (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_neZero N) hv) hpp.pos) hc
  have hlt' := Nat.div_lt_self (Nat.pos_of_neZero N) hpp.one_lt
  omega

/- English proof (translation)
The claim follows from `le_antisymm (conductorExponent_localComponent_le χ v) (le_conductorExponent_localComponent χ hχ v)`.
-/
theorem conductorExponent_localComponent_heckeCharacter (hχ : χ.IsPrimitive)
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    conductorExponent v ((heckeCharacter χ).localComponent v : (v.adicCompletion ℚ)ˣ →* Circle) =
      N.factorization (prime v) :=
  le_antisymm (conductorExponent_localComponent_le χ v) (le_conductorExponent_localComponent χ hχ v)

/- English proof (translation)
Establish `h : ((heckeCharacter χ).toIdele.comp ofFinite).comp (finiteUnitsSingle v) = ((heckeCharacter χ).localComponent v : (v.adicCompletion ℚ)ˣ →* Circle)`. Use extensionality with `a`. Simplify using `only [MonoidHom.comp_apply, ofFinite_finiteUnitsSingle]`. Both sides reduce to the same expression. Rewrite using `[conductorExponentAt, h, conductorExponent_localComponent_heckeCharacter χ hχ]`.
-/
theorem conductorExponentAt_heckeCharacter (hχ : χ.IsPrimitive) (v : HeightOneSpectrum (𝓞 ℚ)) :
    conductorExponentAt ((heckeCharacter χ).toIdele.comp ofFinite) v = N.factorization (prime v) := by
  have h : ((heckeCharacter χ).toIdele.comp ofFinite).comp (finiteUnitsSingle v) =
      ((heckeCharacter χ).localComponent v : (v.adicCompletion ℚ)ˣ →* Circle) := by
    ext a
    simp only [MonoidHom.comp_apply, ofFinite_finiteUnitsSingle]
    rfl
  rw [conductorExponentAt, h, conductorExponent_localComponent_heckeCharacter χ hχ]

end Local

/- English proof (translation)
Rewrite using `[asIdeal_eq_span, Ideal.span_singleton_pow, Ideal.dvd_iff_le, Ideal.span_singleton_le_span_singleton, ← Nat.cast_pow, ← map_dvd_iff Rat.ringOfIntegersEquiv, map_natCast, map_natCast, Int.natCast_dvd_natCast]`.
-/
theorem asIdeal_pow_dvd_span_iff (v : HeightOneSpectrum (𝓞 ℚ)) (n m : ℕ) :
    v.asIdeal ^ n ∣ Ideal.span {(m : 𝓞 ℚ)} ↔ prime v ^ n ∣ m := by
  rw [asIdeal_eq_span, Ideal.span_singleton_pow, Ideal.dvd_iff_le,
    Ideal.span_singleton_le_span_singleton, ← Nat.cast_pow, ← map_dvd_iff Rat.ringOfIntegersEquiv, map_natCast, map_natCast,
    Int.natCast_dvd_natCast]

/- English proof (translation)
Rewrite using `[Ideal.dvd_iff_le, Ideal.span_singleton_le_span_singleton, ← map_dvd_iff Rat.ringOfIntegersEquiv, map_natCast, map_natCast, Int.natCast_dvd_natCast]`.
-/
theorem span_natCast_dvd_span_iff (m n : ℕ) :
    Ideal.span {(m : 𝓞 ℚ)} ∣ Ideal.span {(n : 𝓞 ℚ)} ↔ m ∣ n := by
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_span_singleton, ← map_dvd_iff Rat.ringOfIntegersEquiv,
    map_natCast, map_natCast, Int.natCast_dvd_natCast]

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)

/- English proof (translation)
Establish `hcont : Continuous ((heckeCharacter χ).toIdele.comp ofFinite)` using `(heckeCharacter χ).continuous_toIdele.comp continuous_ofFinite`. Establish `hfun : conductorExponentAt ((heckeCharacter χ).toIdele.comp ofFinite) = fun v ↦ N.factorization (prime v)`. Use function extensionality and compare the values at `(conductorExponentAt_heckeCharacter χ hχ)`. Establish `hsupp : (Function.support fun v : HeightOneSpectrum (𝓞 ℚ) ↦ N.factorization (prime v)).Finite`. Rewrite using `[← hfun]`.

Conclude with `finite_support_conductorExponentAt Circle.noSmallSubgroups _ hcont`. Establish `hcond : (heckeCharacter χ).conductor = ∏ᶠ v : HeightOneSpectrum (𝓞 ℚ), v.asIdeal ^ N.factorization (prime v)`. Rewrite using `[HeckeCharacter.conductor, IdeleGroup.conductor, hfun]`. Take `⟨m, hm⟩` from `exists_eq_span_natCast (heckeCharacter χ).conductor`. Establish `hm0 : m ≠ 0`.

Introduce and unpack `rfl`. Apply `(heckeCharacter χ).conductor_ne_bot` to reduce the goal to its premises. Rewrite using `[hm, Nat.cast_zero, Ideal.span_singleton_eq_bot]`. Establish `hN0 : Ideal.span {(N : 𝓞 ℚ)} ≠ ⊥`. Rewrite using `[Ne, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero]`.

Conclude with `NeZero.ne N`. Establish `hle` using `(finprod_asIdeal_pow_dvd_iff hsupp (heckeCharacter χ).conductor_ne_bot).1 (hcond ▸ dvd_rfl)`. Establish `hNm : N ∣ m`. Use `(Nat.factorization_le_iff_dvd (NeZero.ne N) hm0).1 fun q ↦ ?_` and prove the remaining obligations. Distinguish the cases in `hq : q.Prime`.

Establish `hv` using `prime_placeOf (⟨q, hq⟩ : Nat.Primes)`. Establish `h1` using `pow_dvd_of_le_multiplicity (hle (placeOf ⟨q, hq⟩))`. Rewrite `h1` using `[hm, asIdeal_pow_dvd_span_iff, hv]`. Conclude with `(hq.pow_dvd_iff_le_factorization hm0).1 h1`. Rewrite using `[Nat.factorization_eq_zero_of_not_prime N hq]`.

Conclude with `Nat.zero_le _`. Establish `hdvd : (heckeCharacter χ).conductor ∣ Ideal.span {(N : 𝓞 ℚ)}`. Rewrite using `[hcond]`. Use `(finprod_asIdeal_pow_dvd_iff hsupp hN0).2 fun v ↦ ?_` and prove the remaining obligations. Use `(FiniteMultiplicity.of_prime_left (HeightOneSpectrum.prime v) hN0).le_multiplicity_of_pow_dvd ?_` and prove the remaining obligations.

Rewrite using `[asIdeal_pow_dvd_span_iff]`. Conclude with `Nat.ordProj_dvd N (prime v)`. Rewrite `hdvd` using `[hm, span_natCast_dvd_span_iff]`. Rewrite using `[hm, Nat.dvd_antisymm hdvd hNm]`.
-/
theorem conductor_heckeCharacter (hχ : χ.IsPrimitive) :
    (heckeCharacter χ).conductor = Ideal.span {(N : 𝓞 ℚ)} := by
  have hcont : Continuous ((heckeCharacter χ).toIdele.comp ofFinite) :=
    (heckeCharacter χ).continuous_toIdele.comp continuous_ofFinite
  have hfun : conductorExponentAt ((heckeCharacter χ).toIdele.comp ofFinite) =
      fun v ↦ N.factorization (prime v) :=
    funext (conductorExponentAt_heckeCharacter χ hχ)
  have hsupp : (Function.support fun v : HeightOneSpectrum (𝓞 ℚ) ↦ N.factorization (prime v)).Finite := by
    rw [← hfun]
    exact finite_support_conductorExponentAt Circle.noSmallSubgroups _ hcont
  have hcond : (heckeCharacter χ).conductor =
      ∏ᶠ v : HeightOneSpectrum (𝓞 ℚ), v.asIdeal ^ N.factorization (prime v) := by
    rw [HeckeCharacter.conductor, IdeleGroup.conductor, hfun]
  obtain ⟨m, hm⟩ := exists_eq_span_natCast (heckeCharacter χ).conductor
  have hm0 : m ≠ 0 := by
    rintro rfl
    apply (heckeCharacter χ).conductor_ne_bot
    rw [hm, Nat.cast_zero, Ideal.span_singleton_eq_bot]
  have hN0 : Ideal.span {(N : 𝓞 ℚ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero]
    exact NeZero.ne N

  have hle := (finprod_asIdeal_pow_dvd_iff hsupp (heckeCharacter χ).conductor_ne_bot).1
    (hcond ▸ dvd_rfl)
  have hNm : N ∣ m := by
    refine (Nat.factorization_le_iff_dvd (NeZero.ne N) hm0).1 fun q ↦ ?_
    by_cases hq : q.Prime
    · have hv := prime_placeOf (⟨q, hq⟩ : Nat.Primes)
      have h1 := pow_dvd_of_le_multiplicity (hle (placeOf ⟨q, hq⟩))
      rw [hm, asIdeal_pow_dvd_span_iff, hv] at h1
      exact (hq.pow_dvd_iff_le_factorization hm0).1 h1
    · rw [Nat.factorization_eq_zero_of_not_prime N hq]
      exact Nat.zero_le _

  have hdvd : (heckeCharacter χ).conductor ∣ Ideal.span {(N : 𝓞 ℚ)} := by
    rw [hcond]
    refine (finprod_asIdeal_pow_dvd_iff hsupp hN0).2 fun v ↦ ?_
    refine (FiniteMultiplicity.of_prime_left (HeightOneSpectrum.prime v) hN0).le_multiplicity_of_pow_dvd ?_
    rw [asIdeal_pow_dvd_span_iff]
    exact Nat.ordProj_dvd N (prime v)
  rw [hm, span_natCast_dvd_span_iff] at hdvd
  rw [hm, Nat.dvd_antisymm hdvd hNm]

/- English proof (translation)
Rewrite using `[conductor_heckeCharacter χ hχ, absNorm_span_natCast]`.
-/
theorem absNorm_conductor_heckeCharacter (hχ : χ.IsPrimitive) :
    Ideal.absNorm (heckeCharacter χ).conductor = N := by
  rw [conductor_heckeCharacter χ hχ, absNorm_span_natCast]

end DirichletHecke

end

end GroundTheory.Global
