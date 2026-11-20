import Mathlib
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.StatementW
import Formalism.FormalGroupWitt.FormalGroupWittProofs.WittTeichmullerRoot

noncomputable section

open scoped NNReal
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

namespace Formalism.InvariantFactorPaths.G7

namespace WModel

variable (p : ℕ) [hp : Fact p.Prime]

abbrev WW : Type := WittVector p (AlgebraicClosure (ZMod p))

abbrev KK : Type := FractionRing (WW p)

/- English proof (translation)
Conclude with `hp.out.one_lt` after adjusting the coercions.
-/
theorem one_lt_b : (1 : ℝ≥0) < (p : ℝ≥0) := by exact_mod_cast hp.out.one_lt

def abv : AbsoluteValue (KK p) ℝ :=
  (IsDiscreteValuationRing.maximalIdeal (WW p)).adicAbv (one_lt_b p)

/- English proof (translation)
The claim follows from `(WittVector.irreducible p).maximalIdeal_eq`.
-/
theorem maxIdeal_eq : (IsDiscreteValuationRing.maximalIdeal (WW p)).asIdeal =
    Ideal.span {(p : WW p)} :=
  (WittVector.irreducible p).maximalIdeal_eq

/- English proof (translation)
The claim follows from `isNonarchimedean_adicAbv _ _`.
-/
theorem abv_nonarch : IsNonarchimedean (abv p) :=
  isNonarchimedean_adicAbv _ _

/- English proof (translation)
The claim follows from `adicAbv_coe_le_one _ _ _`.
-/
theorem abv_coe_le_one (w : WW p) : abv p (algebraMap (WW p) (KK p) w) ≤ 1 :=
  adicAbv_coe_le_one _ _ _

/- English proof (translation)
Establish `h : WithZero.exp n = ((Multiplicative.ofAdd n : Multiplicative ℤ) : WithZero (Multiplicative ℤ))` using `rfl`. Rewrite using `[h, WithZeroMulInt.toNNReal_neg_apply he WithZero.coe_ne_zero, WithZero.unzero_coe]`. Both sides reduce to the same expression.
-/
theorem toNNReal_exp {e : ℝ≥0} (he : e ≠ 0) (n : ℤ) :
    WithZeroMulInt.toNNReal he (WithZero.exp n) = e ^ n := by
  have h : WithZero.exp n = ((Multiplicative.ofAdd n : Multiplicative ℤ) :
      WithZero (Multiplicative ℤ)) := rfl
  rw [h, WithZeroMulInt.toNNReal_neg_apply he WithZero.coe_ne_zero, WithZero.unzero_coe]
  rfl

/- English proof (translation)
Establish `h : (p : KK p) = algebraMap (WW p) (KK p) (p : WW p)` using `by simp`. Rewrite using `[h, abv, adicAbv_of_algebraMap]`. Establish `h2` using `intValuation_singleton (IsDiscreteValuationRing.maximalIdeal (WW p)) (WittVector.p_nonzero p _) (maxIdeal_eq p)`. Simplify using `only [intAdicAbv, intAdicAbvDef, AbsoluteValue.coe_mk, MulHom.coe_mk, h2]`. Rewrite using `[toNNReal_exp]`.

Simplify using the standard rewrite rules.
-/
theorem abv_p : abv p (p : KK p) = (p : ℝ)⁻¹ := by
  have h : (p : KK p) = algebraMap (WW p) (KK p) (p : WW p) := by simp
  rw [h, abv, adicAbv_of_algebraMap]
  have h2 := intValuation_singleton (IsDiscreteValuationRing.maximalIdeal (WW p))
    (WittVector.p_nonzero p _) (maxIdeal_eq p)
  simp only [intAdicAbv, intAdicAbvDef, AbsoluteValue.coe_mk, MulHom.coe_mk, h2]
  rw [toNNReal_exp]
  simp

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Apply `IsDiscreteValuationRing.exists_lift_of_le_one` to reduce the goal to its premises. Establish `h' : (adicAbvDef (IsDiscreteValuationRing.maximalIdeal (WW p)) (one_lt_b p) x : ℝ) ≤ 1` using `h`. Rewrite `h'` using `[adicAbvDef]`.

Conclude with `(WithZeroMulInt.toNNReal_le_one_iff (one_lt_b p)).1 (by exact_mod_cast h')`. Introduce and unpack `⟨w, rfl⟩`. Conclude with `abv_coe_le_one p w`.
-/
theorem abv_le_one_iff (x : KK p) : abv p x ≤ 1 ↔ ∃ w : WW p, algebraMap (WW p) (KK p) w = x := by
  constructor
  · intro h
    apply IsDiscreteValuationRing.exists_lift_of_le_one
    have h' : (adicAbvDef (IsDiscreteValuationRing.maximalIdeal (WW p)) (one_lt_b p) x : ℝ) ≤ 1 := h
    rw [adicAbvDef] at h'
    exact (WithZeroMulInt.toNNReal_le_one_iff (one_lt_b p)).1 (by exact_mod_cast h')
  · rintro ⟨w, rfl⟩
    exact abv_coe_le_one p w

/- English proof (translation)
Use `(adicAbv_coe_eq_one_iff _ _ _).2 ?_` and prove the remaining obligations. Use `show (u : WW p) ∉ IsLocalRing.maximalIdeal _`. Simplify using the standard rewrite rules.
-/
theorem abv_unit (u : (WW p)ˣ) : abv p (algebraMap (WW p) (KK p) (u : WW p)) = 1 := by
  refine (adicAbv_coe_eq_one_iff _ _ _).2 ?_
  show (u : WW p) ∉ IsLocalRing.maximalIdeal _
  simp

/- English proof (translation)
Introduce `h`. Use `abv_p p` as an intermediate fact. Rewrite `this` using `[h, map_zero]`. Establish `h2 : (0 : ℝ) < (p : ℝ)⁻¹`. Use `hp.out.pos` as an intermediate fact.

Check the signs of the components of the expression. Conclude with `h2.ne this`.
-/
theorem p_ne_zero : (p : KK p) ≠ 0 := by
  intro h
  have := abv_p p
  rw [h, map_zero] at this
  have h2 : (0 : ℝ) < (p : ℝ)⁻¹ := by
    have := hp.out.pos
    positivity
  exact h2.ne this

/- English proof (translation)
Take `⟨a, b, hb, rfl⟩` from `IsFractionRing.div_surjective (A := WW p) x`. Establish `ha : a ≠ 0`. Introduce and unpack `rfl`. Simplify using `at hx`. Establish `hb0 : b ≠ 0` using `nonZeroDivisors.ne_zero hb`.

Take `⟨m, a', rfl⟩` from `WittVector.exists_eq_pow_p_mul' a ha`. Take `⟨n, b', rfl⟩` from `WittVector.exists_eq_pow_p_mul' b hb0`. Use `⟨(m : ℤ) - n, a' * b'⁻¹, ?_⟩` and prove the remaining obligations. Establish `hp0` using `p_ne_zero p`. Establish `h1 : algebraMap (WW p) (KK p) (b' : WW p) * algebraMap (WW p) (KK p) ((b'⁻¹ : (WW p)ˣ) : WW p) = 1`.

Rewrite using `[← map_mul]`. Simplify using the standard rewrite rules. Establish `hB : algebraMap (WW p) (KK p) (b' : WW p) ≠ 0` using `left_ne_zero_of_mul_eq_one h1`. Establish `h2 : algebraMap (WW p) (KK p) ((b'⁻¹ : (WW p)ˣ) : WW p) = (algebraMap (WW p) (KK p) (b' : WW p))⁻¹` using `eq_inv_of_mul_eq_one_right h1`. Rewrite using `[zpow_sub₀ hp0, Units.val_mul, map_mul, map_mul, map_mul, h2, map_pow, map_pow, map_natCast, zpow_natCast, zpow_natCast]`.

Clear the denominators using the available nonvanishing facts.
-/
theorem exists_pow_unit (x : KK p) (hx : x ≠ 0) :
    ∃ (n : ℤ) (u : (WW p)ˣ), x = (p : KK p) ^ n * algebraMap (WW p) (KK p) (u : WW p) := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := WW p) x
  have ha : a ≠ 0 := by
    rintro rfl
    simp at hx
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨m, a', rfl⟩ := WittVector.exists_eq_pow_p_mul' a ha
  obtain ⟨n, b', rfl⟩ := WittVector.exists_eq_pow_p_mul' b hb0
  refine ⟨(m : ℤ) - n, a' * b'⁻¹, ?_⟩
  have hp0 := p_ne_zero p
  have h1 : algebraMap (WW p) (KK p) (b' : WW p) * algebraMap (WW p) (KK p) ((b'⁻¹ : (WW p)ˣ) : WW p)
      = 1 := by
    rw [← map_mul]
    simp
  have hB : algebraMap (WW p) (KK p) (b' : WW p) ≠ 0 := left_ne_zero_of_mul_eq_one h1
  have h2 : algebraMap (WW p) (KK p) ((b'⁻¹ : (WW p)ˣ) : WW p)
      = (algebraMap (WW p) (KK p) (b' : WW p))⁻¹ := eq_inv_of_mul_eq_one_right h1
  rw [zpow_sub₀ hp0, Units.val_mul, map_mul, map_mul, map_mul, h2, map_pow, map_pow, map_natCast,
    zpow_natCast, zpow_natCast]
  field_simp

/- English proof (translation)
Take `⟨n, u, rfl⟩` from `exists_pow_unit p x hx`. Use `⟨-n, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, abv_unit, mul_one, map_zpow₀, abv_p, inv_zpow']`.
-/
theorem abv_value (x : KK p) (hx : x ≠ 0) : ∃ k : ℤ, abv p x = (p : ℝ) ^ k := by
  obtain ⟨n, u, rfl⟩ := exists_pow_unit p x hx
  refine ⟨-n, ?_⟩
  rw [map_mul, abv_unit, mul_one, map_zpow₀, abv_p, inv_zpow']

/- English proof (translation)
Establish `hp0` using `p_ne_zero p`. Establish `hpos : (0 : ℝ) < ((p : ℝ)⁻¹) ^ N`. Use `hp.out.pos` as an intermediate fact. Check the signs of the components of the expression. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Establish `h1 : abv p (x / (p : KK p) ^ N) ≤ 1`. Rewrite using `[map_div₀, map_pow, abv_p]`. Conclude with `div_le_one_of_le₀ h hpos.le`. Take `⟨w, hw⟩` from `(abv_le_one_iff p _).1 h1`.

Use `⟨w, ?_⟩` and prove the remaining obligations. Rewrite using `[hw]`. Clear the denominators using the available nonvanishing facts. Introduce and unpack `⟨w, rfl⟩`. Rewrite using `[map_mul, map_pow, abv_p]`.

Conclude with `mul_le_of_le_one_right hpos.le (abv_coe_le_one p w)`.
-/
theorem abv_le_pow_iff (N : ℕ) (x : KK p) : abv p x ≤ ((p : ℝ)⁻¹) ^ N ↔
    ∃ w : WW p, x = (p : KK p) ^ N * algebraMap (WW p) (KK p) w := by
  have hp0 := p_ne_zero p
  have hpos : (0 : ℝ) < ((p : ℝ)⁻¹) ^ N := by
    have := hp.out.pos
    positivity
  constructor
  · intro h
    have h1 : abv p (x / (p : KK p) ^ N) ≤ 1 := by
      rw [map_div₀, map_pow, abv_p]
      exact div_le_one_of_le₀ h hpos.le
    obtain ⟨w, hw⟩ := (abv_le_one_iff p _).1 h1
    refine ⟨w, ?_⟩
    rw [hw]
    field_simp
  · rintro ⟨w, rfl⟩
    rw [map_mul, map_pow, abv_p]
    exact mul_le_of_le_one_right hpos.le (abv_coe_le_one p w)

/- English proof (translation)
The claim follows from `nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ (WittVector.frobenius_bijective p _).injective`.
-/
theorem frob_nzd : nonZeroDivisors (WW p) ≤
    Submonoid.comap (WittVector.frobenius : WW p →+* WW p) (nonZeroDivisors (WW p)) :=
  nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
    (WittVector.frobenius_bijective p _).injective

def sig : KK p →+* KK p :=
  IsLocalization.map (KK p) (WittVector.frobenius : WW p →+* WW p) (frob_nzd p)

/- English proof (translation)
The claim follows from `IsLocalization.map_eq (frob_nzd p) w`.
-/
theorem sig_coe (w : WW p) : sig p (algebraMap (WW p) (KK p) w) =
    algebraMap (WW p) (KK p) (WittVector.frobenius w) :=
  IsLocalization.map_eq (frob_nzd p) w

/- English proof (translation)
Establish `h : WittVector.frobenius w - w ^ p ∈ Ideal.span {(p : WW p)}`. Rewrite using `[WittVector.mem_span_p_iff_coeff_zero_eq_zero]`. Use `show WittVector.constantCoeff (WittVector.frobenius w - w ^ p) = 0`. Rewrite using `[map_sub, map_pow]`. Use `show (WittVector.frobenius w).coeff 0 - (w.coeff 0) ^ p = 0`.

Rewrite using `[WittVector.coeff_frobenius_charP, sub_self]`. Conclude with `Ideal.mem_span_singleton.1 h`.
-/
theorem frob_sub_pow (w : WW p) : ∃ y : WW p, WittVector.frobenius w - w ^ p = (p : WW p) * y := by
  have h : WittVector.frobenius w - w ^ p ∈ Ideal.span {(p : WW p)} := by
    rw [WittVector.mem_span_p_iff_coeff_zero_eq_zero]
    show WittVector.constantCoeff (WittVector.frobenius w - w ^ p) = 0
    rw [map_sub, map_pow]
    show (WittVector.frobenius w).coeff 0 - (w.coeff 0) ^ p = 0
    rw [WittVector.coeff_frobenius_charP, sub_self]
  exact Ideal.mem_span_singleton.1 h

/- English proof (translation)
Take `⟨w, rfl⟩` from `(abv_le_one_iff p a).1 ha`. Take `⟨y, hy⟩` from `frob_sub_pow p w`. Use `(abv_le_pow_iff p 1 (sig p (algebraMap (WW p) (KK p) w) - (algebraMap (WW p) (KK p) w) ^ p)).2 ⟨y, by` as an intermediate fact. Rewrite using `[sig_coe, ← map_pow, ← map_sub, hy, map_mul, map_natCast, pow_one]⟩`. Simplify using `using this`.
-/
theorem abv_sig (a : KK p) (ha : abv p a ≤ 1) : abv p (sig p a - a ^ p) ≤ (p : ℝ)⁻¹ := by
  obtain ⟨w, rfl⟩ := (abv_le_one_iff p a).1 ha
  obtain ⟨y, hy⟩ := frob_sub_pow p w
  have := (abv_le_pow_iff p 1 (sig p (algebraMap (WW p) (KK p) w) -
    (algebraMap (WW p) (KK p) w) ^ p)).2 ⟨y, by
      rw [sig_coe, ← map_pow, ← map_sub, hy, map_mul, map_natCast, pow_one]⟩
  simpa using this

@[reducible] def nf : NormedField (KK p) := (abv p).toNormedField

attribute [local instance] nf

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem norm_def (x : KK p) : ‖x‖ = abv p x := rfl

/- English proof (translation)
The claim follows from `IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun x y => abv_nonarch p x y`.
-/
theorem ultra : IsUltrametricDist (KK p) :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun x y => abv_nonarch p x y

/- English proof (translation)
Establish `hpos : (0 : ℝ) < (p : ℝ)⁻¹`. Use `hp.out.pos` as an intermediate fact. Check the signs of the components of the expression. Establish `hlt : (p : ℝ)⁻¹ < 1` using `inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)`. Use `Metric.complete_of_convergent_controlled_sequences (fun n => ((p : ℝ)⁻¹) ^ n) (fun n => pow_pos hpos n) ?_` and prove the remaining obligations.

Introduce `u hu`. Establish `h0 : ∀ n, ∃ w : WW p, algebraMap (WW p) (KK p) w = u n - u 0` using `fun n => (abv_le_one_iff p _).1 (by`. Use `hu 0 n 0 (Nat.zero_le _) le_rfl` as an intermediate fact. Rewrite `this` using `[dist_eq_norm, norm_def]`. Simplify using `using this.le)`.

Use `choose w hw using h0`. Establish `hc : ∀ {m n}, m ≤ n → w m ≡ w n [SMOD (Ideal.span {(p : WW p)} ^ m • ⊤ : Submodule (WW p) (WW p))]`. Introduce `m n hmn`. Rewrite using `[SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]`. Use `(hu m m n le_rfl hmn).le` as an intermediate fact.

Rewrite `this` using `[dist_eq_norm, norm_def]`. Take `⟨y, hy⟩` from `(abv_le_pow_iff p m _).1 this`. Use `⟨y, ?_⟩` and prove the remaining obligations. Apply `IsFractionRing.injective (WW p) (KK p)` to reduce the goal to its premises. Rewrite using `[map_sub, hw, hw, map_mul, map_pow, map_natCast, ← hy]`.

Expand and normalize the polynomial expressions, which then agree. Take `⟨L, hL⟩` from `IsPrecomplete.prec' (I := Ideal.span {(p : WW p)}) w hc`. Use `⟨u 0 + algebraMap (WW p) (KK p) L, ?_⟩` and prove the remaining obligations. Rewrite using `[tendsto_iff_norm_sub_tendsto_zero]`. Use `squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) (tendsto_pow_atTop_nhds_zero_of_lt_one hpos.le hlt)` and prove the remaining obligations.

Rewrite using `[norm_def, abv_le_pow_iff]`. Use `hL n` as an intermediate fact. Rewrite `this` using `[SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]`. Take `⟨y, hy⟩` from `this`. Use `⟨y, ?_⟩` and prove the remaining obligations.

Rewrite using `[← map_natCast (algebraMap (WW p) (KK p)), ← map_pow, ← map_mul, ← hy, map_sub, hw]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem complete : CompleteSpace (KK p) := by
  have hpos : (0 : ℝ) < (p : ℝ)⁻¹ := by
    have := hp.out.pos
    positivity
  have hlt : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)
  refine Metric.complete_of_convergent_controlled_sequences (fun n => ((p : ℝ)⁻¹) ^ n)
    (fun n => pow_pos hpos n) ?_
  intro u hu
  have h0 : ∀ n, ∃ w : WW p, algebraMap (WW p) (KK p) w = u n - u 0 := fun n =>
    (abv_le_one_iff p _).1 (by
      have := hu 0 n 0 (Nat.zero_le _) le_rfl
      rw [dist_eq_norm, norm_def] at this
      simpa using this.le)
  choose w hw using h0
  have hc : ∀ {m n}, m ≤ n →
      w m ≡ w n [SMOD (Ideal.span {(p : WW p)} ^ m • ⊤ : Submodule (WW p) (WW p))] := by
    intro m n hmn
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
    have := (hu m m n le_rfl hmn).le
    rw [dist_eq_norm, norm_def] at this
    obtain ⟨y, hy⟩ := (abv_le_pow_iff p m _).1 this
    refine ⟨y, ?_⟩
    apply IsFractionRing.injective (WW p) (KK p)
    rw [map_sub, hw, hw, map_mul, map_pow, map_natCast, ← hy]
    ring
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := Ideal.span {(p : WW p)}) w hc
  refine ⟨u 0 + algebraMap (WW p) (KK p) L, ?_⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_)
    (tendsto_pow_atTop_nhds_zero_of_lt_one hpos.le hlt)
  rw [norm_def, abv_le_pow_iff]
  have := hL n
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton] at this
  obtain ⟨y, hy⟩ := this
  refine ⟨y, ?_⟩
  rw [← map_natCast (algebraMap (WW p) (KK p)), ← map_pow, ← map_mul, ← hy, map_sub, hw]
  ring

end WModel

open WModel in
/- English proof (translation)
Introduce `p _ hp2`. Establish `hW : CharZero (WW p)` using `Formalism.FG.witt_char_zero p`. Take `⟨ζ, hζ⟩` from `Formalism.FG.witt_teichmuller_root p 2 (by norm_num)`. Use `⟨KK p, nf p, ?_, ?_, complete p, sig p, ⟨Fact.out, hp2, abv_p p, abv_value p, abv_sig p⟩, algebraMap (WW p) (KK p) ζ, hζ.map_of_injective (IsFractionRing.injective (WW p) (KK p))⟩` and prove the remaining obligations. Conclude with `ultra p`.

Conclude with `charZero_of_injective_algebraMap (IsFractionRing.injective (WW p) (KK p))`.
-/
theorem modelExists_statement : ModelExists := by
  intro p _ hp2
  have hW : CharZero (WW p) := Formalism.FG.witt_char_zero p
  obtain ⟨ζ, hζ⟩ := Formalism.FG.witt_teichmuller_root p 2 (by norm_num)
  refine ⟨KK p, nf p, ?_, ?_, complete p, sig p, ⟨Fact.out, hp2, abv_p p, abv_value p, abv_sig p⟩,
    algebraMap (WW p) (KK p) ζ, hζ.map_of_injective (IsFractionRing.injective (WW p) (KK p))⟩
  · exact ultra p
  · exact charZero_of_injective_algebraMap (IsFractionRing.injective (WW p) (KK p))

/- English proof (translation)
Introduce `p _ hp2`. Take `⟨K, i1, h1, h2, h3, σ, hσ, ζ, hζ⟩` from `hM p hp2`. Take `⟨⟨F, hF⟩, -⟩` from `hL K p hσ.1 hσ.2.2.1`. Use `⟨K, i1, h1, h2, h3, σ, F, Gser p 1 (σ 1), hσ, ⟨ζ, hζ⟩, hF, ?_, ?_⟩` and prove the remaining obligations. Conclude with `hG K p σ hσ F hF 1 (by simp) (by simp)`.

Introduce `h`. Establish `h0 : (0 : MvPowerSeries (Fin 2) K) = Gser p 0 (σ 0)` using `by simp [Gser]`. Rewrite `h` using `[h0]`. Conclude with `one_ne_zero (hU K p σ hσ 1 0 (by simp) (by simp) h)`.
-/
theorem BetaNonVacuous_of (hM : ModelExists) (hL : LawExists) (hG : GcIsBeta) (hU : GcUnique) :
    BetaNonVacuous := by
  intro p _ hp2
  obtain ⟨K, i1, h1, h2, h3, σ, hσ, ζ, hζ⟩ := hM p hp2
  obtain ⟨⟨F, hF⟩, -⟩ := hL K p hσ.1 hσ.2.2.1
  refine ⟨K, i1, h1, h2, h3, σ, F, Gser p 1 (σ 1), hσ, ⟨ζ, hζ⟩, hF, ?_, ?_⟩
  · exact hG K p σ hσ F hF 1 (by simp) (by simp)
  · intro h
    have h0 : (0 : MvPowerSeries (Fin 2) K) = Gser p 0 (σ 0) := by simp [Gser]
    rw [h0] at h
    exact one_ne_zero (hU K p σ hσ 1 0 (by simp) (by simp) h)

end Formalism.InvariantFactorPaths.G7
