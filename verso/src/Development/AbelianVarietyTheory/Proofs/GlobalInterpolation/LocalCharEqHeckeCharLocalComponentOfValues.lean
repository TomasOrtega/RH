import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CharacterValueAtT
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LocCharEqZpowMul
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker

namespace GlobalTheory.LocCharComp

/- English proof (translation)
Establish `hle : Ideal.span {π} ≤ P.asIdeal` using `(Ideal.span_singleton_le_iff_mem _).2 hπ`. Take `⟨J, hJ⟩` from `Ideal.dvd_iff_le.2 hle`. Establish `hJP : ¬ J ≤ P.asIdeal`. Introduce `h`. Apply `hπ2` to reduce the goal to its premises.

Establish `hsub : Ideal.span {π} ≤ P.asIdeal ^ 2`. Rewrite using `[hJ, pow_two]`. Conclude with `Ideal.mul_mono_right h`. Conclude with `hsub (Ideal.mem_span_singleton_self π)`. Take `⟨s, hsJ, hsP⟩` from `SetLike.not_le_iff_exists.1 hJP`.

Use `⟨s, hsP, fun x hx => ?_⟩` and prove the remaining obligations. Establish `hmem : x * s ∈ Ideal.span {π}` using `hJ ▸ Ideal.mul_mem_mul hx hsJ`. Take `⟨x₂, hx₂⟩` from `Ideal.mem_span_singleton'.1 hmem`. Conclude with `⟨x₂, hx₂.symm⟩`.
-/
private theorem eventually_abs_le_half_add_of_doubling_bounds {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (π : 𝓞 E)
    (hπ : π ∈ P.asIdeal) (hπ2 : π ∉ P.asIdeal ^ 2) :
    ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ ∀ x ∈ P.asIdeal, ∃ x₂ : 𝓞 E, x * s = x₂ * π := by
  have hle : Ideal.span {π} ≤ P.asIdeal := (Ideal.span_singleton_le_iff_mem _).2 hπ
  obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.2 hle
  have hJP : ¬ J ≤ P.asIdeal := by
    intro h
    apply hπ2
    have hsub : Ideal.span {π} ≤ P.asIdeal ^ 2 := by
      rw [hJ, pow_two]
      exact Ideal.mul_mono_right h
    exact hsub (Ideal.mem_span_singleton_self π)
  obtain ⟨s, hsJ, hsP⟩ := SetLike.not_le_iff_exists.1 hJP
  refine ⟨s, hsP, fun x hx => ?_⟩
  have hmem : x * s ∈ Ideal.span {π} := hJ ▸ Ideal.mul_mem_mul hx hsJ
  obtain ⟨x₂, hx₂⟩ := Ideal.mem_span_singleton'.1 hmem
  exact ⟨x₂, hx₂.symm⟩

/- English proof (translation)
Take `⟨s₀, hs₀, hstep⟩` from `eventually_abs_le_half_add_of_doubling_bounds P π hπ hπ2`. Establish `h1 : (1 : 𝓞 E) ∉ P.asIdeal` using `(Ideal.ne_top_iff_one _).1 P.isPrime.ne_top`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`.

Introduce `x hx`. Conclude with `⟨0, 1, x, h1, by simpa using hx, by simp⟩`. Consider the case `succ n ih`. Introduce `x hx`. Distinguish the cases in `hxP : x ∈ P.asIdeal`.

Take `⟨x₂, hx₂⟩` from `hstep x hxP`. Establish `hx₂n : x₂ ∉ P.asIdeal ^ (n + 1)`. Introduce `h`. Apply `hx` to reduce the goal to its premises. Establish `hmem : x * s₀ ∈ P.asIdeal ^ (n + 1 + 1)`.

Rewrite using `[hx₂, pow_succ]`. Conclude with `Ideal.mul_mem_mul h hπ`. Establish `hv` using `(P.intValuation_le_pow_iff_mem _ _).2 hmem`. Rewrite `hv` using `[map_mul, HeightOneSpectrum.intValuation_eq_one_iff.2 hs₀, mul_one]`. Conclude with `(P.intValuation_le_pow_iff_mem _ _).1 hv`.

Take `⟨m, s, x', hs, hx', he⟩` from `ih x₂ hx₂n`. Use `⟨m + 1, s * s₀, x', fun h => (P.isPrime.mem_or_mem h).elim hs hs₀, hx', ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Conclude with `⟨0, 1, x, h1, hxP, by simp⟩`.
-/
private theorem exists_unit_mul_eq_mul_uniformizer_pow {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (π : 𝓞 E)
    (hπ : π ∈ P.asIdeal) (hπ2 : π ∉ P.asIdeal ^ 2) :
    ∀ n : ℕ, ∀ x : 𝓞 E, x ∉ P.asIdeal ^ (n + 1) →
      ∃ (m : ℕ) (s x' : 𝓞 E), s ∉ P.asIdeal ∧ x' ∉ P.asIdeal ∧ s * x = x' * π ^ m := by
  obtain ⟨s₀, hs₀, hstep⟩ := eventually_abs_le_half_add_of_doubling_bounds P π hπ hπ2
  have h1 : (1 : 𝓞 E) ∉ P.asIdeal := (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top
  intro n
  induction n with
  | zero =>
    intro x hx
    exact ⟨0, 1, x, h1, by simpa using hx, by simp⟩
  | succ n ih =>
    intro x hx
    by_cases hxP : x ∈ P.asIdeal
    · obtain ⟨x₂, hx₂⟩ := hstep x hxP
      have hx₂n : x₂ ∉ P.asIdeal ^ (n + 1) := by
        intro h
        apply hx
        have hmem : x * s₀ ∈ P.asIdeal ^ (n + 1 + 1) := by
          rw [hx₂, pow_succ]
          exact Ideal.mul_mem_mul h hπ
        have hv := (P.intValuation_le_pow_iff_mem _ _).2 hmem
        rw [map_mul, HeightOneSpectrum.intValuation_eq_one_iff.2 hs₀, mul_one] at hv
        exact (P.intValuation_le_pow_iff_mem _ _).1 hv
      obtain ⟨m, s, x', hs, hx', he⟩ := ih x₂ hx₂n
      refine ⟨m + 1, s * s₀, x', fun h => (P.isPrime.mem_or_mem h).elim hs hs₀, hx', ?_⟩
      calc s * s₀ * x = s * (x * s₀) := by ring
        _ = s * x₂ * π := by rw [hx₂]; ring
        _ = x' * π ^ (m + 1) := by rw [he]; ring
    · exact ⟨0, 1, x, h1, hxP, by simp⟩

/- English proof (translation)
Take `⟨n, hn⟩ : ∃ n : ℕ, P.intValuation x = WithZero.exp (-(n : ℤ))` from `⟨_, P.intValuation_if_neg hx⟩`. Use `⟨n, fun h => ?_⟩` and prove the remaining obligations. Establish `hv` using `(P.intValuation_le_pow_iff_mem _ _).2 h`. Rewrite `hv` using `[hn, WithZero.exp_le_exp]`. Move the coercions through the operations in `at hv`.

Use linear arithmetic over natural numbers and integers.
-/
private theorem exists_notMem_pow_succ {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (x : 𝓞 E)
    (hx : x ≠ 0) : ∃ n : ℕ, x ∉ P.asIdeal ^ (n + 1) := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, P.intValuation x = WithZero.exp (-(n : ℤ)) := ⟨_, P.intValuation_if_neg hx⟩
  refine ⟨n, fun h => ?_⟩
  have hv := (P.intValuation_le_pow_iff_mem _ _).2 h
  rw [hn, WithZero.exp_le_exp] at hv
  push_cast at hv
  omega

/- English proof (translation)
Take `⟨x, y, hy, rfl⟩` from `IsFractionRing.div_surjective (𝓞 E) a`. Establish `hinj` using `IsFractionRing.injective (𝓞 E) E`. Establish `hy0 : y ≠ 0` using `nonZeroDivisors.ne_zero hy`. Establish `hx0 : x ≠ 0`. Introduce and unpack `rfl`.

Simplify using `at ha`. Take `⟨n₁, hn₁⟩` from `exists_notMem_pow_succ P x hx0`. Take `⟨n₂, hn₂⟩` from `exists_notMem_pow_succ P y hy0`. Take `⟨m₁, s₁, x₁, hs₁, hx₁, e₁⟩` from `exists_unit_mul_eq_mul_uniformizer_pow P π hπ hπ2 n₁ x hn₁`. Take `⟨m₂, s₂, y₁, hs₂, hy₁, e₂⟩` from `exists_unit_mul_eq_mul_uniformizer_pow P π hπ hπ2 n₂ y hn₂`.

Use `⟨(m₁ : ℤ) - m₂, x₁ * s₂, y₁ * s₁, fun h => (P.isPrime.mem_or_mem h).elim hx₁ hs₂, fun h => (P.isPrime.mem_or_mem h).elim hy₁ hs₁, ?_⟩` and prove the remaining obligations. Establish `e₁'` using `congrArg (algebraMap (𝓞 E) E) e₁`. Establish `e₂'` using `congrArg (algebraMap (𝓞 E) E) e₂`. Simplify using `only [map_mul, map_pow] at e₁' e₂'`. Establish `hπ0 : π ≠ 0`.

Introduce and unpack `rfl`. Conclude with `hπ2 (Submodule.zero_mem _)`. Establish `hY : algebraMap (𝓞 E) E y ≠ 0` using `(map_ne_zero_iff _ hinj).2 hy0`. Establish `hpi : algebraMap (𝓞 E) E π ≠ 0` using `(map_ne_zero_iff _ hinj).2 hπ0`. Rewrite using `[zpow_sub₀ hpi, zpow_natCast, zpow_natCast, map_mul, map_mul]`.

Clear the denominators using the available nonvanishing facts. Take the linear combination `(algebraMap (𝓞 E) E y₁ * algebraMap (𝓞 E) E π ^ m₂) * e₁' - (algebraMap (𝓞 E) E x₁ * algebraMap (𝓞 E) E π ^ m₁) * e₂'`.
-/
private theorem exists_zpow_uniformizer_factorization {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (π : 𝓞 E)
    (hπ : π ∈ P.asIdeal) (hπ2 : π ∉ P.asIdeal ^ 2) (a : E) (ha : a ≠ 0) :
    ∃ (z : ℤ) (r s : 𝓞 E), r ∉ P.asIdeal ∧ s ∉ P.asIdeal ∧
      algebraMap (𝓞 E) E s * a = algebraMap (𝓞 E) E r * algebraMap (𝓞 E) E π ^ z := by
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (𝓞 E) a
  have hinj := IsFractionRing.injective (𝓞 E) E
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at ha
  obtain ⟨n₁, hn₁⟩ := exists_notMem_pow_succ P x hx0
  obtain ⟨n₂, hn₂⟩ := exists_notMem_pow_succ P y hy0
  obtain ⟨m₁, s₁, x₁, hs₁, hx₁, e₁⟩ := exists_unit_mul_eq_mul_uniformizer_pow P π hπ hπ2 n₁ x hn₁
  obtain ⟨m₂, s₂, y₁, hs₂, hy₁, e₂⟩ := exists_unit_mul_eq_mul_uniformizer_pow P π hπ hπ2 n₂ y hn₂
  refine ⟨(m₁ : ℤ) - m₂, x₁ * s₂, y₁ * s₁, fun h => (P.isPrime.mem_or_mem h).elim hx₁ hs₂,
    fun h => (P.isPrime.mem_or_mem h).elim hy₁ hs₁, ?_⟩
  have e₁' := congrArg (algebraMap (𝓞 E) E) e₁
  have e₂' := congrArg (algebraMap (𝓞 E) E) e₂
  simp only [map_mul, map_pow] at e₁' e₂'
  have hπ0 : π ≠ 0 := by
    rintro rfl
    exact hπ2 (Submodule.zero_mem _)
  have hY : algebraMap (𝓞 E) E y ≠ 0 := (map_ne_zero_iff _ hinj).2 hy0
  have hpi : algebraMap (𝓞 E) E π ≠ 0 := (map_ne_zero_iff _ hinj).2 hπ0
  rw [zpow_sub₀ hpi, zpow_natCast, zpow_natCast, map_mul, map_mul]
  field_simp
  linear_combination (algebraMap (𝓞 E) E y₁ * algebraMap (𝓞 E) E π ^ m₂) * e₁' -
    (algebraMap (𝓞 E) E x₁ * algebraMap (𝓞 E) E π ^ m₁) * e₂'

/- English proof (translation)
Use `P.isPrime` as an intermediate fact. Unfold `redP at hb ⊢`. Use `split_ifs at hb ⊢ with h`. Take `⟨r, s, hs, hsb, hc⟩` from `h.choose_spec`. Use `⟨r, s, fun hr => ?_, hs, hsb, hc⟩` and prove the remaining obligations.

Rewrite `hc` using `[Ideal.Quotient.eq_zero_iff_mem.2 hr, hb.mul_left_eq_zero]`. Conclude with `hs (Ideal.Quotient.eq_zero_iff_mem.1 hc)`. Conclude with `absurd hb not_isUnit_zero`.
-/
private theorem exists_integer_ratio_of_isUnit_redP {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (b : E)
    (hb : IsUnit (redP P b)) :
    ∃ r s : 𝓞 E, r ∉ P.asIdeal ∧ s ∉ P.asIdeal ∧ algebraMap (𝓞 E) E s * b = algebraMap (𝓞 E) E r ∧
      Ideal.Quotient.mk P.asIdeal s * redP P b = Ideal.Quotient.mk P.asIdeal r := by
  have := P.isPrime
  unfold redP at hb ⊢
  split_ifs at hb ⊢ with h
  · obtain ⟨r, s, hs, hsb, hc⟩ := h.choose_spec
    refine ⟨r, s, fun hr => ?_, hs, hsb, hc⟩
    rw [Ideal.Quotient.eq_zero_iff_mem.2 hr, hb.mul_left_eq_zero] at hc
    exact hs (Ideal.Quotient.eq_zero_iff_mem.1 hc)
  · exact absurd hb not_isUnit_zero

/- English proof (translation)
Set `` to `Ideal.Quotient.field P.asIdeal`. Establish `hs' : Ideal.Quotient.mk P.asIdeal s ≠ 0` using `fun h => hs (Ideal.Quotient.eq_zero_iff_mem.1 h)`. Establish `hex : ∃ c : 𝓞 E ⧸ P.asIdeal, ∃ r s : 𝓞 E, s ∉ P.asIdeal ∧ algebraMap (𝓞 E) E s * b = algebraMap (𝓞 E) E r ∧ Ideal.Quotient.mk P.asIdeal s * c = Ideal.Quotient.mk P.asIdeal r` using `⟨Ideal.Quotient.mk P.asIdeal r * (Ideal.Quotient.mk P.asIdeal s)⁻¹, r, s, hs, hsb, by rw [mul_comm (Ideal.Quotient.mk P.asIdeal r), ← mul_assoc, mul_inv_cancel₀ hs', one_mul]⟩`. Unfold `redP`. Rewrite using `[dif_pos hex]`.

Take `⟨r₂, s₂, hs₂, hsb₂, hc₂⟩` from `hex.choose_spec`. Use `isUnit_iff_ne_zero.2 fun h0 => ?_` and prove the remaining obligations. Rewrite `hc₂` using `[h0, mul_zero, eq_comm, Ideal.Quotient.eq_zero_iff_mem]`. Establish `he : s * r₂ = s₂ * r` using `IsFractionRing.injective (𝓞 E) E (by`. Simplify using `only [map_mul]`.

Rewrite using `[← hsb₂, ← hsb]`. Use the proof step `ring)`. Establish `hmem : s₂ * r ∈ P.asIdeal` using `he ▸ Ideal.mul_mem_left _ s hc₂`. Conclude with `(P.isPrime.mem_or_mem hmem).elim hs₂ hr`.
-/
private theorem isUnit_redP_of_integer_ratio {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (b : E)
    (r s : 𝓞 E) (hr : r ∉ P.asIdeal) (hs : s ∉ P.asIdeal)
    (hsb : algebraMap (𝓞 E) E s * b = algebraMap (𝓞 E) E r) : IsUnit (redP P b) := by
  let := Ideal.Quotient.field P.asIdeal
  have hs' : Ideal.Quotient.mk P.asIdeal s ≠ 0 := fun h => hs (Ideal.Quotient.eq_zero_iff_mem.1 h)
  have hex : ∃ c : 𝓞 E ⧸ P.asIdeal, ∃ r s : 𝓞 E, s ∉ P.asIdeal ∧
      algebraMap (𝓞 E) E s * b = algebraMap (𝓞 E) E r ∧
      Ideal.Quotient.mk P.asIdeal s * c = Ideal.Quotient.mk P.asIdeal r :=
    ⟨Ideal.Quotient.mk P.asIdeal r * (Ideal.Quotient.mk P.asIdeal s)⁻¹, r, s, hs, hsb,
      by rw [mul_comm (Ideal.Quotient.mk P.asIdeal r), ← mul_assoc, mul_inv_cancel₀ hs', one_mul]⟩
  unfold redP
  rw [dif_pos hex]
  obtain ⟨r₂, s₂, hs₂, hsb₂, hc₂⟩ := hex.choose_spec
  refine isUnit_iff_ne_zero.2 fun h0 => ?_
  rw [h0, mul_zero, eq_comm, Ideal.Quotient.eq_zero_iff_mem] at hc₂
  have he : s * r₂ = s₂ * r := IsFractionRing.injective (𝓞 E) E (by
    simp only [map_mul]
    rw [← hsb₂, ← hsb]
    ring)
  have hmem : s₂ * r ∈ P.asIdeal := he ▸ Ideal.mul_mem_left _ s hc₂
  exact (P.isPrime.mem_or_mem hmem).elim hs₂ hr

/- English proof (translation)
Introduce `E K _ _ _ σ P ψ cq t hq2 h1 h2 a`. Use `P.isPrime` as an intermediate fact. Set `` to `Ideal.Quotient.field P.asIdeal`. Establish `hinj` using `IsFractionRing.injective (𝓞 E) E`. Establish `hπ : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∈ P.asIdeal` using `Ideal.absNorm_mem _`.

Establish `hπE : ((qOf P : ℕ) : E) = algebraMap (𝓞 E) E ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E)`. Rewrite using `[map_natCast]`. Both sides reduce to the same expression. Establish `hπne : ((qOf P : ℕ) : E) ≠ 0`. Rewrite using `[hπE]`.

Use `(map_ne_zero_iff _ hinj).2 fun h0 => hq2 ?_` and prove the remaining obligations. Rewrite using `[h0]`. Conclude with `Submodule.zero_mem _`. Establish `hex : ∃ z : ℤ, IsUnit (redP P ((a : E) / ((qOf P : ℕ) : E) ^ z))`. Take `⟨z, r, s, hr, hs, hsa⟩` from `exists_zpow_uniformizer_factorization P _ hπ hq2 (a : E) a.ne_zero`.

Use `⟨z, isUnit_redP_of_integer_ratio P _ r s hr hs ?_⟩` and prove the remaining obligations. Rewrite using `[hπE, mul_div_assoc', hsa, mul_div_assoc, div_self (zpow_ne_zero _ (hπE ▸ hπne)), mul_one]`. Establish `hU : IsUnit (redP P ((a : E) / ((qOf P : ℕ) : E) ^ LocE.vP P (qOf P) (a : E)))` using `Classical.epsilon_spec hex`. Take `⟨r, s, hr, hs, hsb, hc⟩` from `exists_integer_ratio_of_isUnit_redP P _ hU`. Establish `hr0 : algebraMap (𝓞 E) E r ≠ 0` using `(map_ne_zero_iff _ hinj).2 fun h0 => hr (h0 ▸ Submodule.zero_mem _)`.

Establish `hs0 : algebraMap (𝓞 E) E s ≠ 0` using `(map_ne_zero_iff _ hinj).2 fun h0 => hs (h0 ▸ Submodule.zero_mem _)`. Establish `hmr : Ideal.Quotient.mk P.asIdeal r ≠ 0` using `fun h => hr (Ideal.Quotient.eq_zero_iff_mem.1 h)`. Establish `hms : Ideal.Quotient.mk P.asIdeal s ≠ 0` using `fun h => hs (Ideal.Quotient.eq_zero_iff_mem.1 h)`. Use `set w := LocE.vP P (qOf P) (a : E)`. Set `Q : Eˣ` to `Units.mk0 _ hπne`.

Set `xr : Eˣ` to `Units.mk0 _ hr0`. Set `xs : Eˣ` to `Units.mk0 _ hs0`. Set `cr : (𝓞 E ⧸ P.asIdeal)ˣ` to `Units.mk0 _ hmr`. Set `cs : (𝓞 E ⧸ P.asIdeal)ˣ` to `Units.mk0 _ hms`. Establish `hA : a = Q ^ w * xr * xs⁻¹`.

Use `ext`. Simplify using `only [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_inv_eq_inv_val, Units.val_mk0, Q, xr, xs]`. Rewrite using `[← hsb]`. Clear the denominators using the available nonvanishing facts. Establish `hB : hU.unit = cr * cs⁻¹`.

Use `ext`. Simplify using `only [IsUnit.unit_spec, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, cr, cs]`. Rewrite using `[← hc]`. Clear the denominators using the available nonvanishing facts. Establish `eQ` using `h1 Q rfl`.

Establish `er` using `h2 xr r cr rfl rfl`. Establish `es` using `h2 xs s cs rfl rfl`. Use `show σ (cq ^ w * LocE.unitV t ((a : E) / ((qOf P : ℕ) : E) ^ w)) = _`. Unfold `LocE.unitV`. Rewrite using `[dif_pos hU, hB]`.

Use `conv_rhs => rw [hA]`. Simplify using `only [map_mul, map_inv, map_zpow, map_zpow₀, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, map_inv₀, eQ, er, es]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem locChar_eq_locK : ∀ (E K : Type) [Field E] [NumberField E] [Field K] (σ : K →+* ℂ) (P : HeightOneSpectrum (𝓞 E)) (ψ : Formalism.L2.Host.HChar E) (cq : K) (t : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ), ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2 → (∀ q : Eˣ, (q : E) = ((Ideal.absNorm P.asIdeal : ℕ) : E) → σ cq = ((ψ.locK P q : ℂˣ) : ℂ)) → (∀ (x : Eˣ) (y : 𝓞 E) (c : (𝓞 E ⧸ P.asIdeal)ˣ), (x : E) = (y : E) → (c : 𝓞 E ⧸ P.asIdeal) = Ideal.Quotient.mk P.asIdeal y → σ ((t c : Kˣ) : K) = ((ψ.locK P x : ℂˣ) : ℂ)) → ∀ a : Eˣ, σ (LocE.locChar (Formalism.L2.Col.qOf P) cq t (a : E)) = ((ψ.locK P a : ℂˣ) : ℂ) := by
  intro E K _ _ _ σ P ψ cq t hq2 h1 h2 a
  have := P.isPrime
  let := Ideal.Quotient.field P.asIdeal
  have hinj := IsFractionRing.injective (𝓞 E) E
  have hπ : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∈ P.asIdeal := Ideal.absNorm_mem _
  have hπE : ((qOf P : ℕ) : E) = algebraMap (𝓞 E) E ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) := by
    rw [map_natCast]
    rfl
  have hπne : ((qOf P : ℕ) : E) ≠ 0 := by
    rw [hπE]
    refine (map_ne_zero_iff _ hinj).2 fun h0 => hq2 ?_
    rw [h0]
    exact Submodule.zero_mem _
  have hex : ∃ z : ℤ, IsUnit (redP P ((a : E) / ((qOf P : ℕ) : E) ^ z)) := by
    obtain ⟨z, r, s, hr, hs, hsa⟩ := exists_zpow_uniformizer_factorization P _ hπ hq2 (a : E) a.ne_zero
    refine ⟨z, isUnit_redP_of_integer_ratio P _ r s hr hs ?_⟩
    rw [hπE, mul_div_assoc', hsa, mul_div_assoc, div_self (zpow_ne_zero _ (hπE ▸ hπne)), mul_one]
  have hU : IsUnit (redP P ((a : E) / ((qOf P : ℕ) : E) ^ LocE.vP P (qOf P) (a : E))) :=
    Classical.epsilon_spec hex
  obtain ⟨r, s, hr, hs, hsb, hc⟩ := exists_integer_ratio_of_isUnit_redP P _ hU
  have hr0 : algebraMap (𝓞 E) E r ≠ 0 := (map_ne_zero_iff _ hinj).2 fun h0 => hr (h0 ▸ Submodule.zero_mem _)
  have hs0 : algebraMap (𝓞 E) E s ≠ 0 := (map_ne_zero_iff _ hinj).2 fun h0 => hs (h0 ▸ Submodule.zero_mem _)
  have hmr : Ideal.Quotient.mk P.asIdeal r ≠ 0 := fun h => hr (Ideal.Quotient.eq_zero_iff_mem.1 h)
  have hms : Ideal.Quotient.mk P.asIdeal s ≠ 0 := fun h => hs (Ideal.Quotient.eq_zero_iff_mem.1 h)
  set w := LocE.vP P (qOf P) (a : E)
  let Q : Eˣ := Units.mk0 _ hπne
  let xr : Eˣ := Units.mk0 _ hr0
  let xs : Eˣ := Units.mk0 _ hs0
  let cr : (𝓞 E ⧸ P.asIdeal)ˣ := Units.mk0 _ hmr
  let cs : (𝓞 E ⧸ P.asIdeal)ˣ := Units.mk0 _ hms
  have hA : a = Q ^ w * xr * xs⁻¹ := by
    ext
    simp only [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_inv_eq_inv_val, Units.val_mk0, Q, xr, xs]
    rw [← hsb]
    field_simp
  have hB : hU.unit = cr * cs⁻¹ := by
    ext
    simp only [IsUnit.unit_spec, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, cr, cs]
    rw [← hc]
    field_simp
  have eQ := h1 Q rfl
  have er := h2 xr r cr rfl rfl
  have es := h2 xs s cs rfl rfl
  show σ (cq ^ w * LocE.unitV t ((a : E) / ((qOf P : ℕ) : E) ^ w)) = _
  unfold LocE.unitV
  rw [dif_pos hU, hB]
  conv_rhs => rw [hA]
  simp only [map_mul, map_inv, map_zpow, map_zpow₀, Units.val_mul, Units.val_inv_eq_inv_val,
    Units.val_zpow_eq_zpow_val, map_inv₀, eQ, er, es]
  ring

end GlobalTheory.LocCharComp
