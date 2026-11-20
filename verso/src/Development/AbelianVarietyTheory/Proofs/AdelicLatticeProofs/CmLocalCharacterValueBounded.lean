import Mathlib
import Formalism.UnipotentAdelicQuotients.ThmBInHecke
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CmExtensionAdelesStandardModelDictionaryStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsPrimeIdempotentCMFieldStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PrimeIdempotentEqIndicatorPrimeStatement
open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical HeckeCharacterZeroLocus.ThmBIn
open scoped TensorProduct ContDiff nonZeroDivisors

namespace GlobalTheory.HeckeUnif

/- English proof (translation)
Take the linear combination `(a * b - a - b + 1) * he`.
-/
theorem idem_glue_mul {R : Type*} [CommRing R] {e : R} (he : e * e = e) (a b : R) :
    (e * a + (1 - e)) * (e * b + (1 - e)) = e * (a * b) + (1 - e) := by
  linear_combination (a * b - a - b + 1) * he

/- English proof (translation)
Establish `ha : a ≠ 0` using `by rintro rfl; exact h2 (zero_mem _)`. Establish `k1 : P.intValuation a ≤ WithZero.exp (-((1 : ℕ) : ℤ))`. Rewrite using `[HeightOneSpectrum.intValuation_le_pow_iff_mem]`. Simplify using `using h1`. Establish `k2 : ¬ P.intValuation a ≤ WithZero.exp (-((2 : ℕ) : ℤ))`.

Rewrite using `[HeightOneSpectrum.intValuation_le_pow_iff_mem]`. Conclude with `h2`. Establish `h0 : P.intValuation a ≠ 0` using `HeightOneSpectrum.intValuation_ne_zero P a ha`. Rewrite `k1`, `k2`, the goal using `[← WithZero.exp_log h0]`. Rewrite `k1`, `k2` using `[WithZero.exp_le_exp]`.

Use `congr 1`. Use linear arithmetic over natural numbers and integers.
-/
theorem intValuation_of_mem_notMem_sq {R : Type*} [CommRing R] [IsDedekindDomain R]
    (P : HeightOneSpectrum R) {a : R} (h1 : a ∈ P.asIdeal) (h2 : a ∉ P.asIdeal ^ 2) :
    P.intValuation a = WithZero.exp (-1 : ℤ) := by
  have ha : a ≠ 0 := by rintro rfl; exact h2 (zero_mem _)
  have k1 : P.intValuation a ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
    rw [HeightOneSpectrum.intValuation_le_pow_iff_mem]; simpa using h1
  have k2 : ¬ P.intValuation a ≤ WithZero.exp (-((2 : ℕ) : ℤ)) := by
    rw [HeightOneSpectrum.intValuation_le_pow_iff_mem]; exact h2
  have h0 : P.intValuation a ≠ 0 := HeightOneSpectrum.intValuation_ne_zero P a ha
  rw [← WithZero.exp_log h0] at k1 k2 ⊢
  rw [WithZero.exp_le_exp] at k1 k2
  congr 1
  omega

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hσ χ P`. Take `⟨Φ, h1, h2, h3, -, -⟩` from `GlobalTheory.T.cmExtension_adeles_standardModel_dictionary F E σ hσ`. Establish `hu` using `GlobalTheory.T.primeIdempotent_eq_indicator_prime F E σ Φ h1 h2 h3 P`. Take `⟨e, f, hef⟩` from `GlobalTheory.T.exists_primeIdempotent_CMField F E σ hσ P`. Take `⟨ea, eb, ec⟩` from `hu e f hef`.

Establish `huniq : ∀ e' f', IsPrimeIdem σ P e' f' → e' = e`. Introduce `e' f' h'`. Take `⟨ea', eb', ec'⟩` from `hu e' f' h'`. Apply `Φ.injective` to reduce the goal to its premises. Use `Prod.ext (by rw [ea, ea']) ?_` and prove the remaining obligations.

Use extensionality with `Q`. Distinguish the cases in `hQ : Q = P`. Substitute `hQ` using the available equality. Rewrite using `[eb, eb']`. Rewrite using `[ec Q hQ, ec' Q hQ]`.

Set `ψ : ∀ Q : HeightOneSpectrum (𝓞 E), AE F E →+* Q.adicCompletion E` to `fun Q => ((evalV E Q).toRingHom.comp (RingHom.snd _ _)).comp Φ.toRingHom`. Establish `hψ : ∀ Q y, (Φ y).2 Q = ψ Q y` using `fun _ _ => rfl`. Establish `he : e * e = e`. Apply `Φ.injective` to reduce the goal to its premises. Use `Prod.ext (by rw [map_mul, Prod.fst_mul, ea, mul_zero]) ?_` and prove the remaining obligations.

Use extensionality with `Q`. Rewrite using `[hψ, hψ, map_mul, ← hψ]`. Distinguish the cases in `hQ : Q = P`. Substitute `hQ` using the available equality. Rewrite using `[eb, mul_one]`.

Rewrite using `[ec Q hQ, mul_zero]`. Establish `hint : ∀ c : E, P.valuation E c ≤ 1 → finPart F E (e * incA F E c + (1 - e)) ∈ intAE F E`. Introduce `c hc`. Rewrite using `[h2]`. Introduce `Q`.

Rewrite using `[hψ, map_add, map_sub, map_mul, map_one, ← hψ, ← hψ]`. Distinguish the cases in `hQ : Q = P`. Substitute `hQ` using the available equality. Rewrite using `[eb, h1, one_mul, sub_self, add_zero]`. Establish `: Valued.v ((algebraMap E (FiniteAdeleRing (𝓞 E) E) c) Q) = Q.valuation E c` using `HeightOneSpectrum.valuedAdicCompletion_eq_valuation' Q c`.

Conclude with `this.le.trans hc`. Rewrite using `[ec Q hQ]`. Simplify using the standard rewrite rules. Establish `hex : ∃ x, IsUnifIdele σ P x`. Take `⟨ϖ, m1, m2⟩` from `Ideal.exists_mem_pow_notMem_pow_succ P.asIdeal P.ne_bot P.isPrime.ne_top 1`.

Establish `hϖ : (ϖ : E) ≠ 0`. Introduce `h`. Establish `: ϖ = 0` using `by exact_mod_cast h`. Conclude with `m2 (this ▸ zero_mem _)`. Establish `hm : (e * incA F E (ϖ : E) + (1 - e)) * (e * incA F E (ϖ : E)⁻¹ + (1 - e)) = 1`.

Rewrite using `[idem_glue_mul he, ← map_mul, mul_inv_cancel₀ hϖ, map_one]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `⟨⟨_, _, hm, by rw [mul_comm, hm]⟩, e, f, ϖ, hef, by simpa using m1, m2, rfl⟩`. Establish `hq : ∀ x y : (AE F E)ˣ, IsUnifIdele σ P x → IsUnifIdele σ P y → ∃ c : E, P.valuation E c ≤ 1 ∧ ((x * y⁻¹ : (AE F E)ˣ) : AE F E) = e * incA F E c + (1 - e)`. Introduce and unpack `x y ⟨e1, f1, a, p1, a1, a2, hx⟩ ⟨e2, f2, b, p2, b1, b2, hy⟩`.

Rewrite `hx` using `[huniq _ _ p1]`. Rewrite `hy` using `[huniq _ _ p2]`. Establish `hb : (b : E) ≠ 0`. Introduce `h`. Establish `: b = 0` using `by exact_mod_cast h`.

Conclude with `b2 (this ▸ zero_mem _)`. Use `⟨(a : E) / (b : E), ?_, ?_⟩` and prove the remaining obligations. Establish `va : P.valuation E (a : E) = WithZero.exp (-1 : ℤ)`. Rewrite using `[← intValuation_of_mem_notMem_sq P a1 a2]`. Conclude with `HeightOneSpectrum.valuation_of_algebraMap P a`.

Establish `vb : P.valuation E (b : E) = WithZero.exp (-1 : ℤ)`. Rewrite using `[← intValuation_of_mem_notMem_sq P b1 b2]`. Conclude with `HeightOneSpectrum.valuation_of_algebraMap P b`. Rewrite using `[map_div₀, va, vb, div_self WithZero.exp_ne_zero]`. Rewrite using `[Units.val_mul, Units.mul_inv_eq_iff_eq_mul, hx, hy, idem_glue_mul he, ← map_mul, div_mul_cancel₀ _ hb]`.

Use `⟨hex, ?_, ?_⟩` and prove the remaining obligations. Introduce `hun x hx`. Establish `hc : IsUnramAt σ χ P ∧ ∃ x, IsUnifIdele σ P x` using `⟨hun, hex⟩`. Rewrite using `[chiAt, dif_pos hc]`. Establish `hy` using `hc.2.choose_spec`.

Use `set y := hc.2.choose`. Take `⟨e', f', p', hχ⟩` from `hun`. Rewrite `hχ` using `[huniq _ _ p']`. Take `⟨c, c1, c2⟩` from `hq y x hy hx`. Take `⟨d, d1, d2⟩` from `hq x y hx hy`.

Use `hχ (y * x⁻¹) (by rw [c2]; linear_combination (1 - incA F E c) * he) (by rw [c2]; exact hint c c1) (by rw [mul_inv_rev, inv_inv, d2]; exact hint d d1)` as an intermediate fact. Rewrite `this` using `[map_mul, map_inv, mul_inv_eq_one]`. Rewrite using `[this]`. Rewrite using `[chiAt] split_ifs`. Conclude with `(Circle.norm_coe _).le`.

Simplify using the standard rewrite rules.
-/
theorem unifIdele_exists_chiAt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (χ : (AE F E)ˣ →* Circle) (P : HeightOneSpectrum (𝓞 E)), (∃ x, IsUnifIdele σ P x) ∧ (IsUnramAt σ χ P → ∀ x, IsUnifIdele σ P x → chiAt σ χ P = (χ x : ℂ)) ∧ ‖chiAt σ χ P‖ ≤ 1 := by
  intro F E _ _ _ _ _ σ hσ χ P
  obtain ⟨Φ, h1, h2, h3, -, -⟩ := GlobalTheory.T.cmExtension_adeles_standardModel_dictionary F E σ hσ
  have hu := GlobalTheory.T.primeIdempotent_eq_indicator_prime F E σ Φ h1 h2 h3 P
  obtain ⟨e, f, hef⟩ := GlobalTheory.T.exists_primeIdempotent_CMField F E σ hσ P
  obtain ⟨ea, eb, ec⟩ := hu e f hef
  have huniq : ∀ e' f', IsPrimeIdem σ P e' f' → e' = e := by
    intro e' f' h'
    obtain ⟨ea', eb', ec'⟩ := hu e' f' h'
    apply Φ.injective
    refine Prod.ext (by rw [ea, ea']) ?_
    ext Q
    by_cases hQ : Q = P
    · subst hQ; rw [eb, eb']
    · rw [ec Q hQ, ec' Q hQ]
  let ψ : ∀ Q : HeightOneSpectrum (𝓞 E), AE F E →+* Q.adicCompletion E := fun Q =>
    ((evalV E Q).toRingHom.comp (RingHom.snd _ _)).comp Φ.toRingHom
  have hψ : ∀ Q y, (Φ y).2 Q = ψ Q y := fun _ _ => rfl
  have he : e * e = e := by
    apply Φ.injective
    refine Prod.ext (by rw [map_mul, Prod.fst_mul, ea, mul_zero]) ?_
    ext Q
    rw [hψ, hψ, map_mul, ← hψ]
    by_cases hQ : Q = P
    · subst hQ; rw [eb, mul_one]
    · rw [ec Q hQ, mul_zero]
  have hint : ∀ c : E, P.valuation E c ≤ 1 →
      finPart F E (e * incA F E c + (1 - e)) ∈ intAE F E := by
    intro c hc
    rw [h2]
    intro Q
    rw [hψ, map_add, map_sub, map_mul, map_one, ← hψ, ← hψ]
    by_cases hQ : Q = P
    · subst hQ
      rw [eb, h1, one_mul, sub_self, add_zero]
      have : Valued.v ((algebraMap E (FiniteAdeleRing (𝓞 E) E) c) Q) = Q.valuation E c :=
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation' Q c
      exact this.le.trans hc
    · rw [ec Q hQ]; simp
  have hex : ∃ x, IsUnifIdele σ P x := by
    obtain ⟨ϖ, m1, m2⟩ := Ideal.exists_mem_pow_notMem_pow_succ P.asIdeal P.ne_bot P.isPrime.ne_top 1
    have hϖ : (ϖ : E) ≠ 0 := by
      intro h
      have : ϖ = 0 := by exact_mod_cast h
      exact m2 (this ▸ zero_mem _)
    have hm : (e * incA F E (ϖ : E) + (1 - e)) * (e * incA F E (ϖ : E)⁻¹ + (1 - e)) = 1 := by
      rw [idem_glue_mul he, ← map_mul, mul_inv_cancel₀ hϖ, map_one]; ring
    exact ⟨⟨_, _, hm, by rw [mul_comm, hm]⟩, e, f, ϖ, hef, by simpa using m1, m2, rfl⟩
  have hq : ∀ x y : (AE F E)ˣ, IsUnifIdele σ P x → IsUnifIdele σ P y →
      ∃ c : E, P.valuation E c ≤ 1 ∧
        ((x * y⁻¹ : (AE F E)ˣ) : AE F E) = e * incA F E c + (1 - e) := by
    rintro x y ⟨e1, f1, a, p1, a1, a2, hx⟩ ⟨e2, f2, b, p2, b1, b2, hy⟩
    rw [huniq _ _ p1] at hx
    rw [huniq _ _ p2] at hy
    have hb : (b : E) ≠ 0 := by
      intro h
      have : b = 0 := by exact_mod_cast h
      exact b2 (this ▸ zero_mem _)
    refine ⟨(a : E) / (b : E), ?_, ?_⟩
    · have va : P.valuation E (a : E) = WithZero.exp (-1 : ℤ) := by
        rw [← intValuation_of_mem_notMem_sq P a1 a2]
        exact HeightOneSpectrum.valuation_of_algebraMap P a
      have vb : P.valuation E (b : E) = WithZero.exp (-1 : ℤ) := by
        rw [← intValuation_of_mem_notMem_sq P b1 b2]
        exact HeightOneSpectrum.valuation_of_algebraMap P b
      rw [map_div₀, va, vb, div_self WithZero.exp_ne_zero]
    · rw [Units.val_mul, Units.mul_inv_eq_iff_eq_mul, hx, hy, idem_glue_mul he, ← map_mul,
        div_mul_cancel₀ _ hb]
  refine ⟨hex, ?_, ?_⟩
  · intro hun x hx
    have hc : IsUnramAt σ χ P ∧ ∃ x, IsUnifIdele σ P x := ⟨hun, hex⟩
    rw [chiAt, dif_pos hc]
    have hy := hc.2.choose_spec
    set y := hc.2.choose
    obtain ⟨e', f', p', hχ⟩ := hun
    rw [huniq _ _ p'] at hχ
    obtain ⟨c, c1, c2⟩ := hq y x hy hx
    obtain ⟨d, d1, d2⟩ := hq x y hx hy
    have := hχ (y * x⁻¹) (by rw [c2]; linear_combination (1 - incA F E c) * he)
      (by rw [c2]; exact hint c c1)
      (by rw [mul_inv_rev, inv_inv, d2]; exact hint d d1)
    rw [map_mul, map_inv, mul_inv_eq_one] at this
    rw [this]
  · rw [chiAt]
    split_ifs
    · exact (Circle.norm_coe _).le
    · simp

end GlobalTheory.HeckeUnif
