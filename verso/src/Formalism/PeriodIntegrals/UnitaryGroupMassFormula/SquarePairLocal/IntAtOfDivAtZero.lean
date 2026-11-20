import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarePairLocal.SqPairLocalOfSteps

noncomputable section
open NumberField Matrix

namespace PI.SqPairLocal

open PI.SqPair

attribute [local instance] StModel.cr StModel.dom StModel.dvr StModel.hens StModel.fin

variable {E : Type} [Field E] [NumberField E] [StarRing E]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_cj (x : 𝓞 E) : ((cj E x : 𝓞 E) : E) = star (x : E) := rfl

namespace StModel

variable {Q : Ideal (𝓞 E)} (M : StModel E Q)

/- English proof (translation)
Introduce `h`. Apply `M.ϖ_irr.ne_zero` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[h]`.
-/
theorem ϖ_ne : M.ϖ ≠ 0 := by
  intro h
  apply M.ϖ_irr.ne_zero
  apply Subtype.ext
  simp [h]

/- English proof (translation)
Introduce `hxQ`. Take `⟨u, hu⟩` from `hx`. Take `⟨y, z, hyz⟩` from `M.dense (↑u⁻¹) 1`. Establish `hdz : ∃ z' : M.R, M.j (1 - x * y) = M.j M.ϖ ^ 1 * z'`. Use `⟨M.j x * z, ?_⟩` and prove the remaining obligations.

Establish `h1 : M.j y = ↑u⁻¹ - M.j M.ϖ ^ 1 * z` using `by rw [← hyz]; ring`. Rewrite using `[map_sub, map_one, map_mul, h1, ← hu, mul_sub, Units.mul_inv]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨s, hs, w, hw⟩` from `M.detect (1 - x * y) 1 hdz`. Apply `hs` to reduce the goal to its premises.

Establish `hsw : s = s * x * y + M.ϖ ^ 1 * w` using `by linear_combination hw`. Rewrite using `[hsw]`. Use `Q.add_mem (Q.mul_mem_right _ (Q.mul_mem_left _ hxQ)) (Q.mul_mem_right _ ?_)` and prove the remaining obligations. Rewrite using `[pow_one]`. Conclude with `M.ϖ_Q`.
-/
theorem notMem_of_unit {x : 𝓞 E} (hx : IsUnit (M.j x)) : x ∉ Q := by
  intro hxQ
  obtain ⟨u, hu⟩ := hx
  obtain ⟨y, z, hyz⟩ := M.dense (↑u⁻¹) 1
  have hdz : ∃ z' : M.R, M.j (1 - x * y) = M.j M.ϖ ^ 1 * z' := by
    refine ⟨M.j x * z, ?_⟩
    have h1 : M.j y = ↑u⁻¹ - M.j M.ϖ ^ 1 * z := by rw [← hyz]; ring
    rw [map_sub, map_one, map_mul, h1, ← hu, mul_sub, Units.mul_inv]
    ring
  obtain ⟨s, hs, w, hw⟩ := M.detect (1 - x * y) 1 hdz
  apply hs
  have hsw : s = s * x * y + M.ϖ ^ 1 * w := by linear_combination hw
  rw [hsw]
  refine Q.add_mem (Q.mul_mem_right _ (Q.mul_mem_left _ hxQ)) (Q.mul_mem_right _ ?_)
  rw [pow_one]; exact M.ϖ_Q

/- English proof (translation)
Establish `hϖ0 : M.ϖ ≠ 0` using `M.ϖ_ne`. Establish `hQ0 : Q ≠ ⊥` using `fun h => hϖ0 ((Submodule.eq_bot_iff Q).mp h _ M.ϖ_Q)`. Take `⟨⟨D, hD⟩, hint⟩` from `IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 E)) Finset.univ x`. Establish `hint' : ∀ i, ∃ a : 𝓞 E, algebraMap (𝓞 E) E a = D • x i` using `fun i => hint i (Finset.mem_univ i)`. Use `choose a ha using hint'`.

Establish `hD0 : D ≠ 0` using `nonZeroDivisors.ne_zero hD`. Take `⟨k, t, ht, r, hr⟩ : ∃ k : ℕ, ∃ t : 𝓞 E, t ∉ Q ∧ ∃ r : 𝓞 E, t * M.ϖ ^ k = D * r` from `by haveI : IsDiscreteValuationRing (Localization.AtPrime Q) := by first`. Consider the case `exact IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 E) hQ0 _`. Consider the case `infer_instance`. Establish `hinj : Function.Injective (algebraMap (𝓞 E) (Localization.AtPrime Q))` using `IsLocalization.injective _ (Ideal.primeCompl_le_nonZeroDivisors Q)`.

Establish `hne : ∀ c : 𝓞 E, c ≠ 0 → algebraMap (𝓞 E) (Localization.AtPrime Q) c ≠ 0` using `fun c hc h0 => hc (hinj (by rw [h0, map_zero]))`. Establish `hϖm : algebraMap (𝓞 E) (Localization.AtPrime Q) M.ϖ ∈ IsLocalRing.maximalIdeal (Localization.AtPrime Q)` using `by first`. Consider the case `exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime Q) Q M.ϖ).mpr M.ϖ_Q`. Consider the case `(rw [← Localization.AtPrime.map_eq_maximalIdeal]; exact Ideal.mem_map_of_mem _ M.ϖ_Q)`. Take `⟨π, hπ⟩` from `IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime Q)`.

Take `⟨n, u, hu⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (hne D hD0) hπ`. Take `⟨m, u', hu'⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (hne M.ϖ hϖ0) hπ`. Establish `hm : m ≠ 0`. Introduce and unpack `rfl`. Apply `(IsLocalRing.mem_maximalIdeal _).mp hϖm` to reduce the goal to its premises.

Rewrite using `[hu', pow_zero, mul_one]`. Conclude with `u'.isUnit`. Establish `hdvd : algebraMap (𝓞 E) (Localization.AtPrime Q) D ∣ algebraMap (𝓞 E) (Localization.AtPrime Q) M.ϖ ^ n`. Rewrite using `[hu, hu', mul_pow, ← pow_mul]`. Conclude with `mul_dvd_mul u.isUnit.dvd (pow_dvd_pow π (Nat.le_mul_of_pos_left n (Nat.pos_of_ne_zero hm)))`.

Take `⟨y, hy⟩` from `hdvd`. Take `⟨⟨r, t, htQ⟩, hrt⟩` from `IsLocalization.surj Q.primeCompl y`. Establish `hrt' : y * algebraMap (𝓞 E) (Localization.AtPrime Q) t = algebraMap (𝓞 E) (Localization.AtPrime Q) r` using `hrt`. Use `⟨n, t, htQ, r, hinj ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, map_mul, map_pow, mul_comm (algebraMap (𝓞 E) (Localization.AtPrime Q) t), hy, mul_assoc, hrt']`.

Use `⟨k, t, ht, fun i => r * a i, fun i => ?_⟩` and prove the remaining obligations. Establish `hr'` using `congrArg (algebraMap (𝓞 E) E) hr`. Rewrite `hr'` using `[map_mul, map_pow, map_mul]`. Rewrite using `[map_mul, ha i, Algebra.smul_def, hr']`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_clear [hQ : Q.IsPrime] {ι : Type} [Fintype ι] (x : ι → E) :
    ∃ k : ℕ, ∃ t : 𝓞 E, t ∉ Q ∧ ∃ w : ι → 𝓞 E,
      ∀ i, algebraMap (𝓞 E) E t * algebraMap (𝓞 E) E M.ϖ ^ k * x i = algebraMap (𝓞 E) E (w i) := by
  classical
  have hϖ0 : M.ϖ ≠ 0 := M.ϖ_ne
  have hQ0 : Q ≠ ⊥ := fun h => hϖ0 ((Submodule.eq_bot_iff Q).mp h _ M.ϖ_Q)
  obtain ⟨⟨D, hD⟩, hint⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 E)) Finset.univ x
  have hint' : ∀ i, ∃ a : 𝓞 E, algebraMap (𝓞 E) E a = D • x i := fun i => hint i (Finset.mem_univ i)
  choose a ha using hint'
  have hD0 : D ≠ 0 := nonZeroDivisors.ne_zero hD
  obtain ⟨k, t, ht, r, hr⟩ : ∃ k : ℕ, ∃ t : 𝓞 E, t ∉ Q ∧ ∃ r : 𝓞 E, t * M.ϖ ^ k = D * r := by
    haveI : IsDiscreteValuationRing (Localization.AtPrime Q) := by
      first
        | exact IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 E) hQ0 _
        | infer_instance
    have hinj : Function.Injective (algebraMap (𝓞 E) (Localization.AtPrime Q)) :=
      IsLocalization.injective _ (Ideal.primeCompl_le_nonZeroDivisors Q)
    have hne : ∀ c : 𝓞 E, c ≠ 0 → algebraMap (𝓞 E) (Localization.AtPrime Q) c ≠ 0 := fun c hc h0 =>
      hc (hinj (by rw [h0, map_zero]))
    have hϖm : algebraMap (𝓞 E) (Localization.AtPrime Q) M.ϖ ∈
        IsLocalRing.maximalIdeal (Localization.AtPrime Q) := by
      first
        | exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime Q) Q M.ϖ).mpr M.ϖ_Q
        | (rw [← Localization.AtPrime.map_eq_maximalIdeal]; exact Ideal.mem_map_of_mem _ M.ϖ_Q)
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime Q)
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (hne D hD0) hπ
    obtain ⟨m, u', hu'⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (hne M.ϖ hϖ0) hπ
    have hm : m ≠ 0 := by
      rintro rfl
      apply (IsLocalRing.mem_maximalIdeal _).mp hϖm
      rw [hu', pow_zero, mul_one]; exact u'.isUnit
    have hdvd : algebraMap (𝓞 E) (Localization.AtPrime Q) D ∣
        algebraMap (𝓞 E) (Localization.AtPrime Q) M.ϖ ^ n := by
      rw [hu, hu', mul_pow, ← pow_mul]
      exact mul_dvd_mul u.isUnit.dvd (pow_dvd_pow π (Nat.le_mul_of_pos_left n (Nat.pos_of_ne_zero hm)))
    obtain ⟨y, hy⟩ := hdvd
    obtain ⟨⟨r, t, htQ⟩, hrt⟩ := IsLocalization.surj Q.primeCompl y
    have hrt' : y * algebraMap (𝓞 E) (Localization.AtPrime Q) t = algebraMap (𝓞 E) (Localization.AtPrime Q) r := hrt
    refine ⟨n, t, htQ, r, hinj ?_⟩
    rw [map_mul, map_mul, map_pow, mul_comm (algebraMap (𝓞 E) (Localization.AtPrime Q) t), hy, mul_assoc, hrt']
  refine ⟨k, t, ht, fun i => r * a i, fun i => ?_⟩
  have hr' := congrArg (algebraMap (𝓞 E) E) hr
  rw [map_mul, map_pow, map_mul] at hr'
  rw [map_mul, ha i, Algebra.smul_def, hr']
  ring

/- English proof (translation)
Apply `M.detect` to reduce the goal to its premises. Use `⟨Y a b, ?_⟩` and prove the remaining obligations. Use `congrFun (congrFun h a) b` as an intermediate fact. Simplify `this` using `[RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply]`.
-/
theorem detect_mat {N : ℕ} (A : Matrix (Fin N) (Fin N) (𝓞 E)) (m : ℕ)
    (Y : Matrix (Fin N) (Fin N) M.R) (h : M.j.mapMatrix A = (M.j M.ϖ ^ m) • Y) (a b : Fin N) :
    ∃ s : 𝓞 E, s ∉ Q ∧ ∃ w : 𝓞 E, s * A a b = M.ϖ ^ m * w := by
  apply M.detect
  refine ⟨Y a b, ?_⟩
  have := congrFun (congrFun h a) b
  simpa [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply] using this

end StModel

/- English proof (translation)
Take `⟨s, hs, w, hw⟩` from `h a b`. Use `⟨s, hs, w, ?_⟩` and prove the remaining obligations. Establish `h2` using `congrArg (algebraMap (𝓞 E) E) hw`. Rewrite `h2` using `[map_mul, map_mul]`. Conclude with `h2`.
-/
theorem divAt_of_map {Q : Ideal (𝓞 E)} {N : ℕ} (A : Matrix (Fin N) (Fin N) (𝓞 E)) (c : 𝓞 E)
    (h : ∀ a b, ∃ s : 𝓞 E, s ∉ Q ∧ ∃ w : 𝓞 E, s * A a b = c * w) (a b : Fin N) :
    DivAt Q c ((algebraMap (𝓞 E) E).mapMatrix A a b) := by
  obtain ⟨s, hs, w, hw⟩ := h a b
  refine ⟨s, hs, w, ?_⟩
  have h2 := congrArg (algebraMap (𝓞 E) E) hw
  rw [map_mul, map_mul] at h2
  exact h2

/- English proof (translation)
Take `⟨s, hs, w, hw⟩` from `h a b`. Use `⟨s * d, fun hm => (hQ.mem_or_mem hm).elim hs hd, w, ?_⟩` and prove the remaining obligations. Establish `h2` using `congrArg (algebraMap (𝓞 E) E) hw`. Simplify using `only [map_mul, map_pow, hGX, pow_add] at h2`. Establish `hϖE : algebraMap (𝓞 E) E ϖ ≠ 0`.

Introduce `h0`. Apply `hϖ` to reduce the goal to its premises. Use `first`. Consider the case `exact (map_eq_zero_iff _ (NoZeroSMulDivisors.algebraMap_injective (𝓞 E) E)).mp h0`. Consider the case `exact (map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 E) E)).mp h0`.

Consider the case `exact_mod_cast h0`. Establish `hp : algebraMap (𝓞 E) E ϖ ^ (2 * k) ≠ 0` using `pow_ne_zero _ hϖE`. Establish `h3 : algebraMap (𝓞 E) E ϖ ^ (2 * k) * (algebraMap (𝓞 E) E s * algebraMap (𝓞 E) E d * X a b) = algebraMap (𝓞 E) E ϖ ^ (2 * k) * (algebraMap (𝓞 E) E ϖ ^ m * algebraMap (𝓞 E) E w)`. Take the linear combination `h2`. Establish `h4` using `mul_left_cancel₀ hp h3`.

Use `show algebraMap (𝓞 E) E (s * d) * X a b = algebraMap (𝓞 E) E (ϖ ^ m) * algebraMap (𝓞 E) E w`. Rewrite using `[map_mul, map_pow]`. Conclude with `h4`.
-/
theorem divAt_conj {Q : Ideal (𝓞 E)} [hQ : Q.IsPrime] {N : ℕ} (ϖ d : 𝓞 E) (hϖ : ϖ ≠ 0)
    (hd : d ∉ Q) (k m : ℕ) (G : Matrix (Fin N) (Fin N) (𝓞 E)) (X : Matrix (Fin N) (Fin N) E)
    (hGX : ∀ a b, algebraMap (𝓞 E) E (G a b) =
      algebraMap (𝓞 E) E d * algebraMap (𝓞 E) E ϖ ^ (2 * k) * X a b)
    (h : ∀ a b, ∃ s : 𝓞 E, s ∉ Q ∧ ∃ w : 𝓞 E, s * G a b = ϖ ^ (2 * k + m) * w) (a b : Fin N) :
    DivAt Q (ϖ ^ m) (X a b) := by
  obtain ⟨s, hs, w, hw⟩ := h a b
  refine ⟨s * d, fun hm => (hQ.mem_or_mem hm).elim hs hd, w, ?_⟩
  have h2 := congrArg (algebraMap (𝓞 E) E) hw
  simp only [map_mul, map_pow, hGX, pow_add] at h2
  have hϖE : algebraMap (𝓞 E) E ϖ ≠ 0 := by
    intro h0
    apply hϖ
    first
      | exact (map_eq_zero_iff _ (NoZeroSMulDivisors.algebraMap_injective (𝓞 E) E)).mp h0
      | exact (map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 E) E)).mp h0
      | exact_mod_cast h0
  have hp : algebraMap (𝓞 E) E ϖ ^ (2 * k) ≠ 0 := pow_ne_zero _ hϖE
  have h3 : algebraMap (𝓞 E) E ϖ ^ (2 * k) *
      (algebraMap (𝓞 E) E s * algebraMap (𝓞 E) E d * X a b) =
      algebraMap (𝓞 E) E ϖ ^ (2 * k) * (algebraMap (𝓞 E) E ϖ ^ m * algebraMap (𝓞 E) E w) := by
    linear_combination h2
  have h4 := mul_left_cancel₀ hp h3
  show algebraMap (𝓞 E) E (s * d) * X a b = algebraMap (𝓞 E) E (ϖ ^ m) * algebraMap (𝓞 E) E w
  rw [map_mul, map_pow]
  exact h4

/- English proof (translation)
Take `⟨s, hs, w, hw⟩` from `h`. Conclude with `⟨s, hs, w, by simpa using hw⟩`.
-/
theorem intAt_of_divAt_zero {Q : Ideal (𝓞 E)} (ϖ : 𝓞 E) {x : E} (h : DivAt Q (ϖ ^ 0) x) :
    IntAt Q x := by
  obtain ⟨s, hs, w, hw⟩ := h
  exact ⟨s, hs, w, by simpa using hw⟩

end PI.SqPairLocal
