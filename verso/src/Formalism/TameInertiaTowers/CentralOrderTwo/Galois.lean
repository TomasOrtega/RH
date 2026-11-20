import Mathlib
import Formalism.TameInertiaTowers.StatementField

open NumberField Ideal Polynomial

noncomputable section

namespace Formalism.TwoAdicCyclotomicDecomposition

/- English proof (translation)
Take `⟨⟨P, _, _⟩⟩` from `(span {(p : ℤ)}).nonempty_primesOver (S := 𝓞 K)`. Establish `he : P.ramificationIdx ℤ = 1` using `IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd p K P hpN`. Establish `hp0 : (span {(p : ℤ)}) ≠ ⊥`. Simplify using `[hp.out.ne_zero]`. Establish `he' : (span {(p : ℤ)}).ramificationIdx' P = 1`.

Rewrite using `[Ideal.ramificationIdx'_eq_ramificationIdx _ _ hp0, he]`. Establish `hpP : ((p : ℤ) : 𝓞 K) ∈ P`. Use `(Ideal.over_def P (span {(p : ℤ)}))` as an intermediate fact. Establish `h1 : (p : ℤ) ∈ P.under ℤ` using `by rw [← this]; exact mem_span_singleton_self _`. Simplify using `using h1`.

Establish `hXP : X ∈ P`. Apply `(inferInstance : P.IsPrime).mem_of_pow_mem 2` to reduce the goal to its premises. Rewrite using `[hX, Int.cast_mul]`. Conclude with `P.mul_mem_right _ hpP`. Establish `hX2 : X ^ 2 ∈ P ^ 2` using `Ideal.pow_mem_pow hXP 2`.

Choose the witnesses or unpack the hypotheses as in `⟨s, t, hst⟩ : IsCoprime m (p : ℤ) := by`. Conclude with `((Nat.prime_iff_prime_int.mp hp.out).irreducible.coprime_iff_not_dvd.mpr hm).symm`. Establish `hp2 : ((p : ℤ) : 𝓞 K) ∈ P ^ 2`. Establish `: ((p : ℤ) : 𝓞 K) = (s : 𝓞 K) * X ^ 2 + (t : 𝓞 K) * (((p : ℤ) : 𝓞 K) * ((p : ℤ) : 𝓞 K))`. Rewrite using `[hX]`.

Establish `h' : ((s * m + t * p : ℤ) : 𝓞 K) = 1` using `by rw [hst, Int.cast_one]`. Move the coercions through the operations in `at h' ⊢`. Take the linear combination `(-(p : 𝓞 K)) * h'`. Rewrite using `[this]`. Use `Ideal.add_mem _ (Ideal.mul_mem_left _ _ hX2) (Ideal.mul_mem_left _ _ ?_)` and prove the remaining obligations.

Rewrite using `[pow_two]`. Conclude with `Ideal.mul_mem_mul hpP hpP`. Establish `hle : map (algebraMap ℤ (𝓞 K)) (span {(p : ℤ)}) ≤ P ^ 2`. Rewrite using `[Ideal.map_span, span_le]`. Introduce and unpack `_ ⟨y, hy, rfl⟩`.

Rewrite using `[Set.mem_singleton_iff.mp hy]`. Simplify using `using hp2`. Establish `hB : BddAbove {k | map (algebraMap ℤ (𝓞 K)) (span {(p : ℤ)}) ≤ P ^ k}`. Assume the negation of the conclusion as `hB`. Use `Nat.sSup_of_not_bddAbove hB` as an intermediate fact.

Unfold `Ideal.ramificationIdx' at he'`. Use linear arithmetic over natural numbers and integers. Use `le_csSup hB (show 2 ∈ {k | map (algebraMap ℤ (𝓞 K)) (span {(p : ℤ)}) ≤ P ^ k} from hle)` as an intermediate fact. Unfold `Ideal.ramificationIdx' at he'`. Use linear arithmetic over natural numbers and integers.
-/
theorem not_sq_in_cyclotomic_ring (K : Type*) [Field K] [NumberField K] (N : ℕ) [NeZero N]
    [IsCyclotomicExtension {N} ℚ K] (p : ℕ) [hp : Fact p.Prime] (hpN : ¬ p ∣ N)
    (m : ℤ) (hm : ¬ (p : ℤ) ∣ m) (X : 𝓞 K) (hX : X ^ 2 = ((p * m : ℤ) : 𝓞 K)) : False := by
  obtain ⟨⟨P, _, _⟩⟩ := (span {(p : ℤ)}).nonempty_primesOver (S := 𝓞 K)
  have he : P.ramificationIdx ℤ = 1 :=
    IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd p K P hpN
  have hp0 : (span {(p : ℤ)}) ≠ ⊥ := by
    simp [hp.out.ne_zero]
  have he' : (span {(p : ℤ)}).ramificationIdx' P = 1 := by
    rw [Ideal.ramificationIdx'_eq_ramificationIdx _ _ hp0, he]
  have hpP : ((p : ℤ) : 𝓞 K) ∈ P := by
    have := (Ideal.over_def P (span {(p : ℤ)}))
    have h1 : (p : ℤ) ∈ P.under ℤ := by rw [← this]; exact mem_span_singleton_self _
    simpa using h1
  have hXP : X ∈ P := by
    apply (inferInstance : P.IsPrime).mem_of_pow_mem 2
    rw [hX, Int.cast_mul]
    exact P.mul_mem_right _ hpP
  have hX2 : X ^ 2 ∈ P ^ 2 := Ideal.pow_mem_pow hXP 2
  obtain ⟨s, t, hst⟩ : IsCoprime m (p : ℤ) := by
    exact ((Nat.prime_iff_prime_int.mp hp.out).irreducible.coprime_iff_not_dvd.mpr hm).symm
  have hp2 : ((p : ℤ) : 𝓞 K) ∈ P ^ 2 := by
    have : ((p : ℤ) : 𝓞 K) = (s : 𝓞 K) * X ^ 2 + (t : 𝓞 K) * (((p : ℤ) : 𝓞 K) * ((p : ℤ) : 𝓞 K)) := by
      rw [hX]
      have h' : ((s * m + t * p : ℤ) : 𝓞 K) = 1 := by rw [hst, Int.cast_one]
      push_cast at h' ⊢
      linear_combination (-(p : 𝓞 K)) * h'
    rw [this]
    refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ hX2) (Ideal.mul_mem_left _ _ ?_)
    rw [pow_two]; exact Ideal.mul_mem_mul hpP hpP
  have hle : map (algebraMap ℤ (𝓞 K)) (span {(p : ℤ)}) ≤ P ^ 2 := by
    rw [Ideal.map_span, span_le]
    rintro _ ⟨y, hy, rfl⟩
    rw [Set.mem_singleton_iff.mp hy]
    simpa using hp2
  have hB : BddAbove {k | map (algebraMap ℤ (𝓞 K)) (span {(p : ℤ)}) ≤ P ^ k} := by
    by_contra hB
    have := Nat.sSup_of_not_bddAbove hB
    unfold Ideal.ramificationIdx' at he'
    omega
  have := le_csSup hB (show 2 ∈ {k | map (algebraMap ℤ (𝓞 K)) (span {(p : ℤ)}) ≤ P ^ k} from hle)
  unfold Ideal.ramificationIdx' at he'
  omega

/- English proof (translation)
Establish `hint : IsIntegral ℤ x`. Use `⟨X ^ 2 - C ((p * m : ℤ)), monic_X_pow_sub_C _ two_ne_zero, ?_⟩` and prove the remaining obligations. Rewrite using `[eval₂_sub, eval₂_X_pow, eval₂_C, hx, eq_intCast, sub_self]`. Use `not_sq_in_cyclotomic_ring K N p hpN m hm ⟨x, hint⟩ ?_` and prove the remaining obligations. Apply `RingOfIntegers.ext` to reduce the goal to its premises.

Conclude with `hx`.
-/
theorem not_sq_cyc (K : Type*) [Field K] [NumberField K] (N : ℕ) [NeZero N]
    [IsCyclotomicExtension {N} ℚ K] (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (m : ℤ) (hm : ¬ (p : ℤ) ∣ m) (x : K) (hx : x ^ 2 = ((p * m : ℤ) : K)) : False := by
  have hint : IsIntegral ℤ x := by
    refine ⟨X ^ 2 - C ((p * m : ℤ)), monic_X_pow_sub_C _ two_ne_zero, ?_⟩
    rw [eval₂_sub, eval₂_X_pow, eval₂_C, hx, eq_intCast, sub_self]
  refine not_sq_in_cyclotomic_ring K N p hpN m hm ⟨x, hint⟩ ?_
  apply RingOfIntegers.ext
  exact hx

section Signs

variable {L : Type} [Field L] [NumberField L]

/- English proof (translation)
Establish `: (σ x) ^ 2 = x ^ 2` using `by rw [← map_pow, hx, map_neg, map_natCast]`. Conclude with `sq_eq_sq_iff_eq_or_eq_neg.mp this`.
-/
theorem pm_of_sq {x : L} {c : ℕ} (hx : x ^ 2 = -(c : L)) (σ : Gal(L/ℚ)) :
    σ x = x ∨ σ x = -x := by
  have : (σ x) ^ 2 = x ^ 2 := by rw [← map_pow, hx, map_neg, map_natCast]
  exact sq_eq_sq_iff_eq_or_eq_neg.mp this

/- English proof (translation)
Introduce and unpack `rfl`. Establish `: (c : L) = 0`. Use `hx.symm` as an intermediate fact. Simplify using `using this`. Conclude with `hc (by exact_mod_cast this)`.
-/
theorem ne_zero_of_sq {x : L} {c : ℕ} (hc : c ≠ 0) (hx : x ^ 2 = -(c : L)) : x ≠ 0 := by
  rintro rfl
  have : (c : L) = 0 := by
    have := hx.symm
    simpa using this
  exact hc (by exact_mod_cast this)

/- English proof (translation)
Introduce `h`. Establish `: (2 : L) * x = 0` using `by linear_combination h`. Break down `mul_eq_zero.mp this with h2 | h2` into its components or cases. Conclude with `two_ne_zero h2`. Conclude with `hx0 h2`.
-/
theorem ne_neg_self {x : L} (hx0 : x ≠ 0) : x ≠ -x := by
  intro h
  have : (2 : L) * x = 0 := by linear_combination h
  rcases mul_eq_zero.mp this with h2 | h2
  · exact two_ne_zero h2
  · exact hx0 h2

/- English proof (translation)
Simplify using `[sgn, h]`.
-/
theorem sgn_of_eq {x : L} {ρ : Gal(L/ℚ)} (h : ρ x = x) : sgn ρ x = 1 := by
  simp [sgn, h]

/- English proof (translation)
Establish `: ρ x ≠ x` using `by rw [h]; exact fun e => ne_neg_self hx0 e.symm`. Simplify using `[sgn, this]`.
-/
theorem sgn_of_neg {x : L} (hx0 : x ≠ 0) {ρ : Gal(L/ℚ)} (h : ρ x = -x) : sgn ρ x = -1 := by
  have : ρ x ≠ x := by rw [h]; exact fun e => ne_neg_self hx0 e.symm
  simp [sgn, this]

/- English proof (translation)
Break down `h with h | h` into its components or cases. Rewrite using `[sgn_of_eq h, h]`. Simplify using the standard rewrite rules. Rewrite using `[sgn_of_neg hx0 h, h]`. Simplify using the standard rewrite rules.
-/
theorem sgn_spec {x : L} (hx0 : x ≠ 0) {σ : Gal(L/ℚ)} (h : σ x = x ∨ σ x = -x) :
    σ x = (((sgn σ x : ℤˣ) : ℤ) : L) * x := by
  rcases h with h | h
  · rw [sgn_of_eq h, h]; simp
  · rw [sgn_of_neg hx0 h, h]; simp

/- English proof (translation)
Apply the tactic sequence `rcases hpm τ with hτ | hτ <;> rcases hpm σ with hσ | hσ`. Rewrite using `[sgn_of_eq hσ, sgn_of_eq hτ, sgn_of_eq (by rw [AlgEquiv.mul_apply, hτ, hσ])]; rfl`. Rewrite using `[sgn_of_neg hx0 hσ, sgn_of_eq hτ, sgn_of_neg hx0 (by rw [AlgEquiv.mul_apply, hτ, hσ])]; rfl`. Rewrite using `[sgn_of_eq hσ, sgn_of_neg hx0 hτ, sgn_of_neg hx0 (by rw [AlgEquiv.mul_apply, hτ, map_neg, hσ])]; rfl`. Rewrite using `[sgn_of_neg hx0 hσ, sgn_of_neg hx0 hτ, sgn_of_eq (by rw [AlgEquiv.mul_apply, hτ, map_neg, hσ, neg_neg])]; rfl`.
-/
theorem sgn_mul {x : L} (hx0 : x ≠ 0) (hpm : ∀ σ : Gal(L/ℚ), σ x = x ∨ σ x = -x)
    (σ τ : Gal(L/ℚ)) : sgn (σ * τ) x = sgn σ x * sgn τ x := by
  rcases hpm τ with hτ | hτ <;> rcases hpm σ with hσ | hσ
  · rw [sgn_of_eq hσ, sgn_of_eq hτ, sgn_of_eq (by rw [AlgEquiv.mul_apply, hτ, hσ])]; rfl
  · rw [sgn_of_neg hx0 hσ, sgn_of_eq hτ, sgn_of_neg hx0 (by rw [AlgEquiv.mul_apply, hτ, hσ])]; rfl
  · rw [sgn_of_eq hσ, sgn_of_neg hx0 hτ,
      sgn_of_neg hx0 (by rw [AlgEquiv.mul_apply, hτ, map_neg, hσ])]; rfl
  · rw [sgn_of_neg hx0 hσ, sgn_of_neg hx0 hτ,
      sgn_of_eq (by rw [AlgEquiv.mul_apply, hτ, map_neg, hσ, neg_neg])]; rfl

def sgnHom (x : L) (hx0 : x ≠ 0) (hpm : ∀ σ : Gal(L/ℚ), σ x = x ∨ σ x = -x) :
    Gal(L/ℚ) →* ℤˣ where
  toFun σ := sgn σ x
  map_one' := sgn_of_eq (by simp)
  map_mul' := sgn_mul hx0 hpm

end Signs

/- English proof (translation)
Take `⟨u1, u2⟩` from `u`. Take `⟨v1, v2⟩` from `v`. Take `⟨w1, w2⟩` from `w`. Take `⟨t1, t2⟩` from `t`. Simplify using `only at hu hv hw`.

Substitute `hu hv` using the available equality. Use `revert hw`. Apply the tactic sequence `rcases Int.units_eq_one_or u2 with rfl | rfl <;> rcases Int.units_eq_one_or v1 with rfl | rfl <;>`. Apply the tactic sequence `rcases Int.units_eq_one_or w1 with rfl | rfl <;> rcases Int.units_eq_one_or w2 with rfl | rfl <;>`. Apply the tactic sequence `rcases Int.units_eq_one_or t1 with rfl | rfl <;> rcases Int.units_eq_one_or t2 with rfl | rfl <;>`.

Evaluate the decidable proposition.
-/
theorem klein_four_cover (u v w t : ℤˣ × ℤˣ) (hu : u.1 = -1) (hv : v.2 = -1) (hw : w.1 * w.2 = -1) :
    t = 1 ∨ t = u ∨ t = v ∨ t = w ∨ t = u * v ∨ t = u * w ∨ t = v * w := by
  obtain ⟨u1, u2⟩ := u
  obtain ⟨v1, v2⟩ := v
  obtain ⟨w1, w2⟩ := w
  obtain ⟨t1, t2⟩ := t
  simp only at hu hv hw
  subst hu hv
  revert hw
  rcases Int.units_eq_one_or u2 with rfl | rfl <;> rcases Int.units_eq_one_or v1 with rfl | rfl <;>
    rcases Int.units_eq_one_or w1 with rfl | rfl <;> rcases Int.units_eq_one_or w2 with rfl | rfl <;>
    rcases Int.units_eq_one_or t1 with rfl | rfl <;> rcases Int.units_eq_one_or t2 with rfl | rfl <;>
    decide

section Layer

variable {L : Type} [Field L] [NumberField L] {n q d : ℕ} {ζ a b : L}

/- English proof (translation)
Take `⟨hζ, ha, hb, htop⟩` from `h`. Establish `hquad : ∀ (x : L) (c : ℕ), x ^ 2 = -(c : L) → Splits (X ^ 2 + C (c : L))`. Introduce `x c hx`. Establish `: (X ^ 2 + C (c : L)) = (X - C x) * (X + C x)`. Establish `hc : C (c : L) = - C (x ^ 2)` using `by rw [hx, C_neg, neg_neg]`.

Rewrite using `[hc, C_pow]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `(Splits.X_sub_C x).mul (Splits.X_add_C x)`. Establish `hne : ((X ^ (2 ^ n) - C 1) * (X ^ 2 + C (q : ℚ)) * (X ^ 2 + C (d : ℚ)) : ℚ[X]) ≠ 0` using `(((monic_X_pow_sub_C 1 (pow_ne_zero _ two_ne_zero)).mul (monic_X_pow_add_C _ two_ne_zero)).mul (monic_X_pow_add_C _ two_ne_zero)).ne_zero`.

Prove the components needed by the constructor for the conclusion. Establish `e : ((X ^ (2 ^ n) - C 1) * (X ^ 2 + C (q : ℚ)) * (X ^ 2 + C (d : ℚ)) : ℚ[X]).map (algebraMap ℚ L) = (X ^ (2 ^ n) - C 1) * (X ^ 2 + C (q : L)) * (X ^ 2 + C (d : L))`. Simplify using the standard rewrite rules. Rewrite using `[e]`. Conclude with `((X_pow_sub_one_splits hζ).mul (hquad a q ha)).mul (hquad b d hb)`.

Rewrite using `[eq_top_iff, ← IntermediateField.top_toSubalgebra, ← htop, IntermediateField.adjoin_toSubalgebra]`. Apply `Algebra.adjoin_mono` to reduce the goal to its premises. Introduce `x hx`. Rewrite using `[mem_rootSet]`. Use `⟨hne, ?_⟩` and prove the remaining obligations.

Break down `hx with rfl | rfl | rfl` into its components or cases. Simplify using `[hζ.pow_eq_one]`. Simplify using `[ha]`. Simplify using `[hb]`.
-/
theorem layer_splitting (h : IsLayer n q d ζ a b) :
    IsSplittingField ℚ L ((X ^ (2 ^ n) - C 1) * (X ^ 2 + C (q : ℚ)) * (X ^ 2 + C (d : ℚ))) := by
  obtain ⟨hζ, ha, hb, htop⟩ := h
  have hquad : ∀ (x : L) (c : ℕ), x ^ 2 = -(c : L) → Splits (X ^ 2 + C (c : L)) := by
    intro x c hx
    have : (X ^ 2 + C (c : L)) = (X - C x) * (X + C x) := by
      have hc : C (c : L) = - C (x ^ 2) := by rw [hx, C_neg, neg_neg]
      rw [hc, C_pow]; ring
    rw [this]; exact (Splits.X_sub_C x).mul (Splits.X_add_C x)
  have hne : ((X ^ (2 ^ n) - C 1) * (X ^ 2 + C (q : ℚ)) * (X ^ 2 + C (d : ℚ)) : ℚ[X]) ≠ 0 :=
    (((monic_X_pow_sub_C 1 (pow_ne_zero _ two_ne_zero)).mul
      (monic_X_pow_add_C _ two_ne_zero)).mul (monic_X_pow_add_C _ two_ne_zero)).ne_zero
  constructor
  · have e : ((X ^ (2 ^ n) - C 1) * (X ^ 2 + C (q : ℚ)) * (X ^ 2 + C (d : ℚ)) : ℚ[X]).map
        (algebraMap ℚ L) = (X ^ (2 ^ n) - C 1) * (X ^ 2 + C (q : L)) * (X ^ 2 + C (d : L)) := by
      simp
    rw [e]
    exact ((X_pow_sub_one_splits hζ).mul (hquad a q ha)).mul (hquad b d hb)
  · rw [eq_top_iff, ← IntermediateField.top_toSubalgebra, ← htop,
      IntermediateField.adjoin_toSubalgebra]
    apply Algebra.adjoin_mono
    intro x hx
    rw [mem_rootSet]
    refine ⟨hne, ?_⟩
    rcases hx with rfl | rfl | rfl
    · simp [hζ.pow_eq_one]
    · simp [ha]
    · simp [hb]

/- English proof (translation)
Use `layer_splitting h` as an intermediate fact. Use `Normal.of_isSplittingField (F := ℚ) (E := L) ((X ^ (2 ^ n) - C 1) * (X ^ 2 + C (q : ℚ)) * (X ^ 2 + C (d : ℚ)))` as an intermediate fact. Conclude with `isGalois_iff.mpr ⟨inferInstance, inferInstance⟩`.
-/
theorem layer_isGalois (h : IsLayer n q d ζ a b) : IsGalois ℚ L := by
  have := layer_splitting h
  have := Normal.of_isSplittingField (F := ℚ) (E := L)
    ((X ^ (2 ^ n) - C 1) * (X ^ 2 + C (q : ℚ)) * (X ^ 2 + C (d : ℚ)))
  exact isGalois_iff.mpr ⟨inferInstance, inferInstance⟩

/- English proof (translation)
Establish `htop : Algebra.adjoin ℚ ({ζ, a, b} : Set L) = ⊤`. Rewrite using `[← IntermediateField.adjoin_toSubalgebra, h.2.2.2, IntermediateField.top_toSubalgebra]`. Apply `AlgEquiv.coe_toAlgHom_injective` to reduce the goal to its premises. Apply `AlgHom.ext_of_adjoin_eq_top htop` to reduce the goal to its premises. Introduce `x hx`.

Break down `hx with rfl | rfl | rfl` into its components or cases. Simplify using `using h1`. Simplify using `using h2`. Simplify using `using h3`.
-/
theorem layer_ext (h : IsLayer n q d ζ a b) {σ τ : Gal(L/ℚ)} (h1 : σ ζ = τ ζ) (h2 : σ a = τ a)
    (h3 : σ b = τ b) : σ = τ := by
  have htop : Algebra.adjoin ℚ ({ζ, a, b} : Set L) = ⊤ := by
    rw [← IntermediateField.adjoin_toSubalgebra, h.2.2.2, IntermediateField.top_toSubalgebra]
  apply AlgEquiv.coe_toAlgHom_injective
  apply AlgHom.ext_of_adjoin_eq_top htop
  intro x hx
  rcases hx with rfl | rfl | rfl
  · simpa using h1
  · simpa using h2
  · simpa using h3

/- English proof (translation)
Introduce `σ τ hστ`. Simplify using `only [galMap, Prod.mk.injEq] at hστ`. Take `⟨h1, h2, h3⟩` from `hστ`. Apply `layer_ext h` to reduce the goal to its premises. Rewrite using `[← h.1.autToPow_spec ℚ σ, ← h.1.autToPow_spec ℚ τ, h1]`.

Rewrite using `[sgn_spec (ne_zero_of_sq hq0 h.2.1) (pm_of_sq h.2.1 σ), sgn_spec (ne_zero_of_sq hq0 h.2.1) (pm_of_sq h.2.1 τ), h2]`. Rewrite using `[sgn_spec (ne_zero_of_sq hd0 h.2.2.1) (pm_of_sq h.2.2.1 σ), sgn_spec (ne_zero_of_sq hd0 h.2.2.1) (pm_of_sq h.2.2.1 τ), h3]`.
-/
theorem galMap_injective (h : IsLayer n q d ζ a b) (hq0 : q ≠ 0) (hd0 : d ≠ 0) :
    Function.Injective (galMap h.1 a b) := by
  intro σ τ hστ
  simp only [galMap, Prod.mk.injEq] at hστ
  obtain ⟨h1, h2, h3⟩ := hστ
  apply layer_ext h
  · rw [← h.1.autToPow_spec ℚ σ, ← h.1.autToPow_spec ℚ τ, h1]
  · rw [sgn_spec (ne_zero_of_sq hq0 h.2.1) (pm_of_sq h.2.1 σ),
      sgn_spec (ne_zero_of_sq hq0 h.2.1) (pm_of_sq h.2.1 τ), h2]
  · rw [sgn_spec (ne_zero_of_sq hd0 h.2.2.1) (pm_of_sq h.2.2.1 σ),
      sgn_spec (ne_zero_of_sq hd0 h.2.2.1) (pm_of_sq h.2.2.1 τ), h3]

/- English proof (translation)
The claim follows from `Prod.ext (map_mul _ σ τ) (Prod.ext (sgn_mul (ne_zero_of_sq hq0 h.2.1) (pm_of_sq h.2.1) σ τ) (sgn_mul (ne_zero_of_sq hd0 h.2.2.1) (pm_of_sq h.2.2.1) σ τ))`.
-/
theorem galMap_mul (h : IsLayer n q d ζ a b) (hq0 : q ≠ 0) (hd0 : d ≠ 0) (σ τ : Gal(L/ℚ)) :
    galMap h.1 a b (σ * τ) = galMap h.1 a b σ * galMap h.1 a b τ :=
  Prod.ext (map_mul _ σ τ) (Prod.ext
    (sgn_mul (ne_zero_of_sq hq0 h.2.1) (pm_of_sq h.2.1) σ τ)
    (sgn_mul (ne_zero_of_sq hd0 h.2.2.1) (pm_of_sq h.2.2.1) σ τ))

/- English proof (translation)
Rewrite using `[Nat.card_prod, Nat.card_prod, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime_pow Nat.prime_two (by omega), Nat.card_eq_fintype_card, Fintype.card_units_int]`. Take `⟨k, rfl⟩ : ∃ k, n = k + 1` from `⟨n - 1, by omega⟩`. Simplify using `only [Nat.add_sub_cancel]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem card_galL (hn : 1 ≤ n) : Nat.card (GalL n) = 2 ^ (n + 1) := by
  rw [Nat.card_prod, Nat.card_prod, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
    Nat.totient_prime_pow Nat.prime_two (by omega), Nat.card_eq_fintype_card,
    Fintype.card_units_int]
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  ring

/- English proof (translation)
Take `⟨hζ, ha, hb, htop⟩` from `h`. Take `⟨hq, hd, hqd', hq2, hd2⟩` from `hqd`. Set `K` to `IntermediateField.adjoin ℚ ({ζ} : Set L)`. Establish `: IsCyclotomicExtension {2 ^ n} ℚ K` using `hζ.intermediateField_adjoin_isCyclotomicExtension ℚ`. Establish `hKdeg : Module.finrank ℚ K = 2 ^ (n - 1)`.

Rewrite using `[IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral ζ), ← cyclotomic_eq_minpoly_rat hζ (by positivity), natDegree_cyclotomic, Nat.totient_prime_pow Nat.prime_two (by omega)]`. Simplify using the standard rewrite rules. Establish `hns : ∀ (p : ℕ) (m : ℤ), p.Prime → p ≠ 2 → ¬ (p : ℤ) ∣ m → ∀ y : L, y ∈ K → y ^ 2 = ((p * m : ℤ) : L) → False`. Introduce `p m hp hp2 hm y hy hy2`. Use `Fact.mk hp` as an intermediate fact.

Establish `hpN : ¬ p ∣ 2 ^ n` using `fun hdvd => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hdvd))`. Conclude with `not_sq_cyc K (2 ^ n) p hpN m hm ⟨y, hy⟩ (by ext; simpa using hy2)`. Establish `hndvd1 : ∀ p : ℕ, p.Prime → ¬ (p : ℤ) ∣ -1`. Introduce `p hp hdvd`. Use `Int.eq_one_of_dvd_one (by positivity) ((dvd_neg).mp hdvd)` as an intermediate fact.

Establish `: p = 1` using `by exact_mod_cast this`. Conclude with `hp.one_lt.ne' this`. Establish `hqd_dvd : ¬ (q : ℤ) ∣ (d : ℤ)`. Introduce `hdvd`. Establish `: q ∣ d` using `by exact_mod_cast hdvd`.

Conclude with `hqd' ((Nat.prime_dvd_prime_iff_eq hq hd).mp this)`. Establish `haK : a ∉ K` using `fun haK => hns q (-1) hq hq2 (hndvd1 q hq) a haK (by push_cast; rw [ha]; ring)`. Establish `hbK : b ∉ K` using `fun hbK => hns d (-1) hd hd2 (hndvd1 d hd) b hbK (by push_cast; rw [hb]; ring)`. Establish `habK : a * b ∉ K` using `fun habK => hns q d hq hq2 hqd_dvd (a * b) habK (by rw [mul_pow, ha, hb]; push_cast; ring)`. Establish `hfix : IntermediateField.fixedField K.fixingSubgroup = K` using `IsGalois.fixedField_fixingSubgroup K`.

Establish `hmove : ∀ y : L, y ∉ K → ∃ σ ∈ K.fixingSubgroup, σ y ≠ y`. Introduce `y hy`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Apply `hy` to reduce the goal to its premises.

Rewrite using `[← hfix]`. Conclude with `(IntermediateField.mem_fixedField_iff _ _).mpr hc`. Take `⟨σ1, hσ1, h1⟩` from `hmove a haK`. Take `⟨σ2, hσ2, h2⟩` from `hmove b hbK`. Take `⟨σ3, hσ3, h3⟩` from `hmove (a * b) habK`.

Establish `ha0` using `ne_zero_of_sq hq.ne_zero ha`. Establish `hb0` using `ne_zero_of_sq hd.ne_zero hb`. Set `s : Gal(L/ℚ) →* ℤˣ × ℤˣ` to `(sgnHom a ha0 (pm_of_sq ha)).prod (sgnHom b hb0 (pm_of_sq hb))`. Establish `hs : ∀ σ, s σ = (sgn σ a, sgn σ b)` using `fun σ => rfl`. Establish `hu : (s σ1).1 = -1`.

Rewrite using `[hs]`. Conclude with `sgn_of_neg ha0 ((pm_of_sq ha σ1).resolve_left h1)`. Establish `hv : (s σ2).2 = -1`. Rewrite using `[hs]`. Conclude with `sgn_of_neg hb0 ((pm_of_sq hb σ2).resolve_left h2)`.

Establish `hw : (s σ3).1 * (s σ3).2 = -1`. Rewrite using `[hs]`. Rewrite `h3` using `[map_mul]`. Apply the tactic sequence `rcases pm_of_sq ha σ3 with e1 | e1 <;> rcases pm_of_sq hb σ3 with e2 | e2`. Conclude with `absurd (by rw [e1, e2]) h3`.

Rewrite using `[sgn_of_eq e1, sgn_of_neg hb0 e2]`. Both sides reduce to the same expression. Rewrite using `[sgn_of_neg ha0 e1, sgn_of_eq e2]`. Both sides reduce to the same expression. Conclude with `absurd (by rw [e1, e2, neg_mul_neg]) h3`.

Set `φ : K.fixingSubgroup → ℤˣ × ℤˣ` to `fun σ => s σ`. Establish `hφ : Function.Surjective φ`. Introduce `t`. Break down `klein_four_cover (s σ1) (s σ2) (s σ3) t hu hv hw with e | e | e | e | e | e | e` into its components or cases. Conclude with `⟨1, by simp [φ, e]⟩`.

Conclude with `⟨⟨σ1, hσ1⟩, e.symm⟩`. Conclude with `⟨⟨σ2, hσ2⟩, e.symm⟩`. Conclude with `⟨⟨σ3, hσ3⟩, e.symm⟩`. Conclude with `⟨⟨σ1, hσ1⟩ * ⟨σ2, hσ2⟩, by simp [φ, e]⟩`. Conclude with `⟨⟨σ1, hσ1⟩ * ⟨σ3, hσ3⟩, by simp [φ, e]⟩`.

Conclude with `⟨⟨σ2, hσ2⟩ * ⟨σ3, hσ3⟩, by simp [φ, e]⟩`. Establish `hH : 4 ≤ Nat.card K.fixingSubgroup`. Use `Nat.card_le_card_of_surjective φ hφ` as an intermediate fact. Rewrite `this` using `[Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_units_int]`. Then use the resulting hypothesis. Establish `hLK : Module.finrank K L = Nat.card K.fixingSubgroup` using `(IsGalois.card_fixingSubgroup_eq_finrank K).symm`.

Rewrite using `[← Module.finrank_mul_finrank ℚ K L, hKdeg, hLK]`. Take `⟨k, rfl⟩ : ∃ k, n = k + 1` from `⟨n - 1, by omega⟩`. Simplify using `only [Nat.add_sub_cancel]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem layer_finrank_ge (h : IsLayer n q d ζ a b) (hn : 1 ≤ n) (hqd : HypOdd q d)
    [IsGalois ℚ L] : 2 ^ (n + 1) ≤ Module.finrank ℚ L := by
  obtain ⟨hζ, ha, hb, htop⟩ := h
  obtain ⟨hq, hd, hqd', hq2, hd2⟩ := hqd
  let K := IntermediateField.adjoin ℚ ({ζ} : Set L)
  have : IsCyclotomicExtension {2 ^ n} ℚ K := hζ.intermediateField_adjoin_isCyclotomicExtension ℚ
  have hKdeg : Module.finrank ℚ K = 2 ^ (n - 1) := by
    rw [IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral ζ),
      ← cyclotomic_eq_minpoly_rat hζ (by positivity), natDegree_cyclotomic,
      Nat.totient_prime_pow Nat.prime_two (by omega)]
    simp
  have hns : ∀ (p : ℕ) (m : ℤ), p.Prime → p ≠ 2 → ¬ (p : ℤ) ∣ m → ∀ y : L, y ∈ K →
      y ^ 2 = ((p * m : ℤ) : L) → False := by
    intro p m hp hp2 hm y hy hy2
    have := Fact.mk hp
    have hpN : ¬ p ∣ 2 ^ n := fun hdvd =>
      hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hdvd))
    exact not_sq_cyc K (2 ^ n) p hpN m hm ⟨y, hy⟩ (by ext; simpa using hy2)
  have hndvd1 : ∀ p : ℕ, p.Prime → ¬ (p : ℤ) ∣ -1 := by
    intro p hp hdvd
    have := Int.eq_one_of_dvd_one (by positivity) ((dvd_neg).mp hdvd)
    have : p = 1 := by exact_mod_cast this
    exact hp.one_lt.ne' this
  have hqd_dvd : ¬ (q : ℤ) ∣ (d : ℤ) := by
    intro hdvd
    have : q ∣ d := by exact_mod_cast hdvd
    exact hqd' ((Nat.prime_dvd_prime_iff_eq hq hd).mp this)
  have haK : a ∉ K := fun haK => hns q (-1) hq hq2 (hndvd1 q hq) a haK (by push_cast; rw [ha]; ring)
  have hbK : b ∉ K := fun hbK => hns d (-1) hd hd2 (hndvd1 d hd) b hbK (by push_cast; rw [hb]; ring)
  have habK : a * b ∉ K := fun habK => hns q d hq hq2 hqd_dvd (a * b) habK
    (by rw [mul_pow, ha, hb]; push_cast; ring)
  have hfix : IntermediateField.fixedField K.fixingSubgroup = K := IsGalois.fixedField_fixingSubgroup K
  have hmove : ∀ y : L, y ∉ K → ∃ σ ∈ K.fixingSubgroup, σ y ≠ y := by
    intro y hy
    by_contra hc
    push Not at hc
    apply hy
    rw [← hfix]
    exact (IntermediateField.mem_fixedField_iff _ _).mpr hc
  obtain ⟨σ1, hσ1, h1⟩ := hmove a haK
  obtain ⟨σ2, hσ2, h2⟩ := hmove b hbK
  obtain ⟨σ3, hσ3, h3⟩ := hmove (a * b) habK
  have ha0 := ne_zero_of_sq hq.ne_zero ha
  have hb0 := ne_zero_of_sq hd.ne_zero hb
  let s : Gal(L/ℚ) →* ℤˣ × ℤˣ := (sgnHom a ha0 (pm_of_sq ha)).prod (sgnHom b hb0 (pm_of_sq hb))
  have hs : ∀ σ, s σ = (sgn σ a, sgn σ b) := fun σ => rfl
  have hu : (s σ1).1 = -1 := by
    rw [hs]
    exact sgn_of_neg ha0 ((pm_of_sq ha σ1).resolve_left h1)
  have hv : (s σ2).2 = -1 := by
    rw [hs]
    exact sgn_of_neg hb0 ((pm_of_sq hb σ2).resolve_left h2)
  have hw : (s σ3).1 * (s σ3).2 = -1 := by
    rw [hs]
    rw [map_mul] at h3
    rcases pm_of_sq ha σ3 with e1 | e1 <;> rcases pm_of_sq hb σ3 with e2 | e2
    · exact absurd (by rw [e1, e2]) h3
    · rw [sgn_of_eq e1, sgn_of_neg hb0 e2]; rfl
    · rw [sgn_of_neg ha0 e1, sgn_of_eq e2]; rfl
    · exact absurd (by rw [e1, e2, neg_mul_neg]) h3
  let φ : K.fixingSubgroup → ℤˣ × ℤˣ := fun σ => s σ
  have hφ : Function.Surjective φ := by
    intro t
    rcases klein_four_cover (s σ1) (s σ2) (s σ3) t hu hv hw with e | e | e | e | e | e | e
    · exact ⟨1, by simp [φ, e]⟩
    · exact ⟨⟨σ1, hσ1⟩, e.symm⟩
    · exact ⟨⟨σ2, hσ2⟩, e.symm⟩
    · exact ⟨⟨σ3, hσ3⟩, e.symm⟩
    · exact ⟨⟨σ1, hσ1⟩ * ⟨σ2, hσ2⟩, by simp [φ, e]⟩
    · exact ⟨⟨σ1, hσ1⟩ * ⟨σ3, hσ3⟩, by simp [φ, e]⟩
    · exact ⟨⟨σ2, hσ2⟩ * ⟨σ3, hσ3⟩, by simp [φ, e]⟩
  have hH : 4 ≤ Nat.card K.fixingSubgroup := by
    have := Nat.card_le_card_of_surjective φ hφ
    rwa [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_units_int] at this
  have hLK : Module.finrank K L = Nat.card K.fixingSubgroup :=
    (IsGalois.card_fixingSubgroup_eq_finrank K).symm
  rw [← Module.finrank_mul_finrank ℚ K L, hKdeg, hLK]
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  calc 2 ^ (k + 1 + 1) = 2 ^ k * 4 := by ring
    _ ≤ 2 ^ k * Nat.card K.fixingSubgroup := Nat.mul_le_mul_left _ hH

end Layer

/- English proof (translation)
Introduce `n q d hn hqd L _ _ ζ a b h`. Establish `hG` using `layer_isGalois h`. Establish `hq0 : q ≠ 0` using `hqd.1.ne_zero`. Establish `hd0 : d ≠ 0` using `hqd.2.1.ne_zero`. Establish `hinj` using `galMap_injective h hq0 hd0`.

Establish `hcard1 : Nat.card Gal(L/ℚ) = Module.finrank ℚ L` using `IsGalois.card_aut_eq_finrank ℚ L`. Establish `hle : Nat.card Gal(L/ℚ) ≤ Nat.card (GalL n)` using `Nat.card_le_card_of_injective _ hinj`. Establish `hge` using `layer_finrank_ge h hn hqd`. Rewrite `hle` using `[card_galL hn]`. Use `⟨hG, by omega, galMap_mul h hq0 hd0, hinj.bijective_of_nat_card_le ?_⟩` and prove the remaining obligations.

Rewrite using `[card_galL hn]`. Use linear arithmetic over natural numbers and integers.
-/
theorem layerGalois : LayerGalois := by
  intro n q d hn hqd L _ _ ζ a b h
  have hG := layer_isGalois h
  have hq0 : q ≠ 0 := hqd.1.ne_zero
  have hd0 : d ≠ 0 := hqd.2.1.ne_zero
  have hinj := galMap_injective h hq0 hd0
  have hcard1 : Nat.card Gal(L/ℚ) = Module.finrank ℚ L := IsGalois.card_aut_eq_finrank ℚ L
  have hle : Nat.card Gal(L/ℚ) ≤ Nat.card (GalL n) := Nat.card_le_card_of_injective _ hinj
  have hge := layer_finrank_ge h hn hqd
  rw [card_galL hn] at hle
  refine ⟨hG, by omega, galMap_mul h hq0 hd0, hinj.bijective_of_nat_card_le ?_⟩
  rw [card_galL hn]
  omega

/- English proof (translation)
Introduce `n q d`. Use `set f : ℚ[X] := cyclotomic (2 ^ n) ℚ * (X ^ 2 + C (q : ℚ)) * (X ^ 2 + C (d : ℚ)) with hf`. Set `F` to `SplittingField f`. Establish `: CharZero F` using `charZero_of_injective_algebraMap (algebraMap ℚ F).injective`. Establish `: NumberField F` using `{ to_charZero := inferInstance, to_finiteDimensional := inferInstance }`.

Establish `hmap' : ∀ φ : ℚ →+* F, f.map φ = cyclotomic (2 ^ n) F * (X ^ 2 + C (q : F)) * (X ^ 2 + C (d : F))`. Introduce `φ`. Simplify using `[f, map_cyclotomic, C_eq_natCast]`. Establish `hmap` using `hmap' (algebraMap ℚ F)`. Establish `hsp : Splits (f.map (algebraMap ℚ F))` using `SplittingField.splits f`.

Rewrite `hsp` using `[hmap]`. Establish `hne : cyclotomic (2 ^ n) F * (X ^ 2 + C (q : F)) * (X ^ 2 + C (d : F)) ≠ 0` using `(((cyclotomic.monic _ F).mul (monic_X_pow_add_C _ two_ne_zero)).mul (monic_X_pow_add_C _ two_ne_zero)).ne_zero`. Establish `hc : Splits (cyclotomic (2 ^ n) F)` using `hsp.of_dvd hne (dvd_mul_of_dvd_left (dvd_mul_right _ _) _)`. Establish `hqs : Splits (X ^ 2 + C (q : F))` using `hsp.of_dvd hne (dvd_mul_of_dvd_left (dvd_mul_left _ _) _)`. Establish `hds : Splits (X ^ 2 + C (d : F))` using `hsp.of_dvd hne (dvd_mul_left _ _)`.

Take `⟨ζ, hζ⟩` from `hc.exists_eval_eq_zero (by`. Rewrite using `[degree_cyclotomic]`. Conclude with `(Nat.totient_pos.mpr (by positivity)).ne')` after adjusting the coercions. Establish `hζp : IsPrimitiveRoot ζ (2 ^ n)` using `(isRoot_cyclotomic_iff_charZero (by positivity)).mp hζ`. Take `⟨a, ha⟩` from `hqs.exists_eval_eq_zero (by rw [degree_X_pow_add_C (by norm_num)]; norm_num)`.

Take `⟨b, hb⟩` from `hds.exists_eval_eq_zero (by rw [degree_X_pow_add_C (by norm_num)]; norm_num)`. Establish `ha2 : a ^ 2 = -(q : F)`. Simplify using `only [eval_add, eval_pow, eval_X, eval_C] at ha`. Take the linear combination `ha`. Establish `hb2 : b ^ 2 = -(d : F)`.

Simplify using `only [eval_add, eval_pow, eval_X, eval_C] at hb`. Take the linear combination `hb`. Use `⟨F, inferInstance, inferInstance, ζ, a, b, ?_⟩` and prove the remaining obligations. Rewrite using `[show (DivisionRing.toRatAlgebra : Algebra ℚ F) = SplittingField.instAlgebra_1 f from Subsingleton.elim _ _]`. Use `⟨hζp, ha2, hb2, ?_⟩` and prove the remaining obligations.

Rewrite using `[← IntermediateField.toSubalgebra_inj, IntermediateField.adjoin_toSubalgebra, IntermediateField.top_toSubalgebra, eq_top_iff]`. Use `(SplittingField.adjoin_rootSet f).symm.le.trans ?_` and prove the remaining obligations. Rewrite using `[Algebra.adjoin_le_iff]`. Introduce `x hx`. Rewrite `hx` using `[mem_rootSet]`.

Establish `hx'` using `hx.2`. Rewrite `hx'` using `[← eval_map_algebraMap, hmap']`. Simplify using `only [eval_mul, eval_add, eval_pow, eval_X, eval_C] at hx'`. Break down `mul_eq_zero.mp hx' with hx' | hx'` into its components or cases. Break down `mul_eq_zero.mp hx' with hx' | hx'` into its components or cases.

Establish `hxp : IsPrimitiveRoot x (2 ^ n)` using `(isRoot_cyclotomic_iff_charZero (by positivity)).mp hx'`. Take `⟨i, -, hi⟩` from `hζp.eq_pow_of_pow_eq_one hxp.pow_eq_one`. Rewrite using `[← hi]`. Conclude with `pow_mem (Algebra.subset_adjoin (by simp)) i`. Establish `: x ^ 2 = a ^ 2` using `by rw [ha2]; linear_combination hx'`.

Break down `sq_eq_sq_iff_eq_or_eq_neg.mp this with rfl | rfl` into its components or cases. Conclude with `Algebra.subset_adjoin (by simp)`. Conclude with `neg_mem (Algebra.subset_adjoin (by simp))`. Establish `: x ^ 2 = b ^ 2` using `by rw [hb2]; linear_combination hx'`. Break down `sq_eq_sq_iff_eq_or_eq_neg.mp this with rfl | rfl` into its components or cases.

Conclude with `Algebra.subset_adjoin (by simp)`. Conclude with `neg_mem (Algebra.subset_adjoin (by simp))`.
-/
theorem layerExists : LayerExists := by
  intro n q d
  set f : ℚ[X] := cyclotomic (2 ^ n) ℚ * (X ^ 2 + C (q : ℚ)) * (X ^ 2 + C (d : ℚ)) with hf
  let F := SplittingField f
  have : CharZero F := charZero_of_injective_algebraMap (algebraMap ℚ F).injective
  have : NumberField F := { to_charZero := inferInstance, to_finiteDimensional := inferInstance }
  have hmap' : ∀ φ : ℚ →+* F, f.map φ =
      cyclotomic (2 ^ n) F * (X ^ 2 + C (q : F)) * (X ^ 2 + C (d : F)) := by
    intro φ
    simp [f, map_cyclotomic, C_eq_natCast]
  have hmap := hmap' (algebraMap ℚ F)
  have hsp : Splits (f.map (algebraMap ℚ F)) := SplittingField.splits f
  rw [hmap] at hsp
  have hne : cyclotomic (2 ^ n) F * (X ^ 2 + C (q : F)) * (X ^ 2 + C (d : F)) ≠ 0 :=
    (((cyclotomic.monic _ F).mul (monic_X_pow_add_C _ two_ne_zero)).mul
      (monic_X_pow_add_C _ two_ne_zero)).ne_zero
  have hc : Splits (cyclotomic (2 ^ n) F) :=
    hsp.of_dvd hne (dvd_mul_of_dvd_left (dvd_mul_right _ _) _)
  have hqs : Splits (X ^ 2 + C (q : F)) :=
    hsp.of_dvd hne (dvd_mul_of_dvd_left (dvd_mul_left _ _) _)
  have hds : Splits (X ^ 2 + C (d : F)) := hsp.of_dvd hne (dvd_mul_left _ _)
  obtain ⟨ζ, hζ⟩ := hc.exists_eval_eq_zero (by
    rw [degree_cyclotomic]
    exact_mod_cast (Nat.totient_pos.mpr (by positivity)).ne')
  have hζp : IsPrimitiveRoot ζ (2 ^ n) := (isRoot_cyclotomic_iff_charZero (by positivity)).mp hζ
  obtain ⟨a, ha⟩ := hqs.exists_eval_eq_zero (by rw [degree_X_pow_add_C (by norm_num)]; norm_num)
  obtain ⟨b, hb⟩ := hds.exists_eval_eq_zero (by rw [degree_X_pow_add_C (by norm_num)]; norm_num)
  have ha2 : a ^ 2 = -(q : F) := by
    simp only [eval_add, eval_pow, eval_X, eval_C] at ha
    linear_combination ha
  have hb2 : b ^ 2 = -(d : F) := by
    simp only [eval_add, eval_pow, eval_X, eval_C] at hb
    linear_combination hb
  refine ⟨F, inferInstance, inferInstance, ζ, a, b, ?_⟩
  rw [show (DivisionRing.toRatAlgebra : Algebra ℚ F) = SplittingField.instAlgebra_1 f from
    Subsingleton.elim _ _]
  refine ⟨hζp, ha2, hb2, ?_⟩
  rw [← IntermediateField.toSubalgebra_inj, IntermediateField.adjoin_toSubalgebra,
    IntermediateField.top_toSubalgebra, eq_top_iff]
  refine (SplittingField.adjoin_rootSet f).symm.le.trans ?_
  rw [Algebra.adjoin_le_iff]
  intro x hx
  rw [mem_rootSet] at hx
  have hx' := hx.2
  rw [← eval_map_algebraMap, hmap'] at hx'
  simp only [eval_mul, eval_add, eval_pow, eval_X, eval_C] at hx'
  rcases mul_eq_zero.mp hx' with hx' | hx'
  · rcases mul_eq_zero.mp hx' with hx' | hx'
    · have hxp : IsPrimitiveRoot x (2 ^ n) := (isRoot_cyclotomic_iff_charZero (by positivity)).mp hx'
      obtain ⟨i, -, hi⟩ := hζp.eq_pow_of_pow_eq_one hxp.pow_eq_one
      rw [← hi]
      exact pow_mem (Algebra.subset_adjoin (by simp)) i
    · have : x ^ 2 = a ^ 2 := by rw [ha2]; linear_combination hx'
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp this with rfl | rfl
      · exact Algebra.subset_adjoin (by simp)
      · exact neg_mem (Algebra.subset_adjoin (by simp))
  · have : x ^ 2 = b ^ 2 := by rw [hb2]; linear_combination hx'
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp this with rfl | rfl
    · exact Algebra.subset_adjoin (by simp)
    · exact neg_mem (Algebra.subset_adjoin (by simp))

end Formalism.TwoAdicCyclotomicDecomposition
