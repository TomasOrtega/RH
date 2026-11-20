import Mathlib
import ReciprocityTheory.CommutativeAlgebra.MaximalIdealSquares.RingKrullDimQuotientSpanSingletonAddOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSaturated

open IsLocalRing

namespace GlobalTheory

namespace RegularNormal

def StableDvd (A : Type*) [CommRing A] : Prop :=
  ∀ (a b : A) (I : Ideal A), b ≠ 0 → I ≠ ⊥ → (∀ r ∈ I, ∃ s ∈ I, a * r = b * s) → b ∣ a

/- English proof (translation)
Rewrite using `[isIntegrallyClosed_iff (FractionRing A)]`. Introduce `y hy`. Take `⟨a, b, hb, rfl⟩` from `IsFractionRing.div_surjective (A := A) y`. Use `set K := FractionRing A`. Use `set y : K := algebraMap A K a / algebraMap A K b with hydef`.

Establish `hb0 : b ≠ 0` using `nonZeroDivisors.ne_zero hb`. Establish `hbK : algebraMap A K b ≠ 0`. Simplify using `using hb0`. Establish `hinj : Function.Injective (algebraMap A K)` using `IsFractionRing.injective A K`. Take `⟨d, hd, hdN⟩` from `FractionalIdeal.isFractional_of_fg (S := nonZeroDivisors A) hy.fg_adjoin_singleton`.

Set `I : Ideal A` to `{ carrier := {r | ∀ z ∈ Algebra.adjoin A {y}, ∃ s : A, algebraMap A K s = r • z} zero_mem' := fun z _ => ⟨0, by simp⟩ add_mem' := by`. Introduce `r r' hr hr' z hz`. Take `⟨s, hs⟩` from `hr z hz`. Take `⟨s', hs'⟩` from `hr' z hz`. Conclude with `⟨s + s', by rw [map_add, hs, hs', add_smul]⟩`.

Use the proof step `smul_mem' := by`. Introduce `c r hr z hz`. Take `⟨s, hs⟩` from `hr z hz`. Conclude with `⟨c * s, by rw [map_mul, hs, smul_eq_mul, mul_smul, Algebra.smul_def c]⟩ }`. Establish `hyN : y ∈ Algebra.adjoin A {y}` using `Algebra.self_mem_adjoin_singleton A y`.

Establish `hdI : d ∈ I` using `fun z hz => hdN z hz`. Establish `hI : I ≠ ⊥` using `fun h0 => nonZeroDivisors.ne_zero hd (by simpa [h0] using hdI)`. Take `⟨c, hc⟩` from `h a b I hb0 hI (by`. Introduce `r hr`. Take `⟨s, hs⟩` from `hr y hyN`.

Use `⟨s, fun z hz => ?_, hinj ?_⟩` and prove the remaining obligations. Take `⟨t, ht⟩` from `hr (y * z) (mul_mem hyN hz)`. Use `⟨t, ?_⟩` and prove the remaining obligations. Rewrite using `[ht, Algebra.smul_def s, hs, smul_mul_assoc]`. Rewrite using `[map_mul, map_mul, hs, Algebra.smul_def, hydef, mul_left_comm, mul_div_cancel₀ _ hbK, mul_comm])`.

Use `⟨c, ?_⟩` and prove the remaining obligations. Rewrite using `[hydef, hc, map_mul, mul_div_cancel_left₀ _ hbK]`.
-/
theorem StableDvd.isIntegrallyClosed {A : Type*} [CommRing A] [IsDomain A] (h : StableDvd A) :
    IsIntegrallyClosed A := by
  rw [isIntegrallyClosed_iff (FractionRing A)]
  intro y hy
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := A) y
  set K := FractionRing A
  set y : K := algebraMap A K a / algebraMap A K b with hydef
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbK : algebraMap A K b ≠ 0 := by
    simpa using hb0
  have hinj : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  obtain ⟨d, hd, hdN⟩ := FractionalIdeal.isFractional_of_fg (S := nonZeroDivisors A)
    hy.fg_adjoin_singleton
  let I : Ideal A :=
    { carrier := {r | ∀ z ∈ Algebra.adjoin A {y}, ∃ s : A, algebraMap A K s = r • z}
      zero_mem' := fun z _ => ⟨0, by simp⟩
      add_mem' := by
        intro r r' hr hr' z hz
        obtain ⟨s, hs⟩ := hr z hz
        obtain ⟨s', hs'⟩ := hr' z hz
        exact ⟨s + s', by rw [map_add, hs, hs', add_smul]⟩
      smul_mem' := by
        intro c r hr z hz
        obtain ⟨s, hs⟩ := hr z hz
        exact ⟨c * s, by rw [map_mul, hs, smul_eq_mul, mul_smul, Algebra.smul_def c]⟩ }
  have hyN : y ∈ Algebra.adjoin A {y} := Algebra.self_mem_adjoin_singleton A y
  have hdI : d ∈ I := fun z hz => hdN z hz
  have hI : I ≠ ⊥ := fun h0 => nonZeroDivisors.ne_zero hd (by simpa [h0] using hdI)
  obtain ⟨c, hc⟩ := h a b I hb0 hI (by
    intro r hr
    obtain ⟨s, hs⟩ := hr y hyN
    refine ⟨s, fun z hz => ?_, hinj ?_⟩
    · obtain ⟨t, ht⟩ := hr (y * z) (mul_mem hyN hz)
      refine ⟨t, ?_⟩
      rw [ht, Algebra.smul_def s, hs, smul_mul_assoc]
    · rw [map_mul, map_mul, hs, Algebra.smul_def, hydef, mul_left_comm, mul_div_cancel₀ _ hbK, mul_comm])
  refine ⟨c, ?_⟩
  rw [hydef, hc, map_mul, mul_div_cancel_left₀ _ hbK]

section Step

variable {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A] {x : A}

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.SaturatedNotDvd.main`. Consider the case `exact _root_.GlobalTheory.SaturatedNotDvd.main`. Consider the case `(apply _root_.GlobalTheory.SaturatedNotDvd.main <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.SaturatedNotDvd.main <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.SaturatedNotDvd.main <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.SaturatedNotDvd.main ..)`.
-/
theorem dvd_of_not_dvd (hx : Prime x) (h : StableDvd (A ⧸ Ideal.span {x})) {a b : A}
    (hb : ¬ x ∣ b) {I : Ideal A} (hI : I ≠ ⊥)
    (hst : ∀ r ∈ I, ∃ s ∈ I, a * r = b * s) : b ∣ a := by
  first
  | exact @_root_.GlobalTheory.SaturatedNotDvd.main
  | exact _root_.GlobalTheory.SaturatedNotDvd.main
  | (apply _root_.GlobalTheory.SaturatedNotDvd.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.SaturatedNotDvd.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SaturatedNotDvd.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SaturatedNotDvd.main ..)

omit [IsLocalRing A] in

/- English proof (translation)
Assume the negation of the conclusion as `ha`. Establish `key : ∀ k : ℕ, ∀ r ∈ I, x ^ k ∣ r`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro r _`.

Simplify using the standard rewrite rules. Consider the case `succ k ih`. Introduce `r hr`. Take `⟨s, hs, e⟩` from `hst r hr`. Take `⟨v, rfl⟩` from `ih s hs`.

Conclude with `hx.pow_dvd_of_dvd_mul_left (k + 1) ha ⟨b * v, by linear_combination e⟩`. Take `⟨r, hr, hr0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hI`. Take `⟨n, c, hc, e⟩` from `WfDvdMonoid.max_power_factor' hr0 hx.not_unit`. Take `⟨v, hv⟩` from `key (n + 1) r hr`. Use `hc ⟨v, mul_left_cancel₀ (pow_ne_zero n hx.ne_zero) ?_⟩` and prove the remaining obligations.

Take the linear combination `hv - e`.
-/
theorem prime_dvd_of_stable (hx : Prime x) {a b : A} {I : Ideal A} (hI : I ≠ ⊥)
    (hst : ∀ r ∈ I, ∃ s ∈ I, a * r = x * b * s) : x ∣ a := by
  by_contra ha
  have key : ∀ k : ℕ, ∀ r ∈ I, x ^ k ∣ r := by
    intro k
    induction k with
    | zero => intro r _; simp
    | succ k ih =>
      intro r hr
      obtain ⟨s, hs, e⟩ := hst r hr
      obtain ⟨v, rfl⟩ := ih s hs
      exact hx.pow_dvd_of_dvd_mul_left (k + 1) ha ⟨b * v, by linear_combination e⟩
  obtain ⟨r, hr, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  obtain ⟨n, c, hc, e⟩ := WfDvdMonoid.max_power_factor' hr0 hx.not_unit
  obtain ⟨v, hv⟩ := key (n + 1) r hr
  refine hc ⟨v, mul_left_cancel₀ (pow_ne_zero n hx.ne_zero) ?_⟩
  linear_combination hv - e

/- English proof (translation)
Introduce `a b I hb hI hst`. Take `⟨n, c, hc, rfl⟩` from `WfDvdMonoid.max_power_factor' hb hx.not_unit`. Use `clear hb`. Proceed by induction on `n generalizing a with`. Consider the case `zero`.

Rewrite `hst`, the goal using `[pow_zero, one_mul]`. Conclude with `dvd_of_not_dvd hx h hc hI hst`. Consider the case `succ n ih`. Take `⟨a, rfl⟩` from `prime_dvd_of_stable hx (a := a) (b := x ^ n * c) hI (fun r hr => by`. Take `⟨s, hs, e⟩` from `hst r hr`.

Conclude with `⟨s, hs, by linear_combination e⟩)`. Take `⟨v, hv⟩` from `ih a (fun r hr => by`. Take `⟨s, hs, e⟩` from `hst r hr`. Conclude with `⟨s, hs, mul_left_cancel₀ hx.ne_zero (by linear_combination e)⟩)`. Conclude with `⟨v, by rw [hv]; ring⟩`.
-/
theorem StableDvd.of_quotient (hx : Prime x) (h : StableDvd (A ⧸ Ideal.span {x})) :
    StableDvd A := by
  intro a b I hb hI hst
  obtain ⟨n, c, hc, rfl⟩ := WfDvdMonoid.max_power_factor' hb hx.not_unit
  clear hb
  induction n generalizing a with
  | zero =>
    rw [pow_zero, one_mul] at hst ⊢
    exact dvd_of_not_dvd hx h hc hI hst
  | succ n ih =>
    obtain ⟨a, rfl⟩ := prime_dvd_of_stable hx (a := a) (b := x ^ n * c) hI (fun r hr => by
      obtain ⟨s, hs, e⟩ := hst r hr
      exact ⟨s, hs, by linear_combination e⟩)
    obtain ⟨v, hv⟩ := ih a (fun r hr => by
      obtain ⟨s, hs, e⟩ := hst r hr
      exact ⟨s, hs, mul_left_cancel₀ hx.ne_zero (by linear_combination e)⟩)
    exact ⟨v, by rw [hv]; ring⟩

end Step

open ReciprocityTheory.CA.AB.RegA in
/- English proof (translation)
Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n IH`. Introduce `R _ _ hn`. Establish `: IsDomain R` using `IsRegularLocalRing.isDomain R`. Distinguish the cases in `hsq : maximalIdeal R ≤ maximalIdeal R ^ 2`.

Establish `h0` using `IsRegularLocalRing.maximalIdeal_eq_bot_of_le_sq R hsq`. Introduce `a b I hb _ _`. Use `IsUnit.dvd ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hu`. Establish `: b ∈ maximalIdeal R` using `hu`.

Rewrite `this` using `[h0]`. Conclude with `hb this`. Take `⟨x, hx, hx2⟩` from `SetLike.not_le_iff_exists.mp hsq`. Establish `hx0 : x ≠ 0`. Introduce and unpack `rfl`.

Conclude with `hx2 (zero_mem _)`. Establish `hquot` using `IsRegularLocalRing.quotient_span_singleton hx hx2`. Establish `hxp : Prime x`. Rewrite using `[← Ideal.span_singleton_prime hx0, ← Ideal.Quotient.isDomain_iff_prime]`. Conclude with `IsRegularLocalRing.isDomain _`.

Use `StableDvd.of_quotient hxp (IH _ ?_ _ rfl)` and prove the remaining obligations. Establish `h1` using `IsRegularLocalRing.spanFinrank_maximalIdeal_quotient_succ_le R hx hx2`. Establish `h2 : Submodule.spanFinrank (maximalIdeal R) = Module.finrank (ResidueField R) (CotangentSpace R)`. Rewrite using `[IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]`. Use linear arithmetic over natural numbers and integers.
-/
theorem stableDvd_of_spanFinrank_eq (n : ℕ) :
    ∀ (R : Type) [CommRing R] [IsRegularLocalRing R],
      Submodule.spanFinrank (maximalIdeal R) = n → StableDvd R := by
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro R _ _ hn
  have : IsDomain R := IsRegularLocalRing.isDomain R
  by_cases hsq : maximalIdeal R ≤ maximalIdeal R ^ 2
  · have h0 := IsRegularLocalRing.maximalIdeal_eq_bot_of_le_sq R hsq
    intro a b I hb _ _
    refine IsUnit.dvd ?_
    by_contra hu
    have : b ∈ maximalIdeal R := hu
    rw [h0] at this
    exact hb this
  obtain ⟨x, hx, hx2⟩ := SetLike.not_le_iff_exists.mp hsq
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hx2 (zero_mem _)
  have hquot := IsRegularLocalRing.quotient_span_singleton hx hx2
  have hxp : Prime x := by
    rw [← Ideal.span_singleton_prime hx0, ← Ideal.Quotient.isDomain_iff_prime]
    exact IsRegularLocalRing.isDomain _
  refine StableDvd.of_quotient hxp (IH _ ?_ _ rfl)
  have h1 := IsRegularLocalRing.spanFinrank_maximalIdeal_quotient_succ_le R hx hx2
  have h2 : Submodule.spanFinrank (maximalIdeal R)
      = Module.finrank (ResidueField R) (CotangentSpace R) := by
    rw [IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]
  omega

end RegularNormal

/- English proof (translation)
Introduce `T _ _`. Establish `hd : IsDomain T` using `ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.isDomain T`. Conclude with `⟨hd, (RegularNormal.stableDvd_of_spanFinrank_eq _ T rfl).isIntegrallyClosed⟩`.
-/
theorem isDomain_and_isIntegrallyClosed_of_isRegularLocalRing :
    ∀ (T : Type) [CommRing T] [IsRegularLocalRing T], IsDomain T ∧ IsIntegrallyClosed T := by
  intro T _ _
  have hd : IsDomain T := ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.isDomain T
  exact ⟨hd, (RegularNormal.stableDvd_of_spanFinrank_eq _ T rfl).isIntegrallyClosed⟩

end GlobalTheory
