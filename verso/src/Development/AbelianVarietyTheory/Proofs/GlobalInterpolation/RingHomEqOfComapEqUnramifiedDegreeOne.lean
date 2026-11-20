import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MaxVSpanSingleton
open NumberField IsDedekindDomain

namespace GlobalTheory

/- English proof (translation)
Use `set f := RingOfIntegers.mapRingHom φ with hf`. Use `set g := RingOfIntegers.mapRingHom ψ with hg`. Establish `hpQ : ((p : ℕ) : 𝓞 E) ∈ Q.asIdeal` using `hN ▸ Ideal.absNorm_mem Q.asIdeal`. Establish `hQp` using `Q.isPrime`. Establish `h1 : ∀ x : 𝓞 E, ∃ a : ℤ, x - (a : 𝓞 E) ∈ Q.asIdeal`.

Introduce `x`. Use `haveI : Fact p.Prime := ⟨hp⟩`. Establish `hc : Nat.card (𝓞 E ⧸ Q.asIdeal) = p`. Rewrite using `[← hN, Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Establish `h` using `mem_zmultiples_of_prime_card (g := (1 : 𝓞 E ⧸ Q.asIdeal)) (g' := Ideal.Quotient.mk Q.asIdeal x) hc one_ne_zero`.

Take `⟨a, ha⟩` from `AddSubgroup.mem_zmultiples_iff.1 h`. Use `⟨a, Ideal.Quotient.eq.1 ?_⟩` and prove the remaining obligations. Rewrite using `[← ha, map_intCast, zsmul_one]`. Establish `h2 : Ideal.span {((p : ℕ) : 𝓞 E)} ⊔ Q.asIdeal ^ 2 = Q.asIdeal`. Establish `h` using `Ideal.eq_prime_pow_of_succ_lt_of_le (P := Q.asIdeal) (i := 1) (I := Ideal.span {((p : ℕ) : 𝓞 E)} ⊔ Q.asIdeal ^ 2) Q.ne_bot ?_ ?_`.

Simplify using `using h`. Use `lt_of_le_of_ne le_sup_right fun h => hsq ?_` and prove the remaining obligations. Establish `h' : ((p : ℕ) : 𝓞 E) ∈ Ideal.span {((p : ℕ) : 𝓞 E)} ⊔ Q.asIdeal ^ 2` using `Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)`. Rewrite `h'` using `[← h]`. Conclude with `h'`.

Rewrite using `[pow_one]`. Conclude with `sup_le ((Ideal.span_singleton_le_iff_mem _).2 hpQ) (Ideal.pow_le_self two_ne_zero)`. Establish `h3 : ∀ n : ℕ, Q.asIdeal ≤ Ideal.span {((p : ℕ) : 𝓞 E)} ⊔ Q.asIdeal ^ n`. Introduce `n`. Proceed by induction on `n with`.

Consider the case `zero => simp`. Consider the case `succ n ih`. Break down `n with _ | n` into its components or cases. Simplify using the standard rewrite rules. Use `h2.ge.trans (sup_le le_sup_left ?_)` and prove the remaining obligations.

Rewrite using `[sq]`. Use `(Ideal.mul_mono_right ih).trans ?_` and prove the remaining obligations. Rewrite using `[Ideal.mul_sup, ← pow_succ']`. Conclude with `sup_le_sup_right Ideal.mul_le_right _`. Establish `hmap : ∀ (k : 𝓞 E →+* 𝓞 K), (∀ r : 𝓞 E, r ∈ Q.asIdeal ↔ k r ∈ w.asIdeal) → ∀ (n : ℕ) (z : 𝓞 E), z ∈ Q.asIdeal ^ n → k z ∈ w.asIdeal ^ n`.

Introduce `k hk n z hz`. Establish `h` using `Ideal.mem_map_of_mem k hz`. Rewrite `h` using `[Ideal.map_pow]`. Use `Ideal.pow_right_mono ?_ n h` and prove the remaining obligations. Conclude with `Ideal.map_le_iff_le_comap.2 fun r hr => (hk r).1 hr`.

Establish `hpw : ((p : ℕ) : 𝓞 K) ∈ w.asIdeal`. Simplify using `using (hφ _).1 hpQ`. Establish `h4 : ∀ (n : ℕ) (x : 𝓞 E), f x - g x ∈ w.asIdeal ^ n`. Introduce `n`. Proceed by induction on `n with`.

Consider the case `zero => simp`. Consider the case `succ n ih`. Introduce `x`. Take `⟨a, ha⟩` from `h1 x`. Take `⟨y, hy, z, hz, hyz⟩` from `Submodule.mem_sup.1 (h3 (n + 1) ha)`.

Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton'.1 hy`. Establish `hx : x = c * p + z + a` using `by rw [hyz]; ring`. Establish `he : f x - g x = (f c - g c) * p + (f z - g z)`. Rewrite using `[hx]`. Simplify using `only [map_add, map_mul, map_natCast, map_intCast]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[he]`. Use `add_mem ?_ (sub_mem (hmap f hφ _ _ hz) (hmap g hψ _ _ hz))` and prove the remaining obligations. Rewrite using `[pow_succ]`. Conclude with `Ideal.mul_mem_mul (ih c) hpw`.

Establish `h5 : ∀ x : 𝓞 E, f x = g x`. Introduce `x`. Establish `hb` using `Ideal.iInf_pow_eq_bot_of_isDomain w.asIdeal w.isPrime.ne_top`. Establish `: f x - g x ∈ (⊥ : Ideal (𝓞 K))`. Rewrite using `[← hb]`.

Conclude with `Ideal.mem_iInf.2 fun n => h4 n x`. Conclude with `sub_eq_zero.1 (Ideal.mem_bot.1 this)`. Use `IsFractionRing.ringHom_ext (A := 𝓞 E) fun x => ?_` and prove the remaining obligations. Conclude with `congrArg (algebraMap (𝓞 K) K) (h5 x)`.
-/
theorem ringHom_eq_of_comap_eq_unramified_degree_one
    (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] (φ ψ : E →+* K)
    (w : HeightOneSpectrum (𝓞 K)) (Q : HeightOneSpectrum (𝓞 E)) (p : ℕ) (hp : p.Prime)
    (hN : Ideal.absNorm Q.asIdeal = p) (hsq : ((p : ℕ) : 𝓞 E) ∉ Q.asIdeal ^ 2)
    (hφ : ∀ r : 𝓞 E, r ∈ Q.asIdeal ↔ RingOfIntegers.mapRingHom φ r ∈ w.asIdeal)
    (hψ : ∀ r : 𝓞 E, r ∈ Q.asIdeal ↔ RingOfIntegers.mapRingHom ψ r ∈ w.asIdeal) :
    φ = ψ := by
  set f := RingOfIntegers.mapRingHom φ with hf
  set g := RingOfIntegers.mapRingHom ψ with hg
  have hpQ : ((p : ℕ) : 𝓞 E) ∈ Q.asIdeal := hN ▸ Ideal.absNorm_mem Q.asIdeal
  have hQp := Q.isPrime

  have h1 : ∀ x : 𝓞 E, ∃ a : ℤ, x - (a : 𝓞 E) ∈ Q.asIdeal := by
    intro x
    haveI : Fact p.Prime := ⟨hp⟩
    have hc : Nat.card (𝓞 E ⧸ Q.asIdeal) = p := by
      rw [← hN, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    have h := mem_zmultiples_of_prime_card (g := (1 : 𝓞 E ⧸ Q.asIdeal))
      (g' := Ideal.Quotient.mk Q.asIdeal x) hc one_ne_zero
    obtain ⟨a, ha⟩ := AddSubgroup.mem_zmultiples_iff.1 h
    refine ⟨a, Ideal.Quotient.eq.1 ?_⟩
    rw [← ha, map_intCast, zsmul_one]
  have h2 : Ideal.span {((p : ℕ) : 𝓞 E)} ⊔ Q.asIdeal ^ 2 = Q.asIdeal := by
    have h := Ideal.eq_prime_pow_of_succ_lt_of_le (P := Q.asIdeal) (i := 1)
      (I := Ideal.span {((p : ℕ) : 𝓞 E)} ⊔ Q.asIdeal ^ 2) Q.ne_bot ?_ ?_
    · simpa using h
    · refine lt_of_le_of_ne le_sup_right fun h => hsq ?_
      have h' : ((p : ℕ) : 𝓞 E) ∈ Ideal.span {((p : ℕ) : 𝓞 E)} ⊔ Q.asIdeal ^ 2 :=
        Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)
      rw [← h] at h'
      exact h'
    · rw [pow_one]
      exact sup_le ((Ideal.span_singleton_le_iff_mem _).2 hpQ) (Ideal.pow_le_self two_ne_zero)
  have h3 : ∀ n : ℕ, Q.asIdeal ≤ Ideal.span {((p : ℕ) : 𝓞 E)} ⊔ Q.asIdeal ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rcases n with _ | n
      · simp
      refine h2.ge.trans (sup_le le_sup_left ?_)
      rw [sq]
      refine (Ideal.mul_mono_right ih).trans ?_
      rw [Ideal.mul_sup, ← pow_succ']
      exact sup_le_sup_right Ideal.mul_le_right _
  have hmap : ∀ (k : 𝓞 E →+* 𝓞 K), (∀ r : 𝓞 E, r ∈ Q.asIdeal ↔ k r ∈ w.asIdeal) →
      ∀ (n : ℕ) (z : 𝓞 E), z ∈ Q.asIdeal ^ n → k z ∈ w.asIdeal ^ n := by
    intro k hk n z hz
    have h := Ideal.mem_map_of_mem k hz
    rw [Ideal.map_pow] at h
    refine Ideal.pow_right_mono ?_ n h
    exact Ideal.map_le_iff_le_comap.2 fun r hr => (hk r).1 hr
  have hpw : ((p : ℕ) : 𝓞 K) ∈ w.asIdeal := by
    simpa using (hφ _).1 hpQ
  have h4 : ∀ (n : ℕ) (x : 𝓞 E), f x - g x ∈ w.asIdeal ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro x
      obtain ⟨a, ha⟩ := h1 x
      obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 (h3 (n + 1) ha)
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
      have hx : x = c * p + z + a := by rw [hyz]; ring
      have he : f x - g x = (f c - g c) * p + (f z - g z) := by
        rw [hx]; simp only [map_add, map_mul, map_natCast, map_intCast]; ring
      rw [he]
      refine add_mem ?_ (sub_mem (hmap f hφ _ _ hz) (hmap g hψ _ _ hz))
      rw [pow_succ]
      exact Ideal.mul_mem_mul (ih c) hpw
  have h5 : ∀ x : 𝓞 E, f x = g x := by
    intro x
    have hb := Ideal.iInf_pow_eq_bot_of_isDomain w.asIdeal w.isPrime.ne_top
    have : f x - g x ∈ (⊥ : Ideal (𝓞 K)) := by
      rw [← hb]; exact Ideal.mem_iInf.2 fun n => h4 n x
    exact sub_eq_zero.1 (Ideal.mem_bot.1 this)
  refine IsFractionRing.ringHom_ext (A := 𝓞 E) fun x => ?_
  exact congrArg (algebraMap (𝓞 K) K) (h5 x)

end GlobalTheory
