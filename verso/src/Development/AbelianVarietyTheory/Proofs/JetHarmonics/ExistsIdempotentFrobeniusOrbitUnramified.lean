import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.IsSelfOf
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.UnrIdem

/- English proof (translation)
Establish `hp : Prime (l : ℤ)` using `Nat.prime_iff_prime_int.mp hl`. Establish `hun : Algebra.IsUnramifiedAt ℤ P` using `(NumberField.not_dvd_discr_iff_forall_mem E (𝓞 E) hp).mp hd P hP (by simpa using hlP)`. Establish `hov : P.LiesOver (Ideal.span {(l : ℤ)})` using `(Ideal.liesOver_span_iff hP.ne_top hp).mpr (by simpa using hlP)`. Establish `hmap : (Ideal.span {(l : ℤ)}).map (algebraMap ℤ (𝓞 E)) = Ideal.span {(l : 𝓞 E)}`. Rewrite using `[Ideal.map_span]`.

Simplify using the standard rewrite rules. Establish `hl0 : (l : 𝓞 E) ≠ 0` using `by exact_mod_cast hl.ne_zero`. Establish `hne : (Ideal.span {(l : ℤ)}).map (algebraMap ℤ (𝓞 E)) ≠ ⊥`. Rewrite using `[hmap]`. Simplify using `using hl.ne_zero`.

Establish `hP0 : P ≠ ⊥`. Introduce and unpack `rfl`. Conclude with `hl0 (by simpa using hlP)`. Use `hP.isMaximal hP0` as an intermediate fact. Take `⟨Q, h₁, h₂⟩` from `Ideal.eq_prime_pow_mul_coprime hne P`.

Rewrite `h₂` using `[← Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count _ _ hne, Ideal.ramificationIdx_eq_one P ℤ, pow_one, hmap]`. Take `⟨p, hpP, q, hqQ, hpq⟩` from `Submodule.mem_sup.mp ((Ideal.eq_top_iff_one _).mp h₁)`. Establish `key : ∀ x ∈ P, ∃ y, q * x = (l : 𝓞 E) * y`. Introduce `x hx`. Establish `: x * q ∈ Ideal.span {(l : 𝓞 E)}` using `h₂ ▸ Ideal.mul_mem_mul hx hqQ`.

Take `⟨y, hy⟩` from `Ideal.mem_span_singleton.mp this`. Conclude with `⟨y, by rw [mul_comm, hy]⟩`. Establish `hq1 : q - 1 ∈ P`. Establish `: q - 1 = -p` using `by rw [← hpq]; ring`. Rewrite using `[this]`.

Conclude with `P.neg_mem hpP`. Use `⟨q, ?_, hq1, key⟩` and prove the remaining obligations. Take `⟨y, hy⟩` from `key _ hq1`. Conclude with `⟨y, by rw [← hy]; ring⟩`.
-/
theorem exists_idem (E : Type) [Field E] [NumberField E] (l : ℕ) (hl : l.Prime)
    (hd : ¬ (l : ℤ) ∣ NumberField.discr E) (P : Ideal (𝓞 E)) [hP : P.IsPrime] (hlP : (l : 𝓞 E) ∈ P) :
    ∃ ε : 𝓞 E, (∃ y, ε * ε - ε = (l : 𝓞 E) * y) ∧ ε - 1 ∈ P ∧ ∀ x ∈ P, ∃ y, ε * x = (l : 𝓞 E) * y := by
  have hp : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl
  have hun : Algebra.IsUnramifiedAt ℤ P :=
    (NumberField.not_dvd_discr_iff_forall_mem E (𝓞 E) hp).mp hd P hP (by simpa using hlP)
  have hov : P.LiesOver (Ideal.span {(l : ℤ)}) :=
    (Ideal.liesOver_span_iff hP.ne_top hp).mpr (by simpa using hlP)
  have hmap : (Ideal.span {(l : ℤ)}).map (algebraMap ℤ (𝓞 E)) = Ideal.span {(l : 𝓞 E)} := by
    rw [Ideal.map_span]; simp
  have hl0 : (l : 𝓞 E) ≠ 0 := by exact_mod_cast hl.ne_zero
  have hne : (Ideal.span {(l : ℤ)}).map (algebraMap ℤ (𝓞 E)) ≠ ⊥ := by
    rw [hmap]; simpa using hl.ne_zero
  have hP0 : P ≠ ⊥ := by
    rintro rfl
    exact hl0 (by simpa using hlP)
  have := hP.isMaximal hP0
  obtain ⟨Q, h₁, h₂⟩ := Ideal.eq_prime_pow_mul_coprime hne P
  rw [← Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count _ _ hne,
    Ideal.ramificationIdx_eq_one P ℤ, pow_one, hmap] at h₂
  obtain ⟨p, hpP, q, hqQ, hpq⟩ := Submodule.mem_sup.mp ((Ideal.eq_top_iff_one _).mp h₁)
  have key : ∀ x ∈ P, ∃ y, q * x = (l : 𝓞 E) * y := by
    intro x hx
    have : x * q ∈ Ideal.span {(l : 𝓞 E)} := h₂ ▸ Ideal.mul_mem_mul hx hqQ
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp this
    exact ⟨y, by rw [mul_comm, hy]⟩
  have hq1 : q - 1 ∈ P := by
    have : q - 1 = -p := by rw [← hpq]; ring
    rw [this]; exact P.neg_mem hpP
  refine ⟨q, ?_, hq1, key⟩
  obtain ⟨y, hy⟩ := key _ hq1
  exact ⟨y, by rw [← hy]; ring⟩

variable {C : Type} [Field C] {V : VF C}

/- English proof (translation)
Establish `h1 : IsIntegral (Valuation.integer (V.v : Valuation C (Multiplicative (WithTop ℝ)ᵒᵈ))) x` using `hx.tower_top`. Conclude with `(Valuation.integer.integers (V.v : Valuation C (Multiplicative (WithTop ℝ)ᵒᵈ))).mem_of_integral h1`.
-/
theorem ge_int {x : C} (hx : IsIntegral ℤ x) : V.Ge 0 x := by
  have h1 : IsIntegral (Valuation.integer (V.v : Valuation C (Multiplicative (WithTop ℝ)ᵒᵈ))) x := hx.tower_top
  exact (Valuation.integer.integers (V.v : Valuation C (Multiplicative (WithTop ℝ)ᵒᵈ))).mem_of_integral h1

/- English proof (translation)
The claim follows from `V.v.map_lt_add ha hb`.
-/
theorem mm_add {a b : C} (ha : V.MM a) (hb : V.MM b) : V.MM (a + b) := V.v.map_lt_add ha hb

/- English proof (translation)
Unfold `VF.MM at *`. Unfold `VF.Ge at ha`. Rewrite using `[V.v.map_mul]`. Conclude with `lt_of_lt_of_le hb (le_add_of_nonneg_left (by simpa using ha))`.
-/
theorem mm_mul {a b : C} (ha : V.Ge 0 a) (hb : V.MM b) : V.MM (a * b) := by
  unfold VF.MM at *
  unfold VF.Ge at ha
  rw [V.v.map_mul]
  exact lt_of_lt_of_le hb (le_add_of_nonneg_left (by simpa using ha))

def ker (V : VF C) {R : Type} [CommRing R] (f : R →+* C) (hf : ∀ x, V.Ge 0 (f x)) : Ideal R where
  carrier := {x | V.MM (f x)}
  add_mem' := fun {a b} ha hb => by
    show V.MM (f (a + b))
    rw [map_add]; exact mm_add ha hb
  zero_mem' := by
    show V.MM (f 0)
    simp [VF.MM]
  smul_mem' := fun c x hx => by
    show V.MM (f (c * x))
    rw [map_mul]; exact mm_mul (hf c) hx

/- English proof (translation)
Use `⟨(Ideal.ne_top_iff_one _).mpr ?_, fun {a b} hab => ?_⟩` and prove the remaining obligations. Use `show ¬ V.MM (f 1)`. Simplify using `[VF.MM]`. Express the relevant statement in the definitionally equal form `V.MM (f (a * b)) at hab show V.MM (f a) ∨ V.MM (f b)`. Establish `ha` using `hf a`.

Establish `hb` using `hf b`. Unfold `VF.MM VF.Ge at *`. Rewrite `hab` using `[map_mul, V.v.map_mul]`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`.

Conclude with `absurd hab (not_lt.mpr (add_nonpos hc.1 hc.2))`.
-/
theorem ker_isPrime {R : Type} [CommRing R] (f : R →+* C) (hf : ∀ x, V.Ge 0 (f x)) : (ker V f hf).IsPrime := by
  refine ⟨(Ideal.ne_top_iff_one _).mpr ?_, fun {a b} hab => ?_⟩
  · show ¬ V.MM (f 1)
    simp [VF.MM]
  · change V.MM (f (a * b)) at hab
    show V.MM (f a) ∨ V.MM (f b)
    have ha := hf a
    have hb := hf b
    unfold VF.MM VF.Ge at *
    rw [map_mul, V.v.map_mul] at hab
    by_contra hc
    push Not at hc
    exact absurd hab (not_lt.mpr (add_nonpos hc.1 hc.2))

end GlobalTheory.UnrIdem

open GlobalTheory.UnrIdem in
/- English proof (translation)
Introduce `E _ _ _ H lv c T io C _ _ V ι _ hd d _ tau hF`. Establish `hint : ∀ τ x, V.Ge 0 (emA3 io ι τ x)` using `fun τ x => ge_int ((RingOfIntegers.isIntegral x).map (emA3 io ι τ).toIntAlgHom)`. Establish `hstep : ∀ x s, V.MM (emA3 io ι (tau s) x) → V.MM (emA3 io ι (tau (s + 1)) x)`. Introduce `x s hs`. Establish `h1` using `hF s x`.

Establish `h2 : V.MM (emA3 io ι (tau s) x ^ V.l)`. Take `⟨k, hk⟩` from `Nat.exists_eq_succ_of_ne_zero V.l_prime.ne_zero`. Rewrite using `[hk, pow_succ]`. Conclude with `mm_mul ((hint _ _).pow k) hs`. Simplify using `using mm_add h1 h2`.

Establish `hall : ∀ x, V.MM (emA3 io ι (tau 0) x) → ∀ a, V.MM (emA3 io ι (tau a) x)`. Introduce `x h0 a`. Establish `: ∀ n : ℕ, V.MM (emA3 io ι (tau (n : ZMod d)) x)`. Introduce `n`. Proceed by induction on `n with`.

Consider the case `zero => simpa using h0`. Consider the case `succ n ih => push_cast`. Conclude with `hstep x _ ih`. Simplify using `using this a.val`. Establish `hP` using `ker_isPrime (V := V) (emA3 io ι (tau 0)) (hint _)`.

Take `⟨ε, h1, h2, h3⟩` from `exists_idem E V.l V.l_prime hd (ker V (emA3 io ι (tau 0)) (hint _)) (by show V.MM (emA3 io ι (tau 0) (V.l : 𝓞 E))`. Rewrite using `[map_natCast]`. Unfold `VF.MM`. Rewrite using `[V.v_l]`. Conclude with `zero_lt_one)`.

Use `⟨ε, h1, fun a => ?_, fun x hx => h3 x (hx 0)⟩` and prove the remaining obligations. Use `hall _ h2 a` as an intermediate fact. Rewrite `this` using `[map_sub, map_one]`. Then use the resulting hypothesis.
-/
theorem GlobalTheory.exists_idempotent_of_unramified_place : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (lv : Level H) (c : Coeff lv) (T : CDVR) (io : c.F →+* T.Fr) (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι → ¬ (V.l : ℤ) ∣ NumberField.discr E → ∀ (d : ℕ) [NeZero d] (tau : ZMod d → (E →+* ℂ)), FrobOrd V io ι tau → ∃ ε : 𝓞 E, (∃ y, ε * ε - ε = (V.l : 𝓞 E) * y) ∧ (∀ a, V.MM (emA3 io ι (tau a) ε - 1)) ∧ ∀ x : 𝓞 E, (∀ a, V.MM (emA3 io ι (tau a) x)) → ∃ y, ε * x = (V.l : 𝓞 E) * y := by
  intro E _ _ _ H lv c T io C _ _ V ι _ hd d _ tau hF
  have hint : ∀ τ x, V.Ge 0 (emA3 io ι τ x) := fun τ x =>
    ge_int ((RingOfIntegers.isIntegral x).map (emA3 io ι τ).toIntAlgHom)
  have hstep : ∀ x s, V.MM (emA3 io ι (tau s) x) → V.MM (emA3 io ι (tau (s + 1)) x) := by
    intro x s hs
    have h1 := hF s x
    have h2 : V.MM (emA3 io ι (tau s) x ^ V.l) := by
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero V.l_prime.ne_zero
      rw [hk, pow_succ]
      exact mm_mul ((hint _ _).pow k) hs
    simpa using mm_add h1 h2
  have hall : ∀ x, V.MM (emA3 io ι (tau 0) x) → ∀ a, V.MM (emA3 io ι (tau a) x) := by
    intro x h0 a
    have : ∀ n : ℕ, V.MM (emA3 io ι (tau (n : ZMod d)) x) := by
      intro n
      induction n with
      | zero => simpa using h0
      | succ n ih => push_cast; exact hstep x _ ih
    simpa using this a.val
  have hP := ker_isPrime (V := V) (emA3 io ι (tau 0)) (hint _)
  obtain ⟨ε, h1, h2, h3⟩ := exists_idem E V.l V.l_prime hd (ker V (emA3 io ι (tau 0)) (hint _)) (by
    show V.MM (emA3 io ι (tau 0) (V.l : 𝓞 E))
    rw [map_natCast]
    unfold VF.MM
    rw [V.v_l]
    exact zero_lt_one)
  refine ⟨ε, h1, fun a => ?_, fun x hx => h3 x (hx 0)⟩
  have := hall _ h2 a
  rwa [map_sub, map_one] at this
