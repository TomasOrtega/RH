import Mathlib
open Matrix Polynomial

namespace GlobalTheory

/- English proof (translation)
Take `⟨n, y, hy⟩` from `IsArtinian.exists_pow_succ_smul_dvd a (1 : R)`. Simplify using `only [smul_eq_mul, mul_one, Nat.succ_eq_add_one] at hy`. Establish `key : ∀ k : ℕ, a ^ n = a ^ (n + k) * y ^ k`. Introduce `k`. Proceed by induction on `k with`.

Consider the case `zero => simp`. Consider the case `succ k ih => linear_combination ih + (-(a ^ k * y ^ k)) * hy`. Establish `hm : a ^ (n + 1) = a ^ (n + 1 + (n + 1)) * y ^ (n + 1)`. Take the linear combination `a * key (n + 1)`. Use `⟨a ^ (n + 1) * y ^ (n + 1), a ^ n * y ^ (n + 1), ?_, by ring, ?_⟩` and prove the remaining obligations.

Take the linear combination `(-(y ^ (n + 1))) * hm`. Establish `h0 : (1 - a ^ (n + 1) * y ^ (n + 1)) * a ^ (n + 1) = 0` using `by linear_combination hm`. Establish `hnil : IsNilpotent ((1 - a ^ (n + 1) * y ^ (n + 1)) * a)`. Use `⟨n + 1, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_pow, pow_succ (1 - a ^ (n + 1) * y ^ (n + 1)) n, mul_assoc, h0, mul_zero]`.

Use `hnil.eq_zero` as an intermediate fact. Take the linear combination `-this`.
-/
theorem reducedArtinian_exists_idem {R : Type} [CommRing R] [IsReduced R] [IsArtinianRing R]
    (a : R) : ∃ e b : R, e * e = e ∧ e = a * b ∧ a * e = a := by
  obtain ⟨n, y, hy⟩ := IsArtinian.exists_pow_succ_smul_dvd a (1 : R)
  simp only [smul_eq_mul, mul_one, Nat.succ_eq_add_one] at hy
  have key : ∀ k : ℕ, a ^ n = a ^ (n + k) * y ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => linear_combination ih + (-(a ^ k * y ^ k)) * hy
  have hm : a ^ (n + 1) = a ^ (n + 1 + (n + 1)) * y ^ (n + 1) := by
    linear_combination a * key (n + 1)
  refine ⟨a ^ (n + 1) * y ^ (n + 1), a ^ n * y ^ (n + 1), ?_, by ring, ?_⟩
  · linear_combination (-(y ^ (n + 1))) * hm
  · have h0 : (1 - a ^ (n + 1) * y ^ (n + 1)) * a ^ (n + 1) = 0 := by linear_combination hm
    have hnil : IsNilpotent ((1 - a ^ (n + 1) * y ^ (n + 1)) * a) := by
      refine ⟨n + 1, ?_⟩
      rw [mul_pow, pow_succ (1 - a ^ (n + 1) * y ^ (n + 1)) n, mul_assoc, h0, mul_zero]
    have := hnil.eq_zero
    linear_combination -this

/- English proof (translation)
Introduce `R _ _ _ σ hσ`. Set `S : Set (Ideal R)` to `{I | ∃ e : R, e * e = e ∧ e * σ e = 0 ∧ I = Ideal.span {1 - e - σ e}}`. Establish `hS : S.Nonempty` using `⟨_, 0, by simp, by simp, rfl⟩`. Take `⟨I, ⟨e, he, heσ, rfl⟩, hmin⟩` from `WellFounded.has_min wellFounded_lt S hS`. Establish `hσe : σ e * σ e = σ e` using `by rw [← map_mul, he]`.

Use `set f := 1 - e - σ e with hfdef`. Establish `hf : f * f = f` using `by linear_combination he + hσe + 2 * heσ`. Establish `hσf : σ f = f` using `by simp only [hfdef, map_sub, map_one, hσ]; ring`. Establish `hef : e * f = 0` using `by linear_combination -he - heσ`. Establish `hσef : σ e * f = 0` using `by linear_combination -hσe - heσ`.

Use `⟨e, f, he, hf, heσ, by ring, ?_⟩` and prove the remaining obligations. Introduce `w hw`. Assume the negation of the conclusion as `hwf`. Use `set w' := w * f with hw'def`. Establish `hw'σ : w' * σ w' = 0`.

Rewrite using `[hw'def, map_mul, hσf]`. Take the linear combination `(f * f) * hw`. Take `⟨ε, a, hε, hεa, hw'ε⟩` from `reducedArtinian_exists_idem w'`. Establish `hεne : ε ≠ 0`. Introduce `h0`.

Rewrite `hw'ε` using `[h0, mul_zero]`. Conclude with `hwf hw'ε.symm`. Establish `hεσ : ε * σ ε = 0`. Rewrite using `[hεa, map_mul]`. Take the linear combination `(a * σ a) * hw'σ`.

Establish `hw'f : w' * f = w'` using `by rw [hw'def, mul_assoc, hf]`. Establish `hεf : ε * f = ε` using `by rw [hεa]; linear_combination a * hw'f`. Establish `hσεf : σ ε * f = σ ε`. Use `congrArg σ hεf` as an intermediate fact. Rewrite `this` using `[map_mul, hσf]`.

Conclude with `this`. Establish `hσε : σ ε * σ ε = σ ε` using `by rw [← map_mul, hε]`. Establish `heε : e * ε = 0` using `by linear_combination (-e) * hεf + ε * hef`. Establish `heσε : e * σ ε = 0` using `by linear_combination (-e) * hσεf + σ ε * hef`. Establish `hσeε : σ e * ε = 0` using `by linear_combination (-σ e) * hεf + ε * hσef`.

Establish `hmem : Ideal.span {1 - (e + ε) - σ (e + ε)} ∈ S` using `⟨e + ε, by linear_combination he + hε + 2 * heε, by rw [map_add]; linear_combination heσ + heσε + hσeε + hεσ, rfl⟩`. Apply `hmin _ hmem` to reduce the goal to its premises. Establish `hff : f * (1 - (e + ε) - σ (e + ε)) = 1 - (e + ε) - σ (e + ε)`. Rewrite using `[map_add]`. Take the linear combination `hf - hεf - hσεf`.

Use `lt_of_le_of_ne ?_ ?_` and prove the remaining obligations. Rewrite using `[Ideal.span_singleton_le_span_singleton]`. Conclude with `⟨_, hff.symm⟩`. Introduce `hEq`. Establish `: f ∈ Ideal.span {1 - (e + ε) - σ (e + ε)}`.

Rewrite using `[hEq]`. Conclude with `Ideal.mem_span_singleton_self f`. Take `⟨c, hc⟩` from `Ideal.mem_span_singleton'.mp this`. Apply `hεne` to reduce the goal to its premises. Establish `hεg : ε * (1 - (e + ε) - σ (e + ε)) = 0`.

Rewrite using `[map_add]`. Take the linear combination `-heε - hσeε - hε - hεσ`. Take the linear combination `-hεf - ε * hc + c * hεg`.
-/
theorem reducedArtinian_involution_split :
    ∀ (R : Type) [CommRing R] [IsReduced R] [IsArtinianRing R] (σ : R →+* R), (∀ x, σ (σ x) = x) →
      ∃ e f : R, IsIdempotentElem e ∧ IsIdempotentElem f ∧ e * σ e = 0 ∧ e + σ e + f = 1 ∧
        ∀ w, w * σ w = 0 → w * f = 0 := by
  intro R _ _ _ σ hσ
  let S : Set (Ideal R) := {I | ∃ e : R, e * e = e ∧ e * σ e = 0 ∧ I = Ideal.span {1 - e - σ e}}
  have hS : S.Nonempty := ⟨_, 0, by simp, by simp, rfl⟩
  obtain ⟨I, ⟨e, he, heσ, rfl⟩, hmin⟩ := WellFounded.has_min wellFounded_lt S hS
  have hσe : σ e * σ e = σ e := by rw [← map_mul, he]
  set f := 1 - e - σ e with hfdef
  have hf : f * f = f := by linear_combination he + hσe + 2 * heσ
  have hσf : σ f = f := by simp only [hfdef, map_sub, map_one, hσ]; ring
  have hef : e * f = 0 := by linear_combination -he - heσ
  have hσef : σ e * f = 0 := by linear_combination -hσe - heσ
  refine ⟨e, f, he, hf, heσ, by ring, ?_⟩
  intro w hw
  by_contra hwf
  set w' := w * f with hw'def
  have hw'σ : w' * σ w' = 0 := by
    rw [hw'def, map_mul, hσf]; linear_combination (f * f) * hw
  obtain ⟨ε, a, hε, hεa, hw'ε⟩ := reducedArtinian_exists_idem w'
  have hεne : ε ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hw'ε; exact hwf hw'ε.symm
  have hεσ : ε * σ ε = 0 := by
    rw [hεa, map_mul]; linear_combination (a * σ a) * hw'σ
  have hw'f : w' * f = w' := by rw [hw'def, mul_assoc, hf]
  have hεf : ε * f = ε := by rw [hεa]; linear_combination a * hw'f
  have hσεf : σ ε * f = σ ε := by
    have := congrArg σ hεf; rw [map_mul, hσf] at this; exact this
  have hσε : σ ε * σ ε = σ ε := by rw [← map_mul, hε]
  have heε : e * ε = 0 := by linear_combination (-e) * hεf + ε * hef
  have heσε : e * σ ε = 0 := by linear_combination (-e) * hσεf + σ ε * hef
  have hσeε : σ e * ε = 0 := by linear_combination (-σ e) * hεf + ε * hσef
  have hmem : Ideal.span {1 - (e + ε) - σ (e + ε)} ∈ S :=
    ⟨e + ε, by linear_combination he + hε + 2 * heε,
      by rw [map_add]; linear_combination heσ + heσε + hσeε + hεσ, rfl⟩
  apply hmin _ hmem
  have hff : f * (1 - (e + ε) - σ (e + ε)) = 1 - (e + ε) - σ (e + ε) := by
    rw [map_add]; linear_combination hf - hεf - hσεf
  refine lt_of_le_of_ne ?_ ?_
  · rw [Ideal.span_singleton_le_span_singleton]
    exact ⟨_, hff.symm⟩
  · intro hEq
    have : f ∈ Ideal.span {1 - (e + ε) - σ (e + ε)} := by
      rw [hEq]; exact Ideal.mem_span_singleton_self f
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp this
    apply hεne
    have hεg : ε * (1 - (e + ε) - σ (e + ε)) = 0 := by
      rw [map_add]; linear_combination -heε - hσeε - hε - hεσ
    linear_combination -hεf - ε * hc + c * hεg

end GlobalTheory
