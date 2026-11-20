import Mathlib
import Formalism.PeriodIntegrals.CMTraceOnto

noncomputable section

namespace PI.CMT

open NumberField

variable {K : Type*} [Field K] [StarRing K]

def conj : 𝓞 K →+* 𝓞 K := RingOfIntegers.mapRingHom (starRingEnd K)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_conj (x : 𝓞 K) : ((conj x : 𝓞 K) : K) = star (x : K) := rfl

/- English proof (translation)
Apply `RingOfIntegers.ext` to reduce the goal to its premises. Rewrite using `[coe_conj, coe_conj, star_star]`.
-/
theorem conj_conj (x : 𝓞 K) : conj (conj x) = x := by
  apply RingOfIntegers.ext
  rw [coe_conj, coe_conj, star_star]

def IsTr (s : 𝓞 K) : Prop := ∃ x : 𝓞 K, x + conj x = s

/- English proof (translation)
Assemble the required witnesses or components as `⟨0, by rw [map_zero, add_zero]⟩`.
-/
theorem isTr_zero : IsTr (0 : 𝓞 K) := ⟨0, by rw [map_zero, add_zero]⟩

/- English proof (translation)
Take `⟨x, rfl⟩` from `hs`. Take `⟨y, rfl⟩` from `ht`. Conclude with `⟨x + y, by rw [map_add]; ring⟩`.
-/
theorem isTr_add {s t : 𝓞 K} (hs : IsTr s) (ht : IsTr t) : IsTr (s + t) := by
  obtain ⟨x, rfl⟩ := hs
  obtain ⟨y, rfl⟩ := ht
  exact ⟨x + y, by rw [map_add]; ring⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨x, rfl⟩`.
-/
theorem isTr_self (x : 𝓞 K) : IsTr (x + conj x) := ⟨x, rfl⟩

/- English proof (translation)
Take `⟨x, rfl⟩` from `hs`. Rewrite using `[map_add, conj_conj, add_comm]`.
-/
theorem conj_of_isTr {s : 𝓞 K} (hs : IsTr s) : conj s = s := by
  obtain ⟨x, rfl⟩ := hs
  rw [map_add, conj_conj, add_comm]

/- English proof (translation)
Take `⟨x, rfl⟩` from `hs`. Conclude with `⟨b * x, by rw [map_mul, hb]; ring⟩`.
-/
theorem isTr_mul_fixed {b s : 𝓞 K} (hb : conj b = b) (hs : IsTr s) : IsTr (b * s) := by
  obtain ⟨x, rfl⟩ := hs
  exact ⟨b * x, by rw [map_mul, hb]; ring⟩

def trIdeal (K : Type*) [Field K] [StarRing K] : Ideal (𝓞 K) := Ideal.span {s | IsTr s}

/- English proof (translation)
Assemble the required witnesses or components as `⟨u * conj v, by rw [map_mul, conj_conj]⟩`.
-/
private theorem isTr_mul_conj_add_conj_mul (u v : 𝓞 K) :
    IsTr (u * conj v + conj u * v) :=
  ⟨u * conj v, by rw [map_mul, conj_conj]⟩

/- English proof (translation)
Establish `hu' : u ∈ Submodule.span (𝓞 K) {s : 𝓞 K | IsTr s}` using `hu`. Use `clear hu`. Proceed by induction on `hu' using Submodule.span_induction with`. Consider the case `mem s hs`. Establish `hfix : conj s = s` using `conj_of_isTr hs`.

Rewrite using `[hfix]`. Conclude with `isTr_mul_fixed hfix hs`. Consider the case `zero`. Rewrite using `[map_zero, mul_zero]`. Conclude with `isTr_zero`.

Consider the case `add x y _ _ hx hy`. Establish `h` using `isTr_add (isTr_add hx hy) (isTr_mul_conj_add_conj_mul x y)`. Rewrite using `[map_add]`. Use `h using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.

Consider the case `smul a x _ hx`. Establish `hb : conj (a * conj a) = a * conj a`. Rewrite using `[map_mul, conj_conj, mul_comm]`. Establish `h` using `isTr_mul_fixed hb hx`. Rewrite using `[smul_eq_mul, map_mul]`.

Use `h using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.
-/
theorem isTr_mul_conj_of_mem {u : 𝓞 K} (hu : u ∈ trIdeal K) : IsTr (u * conj u) := by
  have hu' : u ∈ Submodule.span (𝓞 K) {s : 𝓞 K | IsTr s} := hu
  clear hu
  induction hu' using Submodule.span_induction with
  | mem s hs =>
    have hfix : conj s = s := conj_of_isTr hs
    rw [hfix]
    exact isTr_mul_fixed hfix hs
  | zero =>
    rw [map_zero, mul_zero]
    exact isTr_zero
  | add x y _ _ hx hy =>
    have h := isTr_add (isTr_add hx hy) (isTr_mul_conj_add_conj_mul x y)
    rw [map_add]
    convert h using 1
    ring
  | smul a x _ hx =>
    have hb : conj (a * conj a) = a * conj a := by
      rw [map_mul, conj_conj, mul_comm]
    have h := isTr_mul_fixed hb hx
    rw [smul_eq_mul, map_mul]
    convert h using 1
    ring

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Take `⟨P, hPmax, hle⟩` from `Ideal.exists_le_maximal _ hne`. Take `⟨θ, t, ht, hnot⟩` from `hP P hPmax`. Establish `htc : t = conj θ`. Apply `RingOfIntegers.ext` to reduce the goal to its premises.

Rewrite using `[coe_conj]`. Conclude with `ht`. Rewrite `hnot` using `[htc]`. Establish `h1 : θ + conj θ ∈ P` using `hle (Ideal.subset_span (isTr_self θ))`. Establish `h2 : θ * conj θ + conj (θ * conj θ) ∈ P` using `hle (Ideal.subset_span (isTr_self _))`.

Establish `h3 : (θ - conj θ) ^ 2 ∈ P`. Establish `e : (θ - conj θ) ^ 2 = (θ + conj θ) * (θ + conj θ) - 2 * (θ * conj θ + conj (θ * conj θ))`. Rewrite using `[map_mul, conj_conj]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Conclude with `P.sub_mem (P.mul_mem_left _ h1) (P.mul_mem_left _ h2)`. Conclude with `hnot (hPmax.isPrime.mem_of_pow_mem 2 h3)`.
-/
theorem trIdeal_eq_top
    (hP : ∀ P : Ideal (𝓞 K), P.IsMaximal →
      ∃ θ t : 𝓞 K, algebraMap (𝓞 K) K t = star (algebraMap (𝓞 K) K θ) ∧ θ - t ∉ P) :
    trIdeal K = ⊤ := by
  by_contra hne
  obtain ⟨P, hPmax, hle⟩ := Ideal.exists_le_maximal _ hne
  obtain ⟨θ, t, ht, hnot⟩ := hP P hPmax
  have htc : t = conj θ := by
    apply RingOfIntegers.ext
    rw [coe_conj]
    exact ht
  rw [htc] at hnot
  have h1 : θ + conj θ ∈ P :=
    hle (Ideal.subset_span (isTr_self θ))
  have h2 : θ * conj θ + conj (θ * conj θ) ∈ P :=
    hle (Ideal.subset_span (isTr_self _))
  have h3 : (θ - conj θ) ^ 2 ∈ P := by
    have e : (θ - conj θ) ^ 2 =
        (θ + conj θ) * (θ + conj θ) -
          2 * (θ * conj θ + conj (θ * conj θ)) := by
      rw [map_mul, conj_conj]
      ring
    rw [e]
    exact P.sub_mem (P.mul_mem_left _ h1) (P.mul_mem_left _ h2)
  exact hnot (hPmax.isPrime.mem_of_pow_mem 2 h3)

/- English proof (translation)
Establish `h1 : (1 : 𝓞 K) ∈ trIdeal K`. Rewrite using `[trIdeal_eq_top hP]`. Conclude with `Submodule.mem_top`. Establish `h` using `isTr_mul_conj_of_mem h1`. Rewrite `h` using `[map_one, mul_one]`. Then use the resulting hypothesis.
-/
theorem isTr_one
    (hP : ∀ P : Ideal (𝓞 K), P.IsMaximal →
      ∃ θ t : 𝓞 K, algebraMap (𝓞 K) K t = star (algebraMap (𝓞 K) K θ) ∧ θ - t ∉ P) :
    IsTr (1 : 𝓞 K) := by
  have h1 : (1 : 𝓞 K) ∈ trIdeal K := by
    rw [trIdeal_eq_top hP]
    exact Submodule.mem_top
  have h := isTr_mul_conj_of_mem h1
  rwa [map_one, mul_one] at h

/- English proof (translation)
Introduce `L _ _ _ hL a ha`. Establish `hfix : conj a = a`. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Rewrite using `[coe_conj]`. Conclude with `ha`.

Take `⟨x, hx⟩` from `isTr_mul_fixed hfix (isTr_one (K := L) hL.2.2)`. Use `⟨x, conj x, coe_conj x, ?_⟩` and prove the remaining obligations. Rewrite using `[hx, mul_one]`.
-/
theorem main : PI.CMTraceOnto := by
  intro L _ _ _ hL a ha
  have hfix : conj a = a := by
    apply RingOfIntegers.ext
    rw [coe_conj]
    exact ha
  obtain ⟨x, hx⟩ := isTr_mul_fixed hfix (isTr_one (K := L) hL.2.2)
  refine ⟨x, conj x, coe_conj x, ?_⟩
  rw [hx, mul_one]

end PI.CMT

end
