import Mathlib
import Formalism.HermitianLattices.StatementJac

noncomputable section

namespace Formalism.HermitianLatticesTheory

open Polynomial IsLocalRing Matrix

section Quad

variable {S : Type*} [CommRing S] [HenselianLocalRing S]

/- English proof (translation)
Use `set f : S[X] := X ^ 2 + C (T * t₀) * X + C (N * t₀ ^ 2 - d) with hfdef`. Establish `hf : f.Monic` using `by rw [hfdef]; monicity!`. Establish `he : f.eval s₀ = s₀ ^ 2 + T * s₀ * t₀ + N * t₀ ^ 2 - d`. Rewrite using `[hfdef]`. Simplify using the standard rewrite rules.

Expand and normalize the polynomial expressions, which then agree. Establish `hd : f.derivative.eval s₀ = 2 * s₀ + T * t₀`. Rewrite using `[hfdef]`. Simplify using `only [derivative_add, derivative_C, derivative_X_pow, derivative_C_mul_X, add_zero]`. Simplify using the standard rewrite rules.

Take `⟨s, hs, -⟩` from `HenselianLocalRing.is_henselian f hf s₀ (he ▸ h0) (hd ▸ h1)`. Use `⟨s, t₀, ?_⟩` and prove the remaining obligations. Establish `h2 : f.eval s = 0` using `hs`. Rewrite `h2` using `[hfdef]`. Simplify using `at h2`.

Take the linear combination `h2`.
-/
theorem unimodUnramUnique_lift (T N d s₀ t₀ : S)
    (h0 : s₀ ^ 2 + T * s₀ * t₀ + N * t₀ ^ 2 - d ∈ maximalIdeal S)
    (h1 : IsUnit (2 * s₀ + T * t₀)) :
    ∃ s t : S, s ^ 2 + T * s * t + N * t ^ 2 = d := by
  set f : S[X] := X ^ 2 + C (T * t₀) * X + C (N * t₀ ^ 2 - d) with hfdef
  have hf : f.Monic := by rw [hfdef]; monicity!
  have he : f.eval s₀ = s₀ ^ 2 + T * s₀ * t₀ + N * t₀ ^ 2 - d := by
    rw [hfdef]; simp; ring
  have hd : f.derivative.eval s₀ = 2 * s₀ + T * t₀ := by
    rw [hfdef]; simp only [derivative_add, derivative_C, derivative_X_pow, derivative_C_mul_X, add_zero]
    simp
  obtain ⟨s, hs, -⟩ := HenselianLocalRing.is_henselian f hf s₀ (he ▸ h0) (hd ▸ h1)
  refine ⟨s, t₀, ?_⟩
  have h2 : f.eval s = 0 := hs
  rw [hfdef] at h2
  simp at h2
  linear_combination h2

/- English proof (translation)
Take `⟨v, hv⟩` from `hu.exists_right_inv`. Use `⟨1 + r * ((d - 1) * v), (d - 1) * v, ?_⟩` and prove the remaining obligations. Take the linear combination `((d - 1) * v) ^ 2 * hr + (d - 1) * hv`.
-/
theorem unimodUnramUnique_split (T N d r : S) (hr : r ^ 2 + T * r + N = 0)
    (hu : IsUnit (T + 2 * r)) : ∃ s t : S, s ^ 2 + T * s * t + N * t ^ 2 = d := by
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  refine ⟨1 + r * ((d - 1) * v), (d - 1) * v, ?_⟩
  linear_combination ((d - 1) * v) ^ 2 * hr + (d - 1) * hv

/- English proof (translation)
Use `Fintype.ofFinite k` as an intermediate fact. Break down `Nat.mod_two_eq_zero_or_one (Fintype.card k) with h | h` into its components or cases. Take `⟨c, hc⟩` from `FiniteField.isSquare_of_char_two (FiniteField.even_card_iff_char_two.2 h) d`. Conclude with `⟨c, 0, by rw [hc]; ring⟩`. Establish `h2 : (2 : k) ≠ 0` using `Ring.two_ne_zero (fun hc => by`.

Rewrite using `[FiniteField.even_card_iff_char_two.1 hc] at h; exact absurd h (by decide))`. Establish `hf : (X ^ 2 : k[X]).degree = 2` using `by compute_degree!`. Establish `hg : (C (-(T ^ 2 - 4 * N)) * X ^ 2 + C (-(4 * d)) : k[X]).degree = 2` using `by compute_degree!`. Introduce `h; exact hD (by linear_combination -h)`. Take `⟨x, y, hxy⟩` from `FiniteField.exists_root_sum_quadratic hf hg h`.

Simplify using `at hxy`. Use `⟨(x - T * y) / 2, y, ?_⟩` and prove the remaining obligations. Clear the denominators using the available nonvanishing facts. Take the linear combination `hxy`.
-/
theorem unimodUnramUnique_ff {k : Type*} [Field k] [Finite k] (T N d : k)
    (hD : T ^ 2 - 4 * N ≠ 0) : ∃ a b : k, a ^ 2 + T * a * b + N * b ^ 2 = d := by
  classical
  have := Fintype.ofFinite k
  rcases Nat.mod_two_eq_zero_or_one (Fintype.card k) with h | h
  · obtain ⟨c, hc⟩ := FiniteField.isSquare_of_char_two (FiniteField.even_card_iff_char_two.2 h) d
    exact ⟨c, 0, by rw [hc]; ring⟩
  · have h2 : (2 : k) ≠ 0 := Ring.two_ne_zero (fun hc => by
      rw [FiniteField.even_card_iff_char_two.1 hc] at h; exact absurd h (by decide))
    have hf : (X ^ 2 : k[X]).degree = 2 := by compute_degree!
    have hg : (C (-(T ^ 2 - 4 * N)) * X ^ 2 + C (-(4 * d)) : k[X]).degree = 2 := by
      compute_degree!
      intro h; exact hD (by linear_combination -h)
    obtain ⟨x, y, hxy⟩ := FiniteField.exists_root_sum_quadratic hf hg h
    simp at hxy
    refine ⟨(x - T * y) / 2, y, ?_⟩
    field_simp
    linear_combination hxy

/- English proof (translation)
Establish `hD' : residue S (T ^ 2 - 4 * N) ≠ 0` using `(residue_ne_zero_iff_isUnit _).2 hD`. Establish `h2 : residue S 2 = 2` using `map_ofNat _ 2`. Establish `h4 : residue S 4 = 4` using `map_ofNat _ 4`. Distinguish the cases in `hroot : ∃ ρ : ResidueField S, ρ ^ 2 + residue S T * ρ + residue S N = 0`. Take `⟨ρ, hρ⟩` from `hroot`.

Take `⟨r₀, rfl⟩` from `residue_surjective ρ`. Use `set g : S[X] := X ^ 2 + C T * X + C N with hgdef`. Establish `hg : g.Monic` using `by rw [hgdef]; monicity!`. Establish `he : g.eval r₀ = r₀ ^ 2 + T * r₀ + N` using `by rw [hgdef]; simp`. Establish `hd1 : g.derivative.eval r₀ = 2 * r₀ + T` using `by rw [hgdef]; simp; ring`.

Establish `hsq : (2 * r₀ + T) ^ 2 = (T ^ 2 - 4 * N) + 4 * (r₀ ^ 2 + T * r₀ + N)` using `by ring`. Establish `h0 : g.eval r₀ ∈ maximalIdeal S`. Rewrite using `[he, ← residue_eq_zero_iff]`. Simplify using `using hρ`. Establish `h1 : IsUnit (g.derivative.eval r₀)`.

Rewrite using `[hd1, ← residue_ne_zero_iff_isUnit]`. Introduce `hz`. Apply `hD'` to reduce the goal to its premises. Establish `key : residue S (T ^ 2 - 4 * N) = (residue S (2 * r₀ + T)) ^ 2 - 4 * residue S (r₀ ^ 2 + T * r₀ + N)`. Rewrite using `[← map_pow, ← map_ofNat (residue S) 4, ← map_mul, ← map_sub]`.

Use `congr 1`. Take the linear combination `-hsq`. Establish `hz2 : residue S (r₀ ^ 2 + T * r₀ + N) = 0` using `(residue_eq_zero_iff _).2 (he ▸ h0)`. Rewrite using `[key, hz, hz2]`. Expand and normalize the polynomial expressions, which then agree.

Take `⟨r, hr, -⟩` from `HenselianLocalRing.is_henselian g hg r₀ h0 h1`. Establish `hr' : r ^ 2 + T * r + N = 0`. Establish `h2 : g.eval r = 0` using `hr`. Rewrite `h2` using `[hgdef]`. Simplify using `using h2`.

Apply `unimodUnramUnique_split T N d r hr'` to reduce the goal to its premises. Establish `: (T + 2 * r) ^ 2 = T ^ 2 - 4 * N` using `by linear_combination 4 * hr'`. Rewrite using `[← isUnit_pow_iff (two_ne_zero), this]`. Conclude with `hD`. Use `push Not at hroot`.

Establish `hN : IsUnit N`. Rewrite using `[← residue_ne_zero_iff_isUnit]`. Introduce `h; exact hroot 0 (by simp [h])`. Take `⟨a, b, hab⟩` from `unimodUnramUnique_ff (residue S T) (residue S N) (residue S d) (by simpa [h4] using hD')`. Take `⟨s₀, rfl⟩` from `residue_surjective a`.

Take `⟨t₀, rfl⟩` from `residue_surjective b`. Establish `h0 : s₀ ^ 2 + T * s₀ * t₀ + N * t₀ ^ 2 - d ∈ maximalIdeal S`. Rewrite using `[← residue_eq_zero_iff]`. Simplify using `only [map_sub, map_add, map_mul, map_pow]`. Rewrite using `[hab]`.

Expand and normalize the polynomial expressions, which then agree. Distinguish the cases in `hs : IsUnit (2 * s₀ + T * t₀)`. Conclude with `unimodUnramUnique_lift T N d s₀ t₀ h0 hs`. Establish `ht : IsUnit (T * s₀ + 2 * N * t₀)`. Rewrite using `[← residue_ne_zero_iff_isUnit]`.

Rewrite `hs` using `[← residue_ne_zero_iff_isUnit, not_not]`. Introduce `ht`. Establish `hs'` using `hs`. Simplify using `only [map_add, map_mul, h2] at hs' ht`. Establish `hdz : residue S d ≠ 0` using `(residue_ne_zero_iff_isUnit _).2 hd`.

Apply `hdz` to reduce the goal to its premises. Rewrite using `[← hab]`. Establish `hDk : residue S T ^ 2 - 4 * residue S N ≠ 0` using `by simpa [h4] using hD'`. Establish `htz : residue S t₀ = 0`. Establish `: (residue S T ^ 2 - 4 * residue S N) * residue S t₀ = 0`.

Take the linear combination `residue S T * hs' - 2 * ht`. Break down `mul_eq_zero.1 this with h | h` into its components or cases. Conclude with `absurd h hDk`. Conclude with `h`. Establish `hsz : residue S s₀ = 0`.

Establish `: (residue S T ^ 2 - 4 * residue S N) * residue S s₀ = 0`. Take the linear combination `residue S T * ht - 2 * residue S N * hs'`. Break down `mul_eq_zero.1 this with h | h` into its components or cases. Conclude with `absurd h hDk`. Conclude with `h`.

Simplify using `[htz, hsz]`. Take `⟨v, hv⟩` from `hN.exists_right_inv`. Take `⟨t, s, hts⟩` from `unimodUnramUnique_lift (T * v) v (d * v) t₀ s₀ (by`. Establish `: t₀ ^ 2 + T * v * t₀ * s₀ + v * s₀ ^ 2 - d * v = v * (s₀ ^ 2 + T * s₀ * t₀ + N * t₀ ^ 2 - d) + (1 - N * v) * t₀ ^ 2` using `by ring`. Rewrite using `[this, hv, sub_self, zero_mul, add_zero]`.

Conclude with `Ideal.mul_mem_left _ _ h0)`. Use the proof step `(by`. Establish `: 2 * t₀ + T * v * s₀ = v * (T * s₀ + 2 * N * t₀) + (1 - N * v) * (2 * t₀)` using `by ring`. Rewrite using `[this, hv, sub_self, zero_mul, add_zero]`. Conclude with `(isUnit_iff_exists_inv.2 ⟨N, by rw [mul_comm]; exact hv⟩).mul ht)`.

Conclude with `⟨s, t, by linear_combination N * hts - (T * s * t + s ^ 2 - d) * hv⟩`.
-/
theorem unimodUnramUnique_quad [Finite (ResidueField S)] (T N d : S)
    (hD : IsUnit (T ^ 2 - 4 * N)) (hd : IsUnit d) :
    ∃ s t : S, s ^ 2 + T * s * t + N * t ^ 2 = d := by
  have hD' : residue S (T ^ 2 - 4 * N) ≠ 0 := (residue_ne_zero_iff_isUnit _).2 hD
  have h2 : residue S 2 = 2 := map_ofNat _ 2
  have h4 : residue S 4 = 4 := map_ofNat _ 4
  by_cases hroot : ∃ ρ : ResidueField S, ρ ^ 2 + residue S T * ρ + residue S N = 0
  · obtain ⟨ρ, hρ⟩ := hroot
    obtain ⟨r₀, rfl⟩ := residue_surjective ρ
    set g : S[X] := X ^ 2 + C T * X + C N with hgdef
    have hg : g.Monic := by rw [hgdef]; monicity!
    have he : g.eval r₀ = r₀ ^ 2 + T * r₀ + N := by rw [hgdef]; simp
    have hd1 : g.derivative.eval r₀ = 2 * r₀ + T := by rw [hgdef]; simp; ring
    have hsq : (2 * r₀ + T) ^ 2 = (T ^ 2 - 4 * N) + 4 * (r₀ ^ 2 + T * r₀ + N) := by ring
    have h0 : g.eval r₀ ∈ maximalIdeal S := by
      rw [he, ← residue_eq_zero_iff]; simpa using hρ
    have h1 : IsUnit (g.derivative.eval r₀) := by
      rw [hd1, ← residue_ne_zero_iff_isUnit]
      intro hz
      apply hD'
      have key : residue S (T ^ 2 - 4 * N) = (residue S (2 * r₀ + T)) ^ 2
          - 4 * residue S (r₀ ^ 2 + T * r₀ + N) := by
        rw [← map_pow, ← map_ofNat (residue S) 4, ← map_mul, ← map_sub]
        congr 1; linear_combination -hsq
      have hz2 : residue S (r₀ ^ 2 + T * r₀ + N) = 0 := (residue_eq_zero_iff _).2 (he ▸ h0)
      rw [key, hz, hz2]; ring
    obtain ⟨r, hr, -⟩ := HenselianLocalRing.is_henselian g hg r₀ h0 h1
    have hr' : r ^ 2 + T * r + N = 0 := by
      have h2 : g.eval r = 0 := hr
      rw [hgdef] at h2; simpa using h2
    apply unimodUnramUnique_split T N d r hr'
    have : (T + 2 * r) ^ 2 = T ^ 2 - 4 * N := by linear_combination 4 * hr'
    rw [← isUnit_pow_iff (two_ne_zero), this]; exact hD
  · push Not at hroot
    have hN : IsUnit N := by
      rw [← residue_ne_zero_iff_isUnit]
      intro h; exact hroot 0 (by simp [h])
    obtain ⟨a, b, hab⟩ := unimodUnramUnique_ff (residue S T) (residue S N) (residue S d)
      (by simpa [h4] using hD')
    obtain ⟨s₀, rfl⟩ := residue_surjective a
    obtain ⟨t₀, rfl⟩ := residue_surjective b
    have h0 : s₀ ^ 2 + T * s₀ * t₀ + N * t₀ ^ 2 - d ∈ maximalIdeal S := by
      rw [← residue_eq_zero_iff]; simp only [map_sub, map_add, map_mul, map_pow]
      rw [hab]; ring
    by_cases hs : IsUnit (2 * s₀ + T * t₀)
    · exact unimodUnramUnique_lift T N d s₀ t₀ h0 hs
    ·
      have ht : IsUnit (T * s₀ + 2 * N * t₀) := by
        rw [← residue_ne_zero_iff_isUnit]
        rw [← residue_ne_zero_iff_isUnit, not_not] at hs
        intro ht
        have hs' := hs
        simp only [map_add, map_mul, h2] at hs' ht
        have hdz : residue S d ≠ 0 := (residue_ne_zero_iff_isUnit _).2 hd
        apply hdz
        rw [← hab]
        have hDk : residue S T ^ 2 - 4 * residue S N ≠ 0 := by simpa [h4] using hD'
        have htz : residue S t₀ = 0 := by
          have : (residue S T ^ 2 - 4 * residue S N) * residue S t₀ = 0 := by
            linear_combination residue S T * hs' - 2 * ht
          rcases mul_eq_zero.1 this with h | h
          · exact absurd h hDk
          · exact h
        have hsz : residue S s₀ = 0 := by
          have : (residue S T ^ 2 - 4 * residue S N) * residue S s₀ = 0 := by
            linear_combination residue S T * ht - 2 * residue S N * hs'
          rcases mul_eq_zero.1 this with h | h
          · exact absurd h hDk
          · exact h
        simp [htz, hsz]
      obtain ⟨v, hv⟩ := hN.exists_right_inv
      obtain ⟨t, s, hts⟩ := unimodUnramUnique_lift (T * v) v (d * v) t₀ s₀
        (by
          have : t₀ ^ 2 + T * v * t₀ * s₀ + v * s₀ ^ 2 - d * v
              = v * (s₀ ^ 2 + T * s₀ * t₀ + N * t₀ ^ 2 - d) + (1 - N * v) * t₀ ^ 2 := by ring
          rw [this, hv, sub_self, zero_mul, add_zero]
          exact Ideal.mul_mem_left _ _ h0)
        (by
          have : 2 * t₀ + T * v * s₀ = v * (T * s₀ + 2 * N * t₀) + (1 - N * v) * (2 * t₀) := by ring
          rw [this, hv, sub_self, zero_mul, add_zero]
          exact (isUnit_iff_exists_inv.2 ⟨N, by rw [mul_comm]; exact hv⟩).mul ht)
      exact ⟨s, t, by linear_combination N * hts - (T * s * t + s ^ 2 - d) * hv⟩

end Quad

section Herm

variable {R : Type} [CommRing R] [StarRing R] {R₀ : Subring R}

/- English proof (translation)
Take `⟨y, hy⟩` from `hu.exists_right_inv`. Establish `h1 : star y * x = 1`. Use `congrArg star hy` as an intermediate fact. Rewrite `this` using `[star_mul, hx, star_one]`. Then use the resulting hypothesis. Establish `hy' : star y = y`.

Combine the equalities or inequalities in the displayed calculation. Conclude with `isUnit_iff_exists_inv.2 ⟨⟨y, (hR₀ y).2 hy'⟩, Subtype.ext hy⟩`.
-/
theorem unimodUnramUnique_fixUnit (hR₀ : ∀ x, x ∈ R₀ ↔ star x = x) {x : R} (hx : star x = x)
    (hu : IsUnit x) : IsUnit (⟨x, (hR₀ x).2 hx⟩ : R₀) := by
  obtain ⟨y, hy⟩ := hu.exists_right_inv
  have h1 : star y * x = 1 := by
    have := congrArg star hy
    rwa [star_mul, hx, star_one] at this
  have hy' : star y = y := by
    calc star y = star y * (x * y) := by rw [hy, mul_one]
      _ = (star y * x) * y := by ring
      _ = y := by rw [h1, one_mul]
  exact isUnit_iff_exists_inv.2 ⟨⟨y, (hR₀ y).2 hy'⟩, Subtype.ext hy⟩

/- English proof (translation)
Establish `hxy : star (x + y) = x + y` using `by rw [star_add, hx, hy]`. Use `unimodUnramUnique_fixUnit hR₀ hxy h` as an intermediate fact. Establish `e : (⟨x + y, (hR₀ _).2 hxy⟩ : R₀) = ⟨x, (hR₀ x).2 hx⟩ + ⟨y, (hR₀ y).2 hy⟩` using `rfl`. Rewrite `this` using `[e]`. Break down `IsLocalRing.isUnit_or_isUnit_of_isUnit_add this with h1 | h1` into its components or cases.

Conclude with `Or.inl (by simpa using h1.map R₀.subtype)`. Conclude with `Or.inr (by simpa using h1.map R₀.subtype)`.
-/
theorem unimodUnramUnique_unitAdd [IsLocalRing R₀] (hR₀ : ∀ x, x ∈ R₀ ↔ star x = x) {x y : R}
    (hx : star x = x) (hy : star y = y) (h : IsUnit (x + y)) : IsUnit x ∨ IsUnit y := by
  have hxy : star (x + y) = x + y := by rw [star_add, hx, hy]
  have := unimodUnramUnique_fixUnit hR₀ hxy h
  have e : (⟨x + y, (hR₀ _).2 hxy⟩ : R₀) = ⟨x, (hR₀ x).2 hx⟩ + ⟨y, (hR₀ y).2 hy⟩ := rfl
  rw [e] at this
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add this with h1 | h1
  · exact Or.inl (by simpa using h1.map R₀.subtype)
  · exact Or.inr (by simpa using h1.map R₀.subtype)

/- English proof (translation)
Rewrite using `[star_add, star_star, add_comm]`.
-/
theorem unimodUnramUnique_trFix (x : R) : star (x + star x) = x + star x := by
  rw [star_add, star_star, add_comm]

/- English proof (translation)
Assemble the required witnesses or components as `⟨⟨0, 1, fun h => zero_ne_one (α := R₀) (Subtype.ext (by simpa using h))⟩⟩`.
-/
theorem unimodUnramUnique_nontriv [IsLocalRing R₀] : Nontrivial R :=
  ⟨⟨0, 1, fun h => zero_ne_one (α := R₀) (Subtype.ext (by simpa using h))⟩⟩

def unimodUnramUnique_J [IsLocalRing R₀] (hR₀ : ∀ x, x ∈ R₀ ↔ star x = x) : Ideal R where
  carrier := {r | ∀ c : R, ¬ IsUnit (c * r + star (c * r))}
  add_mem' := by
    intro a b ha hb c h
    have e : c * (a + b) + star (c * (a + b))
        = (c * a + star (c * a)) + (c * b + star (c * b)) := by
      rw [mul_add, star_add]; ring
    rw [e] at h
    rcases unimodUnramUnique_unitAdd hR₀ (unimodUnramUnique_trFix _)
      (unimodUnramUnique_trFix _) h with h | h
    exacts [ha c h, hb c h]
  zero_mem' := fun c => by
    have := unimodUnramUnique_nontriv (R₀ := R₀)
    simp
  smul_mem' := by
    intro a r hr c
    simpa [smul_eq_mul, mul_assoc] using hr (c * a)

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem unimodUnramUnique_mem_J [IsLocalRing R₀] (hR₀ : ∀ x, x ∈ R₀ ↔ star x = x) (r : R) :
    r ∈ unimodUnramUnique_J hR₀ ↔ ∀ c : R, ¬ IsUnit (c * r + star (c * r)) := Iff.rfl

/- English proof (translation)
Simplify `congrFun (congrFun hA i) j` using `[conjTranspose_apply]`.
-/
theorem unimodUnramUnique_hermFix {ι : Type} (A : Matrix ι ι R) (hA : Aᴴ = A) (i j : ι) :
    star (A j i) = A i j := by
  simpa [conjTranspose_apply] using congrFun (congrFun hA i) j

/- English proof (translation)
Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Establish `hmem : ∀ i j, A i j ∈ unimodUnramUnique_J hR₀`. Introduce `i j`. Rewrite using `[unimodUnramUnique_mem_J]`.

Introduce `c`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Establish `hfix` using `unimodUnramUnique_hermFix A hA i i`. Establish `e : c * A i i + star (c * A i i) = (c + star c) * A i i`.

Rewrite using `[star_mul, hfix]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `fun h => hdiag i (isUnit_of_mul_isUnit_right h)`. Conclude with `hcon i j c hij`.

Establish `hdetJ : A.det ∈ unimodUnramUnique_J hR₀`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, RingHom.map_det]`. Establish `: (Ideal.Quotient.mk (unimodUnramUnique_J hR₀)).mapMatrix A = 0`. Use extensionality with `i j`. Simplify `hmem i j` using `[Ideal.Quotient.eq_zero_iff_mem]`.

Rewrite using `[this, det_zero]`. Establish `htop` using `Ideal.eq_top_of_isUnit_mem _ hdetJ hdet`. Establish `h1 : (1 : R) ∈ unimodUnramUnique_J hR₀` using `htop ▸ Submodule.mem_top`. Rewrite `h1` using `[unimodUnramUnique_mem_J]`. Take `⟨v, hv⟩` from `hθ.exists_right_inv`.

Apply `h1 (θ * v)` to reduce the goal to its premises. Establish `h2 : star v * (θ - star θ) = -1`. Use `congrArg star hv` as an intermediate fact. Rewrite `this` using `[star_mul, star_sub, star_star, star_one]`. Take the linear combination `-this`.

Establish `hsv : star v = -v`. Combine the equalities or inequalities in the displayed calculation. Establish `: θ * v * 1 + star (θ * v * 1) = 1`. Rewrite using `[mul_one, star_mul, hsv]`. Take the linear combination `hv`.

Rewrite using `[this]`. Conclude with `isUnit_one`.
-/
theorem unimodUnramUnique_offdiag [IsLocalRing R₀] (hR₀ : ∀ x, x ∈ R₀ ↔ star x = x)
    {θ : R} (hθ : IsUnit (θ - star θ)) {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A : Matrix ι ι R) (hA : Aᴴ = A) (hdet : IsUnit A.det) (hdiag : ∀ i, ¬ IsUnit (A i i)) :
    ∃ i j c, i ≠ j ∧ IsUnit (c * A i j + star (c * A i j)) := by
  by_contra hcon
  push Not at hcon
  have hmem : ∀ i j, A i j ∈ unimodUnramUnique_J hR₀ := by
    intro i j
    rw [unimodUnramUnique_mem_J]
    intro c
    by_cases hij : i = j
    · subst hij
      have hfix := unimodUnramUnique_hermFix A hA i i
      have e : c * A i i + star (c * A i i) = (c + star c) * A i i := by
        rw [star_mul, hfix]; ring
      rw [e]; exact fun h => hdiag i (isUnit_of_mul_isUnit_right h)
    · exact hcon i j c hij
  have hdetJ : A.det ∈ unimodUnramUnique_J hR₀ := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, RingHom.map_det]
    have : (Ideal.Quotient.mk (unimodUnramUnique_J hR₀)).mapMatrix A = 0 := by
      ext i j
      simpa [Ideal.Quotient.eq_zero_iff_mem] using hmem i j
    rw [this, det_zero]
  have htop := Ideal.eq_top_of_isUnit_mem _ hdetJ hdet
  have h1 : (1 : R) ∈ unimodUnramUnique_J hR₀ := htop ▸ Submodule.mem_top
  rw [unimodUnramUnique_mem_J] at h1
  obtain ⟨v, hv⟩ := hθ.exists_right_inv
  apply h1 (θ * v)
  have h2 : star v * (θ - star θ) = -1 := by
    have := congrArg star hv
    rw [star_mul, star_sub, star_star, star_one] at this
    linear_combination -this
  have hsv : star v = -v := by
    calc star v = star v * ((θ - star θ) * v) := by rw [hv, mul_one]
      _ = (star v * (θ - star θ)) * v := by ring
      _ = -v := by rw [h2]; ring
  have : θ * v * 1 + star (θ * v * 1) = 1 := by
    rw [mul_one, star_mul, hsv]; linear_combination hv
  rw [this]; exact isUnit_one

/- English proof (translation)
Establish `hT : star (θ + star θ) = θ + star θ` using `unimodUnramUnique_trFix θ`. Establish `hN : star (star θ * θ) = star θ * θ` using `by rw [star_mul, star_star]`. Establish `hD : star ((θ - star θ) ^ 2) = (θ - star θ) ^ 2`. Rewrite using `[star_pow, star_sub, star_star]`. Expand and normalize the polynomial expressions, which then agree.

Use `set T : R₀ := ⟨θ + star θ, (hR₀ _).2 hT⟩ with hTdef`. Use `set N : R₀ := ⟨star θ * θ, (hR₀ _).2 hN⟩ with hNdef`. Use `set d₀ : R₀ := ⟨d, (hR₀ _).2 hd⟩ with hd₀def`. Establish `hDu : IsUnit (T ^ 2 - 4 * N)`. Use `unimodUnramUnique_fixUnit hR₀ hD (hθ.pow 2)` as an intermediate fact.

Use `this using 1` and compare the differences between its conclusion and the goal. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [hTdef, hNdef]`. Use `push_cast`. Rewrite using `[show ((4 : R₀) : R) = 4 from map_ofNat R₀.subtype 4]`.

Expand and normalize the polynomial expressions, which then agree. Take `⟨s, t, hst⟩` from `unimodUnramUnique_quad T N d₀ hDu (unimodUnramUnique_fixUnit hR₀ hd hdu)`. Use `⟨(s : R) + (t : R) * θ, ?_⟩` and prove the remaining obligations. Establish `hs : star (s : R) = s` using `(hR₀ _).1 s.2`. Establish `ht : star (t : R) = t` using `(hR₀ _).1 t.2`.

Use `congrArg Subtype.val hst` as an intermediate fact. Simplify using `only [hTdef, hNdef, hd₀def] at this`. Move the coercions through the operations in `at this`. Rewrite using `[star_add, star_mul, hs, ht]`. Take the linear combination `this`.
-/
theorem unimodUnramUnique_norm [HenselianLocalRing R₀] [Finite (ResidueField R₀)]
    (hR₀ : ∀ x, x ∈ R₀ ↔ star x = x) {θ : R} (hθ : IsUnit (θ - star θ)) {d : R}
    (hd : star d = d) (hdu : IsUnit d) : ∃ w : R, star w * w = d := by
  have hT : star (θ + star θ) = θ + star θ := unimodUnramUnique_trFix θ
  have hN : star (star θ * θ) = star θ * θ := by rw [star_mul, star_star]
  have hD : star ((θ - star θ) ^ 2) = (θ - star θ) ^ 2 := by
    rw [star_pow, star_sub, star_star]; ring
  set T : R₀ := ⟨θ + star θ, (hR₀ _).2 hT⟩ with hTdef
  set N : R₀ := ⟨star θ * θ, (hR₀ _).2 hN⟩ with hNdef
  set d₀ : R₀ := ⟨d, (hR₀ _).2 hd⟩ with hd₀def
  have hDu : IsUnit (T ^ 2 - 4 * N) := by
    have := unimodUnramUnique_fixUnit hR₀ hD (hθ.pow 2)
    convert this using 1
    apply Subtype.ext
    simp only [hTdef, hNdef]
    push_cast
    rw [show ((4 : R₀) : R) = 4 from map_ofNat R₀.subtype 4]
    ring
  obtain ⟨s, t, hst⟩ :=
    unimodUnramUnique_quad T N d₀ hDu (unimodUnramUnique_fixUnit hR₀ hd hdu)
  refine ⟨(s : R) + (t : R) * θ, ?_⟩
  have hs : star (s : R) = s := (hR₀ _).1 s.2
  have ht : star (t : R) = t := (hR₀ _).1 t.2
  have := congrArg Subtype.val hst
  simp only [hTdef, hNdef, hd₀def] at this
  push_cast at this
  rw [star_add, star_mul, hs, ht]
  linear_combination this

/- English proof (translation)
Establish `hfix` using `unimodUnramUnique_hermFix A hA i i`. Take `⟨v, hv⟩` from `hi.exists_right_inv`. Establish `h1 : star v * A i i = 1`. Use `congrArg star hv` as an intermediate fact. Rewrite `this` using `[star_mul, hfix, star_one]`. Then use the resulting hypothesis.

Establish `hvfix : star v = v`. Combine the equalities or inequalities in the displayed calculation. Establish `hvu : IsUnit v` using `isUnit_iff_exists_inv.2 ⟨A i i, by rw [mul_comm]; exact hv⟩`. Take `⟨w, hw⟩` from `unimodUnramUnique_norm hR₀ hθ hvfix hvu`. Establish `hwu : IsUnit w` using `isUnit_of_mul_isUnit_right (hw ▸ hvu)`.

Use `⟨diagonal (Function.update 1 i w), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[det_diagonal, Finset.prod_update_of_mem (Finset.mem_univ i)]`. Simplify using `using hwu`. Rewrite using `[diagonal_conjTranspose]`. Simplify using `[diagonal_mul, mul_diagonal]`.

Take the linear combination `(A i i) * hw + hv`.
-/
theorem unimodUnramUnique_scale [HenselianLocalRing R₀] [Finite (ResidueField R₀)]
    (hR₀ : ∀ x, x ∈ R₀ ↔ star x = x) {θ : R} (hθ : IsUnit (θ - star θ))
    {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι R) (hA : Aᴴ = A) (i : ι)
    (hi : IsUnit (A i i)) : ∃ g : Matrix ι ι R, IsUnit g.det ∧ (gᴴ * A * g) i i = 1 := by
  have hfix := unimodUnramUnique_hermFix A hA i i
  obtain ⟨v, hv⟩ := hi.exists_right_inv
  have h1 : star v * A i i = 1 := by
    have := congrArg star hv; rwa [star_mul, hfix, star_one] at this
  have hvfix : star v = v := by
    calc star v = star v * (A i i * v) := by rw [hv, mul_one]
      _ = (star v * A i i) * v := by ring
      _ = v := by rw [h1, one_mul]
  have hvu : IsUnit v := isUnit_iff_exists_inv.2 ⟨A i i, by rw [mul_comm]; exact hv⟩
  obtain ⟨w, hw⟩ := unimodUnramUnique_norm hR₀ hθ hvfix hvu
  have hwu : IsUnit w := isUnit_of_mul_isUnit_right (hw ▸ hvu)
  refine ⟨diagonal (Function.update 1 i w), ?_, ?_⟩
  · rw [det_diagonal, Finset.prod_update_of_mem (Finset.mem_univ i)]
    simpa using hwu
  · rw [diagonal_conjTranspose]
    simp [diagonal_mul, mul_diagonal]
    linear_combination (A i i) * hw + hv

/- English proof (translation)
Simplify using `[transvection, Matrix.add_mul, Matrix.mul_add, conjTranspose_single, single_mul_apply_same, mul_single_apply_same, Matrix.mul_assoc]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem unimodUnramUnique_transv {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι R)
    (i j : ι) (c : R) :
    ((transvection j i c)ᴴ * A * transvection j i c) i i
      = A i i + (c * A i j + star c * A j i) + star c * c * A j j := by
  simp [transvection, Matrix.add_mul, Matrix.mul_add, conjTranspose_single,
    single_mul_apply_same, mul_single_apply_same, Matrix.mul_assoc]
  ring

/- English proof (translation)
Distinguish the cases in `h : ∃ i, IsUnit (A i i)`. Take `⟨i, hi⟩` from `h`. Take `⟨g, hg, hgi⟩` from `unimodUnramUnique_scale hR₀ hθ A hA i hi`. Conclude with `⟨g, hg, i, hgi⟩`. Use `push Not at h`.

Take `⟨i, j, c, hij, hc⟩` from `unimodUnramUnique_offdiag hR₀ hθ A hA hdet h`. Use `set g₁ := transvection j i c with hg₁def`. Use `set B := g₁ᴴ * A * g₁ with hBdef`. Establish `hB : Bᴴ = B` using `by simp [hBdef, conjTranspose_mul, hA, Matrix.mul_assoc]`. Establish `hBi : IsUnit (B i i)`.

Rewrite using `[hBdef, hg₁def, unimodUnramUnique_transv A i j c]`. Establish `hji : A j i = star (A i j)` using `(unimodUnramUnique_hermFix A hA j i).symm`. Establish `hfi` using `unimodUnramUnique_hermFix A hA i i`. Establish `hfj` using `unimodUnramUnique_hermFix A hA j j`. Establish `e : A i i + (c * A i j + star c * A j i) + star c * c * A j j = (c * A i j + star (c * A i j)) + (A i i + star c * c * A j j)`.

Rewrite using `[star_mul, ← hji]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Establish `hfy : star (A i i + star c * c * A j j) = A i i + star c * c * A j j`. Simplify using `only [star_add, star_mul, star_star, hfi, hfj]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hy : ¬ IsUnit (A i i + star c * c * A j j)`. Introduce `hy`. Establish `hfz : star (star c * c * A j j) = star c * c * A j j`. Simplify using `only [star_mul, star_star, hfj]`.

Expand and normalize the polynomial expressions, which then agree. Break down `unimodUnramUnique_unitAdd hR₀ hfi hfz hy with h1 | h1` into its components or cases. Conclude with `h i h1`. Conclude with `h j (isUnit_of_mul_isUnit_right h1)`. Assume the negation of the conclusion as `hn`.

Establish `hsum : IsUnit ((c * A i j + star (c * A i j) + (A i i + star c * c * A j j)) + -(A i i + star c * c * A j j))` using `by rw [add_neg_cancel_right]; exact hc`. Establish `hfs : star (c * A i j + star (c * A i j) + (A i i + star c * c * A j j)) = c * A i j + star (c * A i j) + (A i i + star c * c * A j j)`. Rewrite using `[star_add, unimodUnramUnique_trFix, hfy]`. Establish `hfn : star (-(A i i + star c * c * A j j)) = -(A i i + star c * c * A j j)`. Rewrite using `[star_neg, hfy]`.

Break down `unimodUnramUnique_unitAdd hR₀ hfs hfn hsum with h1 | h1` into its components or cases. Conclude with `hn h1`. Conclude with `hy (IsUnit.neg_iff _ |>.1 h1)`. Take `⟨g₂, hg₂, hg₂i⟩` from `unimodUnramUnique_scale hR₀ hθ B hB i hBi`. Use `⟨g₁ * g₂, ?_, i, ?_⟩` and prove the remaining obligations.

Rewrite using `[det_mul, hg₁def, det_transvection_of_ne j i (Ne.symm hij), one_mul]`. Conclude with `hg₂`. Rewrite using `[← hg₂i, hBdef]`. Simplify using `[conjTranspose_mul, Matrix.mul_assoc]`.
-/
theorem unimodUnramUnique_diag [HenselianLocalRing R₀] [Finite (ResidueField R₀)]
    (hR₀ : ∀ x, x ∈ R₀ ↔ star x = x) {θ : R} (hθ : IsUnit (θ - star θ))
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] (A : Matrix ι ι R) (hA : Aᴴ = A)
    (hdet : IsUnit A.det) : ∃ g : Matrix ι ι R, IsUnit g.det ∧ ∃ i, (gᴴ * A * g) i i = 1 := by
  by_cases h : ∃ i, IsUnit (A i i)
  · obtain ⟨i, hi⟩ := h
    obtain ⟨g, hg, hgi⟩ := unimodUnramUnique_scale hR₀ hθ A hA i hi
    exact ⟨g, hg, i, hgi⟩
  · push Not at h
    obtain ⟨i, j, c, hij, hc⟩ := unimodUnramUnique_offdiag hR₀ hθ A hA hdet h
    set g₁ := transvection j i c with hg₁def
    set B := g₁ᴴ * A * g₁ with hBdef
    have hB : Bᴴ = B := by simp [hBdef, conjTranspose_mul, hA, Matrix.mul_assoc]
    have hBi : IsUnit (B i i) := by
      rw [hBdef, hg₁def, unimodUnramUnique_transv A i j c]
      have hji : A j i = star (A i j) := (unimodUnramUnique_hermFix A hA j i).symm
      have hfi := unimodUnramUnique_hermFix A hA i i
      have hfj := unimodUnramUnique_hermFix A hA j j
      have e : A i i + (c * A i j + star c * A j i) + star c * c * A j j
          = (c * A i j + star (c * A i j)) + (A i i + star c * c * A j j) := by
        rw [star_mul, ← hji]; ring
      rw [e]
      have hfy : star (A i i + star c * c * A j j) = A i i + star c * c * A j j := by
        simp only [star_add, star_mul, star_star, hfi, hfj]; ring
      have hy : ¬ IsUnit (A i i + star c * c * A j j) := by
        intro hy
        have hfz : star (star c * c * A j j) = star c * c * A j j := by
          simp only [star_mul, star_star, hfj]; ring
        rcases unimodUnramUnique_unitAdd hR₀ hfi hfz hy with h1 | h1
        · exact h i h1
        · exact h j (isUnit_of_mul_isUnit_right h1)
      by_contra hn
      have hsum : IsUnit ((c * A i j + star (c * A i j) + (A i i + star c * c * A j j))
          + -(A i i + star c * c * A j j)) := by rw [add_neg_cancel_right]; exact hc
      have hfs : star (c * A i j + star (c * A i j) + (A i i + star c * c * A j j))
          = c * A i j + star (c * A i j) + (A i i + star c * c * A j j) := by
        rw [star_add, unimodUnramUnique_trFix, hfy]
      have hfn : star (-(A i i + star c * c * A j j)) = -(A i i + star c * c * A j j) := by
        rw [star_neg, hfy]
      rcases unimodUnramUnique_unitAdd hR₀ hfs hfn hsum with h1 | h1
      · exact hn h1
      · exact hy (IsUnit.neg_iff _ |>.1 h1)
    obtain ⟨g₂, hg₂, hg₂i⟩ := unimodUnramUnique_scale hR₀ hθ B hB i hBi
    refine ⟨g₁ * g₂, ?_, i, ?_⟩
    · rw [det_mul, hg₁def, det_transvection_of_ne j i (Ne.symm hij), one_mul]; exact hg₂
    · rw [← hg₂i, hBdef]; simp [conjTranspose_mul, Matrix.mul_assoc]

/- English proof (translation)
Establish `hB11 : B.toBlocks₁₁ = 1`. Use extensionality with `a b`. Consider the cases of `a`. Consider the cases of `b`. Simplify `h1` using `[toBlocks₁₁]`.

Use `set P := B.toBlocks₁₂`. Use `set Q := B.toBlocks₂₁`. Use `set D₀ := B.toBlocks₂₂`. Establish `hBe : B = fromBlocks 1 P Q D₀` using `by rw [← hB11, fromBlocks_toBlocks]`. Rewrite `hB`, `hdet`, the goal using `[hBe]`.

Rewrite `hB` using `[fromBlocks_conjTranspose]`. Take `⟨-, hQP, hPQ, hD₀⟩` from `fromBlocks_inj.1 hB`. Rewrite `hdet` using `[det_fromBlocks_one₁₁]`. Establish `hD : (D₀ - Q * P)ᴴ = D₀ - Q * P`. Rewrite using `[conjTranspose_sub, conjTranspose_mul, hD₀, hPQ, hQP]`.

Take `⟨g', hg', hg'D⟩` from `IH _ hD hdet`. Use `⟨fromBlocks 1 (-(P * g')) 0 g', ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[det_fromBlocks_zero₂₁, det_one, one_mul]`. Conclude with `hg'`. Rewrite using `[fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply, ← fromBlocks_one]`.

Rewrite using `[← hg'D]`. Simplify using `only [conjTranspose_one, conjTranspose_zero, conjTranspose_neg, conjTranspose_mul, hPQ]`. Apply the tactic sequence `congr 1 <;> simp [Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, Matrix.neg_mul, Matrix.mul_neg] <;> abel`.
-/
theorem unimodUnramUnique_block {κ : Type} [Fintype κ] [DecidableEq κ]
    (IH : ∀ A : Matrix κ κ R, Aᴴ = A → IsUnit A.det →
      ∃ g : Matrix κ κ R, IsUnit g.det ∧ gᴴ * A * g = 1)
    (B : Matrix (Unit ⊕ κ) (Unit ⊕ κ) R) (hB : Bᴴ = B) (hdet : IsUnit B.det)
    (h1 : B (Sum.inl ()) (Sum.inl ()) = 1) :
    ∃ g : Matrix (Unit ⊕ κ) (Unit ⊕ κ) R, IsUnit g.det ∧ gᴴ * B * g = 1 := by
  have hB11 : B.toBlocks₁₁ = 1 := by
    ext a b; cases a; cases b; simpa [toBlocks₁₁] using h1
  set P := B.toBlocks₁₂
  set Q := B.toBlocks₂₁
  set D₀ := B.toBlocks₂₂
  have hBe : B = fromBlocks 1 P Q D₀ := by rw [← hB11, fromBlocks_toBlocks]
  rw [hBe] at hB hdet ⊢
  rw [fromBlocks_conjTranspose] at hB
  obtain ⟨-, hQP, hPQ, hD₀⟩ := fromBlocks_inj.1 hB
  rw [det_fromBlocks_one₁₁] at hdet
  have hD : (D₀ - Q * P)ᴴ = D₀ - Q * P := by
    rw [conjTranspose_sub, conjTranspose_mul, hD₀, hPQ, hQP]
  obtain ⟨g', hg', hg'D⟩ := IH _ hD hdet
  refine ⟨fromBlocks 1 (-(P * g')) 0 g', ?_, ?_⟩
  · rw [det_fromBlocks_zero₂₁, det_one, one_mul]; exact hg'
  · rw [fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply, ← fromBlocks_one]
    rw [← hg'D]
    simp only [conjTranspose_one, conjTranspose_zero, conjTranspose_neg, conjTranspose_mul, hPQ]
    congr 1 <;> simp [Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_assoc, Matrix.neg_mul, Matrix.mul_neg] <;> abel

/- English proof (translation)
Establish `hB : B = (B.submatrix e e).submatrix e.symm e.symm` using `by simp`. Rewrite using `[hB, conjTranspose_submatrix, submatrix_mul_equiv, submatrix_mul_equiv, hg, submatrix_one_equiv]`.
-/
theorem unimodUnramUnique_transport {κ ι : Type} [Fintype κ] [Fintype ι] [DecidableEq κ]
    [DecidableEq ι] (e : κ ≃ ι) (B : Matrix ι ι R) (g : Matrix κ κ R)
    (hg : gᴴ * B.submatrix e e * g = 1) :
    (g.submatrix e.symm e.symm)ᴴ * B * g.submatrix e.symm e.symm = 1 := by
  have hB : B = (B.submatrix e e).submatrix e.symm e.symm := by simp
  rw [hB, conjTranspose_submatrix, submatrix_mul_equiv, submatrix_mul_equiv, hg,
    submatrix_one_equiv]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Introduce `ι _ _ hc A _ _`. Establish `: IsEmpty ι` using `Fintype.card_eq_zero_iff.1 hc`. Conclude with `⟨1, by simp, by ext i; exact isEmptyElim i⟩`.

Consider the case `succ n ih`. Introduce `ι _ _ hc A hA hdet`. Establish `: Nonempty ι` using `Fintype.card_pos_iff.1 (by omega)`. Take `⟨g₁, hg₁, i, hi⟩` from `unimodUnramUnique_diag hR₀ hθ A hA hdet`. Use `set B := g₁ᴴ * A * g₁ with hBdef`.

Establish `hB : Bᴴ = B` using `by simp [hBdef, conjTranspose_mul, hA, Matrix.mul_assoc]`. Establish `hBdet : IsUnit B.det`. Rewrite using `[hBdef, det_mul, det_mul, det_conjTranspose]`. Conclude with `(hg₁.star.mul hdet).mul hg₁`. Set `κ` to `{j // j ≠ i}`.

Establish `hκ : Fintype.card κ = n`. Use `Fintype.card_subtype_compl (fun j => j = i)` as an intermediate fact. Simplify using `only [Fintype.card_subtype_eq, hc] at this`. Simplify `this` using `[κ]`. Set `e : Unit ⊕ κ ≃ ι` to `{ toFun := Sum.elim (fun _ => i) Subtype.val invFun := fun j => if h : j = i then Sum.inl () else Sum.inr ⟨j, h⟩ left_inv := by`.

Introduce and unpack `(⟨⟩ | ⟨j, hj⟩)`. Simplify using the standard rewrite rules. Simplify using `[hj]`. Apply the tactic sequence `right_inv := by intro j; by_cases h : j = i <;> simp [h] }`. Establish `hB' : (B.submatrix e e)ᴴ = B.submatrix e e` using `by rw [conjTranspose_submatrix, hB]`.

Establish `hB'det : IsUnit (B.submatrix e e).det` using `by rw [det_submatrix_equiv_self]; exact hBdet`. Establish `hB'1 : B.submatrix e e (Sum.inl ()) (Sum.inl ()) = 1` using `hi`. Take `⟨g₂, hg₂, hg₂e⟩` from `unimodUnramUnique_block (ih κ hκ) _ hB' hB'det hB'1`. Use `⟨g₁ * g₂.submatrix e.symm e.symm, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[det_mul, det_submatrix_equiv_self]`.

Conclude with `hg₁.mul hg₂`. Use `unimodUnramUnique_transport e B g₂ hg₂e` as an intermediate fact. Rewrite using `[← this, hBdef]`. Simplify using `[conjTranspose_mul, Matrix.mul_assoc]`.
-/
theorem unimodUnramUnique_main [HenselianLocalRing R₀] [Finite (ResidueField R₀)]
    (hR₀ : ∀ x, x ∈ R₀ ↔ star x = x) {θ : R} (hθ : IsUnit (θ - star θ)) (n : ℕ) :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι], Fintype.card ι = n →
      ∀ A : Matrix ι ι R, Aᴴ = A → IsUnit A.det →
        ∃ g : Matrix ι ι R, IsUnit g.det ∧ gᴴ * A * g = 1 := by
  induction n with
  | zero =>
    intro ι _ _ hc A _ _
    have : IsEmpty ι := Fintype.card_eq_zero_iff.1 hc
    exact ⟨1, by simp, by ext i; exact isEmptyElim i⟩
  | succ n ih =>
    intro ι _ _ hc A hA hdet
    have : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
    obtain ⟨g₁, hg₁, i, hi⟩ := unimodUnramUnique_diag hR₀ hθ A hA hdet
    set B := g₁ᴴ * A * g₁ with hBdef
    have hB : Bᴴ = B := by simp [hBdef, conjTranspose_mul, hA, Matrix.mul_assoc]
    have hBdet : IsUnit B.det := by
      rw [hBdef, det_mul, det_mul, det_conjTranspose]; exact (hg₁.star.mul hdet).mul hg₁
    let κ := {j // j ≠ i}
    have hκ : Fintype.card κ = n := by
      have := Fintype.card_subtype_compl (fun j => j = i)
      simp only [Fintype.card_subtype_eq, hc] at this
      simpa [κ] using this
    let e : Unit ⊕ κ ≃ ι :=
      { toFun := Sum.elim (fun _ => i) Subtype.val
        invFun := fun j => if h : j = i then Sum.inl () else Sum.inr ⟨j, h⟩
        left_inv := by
          rintro (⟨⟩ | ⟨j, hj⟩)
          · simp
          · simp [hj]
        right_inv := by intro j; by_cases h : j = i <;> simp [h] }
    have hB' : (B.submatrix e e)ᴴ = B.submatrix e e := by rw [conjTranspose_submatrix, hB]
    have hB'det : IsUnit (B.submatrix e e).det := by rw [det_submatrix_equiv_self]; exact hBdet
    have hB'1 : B.submatrix e e (Sum.inl ()) (Sum.inl ()) = 1 := hi
    obtain ⟨g₂, hg₂, hg₂e⟩ := unimodUnramUnique_block (ih κ hκ) _ hB' hB'det hB'1
    refine ⟨g₁ * g₂.submatrix e.symm e.symm, ?_, ?_⟩
    · rw [det_mul, det_submatrix_equiv_self]; exact hg₁.mul hg₂
    · have := unimodUnramUnique_transport e B g₂ hg₂e
      rw [← this, hBdef]; simp [conjTranspose_mul, Matrix.mul_assoc]

end Herm

/- English proof (translation)
Introduce `R _ σ hσ R₀ hR₀ _ _ hθ n A hA hdet`. Take `⟨θ, hθ⟩` from `hθ`. Set `_ : StarRing R` to `{ star := σ star_involutive := hσ star_mul := fun a b => by rw [map_mul, mul_comm] star_add := fun a b => map_add σ a b }`. Establish `hR₀' : ∀ x, x ∈ R₀ ↔ star x = x` using `hR₀`. Establish `hA' : Aᴴ = A` using `hA`.

Take `⟨g, hg, hgA⟩` from `unimodUnramUnique_main hR₀' hθ n (Fin n) (by simp) A hA' hdet`. Conclude with `⟨g, hg, hgA⟩`.
-/
theorem unimodUnramUnique : UnimodUnramUnique := by
  intro R _ σ hσ R₀ hR₀ _ _ hθ n A hA hdet
  obtain ⟨θ, hθ⟩ := hθ
  let _ : StarRing R :=
    { star := σ
      star_involutive := hσ
      star_mul := fun a b => by rw [map_mul, mul_comm]
      star_add := fun a b => map_add σ a b }
  have hR₀' : ∀ x, x ∈ R₀ ↔ star x = x := hR₀
  have hA' : Aᴴ = A := hA
  obtain ⟨g, hg, hgA⟩ := unimodUnramUnique_main hR₀' hθ n (Fin n) (by simp) A hA' hdet
  exact ⟨g, hg, hgA⟩

end Formalism.HermitianLatticesTheory
