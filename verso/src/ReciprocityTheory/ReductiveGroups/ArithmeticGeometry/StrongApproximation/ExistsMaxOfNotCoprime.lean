import Mathlib

namespace ReciprocityTheory.ChartRestriction.G.SA

section
variable {K : Type*} [CommRing K] {σ : K →+* K} (hσ : ∀ x, σ (σ x) = x)
  (hfix : ∀ x, σ x = x → x ≠ 0 → IsUnit x)
include hσ hfix

/- English proof (translation)
Assume the negation of the conclusion as `h`. Establish `hfx : σ (z * σ z) = z * σ z` using `by rw [map_mul, hσ, mul_comm]`. Conclude with `hz (isUnit_of_mul_isUnit_left (hfix _ hfx h))`.
-/
theorem norm_zero_of_not_unit {z : K} (hz : ¬ IsUnit z) : z * σ z = 0 := by
  by_contra h
  have hfx : σ (z * σ z) = z * σ z := by rw [map_mul, hσ, mul_comm]
  exact hz (isUnit_of_mul_isUnit_left (hfix _ hfx h))

/- English proof (translation)
Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Take `⟨h1, h2', h3⟩` from `hcon`. Establish `e1` using `norm_zero_of_not_unit hσ hfix h1`. Establish `e2` using `norm_zero_of_not_unit hσ hfix h2'`.

Establish `e3` using `norm_zero_of_not_unit hσ hfix h3`. Simplify using `only [map_add, map_mul, hσδ, map_neg, map_one] at e2 e3`. Take `⟨a, b, hab⟩` from `hxy`. Establish `hab' : σ a * σ x + σ b * σ y = 1`. Use `congrArg σ hab` as an intermediate fact.

Simplify `this` using `only [map_add, map_mul, map_one]`. Establish `hyy0 : (2 * δ ^ 2) * (y * σ y) = 0` using `by linear_combination 2 * e1 - e2 - e3`. Establish `hyy : y * σ y = 0` using `((h2.mul (hδ.pow 2)).mul_right_eq_zero).mp hyy0`. Establish `hxy0 : (2 * δ) * (y * σ x - x * σ y) = 0` using `by linear_combination e2 - e3`. Establish `hxy' : y * σ x - x * σ y = 0` using `((h2.mul hδ).mul_right_eq_zero).mp hxy0`.

Establish `key : (a * σ b + b * σ a) * (x * σ y) = 1`. Take the linear combination `(σ a * σ x + σ b * σ y) * hab + hab' - σ a * b * hxy' - a * σ a * e1 - b * σ b * hyy`. Establish `hu : IsUnit (x * σ y)` using `isUnit_iff_exists_inv.mpr ⟨_, by rw [mul_comm]; exact key⟩`. Establish `hsq : (x * σ y) * (x * σ y) = 0`. Take the linear combination `(y * σ y) * e1 - (x * σ y) * hxy'`.

Establish `h0 : IsUnit (0 : K)`. Use `hu.mul hu` as an intermediate fact. Rewrite `this` using `[hsq]`. Then use the resulting hypothesis. Use `haveI := subsingleton_of_zero_eq_one (isUnit_zero_iff.mp h0)`. Conclude with `h1 (isUnit_of_subsingleton x)`.
-/
theorem gp [IsReduced K] (h2 : IsUnit (2 : K)) {δ : K} (hδ : IsUnit δ) (hσδ : σ δ = -δ) {x y : K}
    (hxy : IsCoprime x y) :
    IsUnit x ∨ IsUnit (x + δ * y) ∨ IsUnit (x + (-1) * δ * y) := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2', h3⟩ := hcon
  have e1 := norm_zero_of_not_unit hσ hfix h1
  have e2 := norm_zero_of_not_unit hσ hfix h2'
  have e3 := norm_zero_of_not_unit hσ hfix h3
  simp only [map_add, map_mul, hσδ, map_neg, map_one] at e2 e3
  obtain ⟨a, b, hab⟩ := hxy
  have hab' : σ a * σ x + σ b * σ y = 1 := by
    have := congrArg σ hab
    simpa only [map_add, map_mul, map_one] using this
  have hyy0 : (2 * δ ^ 2) * (y * σ y) = 0 := by linear_combination 2 * e1 - e2 - e3
  have hyy : y * σ y = 0 := ((h2.mul (hδ.pow 2)).mul_right_eq_zero).mp hyy0
  have hxy0 : (2 * δ) * (y * σ x - x * σ y) = 0 := by linear_combination e2 - e3
  have hxy' : y * σ x - x * σ y = 0 := ((h2.mul hδ).mul_right_eq_zero).mp hxy0
  have key : (a * σ b + b * σ a) * (x * σ y) = 1 := by
    linear_combination (σ a * σ x + σ b * σ y) * hab + hab' - σ a * b * hxy' - a * σ a * e1 -
      b * σ b * hyy
  have hu : IsUnit (x * σ y) := isUnit_iff_exists_inv.mpr ⟨_, by rw [mul_comm]; exact key⟩
  have hsq : (x * σ y) * (x * σ y) = 0 := by
    linear_combination (y * σ y) * e1 - (x * σ y) * hxy'
  have h0 : IsUnit (0 : K) := by
    have := hu.mul hu
    rwa [hsq] at this
  haveI := subsingleton_of_zero_eq_one (isUnit_zero_iff.mp h0)
  exact h1 (isUnit_of_subsingleton x)

end

/- English proof (translation)
Establish `hI : Ideal.span {a, b} ≠ ⊤`. Introduce `hI`. Establish `h1 : (1 : K) ∈ Ideal.span {a, b}`. Rewrite using `[hI]`. Conclude with `Submodule.mem_top`.

Take `⟨c, d, hcd⟩` from `Ideal.mem_span_pair.mp h1`. Conclude with `h ⟨c, d, hcd⟩`. Take `⟨m, hm, hIm⟩` from `Ideal.exists_le_maximal _ hI`. Conclude with `⟨m, hm, hIm (Ideal.subset_span (by simp)), hIm (Ideal.subset_span (by simp))⟩`.
-/
theorem exists_max_of_not_coprime {K : Type*} [CommRing K] {a b : K} (h : ¬ IsCoprime a b) :
    ∃ m : Ideal K, m.IsMaximal ∧ a ∈ m ∧ b ∈ m := by
  have hI : Ideal.span {a, b} ≠ ⊤ := by
    intro hI
    have h1 : (1 : K) ∈ Ideal.span {a, b} := by
      rw [hI]
      exact Submodule.mem_top
    obtain ⟨c, d, hcd⟩ := Ideal.mem_span_pair.mp h1
    exact h ⟨c, d, hcd⟩
  obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal _ hI
  exact ⟨m, hm, hIm (Ideal.subset_span (by simp)), hIm (Ideal.subset_span (by simp))⟩

/- English proof (translation)
Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Take `⟨h1, h1'⟩` from `hcon`. Take `⟨m0, hm0, ha0, hb0⟩` from `exists_max_of_not_coprime hnc`. Take `⟨m1, hm1, ha1, hb1⟩` from `exists_max_of_not_coprime h1`.

Take `⟨m2, hm2, ha2, hb2⟩` from `exists_max_of_not_coprime h1'`. Establish `key : ∀ m : Ideal K, m.IsMaximal → α ∈ m → β ∈ m → ω ∈ m → False`. Introduce `m hm ha hb hw`. Establish `hν' : ν ∈ m`. Rewrite using `[hdef]`.

Conclude with `m.add_mem (m.add_mem (m.mul_mem_right _ ha) (m.mul_mem_left _ hb)) hw`. Conclude with `hm.ne_top (Ideal.eq_top_of_isUnit_mem _ hν' hν)`. Establish `hA1 : α - ω ∈ m1`. Use `m1.sub_mem ha1 (m1.mul_mem_left c hb1)` as an intermediate fact. Simplify using `using this`.

Establish `hA2 : α + ω ∈ m2`. Use `m2.sub_mem ha2 (m2.mul_mem_left c hb2)` as an intermediate fact. Simplify using `using this`. Break down `hmax m0 m1 m2 hm0 hm1 hm2 with h | h | h` into its components or cases. Substitute `h` using the available equality.

Use `m0.sub_mem ha0 hA1` as an intermediate fact. Conclude with `key m0 hm0 ha0 hb0 (by simpa using this)`. Substitute `h` using the available equality. Use `m0.sub_mem hA2 ha0` as an intermediate fact. Conclude with `key m0 hm0 ha0 hb0 (by simpa using this)`.

Substitute `h` using the available equality. Establish `h2a : 2 * α ∈ m1`. Use `m1.add_mem hA1 hA2` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.

Take `⟨u, hu⟩` from `h2`. Establish `hα : α ∈ m1`. Use `m1.mul_mem_left (↑u⁻¹ : K) h2a` as an intermediate fact. Rewrite `this` using `[← mul_assoc, ← hu, Units.inv_mul, one_mul]`. Then use the resulting hypothesis. Use `m1.sub_mem hA2 hα` as an intermediate fact.

Conclude with `key m1 hm1 hα hb1 (by simpa using this)`.
-/
theorem stepA {K : Type*} [CommRing K] {σ : K →+* K}
    (hmax : ∀ m₀ m₁ m₂ : Ideal K, m₀.IsMaximal → m₁.IsMaximal → m₂.IsMaximal →
      m₀ = m₁ ∨ m₀ = m₂ ∨ m₁ = m₂)
    (h2 : IsUnit (2 : K)) {α β ω ν c : K} (hν : IsUnit ν) (hdef : ν = α * σ β + σ α * β + ω)
    (hnc : ¬ IsCoprime α β) :
    IsCoprime (α - ω + c * β) β ∨ IsCoprime (α + ω + c * β) β := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h1'⟩ := hcon
  obtain ⟨m0, hm0, ha0, hb0⟩ := exists_max_of_not_coprime hnc
  obtain ⟨m1, hm1, ha1, hb1⟩ := exists_max_of_not_coprime h1
  obtain ⟨m2, hm2, ha2, hb2⟩ := exists_max_of_not_coprime h1'
  have key : ∀ m : Ideal K, m.IsMaximal → α ∈ m → β ∈ m → ω ∈ m → False := by
    intro m hm ha hb hw
    have hν' : ν ∈ m := by
      rw [hdef]
      exact m.add_mem (m.add_mem (m.mul_mem_right _ ha) (m.mul_mem_left _ hb)) hw
    exact hm.ne_top (Ideal.eq_top_of_isUnit_mem _ hν' hν)
  have hA1 : α - ω ∈ m1 := by
    have := m1.sub_mem ha1 (m1.mul_mem_left c hb1)
    simpa using this
  have hA2 : α + ω ∈ m2 := by
    have := m2.sub_mem ha2 (m2.mul_mem_left c hb2)
    simpa using this
  rcases hmax m0 m1 m2 hm0 hm1 hm2 with h | h | h
  · subst h
    have := m0.sub_mem ha0 hA1
    exact key m0 hm0 ha0 hb0 (by simpa using this)
  · subst h
    have := m0.sub_mem hA2 ha0
    exact key m0 hm0 ha0 hb0 (by simpa using this)
  · subst h
    have h2a : 2 * α ∈ m1 := by
      have := m1.add_mem hA1 hA2
      convert this using 1
      ring
    obtain ⟨u, hu⟩ := h2
    have hα : α ∈ m1 := by
      have := m1.mul_mem_left (↑u⁻¹ : K) h2a
      rwa [← mul_assoc, ← hu, Units.inv_mul, one_mul] at this
    have := m1.sub_mem hA2 hα
    exact key m1 hm1 hα hb1 (by simpa using this)

end ReciprocityTheory.ChartRestriction.G.SA
