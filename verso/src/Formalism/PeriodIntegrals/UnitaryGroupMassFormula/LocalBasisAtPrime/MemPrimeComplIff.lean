import Mathlib
import Formalism.PeriodIntegrals.LocBasisPlace
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalBasisAtPrime.SpanClear

open NumberField

namespace LocBasisPlaceWork

variable {E : Type} [Field E] [NumberField E] {p : ℕ} [Fact p.Prime] (ρ : E →+* ℂ_[p])

/- English proof (translation)
Establish `hv` using `Valuation.integer.integers (NormedField.valuation (K := ℂ_[p]))`. Establish `h2 : IsIntegral (NormedField.valuation (K` using `ℂ_[p])).integer (ρ (a : E)) := IsIntegral.map_of_comp_eq (Int.castRingHom _) ρ (RingHom.ext_int _ _) (RingOfIntegers.isIntegral_coe a)`. Establish `h3` using `hv.mem_of_integral h2`. Establish `h4 : ‖ρ (a : E)‖₊ ≤ 1` using `h3`. Conclude with `h4` after adjusting the coercions.
-/
theorem norm_le_one (a : 𝓞 E) : ‖ρ (a : E)‖ ≤ 1 := by
  have hv := Valuation.integer.integers (NormedField.valuation (K := ℂ_[p]))
  have h2 : IsIntegral (NormedField.valuation (K := ℂ_[p])).integer (ρ (a : E)) :=
    IsIntegral.map_of_comp_eq (Int.castRingHom _) ρ (RingHom.ext_int _ _)
      (RingOfIntegers.isIntegral_coe a)
  have h3 := hv.mem_of_integral h2
  have h4 : ‖ρ (a : E)‖₊ ≤ 1 := h3
  exact_mod_cast h4

def plc : Ideal (𝓞 E) where
  carrier := {a | ‖ρ (a : E)‖ < 1}
  add_mem' {a b} ha hb := by
    show ‖ρ (algebraMap (𝓞 E) E (a + b))‖ < 1
    rw [map_add, map_add]
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)
  zero_mem' := by
    show ‖ρ ((0 : 𝓞 E) : E)‖ < 1
    simp
  smul_mem' c a ha := by
    show ‖ρ (algebraMap (𝓞 E) E (c * a))‖ < 1
    rw [map_mul, map_mul, norm_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) (norm_le_one ρ c)) ha

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_plc (a : 𝓞 E) : a ∈ plc ρ ↔ ‖ρ (a : E)‖ < 1 := Iff.rfl

instance plc_isPrime : (plc ρ).IsPrime where
  ne_top' h := by
    have h1 : (1 : 𝓞 E) ∈ plc ρ := h ▸ Submodule.mem_top
    rw [mem_plc] at h1
    simp at h1
  mem_or_mem' {a b} hab := by
    rw [mem_plc, mem_plc]
    have hab' : ‖ρ (algebraMap (𝓞 E) E (a * b))‖ < 1 := hab
    rw [map_mul, map_mul, norm_mul] at hab'
    by_contra h
    push Not at h
    have := mul_le_mul h.1 h.2 zero_le_one (le_trans zero_le_one h.1)
    change ‖ρ (algebraMap (𝓞 E) E a)‖ * ‖ρ (algebraMap (𝓞 E) E b)‖ < 1 at hab'
    linarith

/- English proof (translation)
Establish `h1` using `PadicComplex.norm_extends' p (p : ℚ_[p])`. Simplify using `only [map_natCast, Padic.norm_p] at h1`. Establish `h2 : ‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹`. Use `h1 using 2` and compare the differences between its conclusion and the goal. Use `first`.

Consider the case `rfl`. Consider the case `exact (map_natCast _ p).symm`. Consider the case `norm_cast`. Rewrite using `[h2]`. Conclude with `inv_lt_one_of_one_lt₀ (Nat.one_lt_cast.mpr (Fact.out : p.Prime).one_lt)`.
-/
theorem norm_p_lt_one : ‖(p : ℂ_[p])‖ < 1 := by
  have h1 := PadicComplex.norm_extends' p (p : ℚ_[p])
  simp only [map_natCast, Padic.norm_p] at h1
  have h2 : ‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹ := by
    convert h1 using 2
    first
    | rfl
    | exact (map_natCast _ p).symm
    | norm_cast
  rw [h2]
  exact inv_lt_one_of_one_lt₀ (Nat.one_lt_cast.mpr (Fact.out : p.Prime).one_lt)

/- English proof (translation)
Introduce `h`. Establish `hp : (p : 𝓞 E) ∈ plc ρ`. Rewrite using `[mem_plc]`. Simplify `norm_p_lt_one (p := p)` using `[map_natCast]`. Rewrite `hp` using `[h, Ideal.mem_bot]`.

Conclude with `(Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) hp`.
-/
theorem plc_ne_bot : plc ρ ≠ ⊥ := by
  intro h
  have hp : (p : 𝓞 E) ∈ plc ρ := by
    rw [mem_plc]
    simpa [map_natCast] using norm_p_lt_one (p := p)
  rw [h, Ideal.mem_bot] at hp
  exact (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) hp

/- English proof (translation)
Rewrite using `[Ideal.mem_primeCompl_iff, mem_plc, not_lt]`. Conclude with `⟨fun h => le_antisymm (norm_le_one ρ s) h, fun h => h.ge⟩`.
-/
theorem mem_primeCompl_iff (s : 𝓞 E) : s ∈ (plc ρ).primeCompl ↔ ‖ρ (s : E)‖ = 1 := by
  rw [Ideal.mem_primeCompl_iff, mem_plc, not_lt]
  exact ⟨fun h => le_antisymm (norm_le_one ρ s) h, fun h => h.ge⟩

end LocBasisPlaceWork
