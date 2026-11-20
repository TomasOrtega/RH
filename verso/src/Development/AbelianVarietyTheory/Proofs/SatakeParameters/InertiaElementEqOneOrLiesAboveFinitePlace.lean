import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModGDefs
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModGBasic
open NumberField IsDedekindDomain Neutral.HilbertClassField

namespace GlobalTheory

/- English proof (translation)
Introduce `E Ω _ _ _ _ _ A g hg`. Establish `hint : ∀ x : 𝓞 E, algebraMap E Ω (x : E) ∈ A` using `fun x => ReciprocityTheory.ChartRestriction.L1.mem_of_isIntegral A ((NumberField.RingOfIntegers.isIntegral_coe x).algebraMap)`. Set `φ : 𝓞 E →+* A` to `RingHom.codRestrict ((algebraMap E Ω).comp (algebraMap (𝓞 E) E)) A hint`. Set `I : Ideal (𝓞 E)` to `Ideal.comap φ (IsLocalRing.maximalIdeal A)`. Establish `hI : ∀ x : 𝓞 E, algebraMap E Ω (x : E) ∈ A.nonunits ↔ x ∈ I`.

Introduce `x`. Rewrite using `[ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal, Ideal.mem_comap]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨_, h⟩`. Conclude with `h`.

Introduce `h`. Conclude with `⟨hint x, h⟩`. Distinguish the cases in `hbot : I = ⊥`. Use `left`. Establish `hE : ∀ y : E, algebraMap E Ω y ∈ A`.

Introduce `y`. Take `⟨a, b, hb, rfl⟩` from `IsFractionRing.div_surjective (A := 𝓞 E) y`. Establish `hb0 : b ≠ 0` using `nonZeroDivisors.ne_zero hb`. Establish `hbn : algebraMap E Ω (algebraMap (𝓞 E) E b) ∉ A.nonunits`. Rewrite using `[show algebraMap (𝓞 E) E b = (b : E) from rfl, hI, hbot, Ideal.mem_bot]`.

Conclude with `hb0`. Establish `hbinv : (algebraMap E Ω (algebraMap (𝓞 E) E b))⁻¹ ∈ A`. Rewrite `hbn` using `[ValuationSubring.mem_nonunits_iff_or]`. Use `push_neg at hbn`. Conclude with `hbn.2`.

Rewrite using `[map_div₀, div_eq_mul_inv]`. Conclude with `mul_mem (hint a) hbinv`. Establish `hall : ∀ x : Ω, x ∈ A`. Introduce `x`. Establish `hx : IsIntegral E x` using `((IsAlgClosure.isAlgebraic (R := E) (K := Ω)).isAlgebraic x).isIntegral`.

Take `⟨p, hpm, hp⟩` from `hx`. Set `ψ : E →+* A` to `RingHom.codRestrict (algebraMap E Ω) A hE`. Establish `hcomp : (algebraMap A Ω).comp ψ = algebraMap E Ω` using `by ext; rfl`. Establish `h1 : IsIntegral A x` using `⟨p.map ψ, hpm.map ψ, by rw [Polynomial.eval₂_map, hcomp]; exact hp⟩`. Take `⟨y, hy⟩` from `(IsIntegrallyClosed.isIntegral_iff (R := A) (K := Ω)).mp h1`.

Rewrite using `[← hy]`. Conclude with `y.2`. Use extensionality with `x`. Establish `h` using `hg.2 x (hall x)`. Rewrite `h` using `[ValuationSubring.mem_nonunits_iff_or]`.

Break down `h with h | h` into its components or cases. Simplify `h` using `[sub_eq_zero]`. Conclude with `absurd (hall _) h`. Use `right`. Conclude with `⟨⟨I, Ideal.IsPrime.comap φ, hbot⟩, fun x => hI x⟩`.
-/
theorem inertiaEl_eq_one_or_liesAbove : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (A : ValuationSubring Ω) (g : Ω ≃ₐ[E] Ω),
    ReciprocityTheory.ChartRestriction.L1.InertiaEl A g → g = 1 ∨ ∃ v : HeightOneSpectrum (𝓞 E), LiesAbove A v := by
  intro E Ω _ _ _ _ _ A g hg
  have hint : ∀ x : 𝓞 E, algebraMap E Ω (x : E) ∈ A := fun x =>
    ReciprocityTheory.ChartRestriction.L1.mem_of_isIntegral A ((NumberField.RingOfIntegers.isIntegral_coe x).algebraMap)
  let φ : 𝓞 E →+* A := RingHom.codRestrict ((algebraMap E Ω).comp (algebraMap (𝓞 E) E)) A hint
  let I : Ideal (𝓞 E) := Ideal.comap φ (IsLocalRing.maximalIdeal A)
  have hI : ∀ x : 𝓞 E, algebraMap E Ω (x : E) ∈ A.nonunits ↔ x ∈ I := by
    intro x
    rw [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal, Ideal.mem_comap]
    constructor
    · rintro ⟨_, h⟩; exact h
    · intro h; exact ⟨hint x, h⟩
  by_cases hbot : I = ⊥
  · left
    have hE : ∀ y : E, algebraMap E Ω y ∈ A := by
      intro y
      obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) y
      have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
      have hbn : algebraMap E Ω (algebraMap (𝓞 E) E b) ∉ A.nonunits := by
        rw [show algebraMap (𝓞 E) E b = (b : E) from rfl, hI, hbot, Ideal.mem_bot]; exact hb0
      have hbinv : (algebraMap E Ω (algebraMap (𝓞 E) E b))⁻¹ ∈ A := by
        rw [ValuationSubring.mem_nonunits_iff_or] at hbn
        push_neg at hbn; exact hbn.2
      rw [map_div₀, div_eq_mul_inv]
      exact mul_mem (hint a) hbinv
    have hall : ∀ x : Ω, x ∈ A := by
      intro x
      have hx : IsIntegral E x := ((IsAlgClosure.isAlgebraic (R := E) (K := Ω)).isAlgebraic x).isIntegral
      obtain ⟨p, hpm, hp⟩ := hx
      let ψ : E →+* A := RingHom.codRestrict (algebraMap E Ω) A hE
      have hcomp : (algebraMap A Ω).comp ψ = algebraMap E Ω := by ext; rfl
      have h1 : IsIntegral A x := ⟨p.map ψ, hpm.map ψ, by rw [Polynomial.eval₂_map, hcomp]; exact hp⟩
      obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := Ω)).mp h1
      rw [← hy]; exact y.2
    ext x
    have h := hg.2 x (hall x)
    rw [ValuationSubring.mem_nonunits_iff_or] at h
    rcases h with h | h
    · simpa [sub_eq_zero] using h
    · exact absurd (hall _) h
  · right
    exact ⟨⟨I, Ideal.IsPrime.comap φ, hbot⟩, fun x => hI x⟩

end GlobalTheory
