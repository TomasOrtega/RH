import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsGaugeAll

open NumberField

namespace GlobalTheory.TraceOnto

variable {E : Type} [Field E] [NumberField E] [StarRing E]

/- English proof (translation)
Assemble the required witnesses or components as `⟨RingOfIntegers.mapRingHom (starRingEnd E) x, rfl⟩`.
-/
theorem exists_star (x : 𝓞 E) : ∃ t : 𝓞 E, (t : E) = star (x : E) :=
  ⟨RingOfIntegers.mapRingHom (starRingEnd E) x, rfl⟩

def normTraceIdeal (E : Type) [Field E] [NumberField E] [StarRing E] : Ideal (𝓞 E) where
  carrier := {x | ∃ w : 𝓞 E, (w : E) + star (w : E) = (x : E) * star (x : E)}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro a b ⟨u, hu⟩ ⟨v, hv⟩
    obtain ⟨t, ht⟩ := exists_star b
    refine ⟨u + v + a * t, ?_⟩
    push_cast
    simp only [ht, star_add, star_mul', star_star]
    linear_combination hu + hv
  smul_mem' := by
    rintro c a ⟨u, hu⟩
    obtain ⟨t, ht⟩ := exists_star c
    refine ⟨c * t * u, ?_⟩
    simp only [smul_eq_mul]
    push_cast
    simp only [ht, star_mul', star_star]
    linear_combination ((c : E) * star (c : E)) * hu

/- English proof (translation)
Introduce `E _ _ _ h`. Establish `htop : normTraceIdeal E = ⊤`. Assume the negation of the conclusion as `hne`. Take `⟨P, hP, hle⟩` from `Ideal.exists_le_maximal _ hne`. Take `⟨θ, t, ht, hn⟩` from `h.2.2 P hP`.

Apply `hn` to reduce the goal to its premises. Apply `hle` to reduce the goal to its premises. Establish `ht' : (t : E) = star (θ : E)` using `ht`. Use `⟨θ * t - θ * θ, ?_⟩` and prove the remaining obligations. Use `push_cast`.

Simplify using `only [ht', star_sub, star_mul', star_star]`. Expand and normalize the polynomial expressions, which then agree. Establish `h1 : (1 : 𝓞 E) ∈ normTraceIdeal E` using `htop ▸ Submodule.mem_top`. Take `⟨w, hw⟩` from `h1`. Conclude with `⟨w, by simpa using hw⟩`.
-/
theorem exists_trace_one : ∀ (E : Type) [Field E] [NumberField E] [StarRing E],
    Formalism.HermitianLatticesTheory.IsCMUnram E → ∃ w : 𝓞 E, (w : E) + star (w : E) = 1 := by
  intro E _ _ _ h
  have htop : normTraceIdeal E = ⊤ := by
    by_contra hne
    obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨θ, t, ht, hn⟩ := h.2.2 P hP
    apply hn
    apply hle
    have ht' : (t : E) = star (θ : E) := ht
    refine ⟨θ * t - θ * θ, ?_⟩
    push_cast
    simp only [ht', star_sub, star_mul', star_star]
    ring
  have h1 : (1 : 𝓞 E) ∈ normTraceIdeal E := htop ▸ Submodule.mem_top
  obtain ⟨w, hw⟩ := h1
  exact ⟨w, by simpa using hw⟩

end GlobalTheory.TraceOnto
