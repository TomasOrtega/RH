import Mathlib
import Formalism.LocalRingCardinality.DataSpaces
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsMemFractionalIdealPrimitiveLocalGeneratorAStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeMapComapOfLeConjMaximalCmDataStatement

open NumberField IsDedekindDomain

namespace GlobalTheory

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ hcm c hc N hN`. Take `⟨a, hac, hQ, hp⟩` from `GlobalTheory.T.exists_mem_fractionalIdeal_primitive_local_generator' F E hcm.deg2 c hc N hN`. Establish `ha : a ≠ 0`. Introduce and unpack `rfl`. Take `⟨p, hpm⟩` from `Ideal.exists_maximal (𝓞 F)`.

Conclude with `hp p hpm (Submodule.zero_mem _)`. Establish `hle : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) a * c⁻¹ ≤ 1`. Rewrite using `[← mul_inv_cancel₀ hc]`. Conclude with `mul_le_mul' (FractionalIdeal.spanSingleton_le_iff_mem.mpr hac) le_rfl`. Take `⟨P, hP⟩` from `FractionalIdeal.le_one_iff_exists_coeIdeal.mp hle`.

Establish `hPc : (P : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) * c = FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) a`. Rewrite using `[hP, mul_assoc, inv_mul_cancel₀ hc, mul_one]`. Establish `key : ∀ Q : Ideal (𝓞 E), P ≤ Q → a ∈ (Q : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) * c`. Introduce `Q hPQ`. Rewrite using `[← FractionalIdeal.spanSingleton_le_iff_mem, ← hPc]`.

Conclude with `mul_le_mul' ((FractionalIdeal.coeIdeal_le_coeIdeal E).mpr hPQ) le_rfl`. Establish `hσσ : ∀ x : 𝓞 E, RingOfIntegers.mapRingHom (starRingEnd E) (RingOfIntegers.mapRingHom (starRingEnd E) x) = x`. Introduce `x`. Use `ext`. Simplify using the standard rewrite rules.

Use `⟨P, ?_, ?_, ?_, a, hPc⟩` and prove the remaining obligations. Introduce and unpack `rfl`. Apply `ha` to reduce the goal to its premises. Rewrite `hPc` using `[FractionalIdeal.coeIdeal_bot, zero_mul, eq_comm, FractionalIdeal.spanSingleton_eq_zero_iff]`. Conclude with `hPc`.

Assume the negation of the conclusion as `htop`. Take `⟨Q, hQm, hPQ⟩` from `Ideal.exists_le_maximal _ htop`. Establish `h1 : P ≤ Q` using `le_sup_left.trans hPQ`. Establish `h2 : P ≤ Q.comap (RingOfIntegers.mapRingHom (starRingEnd E))`. Introduce `x hx`.

Apply `hPQ (Ideal.mem_sup_right _)` to reduce the goal to its premises. Use `show RingOfIntegers.mapRingHom (starRingEnd E) (RingOfIntegers.mapRingHom (starRingEnd E) x) ∈ P`. Rewrite using `[hσσ]`. Conclude with `hx`. Establish `h3` using `GlobalTheory.T.le_map_comap_of_le_conj_maximal_cmData F E hcm P Q hQm h1 h2`.

Establish `hpm : (Q.comap (algebraMap (𝓞 F) (𝓞 E))).IsMaximal` using `Ideal.isMaximal_comap_of_isIntegral_of_isMaximal Q`. Conclude with `hp _ hpm (key _ h3)`. Establish `htop : P ⊔ Ideal.span {N} = ⊤`. Assume the negation of the conclusion as `htop`. Take `⟨Q, hQm, hPQ⟩` from `Ideal.exists_le_maximal _ htop`.

Conclude with `hQ Q hQm (hPQ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self N))) (key Q (le_sup_left.trans hPQ))`. Establish `h1 : (1 : 𝓞 E) ∈ P ⊔ Ideal.span {N}` using `htop ▸ Submodule.mem_top`. Take `⟨y, hy, z, hz, hyz⟩` from `Submodule.mem_sup.mp h1`. Take `⟨t, rfl⟩` from `Ideal.mem_span_singleton'.mp hz`. Conclude with `⟨t, y, hy, by rw [add_comm]; exact hyz⟩`.
-/
theorem exists_ideal_coprime_conj_mul_eq_spanSingleton :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E],
      Formalism.BasicNotions.CMData F E → ∀ (c : FractionalIdeal (nonZeroDivisors (𝓞 E)) E), c ≠ 0 →
      ∀ N : 𝓞 E, N ≠ 0 → ∃ P : Ideal (𝓞 E), P ≠ ⊥ ∧
        P ⊔ P.comap (RingOfIntegers.mapRingHom (starRingEnd E)) = ⊤ ∧
        (∃ t : 𝓞 E, ∃ p ∈ P, t * N + p = 1) ∧
        ∃ α : E, (P : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) * c =
          FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) α := by
  intro F E _ _ _ _ _ _ hcm c hc N hN
  obtain ⟨a, hac, hQ, hp⟩ := GlobalTheory.T.exists_mem_fractionalIdeal_primitive_local_generator' F E hcm.deg2 c hc N hN

  have ha : a ≠ 0 := by
    rintro rfl
    obtain ⟨p, hpm⟩ := Ideal.exists_maximal (𝓞 F)
    exact hp p hpm (Submodule.zero_mem _)

  have hle : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) a * c⁻¹ ≤ 1 := by
    rw [← mul_inv_cancel₀ hc]
    exact mul_le_mul' (FractionalIdeal.spanSingleton_le_iff_mem.mpr hac) le_rfl
  obtain ⟨P, hP⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hle
  have hPc : (P : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) * c =
      FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) a := by
    rw [hP, mul_assoc, inv_mul_cancel₀ hc, mul_one]

  have key : ∀ Q : Ideal (𝓞 E), P ≤ Q → a ∈ (Q : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) * c := by
    intro Q hPQ
    rw [← FractionalIdeal.spanSingleton_le_iff_mem, ← hPc]
    exact mul_le_mul' ((FractionalIdeal.coeIdeal_le_coeIdeal E).mpr hPQ) le_rfl
  have hσσ : ∀ x : 𝓞 E, RingOfIntegers.mapRingHom (starRingEnd E)
      (RingOfIntegers.mapRingHom (starRingEnd E) x) = x := by
    intro x
    ext
    simp
  refine ⟨P, ?_, ?_, ?_, a, hPc⟩
  · rintro rfl
    apply ha
    rw [FractionalIdeal.coeIdeal_bot, zero_mul, eq_comm,
      FractionalIdeal.spanSingleton_eq_zero_iff] at hPc
    exact hPc
  · by_contra htop
    obtain ⟨Q, hQm, hPQ⟩ := Ideal.exists_le_maximal _ htop
    have h1 : P ≤ Q := le_sup_left.trans hPQ
    have h2 : P ≤ Q.comap (RingOfIntegers.mapRingHom (starRingEnd E)) := by
      intro x hx
      apply hPQ (Ideal.mem_sup_right _)
      show RingOfIntegers.mapRingHom (starRingEnd E) (RingOfIntegers.mapRingHom (starRingEnd E) x) ∈ P
      rw [hσσ]
      exact hx
    have h3 := GlobalTheory.T.le_map_comap_of_le_conj_maximal_cmData F E hcm P Q hQm h1 h2
    have hpm : (Q.comap (algebraMap (𝓞 F) (𝓞 E))).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal Q
    exact hp _ hpm (key _ h3)
  · have htop : P ⊔ Ideal.span {N} = ⊤ := by
      by_contra htop
      obtain ⟨Q, hQm, hPQ⟩ := Ideal.exists_le_maximal _ htop
      exact hQ Q hQm (hPQ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self N)))
        (key Q (le_sup_left.trans hPQ))
    have h1 : (1 : 𝓞 E) ∈ P ⊔ Ideal.span {N} := htop ▸ Submodule.mem_top
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp h1
    obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp hz
    exact ⟨t, y, hy, by rw [add_comm]; exact hyz⟩

end GlobalTheory
