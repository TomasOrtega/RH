import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsLocalCoeffRing
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u

/- English proof (translation)
Introduce `R _ P U _ f g`. Use `set S := Localization.AtPrime U`. Use `set I := P.map (algebraMap R S)`. Establish `hφ : ∀ x : R, localQuotMap P U x = Ideal.Quotient.mk I (algebraMap R S x)` using `fun _ => rfl`. Apply `le_antisymm` to reduce the goal to its premises.

Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `x hx`. Rewrite using `[Ideal.mem_comap, Submodule.mem_colon_singleton, smul_eq_mul]`. Rewrite `hx` using `[Submodule.mem_colon_singleton, smul_eq_mul]`. Take `⟨p, hp, z, hz, hpz⟩` from `Submodule.mem_sup.mp hx`.

Take `⟨a, rfl⟩` from `Ideal.mem_span_singleton'.mp hz`. Establish `hp0 : localQuotMap P U p = 0`. Rewrite using `[hφ, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `Ideal.mem_map_of_mem _ hp`. Use `Ideal.mem_span_singleton'.mpr ⟨localQuotMap P U a, ?_⟩` and prove the remaining obligations.

Rewrite using `[← map_mul, ← map_mul, ← hpz, map_add, hp0, zero_add, map_mul]`. Introduce `y hy`. Rewrite `hy` using `[Submodule.mem_colon_singleton, smul_eq_mul]`. Take `⟨b, hb⟩` from `Ideal.mem_span_singleton'.mp hy`. Take `⟨y0, rfl⟩` from `Ideal.Quotient.mk_surjective y`.

Take `⟨b0, rfl⟩` from `Ideal.Quotient.mk_surjective b`. Take `⟨⟨r, t⟩, rfl⟩` from `IsLocalization.mk'_surjective U.primeCompl y0`. Take `⟨⟨r', t'⟩, rfl⟩` from `IsLocalization.mk'_surjective U.primeCompl b0`. Simplify using `only [hφ] at hb`. Establish `hI` using `Ideal.Quotient.eq.mp hb`.

Establish `e1` using `IsLocalization.mk'_spec S r t`. Establish `e2` using `IsLocalization.mk'_spec S r' t'`. Establish `hw : algebraMap R S ((t : R) * r' * f - (t' : R) * r * g) ∈ I`. Use `I.mul_mem_left (algebraMap R S ((t : R) * t')) hI` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Simplify using `only [map_mul, map_sub]`. Take the linear combination `(algebraMap R S t' * algebraMap R S g) * e1 - (algebraMap R S t * algebraMap R S f) * e2`. Take `⟨⟨p, s⟩, hps⟩` from `(IsLocalization.mem_map_algebraMap_iff U.primeCompl S).mp hw`. Rewrite `hps` using `[← map_mul]`. Take `⟨c, hc⟩` from `(IsLocalization.eq_iff_exists U.primeCompl S).mp hps`.

Establish `hx : (c : R) * s * t' * r ∈ (P ⊔ Ideal.span {f}).colon {g}`. Rewrite using `[Submodule.mem_colon_singleton, smul_eq_mul]`. Use `Submodule.mem_sup.mpr ⟨-((c : R) * p), P.neg_mem (P.mul_mem_left _ p.2), (c : R) * s * t * r' * f, Ideal.mem_span_singleton'.mpr ⟨_, rfl⟩, ?_⟩` and prove the remaining obligations. Take the linear combination `hc`. Establish `hy' : Ideal.Quotient.mk I (IsLocalization.mk' S r t) = localQuotMap P U ((c : R) * s * t' * r) * Ideal.Quotient.mk I (IsLocalization.mk' S (1 : R) (c * s * t' * t))`.

Rewrite using `[hφ, ← map_mul, IsLocalization.mul_mk'_eq_mk'_of_mul, mul_one]`. Use `congr 1`. Rewrite using `[IsLocalization.mk'_eq_iff_eq]`. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hy']`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hx)`.
-/
theorem LocalQuotColon.proof : LocalQuotColon.Statement.{u} := by
  intro R _ P U _ f g
  set S := Localization.AtPrime U
  set I := P.map (algebraMap R S)
  have hφ : ∀ x : R, localQuotMap P U x = Ideal.Quotient.mk I (algebraMap R S x) := fun _ => rfl
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, Submodule.mem_colon_singleton, smul_eq_mul]
    rw [Submodule.mem_colon_singleton, smul_eq_mul] at hx
    obtain ⟨p, hp, z, hz, hpz⟩ := Submodule.mem_sup.mp hx
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hz
    have hp0 : localQuotMap P U p = 0 := by
      rw [hφ, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_map_of_mem _ hp
    refine Ideal.mem_span_singleton'.mpr ⟨localQuotMap P U a, ?_⟩
    rw [← map_mul, ← map_mul, ← hpz, map_add, hp0, zero_add, map_mul]
  · intro y hy
    rw [Submodule.mem_colon_singleton, smul_eq_mul] at hy
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hy
    obtain ⟨y0, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨b0, rfl⟩ := Ideal.Quotient.mk_surjective b
    obtain ⟨⟨r, t⟩, rfl⟩ := IsLocalization.mk'_surjective U.primeCompl y0
    obtain ⟨⟨r', t'⟩, rfl⟩ := IsLocalization.mk'_surjective U.primeCompl b0
    simp only [hφ] at hb
    have hI := Ideal.Quotient.eq.mp hb
    have e1 := IsLocalization.mk'_spec S r t
    have e2 := IsLocalization.mk'_spec S r' t'
    have hw : algebraMap R S ((t : R) * r' * f - (t' : R) * r * g) ∈ I := by
      have := I.mul_mem_left (algebraMap R S ((t : R) * t')) hI
      convert this using 1
      simp only [map_mul, map_sub]
      linear_combination (algebraMap R S t' * algebraMap R S g) * e1 -
        (algebraMap R S t * algebraMap R S f) * e2
    obtain ⟨⟨p, s⟩, hps⟩ := (IsLocalization.mem_map_algebraMap_iff U.primeCompl S).mp hw
    rw [← map_mul] at hps
    obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists U.primeCompl S).mp hps
    have hx : (c : R) * s * t' * r ∈ (P ⊔ Ideal.span {f}).colon {g} := by
      rw [Submodule.mem_colon_singleton, smul_eq_mul]
      refine Submodule.mem_sup.mpr ⟨-((c : R) * p), P.neg_mem (P.mul_mem_left _ p.2),
        (c : R) * s * t * r' * f, Ideal.mem_span_singleton'.mpr ⟨_, rfl⟩, ?_⟩
      linear_combination hc
    have hy' : Ideal.Quotient.mk I (IsLocalization.mk' S r t) =
        localQuotMap P U ((c : R) * s * t' * r) *
          Ideal.Quotient.mk I (IsLocalization.mk' S (1 : R) (c * s * t' * t)) := by
      rw [hφ, ← map_mul, IsLocalization.mul_mk'_eq_mk'_of_mul, mul_one]
      congr 1
      rw [IsLocalization.mk'_eq_iff_eq]
      congr 1
      push_cast
      ring
    rw [hy']
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hx)

end GroundTheory.Heights₂.Heights.NumbersDVR
