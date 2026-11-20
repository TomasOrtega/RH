import Mathlib
open IsLocalRing

namespace GlobalTheory

/- English proof (translation)
Use `set x : R ⧸ Ideal.span {T} := Ideal.Quotient.mk _ z`. Take `⟨k, y, hy⟩` from `IsArtinian.exists_pow_succ_smul_dvd x (1 : R ⧸ Ideal.span {T})`. Simplify using `only [smul_eq_mul, mul_one] at hy`. Take `⟨w, rfl⟩` from `Ideal.Quotient.mk_surjective y`. Establish `h0 : x * (1 - x * Ideal.Quotient.mk _ w) = 0`.

Apply `IsReduced.eq_zero` to reduce the goal to its premises. Use `⟨k + 1, ?_⟩` and prove the remaining obligations. Establish `: x ^ k * (1 - x * Ideal.Quotient.mk _ w) = 0`. Rewrite using `[mul_sub, mul_one, ← mul_assoc, ← pow_succ, hy, sub_self]`. Combine the equalities or inequalities in the displayed calculation.

Use `⟨1 - z * w, ?_, ?_⟩` and prove the remaining obligations. Introduce `hc`. Establish `: (1 : R) ∈ n`. Use `n.add_mem hc (n.mul_mem_right w hz)` as an intermediate fact. Simplify using `using this`.

Conclude with `(Ideal.IsPrime.ne_top ‹_›) ((Ideal.eq_top_iff_one _).2 this)`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem]`. Simplify `h0` using `[x, mul_comm]`.
-/
theorem exists_not_mem_mul_mem_span_of_reduced_artinian (R : Type) [CommRing R] (T : R)
    (hred : IsReduced (R ⧸ Ideal.span {T})) (hart : IsArtinianRing (R ⧸ Ideal.span {T}))
    (n : Ideal R) [n.IsPrime] (z : R) (hz : z ∈ n) :
    ∃ c : R, c ∉ n ∧ c * z ∈ Ideal.span {T} := by
  set x : R ⧸ Ideal.span {T} := Ideal.Quotient.mk _ z
  obtain ⟨k, y, hy⟩ := IsArtinian.exists_pow_succ_smul_dvd x (1 : R ⧸ Ideal.span {T})
  simp only [smul_eq_mul, mul_one] at hy
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective y
  have h0 : x * (1 - x * Ideal.Quotient.mk _ w) = 0 := by
    apply IsReduced.eq_zero
    refine ⟨k + 1, ?_⟩
    have : x ^ k * (1 - x * Ideal.Quotient.mk _ w) = 0 := by
      rw [mul_sub, mul_one, ← mul_assoc, ← pow_succ, hy, sub_self]
    calc (x * (1 - x * Ideal.Quotient.mk _ w)) ^ (k + 1)
        = (x ^ k * (1 - x * Ideal.Quotient.mk _ w)) * (x * (1 - x * Ideal.Quotient.mk _ w) ^ k) := by rw [mul_pow, pow_succ, pow_succ]; ring
      _ = 0 := by rw [this, zero_mul]
  refine ⟨1 - z * w, ?_, ?_⟩
  · intro hc
    have : (1 : R) ∈ n := by
      have := n.add_mem hc (n.mul_mem_right w hz)
      simpa using this
    exact (Ideal.IsPrime.ne_top ‹_›) ((Ideal.eq_top_iff_one _).2 this)
  · rw [← Ideal.Quotient.eq_zero_iff_mem]
    simpa [x, mul_comm] using h0

/- English proof (translation)
Introduce `R _ T hred hart n _ hT`. Rewrite using `[← Localization.AtPrime.map_eq_maximalIdeal]`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `z hz`.

Take `⟨c, hc, hcz⟩` from `exists_not_mem_mul_mem_span_of_reduced_artinian R T hred hart n z hz`. Take `⟨a, ha⟩` from `Ideal.mem_span_singleton'.1 hcz`. Establish `hu : IsUnit (algebraMap R (Localization.AtPrime n) c)` using `IsLocalization.map_units (Localization.AtPrime n) (⟨c, hc⟩ : n.primeCompl)`. Rewrite using `[Ideal.mem_comap]`. Establish `: algebraMap R (Localization.AtPrime n) z = (hu.unit⁻¹ : (Localization.AtPrime n)ˣ) * algebraMap R _ a * algebraMap R _ T`.

Rewrite using `[mul_assoc, ← map_mul, ha, map_mul, ← mul_assoc, IsUnit.val_inv_mul, one_mul]`. Rewrite using `[this]`. Conclude with `Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)`. Rewrite using `[Ideal.span_le, Set.singleton_subset_iff]`. Conclude with `Ideal.mem_map_of_mem _ hT`.
-/
theorem maximalIdeal_localization_eq_span_of_reduced_artinian :
    ∀ (R : Type) [CommRing R] (T : R), IsReduced (R ⧸ Ideal.span {T}) → IsArtinianRing (R ⧸ Ideal.span {T}) → ∀ (n : Ideal R) [n.IsPrime], T ∈ n → IsLocalRing.maximalIdeal (Localization.AtPrime n) = Ideal.span {algebraMap R (Localization.AtPrime n) T} := by
  intro R _ T hred hart n _ hT
  rw [← Localization.AtPrime.map_eq_maximalIdeal]
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro z hz
    obtain ⟨c, hc, hcz⟩ := exists_not_mem_mul_mem_span_of_reduced_artinian R T hred hart n z hz
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 hcz
    have hu : IsUnit (algebraMap R (Localization.AtPrime n) c) :=
      IsLocalization.map_units (Localization.AtPrime n) (⟨c, hc⟩ : n.primeCompl)
    rw [Ideal.mem_comap]
    have : algebraMap R (Localization.AtPrime n) z =
        (hu.unit⁻¹ : (Localization.AtPrime n)ˣ) * algebraMap R _ a * algebraMap R _ T := by
      rw [mul_assoc, ← map_mul, ha, map_mul, ← mul_assoc, IsUnit.val_inv_mul, one_mul]
    rw [this]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.mem_map_of_mem _ hT

end GlobalTheory
