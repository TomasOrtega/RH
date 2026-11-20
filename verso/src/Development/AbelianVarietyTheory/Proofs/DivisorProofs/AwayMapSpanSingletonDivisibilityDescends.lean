import Mathlib

namespace GlobalTheory

/- English proof (translation)
Introduce `A C _ _ _ f g H b hb`. Take `⟨⟨a, ⟨_, k, rfl⟩⟩, rfl⟩` from `IsLocalization.mk'_surjective (Submonoid.powers f) b`. Rewrite `hb` using `[Ideal.mem_span_singleton']`. Take `⟨d, hd⟩` from `hb`. Take `⟨⟨c, ⟨_, m, rfl⟩⟩, rfl⟩` from `IsLocalization.mk'_surjective (Submonoid.powers (algebraMap A C f)) d`.

Simplify using `only [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_mk', IsLocalization.map_eq] at hd`. Rewrite `hd` using `[mul_comm, IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mk'_eq_iff_eq, IsLocalization.eq_iff_exists (Submonoid.powers (algebraMap A C f))]`. Take `⟨⟨_, n, rfl⟩, hn⟩` from `hd`. Simplify using `only [map_pow] at hn`. Establish `key : algebraMap A C (f ^ (n + m) * a) ∈ Ideal.span {algebraMap A C g}`.

Rewrite using `[Ideal.mem_span_singleton']`. Use `⟨algebraMap A C f ^ (n + k) * c, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, map_pow, pow_add, pow_add]`. Take the linear combination `hn`. Take `⟨e, he⟩` from `Ideal.mem_span_singleton'.mp (H _ key)`.

Rewrite using `[Ideal.mem_span_singleton']`. Use `⟨IsLocalization.mk' (Localization.Away f) e (⟨f ^ (n + m + k), n + m + k, rfl⟩ : Submonoid.powers f), ?_⟩` and prove the remaining obligations. Rewrite using `[mul_comm, IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mk'_eq_iff_eq]`. Use `congr 1`. Simplify using `only`.

Rewrite using `[pow_add, mul_comm g e, he]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem awayMap_descends_divisibility : ∀ (A C : Type) [CommRing A] [CommRing C] [Algebra A C] (f g : A), (∀ a : A, algebraMap A C a ∈ Ideal.span {algebraMap A C g} → a ∈ Ideal.span {g}) → ∀ b : Localization.Away f, Localization.awayMap (algebraMap A C) f b ∈ Ideal.span {Localization.awayMap (algebraMap A C) f (algebraMap A (Localization.Away f) g)} → b ∈ Ideal.span {algebraMap A (Localization.Away f) g} := by
  intro A C _ _ _ f g H b hb
  obtain ⟨⟨a, ⟨_, k, rfl⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers f) b
  rw [Ideal.mem_span_singleton'] at hb
  obtain ⟨d, hd⟩ := hb
  obtain ⟨⟨c, ⟨_, m, rfl⟩⟩, rfl⟩ :=
    IsLocalization.mk'_surjective (Submonoid.powers (algebraMap A C f)) d
  simp only [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_mk',
    IsLocalization.map_eq] at hd
  rw [mul_comm, IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mk'_eq_iff_eq,
    IsLocalization.eq_iff_exists (Submonoid.powers (algebraMap A C f))] at hd
  obtain ⟨⟨_, n, rfl⟩, hn⟩ := hd
  simp only [map_pow] at hn
  have key : algebraMap A C (f ^ (n + m) * a) ∈ Ideal.span {algebraMap A C g} := by
    rw [Ideal.mem_span_singleton']
    refine ⟨algebraMap A C f ^ (n + k) * c, ?_⟩
    rw [map_mul, map_pow, pow_add, pow_add]
    linear_combination hn
  obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.mp (H _ key)
  rw [Ideal.mem_span_singleton']
  refine ⟨IsLocalization.mk' (Localization.Away f) e
    (⟨f ^ (n + m + k), n + m + k, rfl⟩ : Submonoid.powers f), ?_⟩
  rw [mul_comm, IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mk'_eq_iff_eq]
  congr 1
  simp only
  rw [pow_add, mul_comm g e, he]
  ring

end GlobalTheory
