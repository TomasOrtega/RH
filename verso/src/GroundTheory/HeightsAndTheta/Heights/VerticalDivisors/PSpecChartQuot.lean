import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

noncomputable section

namespace SpecChart

variable {A : Type*} [CommRing A] (W : Ideal A) [W.IsPrime] (P : Ideal A)

/- English proof (translation)
Rewrite using `[_root_.isLocalization_iff]`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨_, s, hs, rfl⟩`. Rewrite using `[Ideal.Quotient.algebraMap_quotient_map_quotient]`. Conclude with `(IsLocalization.map_units (Localization.AtPrime W) (⟨s, hs⟩ : W.primeCompl)).map _`.

Introduce `z`. Take `⟨x, rfl⟩` from `Ideal.Quotient.mk_surjective z`. Take `⟨⟨a, s⟩, rfl⟩` from `IsLocalization.mk'_surjective W.primeCompl x`. Use `⟨⟨Ideal.Quotient.mk P a, ⟨_, s.1, s.2, rfl⟩⟩, ?_⟩` and prove the remaining obligations. Simplify using `only [Ideal.Quotient.algebraMap_quotient_map_quotient, ← map_mul, IsLocalization.mk'_spec]`.

Introduce `x y h`. Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Take `⟨b, rfl⟩` from `Ideal.Quotient.mk_surjective y`. Rewrite `h` using `[Ideal.Quotient.algebraMap_quotient_map_quotient, Ideal.Quotient.algebraMap_quotient_map_quotient, Ideal.Quotient.eq, ← map_sub, IsLocalization.mem_map_algebraMap_iff W.primeCompl]`. Take `⟨⟨⟨p, hp⟩, ⟨t, ht⟩⟩, h⟩` from `h`.

Simplify using `only at h`. Rewrite `h` using `[← map_mul, IsLocalization.eq_iff_exists W.primeCompl]`. Take `⟨⟨u, hu⟩, h⟩` from `h`. Use `⟨⟨Ideal.Quotient.mk P (u * t), ⟨u * t, W.primeCompl.mul_mem hu ht, rfl⟩⟩, ?_⟩` and prove the remaining obligations. Simplify using `only`.

Rewrite using `[← map_mul, ← map_mul, Ideal.Quotient.eq, ← mul_sub]`. Establish `h' : u * ((a - b) * t) = u * p` using `h`. Rewrite using `[show u * t * (a - b) = u * ((a - b) * t) by ring, h']`. Conclude with `P.mul_mem_left _ hp`.
-/
theorem isLocalization_quot :
    IsLocalization (W.primeCompl.map (Ideal.Quotient.mk P))
      (Localization.AtPrime W ⧸ P.map (algebraMap A (Localization.AtPrime W))) := by
  rw [_root_.isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, s, hs, rfl⟩
    rw [Ideal.Quotient.algebraMap_quotient_map_quotient]
    exact (IsLocalization.map_units (Localization.AtPrime W) (⟨s, hs⟩ : W.primeCompl)).map _
  · intro z
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective W.primeCompl x
    refine ⟨⟨Ideal.Quotient.mk P a, ⟨_, s.1, s.2, rfl⟩⟩, ?_⟩
    simp only [Ideal.Quotient.algebraMap_quotient_map_quotient, ← map_mul, IsLocalization.mk'_spec]
  · intro x y h
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [Ideal.Quotient.algebraMap_quotient_map_quotient, Ideal.Quotient.algebraMap_quotient_map_quotient,
      Ideal.Quotient.eq, ← map_sub, IsLocalization.mem_map_algebraMap_iff W.primeCompl] at h
    obtain ⟨⟨⟨p, hp⟩, ⟨t, ht⟩⟩, h⟩ := h
    simp only at h
    rw [← map_mul, IsLocalization.eq_iff_exists W.primeCompl] at h
    obtain ⟨⟨u, hu⟩, h⟩ := h
    refine ⟨⟨Ideal.Quotient.mk P (u * t), ⟨u * t, W.primeCompl.mul_mem hu ht, rfl⟩⟩, ?_⟩
    simp only
    rw [← map_mul, ← map_mul, Ideal.Quotient.eq, ← mul_sub]
    have h' : u * ((a - b) * t) = u * p := h
    rw [show u * t * (a - b) = u * ((a - b) * t) by ring, h']
    exact P.mul_mem_left _ hp

/- English proof (translation)
Use `letI := g.toAlgebra`. Use `letI : Algebra R T := (g.comp (algebraMap R S)).toAlgebra`. Use `haveI : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq fun _ => rfl`. Conclude with `(Module.flat_iff_of_isLocalization S M T).mpr hg`.
-/
theorem flat_of_isLocalization_comp {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S] (g : S →+* T) (hg : (g.comp (algebraMap R S)).Flat) :
    g.Flat := by
  letI := g.toAlgebra
  letI : Algebra R T := (g.comp (algebraMap R S)).toAlgebra
  haveI : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact (Module.flat_iff_of_isLocalization S M T).mpr hg

end SpecChart

end

end GroundTheory.Heights₂.Heights.Vertical
