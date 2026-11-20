import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

noncomputable section

namespace SpecChart

variable {A : Type*} [CommRing A] (W : Ideal A) [W.IsPrime] (P : Ideal A)

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules.

Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the hypotheses and the conclusion using the stated equalities. A detailed English derivation is pending.
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
Equip the data with the indicated structure. Equip the data with the indicated structure. A detailed English derivation is pending.
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
