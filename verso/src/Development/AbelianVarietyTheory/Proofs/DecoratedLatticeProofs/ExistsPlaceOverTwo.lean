import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSplitIdempotentsOfRelTraceOneModTwo

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta IsDedekindDomain NumberField

noncomputable section

namespace GlobalTheory.LocMod.Inhab

/- English proof (translation)
Establish `h2 : ¬ IsUnit (2 : 𝓞 F)`. Introduce `hu`. Establish `hn` using `hu.map (Algebra.norm ℤ (S := 𝓞 F))`. Rewrite `hn` using `[show (2 : 𝓞 F) = algebraMap ℤ (𝓞 F) 2 by simp, Algebra.norm_algebraMap]`. Establish `hr : 0 < Module.finrank ℤ (𝓞 F)` using `Module.finrank_pos`.

Establish `hge : (2 : ℤ) ≤ 2 ^ Module.finrank ℤ (𝓞 F)`. Combine the equalities or inequalities in the displayed calculation. Apply the tactic sequence `rcases Int.isUnit_iff.mp hn with h | h <;> omega`. Take `⟨M, hM, h2M⟩` from `Ideal.exists_le_maximal (Ideal.span {(2 : 𝓞 F)}) (by rwa [Ne, Ideal.span_singleton_eq_top])`. Establish `h2mem : (2 : 𝓞 F) ∈ M` using `h2M (Ideal.mem_span_singleton_self 2)`.

Establish `hM0 : M ≠ ⊥`. Introduce and unpack `rfl`. Establish `h0 : (2 : 𝓞 F) = 0` using `(Submodule.mem_bot _).mp h2mem`. Establish `h0' : (2 : F) = 0`. Use `congrArg (algebraMap (𝓞 F) F) h0` as an intermediate fact.

Rewrite `this` using `[map_ofNat, map_zero]`. Then use the resulting hypothesis. Conclude with `two_ne_zero h0'`. Conclude with `⟨⟨M, hM.isPrime, hM0⟩, h2mem⟩`.
-/
theorem exists_place_over_two (F : Type) [Field F] [NumberField F] :
    ∃ v : HeightOneSpectrum (𝓞 F), (2 : 𝓞 F) ∈ v.asIdeal := by
  have h2 : ¬ IsUnit (2 : 𝓞 F) := by
    intro hu
    have hn := hu.map (Algebra.norm ℤ (S := 𝓞 F))
    rw [show (2 : 𝓞 F) = algebraMap ℤ (𝓞 F) 2 by simp, Algebra.norm_algebraMap] at hn
    have hr : 0 < Module.finrank ℤ (𝓞 F) := Module.finrank_pos
    have hge : (2 : ℤ) ≤ 2 ^ Module.finrank ℤ (𝓞 F) := by
      calc (2 : ℤ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ Module.finrank ℤ (𝓞 F) := pow_le_pow_right₀ (by norm_num) hr
    rcases Int.isUnit_iff.mp hn with h | h <;> omega
  obtain ⟨M, hM, h2M⟩ := Ideal.exists_le_maximal (Ideal.span {(2 : 𝓞 F)})
    (by rwa [Ne, Ideal.span_singleton_eq_top])
  have h2mem : (2 : 𝓞 F) ∈ M := h2M (Ideal.mem_span_singleton_self 2)
  have hM0 : M ≠ ⊥ := by
    rintro rfl
    have h0 : (2 : 𝓞 F) = 0 := (Submodule.mem_bot _).mp h2mem
    have h0' : (2 : F) = 0 := by
      have := congrArg (algebraMap (𝓞 F) F) h0
      rwa [map_ofNat, map_zero] at this
    exact two_ne_zero h0'
  exact ⟨⟨M, hM.isPrime, hM0⟩, h2mem⟩

/- English proof (translation)
Introduce `D`. Take `⟨v, hv⟩` from `exists_place_over_two D.host.F`. Take `⟨e, he1, he2, he3, -⟩` from `GlobalTheory.SplitIdem.exists_split_idempotent D v hv`. Conclude with `⟨e, (GlobalTheory.IdemModTwo.isSplitIdem_iff e).2 ⟨v, he1, he2, he3⟩⟩`.
-/
theorem exists_isSplitIdem : ∀ D : D7, ∃ e : Formalism.L2.Theta.AE D, IsSplitIdem D e := by
  intro D
  obtain ⟨v, hv⟩ := exists_place_over_two D.host.F
  obtain ⟨e, he1, he2, he3, -⟩ := GlobalTheory.SplitIdem.exists_split_idempotent D v hv
  exact ⟨e, (GlobalTheory.IdemModTwo.isSplitIdem_iff e).2 ⟨v, he1, he2, he3⟩⟩

end GlobalTheory.LocMod.Inhab
