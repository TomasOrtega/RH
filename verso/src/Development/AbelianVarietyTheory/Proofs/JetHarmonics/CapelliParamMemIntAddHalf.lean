import Mathlib
import Formalism.HermitianCurvature.StatementQ
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsHarishChandraParamOfTypeOfUnitaryW
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SupExistsOfInterlaced
open Formalism.FourierDecayAlt Formalism.QuantumDeterminants

namespace GlobalTheory

/- English proof (translation)
Introduce `k r Wp _ _ _ z π u hz hT hπ i hi`. Take `⟨u₀, h₀⟩` from `GlobalTheory.besType_hcParam k r Wp z π u hz hT hπ`. Establish `ha` using `(GlobalTheory.BesselMapCompare.isHCParam_of_isHCTypeW h₀).2`. Rewrite `hi` using `[Finset.mem_Icc]`. Establish `h1` using `GlobalTheory.SupNonzero.prod_eq hπ h₀ (-(u i : ℂ))`.

Establish `h2 : ∏ s : Fin k, (-(u i : ℂ) + (u (s.val + 1) : ℂ)) = 0`. Use `Finset.prod_eq_zero (Finset.mem_univ ⟨i - 1, by omega⟩) ?_` and prove the remaining obligations. Establish `: i - 1 + 1 = i` using `by omega`. Simplify using `[this]`. Rewrite `h1` using `[h2]`.

Take `⟨t, -, ht⟩` from `Finset.prod_eq_zero_iff.1 h1`. Establish `e : u i = u₀ t` using `by exact_mod_cast neg_add_eq_zero.1 ht`. Take `⟨m, hm⟩` from `ha t`. Conclude with `⟨m, by rw [e]; linarith⟩`.
-/
theorem capelliParam_mem_int_add_half : ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ), inWb k r z → 0 < Tz k r z → Q.IsType k r z π u → ∀ i ∈ Finset.Icc 1 k, ∃ m : ℤ, u i = (m : ℝ) + ((k : ℝ) - 1) / 2 := by
  intro k r Wp _ _ _ z π u hz hT hπ i hi
  obtain ⟨u₀, h₀⟩ := GlobalTheory.besType_hcParam k r Wp z π u hz hT hπ
  have ha := (GlobalTheory.BesselMapCompare.isHCParam_of_isHCTypeW h₀).2
  rw [Finset.mem_Icc] at hi
  have h1 := GlobalTheory.SupNonzero.prod_eq hπ h₀ (-(u i : ℂ))
  have h2 : ∏ s : Fin k, (-(u i : ℂ) + (u (s.val + 1) : ℂ)) = 0 := by
    refine Finset.prod_eq_zero (Finset.mem_univ ⟨i - 1, by omega⟩) ?_
    have : i - 1 + 1 = i := by omega
    simp [this]
  rw [h2] at h1
  obtain ⟨t, -, ht⟩ := Finset.prod_eq_zero_iff.1 h1
  have e : u i = u₀ t := by exact_mod_cast neg_add_eq_zero.1 ht
  obtain ⟨m, hm⟩ := ha t
  exact ⟨m, by rw [e]; linarith⟩

end GlobalTheory
