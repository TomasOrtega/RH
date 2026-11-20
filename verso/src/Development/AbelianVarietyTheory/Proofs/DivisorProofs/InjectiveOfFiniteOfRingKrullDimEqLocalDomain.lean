import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.Integral
open IsLocalRing

namespace GlobalTheory

open IsLocalRing in

/- English proof (translation)
Introduce `B R _ _ _ _ _ _ ψ hψ hdim`. Use `letI : Algebra B R := ψ.toAlgebra`. Use `haveI : Module.Finite B R := hψ`. Establish `hlt : ringKrullDim B < ⊤` using `ringKrullDim_lt_top`. Establish `hne : ringKrullDim B ≠ ⊥` using `fun h => (WithBot.bot_lt_coe (0 : ℕ∞)).not_ge (h ▸ (ringKrullDim_nonneg_of_nontrivial (R := B)))`.

Take `⟨m, hm⟩` from `WithBot.ne_bot_iff_exists.mp hne`. Choose the witnesses or unpack the hypotheses as in `⟨n, rfl⟩ : ∃ n : ℕ, (n : ℕ∞) = m := by`. Use `ENat.ne_top_iff_exists.mp ?_` and prove the remaining obligations. Introduce and unpack `rfl`. Conclude with `hlt.ne hm.symm`.

Conclude with `_root_.GlobalTheory.CohenStructure.injective_of_ringKrullDim_eq (A := B) (S := R) hm.symm (hdim.trans hm.symm)`.
-/
theorem _root_.GlobalTheory.injective_of_finite_of_ringKrullDim_eq_of_local_domain :
    ∀ (B R : Type) [CommRing B] [IsDomain B] [IsLocalRing B] [IsNoetherianRing B] [CommRing R]
      [IsLocalRing R] (ψ : B →+* R), ψ.Finite → ringKrullDim R = ringKrullDim B →
      Function.Injective ψ := by
  intro B R _ _ _ _ _ _ ψ hψ hdim
  letI : Algebra B R := ψ.toAlgebra
  haveI : Module.Finite B R := hψ
  have hlt : ringKrullDim B < ⊤ := ringKrullDim_lt_top
  have hne : ringKrullDim B ≠ ⊥ := fun h =>
    (WithBot.bot_lt_coe (0 : ℕ∞)).not_ge (h ▸ (ringKrullDim_nonneg_of_nontrivial (R := B)))
  obtain ⟨m, hm⟩ := WithBot.ne_bot_iff_exists.mp hne
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, (n : ℕ∞) = m := by
    refine ENat.ne_top_iff_exists.mp ?_
    rintro rfl
    exact hlt.ne hm.symm
  exact _root_.GlobalTheory.CohenStructure.injective_of_ringKrullDim_eq (A := B) (S := R) hm.symm
    (hdim.trans hm.symm)

end GlobalTheory
