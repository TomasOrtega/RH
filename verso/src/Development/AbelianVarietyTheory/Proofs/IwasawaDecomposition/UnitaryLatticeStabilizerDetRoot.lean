import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.Divisibility.Tuples
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.MuCardLeTwo
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsIntegralDetOfIsIntegral

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.L2.DIV

namespace GlobalTheory.Mem.StabDet

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem isIntegral_det {E : Type} [Field E] [NumberField E] {N : ℕ} (L : Submodule (𝓞 E) (Fin N → E))
    (hfg : L.FG) (hsp : Submodule.span E (L : Set (Fin N → E)) = ⊤) (γ : Matrix (Fin N) (Fin N) E)
    (hγ : ∀ v ∈ L, γ.mulVec v ∈ L) : IsIntegral ℤ γ.det :=
  _root_.UpperTheory.Reformulated.B.Ybf4.isIntegral_det L hfg hsp γ hγ

/- English proof (translation)
Equip the data with the indicated structure. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Supply the required witnesses or components.

A detailed English derivation is pending.
-/
theorem eq_pm_one_of_unitary {R : Ranks} (H : Formalism.BasicNotions.Host R) :
    letI := H.cmStar; ∀ z : H.E, z ∈ unitary H.E → IsIntegral ℤ z → ∃ m : ℕ, 0 < m ∧ z ^ m = 1 := by
  letI := H.cmStar
  intro z hu hz
  have := H.isCMField_hostE
  obtain ⟨n, hn, hp⟩ := NumberField.Embeddings.pow_eq_one_of_norm_eq_one H.E ℂ hz (fun φ => by
    have h1 : star z * z = 1 := hu.1
    have h2 : φ (star z) = starRingEnd ℂ (φ z) := IsCMField.complexEmbedding_complexConj H.E φ z
    have h3 := congrArg φ h1
    rw [map_mul, h2, map_one, Complex.conj_mul'] at h3
    have h4 : ‖φ z‖ ^ 2 = 1 := by exact_mod_cast h3
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h4)
  exact ⟨n, hn, hp⟩

end GlobalTheory.Mem.StabDet
