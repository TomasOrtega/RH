import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaneZeroInsertionLinearApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendByZeroMemSchA
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.PlaneEv

namespace GlobalTheory.ThK.PlaneEv.SchMap

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Extract witnesses or component facts from the available result. Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem ins0_eq_extend {R : Type} [Zero R] {n d d₁ : ℕ} (hd : d = d₁ + 2) (x : Fin n × Fin d₁ → R) :
    ins0 hd x = Function.extend ((idx hd).symm ∘ Sum.inl) x 0 := by
  funext k
  obtain ⟨s, rfl⟩ := (idx hd).symm.surjective k
  rcases s with p | p
  · rw [planeZeroInsertion_apply_inl]
    exact ((((idx hd).symm.injective).comp Sum.inl_injective).extend_apply x 0 p).symm
  · rw [planeZeroInsertion_apply_inr, Function.extend_apply']
    · rfl
    · rintro ⟨a, ha⟩
      simp only [Function.comp_apply, (idx hd).symm.injective.eq_iff] at ha
      exact Sum.inl_ne_inr ha

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Apply an available result and prove the equalities needed to match it to the conclusion. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities.
-/
theorem evA_mem_schA : ∀ (F : Type) [Field F] [NumberField F] (n d d₁ : ℕ) (hd : d = d₁ + 2), ∀ Φ ∈ schA F (Fin n × Fin d),
    evA F hd Φ ∈ schA F (Fin n × Fin d₁) := by
  intro F _ _ n d d₁ hd Φ hΦ
  have h := GlobalTheory.RestrSchA.mem_schA_comp_extend F ((idx hd).symm ∘ Sum.inl)
    (((idx hd).symm.injective).comp Sum.inl_injective) Φ hΦ
  convert h using 1
  funext y
  rw [evA_apply, ins0_eq_extend]

end GlobalTheory.ThK.PlaneEv.SchMap
