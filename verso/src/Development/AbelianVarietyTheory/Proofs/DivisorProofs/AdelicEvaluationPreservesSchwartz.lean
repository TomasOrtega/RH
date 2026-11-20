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
Use function extensionality and compare the values at `k`. Take `⟨s, rfl⟩` from `(idx hd).symm.surjective k`. Break down `s with p | p` into its components or cases. Rewrite using `[planeZeroInsertion_apply_inl]`. Conclude with `((((idx hd).symm.injective).comp Sum.inl_injective).extend_apply x 0 p).symm`.

Rewrite using `[planeZeroInsertion_apply_inr, Function.extend_apply']`. Both sides reduce to the same expression. Introduce and unpack `⟨a, ha⟩`. Simplify using `only [Function.comp_apply, (idx hd).symm.injective.eq_iff] at ha`. Conclude with `Sum.inl_ne_inr ha`.
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
Introduce `F _ _ n d d₁ hd Φ hΦ`. Establish `h` using `GlobalTheory.RestrSchA.mem_schA_comp_extend F ((idx hd).symm ∘ Sum.inl) (((idx hd).symm.injective).comp Sum.inl_injective) Φ hΦ`. Use `h using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `y`. Rewrite using `[evA_apply, ins0_eq_extend]`.
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
