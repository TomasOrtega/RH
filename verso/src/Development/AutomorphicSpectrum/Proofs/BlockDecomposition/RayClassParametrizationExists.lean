import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsAvoidOne
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.PartialSum
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsShintaniConeDomain
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.RayClassConeParametrization

set_option autoImplicit false

noncomputable section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani

/- English proof (translation)
Introduce `F _ _ _ 𝔣 h𝔣 𝔞 h𝔞`. Take `⟨ι, _, r, v, hdom⟩` from `exists_coneDomain F 𝔣 h𝔣`. Take `⟨𝔟, x₀, hb, hx0, hx1, hxp, hab⟩` from `exists_complement h𝔣 h𝔞`. Take `⟨N, w, hN, hw⟩` from `exists_scaled (𝔪 := 𝔟 * 𝔣) (mul_ne_zero hb.1 h𝔣) r v`. Establish `hd` using `hdom.scale hN (u := fun c i => (w c i : F)) (fun c i => (hw c i).2)`.

Take `⟨J, a, b, c, d, e⟩` from `classParam_of_scaled hb.1 hx0 hx1 hxp hab hd (fun c i => (Ideal.mul_le_left : 𝔟 * 𝔣 ≤ 𝔟) (hw c i).1) (fun c i => (Ideal.mul_le_right : 𝔟 * 𝔣 ≤ 𝔣) (hw c i).1)`. Conclude with `⟨𝔟, J, a, b, c, d, e, hb.2⟩`.
-/
theorem exists_classParam_sup_eq_top : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔣 : Ideal (𝓞 F)), 𝔣 ≠ ⊥ →
    ∀ 𝔞 : Ideal (𝓞 F), CoprimeTo F 𝔣 𝔞 →
      ∃ (𝔟 : Ideal (𝓞 F)) (J : Type) (_ : Fintype J) (r' : J → ℕ) (y : J → 𝓞 F) (v' : ∀ j, Fin (r' j) → 𝓞 F),
        ClassParam 𝔣 𝔞 𝔟 r' y v' ∧ 𝔟 ⊔ 𝔣 = ⊤ := by
  intro F _ _ _ 𝔣 h𝔣 𝔞 h𝔞
  obtain ⟨ι, _, r, v, hdom⟩ := exists_coneDomain F 𝔣 h𝔣
  obtain ⟨𝔟, x₀, hb, hx0, hx1, hxp, hab⟩ := exists_complement h𝔣 h𝔞
  obtain ⟨N, w, hN, hw⟩ := exists_scaled (𝔪 := 𝔟 * 𝔣) (mul_ne_zero hb.1 h𝔣) r v
  have hd := hdom.scale hN (u := fun c i => (w c i : F)) (fun c i => (hw c i).2)
  obtain ⟨J, a, b, c, d, e⟩ := classParam_of_scaled hb.1 hx0 hx1 hxp hab hd
    (fun c i => (Ideal.mul_le_left : 𝔟 * 𝔣 ≤ 𝔟) (hw c i).1)
    (fun c i => (Ideal.mul_le_right : 𝔟 * 𝔣 ≤ 𝔣) (hw c i).1)
  exact ⟨𝔟, J, a, b, c, d, e, hb.2⟩

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani
