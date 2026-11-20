import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HsConjTranspose

noncomputable section

open Matrix
open CompanionTheory.RgExh.Dec CompanionTheory.RgExh.Dec.L ReciprocityTheory.ChartRestriction.DS GlobalTheory.CompanionTheory.PSubFlag GlobalTheory.CompanionTheory.UGeo

namespace GlobalTheory.CompanionTheory.UGeo

/- English proof (translation)
Establish `h1 : (Formalism.MainNotions.S.uMat k)ᴴ * Formalism.MainNotions.S.uMat k = 1` using `hk`. Establish `h2 : Formalism.MainNotions.S.uMat k * (Formalism.MainNotions.S.uMat k)ᴴ = 1` using `mul_eq_one_comm.1 h1`. Establish `h3 : (Formalism.MainNotions.S.uMat k)ᴴ * Formalism.REAL.Jm ε * Formalism.MainNotions.S.uMat k = Formalism.REAL.Jm ε` using `GlobalTheory.RealIwasawa.uMat_form k`. Establish `h4 : Formalism.REAL.Jm ε * Formalism.MainNotions.S.uMat k = Formalism.MainNotions.S.uMat k * Formalism.REAL.Jm ε`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[h2, Matrix.one_mul]`. Use `_ = Formalism.MainNotions.S.uMat k * ((Formalism.MainNotions.S.uMat k)ᴴ * Formalism.REAL.Jm ε * Formalism.MainNotions.S.uMat k) := by`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = Formalism.MainNotions.S.uMat k * Formalism.REAL.Jm ε := by rw [h3]`. Use `⟨Unitary.mem_iff.2 ⟨h1, h2⟩, ?_⟩` and prove the remaining obligations.

Conclude with `h4.symm`.
-/
theorem mem_KG_of_mem_maxK {n : ℕ} {ε : Fin n → Bool} {k : S7.UJ ε} (hk : k ∈ GlobalTheory.FlagMeas.maxK ε) :
    k ∈ S7.KG ε := by
  have h1 : (Formalism.MainNotions.S.uMat k)ᴴ * Formalism.MainNotions.S.uMat k = 1 := hk
  have h2 : Formalism.MainNotions.S.uMat k * (Formalism.MainNotions.S.uMat k)ᴴ = 1 := mul_eq_one_comm.1 h1
  have h3 : (Formalism.MainNotions.S.uMat k)ᴴ * Formalism.REAL.Jm ε * Formalism.MainNotions.S.uMat k = Formalism.REAL.Jm ε :=
    GlobalTheory.RealIwasawa.uMat_form k
  have h4 : Formalism.REAL.Jm ε * Formalism.MainNotions.S.uMat k = Formalism.MainNotions.S.uMat k * Formalism.REAL.Jm ε := by
    calc Formalism.REAL.Jm ε * Formalism.MainNotions.S.uMat k
        = (Formalism.MainNotions.S.uMat k * (Formalism.MainNotions.S.uMat k)ᴴ) * Formalism.REAL.Jm ε * Formalism.MainNotions.S.uMat k := by
          rw [h2, Matrix.one_mul]
      _ = Formalism.MainNotions.S.uMat k * ((Formalism.MainNotions.S.uMat k)ᴴ * Formalism.REAL.Jm ε * Formalism.MainNotions.S.uMat k) := by
          simp only [Matrix.mul_assoc]
      _ = Formalism.MainNotions.S.uMat k * Formalism.REAL.Jm ε := by rw [h3]
  refine ⟨Unitary.mem_iff.2 ⟨h1, h2⟩, ?_⟩
  exact h4.symm

/- English proof (translation)
Take `⟨k, hk, hp⟩` from `GlobalTheory.RealIwasawa.exists_stab_mul_compact (isoFlag hA) g`. Take `⟨m, hm, hu⟩` from `GlobalTheory.RealIwasawa.exists_unip_mul_levi (isoFlag hA) _ hp`. Conclude with `⟨g * k⁻¹, (psubEq n ε A hA _).2 ⟨_, hu, m, hm, by group⟩, k, hk, by group⟩`.
-/
theorem exists_psub_mul_maxK {n : ℕ} {ε : Fin n → Bool} {A : Matrix (Fin n) (Fin n) ℂ} (hA : IsGrad ε A)
    (g : Formalism.REAL.UJ ε) : ∃ p : Formalism.REAL.UJ ε, p ∈ PSub ε A ∧ ∃ k ∈ GlobalTheory.FlagMeas.maxK ε, g = p * k := by
  obtain ⟨k, hk, hp⟩ := GlobalTheory.RealIwasawa.exists_stab_mul_compact (isoFlag hA) g
  obtain ⟨m, hm, hu⟩ := GlobalTheory.RealIwasawa.exists_unip_mul_levi (isoFlag hA) _ hp
  exact ⟨g * k⁻¹, (psubEq n ε A hA _).2 ⟨_, hu, m, hm, by group⟩, k, hk, by group⟩

/- English proof (translation)
Introduce `n ε A hA g`. Take `⟨p, hp, k, hk, e⟩` from `exists_psub_mul_maxK (A := A) hA g`. Conclude with `⟨⟨p, hp⟩, ⟨k, mem_KG_of_mem_maxK hk⟩, e⟩`.
-/
theorem iwasawa_psub : ∀ (n : ℕ) (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ), IsGrad ε A →
    ∀ g : S7.UJ ε, ∃ (x : PSub ε A) (k : S7.KG ε), g = (x : S7.UJ ε) * (k : S7.UJ ε) := by
  intro n ε A hA g
  obtain ⟨p, hp, k, hk, e⟩ := exists_psub_mul_maxK (A := A) hA g
  exact ⟨⟨p, hp⟩, ⟨k, mem_KG_of_mem_maxK hk⟩, e⟩

end GlobalTheory.CompanionTheory.UGeo
