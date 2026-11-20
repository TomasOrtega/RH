import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModGDefs
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModGBasic
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModLocA
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModLocB
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModLocC
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModLocD

noncomputable section
open scoped BigOperators Classical UpperHalfPlane
open NumberField IsDedekindDomain Formalism.L2.Th1.CM Neutral.HilbertClassField

namespace ReciprocityTheory.ChartRestriction.L1

/- English proof (translation)
Take `⟨e, he⟩` from `locEmb d l ι`. Establish `hs : (e (algebraMap (KQ d) (Om d) (sqK d))) ^ 2 = -(d : PadicAlgCl l)`. Establish `h1 : (algebraMap (KQ d) (Om d) (sqK d)) ^ 2 = -(d : Om d)`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify `sqD_sq d` using `[sqK]`.

Rewrite using `[← map_pow, h1, map_neg, map_natCast]`. Establish `hint : IsIntegral ℚ_[l] (e (algebraMap (KQ d) (Om d) (sqK d)))`. Use `⟨Polynomial.X ^ 2 + Polynomial.C (d : ℚ_[l]), Polynomial.monic_X_pow_add_C _ (by norm_num), ?_⟩` and prove the remaining obligations. Simplify using `[hs]`. Establish `hK` using `IntermediateField.adjoin.finiteDimensional hint`.

Establish `hmem` using `fixed_mem_Kur _ hK (e x) (fun ρ hρ => by`. Take `⟨σ, hσ, hc⟩` from `locLift ι e he ρ hρ`. Rewrite using `[← hc, hx σ hσ])`. Rewrite using `[← he]`. Conclude with `kur_le hl hld hs hmem`.
-/
theorem inertKur {d l : ℕ} [Fact l.Prime] (hl : l ≠ 2) (hld : ¬ l ∣ d) (ι : ℂ ≃+* ℂ_[l]) (x : Om d)
    (hx : ∀ σ : Om d ≃ₐ[KQ d] Om d, InertiaEl (Aio d l ι) σ → σ x = x) : ι (x : ℂ) ∈ MaximalUnramifiedExtension l := by
  obtain ⟨e, he⟩ := locEmb d l ι
  have hs : (e (algebraMap (KQ d) (Om d) (sqK d))) ^ 2 = -(d : PadicAlgCl l) := by
    have h1 : (algebraMap (KQ d) (Om d) (sqK d)) ^ 2 = -(d : Om d) := by
      apply Subtype.ext
      simpa [sqK] using sqD_sq d
    rw [← map_pow, h1, map_neg, map_natCast]
  have hint : IsIntegral ℚ_[l] (e (algebraMap (KQ d) (Om d) (sqK d))) := by
    refine ⟨Polynomial.X ^ 2 + Polynomial.C (d : ℚ_[l]), Polynomial.monic_X_pow_add_C _ (by norm_num), ?_⟩
    simp [hs]
  have hK := IntermediateField.adjoin.finiteDimensional hint
  have hmem := fixed_mem_Kur _ hK (e x) (fun ρ hρ => by
    obtain ⟨σ, hσ, hc⟩ := locLift ι e he ρ hρ
    rw [← hc, hx σ hσ])
  rw [← he]
  exact kur_le hl hld hs hmem

end ReciprocityTheory.ChartRestriction.L1
