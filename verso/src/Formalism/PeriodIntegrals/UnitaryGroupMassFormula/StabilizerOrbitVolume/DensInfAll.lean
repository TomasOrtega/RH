import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.DensInfTR

noncomputable section

namespace PI.VolStabSW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField
open scoped TensorProduct
open PI.AdicCompletionValuation

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hCM M J hJ ha hc a hA1 hA2 X0 hT0 hdet`. Establish `: IsTotallyReal F` using `hCM.1`. Take `⟨k, eK, hK⟩` from `exists_coord_tens F E`. Take `⟨k1, e1, h1⟩` from `exists_coord_pi eK hK (Fin M)`. Take `⟨n, eV, hV⟩` from `exists_coord_pi e1 h1 (Fin a)`.

Take `⟨k2, e2, h2⟩` from `exists_coord_pi eK hK (Fin a)`. Take `⟨N, eM, hM⟩` from `exists_coord_pi e2 h2 (Fin a)`. Establish `hdiv : ∀ n : ℕ, 0 < n → ∀ S ∈ HermR (Ainf F) σ a, ∃ T ∈ HermR (Ainf F) σ a, n • T = S`. Introduce `n hn S hS`. Set `c : Ainf F ⊗[F] E` to `algebraMap F (Ainf F ⊗[F] E) (1 / n)`.

Establish `hsc : sigR (Ainf F) σ c = c` using `(Algebra.TensorProduct.map (AlgHom.id F (Ainf F)) σ).commutes _`. Use `⟨c • S, ?_, ?_⟩` and prove the remaining obligations. Introduce `i j`. Simplify using `only [Matrix.smul_apply, smul_eq_mul, map_mul, hsc]`. Rewrite using `[hS i j]`.

Establish `hc1 : (n : Ainf F ⊗[F] E) * c = 1`. Simplify using `only [c]`. Rewrite using `[← map_natCast (algebraMap F (Ainf F ⊗[F] E)) n, ← map_mul]`. Establish `: (n : F) ≠ 0` using `by exact_mod_cast hn.ne'`. Rewrite using `[mul_one_div_cancel this, map_one]`.

Use extensionality with `i j`. Simplify using `only [Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul, ← mul_assoc, hc1, one_mul]`. Take `⟨m, eH, hH⟩` from `exists_coord_sub (X := Matrix (Fin a) (Fin a) (Ainf F ⊗[F] E)) eM hM (HermR (Ainf F) σ a) (isClosed_HermR (Ainf F) σ a) hdiv`. Conclude with `⟨n, m, eV, eH, hV, hH⟩`.
-/
theorem tensR_holds : TensR := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a hA1 hA2 X0 hT0 hdet
  have : IsTotallyReal F := hCM.1
  obtain ⟨k, eK, hK⟩ := exists_coord_tens F E
  obtain ⟨k1, e1, h1⟩ := exists_coord_pi eK hK (Fin M)
  obtain ⟨n, eV, hV⟩ := exists_coord_pi e1 h1 (Fin a)
  obtain ⟨k2, e2, h2⟩ := exists_coord_pi eK hK (Fin a)
  obtain ⟨N, eM, hM⟩ := exists_coord_pi e2 h2 (Fin a)
  have hdiv : ∀ n : ℕ, 0 < n → ∀ S ∈ HermR (Ainf F) σ a, ∃ T ∈ HermR (Ainf F) σ a, n • T = S := by
    intro n hn S hS
    let c : Ainf F ⊗[F] E := algebraMap F (Ainf F ⊗[F] E) (1 / n)
    have hsc : sigR (Ainf F) σ c = c :=
      (Algebra.TensorProduct.map (AlgHom.id F (Ainf F)) σ).commutes _
    refine ⟨c • S, ?_, ?_⟩
    · intro i j
      simp only [Matrix.smul_apply, smul_eq_mul, map_mul, hsc]
      rw [hS i j]
    · have hc1 : (n : Ainf F ⊗[F] E) * c = 1 := by
        simp only [c]
        rw [← map_natCast (algebraMap F (Ainf F ⊗[F] E)) n, ← map_mul]
        have : (n : F) ≠ 0 := by exact_mod_cast hn.ne'
        rw [mul_one_div_cancel this, map_one]
      ext i j
      simp only [Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul, ← mul_assoc, hc1, one_mul]
  obtain ⟨m, eH, hH⟩ := exists_coord_sub (X := Matrix (Fin a) (Fin a) (Ainf F ⊗[F] E)) eM hM
    (HermR (Ainf F) σ a) (isClosed_HermR (Ainf F) σ a) hdiv
  exact ⟨n, m, eV, eH, hV, hH⟩

/- English proof (translation)
The claim follows from `densInf_of_tensR tensR_holds`.
-/
theorem densInf_holds : DensInf := densInf_of_tensR tensR_holds

end PI.VolStabSW
