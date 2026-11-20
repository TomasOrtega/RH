import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplitBasisCompl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.HermPlaneComplSig

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n n₁ Y Y₁ H i₀ i₁ r s hB hY hH`. Establish `h1` using `GlobalTheory.HermPlaneCompl.isHerm_compl hB hY hH`. Use `⟨?_, h1⟩` and prove the remaining obligations. Take `⟨w⟩ : Nonempty (InfinitePlace F)` from `inferInstance`. Establish `a` using `(hY.sig w).1`.

Establish `b` using `(h1.sig w).1`. Establish `c` using `hH.rank`. Use linear arithmetic over natural numbers and integers.
-/
theorem isHerm_complement : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n n₁ : ℕ) (Y : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁) (i₀ i₁ r s : ℕ),
    B.IsGood σ → Y.IsHerm σ B r s → H.IsAdapted σ B Y Y₁ i₀ i₁ → 1 ≤ s ∧ Y₁.IsHerm σ B (r - 1) (s - 1) := by
  intro F E _ _ _ _ _ σ B n n₁ Y Y₁ H i₀ i₁ r s hB hY hH
  have h1 := GlobalTheory.HermPlaneCompl.isHerm_compl hB hY hH
  refine ⟨?_, h1⟩
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have a := (hY.sig w).1
  have b := (h1.sig w).1
  have c := hH.rank
  omega

end GlobalTheory.HermPlaneComplSig
