import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GoodChi
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodTupleConditionOfIdempotentZero

noncomputable section
namespace GlobalTheory.MemN
open Formalism.BasicNotions GlobalTheory.Mem GlobalTheory.MemN NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

/- English proof (translation)
Use `⟨fun p _ => GaloisStage.lData B.host p, ?_⟩` and prove the remaining obligations. Introduce `p hp e _ _ n h`. Rewrite using `[GaloisStage.shaTrue, dif_pos hp.out]`. Use `show ((Formalism.GaloisCohomology.shaLen (GaloisStage.lData B.host p) (e : ℤ)).toNat : ℚ) = n`. Rewrite using `[h, ENat.toNat_natCast]`.
-/
theorem shaOK_shaTrue (B : Pre) : ShaOK B (GaloisStage.shaTrue B.host) := by
  refine ⟨fun p _ => GaloisStage.lData B.host p, ?_⟩
  intro p hp e _ _ n h
  rw [GaloisStage.shaTrue, dif_pos hp.out]
  show ((Formalism.GaloisCohomology.shaLen (GaloisStage.lData B.host p) (e : ℤ)).toNat : ℚ) = n
  rw [h, ENat.toNat_natCast]

/- English proof (translation)
Introduce `B` and use `⟨GaloisStage.shaTrue B.host, GaloisStage.shaTrue_nonneg B.host, shaOK_shaTrue B⟩`.
-/
theorem exists_nonneg_shaOK : ∀ B : Pre, ∃ s : ℕ → ℕ → ℚ, (∀ p e, 0 ≤ s p e) ∧ ShaOK B s :=
  fun B => ⟨GaloisStage.shaTrue B.host, GaloisStage.shaTrue_nonneg B.host, shaOK_shaTrue B⟩

end GlobalTheory.MemN
