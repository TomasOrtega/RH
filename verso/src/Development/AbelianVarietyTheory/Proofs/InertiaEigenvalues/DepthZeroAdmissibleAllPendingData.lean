import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoeffRingsHaveRootsOfUnity
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimitiveCentralIdempotentEqSimpleRepIdempotentStatement
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf

namespace GlobalTheory.AdmDepthZero

/- English proof (translation)
Introduce `D P h i k v PI τ hτ`. Use `haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩`. Introduce `hsq hu`. Take `⟨ρ, hρ, he⟩` from `GlobalTheory.T.primitiveCentralIdempotent_eq_simpleRepIdempotent (D.host.g k) D.R.r (P.lz k) τ`. Establish `hO` using `PairedCharacterCondition.RT.ktyTie_of_spec P i PI k v τ hτ`.

Rewrite `hO` using `[he]`. Establish `hs : Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ * D.ntypes.eSer k ((P.lz k).lab τ) = Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ`. Rewrite using `[← he]`. Conclude with `PairedCharacterCondition.RT.idem_mul_eSer P k τ`. Conclude with `h i k v PI ρ _ hρ hs hO hsq hu`.
-/
theorem main : ∀ (D : D7) (P : PairedCharacterCondition.Pend D), PairedCharacterCondition.RT.AdmDepthZeroTypes (D := D) → PairedCharacterCondition.admDZ P := by
  intro D P h i k v PI τ hτ
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  intro hsq hu
  obtain ⟨ρ, hρ, he⟩ := GlobalTheory.T.primitiveCentralIdempotent_eq_simpleRepIdempotent (D.host.g k) D.R.r (P.lz k) τ
  have hO := PairedCharacterCondition.RT.ktyTie_of_spec P i PI k v τ hτ
  rw [he] at hO
  have hs : Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ * D.ntypes.eSer k ((P.lz k).lab τ) =
      Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ := by
    rw [← he]
    exact PairedCharacterCondition.RT.idem_mul_eSer P k τ
  exact h i k v PI ρ _ hρ hs hO hsq hu

end GlobalTheory.AdmDepthZero
