import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitTorusInLeviParabolic
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIdTorusEltOne
open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.StdPar GlobalTheory.IdTorus
open GlobalTheory.Doubling (absE conjUnit)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.IdTorusCent.centre_levi` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSplitTorusInLeviParabolic.lean&line=56#L56)
-/
theorem _root_.GlobalTheory.T.split_torus_in_levi_parabolic : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}, IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∀ {S : Finset (Fin r)}, (∀ k ∈ S, ∀ i, i ≤ k → i ∈ S) → ∀ {l : Fin r → (AF F ⊗[F] E)ˣ} {a : GAd σ J}, (∀ k ∉ S, l k = 1) → IsIdTorusElt σ J X Y l a → a ∈ levi σ J X Y S ∧ ∀ m ∈ levi σ J X Y S, a * m = m * a := by
  first | exact @GlobalTheory.IdTorusCent.centre_levi | exact GlobalTheory.IdTorusCent.centre_levi | (intros; apply GlobalTheory.IdTorusCent.centre_levi <;> assumption)
