import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CongruenceLengthFinsetSupEqSum
import Formalism.LocalToGlobal.Columns.AlgebraMapMemMaximalIdealPowIff
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverAlg
open Formalism.BasicNotions Formalism.L2 NumberField IsDedekindDomain Module
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FCongruenceLengthFinsetSupEqSum.lean&line=114#L114)
-/
theorem _root_.GlobalTheory.T.congruenceLength_finset_sup_eq_sum : ∀ (O V ι : Type) [CommRing O] [AddCommGroup V] [Module O V] (F : Finset ι) (L G B : ι → Submodule O V), F.SupIndep (fun i => G i ⊔ B i) → (∀ i ∈ F, Disjoint (G i) (B i)) → (∀ i ∈ F, L i ≤ G i ⊔ B i) → Module.length O (↥(F.sup G ⊓ (F.sup L ⊔ F.sup B)) ⧸ (F.sup L ⊓ F.sup G).comap (F.sup G ⊓ (F.sup L ⊔ F.sup B)).subtype) = ∑ i ∈ F, Module.length O (↥(G i ⊓ (L i ⊔ B i)) ⧸ (L i ⊓ G i).comap (G i ⊓ (L i ⊔ B i)).subtype) := by
  first | exact @GlobalTheory.congruence_length_finset_sup | exact GlobalTheory.congruence_length_finset_sup | (intros; apply GlobalTheory.congruence_length_finset_sup <;> assumption)
