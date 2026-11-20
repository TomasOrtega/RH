import Formalism.LocalToGlobal.Columns.ReductionColumnStandardBasis
import Formalism.LocalToGlobal.Columns.UnfoldingPhiCompLeftUnipotentSource

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
theorem cq_card {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) : Nat.card (𝓞 E ⧸ P.asIdeal) = qOf P := by
  unfold qOf
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Substitute using the available equality. A detailed English derivation is pending.
-/
theorem cq_covT : TruncatedUnfoldingChangeOfVarsTarget := by
  intro E _ _ _ P K _ n' c' n c hc hp hu psi D a b e hadd hint Ψ hsupp haD hinv r hr g hgI hg hre _ heD A B hA hbB _ wt y
  subst hc
  exact finite_sum_target_equality (ciQ_mem P) hu hp (cq_card P) psi hadd hint Ψ hsupp haD hinv r hr g hgI hg hre heD hA hbB wt y

end Formalism.L2.Col
