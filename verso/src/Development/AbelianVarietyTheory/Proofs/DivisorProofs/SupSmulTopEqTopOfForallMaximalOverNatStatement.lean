import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupSmulTopEqTopOfForallMaximalOverNat
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmHostUnitAddConjEqOne

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.sup_smul_top_eq_top_of_maximal` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSupSmulTopEqTopOfForallMaximalOverNat.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.sup_smul_top_eq_top_of_forall_maximal_over_nat : ∀ {E : Type} [Field E] [NumberField E] {X : Type} [AddCommGroup X] [Module (𝓞 E) X]
    (N : Submodule (𝓞 E) X) (n : ℕ) (hn : 0 < n)
    (h : ∀ 𝔮 : Ideal (𝓞 E), 𝔮.IsMaximal → (n : 𝓞 E) ∈ 𝔮 → N ⊔ 𝔮 • (⊤ : Submodule (𝓞 E) X) = ⊤),
    N ⊔ Ideal.span {(n : 𝓞 E)} • (⊤ : Submodule (𝓞 E) X) = ⊤ := by
  first | exact @GlobalTheory.sup_smul_top_eq_top_of_maximal | exact GlobalTheory.sup_smul_top_eq_top_of_maximal | (intros; apply GlobalTheory.sup_smul_top_eq_top_of_maximal <;> assumption)
