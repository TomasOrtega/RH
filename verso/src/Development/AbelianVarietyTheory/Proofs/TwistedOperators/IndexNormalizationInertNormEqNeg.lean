import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGoodIndexNormalizationNegativeInert
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ActAApply
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.LamInert

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Reduce the conclusion to the remaining proof obligations.

Express the relevant assertion in an equivalent form by its definition. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Move the embeddings inside the algebraic operations. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations.

Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem lam_qV_inert : ∀ (D : D7) (lam : ℕ →* ℂ), GlobalTheory.FinWeil.GoodNorm (GlobalTheory.FinWeil.sgO D) lam → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)), IsInertAt D.host.F D.host.E v w → lam (qV D.host.E w) = -((qV D.host.F v : ℕ) : ℂ) := by
  intro D lam hl v w hw
  have hmap : Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) v.asIdeal = w.asIdeal := hw
  have hfix : ∀ x : 𝓞 D.host.F, GlobalTheory.FinWeil.sgO D (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x) =
      algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x := fun x => by
    apply RingOfIntegers.coe_injective
    refine (GlobalTheory.FinWeil.coe_sgO D _).trans ?_
    exact (D.host.conjE_mem_hostF_iff _).1 (by
      change ((x : D.host.F) : D.host.E) ∈ _
      exact (x : D.host.F).2)
  have hstab : ∀ r ∈ w.asIdeal, GlobalTheory.FinWeil.sgO D r ∈ w.asIdeal := by
    rw [← hmap]
    have : Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) v.asIdeal ≤
        (Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) v.asIdeal).comap (GlobalTheory.FinWeil.sgO D) := by
      rw [Ideal.map_le_iff_le_comap]
      intro x hx
      rw [Ideal.mem_comap, Ideal.mem_comap, hfix]
      exact Ideal.mem_map_of_mem _ hx
    exact fun r hr => this hr
  have hfin : Finite (𝓞 D.host.E ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot w.asIdeal w.ne_bot
  have h1 := ((hl.2 w.asIdeal w.isMaximal hfin).2 hstab).1
  have hcard : Nat.card (𝓞 D.host.E ⧸ w.asIdeal) = qV D.host.E w := by
    change _ = Ideal.absNorm w.asIdeal
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hsq : qV D.host.E w = qV D.host.F v ^ 2 :=
    GlobalTheory.LFun.InertChart.absNorm_eq (GlobalTheory.AdelicU.isCMExt_host D).2.2.1 hw
  rw [hcard, hsq] at h1
  rw [hsq, h1]
  congr 1
  push_cast
  rw [Real.sqrt_sq (Nat.cast_nonneg _)]
  push_cast
  rfl

end GlobalTheory.LamInert
