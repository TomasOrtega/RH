import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TiltSc
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OrthDecSumLatticeSelfDual
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OrthAtSumLatO
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodIdealZpowCompletionAdeleConjIff
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsPeriodIdealLocalGeneratorAtSplitPoint
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open scoped nonZeroDivisors

namespace GlobalTheory.RowShape

variable {D : D7}

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem nLine_gram (D : D7) : (GlobalTheory.SeeSaw.Model.nLine D).gram = -1 := by
  refine Matrix.ext fun i j => ?_
  refine (congrArg Neg.neg (Formalism.BasicNotions.Examples₂.stdSpace_gram_apply (E := D.host.E) Formalism.BasicNotions.Examples₂.star_isIntegral 1
    (fun _ => false) 1 0 i j)).trans ?_
  rw [Matrix.neg_apply, Matrix.one_apply]
  by_cases h : i = j <;> simp [h, Formalism.BasicNotions.Examples₂.sgn] <;> first | exact rfl | exact fun e => h e

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem mem_latPi {S : HSp D} {I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} {y : Fin S.rank → D.host.E} :
    y ∈ latPi S I ↔ ∀ i, y i ∈ I := by
  simp [latPi, Submodule.mem_pi]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Establish an intermediate fact. Extract witnesses or component facts from the available result. Assume the negation of the conclusion and derive a contradiction.

By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Assume the hypotheses and unpack their components. Establish an intermediate fact. Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify to obtain the desired conclusion from the available facts.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. By extensionality, compare the relevant components. Consider separately whether the proposition holds or fails. Substitute using the available equality.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result.

Supply the required witnesses or components. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify to obtain the desired conclusion from the available facts. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result.

Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.

A detailed English derivation is pending.
-/
theorem isSelfDualC_latPi {S : HSp D} (hg : S.gram = -1) {I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} (hI : I ≠ 0)
    (hII : I * GlobalTheory.SeeSaw.conjFI D I = 1) : IsSelfDualC S (latPi S I) := by
  set J := GlobalTheory.SeeSaw.conjFI D I with hJdef
  have hJ : J ≠ 0 := fun h => hI (by rw [h, mul_zero] at hII; exact absurd hII.symm one_ne_zero)
  have hstar : ∀ x : D.host.E, star x = D.host.conj x := fun x => Formalism.BasicNotions.bridge_star_holds D.R D.host x
  have hmemJ : ∀ x : D.host.E, x ∈ J ↔ star x ∈ I := fun x => by rw [hstar]; exact GlobalTheory.SeeSaw.mem_conjFI
  have hpair : ∀ x y : Fin S.rank → D.host.E, ∑ a, ∑ b, star (x a) * S.gram a b * y b = -∑ a, star (x a) * y a := by
    intro x y
    rw [hg, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single a]
    · simp
    · intro b _ hb; simp [Matrix.neg_apply, Matrix.one_apply, Ne.symm hb]
    · simp
  have hIeq : I = J⁻¹ := eq_inv_of_mul_eq_one_left hII
  obtain ⟨a0, ha0, ha00⟩ : ∃ a ∈ I, a ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hI (by
      ext x
      rw [FractionalIdeal.mem_zero_iff]
      exact ⟨hcon x, fun h => h ▸ Submodule.zero_mem (I : Submodule (𝓞 D.host.E) D.host.E)⟩)
  refine ⟨⟨Submodule.fg_pi fun _ => FractionalIdeal.fg_of_isNoetherianRing le_rfl _, ?_⟩, fun y => ⟨fun hy x hx => ?_, fun h => ?_⟩⟩
  · rw [eq_top_iff, ← (Pi.basisFun D.host.E (Fin S.rank)).span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have hm : (Pi.single i a0 : Fin S.rank → D.host.E) ∈ latPi S I := mem_latPi.2 fun k => by
      by_cases hk : k = i
      · subst hk; simpa using ha0
      · rw [Pi.single_eq_of_ne hk]; exact Submodule.zero_mem (I : Submodule (𝓞 D.host.E) D.host.E)
    have e : (Pi.basisFun D.host.E (Fin S.rank)) i = a0⁻¹ • (Pi.single i a0 : Fin S.rank → D.host.E) := by
      ext k; by_cases hk : k = i
      · subst hk; simp [ha00]
      · simp [hk]
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hm)
  · rw [hpair]
    have hy' := mem_latPi.1 hy
    have hx' := mem_latPi.1 hx
    have hs : -∑ a, star (x a) * y a ∈ (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := by
      refine Submodule.neg_mem _ (Submodule.sum_mem _ fun a _ => ?_)
      rw [← hII, mul_comm]
      exact FractionalIdeal.mul_mem_mul ((hmemJ _).2 (by rw [star_star]; exact hx' a)) (hy' a)
    obtain ⟨b, hb⟩ := (FractionalIdeal.mem_one_iff _).1 hs
    exact ⟨b, by rw [RingOfIntegers.coe_eq_algebraMap]; exact hb⟩
  · refine mem_latPi.2 fun i => ?_
    rw [hIeq, FractionalIdeal.mem_inv_iff hJ]
    intro t ht
    have hx : (Pi.single i (star t) : Fin S.rank → D.host.E) ∈ latPi S I := mem_latPi.2 fun k => by
      by_cases hk : k = i
      · subst hk; simpa using (hmemJ t).1 ht
      · rw [Pi.single_eq_of_ne hk]; exact Submodule.zero_mem (I : Submodule (𝓞 D.host.E) D.host.E)
    obtain ⟨b, hb⟩ := h _ hx
    rw [hpair, Finset.sum_eq_single i (fun k _ hk => by simp [hk]) (by simp)] at hb
    simp only [Pi.single_eq_same, star_star] at hb
    refine (FractionalIdeal.mem_one_iff _).2 ⟨-b, ?_⟩
    rw [map_neg, ← RingOfIntegers.coe_eq_algebraMap, hb, mul_comm]
    ring

/- English proof (translation)
Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities.
-/
theorem conjFI_AAbar (D : D7) : GlobalTheory.SeeSaw.conjFI D D.host.AAbar = D.host.AA := by
  rw [← GlobalTheory.SeeSaw.conjFI_AA]
  ext x
  rw [GlobalTheory.SeeSaw.mem_conjFI, GlobalTheory.SeeSaw.mem_conjFI, GlobalTheory.SeeSaw.conj_conj_host]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem lineId_ne_zero (D : D7) (j : ℕ) : lineId D j ≠ 0 := by
  have hA := GlobalTheory.FinPl.LocGen.AA_ne_zero D
  have hB : D.host.AAbar ≠ 0 := by
    rw [← GlobalTheory.SeeSaw.conjFI_AA]; exact (map_ne_zero _).2 hA
  exact mul_ne_zero (pow_ne_zero _ hA) (inv_ne_zero (pow_ne_zero _ hB))

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Clear the denominators using the available nonvanishing facts. A detailed English derivation is pending.
-/
theorem lineId_mul_conj (D : D7) (j : ℕ) : lineId D j * GlobalTheory.SeeSaw.conjFI D (lineId D j) = 1 := by
  have hA := GlobalTheory.FinPl.LocGen.AA_ne_zero D
  have hB : D.host.AAbar ≠ 0 := by
    rw [← GlobalTheory.SeeSaw.conjFI_AA]; exact (map_ne_zero _).2 hA
  unfold lineId
  rw [map_mul, map_inv₀, map_pow, map_pow, GlobalTheory.SeeSaw.conjFI_AA, conjFI_AAbar]
  have hA' := pow_ne_zero ((D.R.m - 2 - j) / 2 + 1) hA
  have hB' := pow_ne_zero ((D.R.m - 2 - j) / 2 + 1) hB
  field_simp

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Supply the required witnesses or components.
-/
theorem coreL_selfDual_split : Big fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch => ∀ j σ, j + 2 * σ + 2 = D.R.m → IsSelfDualC _ (GlobalTheory.RowShape.lineL D j) ∧
    IsSelfDualC _ (GlobalTheory.RowShape.coreL ch.G j) ∧ ∀ v, GlobalTheory.FinPl.OrthAt (GlobalTheory.OrthSumExists.orthDecHsum D (ch.G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D))
      (GlobalTheory.RowShape.coreL ch.G j) (ch.G.Λ (.top j)) (GlobalTheory.RowShape.lineL D j) v := by
  refine ⟨0, fun _ _ _ => ⟨0, ?_⟩⟩
  intro D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F _ ch _ _ j σ hj
  have hL : IsSelfDualC _ (lineL D j) := isSelfDualC_latPi (nLine_gram D) (lineId_ne_zero D j) (lineId_mul_conj D j)
  have hX : IsSelfDualC _ (ch.G.Λ (.top j)) :=
    (ch.G.isV (X := .top j) (show j ≤ D.R.m by omega) (fun _ h => by cases h)).sd
  exact ⟨hL, GlobalTheory.Core.Rk.SumBox.selfDual_sumLatO D _ _ _ _ _ _ hX hL,
    fun v => GlobalTheory.Core.Rk.SumSplit.orthAt_sumLatO D _ _ _ _ _ _ v⟩

end GlobalTheory.RowShape
