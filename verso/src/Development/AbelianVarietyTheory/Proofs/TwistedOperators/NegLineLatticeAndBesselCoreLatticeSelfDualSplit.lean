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
Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Use `(congrArg Neg.neg (Formalism.BasicNotions.Examples₂.stdSpace_gram_apply (E := D.host.E) Formalism.BasicNotions.Examples₂.star_isIntegral 1 (fun _ => false) 1 0 i j)).trans ?_` and prove the remaining obligations. Rewrite using `[Matrix.neg_apply, Matrix.one_apply]`. Apply the tactic sequence `by_cases h : i = j <;> simp [h, Formalism.BasicNotions.Examples₂.sgn] <;> first | exact rfl | exact fun e => h e`.
-/
theorem nLine_gram (D : D7) : (GlobalTheory.SeeSaw.Model.nLine D).gram = -1 := by
  refine Matrix.ext fun i j => ?_
  refine (congrArg Neg.neg (Formalism.BasicNotions.Examples₂.stdSpace_gram_apply (E := D.host.E) Formalism.BasicNotions.Examples₂.star_isIntegral 1
    (fun _ => false) 1 0 i j)).trans ?_
  rw [Matrix.neg_apply, Matrix.one_apply]
  by_cases h : i = j <;> simp [h, Formalism.BasicNotions.Examples₂.sgn] <;> first | exact rfl | exact fun e => h e

/- English proof (translation)
Simplify using `[latPi, Submodule.mem_pi]`.
-/
theorem mem_latPi {S : HSp D} {I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} {y : Fin S.rank → D.host.E} :
    y ∈ latPi S I ↔ ∀ i, y i ∈ I := by
  simp [latPi, Submodule.mem_pi]

/- English proof (translation)
Use `set J := GlobalTheory.SeeSaw.conjFI D I with hJdef`. Establish `hJ : J ≠ 0` using `fun h => hI (by rw [h, mul_zero] at hII; exact absurd hII.symm one_ne_zero)`. Establish `hstar : ∀ x : D.host.E, star x = D.host.conj x` using `fun x => Formalism.BasicNotions.bridge_star_holds D.R D.host x`. Establish `hmemJ : ∀ x : D.host.E, x ∈ J ↔ star x ∈ I` using `fun x => by rw [hstar]; exact GlobalTheory.SeeSaw.mem_conjFI`. Establish `hpair : ∀ x y : Fin S.rank → D.host.E, ∑ a, ∑ b, star (x a) * S.gram a b * y b = -∑ a, star (x a) * y a`.

Introduce `x y`. Rewrite using `[hg, ← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_eq_single a]`. Simplify using the standard rewrite rules.

Introduce `b _ hb`. Simplify using `[Matrix.neg_apply, Matrix.one_apply, Ne.symm hb]`. Simplify using the standard rewrite rules. Establish `hIeq : I = J⁻¹` using `eq_inv_of_mul_eq_one_left hII`. Choose the witnesses or unpack the hypotheses as in `⟨a0, ha0, ha00⟩ : ∃ a ∈ I, a ≠ 0 := by`.

Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Conclude with `hI (by`. Use extensionality with `x`. Rewrite using `[FractionalIdeal.mem_zero_iff]`.

Conclude with `⟨hcon x, fun h => h ▸ Submodule.zero_mem (I : Submodule (𝓞 D.host.E) D.host.E)⟩)`. Use `⟨⟨Submodule.fg_pi fun _ => FractionalIdeal.fg_of_isNoetherianRing le_rfl _, ?_⟩, fun y => ⟨fun hy x hx => ?_, fun h => ?_⟩⟩` and prove the remaining obligations. Rewrite using `[eq_top_iff, ← (Pi.basisFun D.host.E (Fin S.rank)).span_eq, Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Establish `hm : (Pi.single i a0 : Fin S.rank → D.host.E) ∈ latPi S I` using `mem_latPi.2 fun k => by`.

Distinguish the cases in `hk : k = i`. Substitute `hk` using the available equality. Simplify using `using ha0`. Rewrite using `[Pi.single_eq_of_ne hk]`. Conclude with `Submodule.zero_mem (I : Submodule (𝓞 D.host.E) D.host.E)`.

Establish `e : (Pi.basisFun D.host.E (Fin S.rank)) i = a0⁻¹ • (Pi.single i a0 : Fin S.rank → D.host.E)`. Use extensionality with `k`. Distinguish the cases in `hk : k = i`. Substitute `hk` using the available equality. Simplify using `[ha00]`.

Simplify using `[hk]`. Rewrite using `[e]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span hm)`. Rewrite using `[hpair]`. Establish `hy'` using `mem_latPi.1 hy`.

Establish `hx'` using `mem_latPi.1 hx`. Establish `hs : -∑ a, star (x a) * y a ∈ (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)`. Use `Submodule.neg_mem _ (Submodule.sum_mem _ fun a _ => ?_)` and prove the remaining obligations. Rewrite using `[← hII, mul_comm]`. Conclude with `FractionalIdeal.mul_mem_mul ((hmemJ _).2 (by rw [star_star]; exact hx' a)) (hy' a)`.

Take `⟨b, hb⟩` from `(FractionalIdeal.mem_one_iff _).1 hs`. Conclude with `⟨b, by rw [RingOfIntegers.coe_eq_algebraMap]; exact hb⟩`. Use `mem_latPi.2 fun i => ?_` and prove the remaining obligations. Rewrite using `[hIeq, FractionalIdeal.mem_inv_iff hJ]`. Introduce `t ht`.

Establish `hx : (Pi.single i (star t) : Fin S.rank → D.host.E) ∈ latPi S I` using `mem_latPi.2 fun k => by`. Distinguish the cases in `hk : k = i`. Substitute `hk` using the available equality. Simplify using `using (hmemJ t).1 ht`. Rewrite using `[Pi.single_eq_of_ne hk]`.

Conclude with `Submodule.zero_mem (I : Submodule (𝓞 D.host.E) D.host.E)`. Take `⟨b, hb⟩` from `h _ hx`. Rewrite `hb` using `[hpair, Finset.sum_eq_single i (fun k _ hk => by simp [hk]) (by simp)]`. Simplify using `only [Pi.single_eq_same, star_star] at hb`. Use `(FractionalIdeal.mem_one_iff _).2 ⟨-b, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_neg, ← RingOfIntegers.coe_eq_algebraMap, hb, mul_comm]`. Expand and normalize the polynomial expressions, which then agree.
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
Rewrite using `[← GlobalTheory.SeeSaw.conjFI_AA]`. Use extensionality with `x`. Rewrite using `[GlobalTheory.SeeSaw.mem_conjFI, GlobalTheory.SeeSaw.mem_conjFI, GlobalTheory.SeeSaw.conj_conj_host]`.
-/
theorem conjFI_AAbar (D : D7) : GlobalTheory.SeeSaw.conjFI D D.host.AAbar = D.host.AA := by
  rw [← GlobalTheory.SeeSaw.conjFI_AA]
  ext x
  rw [GlobalTheory.SeeSaw.mem_conjFI, GlobalTheory.SeeSaw.mem_conjFI, GlobalTheory.SeeSaw.conj_conj_host]

/- English proof (translation)
Establish `hA` using `GlobalTheory.FinPl.LocGen.AA_ne_zero D`. Establish `hB : D.host.AAbar ≠ 0`. Rewrite using `[← GlobalTheory.SeeSaw.conjFI_AA]`. Conclude with `(map_ne_zero _).2 hA`. Conclude with `mul_ne_zero (pow_ne_zero _ hA) (inv_ne_zero (pow_ne_zero _ hB))`.
-/
theorem lineId_ne_zero (D : D7) (j : ℕ) : lineId D j ≠ 0 := by
  have hA := GlobalTheory.FinPl.LocGen.AA_ne_zero D
  have hB : D.host.AAbar ≠ 0 := by
    rw [← GlobalTheory.SeeSaw.conjFI_AA]; exact (map_ne_zero _).2 hA
  exact mul_ne_zero (pow_ne_zero _ hA) (inv_ne_zero (pow_ne_zero _ hB))

/- English proof (translation)
Establish `hA` using `GlobalTheory.FinPl.LocGen.AA_ne_zero D`. Establish `hB : D.host.AAbar ≠ 0`. Rewrite using `[← GlobalTheory.SeeSaw.conjFI_AA]`. Conclude with `(map_ne_zero _).2 hA`. Unfold `lineId`.

Rewrite using `[map_mul, map_inv₀, map_pow, map_pow, GlobalTheory.SeeSaw.conjFI_AA, conjFI_AAbar]`. Establish `hA'` using `pow_ne_zero ((D.R.m - 2 - j) / 2 + 1) hA`. Establish `hB'` using `pow_ne_zero ((D.R.m - 2 - j) / 2 + 1) hB`. Clear the denominators using the available nonvanishing facts.
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
Use `⟨0, fun _ _ _ => ⟨0, ?_⟩⟩` and prove the remaining obligations. Introduce `D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F _ ch _ _ j σ hj`. Establish `hL : IsSelfDualC _ (lineL D j)` using `isSelfDualC_latPi (nLine_gram D) (lineId_ne_zero D j) (lineId_mul_conj D j)`. Establish `hX : IsSelfDualC _ (ch.G.Λ (.top j))` using `(ch.G.isV (X := .top j) (show j ≤ D.R.m by omega) (fun _ h => by cases h)).sd`. Conclude with `⟨hL, GlobalTheory.Core.Rk.SumBox.selfDual_sumLatO D _ _ _ _ _ _ hX hL, fun v => GlobalTheory.Core.Rk.SumSplit.orthAt_sumLatO D _ _ _ _ _ _ v⟩`.
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
