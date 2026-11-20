import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HtCard
import Development.AutomorphicArithmetic.BlochKatoExtensions.PhtCmp
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.RkMultVOfNotJump
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompactGroupRepDefinedOverFiniteExtension
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsContinuousLadicGalRepModelFiniteExtHost
import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocA

noncomputable section

namespace GlobalTheory.HtCardProof

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.L2 Module

section Local

variable {l m : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) {K LL : FinExt l}
  (r : ↥(GK K) →* GL (Fin m) ↥LL.1)

set_option maxHeartbeats 1000000 in
include T in

/- English proof (translation)
Take `⟨lo, hlo⟩` from `Formalism.MainNotions.N.Pv.LocalLengthBound.rk_fildR_lo (P.PD K) (vrep r) τ`. Take `⟨hi, hhi⟩` from `Formalism.MainNotions.N.Pv.LocalLengthBound.rk_fildR_hi (P.PD K) (vrep r) τ`. Establish `anti` using `Formalism.MainNotions.N.Pv.LocalLengthBound.rk_fildR_anti (P.PD K) (vrep r) τ`. Use `haveI : ∀ a, FiniteDimensional ↥LL.1 ↥(FildR (P.PD K) (vrep r) τ a) := fun a => Submodule.finiteDimensional_of_le (inf_le_left : FildR (P.PD K) (vrep r) τ a ≤ DdRE (P.PD K) (vrep r) τ)`. Establish `nn : ∀ a, 0 ≤ multV (P.PD K) (vrep r) τ a` using `fun a => by`.

Use `Submodule.finrank_mono (anti (show a ≤ a + 1 by omega))` as an intermediate fact. Unfold `multV`. Use linear arithmetic over natural numbers and integers. Take `⟨lo₁, hl1, hl2⟩ : ∃ lo₁, lo₁ ≤ lo ∧ lo₁ ≤ hi` from `⟨min lo hi, min_le_left _ _, min_le_right _ _⟩`. Establish `zero : ∀ a, a ∉ Finset.Ico lo₁ hi → multV (P.PD K) (vrep r) τ a = 0` using `fun a ha => by`.

Rewrite `ha` using `[Finset.mem_Ico, not_and_or, not_le, not_lt]`. Establish `e : FildR (P.PD K) (vrep r) τ a = FildR (P.PD K) (vrep r) τ (a + 1)`. Break down `ha with ha | ha` into its components or cases. Conclude with `(hlo a (by omega)).trans (hlo (a + 1) (by omega)).symm`. Conclude with `(hhi a ha).trans (hhi (a + 1) (by omega)).symm`.

Unfold `multV`. Rewrite using `[e, sub_self]`. Use `⟨∑ a ∈ Finset.Ico lo₁ hi, Multiset.replicate (multV (P.PD K) (vrep r) τ a).toNat a, ?_, fun b => ?_⟩` and prove the remaining obligations. Rewrite using `[Multiset.card_sum]`. Simplify using `only [Multiset.card_replicate]`.

Establish `hs : ∑ a ∈ Finset.Ico lo₁ hi, multV (P.PD K) (vrep r) τ a = (finrank ↥LL.1 ↥(FildR (P.PD K) (vrep r) τ lo₁) : ℤ) - finrank ↥LL.1 ↥(FildR (P.PD K) (vrep r) τ hi)` using `Formalism.MainNotions.N.Pv.LocalLengthBound.rk_sum_multV _ _ _ _ _ hl2`. Establish `e1 : finrank ↥LL.1 ↥(FildR (P.PD K) (vrep r) τ lo₁) = finrank ↥LL.1 ↥(DdRE (P.PD K) (vrep r) τ)`. Rewrite using `[hlo lo₁ hl1]`. Establish `e2 : finrank ↥LL.1 ↥(FildR (P.PD K) (vrep r) τ hi) = 0` using `Submodule.finrank_eq_zero.2 (hhi hi le_rfl)`. Rewrite `hs` using `[e1, e2]`.

Establish `: ((∑ a ∈ Finset.Ico lo₁ hi, (multV (P.PD K) (vrep r) τ a).toNat : ℕ) : ℤ) = (finrank ↥LL.1 ↥(DdRE (P.PD K) (vrep r) τ) : ℤ)`. Use `push_cast`. Rewrite using `[Finset.sum_congr rfl fun a _ => Int.toNat_of_nonneg (nn a), hs]`. Simplify using the standard rewrite rules. Conclude with `this` after adjusting the coercions.

Rewrite using `[Multiset.count_sum']`. Simplify using `only [Multiset.count_replicate]`. Rewrite using `[Finset.sum_ite_eq']`. Distinguish the cases in `hb : b ∈ Finset.Ico lo₁ hi`. Rewrite using `[if_pos hb, Int.toNat_of_nonneg (nn b)]`.

Rewrite using `[if_neg hb, zero b hb]`. Both sides reduce to the same expression.
-/
theorem exists_count (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) [FiniteDimensional ↥LL.1 ↥(DdRE (P.PD K) (vrep r) τ)] :
    ∃ M : Multiset ℤ, Multiset.card M = finrank ↥LL.1 ↥(DdRE (P.PD K) (vrep r) τ) ∧
      ∀ a, (M.count a : ℤ) = multV (P.PD K) (vrep r) τ a := by
  obtain ⟨lo, hlo⟩ := Formalism.MainNotions.N.Pv.LocalLengthBound.rk_fildR_lo (P.PD K) (vrep r) τ
  obtain ⟨hi, hhi⟩ := Formalism.MainNotions.N.Pv.LocalLengthBound.rk_fildR_hi (P.PD K) (vrep r) τ
  have anti := Formalism.MainNotions.N.Pv.LocalLengthBound.rk_fildR_anti (P.PD K) (vrep r) τ
  haveI : ∀ a, FiniteDimensional ↥LL.1 ↥(FildR (P.PD K) (vrep r) τ a) := fun a =>
    Submodule.finiteDimensional_of_le (inf_le_left : FildR (P.PD K) (vrep r) τ a ≤ DdRE (P.PD K) (vrep r) τ)
  have nn : ∀ a, 0 ≤ multV (P.PD K) (vrep r) τ a := fun a => by
    have := Submodule.finrank_mono (anti (show a ≤ a + 1 by omega))
    unfold multV
    omega
  obtain ⟨lo₁, hl1, hl2⟩ : ∃ lo₁, lo₁ ≤ lo ∧ lo₁ ≤ hi := ⟨min lo hi, min_le_left _ _, min_le_right _ _⟩
  have zero : ∀ a, a ∉ Finset.Ico lo₁ hi → multV (P.PD K) (vrep r) τ a = 0 := fun a ha => by
    rw [Finset.mem_Ico, not_and_or, not_le, not_lt] at ha
    have e : FildR (P.PD K) (vrep r) τ a = FildR (P.PD K) (vrep r) τ (a + 1) := by
      rcases ha with ha | ha
      · exact (hlo a (by omega)).trans (hlo (a + 1) (by omega)).symm
      · exact (hhi a ha).trans (hhi (a + 1) (by omega)).symm
    unfold multV
    rw [e, sub_self]
  refine ⟨∑ a ∈ Finset.Ico lo₁ hi, Multiset.replicate (multV (P.PD K) (vrep r) τ a).toNat a, ?_, fun b => ?_⟩
  · rw [Multiset.card_sum]
    simp only [Multiset.card_replicate]
    have hs : ∑ a ∈ Finset.Ico lo₁ hi, multV (P.PD K) (vrep r) τ a =
        (finrank ↥LL.1 ↥(FildR (P.PD K) (vrep r) τ lo₁) : ℤ) - finrank ↥LL.1 ↥(FildR (P.PD K) (vrep r) τ hi) :=
      Formalism.MainNotions.N.Pv.LocalLengthBound.rk_sum_multV _ _ _ _ _ hl2
    have e1 : finrank ↥LL.1 ↥(FildR (P.PD K) (vrep r) τ lo₁) = finrank ↥LL.1 ↥(DdRE (P.PD K) (vrep r) τ) := by
      rw [hlo lo₁ hl1]
    have e2 : finrank ↥LL.1 ↥(FildR (P.PD K) (vrep r) τ hi) = 0 := Submodule.finrank_eq_zero.2 (hhi hi le_rfl)
    rw [e1, e2] at hs
    have : ((∑ a ∈ Finset.Ico lo₁ hi, (multV (P.PD K) (vrep r) τ a).toNat : ℕ) : ℤ) =
        (finrank ↥LL.1 ↥(DdRE (P.PD K) (vrep r) τ) : ℤ) := by
      push_cast
      rw [Finset.sum_congr rfl fun a _ => Int.toNat_of_nonneg (nn a), hs]
      simp
    exact_mod_cast this
  · rw [Multiset.count_sum']
    simp only [Multiset.count_replicate]
    rw [Finset.sum_ite_eq']
    by_cases hb : b ∈ Finset.Ico lo₁ hi
    · rw [if_pos hb, Int.toNat_of_nonneg (nn b)]
    · rw [if_neg hb, zero b hb]
      rfl

end Local

/- English proof (translation)
The claim follows from `GlobalTheory.PhtCompare.phtCmp`.
-/
theorem htCard : GlobalTheory.HeightCounting.HtCard := GlobalTheory.PhtCompare.phtCmp

end GlobalTheory.HtCardProof

end
