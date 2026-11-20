import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.InvariantsGenerators
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.JSmul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleQuotientKerIffFullLattices
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTopDataOfSlotHyps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleClassesPropsOfFlatCoefficient
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleOfSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleStd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineSumsTwistsCharactersExpectedJumps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralCyclotomicChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankDcrisLetterDeRhamComponentEqDim
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvrComplete
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.RkMultVOfNotJump
open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions
set_option synthInstance.maxHeartbeats 400000
open ReciprocityTheory.Def (Z1 B1 H1)
open TensorProduct

namespace GlobalTheory.Per.LetterJumps

/- English proof (translation)
Introduce `l _ P AI hT H K LL hA V _ _ _ _ _ ρ U hC hU i`. Take `⟨T⟩` from `hT`. Use `haveI := LL.2`. Use `haveI := (P.PD K).finK`. Establish `e : K0 K = K.1` using `inf_eq_left.2 hA.1`.

Set `eK : ↥K.1 ≃ₐ[ℚ_[l]] ↥(K0 K)` to `IntermediateField.equivOfEq e.symm`. Set `τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1` to `((H.W K 1 LL hA.2.2).emb i).comp eK.toAlgHom`. Establish `hτ : tableLineDegreeTwo.Over (H.W K 1 LL hA.2.2).emb i τ`. Use `AlgHom.ext fun x => ?_` and prove the remaining obligations. Use `show (H.W K 1 LL hA.2.2).emb i (eK (algebraMap ↥(K0 K) ↥K.1 x)) = (H.W K 1 LL hA.2.2).emb i x`.

Use `congr 1`. Establish `hc : Nat.card (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) = Module.finrank ℚ_[l] ↥K.1`. Rewrite using `[← Nat.card_congr ((IntermediateField.equivOfEq e).arrowCongr (AlgEquiv.refl : ↥LL.1 ≃ₐ[ℚ_[l]] ↥LL.1)), ← Nat.card_congr (Equiv.ofBijective _ (H.W K 1 LL hA.2.2).emb_bij), Nat.card_zmod]`. Conclude with `(IntermediateField.equivOfEq e).toLinearEquiv.finrank_eq`. Establish `hdim` using `(GlobalTheory.Per.LetterDim.tied_letter_component_finrank l P AI T K LL V ρ).2 hc (GlobalTheory.TopSteps.CrysRules.isDR T K LL ρ hC) τ`.

Use `haveI := (GlobalTheory.Per.FontaineBound.ddR_finite_le (P.PD K) (GlobalTheory.RegularRing.isField_of_tied T) ρ).1`. Use `haveI : FiniteDimensional ↥LL.1 ↥(DdRE (P.PD K) ρ τ) := Submodule.finiteDimensional_of_le (S₂ := DdR (P.PD K) ρ) inf_le_left`. Take `⟨lo, hlo⟩` from `Formalism.MainNotions.N.Pv.LocalLengthBound.rk_fildR_lo (P.PD K) ρ τ`. Take `⟨hi, hhi⟩` from `Formalism.MainNotions.N.Pv.LocalLengthBound.rk_fildR_hi (P.PD K) ρ τ`. Take `⟨b0, hb0⟩` from `(U i).toFinset.bddBelow`.

Take `⟨b1, hb1⟩` from `(U i).toFinset.bddAbove`. Take `⟨m, hm1, hm2, hm3⟩ : ∃ m : ℤ, m ≤ lo ∧ m ≤ b0 ∧ m ≤ hi` from `⟨min (min lo b0) hi, by omega, by omega, by omega⟩`. Take `⟨k, hk1, hk2⟩ : ∃ k : ℤ, hi ≤ k ∧ b1 < k` from `⟨max hi (b1 + 1), by omega, by omega⟩`. Establish `hmk : m ≤ k` using `by omega`. Establish `hsum` using `Formalism.MainNotions.N.Pv.LocalLengthBound.rk_sum_multV (P.PD K) ρ τ m k hmk`.

Rewrite `hsum` using `[hlo m hm1, hhi k hk1, finrank_bot, Nat.cast_zero, sub_zero, hdim]`. Establish `hsub : (U i).toFinset ⊆ Finset.Ico m k` using `fun a ha => by`. Establish `h0` using `hb0 (Finset.mem_coe.2 ha)`. Establish `h1` using `hb1 (Finset.mem_coe.2 ha)`. Rewrite using `[Finset.mem_Ico]`.

Use linear arithmetic over natural numbers and integers. Establish `hcnt : ∑ a ∈ Finset.Ico m k, ((U i).count a : ℤ) = (Multiset.card (U i) : ℤ)`. Rewrite using `[← Multiset.toFinset_sum_count_eq, Nat.cast_sum]`. Conclude with `(Finset.sum_subset hsub fun a _ ha => by`. Rewrite `ha` using `[Multiset.mem_toFinset]`.

Rewrite using `[Multiset.count_eq_zero.2 ha, Nat.cast_zero]).symm`. Use `(Finset.sum_congr rfl fun a _ => hU i τ hτ a).symm.trans hsum` as an intermediate fact. Rewrite `this` using `[hcnt]`. Conclude with `this` after adjusting the coercions.
-/
theorem card_jumps_letter : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (H : LocHW l P) (K LL : FinExt l) (hA : CaseA K LL) (V : Type) [AddCommGroup V] [Module ↥LL.1 V]
      [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V]
      (ρ : Representation ↥LL.1 ↥(GK K) V) (U : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Multiset ℤ),
      IsCrys (P.PD K) ρ →
      (∀ i τ, tableLineDegreeTwo.Over (H.W K 1 LL hA.2.2).emb i τ → ∀ a, multV (P.PD K) ρ τ a = (U i).count a) →
      ∀ i, Multiset.card (U i) = Module.finrank ↥LL.1 V := by
  intro l _ P AI hT H K LL hA V _ _ _ _ _ ρ U hC hU i
  classical
  obtain ⟨T⟩ := hT
  haveI := LL.2
  haveI := (P.PD K).finK
  have e : K0 K = K.1 := inf_eq_left.2 hA.1
  let eK : ↥K.1 ≃ₐ[ℚ_[l]] ↥(K0 K) := IntermediateField.equivOfEq e.symm
  let τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1 := ((H.W K 1 LL hA.2.2).emb i).comp eK.toAlgHom
  have hτ : tableLineDegreeTwo.Over (H.W K 1 LL hA.2.2).emb i τ := by
    refine AlgHom.ext fun x => ?_
    show (H.W K 1 LL hA.2.2).emb i (eK (algebraMap ↥(K0 K) ↥K.1 x)) = (H.W K 1 LL hA.2.2).emb i x
    congr 1
  have hc : Nat.card (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) = Module.finrank ℚ_[l] ↥K.1 := by
    rw [← Nat.card_congr ((IntermediateField.equivOfEq e).arrowCongr (AlgEquiv.refl : ↥LL.1 ≃ₐ[ℚ_[l]] ↥LL.1)),
      ← Nat.card_congr (Equiv.ofBijective _ (H.W K 1 LL hA.2.2).emb_bij), Nat.card_zmod]
    exact (IntermediateField.equivOfEq e).toLinearEquiv.finrank_eq
  have hdim := (GlobalTheory.Per.LetterDim.tied_letter_component_finrank l P AI T K LL V ρ).2 hc
    (GlobalTheory.TopSteps.CrysRules.isDR T K LL ρ hC) τ
  haveI := (GlobalTheory.Per.FontaineBound.ddR_finite_le (P.PD K) (GlobalTheory.RegularRing.isField_of_tied T) ρ).1
  haveI : FiniteDimensional ↥LL.1 ↥(DdRE (P.PD K) ρ τ) :=
    Submodule.finiteDimensional_of_le (S₂ := DdR (P.PD K) ρ) inf_le_left
  obtain ⟨lo, hlo⟩ := Formalism.MainNotions.N.Pv.LocalLengthBound.rk_fildR_lo (P.PD K) ρ τ
  obtain ⟨hi, hhi⟩ := Formalism.MainNotions.N.Pv.LocalLengthBound.rk_fildR_hi (P.PD K) ρ τ
  obtain ⟨b0, hb0⟩ := (U i).toFinset.bddBelow
  obtain ⟨b1, hb1⟩ := (U i).toFinset.bddAbove
  obtain ⟨m, hm1, hm2, hm3⟩ : ∃ m : ℤ, m ≤ lo ∧ m ≤ b0 ∧ m ≤ hi :=
    ⟨min (min lo b0) hi, by omega, by omega, by omega⟩
  obtain ⟨k, hk1, hk2⟩ : ∃ k : ℤ, hi ≤ k ∧ b1 < k := ⟨max hi (b1 + 1), by omega, by omega⟩
  have hmk : m ≤ k := by omega
  have hsum := Formalism.MainNotions.N.Pv.LocalLengthBound.rk_sum_multV (P.PD K) ρ τ m k hmk
  rw [hlo m hm1, hhi k hk1, finrank_bot, Nat.cast_zero, sub_zero, hdim] at hsum
  have hsub : (U i).toFinset ⊆ Finset.Ico m k := fun a ha => by
    have h0 := hb0 (Finset.mem_coe.2 ha)
    have h1 := hb1 (Finset.mem_coe.2 ha)
    rw [Finset.mem_Ico]
    omega
  have hcnt : ∑ a ∈ Finset.Ico m k, ((U i).count a : ℤ) = (Multiset.card (U i) : ℤ) := by
    rw [← Multiset.toFinset_sum_count_eq, Nat.cast_sum]
    exact (Finset.sum_subset hsub fun a _ ha => by
      rw [Multiset.mem_toFinset] at ha
      rw [Multiset.count_eq_zero.2 ha, Nat.cast_zero]).symm
  have := (Finset.sum_congr rfl fun a _ => hU i τ hτ a).symm.trans hsum
  rw [hcnt] at this
  exact_mod_cast this

end GlobalTheory.Per.LetterJumps
