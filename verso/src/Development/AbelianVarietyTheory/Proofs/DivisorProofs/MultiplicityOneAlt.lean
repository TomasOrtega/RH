import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrActApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightModuleUnitaryFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFormOrthogonalComplementStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorActionIsLieActionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitaryTActStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorActionWeightDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiltrationMapEquivariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneratedModuleFiltrationExhaustiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiltrationStepFromSectionKernelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightInRangePlusSubmoduleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionOrthogonalKernelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightTensorRootShiftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CasimirLowerBoundOnStableSubspaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CasimirSectionSumIdentityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneratedSubmoduleHighestWeightStructureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiltrationStableAndIncreasingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockCasimirEqRealCasimirStatement

noncomputable section
open scoped TensorProduct

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.SteepMult

namespace GlobalTheory.SteepMult

/- English proof (translation)
Introduce `R S M Λ v hv hgen hsteep w hw`. Establish `hML : IsKLieAct M.act` using `fun Y Z _ _ => M.lie Y Z`. Take `⟨hfin, hlie, hwts, hvN, hgenN⟩` from `GlobalTheory.T.generated_submodule_highest_weight_structure R S M Λ v hv`. Establish `hN : KStable M.act (GlobalTheory.BlockReps.gen M.act v)` using `GlobalTheory.BlockReps.stable_gen (act := M.act) v`. Use `set N := GlobalTheory.BlockReps.gen M.act v with hNdef`.

Use `haveI : FiniteDimensional ℂ N := hfin`. Use `set A := restrAct M.act N hN with hA`. Use `set v₀ : N := ⟨v, GlobalTheory.BlockReps.mem_gen v⟩ with hv₀`. Take `⟨B, hB⟩` from `GlobalTheory.T.highest_weight_module_unitary_form R S N A Λ v₀ hlie hwts hvN hgenN`. Use `set c : ℚ := GlobalTheory.BlockReps.casVal Λ with hc`.

Establish `hcasN : ∀ x : N, GlobalTheory.BlockReps.casK A x = ((c : ℚ) : ℂ) • x`. Establish `hker` using `GlobalTheory.BlockReps.stable_ker (act := A) hlie ((c : ℚ) : ℂ) 1`. Establish `hv1 : v₀ ∈ LinearMap.ker ((GlobalTheory.BlockReps.casK A - ((c : ℚ) : ℂ) • 1) ^ 1)`. Rewrite using `[pow_one, LinearMap.mem_ker, LinearMap.sub_apply, GlobalTheory.BlockReps.casK_hw hlie hvN.2]`. Simplify using `[hc]`.

Establish `htop` using `GlobalTheory.BlockReps.gen_le hv1 hker`. Rewrite `htop` using `[hgenN]`. Introduce `x`. Use `htop (Submodule.mem_top (x := x))` as an intermediate fact. Rewrite `this` using `[pow_one, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]`.

Simplify using `using this`. Use `set P1 := (LinearMap.ker (phiN M.act N 1)).orthogonalBilin (formT 1 B) with hP1`. Establish `hU1` using `GlobalTheory.T.isUnitary_tAct_formT_of_isUnitary R S 1 N A B hB`. Establish `hpos : ∀ x ∈ P1, x ≠ 0 → ((((R + S : ℕ) : ℚ) + c : ℚ) : ℝ) * (formT 1 B x x).re < (formT 1 B x (GlobalTheory.BlockReps.casK (tAct 1 A) x)).re`. Establish `hL1` using `GlobalTheory.T.tensor_action_is_lie_action R S 1 N A hlie`.

Establish `hW1` using `GlobalTheory.T.tensor_action_weight_decomposition R S 1 N A hwts`. Establish `hkerS : KStable (tAct 1 A) (LinearMap.ker (phiN M.act N 1))` using `fun Z hZ x hx => by`. Rewrite `hx`, the goal using `[LinearMap.mem_ker]`. Rewrite using `[GlobalTheory.T.filtration_map_equivariant R S M N hN 1 Z hZ, hx, map_zero]`. Establish `hPS` using `(GlobalTheory.T.unitary_form_orthogonal_complement R S _ (tAct 1 A) (formT 1 B) hU1 _ hkerS).1`.

Use `GlobalTheory.T.casimir_lower_bound_on_stable_subspace R S _ (tAct 1 A) (formT 1 B) _ hL1 hW1 hU1 P1 hPS ?_` and prove the remaining obligations. Introduce `ν y hyP hy`. Take `⟨a, b, hab, rfl⟩` from `GlobalTheory.T.highest_weight_tensor_root_shift R S N A Λ v₀ hlie hwts hvN hgenN ν y hy`. Establish `hφ0 : phiN M.act N 1 y ≠ 0`. Introduce `h0`.

Establish `h1` using `(Submodule.mem_orthogonalBilin_iff.1 hyP) y (LinearMap.mem_ker.2 h0)`. Establish `hp` using `hU1.2.1 y hy.1`. Establish `h1' : formT 1 B y y = 0` using `h1`. Rewrite `hp` using `[h1']`. Simplify using `at hp`.

Establish `hhw : IsHW M.act (GlobalTheory.RealLift.addRoot Λ a b) (phiN M.act N 1 y)`. Use `⟨hφ0, ?_⟩` and prove the remaining obligations. Establish `hy2` using `GlobalTheory.TensorHW.mem_hw.1 hy.2`. Use `GlobalTheory.TensorHW.mem_hw.2 ⟨fun d => ?_, fun d e hde => ?_⟩` and prove the remaining obligations. Rewrite using `[← GlobalTheory.T.filtration_map_equivariant R S M N hN 1 _ (GlobalTheory.TensorHW.isKC_Eab (GlobalTheory.TensorHW.same_refl d)), hy2.1 d, map_smul]`.

Rewrite using `[← GlobalTheory.T.filtration_map_equivariant R S M N hN 1 _ (GlobalTheory.TensorHW.isKC_Eab (GlobalTheory.TensorHW.same_of_pos hde)), hy2.2 d e hde, map_zero]`. Use `hsteep a b hab _ hhw` as an intermediate fact. Rewrite using `[GlobalTheory.T.block_casimir_eq_real_casimir, hc, GlobalTheory.T.block_casimir_eq_real_casimir]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hno : ∀ (k : ℕ) (Ψ : (Fin (k + 1) → NC R S) → N), Ψ ≠ 0 → Ψ ∈ hwSub (tAct (k + 1) A) Λ → (∀ i g, section1 Ψ i g ∈ P1) → False`.

Introduce `k Ψ hΨ hhw hsec`. Use `set tm : ((Fin 1 → NC R S) → N) → ℝ := fun x => (formT 1 B x (GlobalTheory.BlockReps.casK (tAct 1 A) x)).re - ((R + S : ℕ) : ℝ) * (formT 1 B x x).re - (formT 1 B x (fun h => GlobalTheory.BlockReps.casK A (x h))).re with htm`. Establish `hsc : ∀ x : (Fin 1 → NC R S) → N, (formT 1 B x (fun h => GlobalTheory.BlockReps.casK A (x h))).re = (c : ℝ) * (formT 1 B x x).re`. Introduce `x`. Establish `e : (fun h => GlobalTheory.BlockReps.casK A (x h)) = ((c : ℚ) : ℂ) • x` using `funext fun h => hcasN _`.

Rewrite using `[e, map_smul, smul_eq_mul]`. Establish `: ((c : ℚ) : ℂ) = ((c : ℝ) : ℂ)` using `by push_cast; rfl`. Rewrite using `[this, Complex.re_ofReal_mul]`. Establish `hterm : ∀ x ∈ P1, 0 ≤ tm x ∧ (x ≠ 0 → 0 < tm x)`. Introduce `x hx`.

Establish `hpos' : x ≠ 0 → 0 < tm x` using `fun hne => by`. Use `hpos x hx hne` as an intermediate fact. Simplify using `only [htm, hsc]`. Move the coercions through the operations in `at this ⊢`. Combine the linear equalities and inequalities to obtain the conclusion.

Use `⟨?_, hpos'⟩` and prove the remaining obligations. Distinguish the cases in `h0 : x = 0`. Simplify using `[htm, h0]`. Conclude with `(hpos' h0).le`. Establish `hI` using `GlobalTheory.T.casimir_section_sum_identity R S (k + 1) N A B hB Ψ`.

Establish `hcasT : GlobalTheory.BlockReps.casK (tAct (k + 1) A) Ψ = ((c : ℚ) : ℂ) • Ψ` using `GlobalTheory.BlockReps.casK_hw (GlobalTheory.T.tensor_action_is_lie_action R S (k + 1) N A hlie) hhw`. Establish `hpt : (fun g => GlobalTheory.BlockReps.casK A (Ψ g)) = ((c : ℚ) : ℂ) • Ψ` using `funext fun g => hcasN _`. Rewrite `hI` using `[hcasT, hpt, sub_self, mul_zero]`. Take `⟨g₀, hg₀⟩` from `Function.ne_iff.1 hΨ`. Establish `hne : section1 Ψ 0 g₀ ≠ 0`.

Introduce `h`. Use `congrFun h (fun _ => g₀ 0)` as an intermediate fact. Simplify using `only [section1, Function.update_eq_self, Pi.zero_apply] at this`. Conclude with `hg₀ this`. Establish `hpos2 : 0 < ∑ i, ∑ g, tm (section1 Ψ i g)`.

Use `Finset.sum_pos' (fun i _ => Finset.sum_nonneg fun g _ => (hterm _ (hsec i g)).1) ⟨0, Finset.mem_univ _, ?_⟩` and prove the remaining obligations. Conclude with `Finset.sum_pos' (fun g _ => (hterm _ (hsec 0 g)).1) ⟨g₀, Finset.mem_univ _, (hterm _ (hsec 0 g₀)).2 hne⟩`. Conclude with `absurd hI (not_le.2 hpos2)`. Establish `hdesc : ∀ k, w ∈ filt M.act N k → w ∈ N`. Introduce `k`.

Proceed by induction on `k with`. Consider the case `zero => exact fun h => (GlobalTheory.T.filtration_stable_and_increasing R S M N hN 0).2.2 h`. Consider the case `succ k ih`. Introduce `hk`. Distinguish the cases in `hwk : w ∈ filt M.act N k`.

Conclude with `ih hwk`. It suffices to derive a contradiction. Take `⟨hFs, hFeq, -⟩` from `GlobalTheory.T.filtration_stable_and_increasing R S M N hN k`. Rewrite `hk` using `[hFeq, sup_comm]`. Take `⟨Ψ, hΨP, hΨ0, hΨhw⟩` from `GlobalTheory.T.exists_highestWeight_orthogonal_comap_of_mem_range_sup R S ((Fin (k + 1) → NC R S) → N) (tAct (k + 1) A) (formT (k + 1) B) M.V M.act (phiN M.act N (k + 1)) (filt M.act N k) Λ w (GlobalTheory.T.isUnitary_tAct_formT_of_isUnitary R S (k + 1) N A B hB) hFs (fun Z hZ x …`.

Conclude with `hno k Ψ hΨ0 hΨhw (GlobalTheory.T.section_orthogonal_kernel R S M N hN B k Ψ hΨP)`. Take `⟨k, hk⟩` from `GlobalTheory.T.generated_module_filtration_exhaustive R S M Λ v hv hgen w`. Establish `hwN` using `hdesc k hk`. Distinguish the cases in `hw0 : w = 0`. Conclude with `⟨0, by simp [hw0]⟩`.

Take `⟨-, hspan⟩` from `GlobalTheory.BlockReps.hw_unique hML hN (GlobalTheory.BlockReps.mem_gen v) hv hwN ⟨hw0, hw⟩`. Take `⟨d, hd⟩` from `Submodule.mem_span_singleton.1 hspan`. Conclude with `⟨d, hd.symm⟩`.
-/
theorem multOne : GlobalTheory.RealLift.MultOne := by
  intro R S M Λ v hv hgen hsteep w hw
  classical
  have hML : IsKLieAct M.act := fun Y Z _ _ => M.lie Y Z
  obtain ⟨hfin, hlie, hwts, hvN, hgenN⟩ := GlobalTheory.T.generated_submodule_highest_weight_structure R S M Λ v hv
  have hN : KStable M.act (GlobalTheory.BlockReps.gen M.act v) := GlobalTheory.BlockReps.stable_gen (act := M.act) v
  set N := GlobalTheory.BlockReps.gen M.act v with hNdef
  haveI : FiniteDimensional ℂ N := hfin
  set A := restrAct M.act N hN with hA
  set v₀ : N := ⟨v, GlobalTheory.BlockReps.mem_gen v⟩ with hv₀
  obtain ⟨B, hB⟩ := GlobalTheory.T.highest_weight_module_unitary_form R S N A Λ v₀ hlie hwts hvN hgenN
  set c : ℚ := GlobalTheory.BlockReps.casVal Λ with hc

  have hcasN : ∀ x : N, GlobalTheory.BlockReps.casK A x = ((c : ℚ) : ℂ) • x := by
    have hker := GlobalTheory.BlockReps.stable_ker (act := A) hlie ((c : ℚ) : ℂ) 1
    have hv1 : v₀ ∈ LinearMap.ker ((GlobalTheory.BlockReps.casK A - ((c : ℚ) : ℂ) • 1) ^ 1) := by
      rw [pow_one, LinearMap.mem_ker, LinearMap.sub_apply, GlobalTheory.BlockReps.casK_hw hlie hvN.2]
      simp [hc]
    have htop := GlobalTheory.BlockReps.gen_le hv1 hker
    rw [hgenN] at htop
    intro x
    have := htop (Submodule.mem_top (x := x))
    rw [pow_one, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at this
    simpa using this
  set P1 := (LinearMap.ker (phiN M.act N 1)).orthogonalBilin (formT 1 B) with hP1
  have hU1 := GlobalTheory.T.isUnitary_tAct_formT_of_isUnitary R S 1 N A B hB

  have hpos : ∀ x ∈ P1, x ≠ 0 → ((((R + S : ℕ) : ℚ) + c : ℚ) : ℝ) * (formT 1 B x x).re <
      (formT 1 B x (GlobalTheory.BlockReps.casK (tAct 1 A) x)).re := by
    have hL1 := GlobalTheory.T.tensor_action_is_lie_action R S 1 N A hlie
    have hW1 := GlobalTheory.T.tensor_action_weight_decomposition R S 1 N A hwts
    have hkerS : KStable (tAct 1 A) (LinearMap.ker (phiN M.act N 1)) := fun Z hZ x hx => by
      rw [LinearMap.mem_ker] at hx ⊢
      rw [GlobalTheory.T.filtration_map_equivariant R S M N hN 1 Z hZ, hx, map_zero]
    have hPS := (GlobalTheory.T.unitary_form_orthogonal_complement R S _ (tAct 1 A) (formT 1 B) hU1 _ hkerS).1
    refine GlobalTheory.T.casimir_lower_bound_on_stable_subspace R S _ (tAct 1 A) (formT 1 B) _ hL1 hW1 hU1 P1 hPS ?_
    intro ν y hyP hy
    obtain ⟨a, b, hab, rfl⟩ := GlobalTheory.T.highest_weight_tensor_root_shift R S N A Λ v₀ hlie hwts hvN hgenN ν y hy
    have hφ0 : phiN M.act N 1 y ≠ 0 := by
      intro h0
      have h1 := (Submodule.mem_orthogonalBilin_iff.1 hyP) y (LinearMap.mem_ker.2 h0)
      have hp := hU1.2.1 y hy.1
      have h1' : formT 1 B y y = 0 := h1
      rw [h1'] at hp
      simp at hp
    have hhw : IsHW M.act (GlobalTheory.RealLift.addRoot Λ a b) (phiN M.act N 1 y) := by
      refine ⟨hφ0, ?_⟩
      have hy2 := GlobalTheory.TensorHW.mem_hw.1 hy.2
      refine GlobalTheory.TensorHW.mem_hw.2 ⟨fun d => ?_, fun d e hde => ?_⟩
      · rw [← GlobalTheory.T.filtration_map_equivariant R S M N hN 1 _ (GlobalTheory.TensorHW.isKC_Eab (GlobalTheory.TensorHW.same_refl d)), hy2.1 d, map_smul]
      · rw [← GlobalTheory.T.filtration_map_equivariant R S M N hN 1 _ (GlobalTheory.TensorHW.isKC_Eab (GlobalTheory.TensorHW.same_of_pos hde)), hy2.2 d e hde, map_zero]
    have := hsteep a b hab _ hhw
    rw [GlobalTheory.T.block_casimir_eq_real_casimir, hc, GlobalTheory.T.block_casimir_eq_real_casimir]
    linarith

  have hno : ∀ (k : ℕ) (Ψ : (Fin (k + 1) → NC R S) → N), Ψ ≠ 0 → Ψ ∈ hwSub (tAct (k + 1) A) Λ →
      (∀ i g, section1 Ψ i g ∈ P1) → False := by
    intro k Ψ hΨ hhw hsec
    set tm : ((Fin 1 → NC R S) → N) → ℝ := fun x => (formT 1 B x (GlobalTheory.BlockReps.casK (tAct 1 A) x)).re -
        ((R + S : ℕ) : ℝ) * (formT 1 B x x).re - (formT 1 B x (fun h => GlobalTheory.BlockReps.casK A (x h))).re with htm
    have hsc : ∀ x : (Fin 1 → NC R S) → N, (formT 1 B x (fun h => GlobalTheory.BlockReps.casK A (x h))).re =
        (c : ℝ) * (formT 1 B x x).re := by
      intro x
      have e : (fun h => GlobalTheory.BlockReps.casK A (x h)) = ((c : ℚ) : ℂ) • x := funext fun h => hcasN _
      rw [e, map_smul, smul_eq_mul]
      have : ((c : ℚ) : ℂ) = ((c : ℝ) : ℂ) := by push_cast; rfl
      rw [this, Complex.re_ofReal_mul]
    have hterm : ∀ x ∈ P1, 0 ≤ tm x ∧ (x ≠ 0 → 0 < tm x) := by
      intro x hx
      have hpos' : x ≠ 0 → 0 < tm x := fun hne => by
        have := hpos x hx hne
        simp only [htm, hsc]
        push_cast at this ⊢
        linarith
      refine ⟨?_, hpos'⟩
      by_cases h0 : x = 0
      · simp [htm, h0]
      · exact (hpos' h0).le
    have hI := GlobalTheory.T.casimir_section_sum_identity R S (k + 1) N A B hB Ψ
    have hcasT : GlobalTheory.BlockReps.casK (tAct (k + 1) A) Ψ = ((c : ℚ) : ℂ) • Ψ :=
      GlobalTheory.BlockReps.casK_hw (GlobalTheory.T.tensor_action_is_lie_action R S (k + 1) N A hlie) hhw
    have hpt : (fun g => GlobalTheory.BlockReps.casK A (Ψ g)) = ((c : ℚ) : ℂ) • Ψ := funext fun g => hcasN _
    rw [hcasT, hpt, sub_self, mul_zero] at hI
    obtain ⟨g₀, hg₀⟩ := Function.ne_iff.1 hΨ
    have hne : section1 Ψ 0 g₀ ≠ 0 := by
      intro h
      have := congrFun h (fun _ => g₀ 0)
      simp only [section1, Function.update_eq_self, Pi.zero_apply] at this
      exact hg₀ this
    have hpos2 : 0 < ∑ i, ∑ g, tm (section1 Ψ i g) := by
      refine Finset.sum_pos' (fun i _ => Finset.sum_nonneg fun g _ => (hterm _ (hsec i g)).1) ⟨0, Finset.mem_univ _, ?_⟩
      exact Finset.sum_pos' (fun g _ => (hterm _ (hsec 0 g)).1) ⟨g₀, Finset.mem_univ _, (hterm _ (hsec 0 g₀)).2 hne⟩
    exact absurd hI (not_le.2 hpos2)

  have hdesc : ∀ k, w ∈ filt M.act N k → w ∈ N := by
    intro k
    induction k with
    | zero => exact fun h => (GlobalTheory.T.filtration_stable_and_increasing R S M N hN 0).2.2 h
    | succ k ih =>
      intro hk
      by_cases hwk : w ∈ filt M.act N k
      · exact ih hwk
      exfalso
      obtain ⟨hFs, hFeq, -⟩ := GlobalTheory.T.filtration_stable_and_increasing R S M N hN k
      rw [hFeq, sup_comm] at hk
      obtain ⟨Ψ, hΨP, hΨ0, hΨhw⟩ := GlobalTheory.T.exists_highestWeight_orthogonal_comap_of_mem_range_sup R S ((Fin (k + 1) → NC R S) → N) (tAct (k + 1) A) (formT (k + 1) B) M.V
        M.act (phiN M.act N (k + 1)) (filt M.act N k) Λ w (GlobalTheory.T.isUnitary_tAct_formT_of_isUnitary R S (k + 1) N A B hB) hFs
        (fun Z hZ x => GlobalTheory.T.filtration_map_equivariant R S M N hN (k + 1) Z hZ x) hk hw hwk
      exact hno k Ψ hΨ0 hΨhw (GlobalTheory.T.section_orthogonal_kernel R S M N hN B k Ψ hΨP)
  obtain ⟨k, hk⟩ := GlobalTheory.T.generated_module_filtration_exhaustive R S M Λ v hv hgen w
  have hwN := hdesc k hk
  by_cases hw0 : w = 0
  · exact ⟨0, by simp [hw0]⟩
  obtain ⟨-, hspan⟩ := GlobalTheory.BlockReps.hw_unique hML hN (GlobalTheory.BlockReps.mem_gen v) hv hwN ⟨hw0, hw⟩
  obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.1 hspan
  exact ⟨d, hd.symm⟩

end GlobalTheory.SteepMult

end
