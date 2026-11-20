import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistablePeriodRingGaloisInvariantsIffConstStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistableLinearFormOnConstantsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MonVEqZeroIffExistsCrisInclStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusTensorCrisToSemistableCommStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSemistableTensorPairingOfDualStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistableDieudonneModuleSpansTensorPeriodRingStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory.PMon

/- English proof (translation)
Rewrite `hx`, the goal using `[mem_Dst]`. Introduce `g`. Establish `h : stRep P ρ g * onB P ℚ_[l] V (LinearMap.mulLeft ℚ_[l] a) = onB P ℚ_[l] V (LinearMap.mulLeft ℚ_[l] a) * stRep P ρ g` using `end_ext P fun v b => by`. Simplify using `only [End.mul_apply, onB_tmul, stRep_tmul, LinearMap.mulLeft_apply, map_mul, ha]`. Rewrite using `[← End.mul_apply, h, End.mul_apply, hx]`.
-/
theorem onB_mulLeft_mem_Dst_of_fixed {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K : FinExt l}
    {V : Type} [AddCommGroup V] [Module ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V)
    (a : Bst P) (ha : ∀ g : ↥(GK K), actSt P (g : GQ l) a = a) (x : V ⊗[ℚ_[l]] Bst P)
    (hx : x ∈ Dst P ρ) : onB P ℚ_[l] V (LinearMap.mulLeft ℚ_[l] a) x ∈ Dst P ρ := by
  rw [mem_Dst] at hx ⊢
  intro g
  have h : stRep P ρ g * onB P ℚ_[l] V (LinearMap.mulLeft ℚ_[l] a) =
      onB P ℚ_[l] V (LinearMap.mulLeft ℚ_[l] a) * stRep P ρ g :=
    end_ext P fun v b => by
      simp only [End.mul_apply, onB_tmul, stRep_tmul, LinearMap.mulLeft_apply, map_mul, ha]
  rw [← End.mul_apply, h, End.mul_apply, hx]

/- English proof (translation)
Introduce `l _ P AI T K V _ _ _ V' _ _ _ ρ ρ' m hd hs`. Take `⟨pr, hφ, hN, hg, hmul, hnd⟩` from `GlobalTheory.T.exists_semistable_tensor_pairing_of_dual l P K V V' ρ ρ' m hd`. Take `⟨lam, hlφ, hlnd⟩` from `GlobalTheory.T.exists_linearForm_semistable_extending_trace l P K`. Set `W` to `Dcris (P.PD K) ρ' ⊓ LinearMap.ker (φVB (P.PD K) (LL := ℚ_[l]) (V := V') - LinearMap.id)`. Set `j : ↥W →ₗ[ℚ_[l]] V' ⊗[ℚ_[l]] Bst P` to `(crisIncl P ℚ_[l] V') ∘ₗ W.subtype`.

Establish `hj : ∀ w : ↥W, j w = crisIncl P ℚ_[l] V' (w : V' ⊗[ℚ_[l]] P.R.B)` using `fun _ => rfl`. Establish `hjg : ∀ (w : ↥W) g, stRep P ρ' g (j w) = j w`. Introduce `w g`. Establish `h1` using `w.2.1`. Establish `h2 : actVB (P.PD K) ρ' g (w : V' ⊗[ℚ_[l]] P.R.B) = w`.

Use `(Submodule.mem_iInf _).mp h1 g` as an intermediate fact. Rewrite `this` using `[LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]`. Then use the resulting hypothesis. Rewrite using `[hj, stRep_crisIncl, h2]`. Establish `hjN : ∀ w : ↥W, monV P ℚ_[l] V' (j w) = 0` using `fun w => (GlobalTheory.T.monV_eq_zero_iff_mem_range_crisIncl' l P V' _).mpr ⟨_, (hj w).symm⟩`. Establish `hjφ : ∀ w : ↥W, phiV P ℚ_[l] V' (j w) = j w`.

Introduce `w`. Establish `h2 : φVB (P.PD K) (LL` using `ℚ_[l]) (V := V') (w : V' ⊗[ℚ_[l]] P.R.B) = w := by`. Use `w.2.2` as an intermediate fact. Rewrite `this` using `[SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]`. Then use the resulting hypothesis. Rewrite using `[hj, GlobalTheory.T.frobeniusTensor_crisToSemistable_comm l P K, h2]`.

Establish `hinv : ∀ x ∈ Dst P ρ, ∀ w : ↥W, ∃ c : ↥(K0 K), Polynomial.C P.tB * pr x (j w) = Polynomial.C (algebraMap ↥(K0 K) P.R.B c)`. Introduce `x hx w`. Use `(GlobalTheory.T.semistablePeriodRing_galois_invariants_iff_const l P AI T K _).mp fun g => ?_` and prove the remaining obligations. Establish `h1` using `hg g x (j w)`. Rewrite `h1` using `[(mem_Dst P ρ).mp hx g, hjg]`.

Rewrite using `[map_mul, actSt_C, localPrime_galoisAction_periodT, ← Polynomial.smul_C, smul_mul_assoc, ← mul_smul_comm, ← h1]`. Set `B : V ⊗[ℚ_[l]] Bst P →ₗ[ℚ_[l]] ↥W →ₗ[ℚ_[l]] ℚ_[l]` to `(pr.compl₂ j).compr₂ (lam ∘ₗ LinearMap.mulLeft ℚ_[l] (Polynomial.C P.tB))`. Establish `hB : ∀ x w, B x w = lam (Polynomial.C P.tB * pr x (j w))` using `fun _ _ => rfl`. Use `⟨B, fun x hx w => ?_, fun x hx w => ?_, fun w hw => ?_⟩` and prove the remaining obligations. Take `⟨c, hc⟩` from `hinv x hx w`.

Establish `h1` using `hN x (j w)`. Rewrite `h1` using `[hjN, map_zero, add_zero]`. Rewrite using `[hB, h1, ← monSt_C_mul, hc, (monSt_eq_zero_iff P _).mpr ⟨_, rfl⟩, map_zero]`. Take `⟨c, hc⟩` from `hinv x hx w`. Establish `h1` using `hφ x (j w)`.

Rewrite `h1` using `[hjφ]`. Rewrite using `[hB, hB, map_smul, LinearMap.smul_apply, h1, mul_smul_comm, ← smul_mul_assoc, Polynomial.smul_C, ← localPrime_frobenius_periodT, ← phiSt_C, ← map_mul, hc, hlφ]`. Establish `h0 : ∀ x ∈ Dst P ρ, pr x (j w) = 0`. Introduce `x hx`. Take `⟨c, hc⟩` from `hinv x hx w`.

Establish `hc0 : c = 0`. Use `hlnd c fun c' => ?_` and prove the remaining obligations. Establish `h2` using `hw _ (onB_mulLeft_mem_Dst_of_fixed P ρ _ ((GlobalTheory.T.semistablePeriodRing_galois_invariants_iff_const l P AI T K _).mpr ⟨c', rfl⟩) x hx)`. Rewrite `h2` using `[hB, hmul, mul_left_comm, hc]`. Conclude with `h2`.

Rewrite `hc` using `[hc0, map_zero, map_zero]`. Conclude with `((isUnit_tB P).map Polynomial.C).mul_right_eq_zero.mp hc`. Establish `h1 : j w = 0`. Use `hnd _ fun v => ?_` and prove the remaining obligations. Take `⟨k, a, x, hx, hv⟩` from `GlobalTheory.T.semistableDieudonneModule_spans_tensor_periodRing l P AI T K V ρ hs v`.

Rewrite using `[hv, map_sum, LinearMap.sum_apply]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hmul, h0 _ (hx i), mul_zero]`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `crisIncl_injective P (LL := ℚ_[l])` to reduce the goal to its premises.

Rewrite using `[← hj, h1]`. Simplify using the standard rewrite rules.
-/
theorem exists_pairing_Dst_Dcris_phi_one : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] (V' : Type) [AddCommGroup V'] [Module ℚ_[l] V'] [FiniteDimensional ℚ_[l] V'] (ρ : Representation ℚ_[l] ↥(GK K) V) (ρ' : Representation ℚ_[l] ↥(GK K) V') (m : V →ₗ[ℚ_[l]] V' →ₗ[ℚ_[l]] ℚ_[l]), IsDual1 (P.PD K) ρ ρ' m → IsSst P ρ → ∃ B : V ⊗[ℚ_[l]] Bst P →ₗ[ℚ_[l]] ↥(Dcris (P.PD K) ρ' ⊓ LinearMap.ker (φVB (P.PD K) (LL := ℚ_[l]) (V := V') - LinearMap.id)) →ₗ[ℚ_[l]] ℚ_[l], (∀ x ∈ Dst P ρ, ∀ w, B (monV P ℚ_[l] V x) w = 0) ∧ (∀ x ∈ Dst P ρ, ∀ w, B ((l : ℚ_[l]) • phiV P ℚ_[l] V x) w = B x w) ∧ ∀ w, (∀ x ∈ Dst P ρ, B x w = 0) → w = 0 := by
  intro l _ P AI T K V _ _ _ V' _ _ _ ρ ρ' m hd hs
  obtain ⟨pr, hφ, hN, hg, hmul, hnd⟩ := GlobalTheory.T.exists_semistable_tensor_pairing_of_dual l P K V V' ρ ρ' m hd
  obtain ⟨lam, hlφ, hlnd⟩ := GlobalTheory.T.exists_linearForm_semistable_extending_trace l P K
  let W := Dcris (P.PD K) ρ' ⊓ LinearMap.ker (φVB (P.PD K) (LL := ℚ_[l]) (V := V') - LinearMap.id)
  let j : ↥W →ₗ[ℚ_[l]] V' ⊗[ℚ_[l]] Bst P := (crisIncl P ℚ_[l] V') ∘ₗ W.subtype
  have hj : ∀ w : ↥W, j w = crisIncl P ℚ_[l] V' (w : V' ⊗[ℚ_[l]] P.R.B) := fun _ => rfl
  have hjg : ∀ (w : ↥W) g, stRep P ρ' g (j w) = j w := by
    intro w g
    have h1 := w.2.1
    have h2 : actVB (P.PD K) ρ' g (w : V' ⊗[ℚ_[l]] P.R.B) = w := by
      have := (Submodule.mem_iInf _).mp h1 g
      rwa [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at this
    rw [hj, stRep_crisIncl, h2]
  have hjN : ∀ w : ↥W, monV P ℚ_[l] V' (j w) = 0 := fun w =>
    (GlobalTheory.T.monV_eq_zero_iff_mem_range_crisIncl' l P V' _).mpr ⟨_, (hj w).symm⟩
  have hjφ : ∀ w : ↥W, phiV P ℚ_[l] V' (j w) = j w := by
    intro w
    have h2 : φVB (P.PD K) (LL := ℚ_[l]) (V := V') (w : V' ⊗[ℚ_[l]] P.R.B) = w := by
      have := w.2.2
      rwa [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
        sub_eq_zero] at this
    rw [hj, GlobalTheory.T.frobeniusTensor_crisToSemistable_comm l P K, h2]
  have hinv : ∀ x ∈ Dst P ρ, ∀ w : ↥W, ∃ c : ↥(K0 K), Polynomial.C P.tB * pr x (j w) =
      Polynomial.C (algebraMap ↥(K0 K) P.R.B c) := by
    intro x hx w
    refine (GlobalTheory.T.semistablePeriodRing_galois_invariants_iff_const l P AI T K _).mp fun g => ?_
    have h1 := hg g x (j w)
    rw [(mem_Dst P ρ).mp hx g, hjg] at h1
    rw [map_mul, actSt_C, localPrime_galoisAction_periodT, ← Polynomial.smul_C, smul_mul_assoc, ← mul_smul_comm, ← h1]
  let B : V ⊗[ℚ_[l]] Bst P →ₗ[ℚ_[l]] ↥W →ₗ[ℚ_[l]] ℚ_[l] :=
    (pr.compl₂ j).compr₂ (lam ∘ₗ LinearMap.mulLeft ℚ_[l] (Polynomial.C P.tB))
  have hB : ∀ x w, B x w = lam (Polynomial.C P.tB * pr x (j w)) := fun _ _ => rfl
  refine ⟨B, fun x hx w => ?_, fun x hx w => ?_, fun w hw => ?_⟩
  · obtain ⟨c, hc⟩ := hinv x hx w
    have h1 := hN x (j w)
    rw [hjN, map_zero, add_zero] at h1
    rw [hB, h1, ← monSt_C_mul, hc, (monSt_eq_zero_iff P _).mpr ⟨_, rfl⟩, map_zero]
  · obtain ⟨c, hc⟩ := hinv x hx w
    have h1 := hφ x (j w)
    rw [hjφ] at h1
    rw [hB, hB, map_smul, LinearMap.smul_apply, h1, mul_smul_comm, ← smul_mul_assoc,
      Polynomial.smul_C, ← localPrime_frobenius_periodT, ← phiSt_C, ← map_mul, hc, hlφ]
  · have h0 : ∀ x ∈ Dst P ρ, pr x (j w) = 0 := by
      intro x hx
      obtain ⟨c, hc⟩ := hinv x hx w
      have hc0 : c = 0 := by
        refine hlnd c fun c' => ?_
        have h2 := hw _ (onB_mulLeft_mem_Dst_of_fixed P ρ _
          ((GlobalTheory.T.semistablePeriodRing_galois_invariants_iff_const l P AI T K _).mpr ⟨c', rfl⟩) x hx)
        rw [hB, hmul, mul_left_comm, hc] at h2
        exact h2
      rw [hc0, map_zero, map_zero] at hc
      exact ((isUnit_tB P).map Polynomial.C).mul_right_eq_zero.mp hc
    have h1 : j w = 0 := by
      refine hnd _ fun v => ?_
      obtain ⟨k, a, x, hx, hv⟩ := GlobalTheory.T.semistableDieudonneModule_spans_tensor_periodRing l P AI T K V ρ hs v
      rw [hv, map_sum, LinearMap.sum_apply]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [hmul, h0 _ (hx i), mul_zero]
    apply Subtype.ext
    apply crisIncl_injective P (LL := ℚ_[l])
    rw [← hj, h1]
    simp

end GlobalTheory.PMon
