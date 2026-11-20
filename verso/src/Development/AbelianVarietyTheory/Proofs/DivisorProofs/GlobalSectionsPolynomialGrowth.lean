import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPowVanishingIdealLeAnnihilator
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SupportPushforwardSubschemeSubset
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TensOfForallIsPsEff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowLeGlobalSectionsDimLineBundlePow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SheafCohomologyDimTwistCutInequalitiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AsymptoticRiemannRochAmpleCoherentStatement

set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

/- English proof (translation)
Proceed by induction on `j with`. Consider the case `zero`. Introduce `M M' hM hM' e`. Take `⟨e⟩` from `nonempty_twist_iso_of_cls_eq F hM hM' (by simpa using e)`. Conclude with `(hdim_congr k 0 e).ge`.

Consider the case `succ j ih`. Introduce `M M' hM hM' e`. Take `⟨N, hN, eN⟩` from `cls_surj (cls M' hM' + j • cls B hB)`. Conclude with `(ih N M' hN hM' eN).trans (GlobalTheory.T.sheafCohomologyDim_twist_cut_inequalities k X hX F B M N hB hM hN s hs (by rw [e, eN, succ_nsmul, add_assoc])).2.2`.
-/
theorem hdim_twist_zero_le_of_cls_eq_add_nsmul (k : Type) [Field k] [Infinite k] (X : Scheme.{0})
    [Algebra k Γ(X, ⊤)] (hX : IsProjOver (strHom k X)) (F : X.Modules) [IsFiniteQC F]
    (B : LB X) (hB : B.IsLB) (s : B.Sec) (hs : Mono (cutHom F hB s)) (j : ℕ) :
    ∀ (M M' : LB X) (hM : M.IsLB) (hM' : M'.IsLB), cls M hM = cls M' hM' + j • cls B hB →
      hdim k (twist F M') 0 ≤ hdim k (twist F M) 0 := by
  induction j with
  | zero =>
    intro M M' hM hM' e
    obtain ⟨e⟩ := nonempty_twist_iso_of_cls_eq F hM hM' (by simpa using e)
    exact (hdim_congr k 0 e).ge
  | succ j ih =>
    intro M M' hM hM' e
    obtain ⟨N, hN, eN⟩ := cls_surj (cls M' hM' + j • cls B hB)
    exact (ih N M' hN hM' eN).trans
      (GlobalTheory.T.sheafCohomologyDim_twist_cut_inequalities k X hX F B M N hB hM hN s hs (by rw [e, eN, succ_nsmul, add_assoc])).2.2

/- English proof (translation)
Introduce `k _ _ X _ hX d L hL F _ hF`. Use `isNoetherian_of_isProjOver hX` as an intermediate fact. Take `⟨-, A, hA⟩` from `isProper_and_exists_isAmpleLB_of_isProjOver hX`. Take `⟨D, hD, eD⟩` from `cls_surj (-cls L hL)`. Take `⟨n, hn, hn1⟩` from `((tendsto_natCast_atTop_atTop (R := ℤ).eventually (hA.eventually_exists_mono_cutHom hD F)).and (eventually_ge_atTop 1)).exists`.

Take `⟨B, hB, eB⟩` from `cls_surj (cls D hD + (n : ℤ) • cls A hA.isLB)`. Take `⟨s, hs⟩` from `hn B hB eB`. Establish `hH : IsAmpleLB (lbPow A n)` using `(isAmpleLB_pow_iff hA.isLB hn1).2 hA`. Establish `h₁ : ∀ m : ℕ, hdim k (twist F (lbPow L m)) 0 ≤ hdim k (twist F (lbPow (lbPow A n) m)) 0` using `fun m => hdim_twist_zero_le_of_cls_eq_add_nsmul k X hX F B hB s hs m _ _ (isLB_lbPow hH.isLB m) (isLB_lbPow hL m) (by`. Rewrite using `[cls_lbPow hH.isLB, cls_lbPow hA.isLB, cls_lbPow hL, eB, eD, natCast_zsmul, ← nsmul_add, add_neg_cancel_left])`.

Take `⟨C, m₀, hC⟩` from `GlobalTheory.T.asymptotic_riemannRoch_ample_coherent k X hX d F hF _ hH`. Use `set a := interNum k F (fun _ : Fin d => lbPow A n)`. Use `set h : ℕ → ℕ := fun m => hdim k (twist F (lbPow (lbPow A n) m)) 0 with hh`. Use `⟨a.natAbs + C * d + ∑ i ∈ Finset.range m₀, h i, fun m => (h₁ m).trans ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `h m ≤ _`.

Establish `hp : 1 ≤ (m + 1) ^ d` using `Nat.one_le_pow _ _ (Nat.succ_pos m)`. Break down `lt_or_ge m m₀ with hm | hm` into its components or cases. Establish `: h m ≤ ∑ i ∈ Finset.range m₀, h i` using `Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 hm)`. Conclude with `(this.trans (Nat.le_add_left _ _)).trans (Nat.le_mul_of_pos_right _ hp)`. Establish `h₂ : (d.factorial : ℤ) * (h m : ℤ) - a * (m : ℤ) ^ d ≤ C * ((d : ℤ) * ((m : ℤ) + 1) ^ (d - 1))` using `(abs_le.1 (hC m hm)).2`.

Establish `h₃ : (h m : ℤ) ≤ (d.factorial : ℤ) * (h m : ℤ)` using `le_mul_of_one_le_left (by positivity) (by exact_mod_cast d.factorial_pos)`. Establish `h₄ : a * (m : ℤ) ^ d ≤ |a| * ((m : ℤ) + 1) ^ d` using `(mul_le_mul_of_nonneg_right (le_abs_self a) (by positivity)).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) d) (abs_nonneg a))`. Establish `h₅ : (C : ℤ) * ((d : ℤ) * ((m : ℤ) + 1) ^ (d - 1)) ≤ C * ((d : ℤ) * ((m : ℤ) + 1) ^ d)` using `by gcongr`. Establish `: (0 : ℤ) ≤ m` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion.

Conclude with `Nat.sub_le _ _`. Establish `h₆ : (h m : ℤ) ≤ ((a.natAbs + C * d) * (m + 1) ^ d : ℕ)`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `(by exact_mod_cast h₆ : h m ≤ _).trans (Nat.mul_le_mul_right _ (Nat.le_add_right _ _))`.
-/
theorem exists_hdim_twist_lbPow_zero_le :
    ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k X) → ∀ (d : ℕ) (L : LB X), L.IsLB → ∀ (F : X.Modules) [IsFiniteQC F], suppDim F ≤ (d : ℕ) → ∃ C : ℕ, ∀ m : ℕ, hdim k (twist F (lbPow L m)) 0 ≤ C * (m + 1) ^ d := by
  intro k _ _ X _ hX d L hL F _ hF
  have := isNoetherian_of_isProjOver hX
  obtain ⟨-, A, hA⟩ := isProper_and_exists_isAmpleLB_of_isProjOver hX
  obtain ⟨D, hD, eD⟩ := cls_surj (-cls L hL)
  obtain ⟨n, hn, hn1⟩ := ((tendsto_natCast_atTop_atTop (R := ℤ).eventually
    (hA.eventually_exists_mono_cutHom hD F)).and (eventually_ge_atTop 1)).exists
  obtain ⟨B, hB, eB⟩ := cls_surj (cls D hD + (n : ℤ) • cls A hA.isLB)
  obtain ⟨s, hs⟩ := hn B hB eB
  have hH : IsAmpleLB (lbPow A n) := (isAmpleLB_pow_iff hA.isLB hn1).2 hA
  have h₁ : ∀ m : ℕ, hdim k (twist F (lbPow L m)) 0 ≤ hdim k (twist F (lbPow (lbPow A n) m)) 0 :=
    fun m => hdim_twist_zero_le_of_cls_eq_add_nsmul k X hX F B hB s hs m _ _
      (isLB_lbPow hH.isLB m) (isLB_lbPow hL m) (by
        rw [cls_lbPow hH.isLB, cls_lbPow hA.isLB, cls_lbPow hL, eB, eD, natCast_zsmul, ← nsmul_add,
          add_neg_cancel_left])
  obtain ⟨C, m₀, hC⟩ := GlobalTheory.T.asymptotic_riemannRoch_ample_coherent k X hX d F hF _ hH
  set a := interNum k F (fun _ : Fin d => lbPow A n)
  set h : ℕ → ℕ := fun m => hdim k (twist F (lbPow (lbPow A n) m)) 0 with hh
  refine ⟨a.natAbs + C * d + ∑ i ∈ Finset.range m₀, h i, fun m => (h₁ m).trans ?_⟩
  change h m ≤ _
  have hp : 1 ≤ (m + 1) ^ d := Nat.one_le_pow _ _ (Nat.succ_pos m)
  rcases lt_or_ge m m₀ with hm | hm
  · have : h m ≤ ∑ i ∈ Finset.range m₀, h i :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 hm)
    exact (this.trans (Nat.le_add_left _ _)).trans (Nat.le_mul_of_pos_right _ hp)
  · have h₂ : (d.factorial : ℤ) * (h m : ℤ) - a * (m : ℤ) ^ d ≤
        C * ((d : ℤ) * ((m : ℤ) + 1) ^ (d - 1)) := (abs_le.1 (hC m hm)).2
    have h₃ : (h m : ℤ) ≤ (d.factorial : ℤ) * (h m : ℤ) :=
      le_mul_of_one_le_left (by positivity) (by exact_mod_cast d.factorial_pos)
    have h₄ : a * (m : ℤ) ^ d ≤ |a| * ((m : ℤ) + 1) ^ d :=
      (mul_le_mul_of_nonneg_right (le_abs_self a) (by positivity)).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) d) (abs_nonneg a))
    have h₅ : (C : ℤ) * ((d : ℤ) * ((m : ℤ) + 1) ^ (d - 1)) ≤ C * ((d : ℤ) * ((m : ℤ) + 1) ^ d) := by
      gcongr
      · have : (0 : ℤ) ≤ m := by positivity
        linarith
      · exact Nat.sub_le _ _
    have h₆ : (h m : ℤ) ≤ ((a.natAbs + C * d) * (m + 1) ^ d : ℕ) := by
      push_cast
      linarith
    exact (by exact_mod_cast h₆ : h m ≤ _).trans (Nat.mul_le_mul_right _ (Nat.le_add_right _ _))

end GlobalTheory
