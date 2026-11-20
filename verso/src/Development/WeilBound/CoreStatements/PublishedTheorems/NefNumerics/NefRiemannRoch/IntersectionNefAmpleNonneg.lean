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
import Development.WeilBound.CoreStatements.PublishedTheorems.NefNumerics.NefRiemannRoch.IntersectionNumberNonnegEffective

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

/- English proof (translation)
Introduce `k _ _ X _ hp d`. Establish `hf` using `algebraMap_eq_strHom k X`. Use `haveI := isNoetherian_of_isProjOver hp`. Proceed by induction on `d with`. Consider the case `zero`.

Introduce `F _ hF N P hN _`. Use `haveI : IsProper (strHom k X) := (isProper_and_exists_isAmpleLB_of_isProjOver hp).1`. Establish `hN'` using `(isNef_iff hf).1 hN`. Establish `e : (Fin.cons N P : Fin (0 + 1) → LB X) = ![N]`. Use extensionality with `i`.

Use `fin_cases i`. Both sides reduce to the same expression. Rewrite using `[e]`. Use `SheafCycle.interNum_nonneg_of_interNumRed_nonneg k X hp 1 F (by simpa using hF) ![N] (fun i => by fin_cases i; exact hN'.1) fun Z hZ hd => hN'.2 Z hZ (by simpa using hd)` and prove the remaining obligations. Consider the case `succ d ih`.

Introduce `F _ hF N P hN hP`. Establish `hPb : ∀ i, (P i).IsLB` using `fun i => (hP i).isLB`. Use `set A := P 0`. Use `set Q : Fin d → LB X := Fin.tail P`. Establish `hQ : ∀ i, IsAmpleLB (Q i)` using `fun i => hP _`.

Establish `hQb : ∀ i, (Q i).IsLB` using `fun i => (hQ i).isLB`. Establish `hPe : P = Fin.cons A Q` using `(Fin.cons_self_tail P).symm`. Establish `hL : ∀ i, (Fin.cons N P : Fin (d + 2) → LB X) i |>.IsLB` using `isLB_cons hN.isLB hPb`. Establish `hsw : (Fin.cons N P : Fin (d + 2) → LB X) ∘ Equiv.swap 0 1 = (Fin.cons A (Fin.cons N Q) : Fin (d + 2) → LB X)`. Rewrite using `[hPe]`.

Use extensionality with `i`. Use `Fin.cases ?_ (fun j => ?_) i` and prove the remaining obligations. Both sides reduce to the same expression. Use `Fin.cases ?_ (fun l => ?_) j` and prove the remaining obligations. Both sides reduce to the same expression.

Establish `h1 : l.succ.succ ≠ (1 : Fin (d + 2))`. Rewrite using `[← Fin.succ_zero_eq_one]`. Conclude with `(Fin.succ_injective _).ne (Fin.succ_ne_zero l)`. Rewrite using `[Function.comp_apply, Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) h1]`. Both sides reduce to the same expression.

Rewrite using `[← interNum_comp_perm k F hL (Equiv.swap 0 1), hsw]`. Establish `hfin` using `finiteCohTwists_of_isProjOver hf F hp`. Establish `hv` using `diffVanish_chiPic_of_isProjOver hf F hp hF`. Take `⟨a, ha, s, hs, -⟩` from `(hP 0).exists_mono_cutHom F`. Establish `hLa` using `isLB_lbPow (hP 0).isLB a`.

Establish `hNQ : ∀ i, (Fin.cons N Q : Fin (d + 1) → LB X) i |>.IsLB` using `isLB_cons hN.isLB hQb`. Establish `h0` using `ih (cut F hLa s) (suppDim_cut_le _ hLa s hF) N Q hN hQ`. Rewrite `h0` using `[← interNum_cons_eq_interNum_cut hLa s hNQ hfin]`. Establish `h` using `hv.interNum_update_of_cls_eq_zsmul (by simp) (isLB_cons (hP 0).isLB hNQ) (0 : Fin (d + 2)) hLa (hP 0).isLB (a : ℤ) (cls_lbZPow (hP 0).isLB a _)`. Simplify using `only [Fin.update_cons_zero] at h`.

Rewrite `h0` using `[h]`. Conclude with `nonneg_of_mul_nonneg_right h0 (by exact_mod_cast ha)`.
-/
theorem interNum_cons_nef_ample_nonneg :
    ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k X) → ∀ (d : ℕ) (F : X.Modules) [IsFiniteQC F], suppDim F ≤ (d + 1 : ℕ) → ∀ (N : LB X) (P : Fin d → LB X), IsNef k N → (∀ i, IsAmpleLB (P i)) → 0 ≤ interNum k F (Fin.cons N P : Fin (d + 1) → LB X) := by
  intro k _ _ X _ hp d
  have hf := algebraMap_eq_strHom k X
  haveI := isNoetherian_of_isProjOver hp
  induction d with
  | zero =>
    intro F _ hF N P hN _
    haveI : IsProper (strHom k X) := (isProper_and_exists_isAmpleLB_of_isProjOver hp).1
    have hN' := (isNef_iff hf).1 hN
    have e : (Fin.cons N P : Fin (0 + 1) → LB X) = ![N] := by
      ext i; fin_cases i; rfl
    rw [e]
    refine SheafCycle.interNum_nonneg_of_interNumRed_nonneg k X hp 1 F (by simpa using hF) ![N]
      (fun i => by fin_cases i; exact hN'.1) fun Z hZ hd => hN'.2 Z hZ (by simpa using hd)
  | succ d ih =>
    intro F _ hF N P hN hP
    have hPb : ∀ i, (P i).IsLB := fun i => (hP i).isLB
    set A := P 0
    set Q : Fin d → LB X := Fin.tail P
    have hQ : ∀ i, IsAmpleLB (Q i) := fun i => hP _
    have hQb : ∀ i, (Q i).IsLB := fun i => (hQ i).isLB
    have hPe : P = Fin.cons A Q := (Fin.cons_self_tail P).symm
    have hL : ∀ i, (Fin.cons N P : Fin (d + 2) → LB X) i |>.IsLB := isLB_cons hN.isLB hPb
    have hsw : (Fin.cons N P : Fin (d + 2) → LB X) ∘ Equiv.swap 0 1 =
        (Fin.cons A (Fin.cons N Q) : Fin (d + 2) → LB X) := by
      rw [hPe]; ext i
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · refine Fin.cases ?_ (fun l => ?_) j
        · rfl
        · have h1 : l.succ.succ ≠ (1 : Fin (d + 2)) := by
            rw [← Fin.succ_zero_eq_one]; exact (Fin.succ_injective _).ne (Fin.succ_ne_zero l)
          rw [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) h1]
          rfl
    rw [← interNum_comp_perm k F hL (Equiv.swap 0 1), hsw]
    have hfin := finiteCohTwists_of_isProjOver hf F hp
    have hv := diffVanish_chiPic_of_isProjOver hf F hp hF
    obtain ⟨a, ha, s, hs, -⟩ := (hP 0).exists_mono_cutHom F
    have hLa := isLB_lbPow (hP 0).isLB a
    have hNQ : ∀ i, (Fin.cons N Q : Fin (d + 1) → LB X) i |>.IsLB := isLB_cons hN.isLB hQb
    have h0 := ih (cut F hLa s) (suppDim_cut_le _ hLa s hF) N Q hN hQ
    rw [← interNum_cons_eq_interNum_cut hLa s hNQ hfin] at h0
    have h := hv.interNum_update_of_cls_eq_zsmul (by simp) (isLB_cons (hP 0).isLB hNQ)
      (0 : Fin (d + 2)) hLa (hP 0).isLB (a : ℤ) (cls_lbZPow (hP 0).isLB a _)
    simp only [Fin.update_cons_zero] at h
    rw [h] at h0
    exact nonneg_of_mul_nonneg_right h0 (by exact_mod_cast ha)

end GlobalTheory
