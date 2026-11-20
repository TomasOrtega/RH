import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.WeilBound.CoreStatements.PublishedTheorems.NefNumerics.NefRiemannRoch.IntersectionNefAmpleNonnegStatement
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPowVanishingIdealLeAnnihilator
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SupportPushforwardSubschemeSubset
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TensOfForallIsPsEff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowLeGlobalSectionsDimLineBundlePow

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory.NefLower

/- English proof (translation)
Introduce `k _ _ X _ hX d hdim A N L hA hN hL hyp a b hcls`. Establish `hsupp : suppDim (GlobalTheory.structureModule X) ≤ ((d + 1 : ℕ) : WithBot ℕ∞)` using `(QCoh.suppDim_le _).trans hdim`. Establish `hDV : DiffVanish (d + 1 + 1) (chiPic k (GlobalTheory.structureModule X))` using `diffVanish_chiPic_of_isProjOver (algebraMap_eq_strHom k X) _ hX hsupp`. Establish `hALB : A.IsLB` using `hA.isLB`. Establish `hNLB : N.IsLB` using `hN.isLB`.

Establish `hLLB : L.IsLB` using `hL.isLB`. Use `set R : Fin d → LB X := fun _ => L with hR`. Establish `hL0 : (fun _ : Fin (d + 1) => L) = (Fin.cons L R : Fin (d + 1) → LB X)`. Use function extensionality and compare the values at `i`. Conclude with `Fin.cases rfl (fun _ => rfl) i`.

Establish `hconsLB : ∀ M : LB X, M.IsLB → ∀ i, ((Fin.cons M R : Fin (d + 1) → LB X) i).IsLB` using `fun M hM i => Fin.cases hM (fun _ => hLLB) i`. Establish `hadd` using `DiffVanish.interNum_update_of_cls_eq_add hDV (le_of_eq (Fintype.card_fin _).symm) (hconsLB L hLLB) 0 hLLB (isLB_lbPow hNLB a) (isLB_lbPow hALB b) (by rw [cls_lbPow hNLB, cls_lbPow hALB]; exact hcls)`. Simplify using `only [Fin.update_cons_zero] at hadd`. Establish `hsN` using `DiffVanish.interNum_update_of_cls_eq_zsmul hDV (le_of_eq (Fintype.card_fin _).symm) (hconsLB N hNLB) 0 (isLB_lbPow hNLB a) hNLB (a : ℤ) (by rw [cls_lbPow hNLB]; simp)`. Establish `hsA` using `DiffVanish.interNum_update_of_cls_eq_zsmul hDV (le_of_eq (Fintype.card_fin _).symm) (hconsLB A hALB) 0 (isLB_lbPow hALB b) hALB (b : ℤ) (by rw [cls_lbPow hALB]; simp)`.

Simplify using `only [Fin.update_cons_zero] at hsN hsA`. Establish `hNpos : 0 ≤ interNum k (GlobalTheory.structureModule X) (Fin.cons N R : Fin (d + 1) → LB X)` using `T.intersection_nef_ample_nonneg k X hX d _ hsupp N R hN (fun _ => hL)`. Establish `hfam : ∀ j, ((![A, N] : Fin 2 → LB X) j).IsLB` using `fun j => by fin_cases j`. Conclude with `hALB`. Conclude with `hNLB`.

Establish `hQLB : ∀ i, ((Fin.cons A R : Fin (d + 1) → LB X) i).IsLB` using `hconsLB A hALB`. Set `n : Fin (d + 1) → Fin 2 → ℤ` to `Fin.cons ![1, 0] (fun _ => ![(b : ℤ), (a : ℤ)])`. Establish `hexp` using `DiffVanish.interNum_of_cls_eq_sum hDV hfam hQLB n (by`. Introduce `i`. Use `Fin.cases ?_ (fun j => ?_) i` and prove the remaining obligations.

Simplify using `[n, Fin.sum_univ_two]`. Simplify using `only [n, Fin.sum_univ_two, Fin.cons_succ]`. Simplify using `only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, natCast_zsmul]`. Use `show cls L _ = _`. Rewrite using `[hcls, add_comm])`.

Establish `hterm : ∀ α : Fin (d + 1) → Fin 2, 0 ≤ (∏ i, n i (α i)) * interNum k (GlobalTheory.structureModule X) ((![A, N] : Fin 2 → LB X) ∘ α)`. Introduce `α`. Establish `hprod : 0 ≤ ∏ i, n i (α i)`. Use `Finset.prod_nonneg fun i _ => ?_` and prove the remaining obligations. Use `Fin.cases ?_ (fun j => ?_) i` and prove the remaining obligations.

Simplify using `only [n, Fin.cons_zero]`. Generalize the expression as in `α 0 = t`. Apply the tactic sequence `fin_cases t <;> simp`. Simplify using `only [n, Fin.cons_succ]`. Generalize the expression as in `α j.succ = t`.

Apply the tactic sequence `fin_cases t <;> simp`. Break down `Fin.exists_fin_two.mp ⟨α 0, rfl⟩ with h0 | h0` into its components or cases. Use `mul_nonneg hprod ?_` and prove the remaining obligations. Establish `hcomp : ((![A, N] : Fin 2 → LB X) ∘ α) = Fin.cons A (fun j : Fin d => (![A, N] : Fin 2 → LB X) (α j.succ))`. Use function extensionality and compare the values at `i`.

Use `Fin.cases ?_ (fun j => rfl) i` and prove the remaining obligations. Simplify using `[h0]`. Rewrite using `[hcomp]`. Use `hyp _ (fun j => ?_)` and prove the remaining obligations. Generalize the expression as in `α j.succ = t`.

Use `fin_cases t`. Conclude with `hA.isNef`. Conclude with `hN`. Establish `hz : (∏ i, n i (α i)) = 0`. Use `Finset.prod_eq_zero (Finset.mem_univ 0) ?_` and prove the remaining obligations.

Simplify using `[n, h0]`. Rewrite using `[hz, zero_mul]`. Set `α0 : Fin (d + 1) → Fin 2` to `fun _ => 0`. Establish `hsingle : (∏ i, n i (α0 i)) * interNum k (GlobalTheory.structureModule X) ((![A, N] : Fin 2 → LB X) ∘ α0) ≤ interNum k (GlobalTheory.structureModule X) (Fin.cons A R : Fin (d + 1) → LB X)`. Rewrite using `[hexp]`.

Conclude with `Finset.single_le_sum (fun α _ => hterm α) (Finset.mem_univ α0)`. Establish `hprod0 : (∏ i, n i (α0 i)) = (b : ℤ) ^ d`. Rewrite using `[Fin.prod_univ_succ]`. Simplify using `[n, α0]`. Establish `hA0 : interNum k (GlobalTheory.structureModule X) ((![A, N] : Fin 2 → LB X) ∘ α0) = topSelfIntersection k A (d + 1)`.

Rewrite using `[topSelf_def]`. Both sides reduce to the same expression. Rewrite `hsingle` using `[hprod0, hA0]`. Rewrite using `[topSelf_def k L, hL0, hadd, hsN, hsA]`. Establish `hb : (0 : ℤ) ≤ b` using `by positivity`.

Establish `ha : (0 : ℤ) ≤ a` using `by positivity`. Combine the equalities or inequalities in the displayed calculation. Use `mul_nonneg ha hNpos` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem topSelf_lower : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k X) → ∀ d : ℕ, topologicalKrullDim X ≤ (d + 1 : ℕ) → ∀ (A N L : LB X) (hA : IsAmpleLB A) (hN : IsNef k N) (hL : IsAmpleLB L), (∀ P : Fin d → LB X, (∀ i, IsNef k (P i)) → 0 ≤ interNum k (GlobalTheory.structureModule X) (Fin.cons A P : Fin (d + 1) → LB X)) → ∀ a b : ℕ, cls L hL.isLB = a • cls N hN.isLB + b • cls A hA.isLB → (b : ℤ) ^ (d + 1) * topSelfIntersection k A (d + 1) ≤ topSelfIntersection k L (d + 1) := by
  intro k _ _ X _ hX d hdim A N L hA hN hL hyp a b hcls
  have hsupp : suppDim (GlobalTheory.structureModule X) ≤ ((d + 1 : ℕ) : WithBot ℕ∞) :=
    (QCoh.suppDim_le _).trans hdim
  have hDV : DiffVanish (d + 1 + 1) (chiPic k (GlobalTheory.structureModule X)) :=
    diffVanish_chiPic_of_isProjOver (algebraMap_eq_strHom k X) _ hX hsupp
  have hALB : A.IsLB := hA.isLB
  have hNLB : N.IsLB := hN.isLB
  have hLLB : L.IsLB := hL.isLB
  set R : Fin d → LB X := fun _ => L with hR
  have hL0 : (fun _ : Fin (d + 1) => L) = (Fin.cons L R : Fin (d + 1) → LB X) := by
    funext i; exact Fin.cases rfl (fun _ => rfl) i
  have hconsLB : ∀ M : LB X, M.IsLB → ∀ i, ((Fin.cons M R : Fin (d + 1) → LB X) i).IsLB :=
    fun M hM i => Fin.cases hM (fun _ => hLLB) i
  have hadd := DiffVanish.interNum_update_of_cls_eq_add hDV (le_of_eq (Fintype.card_fin _).symm)
    (hconsLB L hLLB) 0 hLLB (isLB_lbPow hNLB a) (isLB_lbPow hALB b)
    (by rw [cls_lbPow hNLB, cls_lbPow hALB]; exact hcls)
  simp only [Fin.update_cons_zero] at hadd
  have hsN := DiffVanish.interNum_update_of_cls_eq_zsmul hDV (le_of_eq (Fintype.card_fin _).symm)
    (hconsLB N hNLB) 0 (isLB_lbPow hNLB a) hNLB (a : ℤ) (by rw [cls_lbPow hNLB]; simp)
  have hsA := DiffVanish.interNum_update_of_cls_eq_zsmul hDV (le_of_eq (Fintype.card_fin _).symm)
    (hconsLB A hALB) 0 (isLB_lbPow hALB b) hALB (b : ℤ) (by rw [cls_lbPow hALB]; simp)
  simp only [Fin.update_cons_zero] at hsN hsA
  have hNpos : 0 ≤ interNum k (GlobalTheory.structureModule X) (Fin.cons N R : Fin (d + 1) → LB X) :=
    T.intersection_nef_ample_nonneg k X hX d _ hsupp N R hN (fun _ => hL)
  have hfam : ∀ j, ((![A, N] : Fin 2 → LB X) j).IsLB := fun j => by
    fin_cases j
    · exact hALB
    · exact hNLB
  have hQLB : ∀ i, ((Fin.cons A R : Fin (d + 1) → LB X) i).IsLB := hconsLB A hALB
  let n : Fin (d + 1) → Fin 2 → ℤ := Fin.cons ![1, 0] (fun _ => ![(b : ℤ), (a : ℤ)])
  have hexp := DiffVanish.interNum_of_cls_eq_sum hDV hfam hQLB n (by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [n, Fin.sum_univ_two]
    · simp only [n, Fin.sum_univ_two, Fin.cons_succ]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, natCast_zsmul]
      show cls L _ = _
      rw [hcls, add_comm])
  have hterm : ∀ α : Fin (d + 1) → Fin 2,
      0 ≤ (∏ i, n i (α i)) * interNum k (GlobalTheory.structureModule X) ((![A, N] : Fin 2 → LB X) ∘ α) := by
    intro α
    have hprod : 0 ≤ ∏ i, n i (α i) := by
      refine Finset.prod_nonneg fun i _ => ?_
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [n, Fin.cons_zero]
        generalize α 0 = t
        fin_cases t <;> simp
      · simp only [n, Fin.cons_succ]
        generalize α j.succ = t
        fin_cases t <;> simp
    rcases Fin.exists_fin_two.mp ⟨α 0, rfl⟩ with h0 | h0
    · refine mul_nonneg hprod ?_
      have hcomp : ((![A, N] : Fin 2 → LB X) ∘ α) =
          Fin.cons A (fun j : Fin d => (![A, N] : Fin 2 → LB X) (α j.succ)) := by
        funext i
        refine Fin.cases ?_ (fun j => rfl) i
        simp [h0]
      rw [hcomp]
      refine hyp _ (fun j => ?_)
      generalize α j.succ = t
      fin_cases t
      · exact hA.isNef
      · exact hN
    · have hz : (∏ i, n i (α i)) = 0 := by
        refine Finset.prod_eq_zero (Finset.mem_univ 0) ?_
        simp [n, h0]
      rw [hz, zero_mul]
  let α0 : Fin (d + 1) → Fin 2 := fun _ => 0
  have hsingle : (∏ i, n i (α0 i)) *
      interNum k (GlobalTheory.structureModule X) ((![A, N] : Fin 2 → LB X) ∘ α0) ≤
      interNum k (GlobalTheory.structureModule X) (Fin.cons A R : Fin (d + 1) → LB X) := by
    rw [hexp]
    exact Finset.single_le_sum (fun α _ => hterm α) (Finset.mem_univ α0)
  have hprod0 : (∏ i, n i (α0 i)) = (b : ℤ) ^ d := by
    rw [Fin.prod_univ_succ]
    simp [n, α0]
  have hA0 : interNum k (GlobalTheory.structureModule X) ((![A, N] : Fin 2 → LB X) ∘ α0) =
      topSelfIntersection k A (d + 1) := by
    rw [topSelf_def]; rfl
  rw [hprod0, hA0] at hsingle
  rw [topSelf_def k L, hL0, hadd, hsN, hsA]
  have hb : (0 : ℤ) ≤ b := by positivity
  have ha : (0 : ℤ) ≤ a := by positivity
  calc (b : ℤ) ^ (d + 1) * topSelfIntersection k A (d + 1)
      = (b : ℤ) * ((b : ℤ) ^ d * topSelfIntersection k A (d + 1)) := by ring
    _ ≤ (b : ℤ) * interNum k (GlobalTheory.structureModule X) (Fin.cons A R : Fin (d + 1) → LB X) :=
        mul_le_mul_of_nonneg_left hsingle hb
    _ ≤ (a : ℤ) * interNum k (GlobalTheory.structureModule X) (Fin.cons N R : Fin (d + 1) → LB X) +
        (b : ℤ) * interNum k (GlobalTheory.structureModule X) (Fin.cons A R : Fin (d + 1) → LB X) := by
        have := mul_nonneg ha hNpos
        linarith

end GlobalTheory.NefLower
