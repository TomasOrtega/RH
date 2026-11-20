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

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

/- English proof (translation)
Introduce `k _ _ X _ hp d`. Establish `hf` using `algebraMap_eq_strHom k X`. Use `isNoetherian_of_isProjOver hp` as an intermediate fact. Proceed by induction on `d with`. Consider the case `zero`.

Introduce `F _ hd P _`. Rewrite using `[interNum_of_isEmpty, chi_eq_hdim_zero_of_suppDim_le_zero k hd]`. Conclude with `Nat.cast_nonneg _`. Consider the case `succ d ih`. Introduce `F _ hd P hP`.

Take `⟨n, hn, s, hs, -⟩` from `(hP 0).exists_mono_cutHom F`. Establish `hL` using `isLB_lbPow (hP 0).isLB n`. Establish `h1` using `ih (cut F hL s) (suppDim_cut_le F hL s hd) (Fin.tail P) fun i => hP i.succ`. Rewrite `h1` using `[← interNum_cons_eq_interNum_cut hL s (P := Fin.tail P) (fun i => (hP i.succ).isLB) (finiteCohTwists_of_isProjOver hf F hp)]`. Establish `h2` using `(diffVanish_chiPic_of_isProjOver hf F hp hd).interNum_update_of_cls_eq_zsmul (L := P) (by simp) (fun i => (hP i).isLB) 0 hL (hP 0).isLB (n : ℤ) (by rw [cls_lbPow (hP 0).isLB, natCast_zsmul])`.

Establish `e : Function.update P 0 (lbPow (P 0) n) = (Fin.cons (lbPow (P 0) n) (Fin.tail P) : Fin (d + 1) → LB X)`. Use function extensionality and compare the values at `i`. Use `Fin.cases ?_ (fun j => ?_) i` and prove the remaining obligations. Simplify using the standard rewrite rules. Simplify using `[Fin.tail]`.

Rewrite `h2` using `[Function.update_eq_self, e]`. Rewrite `h1` using `[h2]`. Conclude with `nonneg_of_mul_nonneg_right h1 (Nat.cast_pos.2 hn)`.
-/
theorem interNum_nonneg_of_isAmpleLB_of_isProjOver :
    ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)],
      IsProjOver (strHom k X) → ∀ (d : ℕ) (F : X.Modules) [IsFiniteQC F], suppDim F ≤ (d : ℕ) →
        ∀ P : Fin d → LB X, (∀ i, IsAmpleLB (P i)) → 0 ≤ interNum k F P := by
  intro k _ _ X _ hp d
  have hf := algebraMap_eq_strHom k X
  have := isNoetherian_of_isProjOver hp
  induction d with
  | zero =>
    intro F _ hd P _
    rw [interNum_of_isEmpty, chi_eq_hdim_zero_of_suppDim_le_zero k hd]
    exact Nat.cast_nonneg _
  | succ d ih =>
    intro F _ hd P hP
    obtain ⟨n, hn, s, hs, -⟩ := (hP 0).exists_mono_cutHom F
    have hL := isLB_lbPow (hP 0).isLB n
    have h1 := ih (cut F hL s) (suppDim_cut_le F hL s hd) (Fin.tail P) fun i => hP i.succ
    rw [← interNum_cons_eq_interNum_cut hL s (P := Fin.tail P) (fun i => (hP i.succ).isLB)
      (finiteCohTwists_of_isProjOver hf F hp)] at h1
    have h2 := (diffVanish_chiPic_of_isProjOver hf F hp hd).interNum_update_of_cls_eq_zsmul
      (L := P) (by simp) (fun i => (hP i).isLB) 0 hL (hP 0).isLB (n : ℤ)
      (by rw [cls_lbPow (hP 0).isLB, natCast_zsmul])
    have e : Function.update P 0 (lbPow (P 0) n) =
        (Fin.cons (lbPow (P 0) n) (Fin.tail P) : Fin (d + 1) → LB X) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp
      · simp [Fin.tail]
    rw [Function.update_eq_self, e] at h2
    rw [h2] at h1
    exact nonneg_of_mul_nonneg_right h1 (Nat.cast_pos.2 hn)

end GlobalTheory
