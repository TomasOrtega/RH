import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CasimirFockAct1SubCasimirFockAct2

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.BasicNotions.TH GlobalTheory.FockAlg MvPolynomial

noncomputable section

namespace GlobalTheory.FockSecondSwap

variable {p q r s : ℕ}

def swapLn (p q r s : ℕ) : Ln p q r s ≃ Ln p q s r :=
  Equiv.prodCongr (Equiv.refl _) (Equiv.sumComm _ _)

def lsg (l : Ln p q r s) : ℂ := if linePos l then 1 else -1

def eps : Ix p q → ℂ := Sum.elim (fun _ => 1) (fun _ => -1)

def tJ (X : Mat p q) : Mat p q := Matrix.of fun a b => eps a * eps b * X b a

/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem eps_mul_self (a : Ix p q) : eps a * eps a = 1 := by
  rcases a with a | a <;> simp [eps]

/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem linePos_swapLn (l : Ln p q r s) : linePos (swapLn p q r s l) = !linePos l := by
  rcases l with ⟨a | a, c | c⟩ <;> rfl

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem trace_tJ (X : Mat p q) : (tJ X).trace = X.trace := by
  simp only [Matrix.trace, Matrix.diag, tJ, Matrix.of_apply, eps_mul_self, one_mul]

/- English proof (translation)
Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem rename_raiB (l : Ln p q r s) (f : Pol p q r s) :
    rename (swapLn p q r s) (raiB l f) = lsg l • lowB (swapLn p q r s l) (rename (swapLn p q r s) f) := by
  have hd := pderiv_rename (R := ℂ) (swapLn p q r s).injective l f
  unfold raiB lowB lsg
  rw [linePos_swapLn]
  cases h : linePos l <;> simp [hd]

/- English proof (translation)
Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem rename_lowB (l : Ln p q r s) (f : Pol p q r s) :
    rename (swapLn p q r s) (lowB l f) = -(lsg l) • raiB (swapLn p q r s l) (rename (swapLn p q r s) f) := by
  have hd := pderiv_rename (R := ℂ) (swapLn p q r s).injective l f
  unfold raiB lowB lsg
  rw [linePos_swapLn]
  cases h : linePos l <;> simp [hd]

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Consider separately whether the proposition holds or fails. Substitute using the available equality.

Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation. Apply the first step, then apply the next step to every resulting obligation. Establish an intermediate fact. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem rename_omE (l l' : Ln p q r s) (f : Pol p q r s) :
    rename (swapLn p q r s) (omE l l' f) =
      -(lsg l * lsg l') • omE (swapLn p q r s l') (swapLn p q r s l) (rename (swapLn p q r s) f) := by
  have hc := congrArg (fun T : Module.End ℂ (Pol p q s r) => T (rename (swapLn p q r s) f))
    (GlobalTheory.FockCasimir.lowB_mul_raiB (swapLn p q r s l) (swapLn p q r s l'))
  simp only [Module.End.mul_apply, LinearMap.add_apply] at hc
  simp only [omE, LinearMap.add_apply, Module.End.mul_apply, map_add, rename_raiB, rename_lowB,
    LinearMap.map_smul, hc]
  by_cases h : l = l'
  · subst h
    simp only [if_true, LinearMap.smul_apply, Module.End.one_apply, map_smul]
    have h1 : lsg l = 1 ∨ lsg l = -1 := by unfold lsg; split_ifs <;> simp
    rcases h1 with h1 | h1 <;> rw [h1] <;> module
  · have h' : swapLn p q r s l ≠ swapLn p q r s l' := fun e => h ((swapLn p q r s).injective e)
    simp only [h, h', Ne.symm h', if_false, LinearMap.zero_apply, add_zero, map_zero]
    module

def swapM (Z : Matrix (Ln p q r s) (Ln p q r s) ℂ) : Matrix (Ln p q s r) (Ln p q s r) ℂ :=
  Matrix.of fun m m' => lsg ((swapLn p q r s).symm m') * lsg ((swapLn p q r s).symm m) *
    Z ((swapLn p q r s).symm m') ((swapLn p q r s).symm m)

/- English proof (translation)
Simplify using the standard rewrite rules. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Put the polynomial expressions in normal form.
-/
theorem rename_omAct (Z : Matrix (Ln p q r s) (Ln p q r s) ℂ) (f : Pol p q r s) :
    rename (swapLn p q r s) (omAct p q r s Z f) = -(omAct p q s r (swapM Z) (rename (swapLn p q r s) f)) := by
  simp only [omAct_apply, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, rename_omE]
  have e : ∀ h : Ln p q s r → Ln p q s r → Pol p q s r,
      ∑ m, ∑ m', h m m' = ∑ l, ∑ l', h (swapLn p q r s l') (swapLn p q r s l) := by
    intro h
    rw [Finset.sum_comm, ← (swapLn p q r s).sum_comp]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← (swapLn p q r s).sum_comp]
  rw [e]
  simp only [swapM, Matrix.of_apply, Equiv.symm_apply_apply, ← Finset.sum_neg_distrib, smul_smul, neg_smul,
    smul_neg, mul_neg]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ => ?_
  ring_nf

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem kron_apply (X : Mat p q) (a b : Ix p q) (c d : Ix r s) :
    (Matrix.kroneckerMapBilinear (LinearMap.mul ℂ ℂ)).flip (1 : Mat r s) X (a, c) (b, d) = X a b * (1 : Mat r s) c d := by
  simp [Matrix.kroneckerMapBilinear_apply_apply, Matrix.kroneckerMap_apply]

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem swapM_kron (X : Mat p q) :
    swapM ((Matrix.kroneckerMapBilinear (LinearMap.mul ℂ ℂ)).flip (1 : Mat r s) X) =
      (Matrix.kroneckerMapBilinear (LinearMap.mul ℂ ℂ)).flip (1 : Mat s r) (tJ X) := by
  ext ⟨a, c⟩ ⟨b, d⟩
  simp only [swapM, Matrix.of_apply, kron_apply, tJ, swapLn, Equiv.prodCongr_symm, Equiv.prodCongr_apply,
    Equiv.refl_symm, Equiv.refl_apply, Equiv.sumComm_symm, Equiv.sumComm_apply, Prod.map]
  rcases a with a | a <;> rcases b with b | b <;> rcases c with c | c <;> rcases d with d | d <;>
    simp [lsg, linePos, eps, Matrix.one_apply] <;> split_ifs <;> simp_all [eq_comm]

/- English proof (translation)
Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem rename_fockAct1 (X : Mat p q) (f : Pol p q r s) :
    rename (swapLn p q r s) (fockAct1 p q r s X f) = -(fockAct1 p q s r (tJ X) (rename (swapLn p q r s) f)) := by
  simp only [fockAct1, LinearMap.comp_apply]
  rw [rename_omAct, swapM_kron]

end GlobalTheory.FockSecondSwap

namespace GlobalTheory.RealLift

open GlobalTheory.FockSecondSwap

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hasForm_swap {P Q R S : ℕ} {x : ℚ} (h : HasForm P Q S R x) : HasForm P Q R S (-x) := by
  obtain ⟨l, hl0, hl⟩ := h
  refine ⟨l.comp (rename (swapLn P Q R S)).toLinearMap, fun h0 => hl0 (LinearMap.ext fun f => ?_), fun X f => ?_⟩
  · have := LinearMap.congr_fun h0 (rename (swapLn P Q R S).symm f)
    simpa [rename_rename, Equiv.self_comp_symm, rename_id] using this
  · simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply]
    rw [rename_fockAct1, map_neg, hl, trace_tJ]
    push_cast
    ring

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem hasForm_neg_of_formEx : FormEx → ∀ (P Q R S : ℕ) (x : ℚ) (k k' : ℕ), P ≤ S → Q ≤ R → 0 < k → 0 < k' →
    x - Formalism.BasicNotions.TH.cPair S R = k → x + Formalism.BasicNotions.TH.cPair S R = k' → HasForm P Q R S (-x) :=
  fun hF P Q R S x k k' h1 h2 h3 h4 h5 h6 => hasForm_swap (hF P Q S R x k k' h1 h2 h3 h4 h5 h6)

end GlobalTheory.RealLift
