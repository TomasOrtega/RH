import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DRConjTranspose
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.CoordGamma

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct ComplexOrder
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.VacE

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.Glob PositivityTheory.Rg.Sw.Glob.VacS PositivityTheory.Rg.Sw.Glob.VacB PositivityTheory.Rg.Sw.Glob.VacC
  PositivityTheory.Rg.Sw.Glob.VacD

def rhoT {m : ℕ} (t : ℝ) (ε : Fin m → Bool) (a : Fin m) : ℝ := if epsT t ε a then 1 else -1

/- English proof (translation)
Replace the relevant objects with their definitions. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Put the polynomial expressions in normal form. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem isSiegel_I (n : ℕ) : IsSiegel (Complex.I • (1 : Matrix (Fin n) (Fin n) ℂ)) := by
  unfold IsSiegel
  have h : -(Complex.I / 2) • (Complex.I • (1 : Matrix (Fin n) (Fin n) ℂ)
      - (Complex.I • (1 : Matrix (Fin n) (Fin n) ℂ))ᴴ) = 1 := by
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, ← sub_smul, smul_smul]
    have hc : -(Complex.I / 2) * (Complex.I - star Complex.I) = 1 := by
      rw [Complex.star_def, Complex.conj_I]
      ring_nf
      rw [Complex.I_sq]; ring
    rw [hc, one_smul]
  rw [h]
  exact Matrix.PosDef.one

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities.
-/
theorem isSch_smul {m n : ℕ} {f : (Fin m → Fin n → ℂ) → ℂ} (hf : IsSch f) (K : ℂ) : IsSch (fun u => K * f u) := by
  obtain ⟨S, hS⟩ := hf
  refine ⟨K • S, ?_⟩
  funext u
  rw [SchwartzMap.smul_apply, hS, smul_eq_mul]

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Establish an intermediate fact.

Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Reduce the equality to equality of the corresponding arguments. Rewrite the conclusion repeatedly using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Apply the first step, then apply the next step to every resulting obligation. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Chain the equalities or inequalities of the calculation. Rewrite the conclusion repeatedly using the stated equalities. Rewrite the conclusion using the stated equalities.

Take a linear combination of the given relations to obtain the conclusion. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem isSch_DG {m n : ℕ} (hGZ : GZSch) (ε : Fin m → Bool) (t c : ℝ) (hc : 0 < c) (ht : |t| = c) (K : ℂ) :
    IsSch (DG (m := m) (n := n) K (fun _ _ => (c : ℂ))) := by
  have htr : ∀ b : Bool, ∀ u : Fin m → Fin n → ℂ, (gramB (n := n) (epsT t ε) b u).trace
      = ∑ a : Fin m, if epsT t ε a = b then ∑ j : Fin n, ((‖u a j‖ ^ 2 : ℝ) : ℂ) else 0 := by
    intro b u
    simp only [Matrix.trace, Matrix.diag, gramB, PositivityTheory.Rg.Sw.evX, PositivityTheory.Rg.Sw.Qb, map_sum, map_mul,
      MvPolynomial.eval_X]
    simp
    rw [Finset.sum_comm, Finset.sum_filter]
    refine Finset.sum_congr rfl fun a _ => ?_
    split_ifs
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [Complex.conj_mul']
    · rfl
  have hfun : DG (m := m) (n := n) K (fun _ _ => (c : ℂ))
      = fun u => K * gZf (n := n) ε t c (Complex.I • (1 : Matrix (Fin n) (Fin n) ℂ)) u := by
    funext u
    simp only [DG, gZf]
    congr 1
    simp_rw [← Complex.exp_sum]
    congr 1
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Matrix.smul_mul, Matrix.smul_mul,
      Matrix.one_mul, Matrix.one_mul, Matrix.trace_smul, Matrix.trace_smul, htr, htr,
      Complex.star_def, Complex.conj_I]
    simp only [smul_eq_mul]
    have hsplit : ∀ a : Fin m, ((if epsT t ε a = true then ∑ j : Fin n, ((‖u a j‖ ^ 2 : ℝ) : ℂ) else 0)
        + if epsT t ε a = false then ∑ j : Fin n, ((‖u a j‖ ^ 2 : ℝ) : ℂ) else 0)
        = ∑ j : Fin n, ((‖u a j‖ ^ 2 : ℝ) : ℂ) := by
      intro a; cases epsT t ε a <;> simp
    have hs := Finset.sum_congr (rfl : (Finset.univ : Finset (Fin m)) = _) fun a _ => hsplit a
    rw [Finset.sum_add_distrib] at hs
    set A := ∑ a : Fin m, if epsT t ε a = true then ∑ j : Fin n, ((‖u a j‖ ^ 2 : ℝ) : ℂ) else 0
    set B := ∑ a : Fin m, if epsT t ε a = false then ∑ j : Fin n, ((‖u a j‖ ^ 2 : ℝ) : ℂ) else 0
    have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
    calc _ = -(c : ℂ) * ∑ a : Fin m, ∑ j : Fin n, ((‖u a j‖ ^ 2 : ℝ) : ℂ) := by
          simp_rw [Finset.mul_sum]
      _ = _ := by
          rw [← hs]
          linear_combination (-(c : ℂ) * A - (c : ℂ) * B) * hI
  rw [hfun]
  exact isSch_smul (hGZ m n ε t c hc ht _ (isSiegel_I n)) K

/- English proof (translation)
Replace the relevant objects with their definitions. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Apply the first step, then apply the next step to every resulting obligation. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.
-/
theorem rhoT_eq {m : ℕ} (t c : ℝ) (ht : |t| = c) (hc : 0 < c) (ε : Fin m → Bool) (a : Fin m) :
    rhoT t ε a = VacC.sigR ε a * t / c := by
  unfold rhoT VacC.sigR epsT
  rcases lt_or_gt_of_ne (show t ≠ 0 by rintro rfl; simp at ht; linarith) with h | h
  · have htc : t = -c := by rw [abs_of_neg h] at ht; linarith
    have hn : ¬ (0 < t) := by linarith
    rw [if_neg hn, htc, mul_div_assoc, neg_div, div_self hc.ne']
    cases ε a <;> simp
  · have htc : t = c := by rw [abs_of_pos h] at ht; exact ht
    rw [if_pos h, htc, mul_div_assoc, div_self hc.ne', mul_one]

end PositivityTheory.Rg.Sw.Glob.VacE
