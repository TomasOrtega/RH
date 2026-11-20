import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsFundU
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselGroupActionFourierBesselBasePointStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRationalOrbitPointEqBesselBasePointStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB

namespace GlobalTheory.Unf.FB

variable {D : D7} {σ : ℕ}

def eLast (D : D7) (ρ : ℕ) : Fin ρ → D.host.E := fun i => if i.1 + 1 = ρ then 1 else 0

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `only [ratV, eLast, ell]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem ratV_eLast (ρ : ℕ) : ratV (eLast D ρ) = ell D ρ := by
  funext i
  simp only [ratV, eLast, ell]
  split_ifs <;> simp

def zlQ (B : BesLev D σ) : Matrix (Fin B.L.rank) (Fin (σ + 1)) D.host.E := vecMulVec B.ζ (eLast D (σ + 1))

/- English proof (translation)
Rewrite using `[zl, zEll, ← ratV_eLast]`. Use function extensionality and compare the values at `i j`. Simplify using `[rat, zlQ, vecMulVec_apply, ratV]`.
-/
theorem rat_zlQ (B : BesLev D σ) : (rat (zlQ B) : Mx D B.L.rank (σ + 1)) = zl B := by
  rw [zl, zEll, ← ratV_eLast]
  funext i j
  simp [rat, zlQ, vecMulVec_apply, ratV]

/- English proof (translation)
Rewrite using `[gramQ, rat_mul, rat_mul, rat_conjTranspose]`. Both sides reduce to the same expression.
-/
theorem rat_gramQ (W : HSp D) {ρ : ℕ} (x : Matrix (Fin W.rank) (Fin ρ) D.host.E) :
    (rat (gramQ W x) : Mx D ρ ρ) = adj (rat x) ⬝ (gA W ⬝ rat x) := by
  rw [gramQ, rat_mul, rat_mul, rat_conjTranspose]; rfl

/- English proof (translation)
Establish `hu : IsUnit (-incA D D.host.xi0)` using `((isUnit_iff_ne_zero.2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)).map (incA D)).neg`. Unfold `GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew at h`. Rewrite `h` using `[hu.smul_left_cancel, Matrix.transpose_inj]`. Apply `rat_injective` to reduce the goal to its premises. Rewrite using `[rat_gramQ, rat_gramQ, h]`.
-/
theorem gramQ_eq_of_gramSkew {W W' : HSp D} {ρ : ℕ} (x : Matrix (Fin W.rank) (Fin ρ) D.host.E)
    (x' : Matrix (Fin W'.rank) (Fin ρ) D.host.E)
    (h : GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew W (rat x : Mx D W.rank ρ) = GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew W' (rat x')) :
    gramQ W x = gramQ W' x' := by
  have hu : IsUnit (-incA D D.host.xi0) :=
    ((isUnit_iff_ne_zero.2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)).map (incA D)).neg
  unfold GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew at h
  rw [hu.smul_left_cancel, Matrix.transpose_inj] at h
  apply rat_injective
  rw [rat_gramQ, rat_gramQ, h]

/- English proof (translation)
Rewrite using `[pairS, adj_mul, Matrix.mul_assoc]`.
-/
theorem pairS_mul (T : HSp D) {ρ : ℕ} (x : Mx D T.rank ρ) (c : Mx D ρ ρ) :
    pairS T x (x ⬝ c) = (adj c ⬝ (adj x ⬝ (gA T ⬝ x))).trace := by
  rw [pairS, adj_mul, Matrix.mul_assoc]

/- English proof (translation)
Simplify using `only [gramQ, zlQ, Matrix.mulVec, dotProduct, Matrix.mul_apply, conjTranspose_apply, vecMulVec_apply, eLast, Pi.star_apply, Fin.val_last]`. Simplify using `only [if_true, mul_one, star_one]`. Rewrite using `[Finset.sum_eq_single (Fin.last σ)]`. Simplify using `only [Fin.val_last, if_true, mul_one]`. Introduce `b _ hb`.

Establish `hb' : ¬ (b.1 + 1 = σ + 1)` using `fun h => hb (Fin.ext (by simp only [Fin.val_last]; omega))`. Simplify using `only [hb', if_false, mul_zero, Finset.sum_const_zero, zero_mul]`. Simplify using the standard rewrite rules.
-/
theorem gramQ_zlQ_mulVec_last (B : BesLev D σ) (a : Fin (σ + 1) → D.host.E) :
    (gramQ B.L (zlQ B) *ᵥ a) (Fin.last σ) = (star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ) * a (Fin.last σ) := by
  simp only [gramQ, zlQ, Matrix.mulVec, dotProduct, Matrix.mul_apply, conjTranspose_apply, vecMulVec_apply, eLast,
    Pi.star_apply, Fin.val_last]
  simp only [if_true, mul_one, star_one]
  rw [Finset.sum_eq_single (Fin.last σ)]
  · simp only [Fin.val_last, if_true, mul_one]
  · intro b _ hb
    have hb' : ¬ (b.1 + 1 = σ + 1) := fun h => hb (Fin.ext (by simp only [Fin.val_last]; omega))
    simp only [hb', if_false, mul_zero, Finset.sum_const_zero, zero_mul]
  · simp

/- English proof (translation)
Introduce `D σ B`. Take `⟨x, ⟨hli, hg⟩, hx⟩` from `GlobalTheory.T.exists_mem_orb_rat_eq_x0 D σ B`. Rewrite `hg` using `[← rat_zlQ]`. Establish `hG : gramQ B.V x = gramQ B.L (zlQ B)` using `gramQ_eq_of_gramSkew x (zlQ B) hg`. Establish `hA : adj (x0 B) ⬝ (gA B.V ⬝ x0 B) = adj (zl B) ⬝ (gA B.L ⬝ zl B)`.

Rewrite using `[← hx, ← rat_zlQ, ← rat_gramQ, ← rat_gramQ, hG]`. Use `⟨x, hx, ⟨hli, fun u hu => ?_⟩, ?_, fun a ha => ?_, fun S S₀ d c => ?_⟩` and prove the remaining obligations. Rewrite using `[rat_gramQ, hx, hA, ]`. Establish `hz : zl B ⬝ u.1 = zl B` using `zEll_mul B.L B.ζ hu`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[adj_mul]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = adj (zl B) ⬝ (gA B.L ⬝ zl B) := by rw [hz]`. Use extensionality with `g`. Rewrite using `[hx]`.

Conclude with `((GlobalTheory.T.mem_besGrp_iff_mt_mul_x0_eq_x0_mul D σ B).1 g).symm`. Establish `h1` using `congrFun ha (Fin.last σ)`. Rewrite `h1` using `[hG, gramQ_zlQ_mulVec_last, Pi.zero_apply]`. Conclude with `(mul_eq_zero.1 h1).resolve_left B.line.2`. Rewrite using `[HypDec.qS, HypDec.qS, HypDec.symplOH_extX_extY, HypDec.symplOH_extX_extY, pairS_mul, pairS_mul, hA]`.
-/
theorem basePoint_spec : ∀ (D : D7) (σ : ℕ) (B : BesLev D σ), ∃ x₀ : Matrix (Fin B.V.rank) (Fin (σ + 1)) D.host.E,
    (rat x₀ : Mx D B.V.rank (σ + 1)) = x0 B ∧ IsBase B.V x₀ ∧
    Rgrp B.V (rat x₀ : Mx D B.V.rank (σ + 1)) = besGrp B.d B.o ∧
    (∀ a : Fin (σ + 1) → D.host.E, gramQ B.V x₀ *ᵥ a = 0 → a (Fin.last σ) = 0) ∧
    ∀ (S S₀ : HSp D) (d : HypDec S S₀ (σ + 1)) (c : skewA D (σ + 1)), d.qS B.V c (x0 B) = d.qS B.L c (zl B) := by
  intro D σ B
  obtain ⟨x, ⟨hli, hg⟩, hx⟩ := GlobalTheory.T.exists_mem_orb_rat_eq_x0 D σ B
  rw [← rat_zlQ] at hg
  have hG : gramQ B.V x = gramQ B.L (zlQ B) := gramQ_eq_of_gramSkew x (zlQ B) hg
  have hA : adj (x0 B) ⬝ (gA B.V ⬝ x0 B) = adj (zl B) ⬝ (gA B.L ⬝ zl B) := by
    rw [← hx, ← rat_zlQ, ← rat_gramQ, ← rat_gramQ, hG]
  refine ⟨x, hx, ⟨hli, fun u hu => ?_⟩, ?_, fun a ha => ?_, fun S S₀ d c => ?_⟩
  · rw [rat_gramQ, hx, hA, ]
    have hz : zl B ⬝ u.1 = zl B := zEll_mul B.L B.ζ hu
    calc adj u.1 ⬝ (adj (zl B) ⬝ (gA B.L ⬝ zl B) ⬝ u.1) = adj (zl B ⬝ u.1) ⬝ (gA B.L ⬝ (zl B ⬝ u.1)) := by
          rw [adj_mul]; simp only [Matrix.mul_assoc]
      _ = adj (zl B) ⬝ (gA B.L ⬝ zl B) := by rw [hz]
  · ext g
    rw [hx]
    exact ((GlobalTheory.T.mem_besGrp_iff_mt_mul_x0_eq_x0_mul D σ B).1 g).symm
  · have h1 := congrFun ha (Fin.last σ)
    rw [hG, gramQ_zlQ_mulVec_last, Pi.zero_apply] at h1
    exact (mul_eq_zero.1 h1).resolve_left B.line.2
  · rw [HypDec.qS, HypDec.qS, HypDec.symplOH_extX_extY, HypDec.symplOH_extX_extY, pairS_mul, pairS_mul, hA]

end GlobalTheory.Unf.FB
