import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedModelCentralTermsGramIdentitiesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SkewHermitianTracePairingStandardCharacterPerfecStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.CentralGram

variable {D : D7}

/- English proof (translation)
Use `show Algebra.trace (AF D.host.F) (AE D) ((1 : AF D.host.F) ⊗ₜ[D.host.F] x) = _`. Rewrite using `[Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]`.
-/
theorem trace_incA_eq (x : D.host.E) : Algebra.trace (AF D.host.F) (AE D) (incA D x) =
    algebraMap D.host.F (AF D.host.F) (Algebra.trace D.host.F D.host.E x) := by
  show Algebra.trace (AF D.host.F) (AE D) ((1 : AF D.host.F) ⊗ₜ[D.host.F] x) = _
  rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]

def qG {ρ : ℕ} (A c : Mx D ρ ρ) : AF D.host.F :=
  algebraMap D.host.F (AF D.host.F) (1 / 2) * Algebra.trace (AF D.host.F) (AE D) (A ⬝ c).trace

/- English proof (translation)
Simplify using `only [qG, Matrix.mul_add, Matrix.trace_add, map_add, mul_add]`.
-/
theorem qG_add_right {ρ : ℕ} (A c c' : Mx D ρ ρ) : qG A (c + c') = qG A c + qG A c' := by
  simp only [qG, Matrix.mul_add, Matrix.trace_add, map_add, mul_add]

/- English proof (translation)
Simplify using `only [qG, Matrix.sub_mul, Matrix.trace_sub, map_sub, mul_sub]`.
-/
theorem qG_sub_left {ρ : ℕ} (A A' c : Mx D ρ ρ) : qG (A - A') c = qG A c - qG A' c := by
  simp only [qG, Matrix.sub_mul, Matrix.trace_sub, map_sub, mul_sub]

/- English proof (translation)
Simplify using `only [Matrix.trace, Matrix.diag, rat, Matrix.map_apply, map_sum]`.
-/
theorem trace_rat {ρ : ℕ} (M : Matrix (Fin ρ) (Fin ρ) D.host.E) : (rat M : Mx D ρ ρ).trace = incA D M.trace := by
  simp only [Matrix.trace, Matrix.diag, rat, Matrix.map_apply, map_sum]

/- English proof (translation)
Rewrite using `[qG, ← rat_mul, trace_rat, trace_incA_eq, map_mul]`.
-/
theorem qG_rat {ρ : ℕ} (M C : Matrix (Fin ρ) (Fin ρ) D.host.E) :
    qG (rat M) (rat C) = algebraMap D.host.F (AF D.host.F) (1 / 2 * Algebra.trace D.host.F D.host.E (M * C).trace) := by
  rw [qG, ← rat_mul, trace_rat, trace_incA_eq, map_mul]

/- English proof (translation)
Use function extensionality and compare the values at `i j`. Conclude with `GlobalTheory.DualPairCheck.cA_incA _`.
-/
theorem map_cA_rat {m n : ℕ} (N : Matrix (Fin m) (Fin n) D.host.E) : (rat N).map (cA D) = rat (N.map star) := by
  funext i j; exact GlobalTheory.DualPairCheck.cA_incA _

def gramE (T : HSp D) {ρ : ℕ} (X : Matrix (Fin T.rank) (Fin ρ) D.host.E) : Matrix (Fin ρ) (Fin ρ) D.host.E :=
  (-D.host.xi0) • (Xᴴ * (T.gram * X))ᵀ

/- English proof (translation)
Rewrite using `[GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew, ← rat_conjTranspose, gA, ← rat_mul, ← rat_mul, ← map_neg (incA D), gramE, rat_smul]`. Both sides reduce to the same expression.
-/
theorem gramSkew_rat (T : HSp D) {ρ : ℕ} (X : Matrix (Fin T.rank) (Fin ρ) D.host.E) :
    GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew T (rat X) = rat (gramE T X) := by
  rw [GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew, ← rat_conjTranspose, gA, ← rat_mul, ← rat_mul, ← map_neg (incA D), gramE, rat_smul]
  rfl

/- English proof (translation)
Establish `hK : (Xᴴ * (T.gram * X))ᴴ = Xᴴ * (T.gram * X)`. Rewrite using `[Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, gram_conjTranspose, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]`. Use function extensionality and compare the values at `i j`. Establish `h` using `congrFun (congrFun hK i) j`. Rewrite `h` using `[Matrix.conjTranspose_apply]`.

Simplify using `only [gramE, Matrix.conjTranspose_apply, Matrix.map_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul, star_star, star_mul', star_neg, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, h]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gramE_skew (T : HSp D) {ρ : ℕ} (X : Matrix (Fin T.rank) (Fin ρ) D.host.E) :
    ((gramE T X).map star)ᴴ = -((gramE T X).map star) := by
  have hK : (Xᴴ * (T.gram * X))ᴴ = Xᴴ * (T.gram * X) := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, gram_conjTranspose, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc]
  funext i j
  have h := congrFun (congrFun hK i) j
  rw [Matrix.conjTranspose_apply] at h
  simp only [gramE, Matrix.conjTranspose_apply, Matrix.map_apply, Matrix.neg_apply, Matrix.smul_apply,
    Matrix.transpose_apply, smul_eq_mul, star_star, star_mul', star_neg, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, h]
  ring

/- English proof (translation)
Introduce `D`. Establish `h1` using `GlobalTheory.T.mixed_model_central_terms_gram_identities D`. Establish `hq : ∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (c : skewA D ρ) (x : Mx D T.rank ρ), d.qS T c x = -qG ((GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew T x).map (cA D)) c.1` using `fun S S₀ T ρ d c x => (h1.1 S S₀ T ρ d).2 c x`. Use `⟨fun S S₀ T ρ d => ⟨(h1.1 S S₀ T ρ d).1, (h1.1 S S₀ T ρ d).2, fun ψ hψ => ⟨?_, ?_, ?_⟩⟩, h1.2⟩` and prove the remaining obligations. Introduce `x c c'`.

Rewrite using `[hq, hq, hq, AddSubgroup.coe_add, qG_add_right, neg_add, AddChar.map_add_eq_mul]`. Introduce `x hx c hc`. Take `⟨X, rfl⟩` from `mem_ratMx.1 hx`. Take `⟨C, hC⟩` from `mem_ratMx.1 hc`. Rewrite using `[hq, gramSkew_rat, map_cA_rat, ← hC, qG_rat, ← map_neg]`.

Conclude with `hψ.1.2.2.1 _`. Introduce `x hx x' hx'`. Take `⟨X, rfl⟩` from `mem_ratMx.1 hx`. Take `⟨X', rfl⟩` from `mem_ratMx.1 hx'`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Establish `hM` using `GlobalTheory.T.skewHermitian_tracePairing_standardCharacter_perfect D ψ hψ ρ ((gramE T X).map star - (gramE T X').map star) (by rw [Matrix.conjTranspose_sub, gramE_skew, gramE_skew, neg_sub, neg_sub_neg]) (fun c => by`. Rewrite using `[rat_sub, ← map_cA_rat, ← map_cA_rat, ← gramSkew_rat, ← gramSkew_rat]`. Express the relevant statement in the definitionally equal form `ψ (qG _ c.1) = 1`. Establish `eA : qG ((GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew T (rat X)).map (cA D)) c.1 = -d.qS T c (rat X)`.

Rewrite using `[hq S S₀ T ρ d, neg_neg]`. Establish `eA' : qG ((GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew T (rat X')).map (cA D)) c.1 = -d.qS T c (rat X')`. Rewrite using `[hq S S₀ T ρ d, neg_neg]`. Rewrite using `[qG_sub_left, eA, eA', sub_eq_add_neg, neg_neg, AddChar.map_add_eq_mul, ← h c, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one])`. Rewrite `hM` using `[sub_eq_zero]`.

Rewrite using `[gramSkew_rat, gramSkew_rat, Matrix.map_injective star_injective hM]`. Introduce `h c`. Rewrite using `[hq, hq, h]`.
-/
theorem central : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.CentralTerms D := by
  intro D
  have h1 := GlobalTheory.T.mixed_model_central_terms_gram_identities D
  have hq : ∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (c : skewA D ρ) (x : Mx D T.rank ρ),
      d.qS T c x = -qG ((GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew T x).map (cA D)) c.1 :=
    fun S S₀ T ρ d c x => (h1.1 S S₀ T ρ d).2 c x
  refine ⟨fun S S₀ T ρ d => ⟨(h1.1 S S₀ T ρ d).1, (h1.1 S S₀ T ρ d).2, fun ψ hψ => ⟨?_, ?_, ?_⟩⟩, h1.2⟩
  · intro x c c'
    rw [hq, hq, hq, AddSubgroup.coe_add, qG_add_right, neg_add, AddChar.map_add_eq_mul]
  · intro x hx c hc
    obtain ⟨X, rfl⟩ := mem_ratMx.1 hx
    obtain ⟨C, hC⟩ := mem_ratMx.1 hc
    rw [hq, gramSkew_rat, map_cA_rat, ← hC, qG_rat, ← map_neg]
    exact hψ.1.2.2.1 _
  · intro x hx x' hx'
    obtain ⟨X, rfl⟩ := mem_ratMx.1 hx
    obtain ⟨X', rfl⟩ := mem_ratMx.1 hx'
    constructor
    · intro h
      have hM := GlobalTheory.T.skewHermitian_tracePairing_standardCharacter_perfect D ψ hψ ρ ((gramE T X).map star - (gramE T X').map star)
        (by rw [Matrix.conjTranspose_sub, gramE_skew, gramE_skew, neg_sub, neg_sub_neg]) (fun c => by
          rw [rat_sub, ← map_cA_rat, ← map_cA_rat, ← gramSkew_rat, ← gramSkew_rat]
          change ψ (qG _ c.1) = 1
          have eA : qG ((GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew T (rat X)).map (cA D)) c.1 = -d.qS T c (rat X) := by
            rw [hq S S₀ T ρ d, neg_neg]
          have eA' : qG ((GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew T (rat X')).map (cA D)) c.1 = -d.qS T c (rat X') := by
            rw [hq S S₀ T ρ d, neg_neg]
          rw [qG_sub_left, eA, eA', sub_eq_add_neg, neg_neg, AddChar.map_add_eq_mul, ← h c, ← AddChar.map_add_eq_mul,
            neg_add_cancel, AddChar.map_zero_eq_one])
      rw [sub_eq_zero] at hM
      rw [gramSkew_rat, gramSkew_rat, Matrix.map_injective star_injective hM]
    · intro h c
      rw [hq, hq, h]

end GlobalTheory.CentralGram
