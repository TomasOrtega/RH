import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DerAlong
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RatPairSep

variable {D : D7}

/- English proof (translation)
Use `(traceForm_nondegenerate ℚ D.host.E).1 q fun z => ?_` and prove the remaining obligations. Establish `hl : (Algebra.traceForm ℚ D.host.E) q = 0` using `(integralBasis D.host.E).ext fun k => by`. Rewrite using `[LinearMap.zero_apply, Algebra.traceForm_apply]`. Conclude with `h k`. Rewrite using `[hl, LinearMap.zero_apply]`.
-/
theorem eq_zero_of_trace_integralBasis (D : D7) (q : D.host.E)
    (h : ∀ k, Algebra.trace ℚ D.host.E (q * integralBasis D.host.E k) = 0) : q = 0 := by
  refine (traceForm_nondegenerate ℚ D.host.E).1 q fun z => ?_
  have hl : (Algebra.traceForm ℚ D.host.E) q = 0 :=
    (integralBasis D.host.E).ext fun k => by
      rw [LinearMap.zero_apply, Algebra.traceForm_apply]; exact h k
  rw [hl, LinearMap.zero_apply]

/- English proof (translation)
Establish `: adj D (y - y') = adj D y - adj D y'`. Use extensionality with `i j`. Simplify using `[adj, Formalism.UG.cT]`. Simplify using `only [pairQ, this, Matrix.sub_mul, smul_sub]`.
-/
theorem pairQ_sub (W : HSp D) {r : ℕ} (y y' : Matrix (Fin W.rank) (Fin r) D.host.E) :
    pairQ W y - pairQ W y' = pairQ W (y - y') := by
  have : adj D (y - y') = adj D y - adj D y' := by
    ext i j; simp [adj, Formalism.UG.cT]
  simp only [pairQ, this, Matrix.sub_mul, smul_sub]

/- English proof (translation)
Establish `h1 : adj D y * W.gram = adj D y' * W.gram`. Use `congrArg (fun M => (D.host.xi0)⁻¹ • M) h` as an intermediate fact. Simplify `this` using `[pairQ, smul_smul, inv_mul_cancel₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)]`. Establish `h2 : adj D y = adj D y'`. Use `congrArg (fun M => M * W.gram⁻¹) h1` as an intermediate fact.

Simplify `this` using `[Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (GlobalTheory.LatVac.gram_det_isUnit W)]`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Use `congrFun (congrFun h2 j) i` as an intermediate fact. Simplify using `only [adj, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply] at this`. Conclude with `(D.sp.cm.sig : D.host.E →+* D.host.E).injective this`.
-/
theorem eq_of_pairQ_eq (W : HSp D) {r : ℕ} (y y' : Matrix (Fin W.rank) (Fin r) D.host.E)
    (h : pairQ W y = pairQ W y') : y = y' := by
  have h1 : adj D y * W.gram = adj D y' * W.gram := by
    have := congrArg (fun M => (D.host.xi0)⁻¹ • M) h
    simpa [pairQ, smul_smul, inv_mul_cancel₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)] using this
  have h2 : adj D y = adj D y' := by
    have := congrArg (fun M => M * W.gram⁻¹) h1
    simpa [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (GlobalTheory.LatVac.gram_det_isUnit W)] using this
  refine Matrix.ext fun i j => ?_
  have := congrFun (congrFun h2 j) i
  simp only [adj, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply] at this
  exact (D.sp.cm.sig : D.host.E →+* D.host.E).injective this

/- English proof (translation)
Set `ι` to `Fin W.rank × Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 D.host.E)`. Set `e` to `Fintype.equivFin ι`. Set `Y : ι → Matrix (Fin W.rank) (Fin r) D.host.E` to `fun t => Matrix.single t.1 t.2.1 (integralBasis D.host.E t.2.2)`. Use `⟨Fintype.card ι, fun j => Y (e.symm j), ?_, ?_⟩` and prove the remaining obligations. Introduce `j a b`.

Simplify using `only [Y, Matrix.single_apply]`. Use `split_ifs`. Rewrite using `[integralBasis_apply]`. Conclude with `(RingOfIntegers.basis D.host.E _).isIntegral_coe`. Conclude with `isIntegral_zero`.

Introduce `y y' h`. Apply `eq_of_pairQ_eq W y y'` to reduce the goal to its premises. Rewrite using `[← sub_eq_zero, pairQ_sub]`. Use `Matrix.ext fun l i => ?_` and prove the remaining obligations. Rewrite using `[Matrix.zero_apply]`.

Use `eq_zero_of_trace_integralBasis D _ fun k => ?_` and prove the remaining obligations. Establish `hj` using `h (e (i, l, k))`. Simplify using `only [ratPair, Equiv.symm_apply_apply, Y, Rat.cast_inj] at hj`. Rewrite `hj` using `[← sub_eq_zero, ← map_sub, ← Matrix.trace_sub, ← Matrix.sub_mul, pairQ_sub, Matrix.trace_mul_single]`. Simplify `hj` using `[MulOpposite.smul_eq_mul_unop]`.
-/
theorem exists_sep (D : D7) (W : HSp D) (r : ℕ) :
    ∃ (n : ℕ) (X : Fin n → Matrix (Fin W.rank) (Fin r) D.host.E), (∀ j a b, IsIntegral ℤ (X j a b)) ∧
      ∀ y y' : Matrix (Fin W.rank) (Fin r) D.host.E, (∀ j, ratPair W y (X j) = ratPair W y' (X j)) → y = y' := by
  let ι := Fin W.rank × Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 D.host.E)
  let e := Fintype.equivFin ι
  let Y : ι → Matrix (Fin W.rank) (Fin r) D.host.E := fun t => Matrix.single t.1 t.2.1 (integralBasis D.host.E t.2.2)
  refine ⟨Fintype.card ι, fun j => Y (e.symm j), ?_, ?_⟩
  · intro j a b
    simp only [Y, Matrix.single_apply]
    split_ifs
    · rw [integralBasis_apply]; exact (RingOfIntegers.basis D.host.E _).isIntegral_coe
    · exact isIntegral_zero
  · intro y y' h
    apply eq_of_pairQ_eq W y y'
    rw [← sub_eq_zero, pairQ_sub]
    refine Matrix.ext fun l i => ?_
    rw [Matrix.zero_apply]
    refine eq_zero_of_trace_integralBasis D _ fun k => ?_
    have hj := h (e (i, l, k))
    simp only [ratPair, Equiv.symm_apply_apply, Y, Rat.cast_inj] at hj
    rw [← sub_eq_zero, ← map_sub, ← Matrix.trace_sub, ← Matrix.sub_mul, pairQ_sub,
      Matrix.trace_mul_single] at hj
    simpa [MulOpposite.smul_eq_mul_unop] using hj

end GlobalTheory.RatPairSep

/- English proof (translation)
The claim follows from `GlobalTheory.RatPairSep.exists_sep`.
-/
theorem GlobalTheory.RatPairSep.main : ∀ (D : D7) (W : HSp D) (r : ℕ), ∃ (n : ℕ) (X : Fin n → Matrix (Fin W.rank) (Fin r) D.host.E),
    (∀ j a b, IsIntegral ℤ (X j a b)) ∧ ∀ y y' : Matrix (Fin W.rank) (Fin r) D.host.E,
    (∀ j, ratPair W y (X j) = ratPair W y' (X j)) → y = y' := GlobalTheory.RatPairSep.exists_sep
